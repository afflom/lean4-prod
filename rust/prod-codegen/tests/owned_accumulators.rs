//! Raw-IR API regression; source/kernel execution is a separate fixture gate.
use prod_codegen::{generate_cargo_package, generate_module, CargoPackageSpec};
use prod_ir::parser::parse_module;
use sha2::{Digest, Sha256};
use std::{path::PathBuf, process::Command};

const IR: &str = r#"(module OwnedAccumulator
  (type "Row" (ctor "Row.mk" (bytes Bytes)))
  (type "Rows" (ctor "Rows.mk" (items (List (named "Row")))))
  (type "Pair" (ctor "Pair.mk" (left (List (named "Row"))) (right (List (named "Row")))))
  (def __prod_owned_7_collect () Nat 17)
  (def collect ((items (List (named "Row"))) (fuel Nat)) (named "Rows")
    (cases fuel
      (alt "Nat.zero" () (ctor "Rows.mk" items))
      (alt "Nat.succ" (rest)
        (let next (append items (ctor "List.cons" (ctor "Row.mk" (bytes 42)) (ctor "List.nil")))
          (call collect next rest)))))
  (def start ((fuel Nat)) (named "Rows")
    (call collect (ctor "List.nil") fuel))
  (def owned_start ((seed (Option (named "Row"))) (fuel Nat)) (named "Rows")
    (cases seed
      (alt "Option.none" () (call start fuel))
      (alt "Option.some" (row)
        (call collect (ctor "List.cons" row (ctor "List.nil")) fuel))))
  (def alias ((items (List (named "Row"))) (fuel Nat)) (named "Pair")
    (if (eq fuel 0) (ctor "Pair.mk" items items)
      (call alias (append items (ctor "List.nil")) (sub fuel 1))))
  (def branch ((items (List (named "Row"))) (fuel Nat) (flag Bool)) (named "Rows")
    (if (eq fuel 0) (ctor "Rows.mk" items)
      (if flag
        (call branch (append items (ctor "List.cons" (ctor "Row.mk" (bytes 1)) (ctor "List.nil"))) (sub fuel 1) false)
        (call branch (append items (ctor "List.cons" (ctor "Row.mk" (bytes 2)) (ctor "List.nil"))) (sub fuel 1) true))))
  (def checked ((items (List (named "Row"))) (fuel Nat) (left Nat) (right Nat)) (named "Rows")
    (if (eq fuel 0) (ctor "Rows.mk" items)
      (call checked (append items (ctor "List.nil")) (sub fuel 1) (add left 1) (mul right 2))))
  (def retained_read ((items (List (named "Row"))) (fuel Nat)) (named "Pair")
    (if (eq fuel 0) (ctor "Pair.mk" items (ctor "List.nil"))
      (let result (call retained_read (append items (ctor "List.nil")) (sub fuel 1))
        (ctor "Pair.mk" items (proj "Pair" "right" result)))))
  (def changed_borrow ((input (named "Row")) (items (List (named "Row"))) (fuel Nat)) (named "Rows")
    (if (eq fuel 0) (ctor "Rows.mk" items)
      (call changed_borrow (ctor "Row.mk" (bytes 9)) (append items (ctor "List.nil")) (sub fuel 1))))
)"#;

#[test]
fn single_use_list_accumulator_keeps_public_slice_and_moves_private_worker() {
    let (remaining, module) = parse_module(IR).unwrap();
    assert!(remaining.is_empty());
    let generated = generate_module(&module).unwrap();
    assert!(generated.contains("pub fn collect(items: &[crate::Row], fuel: u64)"));
    assert!(
        generated.contains(
            "fn __prod_owned_7_collect_(mut items: alloc::vec::Vec<crate::Row>, mut fuel: u64)"
        ),
        "{generated}"
    );
    let worker = generated
        .split("fn __prod_owned_7_collect_(")
        .nth(1)
        .unwrap()
        .split("\npub fn ")
        .next()
        .unwrap();
    assert!(worker.contains("loop {"));
    assert!(
        !worker.contains("ToOwned"),
        "the recursive worker must retain the accumulator owner"
    );
    assert!(
        !worker.contains("__prod_owned_7_collect_("),
        "the self-tail back edge must not recurse"
    );
    assert!(generated.contains("__prod_owned_7_collect_(alloc::vec::Vec::new(), fuel)"));
    for refused in ["alias", "retained_read", "changed_borrow"] {
        assert!(!generated.contains(&format!("fn __prod_owned_{}_{refused}(", refused.len())));
    }
}

#[test]
fn raw_scope_reads_aliases_and_non_tail_shapes_keep_the_existing_borrowed_path() {
    let bodies = [
        // Source sharing must remain sharing even though self-append has a
        // separate existing optimization for one owned collection expression.
        r#"(if (eq fuel 0) (ctor "Rows.mk" items) (call f (append items items) (sub fuel 1)))"#,
        r#"(if (eq fuel 0) (ctor "Rows.mk" items) (let alias items (call f (append alias (ctor "List.nil")) (sub fuel 1))))"#,
        r#"(if (eq (length items) 0) (ctor "Rows.mk" items) (call f (append items (ctor "List.nil")) (sub fuel 1)))"#,
        r#"(if (eq fuel 0) (ctor "Rows.mk" (param 0)) (call f (append items (ctor "List.nil")) (sub fuel 1)))"#,
        r#"(if (eq fuel 0) (ctor "Rows.mk" items) (let next (jp next () (call f (append items (ctor "List.nil")) (sub fuel 1))) (jmp next)))"#,
        r#"(if (eq fuel 0) (ctor "Rows.mk" items) (let items (ctor "List.nil") (call f (append items (ctor "List.nil")) (sub fuel 1))))"#,
        r#"(cases items (alt "List.nil" () (ctor "Rows.mk" (ctor "List.nil"))) (alt "List.cons" (head tail) (call f tail (sub fuel 1))))"#,
        r#"(if (eq fuel 0) (ctor "Rows.mk" items) (let ignored (call f (append items (ctor "List.nil")) (sub fuel 1)) (ctor "Rows.mk" (ctor "List.nil"))))"#,
    ];
    for body in bodies {
        let ir = format!(
            r#"(module Guard
          (type "Row" (ctor "Row.mk" (bytes Bytes)))
          (type "Rows" (ctor "Rows.mk" (items (List (named "Row")))))
          (def f ((items (List (named "Row"))) (fuel Nat)) (named "Rows") {body}))"#
        );
        let (remaining, module) = parse_module(&ir).unwrap();
        assert!(remaining.is_empty());
        let generated = generate_module(&module).unwrap();
        assert!(generated.contains("pub fn f(items: &[crate::Row], fuel: u64)"));
        assert!(
            !generated.contains("fn __prod_owned_1_f("),
            "{body}\n{generated}"
        );
    }
}

const RUNNER: &str = r#"
use owned_accumulator_fixture::*;
fn main() {
    assert_eq!(__prod_owned_7_collect(), 17);
    std::thread::Builder::new().stack_size(65536).spawn(|| {
        for fuel in [0, 1, 2, 255, 256, 65536] {
            let seed = vec![7; 4096]; let pointer = seed.as_ptr();
            let actual = owned_start(Some(Row {bytes: seed}), fuel);
            assert_eq!(actual.items.len(), fuel as usize + 1);
            assert_eq!(actual.items[0].bytes.as_ptr(), pointer, "source-owned payload is never cloned along back edges");
            assert_eq!(actual.items[0].bytes, vec![7; 4096]);
            assert!(actual.items[1..].iter().all(|row| row.bytes == [42]));
        }
        for fuel in [0, 1, 2, 17, 256] {
            let seed = vec![Row {bytes: vec![8; 4096]}];
            let actual = collect(&seed, fuel);
            assert_eq!(seed[0].bytes, vec![8; 4096]);
            assert_ne!(actual.items[0].bytes.as_ptr(), seed[0].bytes.as_ptr(), "public slice caller retains independent ownership");
            assert_eq!(actual.items.len(), fuel as usize + 1);
            for flag in [false, true] {
                let actual = branch(&[], fuel, flag);
                assert_eq!(actual.items.len(), fuel as usize);
                for (index, row) in actual.items.iter().enumerate() {
                    assert_eq!(row.bytes, [if flag ^ (index % 2 == 1) {1} else {2}]);
                }
            }
        }
        assert_eq!(checked(&[], 0, u64::MAX, u64::MAX), Ok(Rows {items: vec![]}));
        assert_eq!(checked(&[], 1, u64::MAX, u64::MAX), Err(ComputeError::AddOverflow));
        assert_eq!(checked(&[], 1, 0, u64::MAX), Err(ComputeError::MulOverflow));
        assert_eq!(checked(&[], 3, 1, 2), Ok(Rows {items: vec![]}));
        let seed = vec![Row {bytes: vec![3,4]}];
        let mut result = alias(&seed, 2);
        result.left[0].bytes[0] = 9;
        assert_eq!(result.right[0].bytes, [3,4]);
        assert_eq!(seed[0].bytes, [3,4]);
        assert_eq!(retained_read(&seed, 2).left, seed);
        assert_eq!(changed_borrow(&Row {bytes: vec![0]}, &seed, 2).items, seed);
    }).unwrap().join().unwrap();
    println!("owned accumulator: ownership, alias, branch, eager errors and 64KiB stack passed");
}
"#;

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "prod-owned-accumulator-{}-{nonce}",
            std::process::id()
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained failing fixture: {}", self.0.display());
        } else {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}
fn succeeds(command: &mut Command) -> String {
    let result = command.output().unwrap();
    assert!(
        result.status.success(),
        "{command:?}\n{}\n{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    String::from_utf8(result.stdout).unwrap()
}

#[test]
fn native_owners_branches_aliases_errors_and_small_stack() {
    single_use_list_accumulator_keeps_public_slice_and_moves_private_worker();
    let (_, module) = parse_module(IR).unwrap();
    let spec = CargoPackageSpec {
        name: "owned-accumulator-fixture".into(),
        version: "0.1.0".into(),
        description: "Compiler owned list-accumulator regression".into(),
        repository: "https://github.com/auser/lean4-prod".into(),
        homepage: "https://github.com/auser/lean4-prod".into(),
        readme: "Compiler regression fixture.\n".into(),
        license_mit: "MIT\n".into(),
        license_apache: "Apache-2.0\n".into(),
        input_sha256: format!("{:x}", Sha256::digest(IR.as_bytes())),
        dependencies: vec![],
    };
    let package = generate_cargo_package(&module, &spec).unwrap();
    assert_eq!(package, generate_cargo_package(&module, &spec).unwrap());
    let scratch = Scratch::new();
    for file in package.files {
        let path = scratch.0.join(file.path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, file.bytes).unwrap();
    }
    let runner = scratch.0.join("runner.rs");
    std::fs::write(&runner, RUNNER).unwrap();
    for standard in [true, false] {
        for optimized in [false, true] {
            let library = scratch
                .0
                .join(format!("libfixture_{standard}_{optimized}.rlib"));
            let mut compiler = Command::new("rustc");
            compiler.args([
                "--edition=2021",
                "--crate-type=rlib",
                "--crate-name=owned_accumulator_fixture",
            ]);
            if standard {
                compiler.args(["--cfg", "feature=\"std\""]);
            }
            compiler.args([
                "-C",
                if optimized {
                    "opt-level=3"
                } else {
                    "opt-level=0"
                },
                "-C",
                "overflow-checks=yes",
                "-C",
                "debug-assertions=yes",
            ]);
            succeeds(
                compiler
                    .arg(scratch.0.join("src/lib.rs"))
                    .arg("-o")
                    .arg(&library),
            );
            let executable = scratch.0.join(format!("runner_{standard}_{optimized}"));
            succeeds(
                Command::new("rustc")
                    .arg("--edition=2021")
                    .arg(&runner)
                    .arg("--extern")
                    .arg(format!("owned_accumulator_fixture={}", library.display()))
                    .arg("-o")
                    .arg(&executable),
            );
            assert_eq!(succeeds(&mut Command::new(&executable)), "owned accumulator: ownership, alias, branch, eager errors and 64KiB stack passed\n");
        }
    }
}
