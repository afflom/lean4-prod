//! Stack-bounded self-tail calls preserve ownership, eager errors and swaps.
use prod_codegen::{
    generate_cargo_package, generate_core_wasm_package, CargoPackageSpec, CoreWasmSpec,
};
use prod_ir::parser::parse_module;
use sha2::{Digest, Sha256};
use std::{path::PathBuf, process::Command};

const IR: &str = r#"(module TailCalls
  (type "Progress" (ctor "Progress.mk" (bytes Bytes) (steps Nat)))
  (def walk ((input Bytes) (remaining Nat) (state (Option (named "Progress")))) (Option (named "Progress"))
    (cases remaining
      (alt "Nat.zero" () state)
      (alt "Nat.succ" (rest)
        (cases state
          (alt "Option.none" () (ctor "Option.none"))
          (alt "Option.some" (row)
            (let bytes (proj "Progress" "bytes" row)
              (let steps (proj "Progress" "steps" row)
                (if (eq (length input) 0)
                  (ctor "Option.none")
                  (let next (call walk input rest (ctor "Option.some" (ctor "Progress.mk" bytes (add steps 1)))) next)))))))))
  (def borrowed_walk ((input Bytes) (remaining Nat) (expected Nat)) Bool
    (if (eq remaining 0) (eq (length input) expected)
      (call borrowed_walk input (sub remaining 1) expected)))
  (def swap ((remaining Nat) (left Nat) (right Nat)) Nat
    (if (eq remaining 0) left (call swap (sub remaining 1) right left)))
  (def checked ((remaining Nat) (left Nat) (right Nat)) Nat
    (if (eq remaining 0) left
      (call checked (sub remaining 1) (add left 1) (mul right 2))))
  (def shadow ((remaining Nat) (__prod_tail Nat) (__next Nat)) Nat
    (if (eq remaining 0) __next
      (let __next (add __prod_tail __next)
        (call shadow (sub remaining 1) __prod_tail __next))))
  (def through_join ((remaining Nat) (total Nat)) Nat
    (let finish (jp finish (next) (call through_join (sub remaining 1) next))
      (if (eq remaining 0) total (jmp finish (add total 1)))))
  (def non_tail ((remaining Nat)) Nat
    (if (eq remaining 0) 0 (add 1 (call non_tail (sub remaining 1)))))
  (def changing_borrow ((input Bytes) (remaining Nat)) Bool
    (if (eq remaining 0) (eq (length input) 1)
      (call changing_borrow (bytes 42) (sub remaining 1))))
  (def entry ((input Bytes)) Bytes
    (cases (call walk (bytes 1) 100000 (ctor "Option.some" (ctor "Progress.mk" input 0)))
      (alt "Option.none" () (bytes))
      (alt "Option.some" (row)
        (if (eq (proj "Progress" "steps" row) 100000) (proj "Progress" "bytes" row) (bytes)))))
)"#;

fn package() -> prod_codegen::GeneratedPackage {
    let (remaining, module) = parse_module(IR).unwrap();
    assert!(remaining.trim().is_empty());
    let spec = CargoPackageSpec {
        name: "tail-calls-fixture".into(),
        version: "0.1.0".into(),
        description: "Compiler self-tail-call regression".into(),
        repository: "https://github.com/auser/lean4-prod".into(),
        homepage: "https://github.com/auser/lean4-prod".into(),
        readme: "Compiler regression fixture.\n".into(),
        license_mit: "MIT\n".into(),
        license_apache: "Apache-2.0\n".into(),
        input_sha256: format!("{:x}", Sha256::digest(IR.as_bytes())),
        dependencies: vec![],
    };
    let result = generate_cargo_package(&module, &spec).unwrap();
    assert_eq!(result, generate_cargo_package(&module, &spec).unwrap());
    result
}

#[test]
fn eligible_tail_calls_are_explicit_loops_not_optimizer_promises() {
    let package = package();
    let code = std::str::from_utf8(
        &package
            .files
            .iter()
            .find(|file| file.path == "src/lib.rs")
            .unwrap()
            .bytes,
    )
    .unwrap();
    assert_eq!(
        code.matches("loop {").count(),
        6,
        "six eligible definitions"
    );
    assert_eq!(code.matches("continue;").count(), 6);
    assert!(code.contains("non_tail("));
    assert!(code.contains("changing_borrow("));
}

const RUNNER: &str = r#"
use tail_calls_fixture::*;
fn main() {
    std::thread::Builder::new().stack_size(65536).spawn(|| {
        let input = [1, 2, 3];
        for count in [0, 1, 2, 1024, 100000] {
            let bytes = input.to_vec();
            let pointer = bytes.as_ptr();
            let result = walk(input.to_vec(), count, Some(Progress { bytes, steps: 0 })).unwrap().unwrap();
            assert_eq!(result.bytes, input);
            assert_eq!(result.bytes.as_ptr(), pointer, "owned progress must move");
            assert_eq!(result.steps, count);
            assert_eq!(walk(input.to_vec(), count, None), Ok(None));
            assert_eq!(swap(count, 7, 13), if count % 2 == 0 { 7 } else { 13 });
            assert_eq!(shadow(count, 1, 0), Ok(count));
            assert_eq!(through_join(count, 0), Ok(count));
            assert!(borrowed_walk(&input, count, 3));
            assert!(!borrowed_walk(&input, count, 4));
        }
        assert_eq!(walk(vec![], 1, Some(Progress { bytes: vec![1], steps: 0 })), Ok(None));
        assert_eq!(walk(vec![1], 1, Some(Progress { bytes: vec![], steps: u64::MAX })), Err(ComputeError::AddOverflow));
        assert_eq!(checked(0, u64::MAX, u64::MAX), Ok(u64::MAX));
        assert_eq!(checked(1, u64::MAX, u64::MAX), Err(ComputeError::AddOverflow));
        assert_eq!(checked(1, 0, u64::MAX), Err(ComputeError::MulOverflow));
        assert_eq!(checked(3, 1, 2), Ok(4));
        assert_eq!(non_tail(5), Ok(5));
        assert!(!changing_borrow(&[], 0));
        assert!(changing_borrow(&[], 3));
    }).unwrap().join().unwrap();
    println!("tail calls: small-stack ownership, order and boundaries passed");
}
"#;

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path =
            std::env::temp_dir().join(format!("prod-tail-calls-{}-{nonce}", std::process::id()));
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
fn generated_tail_calls_execute_on_small_stack_in_std_no_std_o0_o3() {
    // A structural failure is a safe precondition failure, not a process-aborting
    // stack overflow on an unchanged compiler.
    eligible_tail_calls_are_explicit_loops_not_optimizer_promises();
    let scratch = Scratch::new();
    for file in package().files {
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
            let mut command = Command::new("rustc");
            command.args([
                "--edition=2021",
                "--crate-type=rlib",
                "--crate-name=tail_calls_fixture",
            ]);
            if standard {
                command.args(["--cfg", "feature=\"std\""]);
            }
            command.args([
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
                command
                    .arg(scratch.0.join("src/lib.rs"))
                    .arg("-o")
                    .arg(&library),
            );
            let binary = scratch.0.join(format!("runner_{standard}_{optimized}"));
            succeeds(
                Command::new("rustc")
                    .arg("--edition=2021")
                    .arg(&runner)
                    .arg("--extern")
                    .arg(format!("tail_calls_fixture={}", library.display()))
                    .arg("-o")
                    .arg(&binary),
            );
            assert_eq!(
                succeeds(&mut Command::new(binary)),
                "tail calls: small-stack ownership, order and boundaries passed\n"
            );
        }
    }
}

#[test]
fn generated_tail_calls_execute_in_unoptimized_and_optimized_bounded_wasm() {
    eligible_tail_calls_are_explicit_loops_not_optimizer_promises();
    let (remaining, module) = parse_module(IR).unwrap();
    assert!(remaining.trim().is_empty());
    let spec = CoreWasmSpec {
        crate_name: "tail-calls-guest".into(),
        entry: "entry".into(),
        export_name: "holo_run".into(),
        input_allocation_cap: 4096,
        output_allocation_cap: 4096,
        maximum_pages: 16,
        input_ir_sha256: format!("{:x}", Sha256::digest(IR.as_bytes())),
    };
    let package = generate_core_wasm_package(&module, &spec).unwrap();
    assert_eq!(package, generate_core_wasm_package(&module, &spec).unwrap());
    let scratch = Scratch::new();
    for file in package.files {
        let path = scratch.0.join(file.path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, file.bytes).unwrap();
    }
    let flags = std::fs::read_to_string(scratch.0.join(".cargo/config.toml")).unwrap();
    assert!(flags.contains("stack-size=65536"));
    for profile in ["debug", "release"] {
        let mut build = Command::new("cargo");
        build
            .current_dir(&scratch.0)
            .args(["build", "--locked", "--offline"])
            .env_remove("RUSTC_WRAPPER")
            .env("CARGO_TARGET_DIR", scratch.0.join("target"));
        if profile == "release" {
            build.arg("--release");
        }
        succeeds(&mut build);
        succeeds(
            Command::new("node")
                .arg(
                    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                        .join("tests/fixtures/tail_calls_wasm_test.mjs"),
                )
                .arg(scratch.0.join(format!(
                    "target/wasm32-unknown-unknown/{profile}/tail_calls_guest.wasm"
                ))),
        );
    }
}
