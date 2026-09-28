//! LCNF scalar literal bindings in allocation-free promoted list constants.
//! The verbatim P-256 fixture comes from the kernel-checked LexLean source at
//! UOR-Foundation/PrismPM commit 620eb1d, Foundation/Crypto/P256/Model.lex.tex;
//! its source and original exported-module hashes accompany the fixture.
use prod_codegen::{generate_cargo_package, generate_module, CargoPackageSpec, Error};
use prod_ir::parser::parse_module;
use sha2::{Digest, Sha256};
use std::{fs, path::PathBuf, process::Command};

const IR: &str = r#"(module StaticBindings
  (def constants () (List Nat)
    (let zero 0 (let limb 65535 (let wide 4294967296
      (let largest 18446744073709551615 (let alias wide
        (let empty (ctor "List.nil")
          (let tail (ctor "List.cons" largest empty)
            (let tail (ctor "List.cons" alias tail)
              (let wide 7
                (ctor "List.cons" zero
                  (ctor "List.cons" limb (ctor "List.cons" wide tail)))))))))))))
  (def booleans () (List Bool)
    (let yes true (let alias yes (let no false
      (ctor "List.cons" alias (ctor "List.cons" no (ctor "List.nil")))))))
  (def octets () (List UInt8)
    (let maximum 255 (ctor "List.cons" maximum (ctor "List.nil"))))
  (def signed () (List Int8)
    (let minimum -128 (let maximum 127
      (ctor "List.cons" minimum (ctor "List.cons" maximum (ctor "List.nil"))))))
  (def captured () (List Nat)
    (let x 3 (let xs (ctor "List.cons" x (ctor "List.nil"))
      (let x 9 (ctor "List.cons" x xs)))))
  (def rebound () (List Nat)
    (let x 1 (let alias x (let x (ctor "List.cons" x (ctor "List.nil"))
      (let saved x (let x alias (ctor "List.cons" x saved)))))))
  (def captured_only () (List Nat)
    (let x 1 (let xs (ctor "List.cons" x (ctor "List.nil")) (let x 2 xs))))
  (def unsigned16 () (List UInt16)
    (let high 65535 (ctor "List.cons" high (ctor "List.nil"))))
  (def unsigned32 () (List UInt32)
    (let high 4294967295 (ctor "List.cons" high (ctor "List.nil"))))
  (def signed64 () (List Int64)
    (let low -9223372036854775808 (let high 9223372036854775807
      (ctor "List.cons" low (ctor "List.cons" high (ctor "List.nil")))))))"#;

const RUNNER: &str = r#"use static_bindings_fixture::*;
fn main() {
    assert_eq!(constants(), &[0, 65535, 7, 4294967296, u64::MAX]);
    assert_eq!(booleans(), &[true, false]);
    assert_eq!(octets(), &[255]);
    assert_eq!(signed(), &[-128, 127]);
    assert_eq!(captured(), &[9, 3]);
    assert_eq!(rebound(), &[1, 1]);
    assert_eq!(captured_only(), &[1]);
    assert_eq!(unsigned16(), &[u16::MAX]);
    assert_eq!(unsigned32(), &[u32::MAX]);
    assert_eq!(signed64(), &[i64::MIN, i64::MAX]);
    assert_eq!(p256Modulus(), &[65535,65535,65535,65535,65535,65535,0,0,0,0,0,0,1,0,65535,65535,0]);
    assert_eq!(p256CurveB(), &[24651,10194,15422,15310,45302,52307,1712,25885,34492,30360,48469,46059,37863,43578,13784,23238,0]);
    assert_eq!(p256Zero(), &[0;17]);
    assert_eq!(p256BitPowers(), &[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]);
    assert!(core::ptr::eq(constants().as_ptr(), constants().as_ptr()));
}
"#;

const WASM_WRAPPER: &str = r#"extern crate static_bindings_fixture;
use static_bindings_fixture::*;
#[no_mangle] pub extern "C" fn constant_at(i: u32) -> u64 { constants()[i as usize] }
#[no_mangle] pub extern "C" fn boolean_at(i: u32) -> u32 { booleans()[i as usize] as u32 }
#[no_mangle] pub extern "C" fn octet() -> u32 { octets()[0] as u32 }
#[no_mangle] pub extern "C" fn signed_at(i: u32) -> i32 { signed()[i as usize] as i32 }
#[no_mangle] pub extern "C" fn captured_at(i: u32) -> u64 { captured()[i as usize] }
#[no_mangle] pub extern "C" fn rebound_at(i: u32) -> u64 { rebound()[i as usize] }
#[no_mangle] pub extern "C" fn captured_only_at() -> u64 { captured_only()[0] }
#[no_mangle] pub extern "C" fn unsigned16_at() -> u32 { unsigned16()[0] as u32 }
#[no_mangle] pub extern "C" fn unsigned32_at() -> u32 { unsigned32()[0] }
#[no_mangle] pub extern "C" fn signed64_at(i: u32) -> i64 { signed64()[i as usize] }
#[no_mangle] pub extern "C" fn actual_at(which: u32, i: u32) -> u64 {
    (match which { 0 => p256Modulus(), 1 => p256CurveB(), 2 => p256Zero(), _ => p256BitPowers() })[i as usize]
}
"#;

const WASM_TEST: &str = r#"import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
const module = new WebAssembly.Module(readFileSync(process.argv[2]));
assert.deepEqual(WebAssembly.Module.imports(module), []);
const e = new WebAssembly.Instance(module, {}).exports;
assert.deepEqual([0,1,2,3,4].map(i=>BigInt.asUintN(64,e.constant_at(i))),
  [0n,65535n,7n,4294967296n,18446744073709551615n]);
assert.deepEqual([0,1].map(e.boolean_at), [1,0]);
assert.equal(e.octet(),255);
assert.deepEqual([0,1].map(e.signed_at),[-128,127]);
assert.deepEqual([0,1].map(e.captured_at),[9n,3n]);
assert.deepEqual([0,1].map(e.rebound_at),[1n,1n]);
assert.equal(e.captured_only_at(),1n);
assert.equal(e.unsigned16_at(),65535);
assert.equal(e.unsigned32_at()>>>0,4294967295);
assert.deepEqual([0,1].map(e.signed64_at),[-9223372036854775808n,9223372036854775807n]);
for (const [which,values] of [
  [0,[65535,65535,65535,65535,65535,65535,0,0,0,0,0,0,1,0,65535,65535,0]],
  [1,[24651,10194,15422,15310,45302,52307,1712,25885,34492,30360,48469,46059,37863,43578,13784,23238,0]],
  [2,Array(17).fill(0)], [3,Array.from({length:16},(_,i)=>2**i)]])
  assert.deepEqual(values.map((_,i)=>e.actual_at(which,i)),values.map(BigInt));
console.log('all static scalar bindings executed');
"#;

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "prod-static-bindings-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained failing static-list fixture: {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}
fn succeeds(command: &mut Command) {
    let result = command.output().unwrap();
    assert!(
        result.status.success(),
        "{command:?}\n{}\n{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn scalar_bound_static_lists_execute_in_native_std_no_std_and_wasm() {
    let (remaining, mut module) = parse_module(IR).unwrap();
    assert!(remaining.is_empty());
    let actual_ir = include_str!("fixtures/p256_static_lcnf.ir");
    let (remaining, actual_module) = parse_module(actual_ir).unwrap();
    assert!(remaining.is_empty());
    assert_eq!(actual_module.definitions.len(), 4);
    module.definitions.extend(actual_module.definitions);
    let spec = CargoPackageSpec {
        name: "static-bindings-fixture".into(),
        version: "0.1.0".into(),
        description: "Static scalar binding regression".into(),
        repository: "https://github.com/auser/lean4-prod".into(),
        homepage: "https://github.com/auser/lean4-prod".into(),
        readme: "Static scalar binding regression.\n".into(),
        license_mit: "MIT\n".into(),
        license_apache: "Apache-2.0\n".into(),
        input_sha256: format!(
            "{:x}",
            Sha256::digest([IR.as_bytes(), actual_ir.as_bytes()].concat())
        ),
        dependencies: vec![],
    };
    let package = generate_cargo_package(&module, &spec).unwrap();
    assert_eq!(package, generate_cargo_package(&module, &spec).unwrap());
    let scratch = Scratch::new();
    for file in package.files {
        let path = scratch.0.join(file.path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, file.bytes).unwrap();
    }
    let generated = fs::read_to_string(scratch.0.join("src/lib.rs")).unwrap();
    assert!(generated.contains("&'static [u64]"));
    assert!(!generated.contains("Vec"));
    fs::write(scratch.0.join("runner.rs"), RUNNER).unwrap();
    fs::write(scratch.0.join("wasm.rs"), WASM_WRAPPER).unwrap();
    fs::write(scratch.0.join("wasm.mjs"), WASM_TEST).unwrap();
    for standard in [true, false] {
        for optimized in [false, true] {
            let library = scratch
                .0
                .join(format!("libstatic_{standard}_{optimized}.rlib"));
            let mut command = Command::new("rustc");
            command.args([
                "--edition=2021",
                "--crate-type=rlib",
                "--crate-name=static_bindings_fixture",
            ]);
            if standard {
                command.args(["--cfg", "feature=\"std\""]);
            }
            if optimized {
                command.args(["-C", "opt-level=3", "-C", "overflow-checks=yes"]);
            }
            succeeds(
                command
                    .arg(scratch.0.join("src/lib.rs"))
                    .arg("-o")
                    .arg(&library),
            );
            let runner = scratch.0.join(format!("runner_{standard}_{optimized}"));
            succeeds(
                Command::new("rustc")
                    .arg("--edition=2021")
                    .arg(scratch.0.join("runner.rs"))
                    .arg("--extern")
                    .arg(format!("static_bindings_fixture={}", library.display()))
                    .arg("-o")
                    .arg(&runner),
            );
            succeeds(&mut Command::new(runner));
        }
        let library = scratch.0.join(format!("libwasm_{standard}.rlib"));
        let mut command = Command::new("rustc");
        command.args([
            "--edition=2021",
            "--target=wasm32-unknown-unknown",
            "--crate-type=rlib",
            "--crate-name=static_bindings_fixture",
        ]);
        if standard {
            command.args(["--cfg", "feature=\"std\""]);
        }
        succeeds(
            command
                .arg(scratch.0.join("src/lib.rs"))
                .arg("-o")
                .arg(&library),
        );
        let artifact = scratch.0.join(format!("fixture_{standard}.wasm"));
        succeeds(
            Command::new("rustc")
                .args([
                    "--edition=2021",
                    "--target=wasm32-unknown-unknown",
                    "--crate-type=cdylib",
                ])
                .arg(scratch.0.join("wasm.rs"))
                .arg("--extern")
                .arg(format!("static_bindings_fixture={}", library.display()))
                .arg("-o")
                .arg(&artifact),
        );
        succeeds(
            Command::new("node")
                .arg(scratch.0.join("wasm.mjs"))
                .arg(artifact),
        );
    }
}

#[test]
fn scalar_static_bindings_refuse_computation_bad_scope_and_wrong_type_or_range() {
    for (element, body) in [
        (
            "Nat",
            "(let x (add 1 2) (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x (sub 2 1) (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x absent (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x x (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x true (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Bool",
            "(let x 1 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x -1 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "UInt8",
            "(let x 256 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Int8",
            "(let x -129 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Int8",
            "(let x 128 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "UInt16",
            "(let x 65536 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "UInt32",
            "(let x 4294967296 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Int64",
            "(let x 9223372036854775808 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "UInt64",
            "(let x -1 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x -0 (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x 1 (ctor \"List.cons\" (sub x 0) (ctor \"List.nil\")))",
        ),
        (
            "Nat",
            "(let x (ctor \"List.nil\") (ctor \"List.cons\" x (ctor \"List.nil\")))",
        ),
        ("Nat", "(let x 1 (ctor \"List.cons\" x x))"),
        ("Nat", "(let xs (ctor \"List.nil\") (let xs 1 xs))"),
        (
            "Nat",
            "(let xs (ctor \"List.cons\" future (ctor \"List.nil\")) (let future 1 xs))",
        ),
        (
            "Nat",
            "(let xs (ctor \"List.cons\" 1 future) (let future (ctor \"List.nil\") xs))",
        ),
        (
            "Nat",
            "(let x 1 (let x (ctor \"List.nil\") (ctor \"List.cons\" x (ctor \"List.nil\"))))",
        ),
    ] {
        let input = format!("(module M (def value () (List {element}) {body}))");
        let (remaining, module) = parse_module(&input).unwrap();
        assert!(remaining.is_empty());
        assert!(
            matches!(generate_module(&module), Err(Error::UnsupportedList(_))),
            "{input}"
        );
    }
}
