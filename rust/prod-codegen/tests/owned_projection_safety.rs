//! Execute ownership-sensitive projections through the public raw-IR boundary.

use prod_codegen::{generate_cargo_package, CargoPackageSpec};
use prod_ir::parser::parse_module;
use sha2::{Digest, Sha256};
use std::path::PathBuf;
use std::process::Command;

const IR: &str = r#"(module OwnedProjectionSafety
  (type "Parcel" (ctor "Parcel.mk" (bytes Bytes) (marker Nat)))
  (type "Envelope" (ctor "Envelope.mk" (parcel (named "Parcel")) (label String)))
  (type "MaybeEnvelope" (ctor "MaybeEnvelope.mk" (parcel (Option (named "Parcel")))))
  (type "Pair" (ctor "Pair.mk" (first Bytes) (second Bytes)))
  (type "OptionalPair" (ctor "OptionalPair.mk" (first (Option Bytes)) (second (Option Bytes))))
  (def nested_owned ((input (Option (named "Envelope")))) (Option (named "Pair"))
    (cases input
      (alt "Option.none" () (ctor "Option.none"))
      (alt "Option.some" (outer)
        (let inner (proj "Envelope" "parcel" outer)
          (let label (proj "Envelope" "label" outer)
            (let bytes (proj "Parcel" "bytes" inner)
              (let marker (proj "Parcel" "marker" inner)
                (if (eq marker 11)
                  (ctor "Option.some" (ctor "Pair.mk" bytes (utf8-encode label)))
                  (ctor "Option.none")))))))))
  (def borrowed_optional ((input (named "MaybeEnvelope"))) (Option Bytes)
    (let optional (proj "MaybeEnvelope" "parcel" input)
      (cases optional
        (alt "Option.none" () (ctor "Option.none"))
        (alt "Option.some" (inner)
          (ctor "Option.some" (proj "Parcel" "bytes" inner))))))
  (def borrowed_named ((input (named "Envelope"))) (named "Pair")
    (let inner (proj "Envelope" "parcel" input)
      (let label (proj "Envelope" "label" input)
        (ctor "Pair.mk" (proj "Parcel" "bytes" inner) (utf8-encode label)))))
  (def mixed_match ((input (Option (named "Parcel"))) (fallback (named "Parcel"))) (Option Bytes)
    (let selected
      (cases input
        (alt "Option.none" () (proj "Parcel" "bytes" fallback))
        (alt "Option.some" (inner) (proj "Parcel" "bytes" inner)))
      (ctor "Option.some" selected)))
  (def captured_join ((input Bytes)) (named "OptionalPair")
    (let owner (ctor "Parcel.mk" input 11)
      (let continuation
        (jp continuation () (ctor "Option.some" (proj "Parcel" "bytes" owner)))
        (let first (jmp continuation)
          (let second (jmp continuation)
            (ctor "OptionalPair.mk" first second))))))
  (def borrowed_join ((input (named "Parcel"))) (Option Bytes)
    (let continuation
      (jp continuation (row) (ctor "Option.some" (proj "Parcel" "bytes" row)))
      (jmp continuation input)))
  (def positional_shadow ((row (named "Parcel")) (input (Option (named "Parcel")))) (Option (named "Pair"))
    (cases input
      (alt "Option.none" () (ctor "Option.none"))
      (alt "Option.some" (row)
        (let original (proj "Parcel" "bytes" (param 0))
          (let selected (proj "Parcel" "bytes" row)
            (ctor "Option.some" (ctor "Pair.mk" original selected)))))))
  (def nested_shadow ((input (Option (named "Envelope")))) (Option Bytes)
    (cases input
      (alt "Option.none" () (ctor "Option.none"))
      (alt "Option.some" (row)
        (let row (proj "Envelope" "parcel" row)
          (let row (proj "Parcel" "bytes" row)
            (ctor "Option.some" row)))))))"#;

const RUNNER: &str = r#"use owned_projection_safety_fixture::*;

fn parcel(bytes: Vec<u8>, marker: u64) -> Parcel {
    Parcel { bytes, marker }
}

fn main() {
    let mut cases = 0;
    for size in [0, 1, 128, 8192] {
        let expected: Vec<u8> = (0..size).map(|index| (index % 251) as u8).collect();
        for label in ["", "parcel", "🌱\0é"] {
            let bytes = expected.clone();
            let pointer = bytes.as_ptr();
            let label_value = label.to_owned();
            let label_pointer = label_value.as_ptr();
            let output = nested_owned(Some(Envelope {
                parcel: parcel(bytes, 11), label: label_value,
            })).unwrap();
            assert_eq!(output.first, expected);
            assert_eq!(output.second, label.as_bytes());
            if !expected.is_empty() {
                assert_eq!(output.first.as_ptr(), pointer, "nested field keeps its allocation");
            }
            if !label.is_empty() {
                assert_eq!(output.second.as_ptr(), label_pointer, "disjoint String field moves too");
            }
            assert!(nested_owned(Some(Envelope {
                parcel: parcel(expected.clone(), 12), label: label.to_owned(),
            })).is_none());

            let borrowed = Envelope {
                parcel: parcel(expected.clone(), 11), label: label.to_owned(),
            };
            let mut output = borrowed_named(&borrowed);
            assert_eq!(output.first, expected);
            assert_eq!(output.second, label.as_bytes());
            output.first.push(255);
            output.second.push(255);
            assert_eq!(borrowed.parcel.bytes, expected);
            assert_eq!(borrowed.label, label);
            assert_eq!(borrowed_named(&borrowed).first, expected);

            let bytes = expected.clone();
            let pointer = bytes.as_ptr();
            let output = nested_shadow(Some(Envelope {
                parcel: parcel(bytes, 11), label: label.to_owned(),
            })).unwrap();
            assert_eq!(output, expected);
            if !expected.is_empty() {
                assert_eq!(output.as_ptr(), pointer, "normalized inner binders retain ownership");
            }
            cases += 4;
        }

        let borrowed = MaybeEnvelope { parcel: Some(parcel(expected.clone(), 11)) };
        let mut output = borrowed_optional(&borrowed).unwrap();
        assert_eq!(output, expected);
        output.push(255);
        assert_eq!(borrowed.parcel.as_ref().unwrap().bytes, expected);
        assert_eq!(borrowed_optional(&borrowed).unwrap(), expected);

        let fallback_bytes = vec![254; size + 1];
        let fallback = parcel(fallback_bytes.clone(), 11);
        let bytes = expected.clone();
        let pointer = bytes.as_ptr();
        let output = mixed_match(Some(parcel(bytes, 11)), &fallback).unwrap();
        assert_eq!(output, expected);
        if !expected.is_empty() {
            assert_eq!(output.as_ptr(), pointer, "owned Match arm moves its field");
        }
        let mut output = mixed_match(None, &fallback).unwrap();
        assert_eq!(output, fallback_bytes);
        output.push(255);
        assert_eq!(fallback.bytes, fallback_bytes);

        let mut output = captured_join(expected.clone());
        assert_eq!(output.first.as_deref(), Some(expected.as_slice()));
        assert_eq!(output.second.as_deref(), Some(expected.as_slice()));
        output.first.as_mut().unwrap().push(255);
        assert_eq!(output.second.as_deref(), Some(expected.as_slice()));

        let borrowed = parcel(expected.clone(), 11);
        let mut output = borrowed_join(&borrowed).unwrap();
        assert_eq!(output, expected);
        output.push(255);
        assert_eq!(borrowed.bytes, expected);

        let bytes = expected.clone();
        let pointer = bytes.as_ptr();
        let mut output = positional_shadow(&fallback, Some(parcel(bytes, 11))).unwrap();
        assert_eq!(output.first, fallback_bytes);
        assert_eq!(output.second, expected);
        if !expected.is_empty() {
            assert_eq!(output.second.as_ptr(), pointer, "shadowing does not borrow the owned payload");
        }
        output.first.push(255);
        assert_eq!(fallback.bytes, fallback_bytes);
        assert!(positional_shadow(&fallback, None).is_none());
        cases += 7;
    }
    assert!(nested_owned(None).is_none());
    assert!(nested_shadow(None).is_none());
    assert!(borrowed_optional(&MaybeEnvelope { parcel: None }).is_none());
    cases += 3;
    assert_eq!(cases, 79);
    println!("owned projection safety: {cases} cases passed");
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
            "prod-owned-projection-safety-{}-{nonce}",
            std::process::id()
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained failing generated fixture: {}", self.0.display());
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
fn owned_projection_safety_executes_in_std_and_no_std_debug_and_optimized() {
    let (remaining, module) = parse_module(IR).unwrap();
    assert!(remaining.is_empty(), "the complete fixture must parse");
    let spec = CargoPackageSpec {
        name: "owned-projection-safety-fixture".into(),
        version: "0.1.0".into(),
        description: "Owned projection safety regression".into(),
        repository: "https://github.com/auser/lean4-prod".into(),
        homepage: "https://github.com/auser/lean4-prod".into(),
        readme: "Owned projection safety regression fixture.\n".into(),
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
                "--crate-name=owned_projection_safety_fixture",
            ]);
            if standard {
                compiler.args(["--cfg", "feature=\"std\""]);
            }
            if optimized {
                compiler.args(["-C", "opt-level=3", "-C", "overflow-checks=yes"]);
            }
            succeeds(
                compiler
                    .arg(scratch.0.join("src/lib.rs"))
                    .arg("-o")
                    .arg(&library),
            );
            let executable = scratch.0.join(format!("runner_{standard}_{optimized}"));
            let mut runner_compiler = Command::new("rustc");
            runner_compiler.arg("--edition=2021");
            if optimized {
                runner_compiler.args(["-C", "opt-level=3", "-C", "overflow-checks=yes"]);
            }
            succeeds(
                runner_compiler
                    .arg(&runner)
                    .arg("--extern")
                    .arg(format!(
                        "owned_projection_safety_fixture={}",
                        library.display()
                    ))
                    .arg("-o")
                    .arg(&executable),
            );
            assert_eq!(
                succeeds(&mut Command::new(&executable)),
                "owned projection safety: 79 cases passed\n"
            );
        }
    }
}
