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
  (type "ParcelList" (ctor "ParcelList.mk" (slots (List (named "Parcel")))))
  (def empty_order () Ordering (compare-bytes (bytes) (bytes)))
  (def aliased_empty_order () Ordering
    (let empty (bytes) (compare-bytes empty empty)))
  (def literal_order () Ordering (compare-bytes (bytes 0 255) (bytes 128)))
  (def empty_left ((input Bytes)) Ordering (compare-bytes (bytes) input))
  (def empty_right ((input Bytes)) Ordering (compare-bytes input (bytes)))
  (def join_failure_order ((input Nat)) Nat
    (let continuation (jp continuation (first second) 0)
      (jmp continuation (add input 1) (mul input 2))))
  (def panic_value () Nat (unreachable))
  (def join_panic () Nat
    (let continuation (jp continuation (unused) 7)
      (jmp continuation (unreachable))))
  (def join_called_panic () Nat
    (let continuation (jp continuation (unused) 7)
      (jmp continuation (call panic_value))))
  (def join_panic_before_error ((input Nat)) Nat
    (let continuation (jp continuation (first second) 7)
      (jmp continuation (unreachable) (add input 1))))
  (def join_error_before_panic ((input Nat)) Nat
    (let continuation (jp continuation (first second) 7)
      (jmp continuation (add input 1) (unreachable))))
  (def unused_let_panic () Nat (let unused (call panic_value) 7))
  (def join_conditional_panic ((fail Bool)) Nat
    (let continuation (jp continuation (unused) 7)
      (jmp continuation (if fail (unreachable) 0))))
  (def join_once ((input Nat)) Nat
    (let continuation (jp continuation (value) (add value value))
      (jmp continuation (ctor "counted_value" input))))
  (def join_unused_order () Nat
    (let continuation (jp continuation (first second) 7)
      (jmp continuation (ctor "counted_value" 1) (ctor "counted_value" 2))))
  (def join_partial_failure ((input Nat)) Nat
    (let continuation (jp continuation (first second third) 7)
      (jmp continuation (ctor "counted_value" 1) (add input 1) (ctor "counted_value" 2))))
  (def borrowed_head ((input (List (named "Parcel")))) (Option (named "Parcel"))
    (cases input
      (alt "List.nil" () (ctor "Option.none"))
      (alt "List.cons" (head tail) (ctor "Option.some" head))))
  (def borrowed_rebuild ((input (List (named "Parcel")))) (named "ParcelList")
    (cases input
      (alt "List.nil" () (ctor "ParcelList.mk" (ctor "List.nil")))
      (alt "List.cons" (head tail)
        (ctor "ParcelList.mk" (ctor "List.cons" head tail)))))
  (def borrowed_prepend ((head (named "Parcel")) (tail (List (named "Parcel")))) (named "ParcelList")
    (ctor "ParcelList.mk" (ctor "List.cons" head tail)))
  (def borrowed_projected_tail ((head (named "Parcel")) (tail (named "ParcelList"))) (named "ParcelList")
    (let slots (proj "ParcelList" "slots" tail)
      (ctor "ParcelList.mk" (ctor "List.cons" head slots))))
  (def owned_list ((head (Option (named "Parcel"))) (tail (Option (List (named "Parcel"))))) (Option (named "ParcelList"))
    (cases head
      (alt "Option.none" () (ctor "Option.none"))
      (alt "Option.some" (item)
        (cases tail
          (alt "Option.none" () (ctor "Option.none"))
          (alt "Option.some" (items)
            (ctor "Option.some" (ctor "ParcelList.mk" (ctor "List.cons" item items))))))))
  (def owned_singleton ((input (Option (named "Parcel")))) (Option (named "ParcelList"))
    (cases input
      (alt "Option.none" () (ctor "Option.none"))
      (alt "Option.some" (head)
        (ctor "Option.some" (ctor "ParcelList.mk" (ctor "List.cons" head (ctor "List.nil")))))))
  (def mixed_join ((input (List (named "Parcel"))) (replacement Bytes) (choose Bool)) (Option (named "ParcelList"))
    (cases input
      (alt "List.nil" () (ctor "Option.none"))
      (alt "List.cons" (head tail)
        (let continuation
          (jp continuation (item)
            (let alias item
              (ctor "Option.some" (ctor "ParcelList.mk" (ctor "List.cons" alias tail)))))
          (if choose
            (jmp continuation (ctor "Parcel.mk" replacement 42))
            (jmp continuation head))))))
  (def nested_join ((input (named "Parcel"))) (Option (named "Parcel"))
    (let outer
      (jp outer (item)
        (let alias item
          (let inner (jp inner (value) (ctor "Option.some" value))
            (jmp inner alias))))
      (jmp outer input)))
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
        assert_eq!(empty_left(expected.clone()), [].as_slice().cmp(expected.as_slice()));
        assert_eq!(empty_right(expected.clone()), expected.as_slice().cmp(&[]));
        cases += 2;
        let slots = vec![parcel(expected.clone(), 11), parcel(vec![254], 12)];
        let mut output = borrowed_head(&slots).unwrap();
        assert_eq!(output, slots[0]);
        output.bytes.push(255);
        assert_eq!(slots[0].bytes, expected);

        let mut output = borrowed_rebuild(&slots);
        assert_eq!(output.slots, slots);
        output.slots[0].bytes.push(255);
        output.slots[1].bytes.push(255);
        assert_eq!(slots[0].bytes, expected);
        assert_eq!(slots[1].bytes, [254]);

        let head = parcel(vec![253], 13);
        let mut output = nested_join(&head).unwrap();
        assert_eq!(output, head);
        output.bytes.push(255);
        assert_eq!(head.bytes, [253]);
        for choose in [false, true] {
            let replacement = vec![251; size + 1];
            let pointer = replacement.as_ptr();
            let mut output = mixed_join(&slots, replacement, choose).unwrap();
            assert_eq!(output.slots.len(), slots.len());
            if choose {
                assert_eq!(output.slots[0].bytes, vec![251; size + 1]);
                assert_eq!(output.slots[0].marker, 42);
                assert_eq!(output.slots[0].bytes.as_ptr(), pointer, "owned join argument moves");
            } else {
                assert_eq!(output.slots[0], slots[0]);
            }
            output.slots[0].bytes.push(255);
            assert_eq!(slots[0].bytes, expected);
            assert_eq!(output.slots[1], slots[1]);
        }
        cases += 3;
        let mut output = borrowed_prepend(&head, &slots);
        assert_eq!(output.slots, [vec![head.clone()], slots.clone()].concat());
        output.slots[0].bytes.push(255);
        output.slots[1].bytes.push(255);
        assert_eq!(head.bytes, [253]);
        assert_eq!(slots[0].bytes, expected);

        let list = ParcelList { slots };
        let mut output = borrowed_projected_tail(&head, &list);
        assert_eq!(output.slots, [vec![head.clone()], list.slots.clone()].concat());
        output.slots[2].bytes.push(255);
        assert_eq!(list.slots[1].bytes, [254]);

        let mut tail = Vec::with_capacity(4);
        tail.push(parcel(vec![252], 14));
        let list_pointer = tail.as_ptr();
        let tail_pointer = tail[0].bytes.as_ptr();
        let head = parcel(expected.clone(), 11);
        let head_pointer = head.bytes.as_ptr();
        let output = owned_list(Some(head), Some(tail)).unwrap();
        assert_eq!(output.slots.len(), 2);
        assert_eq!(output.slots[0].bytes, expected);
        assert_eq!(output.slots[1].bytes, [252]);
        assert_eq!(output.slots.as_ptr(), list_pointer, "owned list capacity is reused");
        assert_eq!(output.slots[1].bytes.as_ptr(), tail_pointer, "owned tail item moves");
        if size != 0 {
            assert_eq!(output.slots[0].bytes.as_ptr(), head_pointer, "owned head moves");
        }

        let head = parcel(expected.clone(), 11);
        let head_pointer = head.bytes.as_ptr();
        let output = owned_singleton(Some(head)).unwrap();
        assert_eq!(output.slots.len(), 1);
        assert_eq!(output.slots[0].bytes, expected);
        if size != 0 {
            assert_eq!(output.slots[0].bytes.as_ptr(), head_pointer, "singleton moves its item");
        }
        cases += 6;
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
    assert!(borrowed_head(&[]).is_none());
    assert!(borrowed_rebuild(&[]).slots.is_empty());
    assert!(owned_list(None, None).is_none());
    assert!(owned_singleton(None).is_none());
    cases += 4;
    assert_eq!(empty_order(), core::cmp::Ordering::Equal);
    assert_eq!(aliased_empty_order(), core::cmp::Ordering::Equal);
    assert_eq!(literal_order(), core::cmp::Ordering::Less);
    cases += 3;
    assert!(mixed_join(&[], vec![1], true).is_none());
    cases += 1;
    assert_eq!(join_failure_order(0), Ok(0));
    assert_eq!(join_failure_order(u64::MAX), Err(ComputeError::AddOverflow));
    cases += 2;
    assert!(std::panic::catch_unwind(join_panic).is_err());
    assert!(std::panic::catch_unwind(join_called_panic).is_err());
    assert!(std::panic::catch_unwind(|| join_panic_before_error(u64::MAX)).is_err());
    assert_eq!(join_error_before_panic(u64::MAX), Err(ComputeError::AddOverflow));
    assert!(std::panic::catch_unwind(|| join_error_before_panic(0)).is_err());
    assert!(std::panic::catch_unwind(unused_let_panic).is_err());
    assert_eq!(join_conditional_panic(false), 7);
    assert!(std::panic::catch_unwind(|| join_conditional_panic(true)).is_err());
    cases += 8;
    reset_evaluation_probe();
    assert_eq!(join_once(5), Ok(10));
    assert_eq!((evaluation_calls(), evaluation_order()), (1, 5));
    reset_evaluation_probe();
    assert_eq!(join_unused_order(), 7);
    assert_eq!((evaluation_calls(), evaluation_order()), (2, 12));
    reset_evaluation_probe();
    assert_eq!(join_partial_failure(u64::MAX), Err(ComputeError::AddOverflow));
    assert_eq!((evaluation_calls(), evaluation_order()), (1, 1));
    reset_evaluation_probe();
    assert_eq!(join_partial_failure(0), Ok(7));
    assert_eq!((evaluation_calls(), evaluation_order()), (2, 12));
    cases += 4;
    assert_eq!(cases, 145);
    println!("owned projection safety: {cases} cases passed");
}
"#;

// Test-only instrumentation for the compiler's documented bare host-constructor
// boundary. It observes evaluation count/order without changing generated IR
// or supplying application behavior, and also compiles in a no_std library.
const EVALUATION_PROBE: &str = r#"
static EVALUATION_CALLS: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
static EVALUATION_ORDER: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
pub fn reset_evaluation_probe() {
    EVALUATION_CALLS.store(0, core::sync::atomic::Ordering::SeqCst);
    EVALUATION_ORDER.store(0, core::sync::atomic::Ordering::SeqCst);
}
pub fn evaluation_calls() -> usize { EVALUATION_CALLS.load(core::sync::atomic::Ordering::SeqCst) }
pub fn evaluation_order() -> usize { EVALUATION_ORDER.load(core::sync::atomic::Ordering::SeqCst) }
fn counted_value(value: u64) -> u64 {
    EVALUATION_CALLS.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
    EVALUATION_ORDER.store(evaluation_order() * 10 + value as usize, core::sync::atomic::Ordering::SeqCst);
    value
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
    for mut file in package.files {
        if file.path == "src/lib.rs" {
            file.bytes.extend_from_slice(EVALUATION_PROBE.as_bytes());
        }
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
                "owned projection safety: 145 cases passed\n"
            );
        }
    }
}
