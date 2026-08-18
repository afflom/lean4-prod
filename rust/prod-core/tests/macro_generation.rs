#![allow(non_snake_case)] // generated code mirrors Lean definition names

//! The generated definitions, exercised against the Lean-computed goldens.
//!
//! Every test returns `Result<(), ComputeError>` and propagates with `?`
//! rather than unwrapping: the generated functions are fallible by contract,
//! and the tests should read the way real callers are expected to.

use prod_core::{
    belt, classDecode, classIndex, class_count, digitCount, digitSum, digits, sameClass,
    smallEnough, stride, tryClassDecode, ComputeError, Instance,
};

// Golden values computed by the compiled Lean kernel defs (lake exe
// prod-export → goldens.ir, next to prod-core's Cargo.toml). Same IR module
// format, consumed through the same macro — nothing hand-written downstream.
prod_macros::prod_defs! { ir = "goldens.ir" }

// `Instance` carries an invariant, so its fields are `pub(crate)` and this is
// an integration test — external to the crate. The three shared instances used
// to be `const`s; a `const` cannot call a fallible constructor, so each test
// now builds its own with `Instance::new(..)?` and reads fields through the
// generated accessors. `prod-core` denies `unwrap_used`/`expect_used`/`panic`
// in test targets too, so `?` is the only option here.

/// Digits of a `u64` in any of the TF1 bases fit comfortably in 64 slots.
const DIGIT_CAPACITY: usize = 64;

#[test]
fn checked_constructor_accepts_valid_and_rejects_each_violation() -> Result<(), ComputeError> {
    // Lean proves `q >= 1 /\ T >= 1 /\ O >= 1` for every Instance it builds.
    // The generated constructor re-checks exactly that at the crate boundary.
    //
    // This is the only place in the repo that EXECUTES the lowered invariant
    // against the real `kernel.ir` rather than reading the exported text. A
    // comparison lowered with reversed operands compiles, returns a `bool`,
    // and rejects exactly the inputs it should accept; only running it tells
    // the two apart.
    assert!(Instance::new(4, 3, 8).is_ok());
    assert!(
        Instance::new(1, 1, 1).is_ok(),
        "the boundary itself is valid"
    );

    // One violated conjunct at a time, so a constructor that checked only the
    // first field — or that lowered a comparison backwards — fails here rather
    // than passing on a lucky combination.
    for (q, t, o) in [(0, 3, 8), (4, 0, 8), (4, 3, 0)] {
        assert_eq!(
            Instance::new(q, t, o),
            Err(ComputeError::InvariantViolated("UorAtlas.Instance")),
            "Instance::new({}, {}, {}) must be rejected",
            q,
            t,
            o
        );
    }
    // `Instance`'s three conjuncts all point the same direction, so it cannot
    // distinguish a blanket operand swap from a correct per-operator one.
    // `Conformance.MixedCompare` carries that half of the test — see
    // `rust/prod-codegen-compile-tests/tests/smoke.rs`.
    Ok(())
}

#[test]
fn generated_definitions_compile_and_run() -> Result<(), ComputeError> {
    let canonical = Instance::new(4, 3, 8)?;
    assert_eq!(classIndex(1, 2, 3, canonical)?, 43);
    assert_eq!(stride(canonical)?, 24);
    assert_eq!(class_count(canonical)?, 96);
    assert_eq!(belt(canonical)?, 12_288);
    assert_eq!(classDecode(43, canonical)?, (1, (2, 3)));
    // Recursive def: 43 = 5·8+5 is two base-8 digits; fuel 0 short-circuits.
    assert_eq!(digitCount(10, 43, canonical)?, 2);
    assert_eq!(digitCount(10, 511, canonical)?, 3);
    assert_eq!(digitCount(0, 999, canonical)?, 0);
    // List defs write into a caller-owned buffer and report the prefix length;
    // digits of 43 in base 8 are [3, 5] (least-significant first).
    let mut buffer = [0u64; DIGIT_CAPACITY];
    let len = digits(10, 43, canonical, &mut buffer)?;
    assert_eq!(written(&buffer, len), &[3, 5]);
    assert_eq!(digitSum(written(&buffer, len))?, 8);
    // Decidable guards: 43//24 = 44//24 = 1 but 67//24 = 2; belt = 12288.
    assert!(sameClass(43, 44, canonical)?);
    assert!(!sameClass(43, 67, canonical)?);
    assert!(smallEnough(100, canonical)?);
    assert!(!smallEnough(20_000, canonical)?);
    // Option def: 43 < class_count 96 decodes; 100 is out of range.
    assert_eq!(tryClassDecode(43, canonical)?, Some((1, (2, 3))));
    assert_eq!(tryClassDecode(100, canonical)?, None);
    Ok(())
}

#[test]
fn list_builder_reports_an_undersized_buffer_instead_of_panicking() -> Result<(), ComputeError> {
    let canonical = Instance::new(4, 3, 8)?;
    // 43 needs two base-8 digits; one slot is not enough. The generated code
    // splits the buffer rather than indexing it, so exhaustion is an `Err`,
    // never an out-of-bounds panic.
    let mut too_small = [0u64; 1];
    assert_eq!(
        digits(10, 43, canonical, &mut too_small),
        Err(ComputeError::OutputTooSmall)
    );
    let mut empty: [u64; 0] = [];
    assert_eq!(
        digits(10, 43, canonical, &mut empty),
        Err(ComputeError::OutputTooSmall)
    );
    // An exactly-sized buffer succeeds.
    let mut exact = [0u64; 2];
    assert_eq!(digits(10, 43, canonical, &mut exact), Ok(2));
    assert_eq!(exact, [3, 5]);
    Ok(())
}

#[test]
fn arithmetic_overflow_is_reported_not_panicked() -> Result<(), ComputeError> {
    // `belt = class_count · 2^(O-1)`: an instance with a huge O overflows the
    // power, and an enormous q overflows the class-count multiplication.
    // Both must surface as errors — this is the DoS surface the standard
    // cares about, since these are caller-controlled inputs.
    // Both satisfy the invariant (every field is >= 1), so `new` accepts them;
    // it is the arithmetic downstream that overflows, which is the point.
    let wide = Instance::new(1, 1, 70)?;
    assert_eq!(belt(wide), Err(ComputeError::PowOverflow));
    let huge = Instance::new(u64::MAX, 2, 2)?;
    assert_eq!(stride(huge), Ok(4));
    assert_eq!(class_count(huge), Err(ComputeError::MulOverflow));
    Ok(())
}

#[test]
fn golden_values_are_the_hand_checked_tf1_numbers() {
    // Hand-checked: stride = T·O, class_count = q·stride, belt = class_count·2^(O-1),
    // classIndex(h2,d,l) = stride·h2 + O·d + l.
    // Goldens are constant, so they stay infallible — the fallibility fixpoint
    // does not spread `Result` to definitions that cannot fail.
    assert_eq!(golden_stride_canonical(), 24);
    assert_eq!(golden_class_count_canonical(), 96);
    assert_eq!(golden_belt_canonical(), 12_288);
    assert_eq!(golden_stride_demo_small(), 8);
    assert_eq!(golden_class_count_demo_small(), 16);
    assert_eq!(golden_belt_demo_small(), 128);
    assert_eq!(golden_stride_third(), 3);
    assert_eq!(golden_class_count_third(), 15);
    assert_eq!(golden_belt_third(), 60);
    assert_eq!(golden_classIndex_1_2_3_canonical(), 43);
    assert_eq!(golden_classDecode_43_canonical(), (1, (2, 3)));
    assert_eq!(golden_digitCount_43_canonical(), 2);
    assert_eq!(golden_digitCount_511_canonical(), 3);
    assert_eq!(golden_digitCount_zero_fuel_canonical(), 0);
    // A zero-argument list golden is a promoted `&'static [u64]` — no heap,
    // no buffer parameter.
    assert_eq!(golden_digits_43_canonical(), &[3, 5]);
    assert_eq!(golden_digitSum_digits_43_canonical(), 8);
    assert!(golden_sameClass_43_44_canonical());
    assert!(!golden_sameClass_43_67_canonical());
    assert!(golden_smallEnough_100_canonical());
    assert!(!golden_smallEnough_20000_canonical());
    assert_eq!(golden_tryClassDecode_43_canonical(), Some((1, (2, 3))));
    assert_eq!(golden_tryClassDecode_100_canonical(), None);
}

#[test]
fn generated_definitions_match_lean_goldens() -> Result<(), ComputeError> {
    let canonical = Instance::new(4, 3, 8)?;
    let demo_small = Instance::new(2, 2, 4)?;
    let third = Instance::new(5, 1, 3)?;
    for (inst, g_stride, g_class_count, g_belt) in [
        (
            canonical,
            golden_stride_canonical(),
            golden_class_count_canonical(),
            golden_belt_canonical(),
        ),
        (
            demo_small,
            golden_stride_demo_small(),
            golden_class_count_demo_small(),
            golden_belt_demo_small(),
        ),
        (
            third,
            golden_stride_third(),
            golden_class_count_third(),
            golden_belt_third(),
        ),
    ] {
        assert_eq!(stride(inst)?, g_stride);
        assert_eq!(class_count(inst)?, g_class_count);
        assert_eq!(belt(inst)?, g_belt);
    }
    assert_eq!(
        classIndex(1, 2, 3, canonical)?,
        golden_classIndex_1_2_3_canonical()
    );
    assert_eq!(
        classDecode(43, canonical)?,
        golden_classDecode_43_canonical()
    );
    assert_eq!(
        digitCount(10, 43, canonical)?,
        golden_digitCount_43_canonical()
    );
    assert_eq!(
        digitCount(10, 511, canonical)?,
        golden_digitCount_511_canonical()
    );
    assert_eq!(
        digitCount(0, 999, canonical)?,
        golden_digitCount_zero_fuel_canonical()
    );
    let mut buffer = [0u64; DIGIT_CAPACITY];
    let len = digits(10, 43, canonical, &mut buffer)?;
    assert_eq!(written(&buffer, len), golden_digits_43_canonical());
    assert_eq!(
        digitSum(written(&buffer, len))?,
        golden_digitSum_digits_43_canonical()
    );
    assert_eq!(
        sameClass(43, 44, canonical)?,
        golden_sameClass_43_44_canonical()
    );
    assert_eq!(
        sameClass(43, 67, canonical)?,
        golden_sameClass_43_67_canonical()
    );
    assert_eq!(
        smallEnough(100, canonical)?,
        golden_smallEnough_100_canonical()
    );
    assert_eq!(
        smallEnough(20_000, canonical)?,
        golden_smallEnough_20000_canonical()
    );
    assert_eq!(
        tryClassDecode(43, canonical)?,
        golden_tryClassDecode_43_canonical()
    );
    assert_eq!(
        tryClassDecode(100, canonical)?,
        golden_tryClassDecode_100_canonical()
    );
    Ok(())
}

#[test]
fn generated_definitions_roundtrip_lean_examples() -> Result<(), ComputeError> {
    let canonical = Instance::new(4, 3, 8)?;
    let demo_small = Instance::new(2, 2, 4)?;
    let third = Instance::new(5, 1, 3)?;
    for inst in [canonical, demo_small, third] {
        // Fields are `pub(crate)` now; external readers go through accessors.
        for h2 in 0..inst.q() {
            for d in 0..inst.T() {
                for l in 0..inst.O() {
                    let idx = classIndex(h2, d, l, inst)?;
                    assert_eq!(classDecode(idx, inst)?, (h2, (d, l)));
                }
            }
        }
    }
    Ok(())
}

#[test]
fn decode_encode_roundtrip_full_index_sweep() -> Result<(), ComputeError> {
    let canonical = Instance::new(4, 3, 8)?;
    let demo_small = Instance::new(2, 2, 4)?;
    let third = Instance::new(5, 1, 3)?;
    // decode∘encode is the identity on every valid index of each instance.
    for inst in [canonical, demo_small, third] {
        for idx in 0..class_count(inst)? {
            let (h2, (d, l)) = classDecode(idx, inst)?;
            assert_eq!(classIndex(h2, d, l, inst)?, idx);
        }
    }
    Ok(())
}

/// The initialized prefix of a list builder's output buffer, taken without an
/// index.
///
/// `prod-core` denies `clippy::indexing_slicing`: the rule that keeps a panic
/// path out of the generated writer keeps one out of the test that exercises
/// it too, so this returns the empty prefix rather than panicking on a `len`
/// the buffer cannot cover.
fn written<T>(buffer: &[T], len: usize) -> &[T] {
    buffer.get(..len).unwrap_or(&[])
}
