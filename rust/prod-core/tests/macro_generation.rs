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

const CANONICAL: Instance = Instance { q: 4, T: 3, O: 8 };
const DEMO_SMALL: Instance = Instance { q: 2, T: 2, O: 4 };
const THIRD: Instance = Instance { q: 5, T: 1, O: 3 };

/// Digits of a `u64` in any of the TF1 bases fit comfortably in 64 slots.
const DIGIT_CAPACITY: usize = 64;

#[test]
fn generated_definitions_compile_and_run() -> Result<(), ComputeError> {
    assert_eq!(classIndex(1, 2, 3, CANONICAL)?, 43);
    assert_eq!(stride(CANONICAL)?, 24);
    assert_eq!(class_count(CANONICAL)?, 96);
    assert_eq!(belt(CANONICAL)?, 12_288);
    assert_eq!(classDecode(43, CANONICAL)?, (1, (2, 3)));
    // Recursive def: 43 = 5·8+5 is two base-8 digits; fuel 0 short-circuits.
    assert_eq!(digitCount(10, 43, CANONICAL)?, 2);
    assert_eq!(digitCount(10, 511, CANONICAL)?, 3);
    assert_eq!(digitCount(0, 999, CANONICAL)?, 0);
    // List defs write into a caller-owned buffer and report the prefix length;
    // digits of 43 in base 8 are [3, 5] (least-significant first).
    let mut buffer = [0u64; DIGIT_CAPACITY];
    let len = digits(10, 43, CANONICAL, &mut buffer)?;
    assert_eq!(&buffer[..len], &[3, 5]);
    assert_eq!(digitSum(&buffer[..len])?, 8);
    // Decidable guards: 43//24 = 44//24 = 1 but 67//24 = 2; belt = 12288.
    assert!(sameClass(43, 44, CANONICAL)?);
    assert!(!sameClass(43, 67, CANONICAL)?);
    assert!(smallEnough(100, CANONICAL)?);
    assert!(!smallEnough(20_000, CANONICAL)?);
    // Option def: 43 < class_count 96 decodes; 100 is out of range.
    assert_eq!(tryClassDecode(43, CANONICAL)?, Some((1, (2, 3))));
    assert_eq!(tryClassDecode(100, CANONICAL)?, None);
    Ok(())
}

#[test]
fn list_builder_reports_an_undersized_buffer_instead_of_panicking() {
    // 43 needs two base-8 digits; one slot is not enough. The generated code
    // splits the buffer rather than indexing it, so exhaustion is an `Err`,
    // never an out-of-bounds panic.
    let mut too_small = [0u64; 1];
    assert_eq!(
        digits(10, 43, CANONICAL, &mut too_small),
        Err(ComputeError::OutputTooSmall)
    );
    let mut empty: [u64; 0] = [];
    assert_eq!(
        digits(10, 43, CANONICAL, &mut empty),
        Err(ComputeError::OutputTooSmall)
    );
    // An exactly-sized buffer succeeds.
    let mut exact = [0u64; 2];
    assert_eq!(digits(10, 43, CANONICAL, &mut exact), Ok(2));
    assert_eq!(exact, [3, 5]);
}

#[test]
fn arithmetic_overflow_is_reported_not_panicked() {
    // `belt = class_count · 2^(O-1)`: an instance with a huge O overflows the
    // power, and an enormous q overflows the class-count multiplication.
    // Both must surface as errors — this is the DoS surface the standard
    // cares about, since these are caller-controlled inputs.
    let wide = Instance { q: 1, T: 1, O: 70 };
    assert_eq!(belt(wide), Err(ComputeError::PowOverflow));
    let huge = Instance {
        q: u64::MAX,
        T: 2,
        O: 2,
    };
    assert_eq!(stride(huge), Ok(4));
    assert_eq!(class_count(huge), Err(ComputeError::MulOverflow));
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
    for (inst, g_stride, g_class_count, g_belt) in [
        (
            CANONICAL,
            golden_stride_canonical(),
            golden_class_count_canonical(),
            golden_belt_canonical(),
        ),
        (
            DEMO_SMALL,
            golden_stride_demo_small(),
            golden_class_count_demo_small(),
            golden_belt_demo_small(),
        ),
        (
            THIRD,
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
        classIndex(1, 2, 3, CANONICAL)?,
        golden_classIndex_1_2_3_canonical()
    );
    assert_eq!(
        classDecode(43, CANONICAL)?,
        golden_classDecode_43_canonical()
    );
    assert_eq!(
        digitCount(10, 43, CANONICAL)?,
        golden_digitCount_43_canonical()
    );
    assert_eq!(
        digitCount(10, 511, CANONICAL)?,
        golden_digitCount_511_canonical()
    );
    assert_eq!(
        digitCount(0, 999, CANONICAL)?,
        golden_digitCount_zero_fuel_canonical()
    );
    let mut buffer = [0u64; DIGIT_CAPACITY];
    let len = digits(10, 43, CANONICAL, &mut buffer)?;
    assert_eq!(&buffer[..len], golden_digits_43_canonical());
    assert_eq!(
        digitSum(&buffer[..len])?,
        golden_digitSum_digits_43_canonical()
    );
    assert_eq!(
        sameClass(43, 44, CANONICAL)?,
        golden_sameClass_43_44_canonical()
    );
    assert_eq!(
        sameClass(43, 67, CANONICAL)?,
        golden_sameClass_43_67_canonical()
    );
    assert_eq!(
        smallEnough(100, CANONICAL)?,
        golden_smallEnough_100_canonical()
    );
    assert_eq!(
        smallEnough(20_000, CANONICAL)?,
        golden_smallEnough_20000_canonical()
    );
    assert_eq!(
        tryClassDecode(43, CANONICAL)?,
        golden_tryClassDecode_43_canonical()
    );
    assert_eq!(
        tryClassDecode(100, CANONICAL)?,
        golden_tryClassDecode_100_canonical()
    );
    Ok(())
}

#[test]
fn generated_definitions_roundtrip_lean_examples() -> Result<(), ComputeError> {
    for inst in [CANONICAL, DEMO_SMALL, THIRD] {
        for h2 in 0..inst.q {
            for d in 0..inst.T {
                for l in 0..inst.O {
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
    // decode∘encode is the identity on every valid index of each instance.
    for inst in [CANONICAL, DEMO_SMALL, THIRD] {
        for idx in 0..class_count(inst)? {
            let (h2, (d, l)) = classDecode(idx, inst)?;
            assert_eq!(classIndex(h2, d, l, inst)?, idx);
        }
    }
    Ok(())
}
