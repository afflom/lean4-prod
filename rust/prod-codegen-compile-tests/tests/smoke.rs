#![allow(non_snake_case)] // generated names mirror Lean definitions

//! Compiling proves the generated code is valid Rust; it does not prove the
//! code computes anything. These call a sample of it and check real values.
//!
//! Deliberately thin. The exhaustive value-level checks against Lean-computed
//! goldens live in `prod-core`; this crate's job is that rustc reads the
//! output at all, and the crate building is most of that job.

use prod_codegen_compile_tests::*;

#[test]
fn conformance_golden_code_runs() -> Result<(), ComputeError> {
    // From `lean/Conformance/` — the real Lean → LCNF → IR pipeline.
    assert_eq!(c_nat_add(2, 3)?, 5);
    assert_eq!(c_nat_sub(3, 10), 0); // Lean Nat subtraction truncates
                                     // Lean `Nat.mod`'s own doc comment: "When the divisor is `0`, the result
                                     // is the dividend rather than an error" (doctest `5 % 0 = 5`). This was a
                                     // pre-existing bug (shipping since M3): the shared div/mod zero-guard
                                     // rendered `0` for both, which is right for division but wrong here.
    assert_eq!(c_nat_mod(5, 0), 5);
    assert_eq!(c_nat_shr(8, 2), 2);
    assert_eq!(c_nat_shr(8, 70), 0); // shift past the width is 0, not an error
                                     // Infallible by the fallibility fixpoint: a decidable guard performs no
                                     // checked arithmetic, so it keeps its plain return type.
    assert_eq!(c_guard_lt(1, 2), 1);
    assert_eq!(c_tuple(4, 5), (4, 5));

    // Structure projection, including the type whose Prop field sits in the
    // middle of the declaration.
    let m = MidProp {
        first: 1,
        second: 2,
        third: 3,
    };
    assert_eq!(c_proj_middle_prop(m), (1, (2, 3)));

    // The invariant-lowering probe structures (`lean/Conformance/Structures.lean`).
    // What each one pins about lowering lives in `golden.ir`, which `just
    // conformance` diffs; these calls only establish that the generated Rust
    // for them is constructible and callable. Values satisfy each structure's
    // Lean invariant, so they stay valid once Task 5 turns these literals into
    // checked constructors.
    let mixed = MixedCompare {
        lo: 2,
        hi: 7,
        extra: 5,
    };
    assert_eq!(c_mixed_compare(mixed)?, 14);
    let split = SplitInvariant { a: 1, b: 3 };
    assert_eq!(c_split_invariant(split)?, 4);
    let tagged = TaggedMode { mode: 1, limit: 9 };
    assert_eq!(c_tagged_mode(tagged)?, 10);
    // These two have Prop fields OUTSIDE the lowerable fragment, so they carry
    // no invariant and keep plain public fields — the decline path.
    let unlowerable = UnlowerableProp { x: 1, y: 2 };
    assert_eq!(c_unlowerable_prop(unlowerable)?, 3);
    let non_numeric = NonNumericCompare {
        flagA: true,
        flagB: true,
    };
    assert!(c_non_numeric_compare(non_numeric));

    // List: caller-owned output buffer in, borrowed slice back out.
    // `c_list_build` is base-2 digits least-significant-first, so 5 is [1,0,1]
    // and consuming it sums to 2 — a popcount, not the input.
    let mut buffer = [0u64; 16];
    let n = c_list_build(10, 5, &mut buffer)?;
    assert_eq!(&buffer[..n], &[1, 0, 1]);
    assert_eq!(c_list_consume(&buffer[..n])?, 2);

    // Exhaustion is an error, not an out-of-bounds panic.
    let mut too_small = [0u64; 1];
    assert_eq!(
        c_list_build(10, 5, &mut too_small),
        Err(ComputeError::OutputTooSmall)
    );

    // Int. Euclidean, not truncating. Rust's own `/` and `%` would give -1 and -5.
    assert_eq!(c_int_ediv(-12, 7)?, -2);
    assert_eq!(c_int_emod(-12, 7)?, 2);
    assert_eq!(c_int_sub(i64::MIN, 1), Err(ComputeError::SubOverflow));
    assert_eq!(c_int_neg(i64::MIN), Err(ComputeError::NegOverflow));
    assert_eq!(c_int_ediv(i64::MIN, -1), Err(ComputeError::DivOverflow));
    assert_eq!(c_int_ediv(5, 0)?, 0); // total, like Nat
                                      // `Int`'s `emod_zero : a % 0 = a` (doctest `(7 : Int) % (0 : Int) = 7`):
                                      // modulo by zero is the dividend, not zero, same as `Nat` above.
    assert_eq!(c_int_emod(7, 0)?, 7);
    // Cross-checked against Lean's own computed answer, not just a value
    // someone typed by hand — see the `golden_*` comparisons below for why
    // that distinction matters.
    assert_eq!(c_int_ediv(-12, 7)?, golden_int_ediv_neg_12_7());
    assert_eq!(c_int_emod(-12, 7)?, golden_int_emod_neg_12_7());
    // `Int.pow` was the only published operator with no conformance witness.
    // `Int.pow : Int → Nat → Int` reaches the lowerer through `instance :
    // NatPow Int` → `instPowNat` → `instHPow`, every one of which `natHDictOp`
    // hard-maps to kind `"Nat"` — so the risk was `(pow Nat a b)`, rendering
    // `((a) as u64).checked_pow(..)`. The golden pins `(pow Int a b)`, and a
    // negative base is what makes the assertion able to tell the two apart:
    // under the unsigned reading -2 becomes 18446744073709551614 and the
    // power overflows rather than giving -8.
    assert_eq!(c_int_pow(-2, 3)?, -8);
    assert_eq!(c_int_pow(-2, 3)?, golden_int_pow_neg_2_3());
    assert_eq!(c_int_pow(2, 0)?, 1);
    // Checked, like the rest of `Int`: the exponent is a `Nat`, so both the
    // overflow and the "exponent does not fit u32" case are reported.
    assert_eq!(c_int_pow(2, 63), Err(ComputeError::PowOverflow));
    assert_eq!(
        c_int_pow(2, u64::from(u32::MAX) + 1),
        Err(ComputeError::PowExponentTooLarge)
    );

    // Sized integers. Lean's `UInt8.add` is BitVec addition, so overflow
    // wraps rather than erroring — the opposite of `Nat`/`Int`.
    // Wrapping is the semantics, not a failure — and no Result in sight.
    assert_eq!(c_u8_add(255, 1), 0);
    assert_eq!(c_u8_mul(16, 16), 0);
    assert_eq!(c_u8_div(5, 0), 0); // total
                                   // Sized shifts mask the amount mod the width (`UInt8.shiftLeft a b =
                                   // a <<< (b % 8)`, `Init/Data/UInt/Basic.lean:126`) — they do NOT
                                   // truncate to 0 past the width the way `Nat`'s shift does. So
                                   // `1u8 <<< 8` masks to `1u8 <<< 0 == 1`, not 0.
    assert_eq!(c_u8_shl(1, 8), 1);
    // Guard: a decidable `<` comparison on sized integers lowers to a plain
    // `if`, exercising the `UInt8` decider rows in `deciderNames` (added but
    // previously unexercised by any conformance case).
    assert_eq!(c_u8_guard_lt(1, 2), 1);
    assert_eq!(c_u8_guard_lt(2, 1), 0);

    // The comparison that actually catches a wrong sized rendering: Lean's
    // own compiled `UInt8.add`/`UInt8.shiftLeft`, not a value typed by hand.
    // This is what would have caught (and, once added, did catch) a
    // backwards shift rendering — a hardcoded assertion above can be wrong
    // in the same direction as the bug it's meant to catch; a golden
    // computed by the real Lean toolchain cannot.
    assert_eq!(c_u8_add(255, 1), golden_u8_add_255_1());
    assert_eq!(c_u8_shl(1, 8), golden_u8_shl_1_8());

    // Conversions. Int.toNat is the one with a wrong-by-default rendering:
    // Lean clamps negatives to 0, while a bare `as u64` cast would wrap -5 to
    // 18446744073709551611.
    assert_eq!(c_int_to_nat(-5), 0); // clamps, does not wrap
    assert_eq!(c_int_to_nat(5), 5);
    assert_eq!(c_nat_to_u8(300), 44); // truncates: 300 - 256
    assert_eq!(c_u8_to_nat(255), 255);
    // Cross-checked against Lean's own computed answer, same reasoning as the
    // Int/UInt8 goldens above.
    assert_eq!(c_int_to_nat(-5), golden_int_to_nat_neg_5());
    Ok(())
}

#[test]
fn representative_enum_code_runs() -> Result<(), ComputeError> {
    // The multi-constructor enum path. Nothing else in the repo compiles this.
    assert_eq!(r_area(r_make_circle(3))?, 9);
    assert_eq!(r_area(r_make_rect(3, 4))?, 12);

    // The two constructors really are distinct variants, not one shape.
    assert_ne!(r_make_circle(3), r_make_rect(3, 4));

    // Raw-identifier escaping has to agree between declaration and projection.
    let k = Keyword { r#type: 7, r#fn: 5 };
    assert_eq!(r_keyword_fields(k)?, 12);

    assert_eq!(r_jp_inlined(41)?, 42);
    assert_eq!(r_nested_tuple(1, 2, 3), (1, (2, 3)));
    Ok(())
}
