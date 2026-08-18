//! The renderings under test are not formatting: each one is a Lean fact this
//! project established over two milestones, and one of them shipped backwards
//! and stayed green in CI because nothing checked it.

use super::*;
use alloc::boxed::Box;
use alloc::vec;
use prod_ir::{Alt, Definition, Expr, NumKind, Type};
use prod_lower::error::LowerError;
use prod_lower::lower::{lower_def, lower_types};
use prod_lower::names::NamePolicy;
use prod_lower::profile::TargetProfile;
use prod_lower::shape::signatures;

/// Duplicated from `prod-lower`'s own tests rather than exported: a fixture
/// crossing a crate boundary for one assertion is not worth a `pub` item.
fn def_add() -> Definition {
    Definition {
        name: String::from("f"),
        params: vec![
            (String::from("a"), Type::Nat),
            (String::from("b"), Type::Nat),
        ],
        ret: Type::Nat,
        body: Expr::Add(
            NumKind::Nat,
            Box::new(Expr::Var(String::from("a"))),
            Box::new(Expr::Var(String::from("b"))),
        ),
    }
}

/// `f(a, b) = <body>` over two parameters of the kind's own type.
fn binary(kind: NumKind, body: impl FnOnce(Box<Expr>, Box<Expr>) -> Expr) -> Definition {
    let ty = match kind {
        NumKind::Nat => Type::Nat,
        NumKind::Int => Type::Int,
        other => Type::UInt(other),
    };
    Definition {
        name: String::from("f"),
        params: vec![
            (String::from("a"), ty.clone()),
            (String::from("b"), ty.clone()),
        ],
        ret: ty,
        body: body(
            Box::new(Expr::Var(String::from("a"))),
            Box::new(Expr::Var(String::from("b"))),
        ),
    }
}

fn render(def: &Definition) -> String {
    let defs = vec![def.clone()];
    let shapes = signatures(&defs, &TargetProfile::RUST);
    let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
    emit_body(&body)
}

fn lower_err(def: &Definition) -> LowerError {
    let defs = vec![def.clone()];
    let shapes = signatures(&defs, &TargetProfile::RUST);
    lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect_err("must be rejected")
}

#[test]
fn a_fallible_nat_add_prints_as_checked_rust() {
    let defs = alloc::vec![def_add()];
    let shapes = signatures(&defs, &TargetProfile::RUST);
    let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
    let out = emit_body(&body);
    assert!(
        out.contains("-> Result<u64, crate::ComputeError>"),
        "got: {}",
        out
    );
    assert!(out.contains("checked_add"), "got: {}", out);
    assert!(out.contains('?'), "got: {}", out);
}

#[test]
fn a_total_definition_gets_a_plain_return_type_and_no_question_mark() {
    // The Shape -> signature mapping is the other half of the above: a body
    // with nothing fallible in it must not be wrapped in a Result.
    let out = render(&binary(NumKind::U8, |a, b| Expr::Add(NumKind::U8, a, b)));
    assert!(out.contains("-> u8 {"), "got: {}", out);
    assert!(!out.contains("Result<"), "got: {}", out);
    assert!(!out.contains('?'), "got: {}", out);
}

// ---------------------------------------------------------------------------
// Step 7: the five renderings that must survive the port unchanged.
// ---------------------------------------------------------------------------

/// `Nat.mod`: "When the divisor is `0`, the result is the dividend rather than
/// an error" (`Init/Prelude.lean:2183`, doctest `5 % 0 = 5`), and
/// `Int.emod_zero : a % 0 = a`. Division's zero case is the *other* value:
/// `x / 0 = 0`. Rendering `0` for both was a real defect shipped since M3, so
/// the two are asserted together — a single test for `%` would have passed
/// while `/` was wrong, and vice versa.
#[test]
fn division_by_zero_is_zero_but_modulo_by_zero_is_the_dividend() {
    let div = render(&binary(NumKind::Nat, |a, b| Expr::Div(NumKind::Nat, a, b)));
    assert!(
        div.contains("if (b) == 0 { 0 } else { (a) / (b) }"),
        "div by zero must be 0, got: {}",
        div
    );

    let modulo = render(&binary(NumKind::Nat, |a, b| Expr::Mod(NumKind::Nat, a, b)));
    assert!(
        modulo.contains("if (b) == 0 { a } else { (a) % (b) }"),
        "mod by zero must be the DIVIDEND, not 0, got: {}",
        modulo
    );
}

/// Lean's `Int` division is Euclidean (`Int.ediv`/`Int.emod`, "for
/// compatibility with SMT-LIB"), not Rust's truncating `/`: Lean's doctest
/// gives `(-12) % 7 = 2` where Rust's `%` gives `-5`.
#[test]
fn int_division_is_euclidean_not_truncating() {
    let div = render(&binary(NumKind::Int, |a, b| Expr::Div(NumKind::Int, a, b)));
    assert!(
        div.contains("checked_div_euclid"),
        "Int division must be Euclidean, got: {}",
        div
    );
    assert!(!div.contains("(a) / (b)"), "got: {}", div);

    let modulo = render(&binary(NumKind::Int, |a, b| Expr::Mod(NumKind::Int, a, b)));
    assert!(
        modulo.contains("checked_rem_euclid"),
        "Int modulo must be Euclidean, got: {}",
        modulo
    );
    // The zero guard survives the Euclidean spelling, with its own value.
    assert!(modulo.contains("if (b) == 0 { a }"), "got: {}", modulo);
    assert!(div.contains("if (b) == 0 { 0 }"), "got: {}", div);

    // And the methods named above really do compute Lean's answers. Asserting
    // the rendered text alone is what let a shift rendering ship backwards;
    // this pins the text to a number.
    assert_eq!((-12i64).checked_div_euclid(7), Some(-2));
    assert_eq!((-12i64).checked_rem_euclid(7), Some(2));
    assert_eq!(-12i64 / 7, -1, "Rust's own `/` is the WRONG answer here");
    assert_eq!(-12i64 % 7, -5, "Rust's own `%` is the WRONG answer here");
}

/// `Nat.shiftRight` truncates to `0` for large amounts: `Nat` is unbounded, so
/// `a >>> b = 0` for any `b >= 64` once `a` fits `u64`. There is no width to
/// mask by, and the rendering is total and infallible.
#[test]
fn nat_shift_right_truncates_to_zero_and_cannot_fail() {
    let out = render(&binary(NumKind::Nat, |a, b| Expr::Shr(NumKind::Nat, a, b)));
    assert!(
        out.contains("checked_shr(u32::try_from(b).unwrap_or(u32::MAX)).unwrap_or(0)"),
        "got: {}",
        out
    );
    assert!(
        !out.contains('?'),
        "Nat.shiftRight cannot fail, got: {}",
        out
    );

    assert_eq!(1u64.checked_shr(64), None);
    assert_eq!(1u64.checked_shr(64).unwrap_or(0), 0);
}

/// `UIntN.shiftLeft` MASKS the amount mod the width — it does NOT truncate to
/// `0` like `Nat`. `UInt8.shiftLeft a b = ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩`
/// (`Init/Data/UInt/Basic.lean:126`), so `(1 : UInt8) <<< 8 = 1 <<< 0 = 1`.
///
/// This one shipped backwards once and stayed green in CI, because nothing
/// compared Lean's own golden to Rust's answer. Hence the numeric assertion
/// below, not only the textual one.
#[test]
fn sized_shift_left_masks_the_amount_and_does_not_truncate() {
    let out = render(&binary(NumKind::U8, |a, b| Expr::Shl(NumKind::U8, a, b)));
    assert!(
        out.contains("((a) as u8).wrapping_shl((b) as u32)"),
        "got: {}",
        out
    );
    assert!(
        !out.contains("unwrap_or(0)"),
        "a sized shift must not truncate to 0, got: {}",
        out
    );

    // Lean: `(1 : UInt8) <<< 8 = 1`, not `0`.
    assert_eq!(1u8.wrapping_shl(8), 1);
    assert_eq!(1u8.wrapping_shl(9), 2);
    // The right shift masks the same way.
    let shr = render(&binary(NumKind::U8, |a, b| Expr::Shr(NumKind::U8, a, b)));
    assert!(
        shr.contains("((a) as u8).wrapping_shr((b) as u32)"),
        "got: {}",
        shr
    );
    assert_eq!(0x80u8.wrapping_shr(8), 0x80);
}

/// Sized arithmetic wraps and cannot fail (`UInt8.add a b = ⟨a.toBitVec +
/// b.toBitVec⟩` — wrapping IS the semantics); `pow` on a sized kind is
/// rejected rather than rendered, because narrowing a `u64` exponent to the
/// `u32` that `wrapping_pow` takes would silently compute a different number.
#[test]
fn sized_arithmetic_wraps_and_sized_pow_is_rejected() {
    for (kind, ty) in [
        (NumKind::U8, "u8"),
        (NumKind::U16, "u16"),
        (NumKind::U32, "u32"),
        (NumKind::U64, "u64"),
    ] {
        let out = render(&binary(kind, move |a, b| Expr::Add(kind, a, b)));
        assert!(
            out.contains(&format!("((a) as {}).wrapping_add(b)", ty)),
            "got: {}",
            out
        );
        assert!(!out.contains('?'), "sized add cannot fail, got: {}", out);
    }
    let sub = render(&binary(NumKind::U8, |a, b| Expr::Sub(NumKind::U8, a, b)));
    assert!(sub.contains("wrapping_sub"), "got: {}", sub);
    let mul = render(&binary(NumKind::U8, |a, b| Expr::Mul(NumKind::U8, a, b)));
    assert!(mul.contains("wrapping_mul"), "got: {}", mul);

    // `Nat`/`Int` exponentiation keeps the two-failure-mode rendering: the
    // exponent must narrow to `u32`, and the result can still overflow.
    let pow = render(&binary(NumKind::Nat, |a, b| Expr::Pow(NumKind::Nat, a, b)));
    assert!(
        pow.contains("checked_pow(u32::try_from(b).map_err(|_| crate::ComputeError::PowExponentTooLarge)?).ok_or(crate::ComputeError::PowOverflow)?"),
        "got: {}",
        pow
    );

    // But a sized `pow` is refused outright, and refused by the LOWERING —
    // the printer is total, so a construct no backend renders has to be
    // rejected where the semantics live.
    assert!(matches!(
        lower_err(&binary(NumKind::U8, |a, b| Expr::Pow(NumKind::U8, a, b))),
        LowerError::UnsupportedKind(_)
    ));
}

/// `Nat.sub` saturates in Lean (`2 - 5 = 0`), so it is total; `Nat` shift-left
/// is checked, because an out-of-range amount genuinely overflows `u64`.
#[test]
fn nat_sub_saturates_and_nat_shift_left_is_checked() {
    let sub = render(&binary(NumKind::Nat, |a, b| Expr::Sub(NumKind::Nat, a, b)));
    assert!(
        sub.contains("((a) as u64).saturating_sub(b)"),
        "got: {}",
        sub
    );
    assert!(!sub.contains('?'), "got: {}", sub);

    let shl = render(&binary(NumKind::Nat, |a, b| Expr::Shl(NumKind::Nat, a, b)));
    assert!(
        shl.contains("checked_shl(u32::try_from(b).map_err(|_| crate::ComputeError::ShiftExponentTooLarge)?).ok_or(crate::ComputeError::ShiftOverflow)?"),
        "got: {}",
        shl
    );
}

/// A `TryLet` read exactly once folds back into its use, so Rust output stays
/// idiomatic: `f(g(a)?)`, not a temporary per operation.
#[test]
fn a_singly_used_trylet_is_inlined_into_its_use() {
    // f(a, b) = (a + b) * a — two fallible ops, one nested in the other.
    let def = Definition {
        name: String::from("f"),
        params: vec![
            (String::from("a"), Type::Nat),
            (String::from("b"), Type::Nat),
        ],
        ret: Type::Nat,
        body: Expr::Mul(
            NumKind::Nat,
            Box::new(Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            )),
            Box::new(Expr::Var(String::from("a"))),
        ),
    };
    let out = render(&def);
    assert!(
        !out.contains("let t"),
        "no temporary should survive: {}",
        out
    );
    assert!(out.contains("checked_add"), "got: {}", out);
    assert!(out.contains("checked_mul"), "got: {}", out);
}

/// A temporary read twice stays a `let`: inlining it would evaluate — and
/// possibly fail — twice.
#[test]
fn a_twice_used_trylet_stays_a_let() {
    // f(a, b) = let x := a + b; x * x
    let def = Definition {
        name: String::from("f"),
        params: vec![
            (String::from("a"), Type::Nat),
            (String::from("b"), Type::Nat),
        ],
        ret: Type::Nat,
        body: Expr::Let(
            String::from("x"),
            Box::new(Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            )),
            Box::new(Expr::Mul(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("x"))),
                Box::new(Expr::Var(String::from("x"))),
            )),
        ),
    };
    let out = render(&def);
    assert!(out.contains("let x = "), "got: {}", out);
    assert_eq!(out.matches("checked_add").count(), 1, "got: {}", out);
}

#[test]
fn a_call_to_a_fallible_definition_gets_a_question_mark() {
    let callee = binary(NumKind::Nat, |a, b| Expr::Add(NumKind::Nat, a, b));
    let mut callee = callee;
    callee.name = String::from("g");
    let caller = Definition {
        name: String::from("f"),
        params: vec![(String::from("a"), Type::Nat)],
        ret: Type::Nat,
        body: Expr::Call(
            String::from("g"),
            vec![Expr::Var(String::from("a")), Expr::Var(String::from("a"))],
        ),
    };
    let defs = vec![callee, caller];
    let shapes = signatures(&defs, &TargetProfile::RUST);
    let body = lower_def(&defs[1], &shapes, &TargetProfile::RUST).expect("lowers");
    let out = emit_body(&body);
    assert!(out.contains("Ok(g(a, a)?)"), "got: {}", out);
}

/// Shifts on `Int` are a deliberate non-goal, and — like sized `pow` — are
/// refused by the lowering, not by the printer.
#[test]
fn int_shifts_are_rejected_by_the_lowering() {
    assert!(matches!(
        lower_err(&binary(NumKind::Int, |a, b| Expr::Shl(NumKind::Int, a, b))),
        LowerError::UnsupportedKind(_)
    ));
    assert!(matches!(
        lower_err(&binary(NumKind::Int, |a, b| Expr::Shr(NumKind::Int, a, b))),
        LowerError::UnsupportedKind(_)
    ));
}

/// End to end, the scoping the flat statement list has to preserve.
///
/// `f(x) = (let x := 1; x) + x` renders with the second operand still reading
/// the parameter. The old renderer got this from the brace in
/// `{ let x = 1; x } + x`; the Target IR is flat, so the lowering renames the
/// inner binder and the printed Rust has to show it.
#[test]
fn a_let_shadowing_a_parameter_still_prints_the_parameter_at_the_outer_use() {
    let def = Definition {
        name: String::from("f"),
        params: vec![(String::from("x"), Type::Nat)],
        ret: Type::Nat,
        body: Expr::Add(
            NumKind::Nat,
            Box::new(Expr::Let(
                String::from("x"),
                Box::new(Expr::Nat(1)),
                Box::new(Expr::Var(String::from("x"))),
            )),
            Box::new(Expr::Var(String::from("x"))),
        ),
    };
    let out = render(&def);
    assert!(
        !out.contains("let x ="),
        "the inner binder must not shadow the parameter: {}",
        out
    );
    // The add's right operand is the bare parameter.
    assert!(
        out.contains(".checked_add(x)"),
        "the outer use must still be the parameter: {}",
        out
    );
}

/// The printed form of the no-hoist invariant.
///
/// The `?` on the checked add must sit INSIDE the `if c {` block. Printed
/// above it, the generated function reports an overflow for inputs where
/// Lean's `if` never evaluates the sum at all.
#[test]
fn a_fallible_op_in_one_arm_prints_inside_that_arm() {
    let def = Definition {
        name: String::from("f"),
        params: vec![
            (String::from("c"), Type::Bool),
            (String::from("a"), Type::Nat),
            (String::from("b"), Type::Nat),
        ],
        ret: Type::Nat,
        body: Expr::If(
            Box::new(Expr::Var(String::from("c"))),
            Box::new(Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            )),
            Box::new(Expr::Nat(0)),
        ),
    };
    let out = render(&def);
    let branch = out.find("if c {").expect(&out);
    let add = out.find("checked_add").expect(&out);
    assert!(add > branch, "the checked add escaped its branch:\n{}", out);
    let else_ = out.find("} else {").expect(&out);
    assert!(
        add < else_,
        "the checked add landed in the wrong branch:\n{}",
        out
    );
    assert!(out.contains("return Ok(0);"), "{}", out);
}

/// A `Switch` prints as a Rust `match`, one block per arm, with the arm's
/// binders destructured -- and a dead branch as `unreachable!()`, which is
/// what `prod-codegen` emits for `Expr::Unreachable` today.
#[test]
fn a_match_prints_as_a_rust_match_with_its_binders_destructured() {
    let def = Definition {
        name: String::from("f"),
        params: vec![
            (String::from("x"), Type::Nat),
            (String::from("o"), Type::Option(Box::new(Type::Nat))),
        ],
        ret: Type::Nat,
        body: Expr::Match {
            scrut: Box::new(Expr::Var(String::from("o"))),
            alts: vec![
                Alt {
                    ctor: String::from("Option.none"),
                    binders: vec![],
                    body: Expr::Unreachable,
                },
                Alt {
                    ctor: String::from("Option.some"),
                    binders: vec![String::from("v")],
                    body: Expr::Var(String::from("v")),
                },
            ],
            default: None,
        },
    };
    let out = render(&def);
    assert!(out.contains("match o {"), "{}", out);
    assert!(out.contains("None => {"), "{}", out);
    assert!(out.contains("unreachable!();"), "{}", out);
    assert!(out.contains("Some(v) => {"), "{}", out);
    assert!(out.contains("return v;"), "{}", out);
}

/// LCNF's structural recursion on `Nat`: the zero arm matches first, so the
/// successor arm's scrutinee is at least 1 and `saturating_sub(1)` is the
/// exact predecessor.
#[test]
fn the_nat_recursion_arms_bind_the_predecessor() {
    let def = Definition {
        name: String::from("f"),
        params: vec![(String::from("n"), Type::Nat)],
        ret: Type::Nat,
        body: Expr::Match {
            scrut: Box::new(Expr::Var(String::from("n"))),
            alts: vec![
                Alt {
                    ctor: String::from("Nat.zero"),
                    binders: vec![],
                    body: Expr::Nat(0),
                },
                Alt {
                    ctor: String::from("Nat.succ"),
                    binders: vec![String::from("k")],
                    body: Expr::Var(String::from("k")),
                },
            ],
            default: None,
        },
    };
    let out = render(&def);
    assert!(out.contains("        0 => {"), "{}", out);
    assert!(out.contains("let k = (n).saturating_sub(1);"), "{}", out);
}

/// A temporary bound at the top level but READ inside a branch must not be
/// folded into that branch: the fold would move its `?` behind a condition
/// that may not hold, changing which inputs fail.
#[test]
fn a_temporary_read_only_inside_a_branch_is_not_folded_into_it() {
    // f(c, a, b) = let s := a + b; if c then s else 0
    let def = Definition {
        name: String::from("f"),
        params: vec![
            (String::from("c"), Type::Bool),
            (String::from("a"), Type::Nat),
            (String::from("b"), Type::Nat),
        ],
        ret: Type::Nat,
        body: Expr::Let(
            String::from("s"),
            Box::new(Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            )),
            Box::new(Expr::If(
                Box::new(Expr::Var(String::from("c"))),
                Box::new(Expr::Var(String::from("s"))),
                Box::new(Expr::Nat(0)),
            )),
        ),
    };
    let out = render(&def);
    let add = out.find("checked_add").expect(&out);
    let branch = out.find("if c {").expect(&out);
    assert!(
        add < branch,
        "the sum is computed unconditionally in the source, so it must stay above the branch:\n{}",
        out
    );
}

// ---------------------------------------------------------------------------
// Type declarations, and the invariant machinery
//
// The behaviour under test is `prod-codegen`'s, moved across the seam: the
// decisions on the lowering side, the syntax on this one. These assertions are
// on the *rendered* text because that is what a caller at the crate boundary
// actually gets.
// ---------------------------------------------------------------------------

#[test]
fn an_invariant_carrying_type_still_gets_private_fields_and_a_checked_new() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat))
    (invariant (and (le 1 q) (and (le 1 T) (le 1 O)))))
)
"#;
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let types = lower_types(&module, &NamePolicy::RUST).expect("lowers");
    let out = emit_types(&types);
    assert!(out.contains("pub(crate) q: u64"), "got: {}", out);
    assert!(!out.contains("pub q: u64"));
    assert!(
        out.contains("pub fn new(q: u64, T: u64, O: u64) -> Result<Self, crate::ComputeError>"),
        "got: {}",
        out
    );
    assert!(
        out.contains("if ((1 <= q) && ((1 <= T) && (1 <= O)))"),
        "got: {}",
        out
    );
    assert!(
        out.contains("pub fn q(&self) -> u64 { self.q }"),
        "got: {}",
        out
    );
}

#[test]
fn a_type_with_no_lowerable_invariant_keeps_public_fields() {
    let ir = r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#;
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let out = emit_types(&lower_types(&module, &NamePolicy::RUST).expect("lowers"));
    assert!(out.contains("pub a: u64"), "got: {}", out);
    assert!(!out.contains("pub(crate)"));
    assert!(!out.contains("fn new("));
}

#[test]
fn the_invariant_is_not_lowered_inverted() {
    // `q >= 1` must render `1 <= q`, never `q <= 1`. A reversed comparison
    // compiles, returns a bool, and rejects exactly the inputs it should
    // accept -- a defect of this exact shape has shipped here before. The two
    // conjuncts point opposite ways on purpose, so a blanket swap is visible.
    let ir = r#"
(module M
  (type "M.Bound" (ctor "M.Bound.mk" (lo Nat) (hi Nat))
    (invariant (and (le 2 lo) (le hi 7))))
)
"#;
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let out = emit_types(&lower_types(&module, &NamePolicy::RUST).expect("lowers"));
    assert!(out.contains("(2 <= lo)"), "got: {}", out);
    assert!(out.contains("(hi <= 7)"), "got: {}", out);
}

/// A projection needs no type table to print: the lowering already checked the
/// field against its declaration, so what is left is field-access syntax.
#[test]
fn a_projection_renders_as_field_access() {
    let module = prod_ir::parser::parse_module(
        r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#,
    )
    .expect("parses")
    .1;
    let def = Definition {
        name: String::from("f"),
        params: vec![(String::from("p"), Type::Named(String::from("M.Pair")))],
        ret: Type::Nat,
        body: Expr::Proj(
            String::from("M.Pair"),
            String::from("a"),
            Box::new(Expr::Var(String::from("p"))),
        ),
    };
    let defs = vec![def];
    let shapes = signatures(&defs, &TargetProfile::RUST);
    let body =
        prod_lower::lower::lower_def_in(&defs[0], &shapes, &TargetProfile::RUST, &module.types)
            .expect("lowers");
    let out = emit_body(&body);
    assert!(out.contains("(p).a"), "got: {}", out);
}

/// An invariant is not restricted to comparisons: `Nat.sub` saturates, so
/// `1 <= q - T` is a single total expression, and it must render exactly as
/// `prod-codegen` renders it -- `saturating_sub`, no `?`, no temporary.
///
/// The strings are pinned rather than paraphrased because narrowing what an
/// invariant may contain narrows the published subset, and a comparison of
/// two field expressions is entirely plausible in a Lean-proved structure.
#[test]
fn an_invariant_may_contain_total_arithmetic_and_renders_it_inline() {
    let ir = r#"
(module M
  (type "M.S" (ctor "M.S.mk" (q Nat) (T Nat) (a U8) (b U8))
    (invariant (and (le 1 (sub Nat q T)) (le (add U8 a b) 200))))
)
"#;
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let out = emit_types(&lower_types(&module, &NamePolicy::RUST).expect("lowers"));
    assert!(
        out.contains(
            "if ((1 <= ((q) as u64).saturating_sub(T)) && (((a) as u8).wrapping_add(b) <= 200))"
        ),
        "got: {}",
        out
    );
    // A saturating subtraction and a wrapping addition cannot fail, so nothing
    // was hoisted: no `?` and no `checked_` anywhere in the constructor.
    assert!(!out.contains('?'), "got: {}", out);
    assert!(!out.contains("checked_"), "got: {}", out);
}

// --------------------------------------------------------------- Task 6

/// Every definition in an IR module, rendered.
fn render_module(ir: &str) -> alloc::collections::BTreeMap<String, String> {
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let shapes = signatures(&module.definitions, &TargetProfile::RUST);
    module
        .definitions
        .iter()
        .map(|def| {
            let body =
                prod_lower::lower::lower_def_in(def, &shapes, &TargetProfile::RUST, &module.types)
                    .unwrap_or_else(|e| panic!("`{}` must lower: {:?}", def.name, e));
            (def.name.clone(), emit_body(&body))
        })
        .collect()
}

fn render_one(ir: &str) -> String {
    render_module(ir)
        .into_values()
        .next()
        .expect("one definition")
}

/// The list-builder signature and, in the body, the bounds check the lowering
/// put there.
///
/// The `output[__len]` index cannot be out of range: the `if` immediately
/// above it is the check, and its else-branch returns. That check being in the
/// statement list rather than re-derived here is the point of the task.
#[test]
fn a_caller_buffer_list_prints_its_guard_its_write_and_its_recursion() {
    let out = render_module(include_str!("../../../lean/Conformance/golden.ir"))
        .remove("c_list_build")
        .expect("c_list_build is in the corpus");

    assert!(
        out.contains(
            "pub fn c_list_build(fuel: u64, n: u64, output: &mut [u64]) \
             -> Result<usize, crate::ComputeError>"
        ),
        "got: {}",
        out
    );
    assert!(out.contains("let mut __len: usize = 0;"), "got: {}", out);
    assert!(out.contains("if (__len < output.len()) {"), "got: {}", out);
    assert!(
        out.contains("return Err(crate::ComputeError::OutputTooSmall);"),
        "got: {}",
        out
    );
    assert!(out.contains("output[__len] = n;"), "got: {}", out);
    assert!(out.contains("__len += 1;"), "got: {}", out);
    // The recursion writes where this call left off and reports what it used.
    assert!(
        out.contains("c_list_build(n_27, _x_56, &mut output[__len..])?"),
        "got: {}",
        out
    );
    assert!(out.contains("return Ok(__len);"), "got: {}", out);
    // Nothing is left unrendered.
    assert!(!out.contains("compile_error!"), "got: {}", out);
}

/// A zero-argument list definition keeps its promoted `&'static [E]`
/// rendering. That is a printer concern, and it stays one.
#[test]
fn a_static_list_prints_as_a_promoted_slice() {
    let out = render_one(
        r#"(module M (def m () (List Nat) (ctor "List.cons" 3 (ctor "List.cons" 5 (ctor "List.nil")))))"#,
    );
    assert_eq!(out, "pub fn m() -> &'static [u64] {\n    &[3, 5]\n}\n");
}

/// A list in parameter position borrows as a slice, unchanged.
#[test]
fn a_list_parameter_still_borrows_as_a_slice() {
    let out = render_one(r#"(module M (def m ((xs (List Nat))) Nat 0))"#);
    assert!(out.contains("pub fn m(xs: &[u64]) -> u64"), "got: {}", out);
}

/// Comparisons in a definition BODY, in source order. A reversed comparison
/// still compiles, still returns a `bool`, and rejects precisely the inputs it
/// should accept -- so the order is asserted, not just the operator.
#[test]
fn comparisons_print_in_source_order() {
    for (node, rendered) in [
        ("eq", "(a == b)"),
        ("lt", "(a < b)"),
        ("le", "(a <= b)"),
        ("gt", "(a > b)"),
    ] {
        let out = render_one(&alloc::format!(
            "(module M (def m ((a Nat) (b Nat)) Bool ({} a b)))",
            node
        ));
        assert!(out.contains(rendered), "for {}: got {}", node, out);
    }
}

/// The boolean connectives, matching what the `Renderer` prints today.
#[test]
fn boolean_connectives_print_as_rust_operators() {
    let out = render_one("(module M (def m ((a Nat) (b Nat)) Bool (and (lt a b) (gt a b))))");
    assert!(out.contains("((a < b) && (a > b))"), "got: {}", out);

    let out = render_one("(module M (def m ((a Nat) (b Nat)) Bool (or (lt a b) (gt a b))))");
    assert!(out.contains("((a < b) || (a > b))"), "got: {}", out);

    let out = render_one("(module M (def m ((a Nat) (b Nat)) Bool (not (lt a b))))");
    assert!(out.contains("(!(a < b))"), "got: {}", out);
}

/// The conversions, ported from `prod-codegen` unchanged. Each rendering is a
/// Lean fact: `Int.toNat` clamps negatives to zero, `Nat.toUIntN` truncates.
#[test]
fn the_lossless_conversions_print_exactly_as_the_renderer_does() {
    for (from, to, rendered) in [
        ("Nat", "Int", "((a) as i64)"),
        ("Int", "Nat", "((a).max(0) as u64)"),
        ("Nat", "U8", "((a) as u8)"),
        ("Nat", "U32", "((a) as u32)"),
        ("U8", "Nat", "((a) as u64)"),
        ("U64", "Nat", "((a) as u64)"),
    ] {
        let out = render_one(&alloc::format!(
            "(module M (def m ((a {})) {} (convert {} {} a)))",
            from,
            to,
            from,
            to
        ));
        assert!(
            out.contains(rendered),
            "for {} -> {}: got {}",
            from,
            to,
            out
        );
        assert!(!out.contains("compile_error!"), "got: {}", out);
    }
}

/// A `TryLet` whose operation reads the sequence is PINNED where the lowering
/// put it, even when the fold-into-single-use rule would otherwise move it.
///
/// Folding moves an expression down the statement list. `TExpr::Seq` denotes
/// the cursor at the point it is reached, so moving it past a `Push` or an
/// `Advance` reads a different cursor and silently computes something else.
/// Totality does not rule this out -- `Seq` is total and still may not be
/// relocated -- so the inliner has to ask a second question.
///
/// The body is built by hand because no lowering emits this ordering today:
/// the only `Seq`-bearing `TryLet` the list lowering produces is immediately
/// followed by the `Advance` that consumes it, so the fold would happen to be
/// sound. That is an accident of ordering, and this is the test that stops a
/// later task from disturbing it unnoticed.
#[test]
fn a_trylet_that_reads_the_cursor_is_never_folded_past_a_push() {
    use prod_lower::target::{Body, SeqQuery};

    let seq = || String::from("output");
    let body = Body {
        name: String::from("m"),
        params: vec![],
        ret: Type::List(Box::new(Type::Nat)),
        shape: Shape::Buffer,
        output: Some(seq()),
        stmts: vec![
            // Reads the cursor HERE, while it is still 0.
            Stmt::TryLet {
                name: String::from("t0"),
                ty: Type::Nat,
                op: FallibleOp::Call(String::from("f"), vec![TExpr::Seq(SeqQuery::Rest, seq())]),
            },
            // ... and these move it.
            Stmt::If {
                cond: TExpr::BinOp(
                    NumKind::Nat,
                    BinOp::Lt,
                    Box::new(TExpr::Seq(SeqQuery::Len, seq())),
                    Box::new(TExpr::Seq(SeqQuery::Cap, seq())),
                ),
                then: vec![],
                else_: vec![Stmt::Fail(ErrorCode::OutputTooSmall)],
            },
            Stmt::Push {
                seq: seq(),
                value: TExpr::Lit(Lit::Nat(7)),
            },
            // The single, same-level read of `t0`.
            Stmt::Advance {
                seq: seq(),
                count: TExpr::Var(String::from("t0")),
            },
            Stmt::Return(TExpr::Seq(SeqQuery::Len, seq())),
        ],
    };

    // The read is counted exactly once at this level, so without the pin the
    // fold would fire. If this ever stops holding the test is vacuous.
    let usage = uses(&body.stmts).get("t0").copied().expect("`t0` is read");
    assert_eq!((usage.total, usage.same_level), (1, 1));

    let out = emit_body(&body);
    assert!(
        out.contains("let t0 = f(&mut output[__len..])?;"),
        "the call must stay where the cursor was still 0: {}",
        out
    );
    assert!(
        out.contains("__len += t0;"),
        "the advance must read the binding, not a moved copy of the call: {}",
        out
    );
    assert!(
        !out.contains("__len += f("),
        "the call was folded past a Push and now reads the wrong cursor: {}",
        out
    );
}

/// The second in-repo corpus. `golden.ir` is downstream of Lean;
/// `representative.ir` is the hand-written one, and it carries the
/// multi-constructor enum, the keyword field names and the inlined join point
/// that the Lean corpus cannot produce.
///
/// Every definition lowers and renders. The only `compile_error!` left is the
/// struct literal, which needs the module's type table -- that is the Task 7
/// cutover's job, and this asserts it is the *only* thing outstanding.
#[test]
fn the_hand_written_corpus_lowers_and_renders() {
    let rendered = render_module(include_str!(
        "../../prod-codegen-compile-tests/fixtures/representative.ir"
    ));
    assert_eq!(rendered.len(), 6, "got {:?}", rendered.keys());

    for (name, out) in &rendered {
        for line in out.lines().filter(|l| l.contains("compile_error!")) {
            assert!(
                line.contains("a struct literal needs the module's type table"),
                "`{}` has an unexpected compile_error!: {}",
                name,
                line
            );
        }
    }
    // The join point is inlined at its jump site, not rejected.
    assert!(
        rendered["r_jp_inlined"].contains("checked_add"),
        "got {}",
        rendered["r_jp_inlined"]
    );
    // A keyword field name is escaped identically at declaration and use.
    assert!(
        rendered["r_keyword_fields"].contains("r#type"),
        "got {}",
        rendered["r_keyword_fields"]
    );
}
