//! What a target language's semantics are, declared rather than branched on.

use prod_ir::{Expr, NumKind};

/// How a backend represents Lean's `Nat`.
///
/// Lean's `Nat` is arbitrary precision, so `Nat.add` is total. A backend that
/// maps it to a fixed-width integer introduces a failure mode Lean does not
/// have; a backend with native bignums does not. Every fallibility decision
/// for `Nat` follows from this one field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatRepr {
    /// 64-bit. Checked arithmetic; overflow is reported.
    Bounded64,
    /// Arbitrary precision, as in Lean. Arithmetic is total.
    Exact,
}

/// How a backend represents Lean's `List`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListStrategy {
    /// Caller supplies storage; the lowering emits an explicit bounds check.
    CallerBuffer,
    /// The host has a growable sequence; elements are pushed.
    NativeSequence,
}

/// The host language's own integer division, which the lowering corrects
/// toward Lean's Euclidean semantics when they differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivisionSemantics {
    Euclidean,
    /// Rounds toward negative infinity. Agrees with Euclidean **only when the
    /// divisor is positive** -- `12 / -7` is `-2 rem -2` floor, `-1 rem 5`
    /// Euclidean.
    Floor,
    /// Rounds toward zero.
    Truncate,
}

/// One target language's semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetProfile {
    pub nat_repr: NatRepr,
    pub list_strategy: ListStrategy,
    /// The host has no fixed-width integers, so every sized operation needs an
    /// explicit mask.
    pub sized_mask_required: bool,
    pub host_division: DivisionSemantics,
}

impl TargetProfile {
    pub const RUST: TargetProfile = TargetProfile {
        nat_repr: NatRepr::Bounded64,
        list_strategy: ListStrategy::CallerBuffer,
        sized_mask_required: false,
        host_division: DivisionSemantics::Truncate,
    };

    /// Declared here, in Plan 1, deliberately: a seam with one implementation
    /// encodes that implementation's assumptions. Plan 2 builds the emitter;
    /// this constant is what keeps Plan 1's tests honest.
    pub const PYTHON: TargetProfile = TargetProfile {
        nat_repr: NatRepr::Exact,
        list_strategy: ListStrategy::NativeSequence,
        sized_mask_required: true,
        host_division: DivisionSemantics::Floor,
    };

    /// Does this operation report failure under this profile?
    ///
    /// Sized integers wrap in Lean (`UInt8.add` is BitVec addition), so they
    /// are total under every profile. `Nat` subtraction saturates in Lean and
    /// never fails. `Nat` shift-left is fallible everywhere -- an exact-`Nat`
    /// backend caps it rather than attempting an allocation that would hang.
    /// What remains is governed by `nat_repr`.
    pub fn op_is_fallible(&self, expr: &Expr) -> bool {
        let nat_checked = self.nat_repr == NatRepr::Bounded64;
        match expr {
            Expr::Add(k, ..) | Expr::Mul(k, ..) | Expr::Pow(k, ..) => match k {
                NumKind::Nat => nat_checked,
                NumKind::Int => true,
                _ => false,
            },
            Expr::Sub(k, ..) | Expr::Div(k, ..) | Expr::Mod(k, ..) => *k == NumKind::Int,
            Expr::Neg(k, _) => *k == NumKind::Int,
            Expr::Shl(k, ..) => *k == NumKind::Nat,
            _ => false,
        }
    }

    /// Does this operation report failure under **any** profile?
    ///
    /// Read where a construct has to be total for every backend at once rather
    /// than for one chosen backend. A structure's invariant is the case:
    /// [`crate::lower::lower_types`] takes no profile, so the single lowered
    /// predicate it produces is printed by all of them, and an operation only
    /// *some* profile can hoist into a statement has no place in it.
    ///
    /// [`TargetProfile::op_is_fallible`] reads exactly one field, `nat_repr`,
    /// and `Bounded64` is the stricter of its two answers, so the union over
    /// every profile is the answer a bounded-`Nat` profile gives. The other
    /// fields are set to something, because a `TargetProfile` is a whole
    /// value; nothing here reads them.
    pub fn op_is_fallible_under_any_profile(expr: &Expr) -> bool {
        const STRICTEST: TargetProfile = TargetProfile {
            nat_repr: NatRepr::Bounded64,
            list_strategy: ListStrategy::CallerBuffer,
            sized_mask_required: false,
            host_division: DivisionSemantics::Euclidean,
        };
        STRICTEST.op_is_fallible(expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec;
    use prod_ir::{Definition, Expr, NumKind, Type};

    fn nat_add_def() -> Definition {
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

    #[test]
    fn rust_profile_makes_nat_add_fallible() {
        // u64 is finite, so Lean's total Nat.add becomes a checked add.
        assert!(TargetProfile::RUST.op_is_fallible(&nat_add_def().body));
    }

    #[test]
    fn python_profile_makes_nat_add_total() {
        // Python's int is arbitrary precision, exactly like Lean's Nat, so
        // there is nothing to check. This is the whole point of the profile:
        // if this test ever passes vacuously the split has bought nothing.
        assert!(!TargetProfile::PYTHON.op_is_fallible(&nat_add_def().body));
    }

    #[test]
    fn sized_arithmetic_is_total_under_every_profile() {
        // UInt8 add is BitVec addition in Lean -- wrapping IS the semantics,
        // not an overflow, so no profile may mark it fallible.
        let e = Expr::Add(
            NumKind::U8,
            Box::new(Expr::Var(String::from("a"))),
            Box::new(Expr::Var(String::from("b"))),
        );
        assert!(!TargetProfile::RUST.op_is_fallible(&e));
        assert!(!TargetProfile::PYTHON.op_is_fallible(&e));
    }

    /// The union that `op_is_fallible_under_any_profile` claims to be.
    ///
    /// It is consulted where a construct must be total for every backend at
    /// once -- a structure's invariant -- so if it ever disagreed with the
    /// actual union over the declared profiles it would either admit an
    /// operation some backend cannot render, or refuse one every backend can.
    #[test]
    fn fallible_under_any_profile_is_the_union_over_the_declared_profiles() {
        let a = || Box::new(Expr::Var(String::from("a")));
        let b = || Box::new(Expr::Var(String::from("b")));
        let nodes = [
            // Fallible under Rust's bounded `Nat`, total under an exact one.
            Expr::Add(NumKind::Nat, a(), b()),
            Expr::Mul(NumKind::Nat, a(), b()),
            Expr::Pow(NumKind::Nat, a(), b()),
            // Fallible everywhere.
            Expr::Add(NumKind::Int, a(), b()),
            Expr::Sub(NumKind::Int, a(), b()),
            Expr::Div(NumKind::Int, a(), b()),
            Expr::Shl(NumKind::Nat, a(), b()),
            Expr::Neg(NumKind::Int, a()),
            // Total everywhere: the fragment an invariant may contain.
            Expr::Sub(NumKind::Nat, a(), b()),
            Expr::Div(NumKind::Nat, a(), b()),
            Expr::Mod(NumKind::Nat, a(), b()),
            Expr::Shr(NumKind::Nat, a(), b()),
            Expr::Add(NumKind::U8, a(), b()),
            Expr::Mul(NumKind::U8, a(), b()),
            Expr::Shl(NumKind::U8, a(), b()),
        ];
        for node in &nodes {
            let union = TargetProfile::RUST.op_is_fallible(node)
                || TargetProfile::PYTHON.op_is_fallible(node);
            assert_eq!(
                TargetProfile::op_is_fallible_under_any_profile(node),
                union,
                "for {:?}",
                node
            );
        }
        // Not vacuous: the set is neither all-true nor all-false.
        assert!(nodes
            .iter()
            .any(TargetProfile::op_is_fallible_under_any_profile));
        assert!(!nodes
            .iter()
            .all(TargetProfile::op_is_fallible_under_any_profile));
    }

    #[test]
    fn nat_shift_left_stays_fallible_even_under_exact_nat() {
        // The spec's deliberate divergence: an exact-Nat backend caps the
        // shift and raises rather than attempting 1 << 10**9 and exhausting
        // memory. A hang is a worse failure than an error.
        let e = Expr::Shl(
            NumKind::Nat,
            Box::new(Expr::Var(String::from("a"))),
            Box::new(Expr::Var(String::from("b"))),
        );
        assert!(TargetProfile::RUST.op_is_fallible(&e));
        assert!(TargetProfile::PYTHON.op_is_fallible(&e));
    }
}
