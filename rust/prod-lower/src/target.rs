//! The imperative IR every backend prints.
//!
//! # The invariant that makes this worth having
//!
//! **`TExpr` is total by construction.** Anything that can fail is a [`Stmt`].
//!
//! Rust and Python propagate errors inside an expression (`?`, exceptions); C
//! cannot -- it needs statements before the expression they feed. A renderer
//! returning a String per expression node can serve the first two and never
//! the third. Hoisting every failure to statement position serves all three,
//! and means the fallibility decision is made once, here, rather than
//! re-derived by each printer.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use prod_ir::{NumKind, Type};

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Nat(u64),
    Int(i64),
    Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    /// Lean's `x / y`, computed with the **host's own** division. Emitted when
    /// the profile's `host_division` already agrees with Lean for this kind;
    /// [`crate::lower`] makes that call, not the printer.
    ///
    /// Lean's division is total and the host's is not, so the operator
    /// carries a divisor-is-zero case: `x / 0 = 0` (`Nat.div n 0 = 0`,
    /// `Int.ediv _ 0 = 0`, likewise for the sized kinds). Every printer owes
    /// that guard; it is part of what the operator *means*, not a rendering
    /// choice.
    Div,
    /// Lean's `x % y`, computed with the host's own remainder — the
    /// [`BinOp::Div`] counterpart, with the **other** zero-divisor value:
    /// `x % 0 = x`, the dividend, not zero. `Nat.mod`'s own doc comment says
    /// "When the divisor is `0`, the result is the dividend rather than an
    /// error" (doctest `5 % 0 = 5`), and `Int.emod_zero : a % 0 = a`.
    /// Rendering `0` for both was a real defect, shipped since M3.
    Mod,
    Shl,
    Shr,
    Pow,
    /// Lean's `x / y` where the host's division is **not** Euclidean, so the
    /// printer owes an explicit Euclidean division rather than its native
    /// `/`. Lean's `Int` division is `Int.ediv` ("for compatibility with
    /// SMT-LIB"): `(-12) / 7 = -2`, where a truncating host gives `-1`.
    /// Carries the same `x / 0 = 0` guard as [`BinOp::Div`].
    DivE,
    /// Euclidean remainder, the [`BinOp::DivE`] counterpart:
    /// `Int.emod (-12) 7 = 2`, where Rust's `%` gives `-5`. Carries the same
    /// `x % 0 = x` guard as [`BinOp::Mod`].
    ModE,
    Eq,
    Lt,
    Le,
    Gt,
    /// Bitwise AND. Emitted only by sized-integer masking under a profile with
    /// `sized_mask_required`; Lean has no such operator in the whitelist.
    BitAnd,
}

/// An operation that can fail, and therefore may appear only in [`Stmt::TryLet`].
#[derive(Debug, Clone, PartialEq)]
pub enum FallibleOp {
    Arith(NumKind, BinOp, TExpr, TExpr),
    Neg(NumKind, TExpr),
    /// A call to a definition whose [`crate::shape::Shape`] is `Fallible`.
    Call(String, Vec<TExpr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TExpr {
    Lit(Lit),
    Var(String),
    /// Infallible operations ONLY. Anything the profile marks fallible is a
    /// `TryLet`, never this.
    BinOp(NumKind, BinOp, Box<TExpr>, Box<TExpr>),
    Ctor(String, String, Vec<TExpr>),
    Proj(String, String, Box<TExpr>),
    /// Total callees ONLY.
    Call(String, Vec<TExpr>),
    Not(Box<TExpr>),
    And(Box<TExpr>, Box<TExpr>),
    Or(Box<TExpr>, Box<TExpr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub ctor: String,
    pub binders: Vec<String>,
    pub body: Vec<Stmt>,
}

/// Which failure a [`Stmt::Fail`] reports. Mirrors `prod_core::ComputeError`'s
/// variants by name; each printer maps it to its own error type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    OutputTooSmall,
    Unreachable,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let {
        name: String,
        ty: Type,
        value: TExpr,
    },
    /// The only failure point in the language.
    TryLet {
        name: String,
        ty: Type,
        op: FallibleOp,
    },
    If {
        cond: TExpr,
        then: Vec<Stmt>,
        else_: Vec<Stmt>,
    },
    Switch {
        scrut: TExpr,
        arms: Vec<Arm>,
        default: Option<Vec<Stmt>>,
    },
    Return(TExpr),
    Fail(ErrorCode),
    /// List construction, abstract over `ListStrategy`. Under `CallerBuffer`
    /// the lowering emits the index arithmetic and an explicit bounds check
    /// beside this; under `NativeSequence` it stands alone.
    Push {
        seq: String,
        value: TExpr,
    },
}

/// One lowered definition.
#[derive(Debug, Clone, PartialEq)]
pub struct Body {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub shape: crate::shape::Shape,
    pub stmts: Vec<Stmt>,
}
