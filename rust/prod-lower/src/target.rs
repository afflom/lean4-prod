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

/// One lowered type declaration: everything a printer needs, with every
/// question of *whether* already answered.
///
/// The split this type encodes: whether the fields are reachable only from
/// generated code is a semantic question and is settled here
/// ([`TypeDef::fields_private`]); how that is spelled -- `pub(crate)`,
/// a leading underscore, nothing at all -- is the printer's business. Same for
/// the invariant: whether there is one, and what predicate it is, is decided
/// by [`crate::lower::lower_types`]; where the `if` goes is not.
///
/// Names are already mangled under the caller's [`crate::names::NamePolicy`],
/// with one exception: [`TypeDef::lean_name`] and [`CtorDef::lean_name`] keep
/// the full Lean name. The first is a diagnostic string (the checked
/// constructor reports it when the invariant does not hold), and the second is
/// the key a printer resolves a [`TExpr::Ctor`] against -- both of those carry
/// Lean names, because resolution has to happen against something the IR
/// actually wrote.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeDef {
    /// Target identifier for the type.
    pub name: String,
    /// Full Lean name, e.g. `UorAtlas.Instance`.
    pub lean_name: String,
    /// One constructor means a structure; several mean a tagged union.
    pub ctors: Vec<CtorDef>,
    /// The structure's invariant over its own fields, already lowered. The
    /// field references in it are target identifiers, matching
    /// [`CtorDef::fields`], so a printer never re-mangles them.
    pub invariant: Option<TExpr>,
    /// Are the fields reachable only from generated code?
    ///
    /// True exactly when the type carries an invariant. Generated code keeps
    /// constructing such a type directly -- Lean already supplied the proof --
    /// so the fields stay reachable in-crate; only callers outside, where the
    /// proof was erased on export, are routed through the checked constructor.
    pub fields_private: bool,
}

/// One constructor of a [`TypeDef`].
#[derive(Debug, Clone, PartialEq)]
pub struct CtorDef {
    /// Target identifier for the constructor.
    pub name: String,
    /// Full Lean name, e.g. `UorAtlas.Instance.mk`.
    pub lean_name: String,
    /// Fields in declaration order: target identifier and type.
    pub fields: Vec<(String, Type)>,
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
