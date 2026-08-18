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
    /// A conversion between two numeric kinds, `from` then `to`.
    ///
    /// Total, and therefore an expression: the admitted set is exactly the
    /// **lossless** one -- `Nat <-> Int`, `UIntN -> Nat`, `Nat -> UIntN` --
    /// and [`crate::lower`] refuses every other pair before one can reach a
    /// printer. `Int -> Nat` clamps (Lean's `Int.toNat`) and `Nat -> UIntN`
    /// truncates (Lean's `Nat.toUIntN`, which is `BitVec` truncation); both
    /// are total functions in Lean, not failures.
    Convert(NumKind, NumKind, Box<TExpr>),
    /// A question about the output sequence a list-shaped definition appends
    /// to. The `String` is [`Body::output`].
    ///
    /// A sequence has no `TExpr` of its own: what a backend can spell is a
    /// property of it, and which properties exist is [`SeqQuery`]. All of
    /// them are total.
    Seq(SeqQuery, String),
}

/// What a lowering asks about an output sequence.
///
/// Each variant is a question every backend can answer, asked because the
/// *lowering* needed it -- the bounds check is [`SeqQuery::Len`] against
/// [`SeqQuery::Cap`], and it is in the statement list rather than inside a
/// printer precisely so that three printers cannot forget it three times.
///
/// # These are the one POSITION-DEPENDENT expressions in the IR
///
/// Every other [`TExpr`] means the same thing wherever it is evaluated, which
/// is what lets a printer relocate one -- `prod-emit-rust` folds a
/// single-use [`Stmt::TryLet`] down into its use site on exactly that
/// assumption. A `Seq` denotes the cursor, or something taken from it, **at
/// the point in the statement list where it is reached**: every [`Stmt::Push`]
/// and every [`Stmt::Advance`] in between has moved it. Moving a `Seq`-bearing
/// expression past one silently reads a different cursor.
///
/// This is a *different property from totality*, and totality is not a
/// substitute for it. All three variants are total -- none can fail, so none
/// is a [`Stmt::TryLet`] -- and they still may not be relocated. A printer
/// that reorders expressions owes them a pin; `prod-emit-rust` spells that as
/// declining to fold any `TryLet` whose operation mentions one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeqQuery {
    /// How many elements have been appended so far: the running index.
    ///
    /// Also what a list-shaped definition returns. [`crate::shape::Shape`]
    /// documents that signature -- `-> Result<usize, ComputeError>` -- for
    /// every strategy, so "how many did you write" is the answer under
    /// `NativeSequence` too, not a `CallerBuffer` detail leaking out.
    Len,
    /// How many elements the sequence can hold.
    ///
    /// Only a bounded sequence has an answer, so only a
    /// [`crate::profile::ListStrategy::CallerBuffer`] lowering asks; a
    /// `NativeSequence` one emits no bounds check and never mentions this.
    Cap,
    /// The part of the sequence not yet written, handed to a list-shaped
    /// callee so that it appends where this definition left off.
    Rest,
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
    /// Advance `seq` past the `count` elements a list-shaped callee has
    /// already appended to it.
    ///
    /// Split from the call itself on purpose: the call is a [`Stmt::TryLet`]
    /// like every other fallible call -- the callee is the one that can run
    /// out of room and say so -- and this statement, which cannot fail, only
    /// moves the cursor. Folding the two together would make a second failure
    /// point and cost the invariant this IR is built around.
    Advance {
        seq: String,
        count: TExpr,
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
    /// The output sequence this definition appends to, named here because the
    /// printer has to declare it: under `CallerBuffer` it is the trailing
    /// `output: &mut [E]` parameter the signature grows. `Some` exactly when
    /// the shape is `Buffer` or `StaticList`.
    ///
    /// The name comes from the same [`crate::lower`] binder machinery every
    /// other binder does, so it cannot collide with one the source wrote.
    pub output: Option<String>,
    pub stmts: Vec<Stmt>,
}
