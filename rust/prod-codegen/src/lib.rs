//! prod-codegen: renders `prod-ir` modules as Rust source text.
//!
//! **This crate is a facade.** It owns the published rejection contract --
//! [`Error`] and [`REJECTIONS`] -- and nothing else: `prod-lower` decides what
//! a definition *means* as an imperative Target IR, and `prod-emit-rust`
//! decides how Rust *spells* it. A backend-specific decision inside this
//! crate, or inside `prod-lower`, is the design failure the split exists to
//! prevent; it belongs in a `prod_lower::profile::TargetProfile`.
//!
//! It is `#![no_std]` (with `alloc`) and host-independent: it renders Rust as
//! a plain `String`, never as `proc_macro2::TokenStream`, so it can run on
//! wasm32 or inside other hosts. `prod-macros` and `prod-cli` are thin drivers
//! on top of [`generate_module`].
//!
//! # Code generation policy
//!
//! The generated code targets the project's production standard: it must not
//! panic on caller-controlled input, and it must not allocate. Those two rules
//! drive everything below.
//!
//! ## Memory profile: no heap, ever
//!
//! Nothing rendered here can allocate. Lean `List α` is the only type that
//! would naïvely need a heap, so its lowering is position-dependent:
//!
//! - **Parameter position** → `&[α]`. `List.nil` match arms render as the
//!   slice pattern `[]` and `List.cons (h t)` as `[h, t @ ..]`, so structural
//!   recursion passes the tail sub-slice directly — no rebinding, no copying.
//! - **Return position** → a caller-owned output buffer. The signature gains a
//!   trailing `output: &mut [α]` and returns `Result<usize, ComputeError>`,
//!   the length of the initialized prefix. The body appends through a cursor:
//!   every append is preceded by an explicit bounds check whose else-branch
//!   returns `OutputTooSmall`, so exhaustion is an `Err` rather than a
//!   truncated answer — and the append itself is written through `get_mut`,
//!   never an index, so there is no panic path in the emitted text even
//!   considered apart from that check. A list-shaped callee is handed the
//!   unwritten remainder and reports how many elements it added. `let`-bound list values (LCNF emits lists in
//!   A-normal form) are resolved through a scoped environment rather than
//!   materialized.
//! - **Zero-argument definitions returning a list** (the golden values) →
//!   `&'static [α]` built from a promoted array literal.
//!
//! A list value that reaches any other position — an intermediate value used
//! as something other than a builder tail, or a list nested inside another
//! type — is an [`Error::UnsupportedList`]: an honest codegen failure rather
//! than a silently allocating fallback. `Type::Vec` is rejected outright as
//! [`Error::HeapType`].
//!
//! ## Error contract: fallibility is precise, not uniform
//!
//! Lean `Nat` maps to bounded `u64` and Lean `Int` to `i64`. The partial
//! operations report failure instead of panicking: addition, multiplication,
//! shifts, and powers render as `checked_*(..).ok_or(crate::ComputeError::X)?`
//! (with the shift/power exponent narrowed through
//! `u32::try_from(..).map_err(..)?`). Subtraction saturates at zero (Lean Nat
//! subtraction), and division/modulo by zero are total but not the same
//! value: division by zero is `0`, modulo by zero is the dividend (Lean
//! `Nat.mod`'s own doc comment: "the result is the dividend rather than an
//! error"), so neither is fallible. There is no bignum fallback, so this is
//! exact only while values fit in `u64`.
//!
//! **Which operations can fail is a property of the target, not of Lean**, and
//! it is declared once in `TargetProfile` rather than re-derived per backend:
//! the same `Nat.add` is a checked statement under a profile whose `Nat` is a
//! `u64` and a plain expression under one whose `Nat` is unbounded.
//!
//! A definition returns `Result<T, crate::ComputeError>` **only if it needs
//! to**: if its body contains a checked operation, or calls a definition that
//! is itself fallible, or builds a list into a caller buffer. That is a least
//! fixpoint over the module's call graph ([`Shape`]), so leaf definitions and
//! the zero-argument goldens keep their plain return types. Calls to fallible
//! definitions render as `f(args)?`.
//!
//! ## Other lowerings
//!
//! - **LCNF nodes**:
//!   - `Match` renders as a Rust `match`, with `default` becoming the `_` arm.
//!     The Nat structural-recursion ctors are special-cased: `Nat.zero` renders
//!     as the literal pattern `0`, and `Nat.succ k` as the `_` arm with
//!     `k` bound to `(scrut).saturating_sub(1)` (exact, since the zero arm
//!     matches first). `Bool.true`/`Bool.false` → `true`/`false` patterns, and
//!     `Option.none`/`Option.some v` → `None`/`Some(v)` patterns. The List
//!     ctors use the slice patterns described above. A user-declared
//!     constructor becomes its variant path with named fields.
//!   - `Ctor` renders as a struct literal `crate::Type { field: arg, .. }`
//!     (or `crate::Type::Variant { .. }` for a multi-constructor type),
//!     resolved against the module's declarations. Lean's own constructors
//!     need no declaration: `Prod.mk` is a Rust tuple `(a, b)`, the Bool and
//!     Option ctors are `true`/`false` and `None`/`Some(x)`, and
//!     `Int.ofNat`/`Int.negSucc` are the casts LCNF's `Int` literals go
//!     through. A **dotted** constructor the module does not declare is
//!     [`Error::UnresolvedCall`]: a Lean name is not a Rust path in
//!     expression position, so rendering it would surface as a compiler error
//!     far from the IR that caused it.
//!   - `Proj` renders straight through: `(proj "Type" "field" e)` becomes
//!     `e.field` (raw-escaped if `field` is a Rust keyword). The field name
//!     is resolved once, in `Lower.lean`, against Lean's own structure info,
//!     and checked against the module's declaration on the way through, so a
//!     declaration and a projection cannot disagree inside one IR file.
//!   - `Type::Tuple` renders as a Rust tuple type, so
//!     `(Tuple Nat (Tuple Nat Nat))` becomes `(u64, (u64, u64))`.
//!   - `Unreachable` renders as `unreachable!()` — LCNF emits it only for a
//!     branch Lean itself proved dead.
//!   - **Jp/Jmp policy**: a join point with exactly one `jmp` caller that is
//!     not inside its own body is inlined at the jump site, and the `let` LCNF
//!     wrapped its declaration in disappears entirely rather than binding a
//!     unit nobody reads. A join point with no callers renders its body in
//!     place. Anything else — cyclic, several callers, or a `jmp` with no
//!     matching `jp` — is [`Error::UnsupportedJoinPoint`], because it would
//!     need real control flow.
//!
//! ## Recursion
//!
//! Generated recursion is structurally bounded by a fuel or data argument (the
//! Lean side must already be terminating for LCNF to emit it), so stack depth
//! is a function of the caller's inputs, not of unbounded search.

#![no_std]

extern crate alloc;

use alloc::string::String;
use core::fmt;
use prod_ir::{Definition, Module};
use prod_lower::error::LowerError;
use prod_lower::lower::{lower_def, lower_def_in, lower_types};
use prod_lower::names::{NameError, NamePolicy, NameTable};
use prod_lower::profile::TargetProfile;
use prod_lower::shape::signatures;
pub use prod_lower::shape::Shape;

/// Errors that can occur during code generation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Code generation is not possible for an opaque expression
    OpaqueExpr(String),
    /// `(param n)` refers to a parameter index outside the definition's list
    ParamOutOfBounds(usize),
    /// A list value appears somewhere the allocation-free lowering cannot
    /// render it: nested inside another type, or used as an intermediate
    /// value rather than flowing into the output buffer.
    UnsupportedList(String),
    /// A type that would require a heap allocation in generated code.
    HeapType(String),
    /// A type is defined in terms of itself; needs the tier-1 memory profile.
    RecursiveType(String),
    /// A type takes type parameters; needs monomorphization (S5).
    PolymorphicType(String),
    /// A structure shape with no allocation-free rendering, or a constructor
    /// applied to the wrong number of values. Four causes, all sharing this
    /// name: a field type that would need owned storage; an invariant on a
    /// type with more than one constructor, which could not be given the
    /// checked constructor an invariant needs, since a `Prop` field belongs to
    /// exactly one constructor; an arity disagreement between a constructor's
    /// declaration and a use of it (an application or a match alternative);
    /// and an invariant containing an operation that can fail, whose checked
    /// constructor would report that failure rather than the invariant it was
    /// checking.
    UnsupportedFieldType(String),
    /// Two Lean types share a last name component, so they would collide.
    DuplicateTypeName(String),
    /// A type reached codegen with no rendering.
    OpaqueType(String),
    /// The exporter could not resolve a callee to a generated definition.
    UnresolvedCall(String),
    /// A projection names a field the declared type does not have. Catches a
    /// declaration and a projection disagreeing within one IR file.
    UnknownField(String, String),
    /// A join point with several callers, or one that jumps to itself. Only
    /// the single-caller form has a lowering (it inlines at its jump site);
    /// the rest would need real control flow.
    UnsupportedJoinPoint(String),
    /// An operation that has no rendering for the numeric kind it was applied
    /// to — for example a shift on `Int`, or negation on an unsigned kind.
    UnsupportedKind(String),
    /// An invariant-carrying type has a field whose name the generated
    /// checked constructor has already taken. `new` and the field's accessor
    /// would be two inherent methods of the same name in one `impl` (E0592),
    /// so the output would not compile. Only invariant-carrying types are
    /// affected: without an invariant there is no `new` and no accessors, and
    /// a field named `new` is unremarkable.
    ReservedFieldName(String, String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::OpaqueExpr(s) => write!(f, "cannot generate code for opaque expression: {}", s),
            Error::ParamOutOfBounds(i) => write!(f, "parameter index {} is out of bounds", i),
            Error::UnsupportedList(s) => {
                write!(f, "list value cannot be rendered without allocating: {}", s)
            }
            Error::HeapType(s) => write!(
                f,
                "type would require a heap allocation in generated code: {}",
                s
            ),
            Error::RecursiveType(s) => write!(
                f,
                "recursive type `{}` cannot be rendered allocation-free (needs the tier-1 profile)",
                s
            ),
            Error::PolymorphicType(s) => write!(
                f,
                "type `{}` has type parameters; monomorphization is not implemented",
                s
            ),
            Error::UnsupportedFieldType(s) => {
                write!(f, "field type is not allowed in a generated type: {}", s)
            }
            Error::DuplicateTypeName(s) => {
                write!(f, "two Lean types share the last name component `{}`", s)
            }
            Error::OpaqueType(s) => write!(f, "no Rust rendering for type: {}", s),
            Error::UnresolvedCall(s) => write!(
                f,
                "`{}` is neither @[prod]-tagged nor a whitelisted operator, so there is nothing to call",
                s
            ),
            Error::UnknownField(ty, field) => {
                write!(f, "type `{}` declares no field `{}`", ty, field)
            }
            Error::UnsupportedJoinPoint(name) => write!(
                f,
                "join point `{}` has several callers or jumps to itself; only the single-caller form has a lowering",
                name
            ),
            Error::UnsupportedKind(s) => write!(
                f,
                "operation has no rendering for its numeric kind: {}",
                s
            ),
            Error::ReservedFieldName(ty, field) => write!(
                f,
                "type `{}` carries an invariant, so it gets a generated `new` constructor and one accessor per field; its field `{}` would collide with `new`",
                ty, field
            ),
        }
    }
}

/// The rejections the generator makes, for the published subset contract
/// (`prod subset`, `specs/lean-for-production.md`). One entry per `Error`
/// variant, in declaration order; keep in step with `Error` above — the
/// contract is rendered from this list, so a variant missing here is a
/// rejection the published contract silently fails to disclose.
pub const REJECTIONS: &[(&str, &str)] = &[
    (
        "OpaqueExpr",
        "an expression with no Rust rendering",
    ),
    (
        "ParamOutOfBounds",
        "a parameter index outside the definition's parameter list",
    ),
    (
        "UnsupportedList",
        "a list value outside a supported position: nested inside another type, or used as an intermediate value rather than a slice parameter/output buffer",
    ),
    (
        "HeapType",
        "a type that would require a heap allocation in generated code",
    ),
    (
        "RecursiveType",
        "an inductive refers to itself (directly, or through one level of indirection); needs the tier-1 memory profile",
    ),
    (
        "PolymorphicType",
        "an inductive has type parameters; monomorphization is not implemented",
    ),
    (
        "UnsupportedFieldType",
        "a structure shape with no allocation-free rendering. There are exactly four causes: a field type that would need owned storage (a list or vector field); a type that carries an invariant and has more than one constructor, which cannot get the checked constructor an invariant requires, since a `Prop` field belongs to exactly one constructor; a constructor application or a match alternative whose argument/binder count disagrees with the declaration, which is the IR contradicting itself; and an invariant containing an operation that can fail, whose checked constructor would report the arithmetic's error instead of the invariant it was checking",
    ),
    (
        "DuplicateTypeName",
        "two Lean types share a last name component, so they would collide in Rust",
    ),
    (
        "OpaqueType",
        "a type reached codegen with no Rust rendering",
    ),
    (
        "UnresolvedCall",
        "the callee is neither @[prod]-tagged nor a whitelisted operator, so there is nothing to call",
    ),
    (
        "UnknownField",
        "a projection names a field the declared type does not have",
    ),
    (
        "UnsupportedJoinPoint",
        "a join point with several callers, or one that jumps to itself; only the single-caller form, which inlines at its jump site, has a lowering",
    ),
    (
        "UnsupportedKind",
        "an operation with no rendering for the numeric kind it was applied to. There are exactly four causes: a shift on Int; negation on any kind other than Int; pow on a sized kind (UInt8..UInt64), whose u32 exponent cannot be narrowed without silently changing the answer; and a conversion between a pair of numeric kinds that has no rendering, namely every sized-to-sized pair (e.g. UInt8 -> UInt32) and every Int-to-sized pair, both deliberate non-goals",
    ),
    (
        "ReservedFieldName",
        "a field of a structure whose invariant is enforced is named `new`, which the generated checked constructor already uses; the field's accessor would collide with it. Structures with no enforced invariant get neither, so the name is only reserved where the constructor exists",
    ),
];

/// Every [`LowerError`] becomes the `Error` variant of the same name.
///
/// The mapping is name-for-name and payload-for-payload because a rejection's
/// kind and its message are the published subset contract; a conversion that
/// merged two of them, or invented a payload, would change that contract
/// without anyone editing `REJECTIONS`.
impl From<LowerError> for Error {
    fn from(e: LowerError) -> Self {
        match e {
            LowerError::ParamOutOfBounds(i) => Error::ParamOutOfBounds(i),
            LowerError::OpaqueExpr(s) => Error::OpaqueExpr(s),
            LowerError::UnresolvedCall(s) => Error::UnresolvedCall(s),
            LowerError::UnsupportedKind(s) => Error::UnsupportedKind(s),
            LowerError::UnsupportedList(s) => Error::UnsupportedList(s),
            LowerError::HeapType(s) => Error::HeapType(s),
            LowerError::UnsupportedJoinPoint(s) => Error::UnsupportedJoinPoint(s),
            LowerError::PolymorphicType(s) => Error::PolymorphicType(s),
            LowerError::RecursiveType(s) => Error::RecursiveType(s),
            LowerError::OpaqueType(s) => Error::OpaqueType(s),
            LowerError::UnsupportedFieldType(s) => Error::UnsupportedFieldType(s),
            LowerError::DuplicateTypeName(s) => Error::DuplicateTypeName(s),
            LowerError::UnknownField(ty, field) => Error::UnknownField(ty, field),
            LowerError::ReservedFieldName(ty, field) => Error::ReservedFieldName(ty, field),
            LowerError::Name(e) => Error::from(e),
        }
    }
}

/// A name collision is a duplicate *type* name from this crate's point of
/// view: `NameTable` reports the target name two distinct Lean names landed
/// on, and `DuplicateTypeName` is the published rejection for exactly that.
impl From<NameError> for Error {
    fn from(e: NameError) -> Self {
        match e {
            NameError::Collision { target, .. } => Error::DuplicateTypeName(target),
        }
    }
}

/// Render a whole module: its type declarations, then one `pub fn` per
/// definition.
pub fn generate_module(module: &Module) -> Result<String, Error> {
    let profile = TargetProfile::RUST;
    NameTable::build(module, &NamePolicy::RUST)?;
    let types = lower_types(module, &NamePolicy::RUST, &profile)?;
    let shapes = signatures(&module.definitions, &profile);

    let mut out = prod_emit_rust::emit_types(&types);
    for def in &module.definitions {
        // `lower_def_in`, NOT `lower_def`: the type-table-aware form is what
        // makes the constructor-arity and `UnknownField` rejections fire. The
        // table-free `lower_def` cannot check either, so using it here would
        // silently drop two rejections that `REJECTIONS` still advertises.
        let body = lower_def_in(def, &shapes, &profile, &module.types)?;
        out.push_str(&prod_emit_rust::emit_body(&body, &types));
        out.push('\n');
    }
    Ok(out)
}

/// Render a single definition as a `pub fn`.
///
/// Calls to definitions outside `def` itself are assumed infallible, since
/// there is no module to resolve them against; use [`generate_module`] when
/// cross-definition fallibility matters. With no module, there are no type
/// declarations either, so any `(named ...)` type in `def`'s signature is
/// opaque and any user constructor in its body is unresolved.
pub fn generate_def(def: &Definition) -> Result<String, Error> {
    let one = core::slice::from_ref(def);
    let shapes = signatures(one, &TargetProfile::RUST);
    let body = lower_def(def, &shapes, &TargetProfile::RUST)?;
    Ok(prod_emit_rust::emit_body(&body, &[]))
}

#[cfg(test)]
mod tests;
