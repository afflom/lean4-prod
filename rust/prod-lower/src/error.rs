use alloc::string::String;

/// Why a lowering refused.
///
/// **Every variant is named after the `prod_codegen::Error` variant it becomes
/// at the facade**, and carries the same payload, because that is what renders
/// the message the published subset contract pins. The mapping is total and
/// name-for-name on purpose: `From<LowerError> for Error` cannot invent a
/// distinction the lowering did not make, so a rejection that has to keep its
/// published kind has to keep it *here*.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    ParamOutOfBounds(usize),
    /// An expression with no rendering in the Target IR at all. `prod-codegen`
    /// reported the same set as `Error::OpaqueExpr`, and this is the variant
    /// the arms orphaned by deleting `NotYetLowered` were rehomed onto.
    OpaqueExpr(String),
    /// The callee is not something the generated code can call: an `extern`
    /// the exporter could not resolve, or a dotted constructor name this
    /// module does not declare (a Lean name is not a Rust path in expression
    /// position, so rendering it produces output that does not compile).
    UnresolvedCall(String),
    /// A construct no backend will ever render: a shift on `Int`, `pow` on a
    /// sized kind, negation of a non-`Int`.
    /// The printers are total by construction, so a refusal has to happen
    /// here, where the semantics are.
    UnsupportedKind(String),
    /// A list value somewhere the allocation-free lowering cannot put it:
    /// nested inside another type, used as an intermediate value, or built by
    /// something that is not a cons chain.
    ///
    /// Separate from [`LowerError::UnsupportedKind`] because `prod-codegen`
    /// published both names, and `From<LowerError>` at the facade cannot
    /// recover one from the other -- the distinction has to exist at the
    /// source or a published rejection silently changes kind.
    UnsupportedList(String),
    /// A type that would require a heap allocation in generated code.
    HeapType(String),
    /// A join point this lowering will not inline: cyclic, several callers,
    /// or a `jmp` with no matching `jp`. `prod-codegen` rejects exactly the
    /// same set as `Error::UnsupportedJoinPoint`, and this variant exists so
    /// the rejection keeps its own name rather than being folded into
    /// `UnsupportedKind` -- widening join-point support is future work, not a
    /// permanent refusal.
    UnsupportedJoinPoint(String),

    // The type-declaration rejections. Each one carries the *same payload* as
    // the `prod_codegen::Error` variant of the same name, because that is what
    // renders the message the published subset contract pins. A payload that
    // drifts here changes the contract without anyone editing it.
    /// A type takes type parameters; needs monomorphization.
    PolymorphicType(String),
    /// A type is defined in terms of itself (directly, or through one level of
    /// indirection); needs the tier-1 memory profile.
    RecursiveType(String),
    /// A type reached the lowering with no rendering: the exporter could not
    /// describe it, a field names a type this module does not declare, or a
    /// field's type is `Opaque`.
    OpaqueType(String),
    /// A structure shape with no allocation-free rendering, or a constructor
    /// applied to the wrong number of values. Four causes, all sharing this
    /// name because `prod-codegen` gave them one: a field type that would need
    /// owned storage; a type that carries an invariant and has more than one
    /// constructor, which cannot get the checked constructor an invariant
    /// requires, since a `Prop` field belongs to exactly one constructor; an
    /// arity disagreement between a constructor's declaration and its use; and
    /// an invariant containing an operation that can fail, which would leave
    /// the checked constructor reporting the operation's failure rather than
    /// the invariant it was checking.
    UnsupportedFieldType(String),
    /// Two Lean types share a last name component, so they would collide.
    DuplicateTypeName(String),
    /// A projection names a field the declared type does not have. Catches a
    /// declaration and a projection disagreeing within one IR file.
    UnknownField(String, String),
    /// An invariant-carrying type has a field whose name the generated checked
    /// constructor has already taken. The type gets a `new` and one accessor
    /// per field, so a field named `new` would produce two members of the same
    /// name. Only invariant-carrying types are affected: without an invariant
    /// there is neither constructor nor accessor, and a field named `new` is
    /// unremarkable.
    ReservedFieldName(String, String),

    Name(crate::names::NameError),
}
