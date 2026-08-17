use alloc::string::String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    ParamOutOfBounds(usize),
    /// Scaffolding. Task 7 proves no corpus definition can produce this, then
    /// deletes the variant so the compiler finds any node without a lowering.
    NotYetLowered(String),
    /// A construct no backend will ever render: a shift on `Int`, `pow` on a
    /// sized kind, negation of a non-`Int`. Distinct from `NotYetLowered`,
    /// which is scaffolding Task 7 deletes -- these rejections outlive it.
    /// The printers are total by construction, so a refusal has to happen
    /// here, where the semantics are.
    UnsupportedKind(String),
    /// A join point this lowering will not inline: cyclic, several callers,
    /// or a `jmp` with no matching `jp`. `prod-codegen` rejects exactly the
    /// same set as `Error::UnsupportedJoinPoint`, and this variant exists so
    /// the rejection survives the Task 7 cutover with its own name rather
    /// than being folded into `UnsupportedKind` -- widening join-point
    /// support is future work, not a permanent refusal.
    UnsupportedJoinPoint(String),

    // The type-declaration rejections. Each one carries the *same payload* as
    // the `prod_codegen::Error` variant of the same name, because at the Task 7
    // cutover that is what renders the message the published subset contract
    // pins. A payload that drifts here changes the contract without anyone
    // editing it.
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
    /// applied to the wrong number of values. Three causes, all sharing this
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
