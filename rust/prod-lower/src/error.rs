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
    Name(crate::names::NameError),
}
