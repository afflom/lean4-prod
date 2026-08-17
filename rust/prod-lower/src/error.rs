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
    Name(crate::names::NameError),
}
