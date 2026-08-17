use crate::profile::TargetProfile;
use alloc::collections::BTreeMap;
use prod_ir::{Definition, Expr, Type};

/// How a generated definition presents itself to its callers.
///
/// Computed for the whole module up front, because a call site cannot know
/// whether to append `?` until the callee's shape is known.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    /// Plain value: `fn f(..) -> T`.
    Value,
    /// Fallible: `fn f(..) -> Result<T, ComputeError>`; call sites append `?`.
    Fallible,
    /// List builder: `fn f(.., output: &mut [E]) -> Result<usize, ComputeError>`.
    Buffer,
    /// Zero-argument list golden: `fn f() -> &'static [E]`.
    StaticList,
}

/// Definition name → [`Shape`], for one module.
pub type Signatures<'m> = BTreeMap<&'m str, Shape>;

/// Compute every definition's [`Shape`] as a least fixpoint over the call
/// graph: seed everything infallible, then promote until nothing changes.
/// Monotone (shapes only ever move `Value` → `Fallible`), so it terminates.
pub fn signatures<'m>(defs: &'m [Definition], profile: &TargetProfile) -> Signatures<'m> {
    let mut shapes: Signatures<'m> = defs
        .iter()
        .map(|def| {
            let shape = match &def.ret {
                Type::List(_) if def.params.is_empty() => Shape::StaticList,
                Type::List(_) => Shape::Buffer,
                _ => Shape::Value,
            };
            (def.name.as_str(), shape)
        })
        .collect();

    loop {
        let mut changed = false;
        for def in defs {
            if shapes.get(def.name.as_str()) != Some(&Shape::Value) {
                continue;
            }
            if is_fallible(&def.body, &shapes, profile) {
                shapes.insert(def.name.as_str(), Shape::Fallible);
                changed = true;
            }
        }
        if !changed {
            return shapes;
        }
    }
}

/// Does this expression perform, or reach, an operation that can fail?
pub fn is_fallible(expr: &Expr, shapes: &Signatures, profile: &TargetProfile) -> bool {
    let here = profile.op_is_fallible(expr)
        || matches!(
            expr,
            Expr::Call(name, _) if matches!(
                shapes.get(name.as_str()),
                Some(Shape::Fallible) | Some(Shape::Buffer)
            )
        );
    here || expr
        .children()
        .any(|child| is_fallible(child, shapes, profile))
}
