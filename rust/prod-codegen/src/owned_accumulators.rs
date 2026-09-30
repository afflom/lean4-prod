//! An owned worker for a deliberately small, linear self-tail accumulator case.
//! The public slice ABI and all borrowed/read-only collection paths stay intact.
use crate::{copy_type, count_path_uses, tail_calls, TypeTable};
use alloc::collections::BTreeSet;
use prod_ir::{Definition, Expr, Type};

pub(super) fn parameters(definition: &Definition, table: &TypeTable<'_>) -> BTreeSet<usize> {
    // This optimization only reuses storage already required by an owned
    // record result. It must not introduce allocation to the list-buffer ABI,
    // predicates, borrowed projections, or otherwise heapless operations.
    if !matches!(definition.ret, Type::Named(_))
        || copy_type(&definition.ret, table, &mut BTreeSet::new())
    {
        return BTreeSet::new();
    }
    let candidates = definition
        .params
        .iter()
        .enumerate()
        .filter(|(index, (name, ty))| {
            matches!(ty, Type::List(_))
                && count_path_uses(&definition.body, name) == 1
                && owned_uses(&definition.body, name, *index, &definition.name, false)
        })
        .map(|(index, _)| index)
        .collect::<BTreeSet<_>>();
    if candidates.is_empty() {
        return candidates;
    }
    // The existing tail verifier proves all self calls are tail-positioned,
    // retains unchanged borrowed inputs, and rejects recursive arguments.
    let Some(plan) = tail_calls::plan(definition, table, &candidates) else {
        return BTreeSet::new();
    };
    candidates
        .into_iter()
        .filter(|index| plan.mutates(*index))
        .collect()
}

fn owned_uses(expr: &Expr, name: &str, index: usize, function: &str, owned: bool) -> bool {
    match expr {
        Expr::Var(actual) if actual == name => owned,
        Expr::Param(_) | Expr::Jp { .. } | Expr::Jmp(..) => false,
        Expr::Let(binding, value, body) => {
            binding != name
                && owned_uses(value, name, index, function, false)
                && owned_uses(body, name, index, function, owned)
        }
        Expr::Ctor(_, arguments) => arguments
            .iter()
            .all(|value| owned_uses(value, name, index, function, true)),
        Expr::Append(left, right) => {
            owned_uses(left, name, index, function, true)
                && owned_uses(right, name, index, function, false)
        }
        Expr::Call(callee, arguments) => arguments.iter().enumerate().all(|(position, value)| {
            owned_uses(
                value,
                name,
                index,
                function,
                callee == function && position == index,
            )
        }),
        Expr::If(condition, yes, no) => {
            owned_uses(condition, name, index, function, false)
                && owned_uses(yes, name, index, function, owned)
                && owned_uses(no, name, index, function, owned)
        }
        Expr::Match {
            scrut,
            alts,
            default,
        } => {
            owned_uses(scrut, name, index, function, false)
                && alts.iter().all(|alt| {
                    !alt.binders.iter().any(|binding| binding == name)
                        && owned_uses(&alt.body, name, index, function, owned)
                })
                && default
                    .as_ref()
                    .is_none_or(|body| owned_uses(body, name, index, function, owned))
        }
        _ => expr
            .children()
            .all(|child| owned_uses(child, name, index, function, false)),
    }
}
