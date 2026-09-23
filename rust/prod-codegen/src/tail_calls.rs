//! Conservative self-tail-call lowering. No trampoline, heap or new runtime ABI.
//! Borrowed formals must remain the identical formal at every back edge: a
//! borrow of an iteration-local owner cannot become the next iteration's input.
use crate::{
    copy_type, internal_borrowed_parameter, rust_local_ident, Error, Mode, Renderer, TypeTable,
};
use alloc::{collections::BTreeSet, format, string::String, vec, vec::Vec};
use prod_ir::{Definition, Expr};

pub(super) struct Plan {
    name: String,
    changed: Vec<bool>,
}

impl Plan {
    pub(super) fn mutates(&self, index: usize) -> bool {
        self.changed[index]
    }
}

fn returned_binding(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Let(name, value, body) if matches!(body.as_ref(), Expr::Var(result) if result == name) => {
            Some(value)
        }
        _ => None,
    }
}

pub(super) fn plan(definition: &Definition, table: &TypeTable<'_>) -> Option<Plan> {
    let returns_copy = copy_type(&definition.ret, table, &mut BTreeSet::new());
    let borrowed = definition
        .params
        .iter()
        .map(|(_, ty)| internal_borrowed_parameter(ty, table, returns_copy))
        .collect::<Vec<_>>();
    let mut result = Plan {
        name: definition.name.clone(),
        changed: vec![false; definition.params.len()],
    };
    let mut found = false;
    fn visit(
        expr: &Expr,
        tail: bool,
        definition: &Definition,
        borrowed: &[bool],
        plan: &mut Plan,
        found: &mut bool,
    ) -> bool {
        if let Some(value) = returned_binding(expr) {
            return visit(value, tail, definition, borrowed, plan, found);
        }
        match expr {
            Expr::Call(name, args) if *name == definition.name => {
                if !tail || args.len() != definition.params.len() {
                    return false;
                }
                *found = true;
                for (index, (arg, (formal, _))) in args.iter().zip(&definition.params).enumerate() {
                    let unchanged = matches!(arg, Expr::Var(name) if name == formal);
                    if borrowed[index] && !unchanged {
                        return false;
                    }
                    plan.changed[index] |= !unchanged;
                    if !visit(arg, false, definition, borrowed, plan, found) {
                        return false;
                    }
                }
                true
            }
            Expr::If(condition, yes, no) => {
                visit(condition, false, definition, borrowed, plan, found)
                    && visit(yes, tail, definition, borrowed, plan, found)
                    && visit(no, tail, definition, borrowed, plan, found)
            }
            Expr::Let(_, value, body) => {
                visit(value, false, definition, borrowed, plan, found)
                    && visit(body, tail, definition, borrowed, plan, found)
            }
            Expr::Match {
                scrut,
                alts,
                default,
            } => {
                visit(scrut, false, definition, borrowed, plan, found)
                    && alts
                        .iter()
                        .all(|alt| visit(&alt.body, tail, definition, borrowed, plan, found))
                    && default
                        .as_deref()
                        .is_none_or(|body| visit(body, tail, definition, borrowed, plan, found))
            }
            _ => expr
                .children()
                .all(|child| visit(child, false, definition, borrowed, plan, found)),
        }
    }
    (visit(
        &definition.body,
        true,
        definition,
        &borrowed,
        &mut result,
        &mut found,
    ) && found)
        .then_some(result)
}

impl<'m> Renderer<'_, 'm> {
    pub(super) fn render_tail(&self, expr: &'m Expr, plan: &Plan) -> Result<String, Error> {
        if let Some(value) = returned_binding(expr) {
            return self.render_tail(value, plan);
        }
        match expr {
            Expr::Call(name, args) if *name == plan.name => {
                // Render/validate the ordinary call arguments first. All changed
                // operands are evaluated once, left-to-right, before assignment;
                // tuple assignment also preserves swaps and eager error order.
                // Unchanged formals are pure references to the existing value.
                let rendered = self.render_call_args(name, args)?;
                let mut formals = Vec::new();
                let mut values = Vec::new();
                for (index, ((formal, _), value)) in self.params.iter().zip(rendered).enumerate() {
                    if plan.mutates(index) {
                        formals.push(rust_local_ident(formal));
                        values.push(value);
                    }
                }
                if formals.is_empty() {
                    Ok(String::from("{ continue; }"))
                } else {
                    Ok(format!(
                        "{{ ({},) = ({},); continue; }}",
                        formals.join(", "),
                        values.join(", ")
                    ))
                }
            }
            Expr::If(condition, yes, no) => Ok(format!(
                "if {} {{ {} }} else {{ {} }}",
                self.value(condition)?,
                self.render_tail(yes, plan)?,
                self.render_tail(no, plan)?
            )),
            Expr::Let(name, _, body) if self.inline_values.contains_key(name) => {
                self.render_tail(body, plan)
            }
            Expr::Let(name, value, body)
                if crate::count_var_uses(body, name) == 0 && crate::discardable_value(value) =>
            {
                self.render_tail(body, plan)
            }
            Expr::Let(name, value, body) => Ok(format!(
                "{{ let {} = {}; {} }}",
                rust_local_ident(name),
                self.value(value)?,
                self.render_tail(body, plan)?
            )),
            Expr::Match {
                scrut,
                alts,
                default,
            } => self.render_match(
                scrut,
                alts,
                default.as_deref(),
                &Mode::OwnedValue,
                Some(plan),
            ),
            _ => self.owned_value(expr),
        }
    }
}
