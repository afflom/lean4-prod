//! Specialize acyclic continuations before name-indexed ownership analysis.
//! The same join parameter may borrow at one call site and own at another.

use crate::{Error, JpContext};
use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    string::String,
    vec::Vec,
};
use prod_ir::{Definition, Expr};

// Compiler resource limits, not application/runtime capacities. Check the
// expanded size before copying a continuation, including indirect DAG reuse.
const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Cost {
    nodes: usize,
    depth: usize,
}

impl Cost {
    fn add(self, other: Self) -> Result<Self, Error> {
        let result = Self {
            nodes: self
                .nodes
                .checked_add(other.nodes)
                .ok_or(Error::JoinExpansionLimit)?,
            depth: self.depth.max(other.depth),
        };
        result.require(MAX_NODES, MAX_DEPTH)
    }

    fn require(self, nodes: usize, depth: usize) -> Result<Self, Error> {
        if self.nodes > nodes || self.depth > depth {
            Err(Error::JoinExpansionLimit)
        } else {
            Ok(self)
        }
    }
}

fn cost(
    source: &Expr,
    context: &JpContext<'_>,
    memo: &mut BTreeMap<String, Cost>,
    active: &mut BTreeSet<String>,
) -> Result<Cost, Error> {
    match source {
        Expr::Jmp(name, arguments) if context.decls.contains_key(name.as_str()) => {
            let (parameters, body) = context.decls[name.as_str()];
            if parameters.len() != arguments.len() || active.contains(name) {
                return Err(Error::UnsupportedJoinPoint(name.clone()));
            }
            if active.len() >= MAX_DEPTH {
                return Err(Error::JoinExpansionLimit);
            }
            let body_cost = if let Some(value) = memo.get(name) {
                *value
            } else {
                active.insert(name.clone());
                let value = cost(body, context, memo, active)?;
                active.remove(name);
                memo.insert(name.clone(), value);
                value
            };
            let mut result = Cost {
                nodes: body_cost.nodes,
                depth: body_cost
                    .depth
                    .checked_add(1)
                    .ok_or(Error::JoinExpansionLimit)?,
            }
            .add(Cost {
                nodes: parameters.len(),
                depth: 0,
            })?;
            for argument in arguments {
                result = result.add(cost(argument, context, memo, active)?)?;
            }
            Ok(result)
        }
        Expr::Jp { name, body, .. } if context.jmp_count(name) == 0 => {
            cost(body, context, memo, active)
        }
        Expr::Jp { .. } => Ok(Cost { nodes: 1, depth: 0 }),
        _ => {
            let mut result = Cost { nodes: 1, depth: 0 };
            for child in source.children() {
                result = result.add(cost(child, context, memo, active)?)?;
            }
            Ok(result)
        }
    }
}

// A control-flow diamond can select a continuation's argument once instead of
// copying the continuation into every branch. Only a single, lexically visible
// argument is supported: no tuple packaging, coercion, closure, or allocation.
fn tail_destination(source: &Expr) -> Option<&str> {
    match source {
        Expr::Jmp(name, arguments) if arguments.len() == 1 => Some(name),
        Expr::Let(_, _, body) => tail_destination(body),
        Expr::If(_, yes, no) => {
            let name = tail_destination(yes)?;
            (tail_destination(no)? == name).then_some(name)
        }
        Expr::Match { alts, default, .. } => {
            let first = alts.first().map(|alt| &alt.body).or(default.as_deref())?;
            let name = tail_destination(first)?;
            (alts
                .iter()
                .all(|alt| tail_destination(&alt.body) == Some(name))
                && default
                    .as_deref()
                    .is_none_or(|body| tail_destination(body) == Some(name)))
            .then_some(name)
        }
        _ => None,
    }
}

fn take_tail_arguments(source: &mut Expr, destination: &str) -> Result<(), Error> {
    match source {
        Expr::Jmp(name, arguments) if name == destination && arguments.len() == 1 => {
            *source = arguments
                .pop()
                .ok_or_else(|| Error::UnsupportedJoinPoint(String::from(destination)))?;
        }
        Expr::Let(_, _, body) => take_tail_arguments(body, destination)?,
        Expr::If(_, yes, no) => {
            take_tail_arguments(yes, destination)?;
            take_tail_arguments(no, destination)?;
        }
        Expr::Match { alts, default, .. } => {
            for alt in alts {
                take_tail_arguments(&mut alt.body, destination)?;
            }
            if let Some(body) = default {
                take_tail_arguments(body, destination)?;
            }
        }
        _ => return Err(Error::UnsupportedJoinPoint(String::from(destination))),
    }
    Ok(())
}

fn factor_tail_diamonds(
    source: &mut Expr,
    available: &mut BTreeSet<String>,
    tail: bool,
) -> Result<(), Error> {
    match source {
        Expr::Let(_, value, body) => {
            factor_tail_diamonds(value, available, false)?;
            let declared = if let Expr::Jp { name, .. } = value.as_ref() {
                available.insert(name.clone()).then(|| name.clone())
            } else {
                None
            };
            factor_tail_diamonds(body, available, tail)?;
            if let Some(name) = declared {
                available.remove(&name);
            }
        }
        Expr::Jp { body, .. } => factor_tail_diamonds(body, available, true)?,
        Expr::If(condition, yes, no) => {
            factor_tail_diamonds(condition, available, false)?;
            factor_tail_diamonds(yes, available, tail)?;
            factor_tail_diamonds(no, available, tail)?;
        }
        Expr::Match {
            scrut,
            alts,
            default,
        } => {
            factor_tail_diamonds(scrut, available, false)?;
            for alt in alts {
                factor_tail_diamonds(&mut alt.body, available, tail)?;
            }
            if let Some(body) = default {
                factor_tail_diamonds(body, available, tail)?;
            }
        }
        _ => {
            for child in source.children_mut() {
                factor_tail_diamonds(child, available, false)?;
            }
        }
    }
    if tail && matches!(source, Expr::If(..) | Expr::Match { .. }) {
        if let Some(name) = tail_destination(source).filter(|name| available.contains(*name)) {
            let name = String::from(name);
            let mut argument = core::mem::replace(source, Expr::Nat(0));
            take_tail_arguments(&mut argument, &name)?;
            *source = Expr::Jmp(name, alloc::vec![argument]);
        }
    }
    Ok(())
}

fn validate_jumps(source: &Expr, context: &JpContext<'_>) -> Result<(), Error> {
    if let Expr::Jmp(name, arguments) = source {
        if !context
            .decls
            .get(name.as_str())
            .is_some_and(|(parameters, _)| parameters.len() == arguments.len())
        {
            return Err(Error::UnsupportedJoinPoint(name.clone()));
        }
    }
    for child in source.children() {
        validate_jumps(child, context)?;
    }
    Ok(())
}

fn reserve_compaction_nodes(source: &Expr, remaining: &mut usize) -> Result<(), Error> {
    *remaining = remaining.checked_sub(1).ok_or(Error::JoinExpansionLimit)?;
    for child in source.children() {
        reserve_compaction_nodes(child, remaining)?;
    }
    Ok(())
}

/// Input names are already alpha-unique. Callers normalize again afterward,
/// because each continuation expansion creates a new lexical binding scope.
pub(crate) fn expand(definition: &Definition) -> Result<Option<Definition>, Error> {
    let context = JpContext::collect(&definition.body);
    if context.decls.is_empty() {
        return Ok(None);
    }
    for name in context.decls.keys() {
        if context.is_cyclic(name) {
            return Err(Error::UnsupportedJoinPoint(String::from(*name)));
        }
    }
    validate_jumps(&definition.body, &context)?;
    let checked = cost(
        &definition.body,
        &context,
        &mut BTreeMap::new(),
        &mut BTreeSet::new(),
    );
    // Preserve the established lowering of every already-admitted definition.
    // The fallback never expands first and never raises the resource limits.
    if checked == Err(Error::JoinExpansionLimit) {
        // Bound the fallback's unexpanded working copy as well. This does not
        // alter previously admitted input or claim a general IR-depth bound.
        let mut remaining = MAX_NODES;
        reserve_compaction_nodes(&definition.body, &mut remaining)?;
    }
    let mut result = definition.clone();
    if checked == Err(Error::JoinExpansionLimit) {
        factor_tail_diamonds(&mut result.body, &mut BTreeSet::new(), true)?;
        let compact = JpContext::collect(&result.body);
        for name in compact.decls.keys() {
            if compact.is_cyclic(name) {
                return Err(Error::UnsupportedJoinPoint(String::from(*name)));
            }
        }
        validate_jumps(&result.body, &compact)?;
        cost(
            &result.body,
            &compact,
            &mut BTreeMap::new(),
            &mut BTreeSet::new(),
        )?;
        let compact_source = result.clone();
        let compact = JpContext::collect(&compact_source.body);
        expression(&mut result.body, &compact, &mut BTreeSet::new())?;
    } else {
        checked?;
        expression(&mut result.body, &context, &mut BTreeSet::new())?;
    }
    Ok(Some(result))
}

fn expression(
    source: &mut Expr,
    context: &JpContext<'_>,
    active: &mut BTreeSet<String>,
) -> Result<(), Error> {
    match source {
        Expr::Jmp(name, arguments) if context.decls.contains_key(name.as_str()) => {
            let (parameters, body) = context.decls[name.as_str()];
            if parameters.len() != arguments.len() || active.contains(name) {
                return Err(Error::UnsupportedJoinPoint(name.clone()));
            }
            // Arguments are evaluated in the caller's scope, in source order.
            for argument in arguments.iter_mut() {
                expression(argument, context, active)?;
            }
            active.insert(name.clone());
            let mut expanded = body.clone();
            expression(&mut expanded, context, active)?;
            active.remove(name);
            for (parameter, argument) in parameters.iter().zip(core::mem::take(arguments)).rev() {
                expanded = Expr::Let(parameter.clone(), Box::new(argument), Box::new(expanded));
            }
            *source = expanded;
        }
        Expr::Jp { name, body, .. } => {
            if context.jmp_count(name) == 0 {
                let mut expanded = *body.clone();
                expression(&mut expanded, context, active)?;
                *source = expanded;
            } else {
                // The declaration previously rendered unit; only jump sites
                // execute its body. Retain the let binder if raw IR uses it.
                *source = Expr::Ctor(String::from("Prod.mk"), Vec::new());
            }
        }
        _ => {
            for child in source.children_mut() {
                expression(child, context, active)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{format, vec};
    use prod_ir::Type;

    fn chain(length: usize, duplicate: bool) -> Definition {
        let mut body = Expr::Jmp(format!("join{}", length - 1), vec![Expr::Nat(1)]);
        for index in (0..length).rev() {
            let parameter = format!("value{index}");
            let continuation = if index == 0 {
                Expr::Var(parameter.clone())
            } else {
                let jump = Expr::Jmp(
                    format!("join{}", index - 1),
                    vec![Expr::Var(parameter.clone())],
                );
                if duplicate {
                    Expr::If(
                        Box::new(Expr::Bool(true)),
                        Box::new(jump.clone()),
                        Box::new(jump),
                    )
                } else {
                    jump
                }
            };
            let name = format!("join{index}");
            body = Expr::Let(
                name.clone(),
                Box::new(Expr::Jp {
                    name,
                    params: vec![parameter],
                    body: Box::new(continuation),
                }),
                Box::new(body),
            );
        }
        Definition {
            name: String::from("bounded"),
            params: vec![],
            ret: Type::Nat,
            body,
        }
    }

    fn measured(definition: &Definition) -> Result<Cost, Error> {
        cost(
            &definition.body,
            &JpContext::collect(&definition.body),
            &mut BTreeMap::new(),
            &mut BTreeSet::new(),
        )
    }

    #[test]
    fn exact_node_and_depth_boundaries_are_inclusive_and_checked() {
        let small = chain(1, false);
        let actual = measured(&small).unwrap();
        assert_eq!(actual, Cost { nodes: 5, depth: 1 });
        assert_eq!(actual.require(5, 1), Ok(actual));
        assert_eq!(actual.require(4, 1), Err(Error::JoinExpansionLimit));
        assert_eq!(actual.require(5, 0), Err(Error::JoinExpansionLimit));
        assert!(expand(&small).unwrap().is_some());
        let nodes = Cost {
            nodes: MAX_NODES,
            depth: MAX_DEPTH,
        };
        assert_eq!(nodes.add(Cost { nodes: 0, depth: 0 }), Ok(nodes));
        assert_eq!(
            nodes.add(Cost { nodes: 1, depth: 0 }),
            Err(Error::JoinExpansionLimit)
        );
        assert_eq!(
            Cost {
                nodes: usize::MAX,
                depth: 0
            }
            .add(nodes),
            Err(Error::JoinExpansionLimit)
        );
        assert_eq!(measured(&chain(MAX_DEPTH, false)).unwrap().depth, MAX_DEPTH);
        assert!(expand(&chain(MAX_DEPTH, false)).unwrap().is_some());
        assert_eq!(
            expand(&chain(MAX_DEPTH + 1, false)),
            Err(Error::JoinExpansionLimit)
        );
    }

    #[test]
    fn actual_expansion_accepts_exact_node_limit_and_rejects_one_more() {
        let mut source = chain(1, false);
        let Expr::Let(_, _, body) = &mut source.body else {
            unreachable!()
        };
        **body = Expr::Ctor(String::from("Host"), vec![Expr::Nat(0); MAX_NODES - 3]);
        assert_eq!(measured(&source).unwrap().nodes, MAX_NODES);
        assert!(expand(&source).unwrap().is_some());
        let Expr::Let(_, _, body) = &mut source.body else {
            unreachable!()
        };
        let Expr::Ctor(_, arguments) = body.as_mut() else {
            unreachable!()
        };
        arguments.push(Expr::Nat(0));
        assert_eq!(expand(&source), Err(Error::JoinExpansionLimit));
    }

    #[test]
    fn acyclic_exponential_expansion_is_rejected_before_materialization() {
        let mut source = chain(16, true);
        fn widen(source: &mut Expr) {
            match source {
                Expr::Jp { name, params, .. } => params.push(format!("extra{name}")),
                Expr::Jmp(_, arguments) => arguments.push(Expr::Nat(0)),
                _ => (),
            }
            for child in source.children_mut() {
                widen(child);
            }
        }
        // Multi-argument DAGs are not factored; the same hard guard still
        // refuses expansion before materializing an exponential tree.
        widen(&mut source.body);
        let original = source.clone();
        assert_eq!(expand(&source), Err(Error::JoinExpansionLimit));
        assert_eq!(source, original, "rejection does not modify source IR");
    }

    fn nodes(source: &Expr) -> usize {
        1 + source.children().map(nodes).sum::<usize>()
    }

    #[test]
    fn one_argument_diamonds_keep_the_guard_and_materialize_linear_size() {
        let source = chain(16, true);
        assert_eq!(measured(&source), Err(Error::JoinExpansionLimit));
        let expanded = expand(&source).unwrap().unwrap();
        assert!(nodes(&expanded.body) < 150);
        assert_eq!(source, chain(16, true), "factoring preserves source IR");
    }

    #[test]
    fn actual_verified_foundry_definition_is_compacted_before_materialization() {
        use sha2::{Digest, Sha256};
        let input = include_str!("../tests/fixtures/foundry_anonymous_ui_lcnf.ir");
        assert_eq!(
            format!("{:x}", Sha256::digest(input.as_bytes())),
            "7fda32ce4c2bde87716b034b819520f1c6728aafd78289e1df0823c80e369133"
        );
        let (remaining, module) = prod_ir::parser::parse_module(input).unwrap();
        assert!(remaining.is_empty());
        let source = module
            .definitions
            .iter()
            .find(|d| d.name == "anonymousPresentation")
            .unwrap();
        assert_eq!(nodes(&source.body), 834);
        assert_eq!(JpContext::collect(&source.body).decls.len(), 17);
        assert_eq!(measured(source), Err(Error::JoinExpansionLimit));
        let expanded = expand(source).unwrap().unwrap();
        assert!(
            nodes(&expanded.body) < 2_000,
            "actual expanded nodes {}",
            nodes(&expanded.body)
        );
        assert!(JpContext::collect(&expanded.body).decls.is_empty());
    }

    fn body(input: &str) -> Expr {
        let input = format!("(module Probe (def probe () Nat {input}))");
        prod_ir::parser::parse_module(&input)
            .unwrap()
            .1
            .definitions
            .remove(0)
            .body
    }

    #[test]
    fn factoring_preserves_branch_scopes_and_conditions_without_copying_arguments() {
        let mut source = body("(if flag (let local 1 (jmp finish (add local 3))) (let local 2 (jmp finish (add local 4))))");
        let expected =
            body("(jmp finish (if flag (let local 1 (add local 3)) (let local 2 (add local 4))))");
        factor_tail_diamonds(
            &mut source,
            &mut BTreeSet::from([String::from("finish")]),
            true,
        )
        .unwrap();
        assert_eq!(source, expected);
    }

    #[test]
    fn factoring_visits_default_branches_and_requires_one_lexically_available_target() {
        let mut source =
            body("(cases flag (alt \"Bool.true\" () (jmp finish 1)) (default (jmp finish 2)))");
        let expected = body("(jmp finish (cases flag (alt \"Bool.true\" () 1) (default 2)))");
        factor_tail_diamonds(
            &mut source,
            &mut BTreeSet::from([String::from("finish")]),
            true,
        )
        .unwrap();
        assert_eq!(source, expected);
        for input in [
            "(if flag (jmp finish 1) (jmp other 2))",
            "(if flag (jmp finish 1 2) (jmp finish 3 4))",
            "(cases flag (alt \"Bool.true\" () (jmp finish 1)) (default (jmp other 2)))",
            "(add 1 (if flag (jmp finish 1) (jmp finish 2)))",
            "(let result (if flag (jmp finish 1) (jmp finish 2)) result)",
        ] {
            let mut source = body(input);
            let original = source.clone();
            factor_tail_diamonds(
                &mut source,
                &mut BTreeSet::from([String::from("finish"), String::from("other")]),
                true,
            )
            .unwrap();
            assert_eq!(
                source, original,
                "unsupported shape remains unchanged: {input}"
            );
        }
        let mut source = body("(if flag (jmp hidden 1) (jmp hidden 2))");
        let original = source.clone();
        factor_tail_diamonds(&mut source, &mut BTreeSet::new(), true).unwrap();
        assert_eq!(
            source, original,
            "join identity cannot escape its declaration scope"
        );
    }

    #[test]
    fn malformed_branches_are_checked_before_early_expansion_refusal() {
        for bad in ["(jmp absent 1)", "(jmp join0 1 2)"] {
            let source = chain(16, true);
            let invalid = Definition {
                body: Expr::If(
                    Box::new(Expr::Bool(true)),
                    Box::new(source.body),
                    Box::new(body(bad)),
                ),
                ..source
            };
            assert!(matches!(
                expand(&invalid),
                Err(Error::UnsupportedJoinPoint(_))
            ));
        }
        let source = chain(16, true);
        let cyclic = body("(let hidden (jp hidden (value) (jmp hidden value)) (jmp hidden 1))");
        let invalid = Definition {
            body: Expr::If(
                Box::new(Expr::Bool(true)),
                Box::new(source.body),
                Box::new(cyclic),
            ),
            ..source
        };
        assert!(matches!(
            expand(&invalid),
            Err(Error::UnsupportedJoinPoint(_))
        ));
    }
}
