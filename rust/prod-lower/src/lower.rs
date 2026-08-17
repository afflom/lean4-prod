//! `Expr` -> [`crate::target`], for one definition.
//!
//! This is where a fallibility decision is *made*. Every printer downstream
//! reads the answer off the statement list rather than re-deriving it, which
//! is the whole point of the split: the same `Nat.add` becomes a
//! [`Stmt::TryLet`] under a profile whose `Nat` is a `u64` and a plain
//! [`TExpr::BinOp`] under one whose `Nat` is unbounded, and no backend gets a
//! vote.

use crate::error::LowerError;
use crate::profile::{DivisionSemantics, TargetProfile};
use crate::shape::{Shape, Signatures};
use crate::target::{Arm, BinOp, Body, ErrorCode, FallibleOp, Lit, Stmt, TExpr};
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use prod_ir::{Definition, Expr, NumKind, Type};

/// Lower one definition to its [`Body`].
pub fn lower_def(
    def: &Definition,
    shapes: &Signatures,
    profile: &TargetProfile,
) -> Result<Body, LowerError> {
    let shape = shapes
        .get(def.name.as_str())
        .copied()
        .unwrap_or(Shape::Value);
    if matches!(shape, Shape::Buffer | Shape::StaticList) {
        // List-shaped definitions are Task 6: they need the buffer index
        // arithmetic and the `Push` statement, which nothing here emits.
        return Err(LowerError::NotYetLowered(format!(
            "{:?}-shaped body",
            shape
        )));
    }
    let mut lowering = Lowering {
        params: &def.params,
        shapes,
        profile,
        next_temp: 0,
        reserved: bound_names(def),
        bound: def.params.iter().map(|(n, _)| n.clone()).collect(),
        scope: Vec::new(),
        types: Vec::new(),
        jps: JpContext::collect(&def.body),
    };
    // The body is lowered in TAIL position: control flow is a statement here,
    // so each branch supplies its own terminator rather than yielding a value
    // for a `Return` this function appends.
    let mut stmts: Vec<Stmt> = Vec::new();
    lowering.tail(&def.body, &mut stmts)?;
    Ok(Body {
        name: def.name.clone(),
        params: def.params.clone(),
        ret: def.ret.clone(),
        shape,
        stmts,
    })
}

/// Which of Lean's two total-but-differently-zero integer operations is being
/// lowered. They share a divisor-is-zero guard but not its value.
#[derive(Clone, Copy)]
enum DivMod {
    Div,
    Mod,
}

/// Lowering makes every binder in a [`Body`] unique, because the Target IR has
/// no nested scope to rely on.
///
/// `Expr::Let` is an *expression* -- it can sit in an operand -- and the
/// statement list it lowers into is flat, so its `Stmt::Let` lands in the
/// enclosing list and stays live for everything after it. Lean's scoping said
/// otherwise. In `Add(Let("x", 1, Var("x")), Var("x"))` over a parameter `x`,
/// the second operand means the *parameter*; flattened naively it would read
/// the inner binding and the definition would compute `2` where Lean says
/// `1 + x`.
///
/// So a source binder that collides with a name already bound in this body is
/// renamed, and references within its own body are rewritten to the new name.
/// Only on an actual collision: the common case keeps the name the source
/// wrote, which is what a reader of the generated code wants to see.
///
/// Uniqueness is what makes flattening sound at all, and the printer depends
/// on it a second time: `uses()` there counts reads by name with no scope of
/// its own, so two live bindings sharing a name would corrupt the decision to
/// fold a temporary into its single use.
struct Lowering<'a> {
    params: &'a [(String, Type)],
    shapes: &'a Signatures<'a>,
    profile: &'a TargetProfile,
    next_temp: usize,
    /// Every name the source definition binds anywhere, collected up front. A
    /// generated temporary must avoid all of them, including binders it has
    /// not reached yet.
    reserved: BTreeSet<String>,
    /// Target names bound so far, parameters included. Membership here is
    /// exactly the collision test.
    bound: BTreeSet<String>,
    /// Source name -> target name, for the binders whose body the lowering is
    /// currently inside. Popped on the way out, so a sibling `let` of the same
    /// name does not resolve through it.
    scope: Vec<(String, String)>,
    /// Target name -> type, for every binding made. Never popped: target names
    /// are unique, so an entry can never be shadowed.
    types: Vec<(String, Type)>,
    /// Join-point declarations and their call counts, collected once for the
    /// whole body.
    jps: JpContext<'a>,
}

impl<'a> Lowering<'a> {
    fn fresh(&mut self) -> String {
        loop {
            let name = format!("t{}", self.next_temp);
            self.next_temp += 1;
            if !self.reserved.contains(&name) && !self.bound.contains(&name) {
                self.bound.insert(name.clone());
                return name;
            }
        }
    }

    /// The target name for a source binder: its own, or a fresh one if that is
    /// already taken.
    fn bind_source(&mut self, name: &str) -> String {
        if self.bound.contains(name) {
            return self.fresh();
        }
        self.bound.insert(String::from(name));
        String::from(name)
    }

    /// The target name a source `Var` refers to: the innermost binder of that
    /// name whose body we are inside, or the name itself (a parameter, or a
    /// name this slice does not bind).
    fn resolve(&self, name: &str) -> String {
        self.scope
            .iter()
            .rev()
            .find(|(source, _)| source == name)
            .map(|(_, target)| target.clone())
            .unwrap_or_else(|| String::from(name))
    }

    fn expr(&mut self, e: &Expr, stmts: &mut Vec<Stmt>) -> Result<TExpr, LowerError> {
        match e {
            Expr::Nat(n) => Ok(TExpr::Lit(Lit::Nat(*n))),
            Expr::Int(n) => Ok(TExpr::Lit(Lit::Int(*n))),
            Expr::Bool(b) => Ok(TExpr::Lit(Lit::Bool(*b))),
            Expr::Var(name) => Ok(TExpr::Var(self.resolve(name))),
            Expr::Param(index) => self
                .params
                .get(*index)
                .map(|(name, _)| TExpr::Var(name.clone()))
                .ok_or(LowerError::ParamOutOfBounds(*index)),

            Expr::Add(k, a, b) => self.arith(e, *k, BinOp::Add, a, b, stmts),
            Expr::Sub(k, a, b) => self.arith(e, *k, BinOp::Sub, a, b, stmts),
            Expr::Mul(k, a, b) => self.arith(e, *k, BinOp::Mul, a, b, stmts),
            Expr::Div(k, a, b) => {
                let op = self.division_op(*k, DivMod::Div);
                self.arith(e, *k, op, a, b, stmts)
            }
            Expr::Mod(k, a, b) => {
                let op = self.division_op(*k, DivMod::Mod);
                self.arith(e, *k, op, a, b, stmts)
            }
            // Shifts on `Int` are a deliberate non-goal, rejected here rather
            // than in a printer: the printers are total by construction, so a
            // construct no backend will render must be refused where the
            // semantics live.
            Expr::Shl(k, a, b) => {
                reject_int_shift(*k)?;
                self.arith(e, *k, BinOp::Shl, a, b, stmts)
            }
            Expr::Shr(k, a, b) => {
                reject_int_shift(*k)?;
                self.arith(e, *k, BinOp::Shr, a, b, stmts)
            }
            // Sized `pow` is rejected, not rendered: narrowing a `u64`
            // exponent to the `u32` that `wrapping_pow` takes would silently
            // compute a different number, and `pow` has no absorbing
            // out-of-range case the way a shift does.
            Expr::Pow(k, a, b) => {
                if !matches!(k, NumKind::Nat | NumKind::Int) {
                    return Err(LowerError::UnsupportedKind(format!(
                        "pow is not supported for sized kind {:?} (unsound u32 exponent narrowing)",
                        k
                    )));
                }
                self.arith(e, *k, BinOp::Pow, a, b, stmts)
            }
            Expr::Neg(k, a) => {
                if *k != NumKind::Int {
                    return Err(LowerError::UnsupportedKind(format!(
                        "unary negation is only supported for Int, not {:?}",
                        k
                    )));
                }
                let value = self.expr(a, stmts)?;
                if self.profile.op_is_fallible(e) {
                    Ok(self.bind_fallible(Type::Int, FallibleOp::Neg(*k, value), stmts))
                } else {
                    // Unreachable today -- every profile makes `Int` negation
                    // fallible -- and `TExpr` has no unary minus to fall back
                    // on, so a profile that made it total would need a node
                    // this slice does not define.
                    Err(LowerError::NotYetLowered(String::from("total Neg")))
                }
            }

            // The value is lowered BEFORE the binder is in scope, so a
            // `let x := x + 1` still reads the outer `x` on the right.
            Expr::Let(name, value, body) => {
                let bound = self.bind_let(name, value, stmts)?;
                let out = self.expr(body, stmts);
                if bound {
                    self.scope.pop();
                }
                out
            }

            // A join point declaration in VALUE position. Its body is the
            // declaration's value when nothing jumps to it; when something
            // does, the body belongs at the jump site and the declaration
            // itself has no value to give. `bind_let` elides the `let` that
            // LCNF wraps it in, so reaching the second case means the `jp`
            // sat somewhere a value was actually wanted.
            Expr::Jp { name, body, .. } => {
                if self.jps.jmp_count(name) == 0 {
                    self.expr(body, stmts)
                } else if self.jps.is_inlineable(name) {
                    Err(LowerError::NotYetLowered(format!(
                        "jp `{}` declared outside a `let` binding",
                        name
                    )))
                } else {
                    Err(LowerError::UnsupportedJoinPoint(name.clone()))
                }
            }

            Expr::Jmp(name, args) => {
                let (body, pushed) = self.inline_jmp(name, args, stmts)?;
                let out = self.expr(body, stmts);
                self.scope.truncate(self.scope.len() - pushed);
                out
            }

            Expr::Call(name, args) => {
                let mut lowered = Vec::with_capacity(args.len());
                for arg in args {
                    lowered.push(self.expr(arg, stmts)?);
                }
                match self.shapes.get(name.as_str()) {
                    Some(Shape::Fallible) => Ok(self.bind_fallible(
                        unknown_type(),
                        FallibleOp::Call(name.clone(), lowered),
                        stmts,
                    )),
                    Some(Shape::Buffer) | Some(Shape::StaticList) => Err(
                        LowerError::NotYetLowered(format!("Call to list-shaped `{}`", name)),
                    ),
                    Some(Shape::Value) | None => Ok(TExpr::Call(name.clone(), lowered)),
                }
            }

            other => Err(LowerError::NotYetLowered(String::from(node_name(other)))),
        }
    }

    /// Lower `e` in TAIL position: the statements it needs, ending in a
    /// terminator ([`Stmt::Return`], [`Stmt::If`], [`Stmt::Switch`] or
    /// [`Stmt::Fail`]).
    ///
    /// # Why branches get their own accumulator
    ///
    /// **A `TryLet` must never cross a control-flow boundary.** Every branch
    /// is lowered into a `Vec<Stmt>` of its own, so nothing a branch needs can
    /// be lifted into the enclosing list. Hoisting a branch's `TryLet` to the
    /// top would evaluate it even when the branch does not run -- turning a
    /// short-circuit into eager evaluation, and reporting an overflow where
    /// Lean, whose `Nat` is unbounded and whose `if` is lazy in its arms, has
    /// no failure at all. That is not a formatting difference; it is a
    /// different function.
    ///
    /// The scrutinee and the condition are lowered into the ENCLOSING list on
    /// purpose: they are evaluated unconditionally, whichever way the branch
    /// goes.
    fn tail(&mut self, e: &Expr, stmts: &mut Vec<Stmt>) -> Result<(), LowerError> {
        match e {
            Expr::If(cond, then_, else_) => {
                let cond = self.expr(cond, stmts)?;
                let mut then_stmts: Vec<Stmt> = Vec::new();
                self.tail(then_, &mut then_stmts)?;
                let mut else_stmts: Vec<Stmt> = Vec::new();
                self.tail(else_, &mut else_stmts)?;
                stmts.push(Stmt::If {
                    cond,
                    then: then_stmts,
                    else_: else_stmts,
                });
                Ok(())
            }

            Expr::Match {
                scrut,
                alts,
                default,
            } => {
                let scrut = self.expr(scrut, stmts)?;
                let mut arms = Vec::with_capacity(alts.len());
                for alt in alts {
                    // An alternative's binders are source binders like any
                    // other: they go through `bind_source`, so one that
                    // shadows a parameter is renamed, and through `scope`, so
                    // reads inside the arm resolve to the renamed binder.
                    // Without both, the printer's `uses()` -- which counts
                    // reads by name and has no scope of its own -- would pool
                    // the arm's reads with the parameter's.
                    let mut binders = Vec::with_capacity(alt.binders.len());
                    for binder in &alt.binders {
                        let target = self.bind_source(binder);
                        self.scope.push((binder.clone(), target.clone()));
                        binders.push(target);
                    }
                    let mut body: Vec<Stmt> = Vec::new();
                    let out = self.tail(&alt.body, &mut body);
                    self.scope.truncate(self.scope.len() - alt.binders.len());
                    out?;
                    arms.push(Arm {
                        ctor: alt.ctor.clone(),
                        binders,
                        body,
                    });
                }
                let default = match default {
                    Some(d) => {
                        let mut body: Vec<Stmt> = Vec::new();
                        self.tail(d, &mut body)?;
                        Some(body)
                    }
                    None => None,
                };
                stmts.push(Stmt::Switch {
                    scrut,
                    arms,
                    default,
                });
                Ok(())
            }

            // A branch LCNF proved dead. It is a terminator, not a value, so
            // it has no lowering in operand position.
            Expr::Unreachable => {
                stmts.push(Stmt::Fail(ErrorCode::Unreachable));
                Ok(())
            }

            Expr::Let(name, value, body) => {
                let bound = self.bind_let(name, value, stmts)?;
                let out = self.tail(body, stmts);
                if bound {
                    self.scope.pop();
                }
                out
            }

            Expr::Jp { name, body, .. } if self.jps.jmp_count(name) == 0 => self.tail(body, stmts),

            Expr::Jmp(name, args) => {
                let (body, pushed) = self.inline_jmp(name, args, stmts)?;
                let out = self.tail(body, stmts);
                self.scope.truncate(self.scope.len() - pushed);
                out
            }

            // Everything else is a value: lower it and return it.
            other => {
                let value = self.expr(other, stmts)?;
                stmts.push(Stmt::Return(value));
                Ok(())
            }
        }
    }

    /// Emit the binding for a source `let` and put it in scope. Returns
    /// whether a scope entry was pushed, so the caller knows to pop it.
    ///
    /// The value is lowered BEFORE the binder is in scope, so a
    /// `let x := x + 1` still reads the outer `x` on the right.
    fn bind_let(
        &mut self,
        name: &str,
        value: &Expr,
        stmts: &mut Vec<Stmt>,
    ) -> Result<bool, LowerError> {
        // LCNF writes a join point as `let g := jp g (..) ..; <continuation>`.
        // When the join point is inlined at its jump site the declaration has
        // nothing left to bind, so the `let` disappears entirely rather than
        // binding a unit nobody reads.
        if let Expr::Jp { name: jp, .. } = value {
            if self.jps.is_inlineable(jp) {
                return Ok(false);
            }
        }
        let value = self.expr(value, stmts)?;
        let ty = self.type_of(&value);
        let target = self.bind_source(name);
        stmts.push(Stmt::Let {
            name: target.clone(),
            ty: ty.clone(),
            value,
        });
        self.types.push((target.clone(), ty));
        self.scope.push((String::from(name), target));
        Ok(true)
    }

    /// Bind a join point's parameters at its jump site and hand back its body
    /// for the caller to lower in whatever position the `jmp` itself was in,
    /// plus the number of scope entries to pop afterwards.
    ///
    /// Only the single-caller, non-cyclic form is inlined; everything else is
    /// [`LowerError::UnsupportedJoinPoint`], which is exactly the set
    /// `prod-codegen` rejects today. Widening that is not this task.
    ///
    /// The arguments are all lowered before any parameter is bound: they are
    /// evaluated in the CALLER's scope, so a later argument must not read a
    /// parameter this jump is in the middle of binding.
    fn inline_jmp(
        &mut self,
        name: &str,
        args: &[Expr],
        stmts: &mut Vec<Stmt>,
    ) -> Result<(&'a Expr, usize), LowerError> {
        let Some((params, body)) = self.jps.decls.get(name).copied() else {
            return Err(LowerError::UnsupportedJoinPoint(String::from(name)));
        };
        if !self.jps.is_inlineable(name) {
            return Err(LowerError::UnsupportedJoinPoint(String::from(name)));
        }
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            values.push(self.expr(arg, stmts)?);
        }
        let mut pushed = 0;
        for (param, value) in params.iter().zip(values) {
            let ty = self.type_of(&value);
            let target = self.bind_source(param);
            stmts.push(Stmt::Let {
                name: target.clone(),
                ty: ty.clone(),
                value,
            });
            self.types.push((target.clone(), ty));
            self.scope.push((param.clone(), target));
            pushed += 1;
        }
        Ok((body, pushed))
    }

    /// Lower a binary arithmetic node, hoisting it to a [`Stmt::TryLet`]
    /// exactly when the profile says it can fail.
    fn arith(
        &mut self,
        node: &Expr,
        kind: NumKind,
        op: BinOp,
        a: &Expr,
        b: &Expr,
        stmts: &mut Vec<Stmt>,
    ) -> Result<TExpr, LowerError> {
        let a = self.expr(a, stmts)?;
        let b = self.expr(b, stmts)?;
        if self.profile.op_is_fallible(node) {
            Ok(self.bind_fallible(kind_type(kind), FallibleOp::Arith(kind, op, a, b), stmts))
        } else {
            Ok(TExpr::BinOp(kind, op, Box::new(a), Box::new(b)))
        }
    }

    /// Which division operator computes *Lean's* answer on this host.
    ///
    /// Lean's `Int` division is Euclidean (`Int.ediv`/`Int.emod`, "for
    /// compatibility with SMT-LIB"): `(-12) / 7 = -2` and `(-12) % 7 = 2`,
    /// where a truncating host gives `-1` and `-5` and a flooring host agrees
    /// only while the divisor is positive. Whether that needs correcting is a
    /// property of the host, declared once in
    /// [`TargetProfile::host_division`] -- not something each printer decides.
    ///
    /// `Nat` and the sized kinds are unsigned, where truncating, flooring and
    /// Euclidean division all coincide, so no host needs a correction there.
    fn division_op(&self, kind: NumKind, which: DivMod) -> BinOp {
        let needs_correction =
            kind == NumKind::Int && self.profile.host_division != DivisionSemantics::Euclidean;
        match (which, needs_correction) {
            (DivMod::Div, false) => BinOp::Div,
            (DivMod::Div, true) => BinOp::DivE,
            (DivMod::Mod, false) => BinOp::Mod,
            (DivMod::Mod, true) => BinOp::ModE,
        }
    }

    fn bind_fallible(&mut self, ty: Type, op: FallibleOp, stmts: &mut Vec<Stmt>) -> TExpr {
        let name = self.fresh();
        stmts.push(Stmt::TryLet {
            name: name.clone(),
            ty: ty.clone(),
            op,
        });
        self.types.push((name.clone(), ty));
        TExpr::Var(name)
    }

    /// Best-effort type of a lowered expression, for the binder it is about to
    /// be bound to.
    fn type_of(&self, e: &TExpr) -> Type {
        match e {
            TExpr::Lit(Lit::Nat(_)) => Type::Nat,
            TExpr::Lit(Lit::Int(_)) => Type::Int,
            TExpr::Lit(Lit::Bool(_)) => Type::Bool,
            TExpr::BinOp(kind, op, ..) => match op {
                BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt => Type::Bool,
                _ => kind_type(*kind),
            },
            TExpr::Not(_) | TExpr::And(..) | TExpr::Or(..) => Type::Bool,
            TExpr::Var(name) => self
                .types
                .iter()
                .rev()
                .chain(self.params.iter().rev())
                .find(|(bound, _)| bound == name)
                .map(|(_, ty)| ty.clone())
                .unwrap_or_else(unknown_type),
            TExpr::Call(..) | TExpr::Ctor(..) | TExpr::Proj(..) => unknown_type(),
        }
    }
}

/// Join-point analysis for one definition body.
///
/// Ported unchanged from `prod-codegen`'s renderer, deliberately: the policy
/// it encodes -- inline the single-caller, non-cyclic form, reject the rest --
/// is the behaviour the Task 7 cutover has to reproduce byte for byte, so it
/// moves without being widened.
struct JpContext<'a> {
    /// name -> (params, body) of each `jp` declaration in the body
    decls: BTreeMap<&'a str, (&'a [String], &'a Expr)>,
    /// name -> total number of `jmp` sites in the body
    jmp_counts: BTreeMap<&'a str, usize>,
}

impl<'a> JpContext<'a> {
    fn collect(body: &'a Expr) -> Self {
        let mut ctx = JpContext {
            decls: BTreeMap::new(),
            jmp_counts: BTreeMap::new(),
        };
        ctx.walk(body);
        ctx
    }

    fn walk(&mut self, expr: &'a Expr) {
        match expr {
            Expr::Jp { name, params, body } => {
                self.decls.insert(name.as_str(), (params, body));
            }
            Expr::Jmp(name, _) => {
                *self.jmp_counts.entry(name.as_str()).or_insert(0) += 1;
            }
            _ => {}
        }
        for child in expr.children() {
            self.walk(child);
        }
    }

    fn jmp_count(&self, name: &str) -> usize {
        self.jmp_counts.get(name).copied().unwrap_or(0)
    }

    /// A join point is cyclic if a jump to it occurs inside its own body.
    fn is_cyclic(&self, name: &str) -> bool {
        match self.decls.get(name) {
            Some((_, body)) => count_jmps(body, name) > 0,
            None => false,
        }
    }

    /// Inlineable: exactly one caller, and not self-referential.
    fn is_inlineable(&self, name: &str) -> bool {
        self.jmp_count(name) == 1 && !self.is_cyclic(name)
    }
}

/// Number of `jmp <name>` sites within `expr`.
fn count_jmps(expr: &Expr, name: &str) -> usize {
    let self_count = match expr {
        Expr::Jmp(n, _) if n == name => 1,
        _ => 0,
    };
    self_count + expr.children().map(|c| count_jmps(c, name)).sum::<usize>()
}

fn kind_type(kind: NumKind) -> Type {
    match kind {
        NumKind::Nat => Type::Nat,
        NumKind::Int => Type::Int,
        other => Type::UInt(other),
    }
}

/// The type a binder gets when this slice cannot determine one.
///
/// [`Signatures`] records each definition's [`Shape`], not its return type, so
/// a call's result is untyped here, as are constructors and projections.
/// Rust's `let` infers, so `prod-emit-rust` never reads the field; a C backend
/// will, and Task 6/7 widens the table consulted here. Spelled `Opaque`
/// deliberately rather than guessed: a printer that does read it then fails
/// loudly instead of declaring the wrong type.
fn unknown_type() -> Type {
    Type::Opaque(String::from("?"))
}

fn reject_int_shift(kind: NumKind) -> Result<(), LowerError> {
    if kind == NumKind::Int {
        return Err(LowerError::UnsupportedKind(String::from(
            "shifts are not supported for Int",
        )));
    }
    Ok(())
}

/// Every name the definition binds: its parameters, its `let`s, its join
/// points and their parameters, and its match binders.
fn bound_names(def: &Definition) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = def.params.iter().map(|(n, _)| n.clone()).collect();
    collect_bound(&def.body, &mut out);
    out
}

fn collect_bound(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Let(name, ..) => {
            out.insert(name.clone());
        }
        Expr::Jp { name, params, .. } => {
            out.insert(name.clone());
            out.extend(params.iter().cloned());
        }
        Expr::Match { alts, .. } => {
            for alt in alts {
                out.extend(alt.binders.iter().cloned());
            }
        }
        _ => {}
    }
    for child in e.children() {
        collect_bound(child, out);
    }
}

/// The variant name reported by [`LowerError::NotYetLowered`].
///
/// Exhaustive on purpose: a new `Expr` variant is a compile error here, which
/// is the prompt to give it a lowering rather than let it fall into a
/// wildcard.
fn node_name(e: &Expr) -> &'static str {
    match e {
        Expr::Nat(_) => "Nat",
        Expr::Int(_) => "Int",
        Expr::Bool(_) => "Bool",
        Expr::Var(_) => "Var",
        Expr::Param(_) => "Param",
        Expr::Add(..) => "Add",
        Expr::Sub(..) => "Sub",
        Expr::Mul(..) => "Mul",
        Expr::Div(..) => "Div",
        Expr::Mod(..) => "Mod",
        Expr::Shl(..) => "Shl",
        Expr::Shr(..) => "Shr",
        Expr::Pow(..) => "Pow",
        Expr::Neg(..) => "Neg",
        Expr::Convert(..) => "Convert",
        Expr::Eq(..) => "Eq",
        Expr::Lt(..) => "Lt",
        Expr::Le(..) => "Le",
        Expr::Gt(..) => "Gt",
        Expr::If(..) => "If",
        Expr::Let(..) => "Let",
        Expr::Call(..) => "Call",
        Expr::Match { .. } => "Match",
        Expr::Ctor(..) => "Ctor",
        Expr::Proj(..) => "Proj",
        Expr::Jp { .. } => "Jp",
        Expr::Jmp(..) => "Jmp",
        Expr::Unreachable => "Unreachable",
        Expr::Opaque(_) => "Opaque",
        Expr::Extern(..) => "Extern",
        Expr::And(..) => "And",
        Expr::Or(..) => "Or",
        Expr::Not(..) => "Not",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::{DivisionSemantics, TargetProfile};
    use crate::shape::signatures;
    use crate::target::*;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use prod_ir::{Alt, Definition, Expr, NumKind, Type};

    fn def_add() -> Definition {
        Definition {
            name: String::from("f"),
            params: vec![
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            ),
        }
    }

    #[test]
    fn a_fallible_op_becomes_a_trylet_and_a_return() {
        let defs = vec![def_add()];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        assert_eq!(
            body.stmts.len(),
            2,
            "expected TryLet + Return, got {:?}",
            body.stmts
        );
        assert!(matches!(
            &body.stmts[0],
            Stmt::TryLet {
                op: FallibleOp::Arith(NumKind::Nat, BinOp::Add, ..),
                ..
            }
        ));
        match (&body.stmts[0], &body.stmts[1]) {
            (Stmt::TryLet { name, .. }, Stmt::Return(TExpr::Var(v))) => {
                assert_eq!(
                    v, name,
                    "the Return must name the temporary the TryLet bound"
                );
            }
            other => panic!(
                "expected TryLet then Return of its temporary, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn the_same_op_is_a_plain_binop_under_an_exact_nat_profile() {
        // Not a formatting difference: under Exact there is no failure to
        // hoist, so the statement list has a different SHAPE. This is the
        // fallibility decision being made once, in the lowering.
        let defs = vec![def_add()];
        let shapes = signatures(&defs, &TargetProfile::PYTHON);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::PYTHON).expect("lowers");

        assert_eq!(
            body.stmts.len(),
            1,
            "expected a bare Return, got {:?}",
            body.stmts
        );
        assert!(matches!(
            &body.stmts[0],
            Stmt::Return(TExpr::BinOp(NumKind::Nat, BinOp::Add, ..))
        ));
    }
    fn def_int_div(op: fn(NumKind, Box<Expr>, Box<Expr>) -> Expr) -> Definition {
        Definition {
            name: String::from("f"),
            params: vec![
                (String::from("a"), Type::Int),
                (String::from("b"), Type::Int),
            ],
            ret: Type::Int,
            body: op(
                NumKind::Int,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            ),
        }
    }

    fn div_op(def: &Definition, profile: &TargetProfile) -> BinOp {
        let defs = vec![def.clone()];
        let shapes = signatures(&defs, profile);
        let body = lower_def(&defs[0], &shapes, profile).expect("lowers");
        for stmt in &body.stmts {
            match stmt {
                Stmt::TryLet {
                    op: FallibleOp::Arith(_, op, ..),
                    ..
                } => return *op,
                Stmt::Return(TExpr::BinOp(_, op, ..)) => return *op,
                _ => {}
            }
        }
        panic!("no arithmetic operator in {:?}", body.stmts)
    }

    /// The Euclidean correction is the profile's decision, not the printer's.
    ///
    /// Lean's `Int` division is `Int.ediv`/`Int.emod`. A host that already
    /// divides that way needs no correction; one that truncates or floors
    /// does. Nothing downstream re-derives this -- the operator in the Target
    /// IR already says which.
    #[test]
    fn the_euclidean_correction_is_chosen_by_host_division() {
        let euclidean_host = TargetProfile {
            host_division: DivisionSemantics::Euclidean,
            ..TargetProfile::RUST
        };

        // Rust truncates: `(-12) / 7` is `-1` there and `-2` in Lean.
        assert_eq!(
            div_op(&def_int_div(Expr::Div), &TargetProfile::RUST),
            BinOp::DivE
        );
        assert_eq!(
            div_op(&def_int_div(Expr::Mod), &TargetProfile::RUST),
            BinOp::ModE
        );
        // Python floors, which agrees with Euclidean only while the divisor
        // is positive -- so it needs the correction too.
        assert_eq!(
            div_op(&def_int_div(Expr::Div), &TargetProfile::PYTHON),
            BinOp::DivE
        );
        // A host whose own division is Euclidean gets the plain operator.
        assert_eq!(div_op(&def_int_div(Expr::Div), &euclidean_host), BinOp::Div);
        assert_eq!(div_op(&def_int_div(Expr::Mod), &euclidean_host), BinOp::Mod);
    }

    /// Unsigned kinds need no correction under any host: truncating, flooring
    /// and Euclidean division all coincide on non-negative operands.
    #[test]
    fn unsigned_division_never_takes_the_euclidean_correction() {
        for kind in [NumKind::Nat, NumKind::U8, NumKind::U64] {
            let ty = if kind == NumKind::Nat {
                Type::Nat
            } else {
                Type::UInt(kind)
            };
            let def = Definition {
                name: String::from("f"),
                params: vec![
                    (String::from("a"), ty.clone()),
                    (String::from("b"), ty.clone()),
                ],
                ret: ty,
                body: Expr::Div(
                    kind,
                    Box::new(Expr::Var(String::from("a"))),
                    Box::new(Expr::Var(String::from("b"))),
                ),
            };
            assert_eq!(div_op(&def, &TargetProfile::RUST), BinOp::Div);
            assert_eq!(div_op(&def, &TargetProfile::PYTHON), BinOp::Div);
        }
    }

    /// A generated temporary must never collide with a name the definition
    /// binds: the printer may fold a temporary into its single use, and a
    /// `let t0` in between would shadow it.
    #[test]
    fn a_fresh_temporary_skips_a_name_the_source_already_binds() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("a"), Type::Nat)],
            ret: Type::Nat,
            // let t0 := a; t0 + t0
            body: Expr::Let(
                String::from("t0"),
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Add(
                    NumKind::Nat,
                    Box::new(Expr::Var(String::from("t0"))),
                    Box::new(Expr::Var(String::from("t0"))),
                )),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        let bound: Vec<&String> = body
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::TryLet { name, .. } => Some(name),
                _ => None,
            })
            .collect();
        assert_eq!(bound, vec![&String::from("t1")], "got {:?}", body.stmts);
    }
    /// The scoping the flattened statement list has to preserve by hand.
    ///
    /// `f(x) = (let x := 1; x) + x`. Lean's second operand is the PARAMETER --
    /// the inner binding's scope ends at the first operand. Hoisting
    /// `let x = 1;` into the enclosing list without renaming would put it in
    /// scope for the second operand too, and the definition would compute
    /// `1 + 1` where Lean says `1 + x`. The old renderer got this from the
    /// brace in `{ let x = 1; x } + x`; a flat list has no brace, so the
    /// lowering renames instead.
    #[test]
    fn a_let_shadowing_a_parameter_does_not_capture_later_uses() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Let(
                    String::from("x"),
                    Box::new(Expr::Nat(1)),
                    Box::new(Expr::Var(String::from("x"))),
                )),
                Box::new(Expr::Var(String::from("x"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        let inner = match &body.stmts[0] {
            Stmt::Let { name, .. } => name.clone(),
            other => panic!("expected the hoisted Let first, got {:?}", other),
        };
        assert_ne!(inner, "x", "the inner binder must be renamed off the param");

        match &body.stmts[1] {
            Stmt::TryLet {
                op: FallibleOp::Arith(_, BinOp::Add, a, b),
                ..
            } => {
                assert_eq!(a, &TExpr::Var(inner), "first operand is the inner binding");
                assert_eq!(
                    b,
                    &TExpr::Var(String::from("x")),
                    "second operand must still be the PARAMETER, got {:?}",
                    b
                );
            }
            other => panic!("expected the add, got {:?}", other),
        }
    }

    /// Two sibling `let`s of the same name are two different bindings. The
    /// first one's value has already been read into an operand by the time the
    /// second is emitted, so the second must not take its name.
    #[test]
    fn sibling_lets_of_the_same_name_get_different_binders() {
        let shadow = |n: u64| {
            Expr::Let(
                String::from("y"),
                Box::new(Expr::Nat(n)),
                Box::new(Expr::Var(String::from("y"))),
            )
        };
        let def = Definition {
            name: String::from("f"),
            params: vec![],
            ret: Type::Nat,
            body: Expr::Add(NumKind::Nat, Box::new(shadow(1)), Box::new(shadow(2))),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        let binders: Vec<String> = body
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Let { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(binders.len(), 2, "got {:?}", body.stmts);
        assert_ne!(binders[0], binders[1], "got {:?}", body.stmts);

        match &body.stmts[2] {
            Stmt::TryLet {
                op: FallibleOp::Arith(_, BinOp::Add, a, b),
                ..
            } => {
                assert_eq!(a, &TExpr::Var(binders[0].clone()));
                assert_eq!(b, &TExpr::Var(binders[1].clone()));
            }
            other => panic!("expected the add, got {:?}", other),
        }
    }

    /// Renaming happens only on an actual collision -- otherwise the generated
    /// code stops looking like the source it came from, and the Task 7 cutover
    /// diff stops being reviewable.
    #[test]
    fn a_let_that_collides_with_nothing_keeps_its_source_name() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("a"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Let(
                String::from("scaled"),
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("scaled"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        assert!(
            matches!(&body.stmts[0], Stmt::Let { name, .. } if name == "scaled"),
            "got {:?}",
            body.stmts
        );
        assert_eq!(
            &body.stmts[1],
            &Stmt::Return(TExpr::Var(String::from("scaled")))
        );
    }

    /// A binder's own value is outside its scope: `let x := x + 1` reads the
    /// OUTER `x` on the right-hand side.
    #[test]
    fn a_binders_value_is_not_in_its_own_scope() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Let(
                String::from("x"),
                Box::new(Expr::Sub(
                    NumKind::Nat,
                    Box::new(Expr::Var(String::from("x"))),
                    Box::new(Expr::Nat(1)),
                )),
                Box::new(Expr::Var(String::from("x"))),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        match &body.stmts[0] {
            Stmt::Let { name, value, .. } => {
                assert_ne!(name, "x");
                // `Nat.sub` saturates, so this stays a plain BinOp.
                assert!(
                    matches!(value, TExpr::BinOp(_, BinOp::Sub, a, _) if **a == TExpr::Var(String::from("x"))),
                    "the value must read the PARAMETER x, got {:?}",
                    value
                );
            }
            other => panic!("expected the hoisted Let, got {:?}", other),
        }
    }

    /// The invariant this task exists for.
    ///
    /// `if c then (a + b) else 0`. Hoisting the `TryLet` for `a + b` to the
    /// top would evaluate it even when `c` is false -- turning a short-circuit
    /// into eager evaluation and producing an overflow error where Lean has
    /// none. Straight-line lowering cannot see this.
    #[test]
    fn a_fallible_op_in_one_arm_stays_in_that_arm() {
        // `if c then (a + b) else 0`, Nat, Rust profile.
        //
        // Hoisting the TryLet for `a + b` to the top would evaluate it even when
        // `c` is false -- turning a short-circuit into eager evaluation and
        // producing an overflow error where Lean has none.
        let def = Definition {
            name: String::from("f"),
            params: vec![
                (String::from("c"), Type::Bool),
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::If(
                Box::new(Expr::Var(String::from("c"))),
                Box::new(Expr::Add(
                    NumKind::Nat,
                    Box::new(Expr::Var(String::from("a"))),
                    Box::new(Expr::Var(String::from("b"))),
                )),
                Box::new(Expr::Nat(0)),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        // Nothing fallible before the branch.
        for s in &body.stmts {
            if matches!(s, Stmt::If { .. }) {
                break;
            }
            assert!(
                !matches!(s, Stmt::TryLet { .. }),
                "a TryLet was hoisted above the If: {:?}",
                body.stmts
            );
        }
        // And the TryLet is inside the then-branch, not the else.
        let Some(Stmt::If { then, else_, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::If { .. }))
        else {
            panic!("expected an If, got {:?}", body.stmts)
        };
        assert!(
            then.iter().any(|s| matches!(s, Stmt::TryLet { .. })),
            "then: {:?}",
            then
        );
        assert!(
            !else_.iter().any(|s| matches!(s, Stmt::TryLet { .. })),
            "else: {:?}",
            else_
        );
    }

    /// The same invariant, one level down: a `Match` arm is a control-flow
    /// boundary too, and the temporary for `a + b` belongs inside the arm that
    /// asked for it.
    #[test]
    fn a_fallible_op_in_one_match_arm_stays_in_that_arm() {
        // match o with | none => 0 | some _ => a + b
        let def = Definition {
            name: String::from("f"),
            params: vec![
                (String::from("o"), Type::Option(Box::new(Type::Nat))),
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::Match {
                scrut: Box::new(Expr::Var(String::from("o"))),
                alts: vec![
                    Alt {
                        ctor: String::from("Option.none"),
                        binders: vec![],
                        body: Expr::Nat(0),
                    },
                    Alt {
                        ctor: String::from("Option.some"),
                        binders: vec![String::from("v")],
                        body: Expr::Add(
                            NumKind::Nat,
                            Box::new(Expr::Var(String::from("a"))),
                            Box::new(Expr::Var(String::from("b"))),
                        ),
                    },
                ],
                default: None,
            },
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        for s in &body.stmts {
            assert!(
                !matches!(s, Stmt::TryLet { .. }),
                "a TryLet was hoisted above the Switch: {:?}",
                body.stmts
            );
        }
        let Some(Stmt::Switch { arms, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::Switch { .. }))
        else {
            panic!("expected a Switch, got {:?}", body.stmts)
        };
        assert!(
            !arms[0]
                .body
                .iter()
                .any(|s| matches!(s, Stmt::TryLet { .. })),
            "none arm: {:?}",
            arms[0].body
        );
        assert!(
            arms[1]
                .body
                .iter()
                .any(|s| matches!(s, Stmt::TryLet { .. })),
            "some arm: {:?}",
            arms[1].body
        );
    }

    /// A match binder is a source binder like any other, so it goes through
    /// `bind_source` and `scope`.
    ///
    /// Without that, the arm below would bind a second `x` while the
    /// parameter `x` is still live, and the printer's `uses()` -- which counts
    /// reads by NAME, with no scope of its own -- would pool their reads. That
    /// corrupts the decision to fold a single-use temporary, so a shadowing
    /// binder changes the SHAPE of the generated code, not only which value it
    /// reads.
    #[test]
    fn a_match_binder_shadowing_a_parameter_is_renamed() {
        // f(x, o) = match o with | none => x | some x => x
        let def = Definition {
            name: String::from("f"),
            params: vec![
                (String::from("x"), Type::Nat),
                (String::from("o"), Type::Option(Box::new(Type::Nat))),
            ],
            ret: Type::Nat,
            body: Expr::Match {
                scrut: Box::new(Expr::Var(String::from("o"))),
                alts: vec![
                    Alt {
                        ctor: String::from("Option.none"),
                        binders: vec![],
                        body: Expr::Var(String::from("x")),
                    },
                    Alt {
                        ctor: String::from("Option.some"),
                        binders: vec![String::from("x")],
                        body: Expr::Var(String::from("x")),
                    },
                ],
                default: None,
            },
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        let Some(Stmt::Switch { arms, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::Switch { .. }))
        else {
            panic!("expected a Switch, got {:?}", body.stmts)
        };
        // The `none` arm reads the PARAMETER.
        assert_eq!(
            arms[0].body,
            vec![Stmt::Return(TExpr::Var(String::from("x")))]
        );
        // The `some` arm binds its own, renamed, and reads that one.
        let bound = arms[1].binders[0].clone();
        assert_ne!(bound, "x", "the arm binder must be renamed off the param");
        assert_eq!(
            arms[1].body,
            vec![Stmt::Return(TExpr::Var(bound.clone()))],
            "the arm body must read its OWN binder, got {:?}",
            arms[1].body
        );
    }

    /// `Unreachable` is a terminator, not a value.
    #[test]
    fn a_dead_branch_lowers_to_a_fail() {
        let def = Definition {
            name: String::from("f"),
            params: vec![(String::from("c"), Type::Bool)],
            ret: Type::Nat,
            body: Expr::If(
                Box::new(Expr::Var(String::from("c"))),
                Box::new(Expr::Nat(1)),
                Box::new(Expr::Unreachable),
            ),
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        let Some(Stmt::If { then, else_, .. }) =
            body.stmts.iter().find(|s| matches!(s, Stmt::If { .. }))
        else {
            panic!("expected an If, got {:?}", body.stmts)
        };
        assert_eq!(then, &vec![Stmt::Return(TExpr::Lit(Lit::Nat(1)))]);
        assert_eq!(else_, &vec![Stmt::Fail(ErrorCode::Unreachable)]);
    }

    /// `let g := jp g (p) <body>; jmp g arg`, the one join-point form the
    /// corpus contains and the only one this lowering inlines.
    fn def_jp(jp_param: &str, jumps: usize, body: Expr) -> Definition {
        let mut jump: Expr = Expr::Jmp(String::from("g"), vec![Expr::Nat(5)]);
        for _ in 1..jumps {
            jump = Expr::Add(
                NumKind::Nat,
                Box::new(jump),
                Box::new(Expr::Jmp(String::from("g"), vec![Expr::Nat(6)])),
            );
        }
        Definition {
            name: String::from("f"),
            params: vec![(String::from("x"), Type::Nat)],
            ret: Type::Nat,
            body: Expr::Let(
                String::from("g"),
                Box::new(Expr::Jp {
                    name: String::from("g"),
                    params: vec![String::from(jp_param)],
                    body: Box::new(body),
                }),
                Box::new(jump),
            ),
        }
    }

    /// The single-caller, non-cyclic join point is inlined at its jump site,
    /// and its parameter goes through `bind_source`/`scope` -- so a parameter
    /// name that collides with a definition parameter is renamed, exactly as a
    /// `let` binder would be.
    #[test]
    fn a_single_caller_join_point_inlines_and_its_parameter_is_renamed() {
        // f(x) = let g := jp g (x) (x + 1); jmp g 5
        let def = def_jp(
            "x",
            1,
            Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("x"))),
                Box::new(Expr::Nat(1)),
            ),
        );
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        // The declaration binds nothing: the body moved to the jump site.
        let lets: Vec<&Stmt> = body
            .stmts
            .iter()
            .filter(|s| matches!(s, Stmt::Let { .. }))
            .collect();
        assert_eq!(lets.len(), 1, "got {:?}", body.stmts);
        let Stmt::Let { name, value, .. } = lets[0] else {
            unreachable!()
        };
        assert_ne!(name, "x", "the jp parameter must be renamed off the param");
        assert_eq!(
            value,
            &TExpr::Lit(Lit::Nat(5)),
            "bound to the jump's argument"
        );

        match &body.stmts[1] {
            Stmt::TryLet {
                op: FallibleOp::Arith(_, BinOp::Add, a, _),
                ..
            } => assert_eq!(
                a,
                &TExpr::Var(name.clone()),
                "the jp body must read its OWN parameter, got {:?}",
                a
            ),
            other => panic!("expected the inlined add, got {:?}", other),
        }
    }

    /// A join point with no jump sites is just its body, in place.
    #[test]
    fn a_join_point_nobody_jumps_to_is_its_body() {
        let mut def = def_jp("p", 1, Expr::Nat(7));
        // Replace the jump with a plain value: now `g` has no callers.
        def.body = match def.body {
            Expr::Let(name, value, _) => Expr::Let(name, value, Box::new(Expr::Nat(9))),
            other => other,
        };
        let defs = vec![def];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
        assert_eq!(
            body.stmts,
            vec![
                Stmt::Let {
                    name: String::from("g"),
                    ty: Type::Nat,
                    value: TExpr::Lit(Lit::Nat(7)),
                },
                Stmt::Return(TExpr::Lit(Lit::Nat(9))),
            ],
            "got {:?}",
            body.stmts
        );
    }

    /// Everything that is not the single-caller, non-cyclic form is rejected,
    /// exactly as `prod-codegen` rejects it today. Widening join-point support
    /// is not part of this plan, and emitting a plausible-looking skeleton for
    /// it is how this project previously shipped Rust that did not compile.
    #[test]
    fn a_multi_caller_or_cyclic_join_point_is_rejected() {
        let two_callers = def_jp("p", 2, Expr::Var(String::from("p")));
        let cyclic = def_jp(
            "p",
            1,
            Expr::Jmp(String::from("g"), vec![Expr::Var(String::from("p"))]),
        );
        for def in [two_callers, cyclic] {
            let defs = vec![def];
            let shapes = signatures(&defs, &TargetProfile::RUST);
            assert_eq!(
                lower_def(&defs[0], &shapes, &TargetProfile::RUST),
                Err(LowerError::UnsupportedJoinPoint(String::from("g"))),
            );
        }
    }
}
