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
use crate::target::{BinOp, Body, FallibleOp, Lit, Stmt, TExpr};
use alloc::boxed::Box;
use alloc::collections::BTreeSet;
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
        taken: bound_names(def),
        env: Vec::new(),
    };
    let mut stmts: Vec<Stmt> = Vec::new();
    let result = lowering.expr(&def.body, &mut stmts)?;
    stmts.push(Stmt::Return(result));
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

struct Lowering<'a> {
    params: &'a [(String, Type)],
    shapes: &'a Signatures<'a>,
    profile: &'a TargetProfile,
    next_temp: usize,
    /// Every name the source definition itself binds. A generated temporary
    /// must not collide with one: the printer may inline a temporary into its
    /// single use, and a user binding of the same name in between would
    /// shadow it and silently change which value is read.
    taken: BTreeSet<String>,
    /// Binder name -> type, innermost last. Only used to type later binders;
    /// see [`Lowering::type_of`].
    env: Vec<(String, Type)>,
}

impl<'a> Lowering<'a> {
    fn fresh(&mut self) -> String {
        loop {
            let name = format!("t{}", self.next_temp);
            self.next_temp += 1;
            if !self.taken.contains(&name) {
                return name;
            }
        }
    }

    fn expr(&mut self, e: &Expr, stmts: &mut Vec<Stmt>) -> Result<TExpr, LowerError> {
        match e {
            Expr::Nat(n) => Ok(TExpr::Lit(Lit::Nat(*n))),
            Expr::Int(n) => Ok(TExpr::Lit(Lit::Int(*n))),
            Expr::Bool(b) => Ok(TExpr::Lit(Lit::Bool(*b))),
            Expr::Var(name) => Ok(TExpr::Var(name.clone())),
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

            Expr::Let(name, value, body) => {
                let value = self.expr(value, stmts)?;
                let ty = self.type_of(&value);
                stmts.push(Stmt::Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    value,
                });
                self.env.push((name.clone(), ty));
                let out = self.expr(body, stmts);
                self.env.pop();
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
        self.env.push((name.clone(), ty));
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
                .env
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
    use prod_ir::{Definition, Expr, NumKind, Type};

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
}
