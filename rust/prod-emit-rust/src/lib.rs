//! The Rust printer for [`prod_lower::target`].
//!
//! Everything here is a *spelling* decision — which Rust method, which cast,
//! where the `?` goes. Every *semantic* decision was already made by
//! [`prod_lower::lower`] and is readable off the [`Body`]: whether an
//! operation can fail (it is a [`Stmt::TryLet`] if so), and whether the host's
//! own division computes Lean's answer (it is [`BinOp::DivE`]/[`BinOp::ModE`]
//! if not). That division of labour is why this function returns a `String`
//! rather than a `Result`: there is nothing left here to refuse.
//!
//! This is the strangler-stage printer. `prod-codegen`'s `Renderer` still
//! produces every byte of real output; nothing outside this crate's own tests
//! calls [`emit_body`] until the Task 7 cutover.

#![no_std]

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use prod_ir::{NumKind, Type};
use prod_lower::names::NamePolicy;
use prod_lower::shape::Shape;
use prod_lower::target::{Arm, BinOp, Body, ErrorCode, FallibleOp, Lit, Stmt, TExpr};

/// The Rust type a numeric kind renders as. Also the cast used to pin an
/// arithmetic receiver's type — LCNF emits let-bound integer literals whose
/// type is ambiguous, and a method call on `{integer}` fails resolution
/// (E0689).
///
/// Lived on `NumKind` in `prod-ir` until the backends were split out; the IR
/// had no business knowing Rust's type names.
pub const fn rust_type(kind: NumKind) -> &'static str {
    match kind {
        NumKind::Nat => "u64",
        NumKind::Int => "i64",
        NumKind::U8 => "u8",
        NumKind::U16 => "u16",
        NumKind::U32 => "u32",
        NumKind::U64 => "u64",
    }
}

/// Render one lowered definition as Rust source.
pub fn emit_body(body: &Body) -> String {
    let mut params = String::new();
    for (i, (name, ty)) in body.params.iter().enumerate() {
        if i > 0 {
            params.push_str(", ");
        }
        params.push_str(&format!("{}: {}", name, param_type(ty)));
    }

    let fallible = body.shape == Shape::Fallible;
    let ret = match body.shape {
        Shape::Fallible => format!("Result<{}, crate::ComputeError>", value_type(&body.ret)),
        _ => value_type(&body.ret),
    };

    let mut printer = Printer {
        fallible,
        inline: BTreeMap::new(),
        uses: uses(&body.stmts),
    };
    let stmts = printer.block(&body.stmts, 1);

    format!(
        "pub fn {}({}) -> {} {{\n{}}}\n",
        body.name, params, ret, stmts
    )
}

struct Printer {
    fallible: bool,
    /// Temporaries that were folded back into their single use, and the text
    /// they render as.
    inline: BTreeMap<String, String>,
    /// How often each bound name is read, at every nesting level.
    uses: BTreeMap<String, Usage>,
}

#[derive(Default, Clone, Copy)]
struct Usage {
    /// Reads anywhere in the body.
    total: usize,
    /// Reads in the statement list the binder itself sits in.
    same_level: usize,
}

impl Printer {
    fn block(&mut self, stmts: &[Stmt], depth: usize) -> String {
        let pad = "    ".repeat(depth);
        let mut out = String::new();
        for (i, stmt) in stmts.iter().enumerate() {
            let last = i + 1 == stmts.len();
            match stmt {
                Stmt::Let { name, value, .. } => {
                    let value = self.expr(value);
                    out.push_str(&format!("{}let {} = {};\n", pad, ident(name), value));
                }
                Stmt::TryLet { name, op, .. } => {
                    let text = self.fallible_op(op);
                    // Rust propagates failure inside an expression, so a
                    // temporary read exactly once — and read in this same
                    // statement list, not inside a branch that might not run —
                    // folds back into its use. The lowering pushes `TryLet`s
                    // in evaluation order and the uses appear in that same
                    // order, so folding cannot reorder which failure is
                    // reported first.
                    let usage = self.uses.get(name).copied().unwrap_or_default();
                    if usage.total == 1 && usage.same_level == 1 {
                        self.inline.insert(name.clone(), text);
                    } else {
                        out.push_str(&format!("{}let {} = {};\n", pad, ident(name), text));
                    }
                }
                Stmt::Return(e) => {
                    let e = self.expr(e);
                    let e = if self.fallible {
                        format!("Ok({})", e)
                    } else {
                        e
                    };
                    if last && depth == 1 {
                        out.push_str(&format!("{}{}\n", pad, e));
                    } else {
                        out.push_str(&format!("{}return {};\n", pad, e));
                    }
                }
                // Each branch is its own statement list, so it prints as its
                // own BLOCK. That is what keeps a branch's `TryLet` -- and the
                // `?` it carries -- from running when the branch does not.
                //
                // Both arms end in a terminator, so the `if` has type `!` and
                // coerces wherever the body needs a value.
                Stmt::If { cond, then, else_ } => {
                    let cond = self.expr(cond);
                    let then = self.block(then, depth + 1);
                    let else_ = self.block(else_, depth + 1);
                    out.push_str(&format!(
                        "{}if {} {{\n{}{}}} else {{\n{}{}}}\n",
                        pad, cond, then, pad, else_, pad
                    ));
                }
                Stmt::Switch {
                    scrut,
                    arms,
                    default,
                } => out.push_str(&self.switch(scrut, arms, default.as_deref(), depth)),
                Stmt::Fail(code) => out.push_str(&format!("{}{}\n", pad, fail(*code))),
                // Lists are Task 6; the lowering in this task emits no
                // `Push`. A `compile_error!` rather than a plausible guess,
                // so a premature use fails at the Rust compiler instead of
                // shipping.
                other => out.push_str(&format!("{}{}\n", pad, todo_stmt(other))),
            }
        }
        out
    }

    /// A `Switch` prints as a Rust `match`, one block per arm.
    ///
    /// The constructor spellings that need no type table are the ones this
    /// slice can render: the `Nat` structural-recursion pair LCNF emits, and
    /// `Bool`/`Option`/`List`, whose Rust patterns are fixed. A user-declared
    /// constructor needs the module's type table to know its path and its
    /// field names, which arrives in Task 5; until then it renders
    /// positionally, exactly as `prod-codegen` does for a constructor it
    /// cannot resolve.
    fn switch(
        &mut self,
        scrut: &TExpr,
        arms: &[Arm],
        default: Option<&[Stmt]>,
        depth: usize,
    ) -> String {
        let pad = "    ".repeat(depth);
        let inner = "    ".repeat(depth + 1);
        let scrut = self.expr(scrut);
        let mut out = format!("{}match {} {{\n", pad, scrut);
        for arm in arms {
            let (pattern, prologue) = arm_pattern(&arm.ctor, &arm.binders, &scrut);
            out.push_str(&format!("{}{} => {{\n", inner, pattern));
            for line in &prologue {
                out.push_str(&format!("{}    {}\n", inner, line));
            }
            out.push_str(&self.block(&arm.body, depth + 2));
            out.push_str(&format!("{}}}\n", inner));
        }
        if let Some(d) = default {
            out.push_str(&format!("{}_ => {{\n", inner));
            out.push_str(&self.block(d, depth + 2));
            out.push_str(&format!("{}}}\n", inner));
        }
        out.push_str(&format!("{}}}\n", pad));
        out
    }

    fn expr(&self, e: &TExpr) -> String {
        match e {
            TExpr::Lit(Lit::Nat(n)) => format!("{}", n),
            TExpr::Lit(Lit::Int(n)) => format!("{}", n),
            TExpr::Lit(Lit::Bool(b)) => format!("{}", b),
            TExpr::Var(name) => match self.inline.get(name) {
                Some(text) => text.clone(),
                None => ident(name),
            },
            TExpr::BinOp(kind, op, a, b) => self.binop(*kind, *op, a, b),
            TExpr::Call(name, args) => format!("{}({})", name, self.args(args)),
            TExpr::Not(a) => format!("(!{})", self.expr(a)),
            TExpr::And(a, b) => format!("({} && {})", self.expr(a), self.expr(b)),
            TExpr::Or(a, b) => format!("({} || {})", self.expr(a), self.expr(b)),
            // Constructors and projections need the module's type table, which
            // arrives in Task 5.
            TExpr::Ctor(..) | TExpr::Proj(..) => unsupported("Ctor/Proj rendering is Task 5"),
        }
    }

    fn args(&self, args: &[TExpr]) -> String {
        args.iter()
            .map(|a| self.expr(a))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// The infallible renderings. Each one is a Lean fact, not a style choice;
    /// the doc comments say which.
    fn binop(&self, kind: NumKind, op: BinOp, a: &TExpr, b: &TExpr) -> String {
        let (a, b) = (self.expr(a), self.expr(b));
        let ty = rust_type(kind);
        let sized = !matches!(kind, NumKind::Nat | NumKind::Int);
        match (op, kind) {
            // Sized-integer arithmetic wraps — that is Lean's semantics
            // (`UInt8.add a b = ⟨a.toBitVec + b.toBitVec⟩`), not a failure.
            (BinOp::Add, _) if sized => wrapping(&a, ty, "wrapping_add", &b),
            (BinOp::Sub, _) if sized => wrapping(&a, ty, "wrapping_sub", &b),
            (BinOp::Mul, _) if sized => wrapping(&a, ty, "wrapping_mul", &b),
            // `Nat.sub` saturates in Lean (`2 - 5 = 0`); it cannot fail.
            (BinOp::Sub, NumKind::Nat) => format!("(({}) as u64).saturating_sub({})", a, b),

            // Lean's division is total where the host's is not, so both
            // operators carry a divisor-is-zero case — and NOT the same one:
            // `x / 0 = 0`, but `x % 0 = x`, the dividend. See `BinOp::Mod`.
            (BinOp::Div, _) => guarded_division(&b, "0", &format!("({}) / ({})", a, b)),
            (BinOp::Mod, _) => guarded_division(&b, &a, &format!("({}) % ({})", a, b)),

            // Sized shifts MASK the amount mod the width; they do not truncate
            // to 0 past it. `UInt8.shiftLeft a b = ⟨a.toBitVec <<< (b % 8)⟩`
            // (`Init/Data/UInt/Basic.lean:126`), so `(1 : UInt8) <<< 8 = 1`,
            // not `0` — which is exactly `wrapping_shl`. This shipped
            // backwards once and stayed green in CI.
            (BinOp::Shl, _) if sized => shift(&a, ty, "wrapping_shl", &b),
            (BinOp::Shr, _) if sized => shift(&a, ty, "wrapping_shr", &b),
            // `Nat.shiftRight` truncates: `Nat` is unbounded, so `a >>> b = 0`
            // for any `b >= 64` once `a` fits `u64`. There is no width to mask
            // by, only a genuine "shifted past everything" case, and
            // `checked_shr(..).unwrap_or(0)` is the exact answer — total and
            // infallible, with no `ComputeError` variant because none is
            // needed.
            (BinOp::Shr, NumKind::Nat) => format!(
                "(({}) as u64).checked_shr(u32::try_from({}).unwrap_or(u32::MAX)).unwrap_or(0)",
                a, b
            ),

            (BinOp::Eq, _) => format!("({} == {})", a, b),
            (BinOp::Lt, _) => format!("({} < {})", a, b),
            (BinOp::Le, _) => format!("({} <= {})", a, b),
            (BinOp::Gt, _) => format!("({} > {})", a, b),
            (BinOp::BitAnd, _) => format!("({} & {})", a, b),

            // What remains is unbounded-kind arithmetic that some profile
            // declared total. Rust has no unbounded integer, so no body
            // lowered under `TargetProfile::RUST` can reach here, and there is
            // no faithful rendering to offer if one does.
            _ => unsupported("no total Rust rendering for this operator and kind"),
        }
    }

    /// The fallible renderings. Every one of these ends in a `?`, which is why
    /// they may appear only where a [`Stmt::TryLet`] put them.
    fn fallible_op(&self, op: &FallibleOp) -> String {
        match op {
            FallibleOp::Arith(kind, op, a, b) => {
                let (a, b) = (self.expr(a), self.expr(b));
                let ty = rust_type(*kind);
                match op {
                    BinOp::Add => checked(&a, ty, "checked_add", &b, "AddOverflow"),
                    BinOp::Sub => checked(&a, ty, "checked_sub", &b, "SubOverflow"),
                    BinOp::Mul => checked(&a, ty, "checked_mul", &b, "MulOverflow"),
                    // The exponent must also narrow to `u32`, a second and
                    // distinct failure mode.
                    BinOp::Pow => exponent(
                        &a,
                        ty,
                        "checked_pow",
                        &b,
                        "PowExponentTooLarge",
                        "PowOverflow",
                    ),
                    BinOp::Shl => exponent(
                        &a,
                        ty,
                        "checked_shl",
                        &b,
                        "ShiftExponentTooLarge",
                        "ShiftOverflow",
                    ),
                    // Euclidean, because Lean's `Int` division is
                    // `Int.ediv`/`Int.emod` and Rust's `/`/`%` truncate:
                    // `(-12) / 7 = -2` and `(-12) % 7 = 2`, against Rust's
                    // `-1` and `-5`. Checked, because `i64::MIN / -1`
                    // overflows — and `checked_rem_euclid` fails exactly where
                    // `checked_div_euclid` does, the Euclidean remainder being
                    // defined in terms of the division, so both report
                    // `DivOverflow`.
                    BinOp::DivE => guarded_division(
                        &b,
                        "0",
                        &checked(&a, ty, "checked_div_euclid", &b, "DivOverflow"),
                    ),
                    BinOp::ModE => guarded_division(
                        &b,
                        &a,
                        &checked(&a, ty, "checked_rem_euclid", &b, "DivOverflow"),
                    ),
                    // A host whose own division is already Euclidean. Not
                    // Rust's — reachable only if a profile says so.
                    BinOp::Div => guarded_division(
                        &b,
                        "0",
                        &checked(&a, ty, "checked_div", &b, "DivOverflow"),
                    ),
                    BinOp::Mod => {
                        guarded_division(&b, &a, &checked(&a, ty, "checked_rem", &b, "DivOverflow"))
                    }
                    BinOp::Shr | BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::BitAnd => {
                        unsupported("this operator has no fallible Rust rendering")
                    }
                }
            }
            FallibleOp::Neg(kind, a) => format!(
                "(({}) as {}).checked_neg().ok_or(crate::ComputeError::NegOverflow)?",
                self.expr(a),
                rust_type(*kind)
            ),
            FallibleOp::Call(name, args) => format!("{}({})?", name, self.args(args)),
        }
    }
}

/// `checked_add`/`checked_mul`: report overflow instead of panicking.
///
/// The `as` cast pins the receiver's type: method calls on an inferred
/// `{integer}` (a let-bound literal, e.g. LCNF's `let _x := 1`) fail method
/// resolution (E0689). It is a no-op when the receiver already has the kind's
/// type.
fn checked(a: &str, ty: &str, method: &str, b: &str, error: &str) -> String {
    format!(
        "(({}) as {}).{}({}).ok_or(crate::ComputeError::{})?",
        a, ty, method, b, error
    )
}

fn exponent(
    a: &str,
    ty: &str,
    method: &str,
    b: &str,
    exponent_error: &str,
    overflow_error: &str,
) -> String {
    format!(
        "(({}) as {}).{}(u32::try_from({}).map_err(|_| crate::ComputeError::{})?).ok_or(crate::ComputeError::{})?",
        a, ty, method, b, exponent_error, overflow_error
    )
}

fn wrapping(a: &str, ty: &str, method: &str, b: &str) -> String {
    format!("(({}) as {}).{}({})", a, ty, method, b)
}

/// The amount narrows to `u32` with a plain `as`, not the saturating
/// `try_from(..).unwrap_or(..)` the checked helpers use: `wrapping_shl` never
/// aborts, and truncating a `u64` amount to `u32` cannot disturb the low 6
/// bits that the mod-64 mask actually reads.
fn shift(a: &str, ty: &str, method: &str, b: &str) -> String {
    format!("(({}) as {}).{}(({}) as u32)", a, ty, method, b)
}

fn guarded_division(b: &str, zero: &str, nonzero: &str) -> String {
    format!("if ({}) == 0 {{ {} }} else {{ {} }}", b, zero, nonzero)
}

fn ident(name: &str) -> String {
    NamePolicy::RUST.apply(name)
}

/// A rendering this slice does not provide, spelled so the Rust compiler
/// refuses it. Generated code that is merely plausible is worse than
/// generated code that does not build.
fn unsupported(why: &str) -> String {
    format!("compile_error!(\"prod-emit-rust: {}\")", why)
}

fn todo_stmt(stmt: &Stmt) -> String {
    let what = match stmt {
        Stmt::Push { .. } => "Push (Task 6)",
        Stmt::Let { .. }
        | Stmt::TryLet { .. }
        | Stmt::Return(_)
        | Stmt::If { .. }
        | Stmt::Switch { .. }
        | Stmt::Fail(_) => unreachable!(),
    };
    format!(
        "compile_error!(\"prod-emit-rust: {} is not lowered yet\");",
        what
    )
}

/// The Rust pattern for one arm, plus any bindings that have to happen inside
/// the arm rather than in the pattern.
///
/// The `Nat` pair is LCNF's structural recursion: `Nat.zero` is the literal
/// `0` and `Nat.succ k` is the `_` arm with `k` bound to the predecessor.
/// Since the zero arm matches first the scrutinee is at least 1 there, so
/// `saturating_sub(1)` is exact -- and stays inside the crate's bounded-`Nat`
/// policy. Match ergonomics bind a slice's head by reference, so the cons arm
/// rebinds it by value and arithmetic on it needs no dereference syntax.
fn arm_pattern(ctor: &str, binders: &[String], scrut: &str) -> (String, Vec<String>) {
    let bound = |i: usize| ident(&binders[i]);
    match (ctor, binders.len()) {
        ("Nat.zero", 0) => (String::from("0"), Vec::new()),
        ("Nat.succ", 1) => (
            String::from("_"),
            alloc::vec![format!("let {} = ({}).saturating_sub(1);", bound(0), scrut)],
        ),
        ("Bool.true", 0) => (String::from("true"), Vec::new()),
        ("Bool.false", 0) => (String::from("false"), Vec::new()),
        ("Option.none", 0) => (String::from("None"), Vec::new()),
        ("Option.some", 1) => (format!("Some({})", bound(0)), Vec::new()),
        ("List.nil", 0) => (String::from("[]"), Vec::new()),
        ("List.cons", 2) => (
            format!("[{}, {} @ ..]", bound(0), bound(1)),
            alloc::vec![format!("let {} = *{};", bound(0), bound(0))],
        ),
        (_, 0) => (String::from(ctor), Vec::new()),
        _ => (
            format!(
                "{}({})",
                ctor,
                binders
                    .iter()
                    .map(|b| ident(b))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Vec::new(),
        ),
    }
}

/// A `Fail` is a terminator, so it prints as one.
///
/// `Unreachable` keeps `prod-codegen`'s `unreachable!()`: LCNF emits it only
/// for a branch Lean itself proved dead, so it is not reachable on
/// caller-controlled input, and there is no `ComputeError` variant for "the
/// impossible happened" to report instead.
fn fail(code: ErrorCode) -> String {
    match code {
        ErrorCode::Unreachable => String::from("unreachable!();"),
        ErrorCode::OutputTooSmall => {
            String::from("return Err(crate::ComputeError::OutputTooSmall);")
        }
    }
}

/// Rust spelling of a type in an ordinary (owned, by-value) position.
fn value_type(ty: &Type) -> String {
    match ty {
        Type::Nat => "u64".to_string(),
        Type::Int => "i64".to_string(),
        Type::Bool => "bool".to_string(),
        Type::UInt(k) => rust_type(*k).to_string(),
        Type::Named(n) => format!("crate::{}", ident(n)),
        Type::Option(inner) => format!("Option<{}>", value_type(inner)),
        Type::Tuple(items) => format!(
            "({})",
            items.iter().map(value_type).collect::<Vec<_>>().join(", ")
        ),
        // Lists are a caller buffer or a promoted static slice, neither of
        // which this slice lowers; `Vec` and `Opaque` are rejected outright.
        Type::List(_) | Type::Vec(_) | Type::Opaque(_) => {
            "prod_emit_rust_unsupported_type".to_string()
        }
    }
}

/// Rust spelling of a parameter type: a top-level list borrows as a slice.
fn param_type(ty: &Type) -> String {
    match ty {
        Type::List(inner) => format!("&[{}]", value_type(inner)),
        _ => value_type(ty),
    }
}

/// Count every read of every bound name, at the binder's own level and below.
///
/// By NAME, with no scope of its own: it relies on `prod_lower::lower` having
/// made every binder in the body unique. Two live bindings sharing a name
/// would pool their reads here, and a temporary that is read once would look
/// read twice (or worse, vice versa) -- so the fold-into-single-use decision
/// depends on that invariant, not only the flat statement list does.
fn uses(stmts: &[Stmt]) -> BTreeMap<String, Usage> {
    let mut out: BTreeMap<String, Usage> = BTreeMap::new();
    count_level(stmts, &mut out, true);
    out
}

fn count_level(stmts: &[Stmt], out: &mut BTreeMap<String, Usage>, same_level: bool) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value, .. } | Stmt::Return(value) | Stmt::Push { value, .. } => {
                count_expr(value, out, same_level)
            }
            Stmt::TryLet { op, .. } => match op {
                FallibleOp::Arith(_, _, a, b) => {
                    count_expr(a, out, same_level);
                    count_expr(b, out, same_level);
                }
                FallibleOp::Neg(_, a) => count_expr(a, out, same_level),
                FallibleOp::Call(_, args) => {
                    for a in args {
                        count_expr(a, out, same_level);
                    }
                }
            },
            Stmt::If { cond, then, else_ } => {
                count_expr(cond, out, same_level);
                count_level(then, out, false);
                count_level(else_, out, false);
            }
            Stmt::Switch {
                scrut,
                arms,
                default,
            } => {
                count_expr(scrut, out, same_level);
                for arm in arms {
                    count_level(&arm.body, out, false);
                }
                if let Some(d) = default {
                    count_level(d, out, false);
                }
            }
            Stmt::Fail(_) => {}
        }
    }
}

fn count_expr(e: &TExpr, out: &mut BTreeMap<String, Usage>, same_level: bool) {
    match e {
        TExpr::Var(name) => {
            let entry = out.entry(name.clone()).or_default();
            entry.total += 1;
            if same_level {
                entry.same_level += 1;
            }
        }
        TExpr::Lit(_) => {}
        TExpr::BinOp(_, _, a, b) | TExpr::And(a, b) | TExpr::Or(a, b) => {
            count_expr(a, out, same_level);
            count_expr(b, out, same_level);
        }
        TExpr::Not(a) | TExpr::Proj(_, _, a) => count_expr(a, out, same_level),
        TExpr::Ctor(_, _, args) | TExpr::Call(_, args) => {
            for a in args {
                count_expr(a, out, same_level);
            }
        }
    }
}

#[cfg(test)]
mod tests;
