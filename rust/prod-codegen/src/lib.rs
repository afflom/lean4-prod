//! prod-codegen: renders `prod-ir` modules as Rust source text.
//!
//! This crate is `#![no_std]` (with `alloc`) and host-independent: it renders
//! Rust code as a plain `String`, never as `proc_macro2::TokenStream`, so it
//! can run on wasm32 or inside other hosts. `prod-macros` and `prod-cli` are
//! thin drivers on top of [`generate_module`].
//!
//! # Code generation policy
//!
//! - **Nat policy**: Lean `Nat` maps to `u64` and Lean `Int` to `i64`.
//!   Arithmetic (`add`/`sub`/`mul`/`div`/`mod`/`shl`) maps directly to the
//!   corresponding `u64` operators, e.g. `(shl 1 (sub o 1))` → `(1 << (o - 1))`.
//!   No overflow checks or bignum fallback — the caller owns that risk.
//! - **Instance**: the IR `Instance` type maps to `crate::Instance` (by value;
//!   it is a small `Copy` struct in `prod-core`).
//! - **Field access**: `(field e "name")` renders as `e.name`, except for the
//!   legacy method-field table below, which renders as method calls. This
//!   table is carried over as-is from `uor-atlas-macros`:
//!
//!   | IR field      | Rust rendering    |
//!   |---------------|-------------------|
//!   | `stride`      | `e.stride()`      |
//!   | `class_count` | `e.class_count()` |
//!   | `belt`        | `e.belt()`        |
//!   | anything else | `e.<name>`        |
//!
//! - **LCNF nodes**:
//!   - `Match` renders as a Rust `match`, with `default` becoming the `_` arm.
//!   - `Ctor` renders as tuple-style construction `Name(args...)` (bare `Name`
//!     when there are no args).
//!   - `Proj` renders as tuple-style field access `(e).<idx>`. A named-field
//!     map (Lean structure field names) is future work; the type name is
//!     currently emitted only in generated comments where useful.
//!   - `Unreachable` renders as `unreachable!()`.
//!   - **Jp/Jmp policy**: a join point with exactly one `jmp` caller that is
//!     not inside its own body is inlined at the jump site as
//!     `{ let p = arg; ...; <jp body> }`, and the declaration site renders as
//!     `()`. A join point with no callers renders its body in place. Anything
//!     else (cyclic or multi-caller join points) renders as a `loop {}`
//!     skeleton with a `manual port required` comment — deliberately not
//!     over-engineered.

#![no_std]

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use prod_ir::{Definition, Expr, Module, Type};

/// Fields rendered as method calls rather than plain field accesses.
/// Legacy table carried over unchanged from `uor-atlas-macros`.
const METHOD_FIELDS: &[&str] = &["stride", "class_count", "belt"];

/// Errors that can occur during code generation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Code generation is not possible for an opaque expression
    OpaqueExpr(String),
    /// `(param n)` refers to a parameter index outside the definition's list
    ParamOutOfBounds(usize),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::OpaqueExpr(s) => write!(f, "cannot generate code for opaque expression: {}", s),
            Error::ParamOutOfBounds(i) => write!(f, "parameter index {} is out of bounds", i),
        }
    }
}

/// Render a whole module: one `pub fn` per definition.
pub fn generate_module(module: &Module) -> Result<String, Error> {
    let mut out = String::new();
    for def in &module.definitions {
        out.push_str(&generate_def(def)?);
        out.push('\n');
    }
    Ok(out)
}

/// Render a single definition as a `pub fn`.
pub fn generate_def(def: &Definition) -> Result<String, Error> {
    let ctx = JpContext::collect(&def.body);

    let mut params = String::new();
    for (i, (name, ty)) in def.params.iter().enumerate() {
        if i > 0 {
            params.push_str(", ");
        }
        params.push_str(&format!("{}: {}", name, type_to_rust(ty)));
    }

    let body = expr_to_rust(&def.body, &def.params, &ctx)?;

    Ok(format!(
        "pub fn {}({}) -> {} {{\n    {}\n}}\n",
        def.name,
        params,
        type_to_rust(&def.ret),
        body
    ))
}

fn type_to_rust(ty: &Type) -> String {
    match ty {
        Type::Nat => String::from("u64"),
        Type::Int => String::from("i64"),
        Type::Bool => String::from("bool"),
        Type::Instance => String::from("crate::Instance"),
        Type::Option(inner) => format!("Option<{}>", type_to_rust(inner)),
        Type::Vec(inner) => format!("Vec<{}>", type_to_rust(inner)),
        Type::Tuple(items) => {
            let types: Vec<String> = items.iter().map(type_to_rust).collect();
            format!("({})", types.join(", "))
        }
        Type::Opaque(s) => s.clone(),
    }
}

/// Join-point analysis for one definition body (two-pass jp/jmp lowering).
struct JpContext<'a> {
    /// name → (params, body) of each `jp` declaration in the body
    decls: BTreeMap<&'a str, (&'a [String], &'a Expr)>,
    /// name → total number of `jmp` sites in the body
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
        // Record decls and counts, then recurse into every subexpression.
        match expr {
            Expr::Jp { name, params, body } => {
                self.decls.insert(name.as_str(), (params, body));
            }
            Expr::Jmp(name, _) => {
                *self.jmp_counts.entry(name.as_str()).or_insert(0) += 1;
            }
            _ => {}
        }
        for child in children(expr) {
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
    self_count + children(expr).map(|c| count_jmps(c, name)).sum::<usize>()
}

/// Iterate over the direct subexpressions of an expression node.
fn children(expr: &Expr) -> impl Iterator<Item = &Expr> {
    let mut out: Vec<&Expr> = Vec::new();
    match expr {
        Expr::Field(e, _) | Expr::Proj(_, _, e) => out.push(e),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Mod(a, b)
        | Expr::Shl(a, b)
        | Expr::Eq(a, b)
        | Expr::Lt(a, b)
        | Expr::Gt(a, b) => {
            out.push(a);
            out.push(b);
        }
        Expr::If(c, t, f) => {
            out.push(c);
            out.push(t);
            out.push(f);
        }
        Expr::Let(_, v, b) => {
            out.push(v);
            out.push(b);
        }
        Expr::Call(_, args) | Expr::Ctor(_, args) | Expr::Jmp(_, args) => {
            out.extend(args.iter());
        }
        Expr::Match {
            scrut,
            alts,
            default,
        } => {
            out.push(scrut);
            out.extend(alts.iter().map(|a| &a.body));
            if let Some(d) = default {
                out.push(d);
            }
        }
        Expr::Jp { body, .. } => out.push(body),
        _ => {}
    }
    out.into_iter()
}

fn expr_to_rust(
    expr: &Expr,
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<String, Error> {
    match expr {
        Expr::Nat(n) => Ok(format!("{}", n)),
        Expr::Int(n) => Ok(format!("{}", n)),
        Expr::Bool(b) => Ok(format!("{}", b)),
        Expr::Var(name) => Ok(name.clone()),
        Expr::Param(index) => params
            .get(*index)
            .map(|(name, _)| name.clone())
            .ok_or(Error::ParamOutOfBounds(*index)),
        Expr::Field(obj, field) => {
            let obj = expr_to_rust(obj, params, ctx)?;
            if METHOD_FIELDS.contains(&field.as_str()) {
                Ok(format!("{}.{}()", obj, field))
            } else {
                Ok(format!("{}.{}", obj, field))
            }
        }
        Expr::Add(a, b) => binop(a, b, "+", params, ctx),
        Expr::Sub(a, b) => binop(a, b, "-", params, ctx),
        Expr::Mul(a, b) => binop(a, b, "*", params, ctx),
        Expr::Div(a, b) => binop(a, b, "/", params, ctx),
        Expr::Mod(a, b) => binop(a, b, "%", params, ctx),
        Expr::Shl(a, b) => binop(a, b, "<<", params, ctx),
        Expr::Eq(a, b) => binop(a, b, "==", params, ctx),
        Expr::Lt(a, b) => binop(a, b, "<", params, ctx),
        Expr::Gt(a, b) => binop(a, b, ">", params, ctx),
        Expr::If(cond, t, f) => {
            let cond = expr_to_rust(cond, params, ctx)?;
            let t = expr_to_rust(t, params, ctx)?;
            let f = expr_to_rust(f, params, ctx)?;
            Ok(format!("if {} {{ {} }} else {{ {} }}", cond, t, f))
        }
        Expr::Let(name, val, body) => {
            let val = expr_to_rust(val, params, ctx)?;
            let body = expr_to_rust(body, params, ctx)?;
            Ok(format!("{{ let {} = {}; {} }}", name, val, body))
        }
        Expr::Call(name, args) => {
            let args = render_args(args, params, ctx)?;
            Ok(format!("{}({})", name, args.join(", ")))
        }
        Expr::Match {
            scrut,
            alts,
            default,
        } => {
            let scrut = expr_to_rust(scrut, params, ctx)?;
            let mut out = format!("match {} {{\n", scrut);
            for alt in alts {
                let pat = if alt.binders.is_empty() {
                    alt.ctor.clone()
                } else {
                    format!("{}({})", alt.ctor, alt.binders.join(", "))
                };
                let body = expr_to_rust(&alt.body, params, ctx)?;
                out.push_str(&format!("        {} => {},\n", pat, body));
            }
            if let Some(d) = default {
                let body = expr_to_rust(d, params, ctx)?;
                out.push_str(&format!("        _ => {},\n", body));
            }
            out.push_str("    }");
            Ok(out)
        }
        Expr::Ctor(name, args) => {
            let args = render_args(args, params, ctx)?;
            if args.is_empty() {
                Ok(name.clone())
            } else {
                Ok(format!("{}({})", name, args.join(", ")))
            }
        }
        Expr::Proj(_ty, idx, e) => {
            let e = expr_to_rust(e, params, ctx)?;
            Ok(format!("({}).{}", e, idx))
        }
        Expr::Jp { name, body, .. } => {
            if ctx.jmp_count(name) == 0 {
                // No jump sites: the declaration is just a block.
                let body = expr_to_rust(body, params, ctx)?;
                Ok(format!(
                    "{{ /* jp \"{}\": no jump sites */ {} }}",
                    name, body
                ))
            } else if ctx.is_inlineable(name) {
                // Inlined at its single jump site; nothing to emit here.
                Ok(format!(
                    "/* jp \"{}\" inlined at its jump site */ ()",
                    name
                ))
            } else {
                // Cyclic or multi-caller: emit a skeleton, not a full lowering.
                let body = expr_to_rust(body, params, ctx)?;
                Ok(format!(
                    "loop {{\n        /* jp \"{}\": cyclic or multi-caller join point — manual port required */\n        {};\n        break;\n    }}",
                    name, body
                ))
            }
        }
        Expr::Jmp(name, args) => match ctx.decls.get(name.as_str()) {
            Some((jp_params, body)) if ctx.is_inlineable(name) => {
                let mut out = String::from("{ ");
                for (p, a) in jp_params.iter().zip(args.iter()) {
                    let a = expr_to_rust(a, params, ctx)?;
                    out.push_str(&format!("let {} = {}; ", p, a));
                }
                let body = expr_to_rust(body, params, ctx)?;
                out.push_str(&body);
                out.push_str(" }");
                Ok(out)
            }
            Some(_) => Ok(format!(
                "loop {{ /* jmp \"{}\": cyclic or multi-caller join point — manual port required */ break; }}",
                name
            )),
            None => Ok(format!(
                "/* jmp \"{}\": no matching jp declaration */ ()",
                name
            )),
        },
        Expr::Unreachable => Ok(String::from("unreachable!()")),
        Expr::Opaque(s) => Err(Error::OpaqueExpr(s.clone())),
    }
}

fn binop(
    a: &Expr,
    b: &Expr,
    op: &str,
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<String, Error> {
    let a = expr_to_rust(a, params, ctx)?;
    let b = expr_to_rust(b, params, ctx)?;
    Ok(format!("({} {} {})", a, op, b))
}

fn render_args(
    args: &[Expr],
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<Vec<String>, Error> {
    args.iter().map(|a| expr_to_rust(a, params, ctx)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use prod_ir::parser::parse_module;

    fn generate(ir: &str) -> String {
        let (_, module) = parse_module(ir).unwrap();
        generate_module(&module).unwrap()
    }

    #[test]
    fn test_generate_class_index() {
        let ir = r#"
(module UorAtlas.Kernel
  (def classIndex ((h2 Nat) (d Nat) (l Nat) (inst Instance)) Nat
    (add (mul (field inst "stride") h2)
         (add (mul (field inst "o") d) l)))

  (def belt ((inst Instance)) Nat
    (mul (call class_count inst)
         (shl 1 (sub (field inst "o") 1))))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn classIndex(h2: u64, d: u64, l: u64, inst: crate::Instance) -> u64 {\n    ((inst.stride() * h2) + ((inst.o * d) + l))\n}\n\npub fn belt(inst: crate::Instance) -> u64 {\n    (class_count(inst) * (1 << (inst.o - 1)))\n}\n\n"
        );
    }

    #[test]
    fn test_generate_match() {
        let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (cases x
      (alt "Some" (v) v)
      (default 0)))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn f(x: u64) -> u64 {\n    match x {\n        Some(v) => v,\n        _ => 0,\n    }\n}\n\n"
        );
    }

    #[test]
    fn test_generate_ctor_proj() {
        let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (proj "Pair" 0 (ctor "Pair" x 2)))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn f(x: u64) -> u64 {\n    (Pair(x, 2)).0\n}\n\n"
        );
    }

    #[test]
    fn test_generate_jp_jmp_inlined() {
        let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (let g (jp g (a) (add a 1)) (jmp g x)))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn f(x: u64) -> u64 {\n    { let g = /* jp \"g\" inlined at its jump site */ (); { let a = x; (a + 1) } }\n}\n\n"
        );
    }

    #[test]
    fn test_generate_cyclic_jp_skeleton() {
        let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (jp loop (i) (if (lt i 10) (jmp loop (add i 1)) i)))
)
"#;
        let out = generate(ir);
        assert!(out.contains("loop {"));
        assert!(out.contains("manual port required"));
    }

    #[test]
    fn test_generate_unreachable() {
        let ir = "(module M (def f ((x Nat)) Nat (unreachable)))";
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn f(x: u64) -> u64 {\n    unreachable!()\n}\n\n"
        );
    }

    #[test]
    fn test_param_out_of_bounds_is_an_error() {
        let ir = "(module M (def f ((x Nat)) Nat (param 5)))";
        let (_, module) = parse_module(ir).unwrap();
        assert_eq!(generate_module(&module), Err(Error::ParamOutOfBounds(5)));
    }
}
