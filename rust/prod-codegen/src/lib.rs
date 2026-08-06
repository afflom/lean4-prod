//! prod-codegen: renders `prod-ir` modules as Rust source text.
//!
//! This crate is `#![no_std]` (with `alloc`) and host-independent: it renders
//! Rust code as a plain `String`, never as `proc_macro2::TokenStream`, so it
//! can run on wasm32 or inside other hosts. `prod-macros` and `prod-cli` are
//! thin drivers on top of [`generate_module`].
//!
//! # Code generation policy
//!
//! - **Nat policy**: Lean `Nat` maps to bounded `u64` and Lean `Int` to `i64`.
//!   The current generated arithmetic is Nat-focused and makes the semantic
//!   boundary explicit: addition, multiplication, shifts, and powers panic on
//!   `u64` overflow; subtraction saturates at zero (Lean Nat subtraction);
//!   division and modulo by zero return zero (Lean Nat's total operations).
//!   There is no bignum fallback, so this is exact only while values fit in
//!   `u64`. Typed Int arithmetic remains a separate lowering task.
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
//!     when there are no args), except `Prod.mk`, which renders as a Rust
//!     tuple `(a, b)` — nested for right-nested pairs.
//!   - `Proj` renders through the projection-field table below for known
//!     structure types, and tuple-style `.idx` for unknown `(type, idx)`
//!     pairs. The table maps Lean structure projection indices to the
//!     runtime's named Rust fields; `("UorAtlas.Instance", i)` follows the
//!     field declaration order `q T O` in `lean/Example/Kernel.lean`, matching
//!     `prod_core::Instance { q, t, o }`:
//!
//!     | (type, idx)               | Rust rendering |
//!     |---------------------------|----------------|
//!     | `("UorAtlas.Instance", 0)` | `e.q`          |
//!     | `("UorAtlas.Instance", 1)` | `e.t`          |
//!     | `("UorAtlas.Instance", 2)` | `e.o`          |
//!     | anything else             | `e.<idx>`      |
//!
//!   - `Type::Tuple` renders as a Rust tuple type, so
//!     `(Tuple Nat (Tuple Nat Nat))` becomes `(u64, (u64, u64))`.
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
        | Expr::Pow(a, b)
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
        Expr::Add(a, b) => checked_binop(
            a,
            b,
            "checked_add",
            "Lean Nat addition overflow",
            params,
            ctx,
        ),
        Expr::Sub(a, b) => saturating_binop(a, b, "saturating_sub", params, ctx),
        Expr::Mul(a, b) => checked_binop(
            a,
            b,
            "checked_mul",
            "Lean Nat multiplication overflow",
            params,
            ctx,
        ),
        Expr::Div(a, b) => total_binop(a, b, "/", params, ctx),
        Expr::Mod(a, b) => total_binop(a, b, "%", params, ctx),
        Expr::Shl(a, b) => checked_shift(a, b, params, ctx),
        Expr::Pow(a, b) => {
            let a = expr_to_rust(a, params, ctx)?;
            let b = expr_to_rust(b, params, ctx)?;
            Ok(format!(
                "(({}) as u64).checked_pow(u32::try_from({}).expect(\"Lean Nat power exponent exceeds u32\")).expect(\"Lean Nat power overflow\")",
                a, b
            ))
        }
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
            if name == "Prod.mk" {
                Ok(format!("({})", args.join(", ")))
            } else if args.is_empty() {
                Ok(name.clone())
            } else {
                Ok(format!("{}({})", name, args.join(", ")))
            }
        }
        Expr::Proj(ty, idx, e) => {
            let e = expr_to_rust(e, params, ctx)?;
            if let Some(field) = instance_field(ty, *idx) {
                Ok(format!("({}).{}", e, field))
            } else {
                Ok(format!("({}).{}", e, idx))
            }
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

fn checked_binop(
    a: &Expr,
    b: &Expr,
    method: &str,
    message: &str,
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<String, Error> {
    let a = expr_to_rust(a, params, ctx)?;
    let b = expr_to_rust(b, params, ctx)?;
    Ok(format!(
        "({}).{}({}).expect(\"{}\")",
        a, method, b, message
    ))
}

fn saturating_binop(
    a: &Expr,
    b: &Expr,
    method: &str,
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<String, Error> {
    let a = expr_to_rust(a, params, ctx)?;
    let b = expr_to_rust(b, params, ctx)?;
    Ok(format!("({}).{}({})", a, method, b))
}

fn total_binop(
    a: &Expr,
    b: &Expr,
    op: &str,
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<String, Error> {
    let a = expr_to_rust(a, params, ctx)?;
    let b = expr_to_rust(b, params, ctx)?;
    Ok(format!("if ({}) == 0 {{ 0 }} else {{ ({}) {} ({}) }}", b, a, op, b))
}

fn checked_shift(
    a: &Expr,
    b: &Expr,
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<String, Error> {
    let a = expr_to_rust(a, params, ctx)?;
    let b = expr_to_rust(b, params, ctx)?;
    Ok(format!(
        "({}).checked_shl(u32::try_from({}).expect(\"Lean Nat shift amount exceeds u32\")).expect(\"Lean Nat shift overflow\")",
        a, b
    ))
}

fn render_args(
    args: &[Expr],
    params: &[(String, Type)],
    ctx: &JpContext,
) -> Result<Vec<String>, Error> {
    args.iter().map(|a| expr_to_rust(a, params, ctx)).collect()
}

/// The projection-field table (see the module docs): Lean structure
/// projection indices → the runtime's named Rust fields. The
/// `UorAtlas.Instance` row is verified against the field declaration order
/// `q T O` in `lean/Example/Kernel.lean` (LCNF projection indices follow
/// declaration order) and `prod_core::Instance { q, t, o }`. Unknown
/// `(type, idx)` pairs fall back to tuple-style `.idx`.
fn instance_field(type_name: &str, idx: u64) -> Option<&'static str> {
    if type_name == "UorAtlas.Instance" || type_name == "Instance" {
        match idx {
            0 => Some("q"),
            1 => Some("t"),
            2 => Some("o"),
            _ => None,
        }
    } else {
        None
    }
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
            "pub fn classIndex(h2: u64, d: u64, l: u64, inst: crate::Instance) -> u64 {\n    ((inst.stride()).checked_mul(h2).expect(\"Lean Nat multiplication overflow\")).checked_add(((inst.o).checked_mul(d).expect(\"Lean Nat multiplication overflow\")).checked_add(l).expect(\"Lean Nat addition overflow\")).expect(\"Lean Nat addition overflow\")\n}\n\npub fn belt(inst: crate::Instance) -> u64 {\n    (class_count(inst)).checked_mul((1).checked_shl(u32::try_from((inst.o).saturating_sub(1)).expect(\"Lean Nat shift amount exceeds u32\")).expect(\"Lean Nat shift overflow\")).expect(\"Lean Nat multiplication overflow\")\n}\n\n"
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
    fn test_generate_instance_projection_and_prod_tuple() {
        let ir = r#"
(module UorAtlas.Kernel
  (def decode ((i Instance)) (Tuple Nat (Tuple Nat Nat))
    (ctor "Prod.mk" (proj "UorAtlas.Instance" 0 i)
      (ctor "Prod.mk" (proj "UorAtlas.Instance" 2 i) 1)))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn decode(i: crate::Instance) -> (u64, (u64, u64)) {\n    ((i).q, ((i).o, 1))\n}\n\n"
        );
    }

    #[test]
    fn test_generate_kernel_ir_shapes() {
        // The exact def shapes prod-export emits for stride and classDecode
        // (see rust/prod-core/kernel.ir).
        let ir = r#"
(module UorAtlas.Kernel
  (def stride ((i Instance)) Nat
    (let _x_4 (proj "UorAtlas.Instance" 1 i) (let _x_5 (proj "UorAtlas.Instance" 2 i) (let _x_13 (mul _x_4 _x_5) _x_13))))

  (def classDecode ((idx Nat) (i Instance)) (Tuple Nat (Tuple Nat Nat))
    (let _x_4 (call stride i) (let h2 (div idx _x_4) (let rem (mod idx _x_4) (let _x_10 (proj "UorAtlas.Instance" 2 i) (let d (div rem _x_10) (let l (mod rem _x_10) (let _x_13 (ctor "Prod.mk" d l) (let _x_14 (ctor "Prod.mk" h2 _x_13) _x_14)))))))))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn stride(i: crate::Instance) -> u64 {\n    { let _x_4 = (i).t; { let _x_5 = (i).o; { let _x_13 = (_x_4).checked_mul(_x_5).expect(\"Lean Nat multiplication overflow\"); _x_13 } } }\n}\n\npub fn classDecode(idx: u64, i: crate::Instance) -> (u64, (u64, u64)) {\n    { let _x_4 = stride(i); { let h2 = if (_x_4) == 0 { 0 } else { (idx) / (_x_4) }; { let rem = if (_x_4) == 0 { 0 } else { (idx) % (_x_4) }; { let _x_10 = (i).o; { let d = if (_x_10) == 0 { 0 } else { (rem) / (_x_10) }; { let l = if (_x_10) == 0 { 0 } else { (rem) % (_x_10) }; { let _x_13 = (d, l); { let _x_14 = (h2, _x_13); _x_14 } } } } } } } }\n}\n\n"
        );
    }

    #[test]
    fn test_generate_unknown_projection_falls_back_to_index() {
        let ir = r#"
(module M
  (def f ((x Nat)) Nat
    (proj "Unknown.Struct" 3 (ctor "Unknown.Struct" x)))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn f(x: u64) -> u64 {\n    (Unknown.Struct(x)).3\n}\n\n"
        );
    }

    #[test]
    fn test_generate_zero_param_golden_def() {
        // The shape prod-export uses for goldens.ir entries.
        let ir = r#"
(module UorAtlas.Goldens
  (def golden_stride_canonical () Nat 24)

  (def golden_classDecode_43_canonical () (Tuple Nat (Tuple Nat Nat))
    (ctor "Prod.mk" 1 (ctor "Prod.mk" 2 3)))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn golden_stride_canonical() -> u64 {\n    24\n}\n\npub fn golden_classDecode_43_canonical() -> (u64, (u64, u64)) {\n    (1, (2, 3))\n}\n\n"
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
            "pub fn f(x: u64) -> u64 {\n    { let g = /* jp \"g\" inlined at its jump site */ (); { let a = x; (a).checked_add(1).expect(\"Lean Nat addition overflow\") } }\n}\n\n"
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
    fn test_generate_pow() {
        let ir = r#"
(module M
  (def belt ((i Nat)) Nat
    (pow 2 (sub i 1)))
)
"#;
        let out = generate(ir);
        assert_eq!(
            out,
            "pub fn belt(i: u64) -> u64 {\n    ((2) as u64).checked_pow(u32::try_from((i).saturating_sub(1)).expect(\"Lean Nat power exponent exceeds u32\")).expect(\"Lean Nat power overflow\")\n}\n\n"
        );
    }

    #[test]
    fn test_generate_nat_arithmetic_policy() {
        let ir = r#"
(module M
  (def add ((x Nat) (y Nat)) Nat (add x y))
  (def sub ((x Nat) (y Nat)) Nat (sub x y))
  (def div ((x Nat) (y Nat)) Nat (div x y))
  (def modu ((x Nat) (y Nat)) Nat (mod x y))
  (def shl ((x Nat) (y Nat)) Nat (shl x y))
  (def pow ((x Nat) (y Nat)) Nat (pow x y))
)
"#;
        let out = generate(ir);
        assert!(out.contains("checked_add(y).expect(\"Lean Nat addition overflow\")"));
        assert!(out.contains("saturating_sub(y)"));
        assert!(out.contains("if (y) == 0 { 0 } else { (x) / (y) }"));
        assert!(out.contains("if (y) == 0 { 0 } else { (x) % (y) }"));
        assert!(out.contains("checked_shl(u32::try_from(y).expect(\"Lean Nat shift amount exceeds u32\")).expect(\"Lean Nat shift overflow\")"));
        assert!(out.contains("checked_pow(u32::try_from(y).expect(\"Lean Nat power exponent exceeds u32\")).expect(\"Lean Nat power overflow\")"));
    }

    #[test]
    fn test_generate_unreachable() {        let ir = "(module M (def f ((x Nat)) Nat (unreachable)))";
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
