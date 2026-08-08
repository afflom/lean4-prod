//! prod-codegen: renders `prod-ir` modules as Rust source text.
//!
//! This crate is `#![no_std]` (with `alloc`) and host-independent: it renders
//! Rust code as a plain `String`, never as `proc_macro2::TokenStream`, so it
//! can run on wasm32 or inside other hosts. `prod-macros` and `prod-cli` are
//! thin drivers on top of [`generate_module`].
//!
//! # Code generation policy
//!
//! The generated code targets the project's production standard: it must not
//! panic on caller-controlled input, and it must not allocate. Those two rules
//! drive everything below.
//!
//! ## Memory profile: no heap, ever
//!
//! Nothing rendered here can allocate. Lean `List α` is the only type that
//! would naïvely need a heap, so its lowering is position-dependent:
//!
//! - **Parameter position** → `&[α]`. `List.nil` match arms render as the
//!   slice pattern `[]` and `List.cons (h t)` as `[h, t @ ..]`, so structural
//!   recursion passes the tail sub-slice directly — no rebinding, no copying.
//! - **Return position** → a caller-owned output buffer. The signature gains a
//!   trailing `output: &mut [α]` and returns `Result<usize, ComputeError>`,
//!   the length of the initialized prefix. The body is rendered in *builder
//!   mode*: `List.nil` becomes `Ok(0)`; `List.cons h t` splits one element off
//!   the front of the buffer (`split_first_mut`, so exhaustion is an `Err`,
//!   never an index panic), writes the head, recurses the tail into the
//!   remainder, and returns `1 +` the tail's length. `if`/`let`/`cases`
//!   recurse into builder mode; `let`-bound list values (LCNF emits lists in
//!   A-normal form) are resolved through a scoped environment rather than
//!   materialized.
//! - **Zero-argument definitions returning a list** (the golden values) →
//!   `&'static [α]` built from a promoted array literal.
//!
//! A list value that reaches any other position — an intermediate value used
//! as something other than a builder tail, or a list nested inside another
//! type — is an [`Error::UnsupportedList`]: an honest codegen failure rather
//! than a silently allocating fallback. `Type::Vec` is rejected outright as
//! [`Error::HeapType`].
//!
//! ## Error contract: fallibility is precise, not uniform
//!
//! Lean `Nat` maps to bounded `u64` and Lean `Int` to `i64`. The partial
//! operations report failure instead of panicking: addition, multiplication,
//! shifts, and powers render as `checked_*(..).ok_or(crate::ComputeError::X)?`
//! (with the shift/power exponent narrowed through
//! `u32::try_from(..).map_err(..)?`). Subtraction saturates at zero (Lean Nat
//! subtraction) and division/modulo by zero return zero (Lean Nat's total
//! operations), so neither is fallible. There is no bignum fallback, so this
//! is exact only while values fit in `u64`.
//!
//! A definition returns `Result<T, crate::ComputeError>` **only if it needs
//! to**: if its body contains a checked operation, or calls a definition that
//! is itself fallible, or builds a list into a caller buffer. That is a least
//! fixpoint over the module's call graph ([`Shape`]), so leaf definitions and
//! the zero-argument goldens keep their plain return types. Calls to fallible
//! definitions render as `f(args)?`.
//!
//! ## Other lowerings
//!
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
//!     The Nat structural-recursion ctors are special-cased: `Nat.zero` renders
//!     as the literal pattern `0`, and `Nat.succ k` as the `_` arm with
//!     `k` bound to `(scrut).saturating_sub(1)` (exact, since the zero arm
//!     matches first). `Bool.true`/`Bool.false` → `true`/`false` patterns, and
//!     `Option.none`/`Option.some v` → `None`/`Some(v)` patterns. The List
//!     ctors use the slice patterns described above.
//!   - `Ctor` renders as tuple-style construction `Name(args...)` (bare `Name`
//!     when there are no args), except `Prod.mk`, which renders as a Rust
//!     tuple `(a, b)` — nested for right-nested pairs — and the Bool/Option
//!     ctors, which render as `true`/`false` and `None`/`Some(x)`.
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
//!
//! ## Recursion
//!
//! Generated recursion is structurally bounded by a fuel or data argument (the
//! Lean side must already be terminating for LCNF to emit it), so stack depth
//! is a function of the caller's inputs, not of unbounded search.

#![no_std]

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::fmt;
use prod_ir::{Alt, Definition, Expr, Module, Type};

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
    /// A list value appears somewhere the allocation-free lowering cannot
    /// render it: nested inside another type, or used as an intermediate
    /// value rather than flowing into the output buffer.
    UnsupportedList(String),
    /// A type that would require a heap allocation in generated code.
    HeapType(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::OpaqueExpr(s) => write!(f, "cannot generate code for opaque expression: {}", s),
            Error::ParamOutOfBounds(i) => write!(f, "parameter index {} is out of bounds", i),
            Error::UnsupportedList(s) => {
                write!(f, "list value cannot be rendered without allocating: {}", s)
            }
            Error::HeapType(s) => write!(
                f,
                "type would require a heap allocation in generated code: {}",
                s
            ),
        }
    }
}

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
type Signatures<'m> = BTreeMap<&'m str, Shape>;

/// Render a whole module: one `pub fn` per definition.
pub fn generate_module(module: &Module) -> Result<String, Error> {
    let shapes = signatures(&module.definitions);
    let mut out = String::new();
    for def in &module.definitions {
        out.push_str(&generate_def_in(def, &shapes)?);
        out.push('\n');
    }
    Ok(out)
}

/// Render a single definition as a `pub fn`.
///
/// Calls to definitions outside `def` itself are assumed infallible, since
/// there is no module to resolve them against; use [`generate_module`] when
/// cross-definition fallibility matters.
pub fn generate_def(def: &Definition) -> Result<String, Error> {
    let one = core::slice::from_ref(def);
    generate_def_in(def, &signatures(one))
}

/// Compute every definition's [`Shape`] as a least fixpoint over the call
/// graph: seed everything infallible, then promote until nothing changes.
/// Monotone (shapes only ever move `Value` → `Fallible`), so it terminates.
fn signatures<'m>(defs: &'m [Definition]) -> Signatures<'m> {
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
            if is_fallible(&def.body, &shapes) {
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
fn is_fallible(expr: &Expr, shapes: &Signatures) -> bool {
    let here = match expr {
        Expr::Add(..) | Expr::Mul(..) | Expr::Shl(..) | Expr::Pow(..) => true,
        Expr::Call(name, _) => matches!(
            shapes.get(name.as_str()),
            Some(Shape::Fallible) | Some(Shape::Buffer)
        ),
        _ => false,
    };
    here || children(expr).any(|child| is_fallible(child, shapes))
}

fn generate_def_in<'m>(def: &'m Definition, shapes: &Signatures<'m>) -> Result<String, Error> {
    let shape = shapes
        .get(def.name.as_str())
        .copied()
        .unwrap_or(Shape::Value);
    let renderer = Renderer {
        shapes,
        params: &def.params,
        ctx: JpContext::collect(&def.body),
    };

    let mut params = String::new();
    for (i, (name, ty)) in def.params.iter().enumerate() {
        if i > 0 {
            params.push_str(", ");
        }
        params.push_str(&format!("{}: {}", name, param_type_to_rust(ty)?));
    }

    match shape {
        Shape::StaticList => {
            let elem = list_element(&def.ret)?;
            if is_fallible(&def.body, shapes) {
                return Err(Error::UnsupportedList(format!(
                    "`{}` computes its list elements, so it cannot be a promoted &'static slice",
                    def.name
                )));
            }
            let mut items = Vec::new();
            renderer.static_list(&def.body, &[], &mut items)?;
            Ok(format!(
                "pub fn {}() -> &'static [{}] {{\n    &[{}]\n}}\n",
                def.name,
                type_to_rust(elem)?,
                items.join(", ")
            ))
        }
        Shape::Buffer => {
            let elem = list_element(&def.ret)?;
            if !params.is_empty() {
                params.push_str(", ");
            }
            params.push_str(&format!("output: &mut [{}]", type_to_rust(elem)?));
            let body = renderer.render(
                &def.body,
                &Mode::Builder {
                    out: "output",
                    env: &[],
                    depth: 0,
                },
            )?;
            Ok(format!(
                "pub fn {}({}) -> Result<usize, crate::ComputeError> {{\n    {}\n}}\n",
                def.name, params, body
            ))
        }
        Shape::Fallible => Ok(format!(
            "pub fn {}({}) -> Result<{}, crate::ComputeError> {{\n    Ok({})\n}}\n",
            def.name,
            params,
            type_to_rust(&def.ret)?,
            renderer.value(&def.body)?
        )),
        Shape::Value => Ok(format!(
            "pub fn {}({}) -> {} {{\n    {}\n}}\n",
            def.name,
            params,
            type_to_rust(&def.ret)?,
            renderer.value(&def.body)?
        )),
    }
}

/// Rust spelling of a type in an ordinary (owned, by-value) position.
fn type_to_rust(ty: &Type) -> Result<String, Error> {
    Ok(match ty {
        Type::Nat => String::from("u64"),
        Type::Int => String::from("i64"),
        Type::Bool => String::from("bool"),
        Type::Instance => String::from("crate::Instance"),
        Type::Option(inner) => format!("Option<{}>", type_to_rust(inner)?),
        Type::Tuple(items) => {
            let mut rendered = Vec::with_capacity(items.len());
            for item in items {
                rendered.push(type_to_rust(item)?);
            }
            format!("({})", rendered.join(", "))
        }
        Type::Opaque(s) => s.clone(),
        // Lists are only renderable at the top level of a parameter or return
        // type, where the caller supplies the storage.
        Type::List(inner) => {
            return Err(Error::UnsupportedList(format!(
                "(List {}) is only supported directly as a parameter or return type",
                type_to_rust(inner).unwrap_or_else(|_| String::from("_"))
            )))
        }
        Type::Vec(inner) => {
            return Err(Error::HeapType(format!(
                "(Vec {})",
                type_to_rust(inner).unwrap_or_else(|_| String::from("_"))
            )))
        }
    })
}

/// Rust spelling of a parameter type: a top-level list borrows as a slice.
fn param_type_to_rust(ty: &Type) -> Result<String, Error> {
    match ty {
        Type::List(inner) => Ok(format!("&[{}]", type_to_rust(inner)?)),
        _ => type_to_rust(ty),
    }
}

/// The element type of a list return type.
fn list_element(ty: &Type) -> Result<&Type, Error> {
    match ty {
        Type::List(inner) => Ok(inner),
        _ => Err(Error::UnsupportedList(
            "expected a list return type".to_string(),
        )),
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
        | Expr::Le(a, b)
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

/// Where the expression being rendered will land.
///
/// The two modes share one traversal: control flow (`if`, `let`, `cases`)
/// is rendered identically and simply propagates the mode into its branches,
/// while the leaves differ.
enum Mode<'x, 'm> {
    /// Ordinary value position. The rendered text has the expression's own
    /// Rust type, with `?` embedded wherever an operation can fail.
    Value,
    /// List builder position. The rendered text has type
    /// `Result<usize, crate::ComputeError>` and fills `out`.
    Builder {
        /// The `&mut [T]` expression this list is written into.
        out: &'x str,
        /// `let`-bound list values in scope, innermost last. LCNF emits lists
        /// in A-normal form, so cons cells arrive as chains of `let`s rather
        /// than as one nested expression.
        env: &'x [(&'m str, &'m Expr)],
        /// Nesting depth, used to keep generated temporaries unique.
        depth: usize,
    },
}

struct Renderer<'s, 'm> {
    shapes: &'s Signatures<'m>,
    params: &'m [(String, Type)],
    ctx: JpContext<'m>,
}

impl<'m> Renderer<'_, 'm> {
    fn value(&self, expr: &'m Expr) -> Result<String, Error> {
        self.render(expr, &Mode::Value)
    }

    fn shape_of(&self, name: &str) -> Option<Shape> {
        self.shapes.get(name).copied()
    }

    /// Is this expression a list value (and therefore only renderable in
    /// builder position or as a `let` binding resolved through `env`)?
    fn is_list_valued(&self, expr: &Expr, env: &[(&'m str, &'m Expr)]) -> bool {
        match expr {
            Expr::Ctor(name, _) => name == "List.nil" || name == "List.cons",
            Expr::Call(name, _) => matches!(
                self.shape_of(name),
                Some(Shape::Buffer) | Some(Shape::StaticList)
            ),
            Expr::Var(name) => lookup(env, name).is_some(),
            _ => false,
        }
    }

    fn render(&self, expr: &'m Expr, mode: &Mode<'_, 'm>) -> Result<String, Error> {
        match expr {
            // ---- control flow: identical in both modes ----
            Expr::If(cond, t, f) => Ok(format!(
                "if {} {{ {} }} else {{ {} }}",
                self.value(cond)?,
                self.render(t, mode)?,
                self.render(f, mode)?
            )),
            Expr::Let(name, val, body) => match mode {
                Mode::Builder { out, env, depth } if self.is_list_valued(val, env) => {
                    // A list binding has no runtime representation to emit;
                    // record it and resolve uses through the environment.
                    let mut extended = env.to_vec();
                    extended.push((name.as_str(), val));
                    self.render(
                        body,
                        &Mode::Builder {
                            out,
                            env: &extended,
                            depth: *depth,
                        },
                    )
                }
                _ => Ok(format!(
                    "{{ let {} = {}; {} }}",
                    name,
                    self.value(val)?,
                    self.render(body, mode)?
                )),
            },
            Expr::Match {
                scrut,
                alts,
                default,
            } => self.render_match(scrut, alts, default.as_deref(), mode),

            // ---- list-shaped leaves ----
            Expr::Ctor(name, args) if name == "List.nil" && args.is_empty() => match mode {
                // Turbofished: an empty list is the one builder leaf that
                // constrains neither type parameter on its own, and it can
                // appear under a `?` (as the tail of a cons).
                Mode::Builder { .. } => Ok(String::from("Ok::<usize, crate::ComputeError>(0)")),
                Mode::Value => Err(Error::UnsupportedList(
                    "`List.nil` outside a list return position".to_string(),
                )),
            },
            Expr::Ctor(name, args) if name == "List.cons" && args.len() == 2 => match mode {
                Mode::Builder { out, env, depth } => {
                    self.render_cons(&args[0], &args[1], out, env, *depth)
                }
                Mode::Value => Err(Error::UnsupportedList(
                    "`List.cons` outside a list return position".to_string(),
                )),
            },

            // ---- everything else ----
            Expr::Var(name) => match mode {
                Mode::Builder { env, .. } => match lookup(env, name) {
                    Some(bound) => self.render(bound, mode),
                    None => Err(Error::UnsupportedList(format!(
                        "`{}` is not a list built in this definition",
                        name
                    ))),
                },
                Mode::Value => Ok(name.clone()),
            },
            Expr::Call(name, args) => {
                let rendered = self.render_args(args)?;
                match (mode, self.shape_of(name)) {
                    (Mode::Builder { out, .. }, Some(Shape::Buffer)) => {
                        // The callee writes straight into our remaining buffer
                        // and reports how much of it it used.
                        let mut all = rendered;
                        all.push((*out).to_string());
                        Ok(format!("{}({})", name, all.join(", ")))
                    }
                    (Mode::Builder { .. }, _) => Err(Error::UnsupportedList(format!(
                        "`{}` does not build its list into a caller buffer",
                        name
                    ))),
                    (Mode::Value, Some(Shape::Buffer)) => Err(Error::UnsupportedList(format!(
                        "`{}` returns a list; its result cannot be used as an intermediate value",
                        name
                    ))),
                    (Mode::Value, Some(Shape::Fallible)) => {
                        Ok(format!("{}({})?", name, rendered.join(", ")))
                    }
                    (Mode::Value, _) => Ok(format!("{}({})", name, rendered.join(", "))),
                }
            }

            // Remaining nodes are value-typed; reaching them in builder mode
            // means the IR put a non-list where a list was declared.
            _ => match mode {
                Mode::Builder { .. } => Err(Error::UnsupportedList(
                    "expression does not build a list".to_string(),
                )),
                Mode::Value => self.render_value_leaf(expr),
            },
        }
    }

    fn render_value_leaf(&self, expr: &'m Expr) -> Result<String, Error> {
        match expr {
            Expr::Nat(n) => Ok(format!("{}", n)),
            Expr::Int(n) => Ok(format!("{}", n)),
            Expr::Bool(b) => Ok(format!("{}", b)),
            Expr::Param(index) => self
                .params
                .get(*index)
                .map(|(name, _)| name.clone())
                .ok_or(Error::ParamOutOfBounds(*index)),
            Expr::Field(obj, field) => {
                let obj = self.value(obj)?;
                if METHOD_FIELDS.contains(&field.as_str()) {
                    Ok(format!("{}.{}()", obj, field))
                } else {
                    Ok(format!("{}.{}", obj, field))
                }
            }
            Expr::Add(a, b) => self.checked_binop(a, b, "checked_add", "AddOverflow"),
            Expr::Mul(a, b) => self.checked_binop(a, b, "checked_mul", "MulOverflow"),
            Expr::Sub(a, b) => {
                // Lean Nat subtraction truncates at zero, so it is total.
                // See `checked_binop` for the `as u64` receiver pin.
                Ok(format!(
                    "(({}) as u64).saturating_sub({})",
                    self.value(a)?,
                    self.value(b)?
                ))
            }
            Expr::Div(a, b) => self.total_binop(a, b, "/"),
            Expr::Mod(a, b) => self.total_binop(a, b, "%"),
            Expr::Shl(a, b) => self.checked_exponent_op(
                a,
                b,
                "checked_shl",
                "ShiftExponentTooLarge",
                "ShiftOverflow",
            ),
            Expr::Pow(a, b) => {
                self.checked_exponent_op(a, b, "checked_pow", "PowExponentTooLarge", "PowOverflow")
            }
            Expr::Eq(a, b) => self.binop(a, b, "=="),
            Expr::Lt(a, b) => self.binop(a, b, "<"),
            Expr::Le(a, b) => self.binop(a, b, "<="),
            Expr::Gt(a, b) => self.binop(a, b, ">"),
            Expr::Ctor(name, args) => {
                let args = self.render_args(args)?;
                if name == "Prod.mk" {
                    Ok(format!("({})", args.join(", ")))
                } else if name == "Bool.true" && args.is_empty() {
                    Ok(String::from("true"))
                } else if name == "Bool.false" && args.is_empty() {
                    Ok(String::from("false"))
                } else if name == "Option.none" && args.is_empty() {
                    Ok(String::from("None"))
                } else if name == "Option.some" && args.len() == 1 {
                    Ok(format!("Some({})", args[0]))
                } else if args.is_empty() {
                    Ok(name.clone())
                } else {
                    Ok(format!("{}({})", name, args.join(", ")))
                }
            }
            Expr::Proj(ty, idx, e) => {
                let e = self.value(e)?;
                match instance_field(ty, *idx) {
                    Some(field) => Ok(format!("({}).{}", e, field)),
                    None => Ok(format!("({}).{}", e, idx)),
                }
            }
            Expr::Jp { name, body, .. } => {
                if self.ctx.jmp_count(name) == 0 {
                    // No jump sites: the declaration is just a block.
                    Ok(format!(
                        "{{ /* jp \"{}\": no jump sites */ {} }}",
                        name,
                        self.value(body)?
                    ))
                } else if self.ctx.is_inlineable(name) {
                    // Inlined at its single jump site; nothing to emit here.
                    Ok(format!("/* jp \"{}\" inlined at its jump site */ ()", name))
                } else {
                    // Cyclic or multi-caller: emit a skeleton, not a full lowering.
                    Ok(format!(
                        "loop {{\n        /* jp \"{}\": cyclic or multi-caller join point — manual port required */\n        {};\n        break;\n    }}",
                        name,
                        self.value(body)?
                    ))
                }
            }
            Expr::Jmp(name, args) => match self.ctx.decls.get(name.as_str()) {
                Some((jp_params, body)) if self.ctx.is_inlineable(name) => {
                    let mut out = String::from("{ ");
                    for (p, a) in jp_params.iter().zip(args.iter()) {
                        out.push_str(&format!("let {} = {}; ", p, self.value(a)?));
                    }
                    out.push_str(&self.value(body)?);
                    out.push_str(" }");
                    Ok(out)
                }
                Some(_) => Ok(format!(
                    "loop {{ /* jmp \"{}\": cyclic or multi-caller join point — manual port required */ break; }}",
                    name
                )),
                None => Ok(format!("/* jmp \"{}\": no matching jp declaration */ ()", name)),
            },
            Expr::Unreachable => Ok(String::from("unreachable!()")),
            Expr::Opaque(s) => Err(Error::OpaqueExpr(s.clone())),
            // Handled by `render` before it delegates here.
            Expr::If(..) | Expr::Let(..) | Expr::Match { .. } | Expr::Var(_) | Expr::Call(..) => {
                unreachable!("control-flow nodes are rendered by `render`")
            }
        }
    }

    /// `List.cons head tail` in builder position: take one element off the
    /// front of the buffer, write the head, and recurse the tail into what is
    /// left. `split_first_mut` makes exhaustion an `Err` rather than an index
    /// panic, so the generated code has no bounds-check panic path at all.
    fn render_cons(
        &self,
        head: &'m Expr,
        tail: &'m Expr,
        out: &str,
        env: &[(&'m str, &'m Expr)],
        depth: usize,
    ) -> Result<String, Error> {
        let head = self.value(head)?;
        let (slot, rest_buf) = (format!("__head{}", depth), format!("__rest{}", depth));
        let rest = self.render(
            tail,
            &Mode::Builder {
                out: &rest_buf,
                env,
                depth: depth + 1,
            },
        )?;
        Ok(format!(
            "match ({}).split_first_mut() {{ None => Err(crate::ComputeError::OutputTooSmall), Some(({}, {})) => {{ *{} = {}; let __len{} = {}?; Ok(__len{} + 1) }} }}",
            out, slot, rest_buf, slot, head, depth, rest, depth
        ))
    }

    fn render_match(
        &self,
        scrut: &'m Expr,
        alts: &'m [Alt],
        default: Option<&'m Expr>,
        mode: &Mode<'_, 'm>,
    ) -> Result<String, Error> {
        let scrut = self.value(scrut)?;
        let mut out = format!("match {} {{\n", scrut);
        for alt in alts {
            let body = self.render(&alt.body, mode)?;
            let arm = match (alt.ctor.as_str(), alt.binders.len()) {
                // LCNF structural recursion on Nat cases: `Nat.zero` is the
                // literal `0`; `Nat.succ k` binds the predecessor. Since the
                // zero arm matches first, the succ arm's scrutinee is ≥ 1 and
                // `saturating_sub(1)` is the exact predecessor (and stays
                // within the crate's bounded-Nat policy).
                ("Nat.zero", 0) => format!("        0 => {},\n", body),
                ("Nat.succ", 1) => format!(
                    "        _ => {{ let {} = ({}).saturating_sub(1); {} }},\n",
                    alt.binders[0], scrut, body
                ),
                // Lists are slices: the empty and non-empty slice patterns are
                // exhaustive, and the tail binds as a sub-slice at no cost.
                // Match ergonomics bind the head by reference; rebind it by
                // value so arithmetic on it needs no dereference syntax.
                ("List.nil", 0) => format!("        [] => {},\n", body),
                ("List.cons", 2) => format!(
                    "        [{}, {} @ ..] => {{ let {} = *{}; {} }},\n",
                    alt.binders[0], alt.binders[1], alt.binders[0], alt.binders[0], body
                ),
                ("Bool.true", 0) => format!("        true => {},\n", body),
                ("Bool.false", 0) => format!("        false => {},\n", body),
                ("Option.none", 0) => format!("        None => {},\n", body),
                ("Option.some", 1) => format!("        Some({}) => {},\n", alt.binders[0], body),
                _ if alt.binders.is_empty() => format!("        {} => {},\n", alt.ctor, body),
                _ => format!(
                    "        {}({}) => {},\n",
                    alt.ctor,
                    alt.binders.join(", "),
                    body
                ),
            };
            out.push_str(&arm);
        }
        if let Some(d) = default {
            out.push_str(&format!("        _ => {},\n", self.render(d, mode)?));
        }
        out.push_str("    }");
        Ok(out)
    }

    /// Flatten a constant `List.cons`/`List.nil` chain into array elements for
    /// a promoted `&'static [T]`. Only `let`-bound list values are followed;
    /// anything computed belongs in builder mode instead.
    fn static_list(
        &self,
        expr: &'m Expr,
        env: &[(&'m str, &'m Expr)],
        items: &mut Vec<String>,
    ) -> Result<(), Error> {
        match expr {
            Expr::Var(name) => match lookup(env, name) {
                Some(bound) => self.static_list(bound, env, items),
                None => Err(Error::UnsupportedList(format!(
                    "`{}` is not a constant list",
                    name
                ))),
            },
            Expr::Let(name, val, body) if self.is_list_valued(val, env) => {
                let mut extended = env.to_vec();
                extended.push((name.as_str(), val));
                self.static_list(body, &extended, items)
            }
            Expr::Ctor(name, args) if name == "List.nil" && args.is_empty() => Ok(()),
            Expr::Ctor(name, args) if name == "List.cons" && args.len() == 2 => {
                items.push(self.value(&args[0])?);
                self.static_list(&args[1], env, items)
            }
            _ => Err(Error::UnsupportedList(
                "zero-argument list definitions must be constant cons chains".to_string(),
            )),
        }
    }

    fn render_args(&self, args: &'m [Expr]) -> Result<Vec<String>, Error> {
        args.iter().map(|a| self.value(a)).collect()
    }

    fn binop(&self, a: &'m Expr, b: &'m Expr, op: &str) -> Result<String, Error> {
        Ok(format!("({} {} {})", self.value(a)?, op, self.value(b)?))
    }

    /// `checked_add`/`checked_mul`: report overflow instead of panicking.
    ///
    /// `as u64` pins the receiver: method calls on an inferred `{integer}`
    /// (a let-bound literal, e.g. LCNF's `let _x := 1`) fail method resolution
    /// (E0689) — a no-op when the receiver is already `u64`.
    fn checked_binop(
        &self,
        a: &'m Expr,
        b: &'m Expr,
        method: &str,
        error: &str,
    ) -> Result<String, Error> {
        Ok(format!(
            "(({}) as u64).{}({}).ok_or(crate::ComputeError::{})?",
            self.value(a)?,
            method,
            self.value(b)?,
            error
        ))
    }

    /// `checked_shl`/`checked_pow`: the exponent must also narrow to `u32`,
    /// which is a second, distinct failure mode.
    fn checked_exponent_op(
        &self,
        a: &'m Expr,
        b: &'m Expr,
        method: &str,
        exponent_error: &str,
        overflow_error: &str,
    ) -> Result<String, Error> {
        Ok(format!(
            "(({}) as u64).{}(u32::try_from({}).map_err(|_| crate::ComputeError::{})?).ok_or(crate::ComputeError::{})?",
            self.value(a)?,
            method,
            self.value(b)?,
            exponent_error,
            overflow_error
        ))
    }

    /// Lean Nat division and modulo are total: `x / 0 = x % 0 = 0`.
    fn total_binop(&self, a: &'m Expr, b: &'m Expr, op: &str) -> Result<String, Error> {
        let (a, b) = (self.value(a)?, self.value(b)?);
        Ok(format!(
            "if ({}) == 0 {{ 0 }} else {{ ({}) {} ({}) }}",
            b, a, op, b
        ))
    }
}

/// Innermost-first lookup in a builder-mode list environment.
fn lookup<'m>(env: &[(&'m str, &'m Expr)], name: &str) -> Option<&'m Expr> {
    env.iter()
        .rev()
        .find(|(bound, _)| *bound == name)
        .map(|(_, value)| *value)
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
mod tests;
