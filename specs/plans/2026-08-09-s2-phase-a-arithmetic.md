# S2 Phase A — the arithmetic layer, Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `Int` and sized-integer arithmetic work, faithfully to Lean's own semantics, by giving every arithmetic node in the IR an explicit numeric kind.

**Architecture:** Arithmetic nodes carry a `NumKind` tag that the Lean side emits from what it already knows (`Nat.add` vs `Int.add` vs `UInt8.add`). Codegen switches rendering on the tag: checked-and-fallible for `Nat`, checked-and-Euclidean for `Int`, wrapping-and-infallible for sized. Comparisons stay kind-less — both operands share a Rust type and `<` works for all of them.

**Tech Stack:** Lean 4.30.0 (pinned, no mathlib), Rust 1.95, `nom` 7 parser, `prod-macros` proc macro, `just` + nix dev shell.

**Design doc:** `specs/designs/2026-08-09-s2-scalar-completeness-and-invariants.md` — this plan is **Phase A only** (its migration steps 1–5). Phase B (invariant-carrying types and `Fin`) gets its own plan, written against the arithmetic layer as it actually ships.

## Global Constraints

- NO mathlib. Pure Lean 4 core/Init. NO `sorry`, NO `axiom`.
- Generated artifacts are never hand-edited. `rust/prod-core/kernel.ir`, `goldens.ir`, `roots.json`, `coverage.md`, `subset.json` are gitignored — do NOT `git add` them, `git add` errors on an explicitly listed ignored path. `lean/Conformance/golden.ir`, `lean/Conformance/golden-rejected.ir` and `specs/lean-for-production.md` are committed but regenerated only by running the tooling.
- Generated code contract unchanged: no panic on caller-controlled input, no heap allocation.
- `prod-ir` and `prod-codegen` stay `#![no_std]` and wasm32-clean. No `std`.
- `unsafe_code = "forbid"` workspace-wide except `prod-wasm` and `prod-alloc-counter`.
- lean/lake are NOT on PATH. Always: `cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build`. Lean builds take MINUTES — use 600000ms timeouts. `just` exists only inside the nix shell.
- Gates before every commit: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod` from the repo root, plus from `rust/`: `cargo clippy --all-targets -- -D warnings`, `cargo fmt --all -- --check`, and `RUSTC=$(rustup which --toolchain stable rustc) rustup run stable cargo build -p prod-ir -p prod-codegen -p prod-wasm --target wasm32-unknown-unknown`.
- Commit at the end of every task. Do NOT `git push`.
- **This codebase compiles its generated output.** `rust/prod-codegen-compile-tests` expands `prod_defs!` over the conformance golden, so a mis-rendering fails to build rather than passing a string comparison. Do not weaken that crate to make something pass.

## File structure

| File | Responsibility in this plan |
|---|---|
| `rust/prod-ir/src/lib.rs` | `NumKind` enum, kind-tagged arithmetic variants, new `Neg` variant |
| `rust/prod-ir/src/parser.rs` | `(add Nat a b)` grammar, `parse_num_kind` |
| `rust/prod-codegen/src/lib.rs` | kind-driven rendering, kind-aware `as` pin, kind-aware fallibility, `UnsupportedKind` |
| `rust/prod-core/src/error.rs` | `SubOverflow`, `DivOverflow`, `NegOverflow` |
| `lean/Prod/Lower.lean` | `numOpNames`/`deciderNames` keyed by kind, kind emission, `Int.neg` |
| `lean/Prod/Emit.lean` | `subsetJson` reads the kind-keyed lists |
| `lean/Conformance.lean` | conformance cases per kind, incl. negative operands |

---

### Task 1: Confirm what Bool connectives actually lower to

The design says `&&`/`||` are `@[macro_inline]` and probably reach LCNF as `cases`, needing no new IR node. That is a prediction. This task turns it into a fact before any later task writes a whitelist entry against it.

**Files:**
- Modify: `lean/Conformance.lean`
- Modify: `lean/Conformance/golden.ir` (regenerated)
- Modify: `specs/designs/2026-08-09-s2-scalar-completeness-and-invariants.md` (record the finding)

**Interfaces:**
- Produces: a recorded finding — either "Bool connectives need no IR change" or the exact constants that must be whitelisted.

- [ ] **Step 1: Add the probe definitions**

In `lean/Conformance.lean`, before `end Conformance`:

```lean
-- Bool connectives. `&&`/`||` are `@[macro_inline]` in Lean and elaborate
-- through `match`, so the expectation is that they reach LCNF as `cases` on
-- `Bool.true`/`Bool.false` and need no IR node at all. These pin whichever
-- answer is true.
@[prod] def c_bool_and (a b : Nat) : Bool := (a < b) && (b < 10)
@[prod] def c_bool_or  (a b : Nat) : Bool := (a < b) || (b < 10)
@[prod] def c_bool_not (a b : Nat) : Bool := !(a < b)
```

- [ ] **Step 2: Export and read the result**

Run:
```bash
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
```

Read the three definitions in `lean/Conformance/golden.ir`. Determine which holds:

- **(A) No IR change needed** — they lower to `cases`/`if` over existing nodes, with no `(extern ...)` and no `(opaque ...)`.
- **(B) They surface as extern calls** — the golden contains `(extern "..." ...)`. Record the exact constant names.

- [ ] **Step 3: Act on the finding**

If **(A)**: nothing further. The definitions stay as permanent conformance cases proving connectives work.

If **(B)**: the probe definitions cannot stay in `lean/Conformance.lean`, because that corpus promises everything in it also generates Rust that compiles, and an `(extern ...)` is a codegen rejection. Move them to `lean/ConformanceRejected.lean` (renaming `c_` to `r_`), regenerate, and extend `rust/prod-codegen-compile-tests/tests/rejected.rs` to expect the additional rejection. Then record the constant names so a later task can whitelist them.

- [ ] **Step 4: Record the finding in the design doc**

Add to `specs/designs/2026-08-09-s2-scalar-completeness-and-invariants.md`, in the "Bool connectives — verify before implementing" subsection, a sentence of this shape with the observed answer filled in:

```
RESOLVED (Task 1): Bool connectives lower to <cases over existing nodes | extern
calls on <names>>. Evidence: `c_bool_and`/`c_bool_or`/`c_bool_not` in
lean/Conformance/golden.ir. <No IR change is needed. | The following constants
must be whitelisted: ...>
```

- [ ] **Step 5: Gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`

```bash
git add lean/Conformance.lean lean/Conformance/golden.ir specs/designs/2026-08-09-s2-scalar-completeness-and-invariants.md
git commit -m "Pin what Bool connectives lower to

The design predicted && and || reach LCNF as cases over existing nodes,
needing no IR node. This turns the prediction into a recorded fact
before any later task writes a whitelist entry against it, and leaves
the probes behind as permanent conformance cases.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: Explicit numeric kinds

Atomic by necessity: the grammar change breaks every existing arithmetic node, so the IR, codegen, the Lean emitter and the goldens must move together. **No behaviour changes** — `Nat` renders exactly as it does today. If any generated output differs beyond the IR text itself, something is wrong.

**Files:**
- Modify: `rust/prod-ir/src/lib.rs`, `rust/prod-ir/src/parser.rs`
- Modify: `rust/prod-codegen/src/lib.rs`, `rust/prod-codegen/src/tests.rs`
- Modify: `lean/Prod/Lower.lean`, `lean/Prod/Emit.lean`
- Modify: `lean/Conformance/golden.ir`, `lean/Conformance/golden-rejected.ir` (regenerated)
- Modify: `rust/prod-codegen-compile-tests/fixtures/representative.ir`

**Interfaces:**
- Produces:
  - `prod_ir::NumKind { Nat, Int, U8, U16, U32, U64 }` with `pub const fn rust_type(self) -> &'static str`
  - `Expr::{Add,Sub,Mul,Div,Mod,Shl,Shr,Pow}(NumKind, Box<Expr>, Box<Expr>)`
  - Grammar `(add Nat a b)`; kind tokens `Nat | Int | U8 | U16 | U32 | U64`
  - Comparisons (`Eq`, `Lt`, `Le`, `Gt`) are UNCHANGED and carry no kind
  - `Prod.numOpNames : List (Name × String × String)` — (Lean constant, IR op, IR kind)
  - `Prod.opWhitelist : Name → Option (String × String)`

- [ ] **Step 1: Write the failing parser tests**

Add to the `tests` module in `rust/prod-ir/src/parser.rs`:

```rust
#[test]
fn test_parse_kind_tagged_arithmetic() {
    let (rest, expr) = parse_expr("(add Nat a b)").unwrap();
    assert!(rest.is_empty());
    match expr {
        Expr::Add(kind, _, _) => assert_eq!(kind, NumKind::Nat),
        _ => panic!("expected Add, got {:?}", expr),
    }
    assert!(matches!(
        parse_expr("(mul Int a b)").unwrap().1,
        Expr::Mul(NumKind::Int, _, _)
    ));
    assert!(matches!(
        parse_expr("(sub U8 a b)").unwrap().1,
        Expr::Sub(NumKind::U8, _, _)
    ));
}

#[test]
fn test_parse_every_num_kind() {
    for (text, expected) in [
        ("Nat", NumKind::Nat),
        ("Int", NumKind::Int),
        ("U8", NumKind::U8),
        ("U16", NumKind::U16),
        ("U32", NumKind::U32),
        ("U64", NumKind::U64),
    ] {
        let ir = alloc::format!("(add {} a b)", text);
        match parse_expr(&ir).unwrap().1 {
            Expr::Add(kind, _, _) => assert_eq!(kind, expected, "for {}", text),
            other => panic!("expected Add for {}, got {:?}", text, other),
        }
    }
}

#[test]
fn test_untagged_arithmetic_no_longer_parses() {
    // The tag is mandatory. An untagged node would have to mean something by
    // default, and "add means Nat" implicitly is exactly what this removes.
    // No arm of `parse_paren_expr` matches `(add a b)` once `add` requires a
    // kind, so the whole expression fails rather than parsing as something
    // else.
    assert!(parse_expr("(add a b)").is_err());
}

#[test]
fn test_parse_neg() {
    match parse_expr("(neg Int a)").unwrap().1 {
        Expr::Neg(kind, _) => assert_eq!(kind, NumKind::Int),
        other => panic!("expected Neg, got {:?}", other),
    }
}

#[test]
fn test_comparisons_are_not_kind_tagged() {
    // Both operands share a Rust type and `<` works for every kind, so a tag
    // here would be noise.
    assert!(matches!(parse_expr("(lt a b)").unwrap().1, Expr::Lt(_, _)));
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cd rust && cargo test -p prod-ir`
Expected: FAIL — `NumKind` does not exist.

- [ ] **Step 3: Add `NumKind` and retag the variants**

In `rust/prod-ir/src/lib.rs`, above `Expr`:

```rust
/// The numeric type an arithmetic node operates on.
///
/// Carried explicitly rather than inferred. The Lean side sees `Nat.add` vs
/// `Int.add` vs `UInt8.add` and knows exactly; codegen would have to guess,
/// and guessing is how this project previously shipped a type declaration and
/// a projection that disagreed about a field name. The three kinds have
/// genuinely different arithmetic contracts — `Nat` and `Int` are checked,
/// sized integers wrap — so a wrong guess is a wrong answer, not a style slip.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum NumKind {
    /// Lean `Nat`, unbounded. Bounded to `u64` by policy.
    Nat,
    /// Lean `Int`, unbounded. Bounded to `i64` by policy.
    Int,
    U8,
    U16,
    U32,
    U64,
}

impl NumKind {
    /// The Rust type this kind renders as. Also the cast used to pin an
    /// arithmetic receiver's type — LCNF emits let-bound integer literals
    /// whose type is ambiguous, and a method call on `{integer}` fails
    /// resolution (E0689).
    pub const fn rust_type(self) -> &'static str {
        match self {
            NumKind::Nat => "u64",
            NumKind::Int => "i64",
            NumKind::U8 => "u8",
            NumKind::U16 => "u16",
            NumKind::U32 => "u32",
            NumKind::U64 => "u64",
        }
    }
}
```

Retag the eight arithmetic variants and add `Neg`, leaving comparisons alone:

```rust
    Add(NumKind, Box<Expr>, Box<Expr>),
    Sub(NumKind, Box<Expr>, Box<Expr>),
    Mul(NumKind, Box<Expr>, Box<Expr>),
    Div(NumKind, Box<Expr>, Box<Expr>),
    Mod(NumKind, Box<Expr>, Box<Expr>),
    Shl(NumKind, Box<Expr>, Box<Expr>),
    Shr(NumKind, Box<Expr>, Box<Expr>),
    Pow(NumKind, Box<Expr>, Box<Expr>),
    /// Unary negation. `Int` only; every other kind is `Error::UnsupportedKind`.
    Neg(NumKind, Box<Expr>),
```

- [ ] **Step 4: Add the grammar**

In `rust/prod-ir/src/parser.rs`, add above `parse_paren_expr`:

```rust
/// `Nat | Int | U8 | U16 | U32 | U64` — the numeric kind tag on an
/// arithmetic node. No prefix collisions among these, so no delimiter guard
/// is needed (unlike `le`, which prefix-matches `let`).
fn parse_num_kind(input: &str) -> IResult<&str, NumKind> {
    ws(alt((
        value(NumKind::Nat, tag("Nat")),
        value(NumKind::Int, tag("Int")),
        value(NumKind::U8, tag("U8")),
        value(NumKind::U16, tag("U16")),
        value(NumKind::U32, tag("U32")),
        value(NumKind::U64, tag("U64")),
    )))(input)
}
```

Rewrite each arithmetic arm to take the kind. For example, `add` becomes:

```rust
                map(
                    tuple((tag("add"), parse_num_kind, ws(parse_expr), ws(parse_expr))),
                    |(_, k, a, b)| Expr::Add(k, Box::new(a), Box::new(b)),
                ),
```

Do the same for `sub`, `mul`, `div`, `mod`, `shl`, `shr`, `pow`. Add `neg`:

```rust
                map(
                    tuple((tag("neg"), parse_num_kind, ws(parse_expr))),
                    |(_, k, a)| Expr::Neg(k, Box::new(a)),
                ),
```

Leave `eq`, `lt`, `le`, `gt` untouched. Update the grammar comment at the top of the file to show the kind tag, and add `NumKind` to the `use super::{...}` list.

- [ ] **Step 5: Make codegen kind-aware without changing Nat behaviour**

In `rust/prod-codegen/src/lib.rs`, thread the kind through the helpers. Replace `checked_binop`'s hard-coded `u64`:

```rust
    /// `checked_add`/`checked_mul`: report overflow instead of panicking.
    ///
    /// The `as` cast pins the receiver's type: method calls on an inferred
    /// `{integer}` (a let-bound literal, e.g. LCNF's `let _x := 1`) fail
    /// method resolution (E0689). It is a no-op when the receiver already has
    /// the kind's type.
    fn checked_binop(
        &self,
        kind: NumKind,
        a: &'m Expr,
        b: &'m Expr,
        method: &str,
        error: &str,
    ) -> Result<String, Error> {
        Ok(format!(
            "(({}) as {}).{}({}).ok_or(crate::ComputeError::{})?",
            self.value(a)?,
            kind.rust_type(),
            method,
            self.value(b)?,
            error
        ))
    }
```

Do the same for `checked_exponent_op` (replace its `as u64`) and `total_binop` (which needs no cast — it renders operators, not method calls — but takes the kind for symmetry and for Task 3's Euclidean branch).

Update the arithmetic arms in `render_value_leaf` to pass `*k` through. Rendering for `NumKind::Nat` must be byte-identical to today.

Every other kind is unreachable at this point — Lean only whitelists `Nat` operators until Task 3 — so route them through the same helpers for now rather than inventing a placeholder rendering. Concretely: a non-`Nat` kind reaching `checked_binop` produces `as i64` / `as u8` and a checked method, which happens to be right for `Int` and wrong for sized integers. That is acceptable *only* because nothing can emit those nodes yet, and Tasks 3 and 4 replace the arms before anything can. Do not add a `_ => unimplemented!()`; an unreachable-but-coherent rendering beats a panic path in a crate that forbids them.

Add:

```rust
            Expr::Neg(k, _) => Err(Error::UnsupportedKind(alloc::format!(
                "unary negation is not supported for {:?}",
                k
            ))),
```

Add the error variant, its `Display` arm, and its `REJECTIONS` row (the exhaustiveness test will force both):

```rust
    /// An operation that has no rendering for the numeric kind it was applied
    /// to — for example a shift on `Int`, or negation on an unsigned kind.
    UnsupportedKind(String),
```

```rust
    (
        "UnsupportedKind",
        "an operation with no rendering for the numeric kind it was applied to, such as a shift on Int or negation on an unsigned kind",
    ),
```

Make `is_fallible` kind-aware. For this task only `Nat` reaches it, but write the full rule now so Tasks 3 and 4 do not have to revisit it:

```rust
/// Does this operation report failure? Kind-dependent: `Nat` and `Int` are
/// checked, sized integers wrap and are total, and `Nat` subtraction
/// saturates rather than failing.
fn op_is_fallible(expr: &Expr) -> bool {
    use prod_ir::NumKind::{Int, Nat};
    match expr {
        Expr::Add(k, ..) | Expr::Mul(k, ..) | Expr::Pow(k, ..) => matches!(k, Nat | Int),
        Expr::Sub(k, ..) | Expr::Div(k, ..) | Expr::Mod(k, ..) => *k == Int,
        Expr::Neg(k, _) => *k == Int,
        Expr::Shl(k, ..) => *k == Nat,
        _ => false,
    }
}
```

and call it from `is_fallible` in place of the current variant list:

```rust
    let here = op_is_fallible(expr)
        || matches!(
            expr,
            Expr::Call(name, _) if matches!(
                shapes.get(name.as_str()),
                Some(Shape::Fallible) | Some(Shape::Buffer)
            )
        );
```

Add `Expr::Neg(_, e) => out.push(e)` to `children()`.

- [ ] **Step 6: Update every fixture, and confirm Nat output is unchanged**

Every `(add a b)` in `rust/prod-codegen/src/tests.rs` and in `rust/prod-codegen-compile-tests/fixtures/representative.ir` becomes `(add Nat a b)`. The **expected output strings must not change** — that is the check that this task is behaviour-preserving. If an expected string needs editing, stop and find out why.

Run: `cd rust && cargo test --workspace`

- [ ] **Step 7: Emit the kind from Lean**

In `lean/Prod/Lower.lean`, replace `natOpNames`/`opWhitelist`. Keep the single-source property — `subsetJson` reads the same list:

```lean
/-- (Lean constant, IR operator, IR numeric kind). Single source of truth for
    the lowerer and for the published contract (`subsetJson` in `Prod.Emit`),
    so the two cannot list different operators.

    Sized-integer rows are generated rather than typed out: every `UIntN`
    shares the same operation names, so listing them by hand would be four
    near-identical blocks that can drift. -/
def natOpRows : List (Name × String × String) :=
  [ (`Nat.add, "add", "Nat"), (`Nat.sub, "sub", "Nat"), (`Nat.mul, "mul", "Nat"),
    (`Nat.div, "div", "Nat"), (`Nat.mod, "mod", "Nat"),
    (`Nat.shiftLeft, "shl", "Nat"), (`Nat.shiftRight, "shr", "Nat"),
    (`Nat.pow, "pow", "Nat") ]

def numOpNames : List (Name × String × String) := natOpRows

/-- `.const` operator whitelist: Lean constant → (IR operator, IR kind). -/
def opWhitelist (n : Name) : Option (String × String) :=
  (numOpNames.find? (fun p => p.1 == n)).map (fun p => (p.2.1, p.2.2))
```

In `lowerLetValue`'s `.const` case, the whitelist branch must emit the kind:

```lean
    match opWhitelist declName with
    | some (op, kind) =>
      if args'.size == 2 then
        return s!"({op} {kind} {args'[0]!} {args'[1]!})"
      modify fun st => { st with externs := st.externs.push s!"{declName} (unusual application)" }
      return s!"(extern \"{declName}\"{spaced args'})"
```

`knownOpOf`/`natDictOp`/`natHDictOp` also produce operator strings for the dictionary-unfolding path. Give each the matching kind — every one of them is a `Nat` dictionary, so they all emit `"Nat"`. Follow the compiler: change the return types and fix what it names.

In `lean/Prod/Emit.lean`, `subsetJson`'s operator list becomes `numOpNames.map fun r => toString r.1`.

- [ ] **Step 8: Rebuild, re-export, review the golden diff**

Run:
```bash
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
```

Review `git diff lean/Conformance/golden.ir`. Every arithmetic node gains ` Nat` and nothing else changes. A structural change means the emitter is wrong.

- [ ] **Step 9: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`, then from `rust/`: `cargo clippy --all-targets -- -D warnings`, `cargo fmt --all -- --check`, and the wasm32 build.

```bash
git add -A
git commit -m "Arithmetic nodes carry an explicit numeric kind

(add a b) meant Nat implicitly, because Nat was the only kind there
was. Int and sized integers have genuinely different contracts — Int
division is Euclidean, sized integers wrap — so one untagged node
cannot mean three renderings, and inferring the kind in codegen would
recreate the derive-it-twice pattern that produced silently swapped
struct fields earlier in this project.

Atomic by necessity: the grammar change breaks every existing
arithmetic node, so the IR, codegen, the emitter and the goldens move
together. No behaviour changes — every expected-output string in the
codegen tests is untouched, which is the check that this is a pure
retag.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: `Int` arithmetic

**Files:**
- Modify: `rust/prod-core/src/error.rs`
- Modify: `rust/prod-codegen/src/lib.rs`, `rust/prod-codegen/src/tests.rs`
- Modify: `lean/Prod/Lower.lean`
- Modify: `lean/Conformance.lean`, `lean/Conformance/golden.ir` (regenerated)
- Modify: `rust/prod-codegen-compile-tests/tests/smoke.rs`

**Interfaces:**
- Consumes: `NumKind`, `op_is_fallible`, kind-aware helpers from Task 2.
- Produces: `ComputeError::{SubOverflow, DivOverflow, NegOverflow}`; `Int` rows in `numOpNames` and `deciderNames`.

- [ ] **Step 1: Confirm the Int decider constants from Lean's source**

Do not guess these. Run:

```bash
L=/nix/store/jpw7rsgz1g25m00n4d4zjb8nlbplv8k0-lean4-4.30.0/src/lean
grep -rn "instDecidableEqInt\|Int.decLt\|Int.decLe\|decidable.*Int" $L/Init/Data/Int/ | head -20
```

Record the exact constant names in your report. If the store path differs, get it with `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command sh -c 'dirname $(dirname $(which lean))'`.

- [ ] **Step 2: Write the failing codegen tests**

Add to `rust/prod-codegen/src/tests.rs`:

```rust
#[test]
fn test_int_division_is_euclidean_not_truncating() {
    // Lean's Div Int / Mod Int instances use Int.ediv / Int.emod — its own
    // docs say so, "for compatibility with SMT-LIB". Rust's / and % truncate.
    // They differ for every negative operand: Lean gives (-12) % 7 = 2, Rust
    // gives -5. Rendering / and % here would be silently wrong, and every test
    // with non-negative inputs would still pass.
    let ir = r#"(module M (def f ((a Int) (b Int)) Int (div Int a b)))"#;
    let out = generate(ir);
    assert!(out.contains("checked_div_euclid"), "got: {}", out);
    assert!(!out.contains("(a) / (b)"), "must not render truncating division");
    // Int.ediv is total on a zero divisor (Init/Data/Int/DivMod/Basic.lean:76
    // is explicit: `| -[_+1], 0 => 0`), so the zero-guard stays.
    assert!(out.contains("if (b) == 0 { 0 }"), "got: {}", out);
}

#[test]
fn test_int_modulo_is_euclidean() {
    let ir = r#"(module M (def f ((a Int) (b Int)) Int (mod Int a b)))"#;
    assert!(generate(ir).contains("checked_rem_euclid"));
}

#[test]
fn test_int_sub_is_checked_unlike_nat() {
    // Nat subtraction truncates at zero and cannot fail; Int subtraction can
    // overflow i64, because Lean's Int is unbounded and i64 is not.
    let nat = generate(r#"(module M (def f ((a Nat) (b Nat)) Nat (sub Nat a b)))"#);
    assert!(nat.contains("saturating_sub"));
    assert!(nat.contains("-> u64 {"), "Nat sub is infallible");

    let int = generate(r#"(module M (def f ((a Int) (b Int)) Int (sub Int a b)))"#);
    assert!(int.contains("checked_sub(b).ok_or(crate::ComputeError::SubOverflow)?"));
    assert!(int.contains("-> Result<i64, crate::ComputeError>"));
}

#[test]
fn test_int_neg_is_checked() {
    let ir = r#"(module M (def f ((a Int)) Int (neg Int a)))"#;
    let out = generate(ir);
    assert!(out.contains("checked_neg().ok_or(crate::ComputeError::NegOverflow)?"));
}

#[test]
fn test_neg_on_a_non_int_kind_is_rejected() {
    let ir = r#"(module M (def f ((a Nat)) Nat (neg Nat a)))"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedKind(_)));
}

#[test]
fn test_int_shifts_are_rejected() {
    // Deliberate non-goal; rejected precisely rather than rendered.
    let ir = r#"(module M (def f ((a Int) (b Int)) Int (shl Int a b)))"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedKind(_)));
}
```

- [ ] **Step 3: Run to verify they fail**

Run: `cd rust && cargo test -p prod-codegen`
Expected: FAIL — no Euclidean rendering, no new error variants.

- [ ] **Step 4: Add the error variants**

In `rust/prod-core/src/error.rs`, add to `ComputeError` and to `as_str`:

```rust
    /// `a - b` on `Int` underflowed `i64`. `Nat` subtraction saturates and
    /// cannot reach this.
    SubOverflow,
    /// `a / b` on `Int` overflowed `i64` — only `i64::MIN / -1`.
    DivOverflow,
    /// `-a` on `Int` overflowed `i64` — only `-i64::MIN`.
    NegOverflow,
```

```rust
            ComputeError::SubOverflow => "Int subtraction overflowed i64",
            ComputeError::DivOverflow => "Int division overflowed i64",
            ComputeError::NegOverflow => "Int negation overflowed i64",
```

Extend the existing distinctness test in that file's `tests` module with the three new variants.

- [ ] **Step 5: Render Int arithmetic**

In `rust/prod-codegen/src/lib.rs`, switch each arithmetic arm on the kind. `Div` and `Mod` need a Euclidean branch:

```rust
    /// Lean `Nat` and sized-integer division/modulo are total: `x / 0 = 0`.
    /// `Int` is total too (`Int.ediv _ 0 = 0`) but Euclidean, and can overflow
    /// at `i64::MIN / -1` — so it keeps the zero-guard and adds a check.
    fn div_or_mod(
        &self,
        kind: NumKind,
        a: &'m Expr,
        b: &'m Expr,
        op: &str,
        euclid_method: &str,
        error: &str,
    ) -> Result<String, Error> {
        let (a, b) = (self.value(a)?, self.value(b)?);
        if kind == NumKind::Int {
            return Ok(format!(
                "if ({}) == 0 {{ 0 }} else {{ (({}) as i64).{}({}).ok_or(crate::ComputeError::{})? }}",
                b, a, euclid_method, b, error
            ));
        }
        Ok(format!(
            "if ({}) == 0 {{ 0 }} else {{ ({}) {} ({}) }}",
            b, a, op, b
        ))
    }
```

Wire the arms:

```rust
            Expr::Div(k, a, b) => self.div_or_mod(*k, a, b, "/", "checked_div_euclid", "DivOverflow"),
            Expr::Mod(k, a, b) => self.div_or_mod(*k, a, b, "%", "checked_rem_euclid", "DivOverflow"),
            Expr::Sub(k, a, b) => match k {
                NumKind::Nat => Ok(format!(
                    "(({}) as u64).saturating_sub({})",
                    self.value(a)?,
                    self.value(b)?
                )),
                NumKind::Int => self.checked_binop(*k, a, b, "checked_sub", "SubOverflow"),
                _ => self.wrapping_binop(*k, a, b, "wrapping_sub"),
            },
            Expr::Neg(k, a) => {
                if *k == NumKind::Int {
                    Ok(format!(
                        "(({}) as i64).checked_neg().ok_or(crate::ComputeError::NegOverflow)?",
                        self.value(a)?
                    ))
                } else {
                    Err(Error::UnsupportedKind(format!(
                        "unary negation is only supported for Int, not {:?}",
                        k
                    )))
                }
            }
            Expr::Shl(k, a, b) => match k {
                NumKind::Nat => self.checked_exponent_op(
                    *k, a, b, "checked_shl", "ShiftExponentTooLarge", "ShiftOverflow",
                ),
                NumKind::Int => Err(Error::UnsupportedKind(String::from(
                    "shifts are not supported for Int",
                ))),
                _ => self.total_shift(*k, a, b, "checked_shl"),
            },
            Expr::Shr(k, a, b) => match k {
                NumKind::Int => Err(Error::UnsupportedKind(String::from(
                    "shifts are not supported for Int",
                ))),
                _ => self.total_shift(*k, a, b, "checked_shr"),
            },
```

`wrapping_binop` and `total_shift` are Task 4's to exercise but are defined here so the match is exhaustive now:

```rust
    /// Sized-integer arithmetic wraps — that is Lean's semantics
    /// (`UInt8.add a b = ⟨a.toBitVec + b.toBitVec⟩`), not a failure.
    fn wrapping_binop(
        &self,
        kind: NumKind,
        a: &'m Expr,
        b: &'m Expr,
        method: &str,
    ) -> Result<String, Error> {
        Ok(format!(
            "(({}) as {}).{}({})",
            self.value(a)?,
            kind.rust_type(),
            method,
            self.value(b)?
        ))
    }

    /// Shifts on `Nat` (right) and on sized integers (both directions) are
    /// total: shifting by at least the width yields 0.
    ///
    /// CORRECTED AFTER THE FACT — this paragraph originally claimed
    /// `wrapping_shl` was wrong for sized kinds "because it masks the shift
    /// amount, whereas Lean's BitVec shift gives 0". That is true of `BitVec`
    /// shifted by a `Nat`, and FALSE for `UIntN`:
    /// `Init/Data/UInt/Basic.lean:126` defines
    /// `UInt8.shiftLeft a b = ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩`,
    /// which masks mod width first — so `(1 : UInt8) <<< 8 = 1` and
    /// `wrapping_shl` IS correct there. The design said so; this plan
    /// overrode it wrongly. `total_shift` is for `Nat` ONLY, where the type is
    /// unbounded, there is no width to mask by, and shifting past 64 really
    /// does give 0. Sized kinds use `wrapping_shl`/`wrapping_shr` (Task 4).
    fn total_shift(
        &self,
        kind: NumKind,
        a: &'m Expr,
        b: &'m Expr,
        method: &str,
    ) -> Result<String, Error> {
        Ok(format!(
            "(({}) as {}).{}(u32::try_from({}).unwrap_or(u32::MAX)).unwrap_or(0)",
            self.value(a)?,
            kind.rust_type(),
            method,
            self.value(b)?
        ))
    }
```

Keep the existing `Expr::Shr(Nat, ..)` rendering byte-identical by routing it through `total_shift` and confirming the string matches the current test expectation; adjust `total_shift` rather than the test if it does not.

- [ ] **Step 6: Whitelist the Int operators and deciders**

In `lean/Prod/Lower.lean`, add the rows using the constant names confirmed in Step 1:

```lean
def intOpRows : List (Name × String × String) :=
  [ (`Int.add, "add", "Int"), (`Int.sub, "sub", "Int"), (`Int.mul, "mul", "Int"),
    (`Int.ediv, "div", "Int"), (`Int.emod, "mod", "Int"),
    (`Int.neg, "neg", "Int"), (`Int.pow, "pow", "Int") ]

def numOpNames : List (Name × String × String) := natOpRows ++ intOpRows
```

`Int.neg` is unary, so `lowerLetValue`'s whitelist branch must handle arity 1 as well as 2:

```lean
    match opWhitelist declName with
    | some (op, kind) =>
      if op == "neg" && args'.size == 1 then
        return s!"(neg {kind} {args'[0]!})"
      if args'.size == 2 then
        return s!"({op} {kind} {args'[0]!} {args'[1]!})"
      modify fun st => { st with externs := st.externs.push s!"{declName} (unusual application)" }
      return s!"(extern \"{declName}\"{spaced args'})"
```

Add the Int deciders to `deciderNames`, using the Step 1 names.

- [ ] **Step 7: Add conformance cases, with negative operands**

In `lean/Conformance.lean`. These are the load-bearing ones — a suite of non-negative operands passes identically under truncating and Euclidean division:

```lean
-- Int. The negative-operand cases are the point: Lean's / and % are Euclidean
-- (Int.ediv / Int.emod), Rust's truncate, and they differ only when an operand
-- is negative. Lean's own doctest gives (-12) % 7 = 2; Rust's % gives -5.
@[prod] def c_int_add (a b : Int) : Int := a + b
@[prod] def c_int_sub (a b : Int) : Int := a - b
@[prod] def c_int_mul (a b : Int) : Int := a * b
@[prod] def c_int_ediv (a b : Int) : Int := a / b
@[prod] def c_int_emod (a b : Int) : Int := a % b
@[prod] def c_int_neg (a : Int) : Int := -a
```

Add goldens in `lean/Prod/Emit.lean`'s `goldenEntries` so the values come from Lean rather than from anyone's expectation:

```lean
  out := out.push { name := "golden_int_ediv_neg_12_7", ret := "Int",
                    value := toString (Conformance.c_int_ediv (-12) 7) }
  out := out.push { name := "golden_int_emod_neg_12_7", ret := "Int",
                    value := toString (Conformance.c_int_emod (-12) 7) }
```

This needs `import Conformance` in `Emit.lean`, which is already there.

- [ ] **Step 8: Assert the values in the compile-tests crate**

In `rust/prod-codegen-compile-tests/tests/smoke.rs`, inside `conformance_golden_code_runs`:

```rust
    // Euclidean, not truncating. Rust's own `/` and `%` would give -1 and -5.
    assert_eq!(c_int_ediv(-12, 7)?, -2);
    assert_eq!(c_int_emod(-12, 7)?, 2);
    assert_eq!(c_int_sub(i64::MIN, 1), Err(ComputeError::SubOverflow));
    assert_eq!(c_int_neg(i64::MIN), Err(ComputeError::NegOverflow));
    assert_eq!(c_int_ediv(i64::MIN, -1), Err(ComputeError::DivOverflow));
    assert_eq!(c_int_ediv(5, 0)?, 0); // total, like Nat
```

- [ ] **Step 9: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`, then clippy, fmt and the wasm32 build from `rust/`.

```bash
git add -A
git commit -m "Int arithmetic, faithfully Euclidean

Lean's Div Int and Mod Int instances use Int.ediv and Int.emod — its
own source says so, for SMT-LIB compatibility — and its doctest gives
(-12) % 7 = 2 where Rust's % gives -5. Rendering / and % would have
been silently wrong for every negative operand, and a suite of
non-negative inputs would never have noticed, which is why the
conformance cases and their Lean-computed goldens use negative operands
specifically.

Int division is total on a zero divisor like Nat, so it keeps the
zero-guard and adds checked_div_euclid for i64::MIN / -1. Subtraction
and negation are checked because Lean's Int is unbounded and i64 is
not. Shifts on Int are a deliberate non-goal and are rejected.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: Sized integers

**Files:**
- Modify: `rust/prod-codegen/src/tests.rs`
- Modify: `lean/Prod/Lower.lean`
- Modify: `lean/Conformance.lean`, `lean/Conformance/golden.ir` (regenerated)
- Modify: `rust/prod-codegen-compile-tests/tests/smoke.rs`

**Interfaces:**
- Consumes: `wrapping_binop`, `total_shift`, `NumKind::{U8,U16,U32,U64}` from Tasks 2–3.
- Produces: sized rows in `numOpNames` and `deciderNames`; a `Type::UInt(NumKind)` IR type.

- [ ] **Step 1: Confirm the sized-int decider constants**

As in Task 3 Step 1, but for `UInt8`…`UInt64`:

```bash
L=/nix/store/jpw7rsgz1g25m00n4d4zjb8nlbplv8k0-lean4-4.30.0/src/lean
grep -rn "instDecidableEqUInt8\|UInt8.decLt\|UInt8.decLe" $L/Init/Data/UInt/ | head -10
```

Record what you find.

- [ ] **Step 2: Write the failing tests**

```rust
#[test]
fn test_sized_arithmetic_wraps_and_is_infallible() {
    // Lean's UInt8.add is BitVec addition — wrapping IS the semantics, not a
    // failure. So sized definitions keep a plain return type.
    let ir = r#"(module M (def f ((a U8) (b U8)) U8 (add U8 a b)))"#;
    let out = generate(ir);
    assert!(out.contains("(a) as u8).wrapping_add(b)"), "got: {}", out);
    assert!(out.contains("-> u8 {"), "sized arithmetic must be infallible");
    assert!(!out.contains("ComputeError"));
}

// CORRECTED AFTER THE FACT — this test was planned as
// `test_sized_shift_truncates_rather_than_masking`, asserting `checked_shl` +
// `unwrap_or(0)` and forbidding `wrapping_shl`. That is the inverted premise
// (see the `total_shift` correction in Task 3): `UInt8.shiftLeft a b =
// ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩` (`Init/Data/UInt/Basic.lean:126`)
// masks mod the width, so `(1 : UInt8) <<< 8 = 1` and the planned assertions
// would have pinned the wrong rendering. `Nat` is the one that truncates,
// because it is unbounded and has no width to mask by. Shown here as shipped.
#[test]
fn test_sized_shift_masks_the_amount_mod_width() {
    // wrapping_shl is RIGHT: it masks the amount, so 1u8 << 8 == 1, which is
    // exactly Lean's answer. checked_shl(..).unwrap_or(0) would give 0.
    let ir = r#"(module M (def f ((a U8) (b U8)) U8 (shl U8 a b)))"#;
    let out = generate(ir);
    assert!(out.contains("wrapping_shl"), "got: {}", out);
    assert!(!out.contains("checked_shl"), "checked_shl truncates to 0");
    assert!(!out.contains("unwrap_or(0)"));
}

#[test]
fn test_sized_division_is_total() {
    let ir = r#"(module M (def f ((a U8) (b U8)) U8 (div U8 a b)))"#;
    let out = generate(ir);
    assert!(out.contains("if (b) == 0 { 0 }"));
    assert!(!out.contains("ComputeError"));
}
```

- [ ] **Step 3: Run to verify they fail**

Run: `cd rust && cargo test -p prod-codegen`
Expected: FAIL — `U8` is not a parameter type yet.

- [ ] **Step 4: Add the sized types to the IR type grammar**

`prod-ir`'s `Type` has `Nat`, `Int`, `Bool`, `Named`, `Option`, `Vec`, `List`, `Tuple`, `Opaque`. Add:

```rust
    /// A Lean sized integer (`UInt8`…`UInt64`), rendered as the corresponding
    /// Rust unsigned type. Arithmetic on these wraps and is infallible.
    UInt(NumKind),
```

Parse it with `parse_num_kind` restricted to the sized kinds, and render it in `type_to_rust` as `kind.rust_type()`. Reject `Type::UInt(NumKind::Nat)` and `Type::UInt(NumKind::Int)` at parse time by using a dedicated `parse_sized_kind` that only accepts `U8`/`U16`/`U32`/`U64` — an unrepresentable state is better than a checked one.

- [ ] **Step 5: Wire the arithmetic arms**

Route the remaining `_ =>` branches added in Task 3 — `Add`, `Mul`, `Pow` — through `wrapping_binop` with `wrapping_add`, `wrapping_mul`, `wrapping_pow`. Note `wrapping_pow` takes a `u32` exponent, so it needs the `u32::try_from(..).unwrap_or(u32::MAX)` narrowing that `total_shift` uses; write it as its own small helper rather than reusing `wrapping_binop`.

- [ ] **Step 6: Whitelist the sized operators**

In `lean/Prod/Lower.lean`, generate the rows rather than typing four near-identical blocks:

```lean
/-- Operation suffixes shared by every sized integer type. -/
def sizedOpSuffixes : List (Name × String) :=
  [ (`add, "add"), (`sub, "sub"), (`mul, "mul"), (`div, "div"), (`mod, "mod"),
    (`shiftLeft, "shl"), (`shiftRight, "shr") ]

/-- Lean sized-integer types and their IR kind tags. -/
def sizedKinds : List (Name × String) :=
  [ (`UInt8, "U8"), (`UInt16, "U16"), (`UInt32, "U32"), (`UInt64, "U64") ]

def sizedOpRows : List (Name × String × String) :=
  sizedKinds.flatMap fun (ty, kind) =>
    sizedOpSuffixes.map fun (suffix, ir) => (ty ++ suffix, ir, kind)

def numOpNames : List (Name × String × String) := natOpRows ++ intOpRows ++ sizedOpRows
```

Add the sized types to `lowerType`, mapping `UInt8`…`UInt64` to `U8`…`U64`, and the sized deciders to `deciderNames` using the Step 1 names.

- [ ] **Step 7: Conformance cases that actually wrap**

In `lean/Conformance.lean`. A case that stays in range proves nothing:

```lean
-- Sized integers. The boundary cases are the point: wrapping is Lean's
-- semantics (BitVec arithmetic), so a case that stays in range would pass
-- under a checked rendering too.
@[prod] def c_u8_add (a b : UInt8) : UInt8 := a + b
@[prod] def c_u8_sub (a b : UInt8) : UInt8 := a - b
@[prod] def c_u8_mul (a b : UInt8) : UInt8 := a * b
@[prod] def c_u8_div (a b : UInt8) : UInt8 := a / b
@[prod] def c_u8_shl (a b : UInt8) : UInt8 := a <<< b
```

Add Lean-computed goldens for `c_u8_add 255 1` (wraps to 0) and `c_u8_shl 1 8`
in `goldenEntries`.

CORRECTED AFTER THE FACT — this line originally read "`c_u8_shl 1 8` (0, not
1)". Lean's answer is **1**, not 0: the shift amount masks mod the width
(`8 % 8 = 0`, so `1 <<< 0 = 1`). Same inverted premise as the Task 4 Step 2
test above. The golden is computed by calling the compiled Lean definition, so
`goldenEntries` produced the right value regardless of what this line said —
which is the whole point of computing goldens instead of typing them.

- [ ] **Step 8: Assert in the compile-tests crate**

```rust
    // Wrapping is the semantics, not a failure — and no Result in sight.
    assert_eq!(c_u8_add(255, 1), 0);
    assert_eq!(c_u8_mul(16, 16), 0);
    assert_eq!(c_u8_div(5, 0), 0); // total
    // The shift masks rather than truncating: 8 % 8 = 0, so 1 <<< 0 = 1.
    assert_eq!(c_u8_shl(1, 8), 1);
    // ...and compared against Lean's own computed answer, not only this
    // hand-typed one — a hand-typed expectation can be wrong in the same
    // direction as the bug it is meant to catch, which is what happened here.
    assert_eq!(c_u8_shl(1, 8), golden_u8_shl_1_8());
```

CORRECTED AFTER THE FACT — this step originally asserted
`assert_eq!(c_u8_shl(1, 8), 0)`, the inverted premise again (Task 4 Step 2 and
Step 7 above). That assertion shipped, disagreeing with the Lean-computed
`golden_u8_shl_1_8 = 1` sitting in the same repository, and nothing compared
the two — so the build stayed green. The golden comparison is now part of this
step, and `prod-codegen-compile-tests/tests/goldens_consumed.rs` fails the
build if any golden has no consumer at all.

- [ ] **Step 9: Full gates and commit**

```bash
git add -A
git commit -m "Sized integers, wrapping and infallible

Lean's UInt8.add is BitVec addition, so wrapping is the semantics
rather than an overflow — the opposite of the Nat policy, and rendering
these as checked would turn correct Lean programs into spurious Errs.
Division is total on a zero divisor like Nat. Nothing here can fail, so
the fallibility fixpoint leaves sized definitions with plain return
types.

Shifts render wrapping_shl/wrapping_shr. UIntN masks the shift amount
mod width before shifting (Init/Data/UInt/Basic.lean:126), so
(1 : UInt8) <<< 8 = 1, and wrapping_shl — which masks rhs & (bits-1),
identical for power-of-two widths — is exactly right. Nat is different:
unbounded, no width to mask by, so it keeps the truncating rendering.
The conformance case shifts at the width boundary for exactly this
reason, and is asserted against Lean's own computed golden rather than
a hand-written expectation.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 5: Conversions between kinds

**Files:**
- Modify: `rust/prod-ir/src/lib.rs`, `rust/prod-ir/src/parser.rs`
- Modify: `rust/prod-codegen/src/lib.rs`, `rust/prod-codegen/src/tests.rs`
- Modify: `lean/Prod/Lower.lean`
- Modify: `lean/Conformance.lean`, `lean/Conformance/golden.ir` (regenerated)
- Modify: `rust/prod-codegen-compile-tests/tests/smoke.rs`

**Interfaces:**
- Produces: `Expr::Convert(NumKind, NumKind, Box<Expr>)` — from-kind, to-kind, value. Grammar `(convert Nat Int a)`.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn test_nat_to_int_widens() {
    let ir = r#"(module M (def f ((a Nat)) Int (convert Nat Int a)))"#;
    assert!(generate(ir).contains("((a) as i64)"));
}

#[test]
fn test_int_to_nat_clamps_negatives_to_zero() {
    // Lean's Int.toNat clamps: (-5).toNat = 0. `as u64` would wrap to a huge
    // number, which is the whole reason this needs a rendering rather than a
    // cast.
    let ir = r#"(module M (def f ((a Int)) Nat (convert Int Nat a)))"#;
    let out = generate(ir);
    assert!(out.contains("max(0)"), "got: {}", out);
    assert!(!out.contains("(a) as u64)."), "a bare cast would wrap negatives");
}

#[test]
fn test_nat_to_sized_wraps() {
    let ir = r#"(module M (def f ((a Nat)) U8 (convert Nat U8 a)))"#;
    assert!(generate(ir).contains("as u8"));
}

#[test]
fn test_sized_to_nat_widens() {
    let ir = r#"(module M (def f ((a U8)) Nat (convert U8 Nat a)))"#;
    assert!(generate(ir).contains("as u64"));
}

#[test]
fn test_unsupported_conversion_is_rejected() {
    // Cross-width sized conversions are a deliberate non-goal.
    let ir = r#"(module M (def f ((a U8)) U32 (convert U8 U32 a)))"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedKind(_)));
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cd rust && cargo test -p prod-codegen`

- [ ] **Step 3: Add the node and its rendering**

`Expr::Convert(NumKind, NumKind, Box<Expr>)`, grammar `(convert <from> <to> expr)`, a `children()` arm, and:

```rust
            Expr::Convert(from, to, e) => {
                use NumKind::*;
                let v = self.value(e)?;
                match (from, to) {
                    // Nat → Int widens; u64 values above i64::MAX cannot arise
                    // from Lean's Nat under the bounded-u64 policy without
                    // having already overflowed, so this is a plain cast.
                    (Nat, Int) => Ok(format!("(({}) as i64)", v)),
                    // Lean's Int.toNat clamps negatives to 0. A bare cast
                    // would wrap them to enormous values.
                    (Int, Nat) => Ok(format!("(({}).max(0) as u64)", v)),
                    // Lean's Nat.toUIntN truncates, matching BitVec.
                    (Nat, U8) | (Nat, U16) | (Nat, U32) | (Nat, U64) => {
                        Ok(format!("(({}) as {})", v, to.rust_type()))
                    }
                    // UIntN → Nat widens.
                    (U8, Nat) | (U16, Nat) | (U32, Nat) | (U64, Nat) => {
                        Ok(format!("(({}) as u64)", v))
                    }
                    _ => Err(Error::UnsupportedKind(format!(
                        "no conversion from {:?} to {:?}; cross-width sized conversions are a deliberate non-goal",
                        from, to
                    ))),
                }
            }
```

- [ ] **Step 4: Whitelist the conversions in Lean**

`Int.ofNat`, `Int.toNat`, `UInt8.toNat`…`UInt64.toNat`, `Nat.toUInt8`…`Nat.toUInt64`. These are unary, so extend `lowerLetValue`'s whitelist branch with a conversion table separate from `numOpNames` — a conversion carries two kinds, not one:

```lean
/-- (Lean constant, from-kind, to-kind). Unary; emitted as `(convert F T x)`. -/
def conversionNames : List (Name × String × String) :=
  [ (`Int.ofNat, "Nat", "Int"), (`Int.toNat, "Int", "Nat") ]
  ++ sizedKinds.flatMap fun (ty, kind) =>
       [ (ty ++ `toNat, kind, "Nat"), (`Nat ++ ("to" ++ ty.toString).toName, "Nat", kind) ]
```

Verify the `Nat.toUInt8` spelling against Lean's source before relying on the constructed name; if it differs, list the four rows literally rather than constructing them.

- [ ] **Step 5: Conformance cases and goldens**

```lean
-- Conversions. Int.toNat clamping is the one with a wrong-by-default
-- rendering: (-5).toNat is 0 in Lean, and a bare `as u64` cast would give
-- 18446744073709551611.
@[prod] def c_int_of_nat (a : Nat) : Int := Int.ofNat a
@[prod] def c_int_to_nat (a : Int) : Nat := a.toNat
@[prod] def c_nat_to_u8 (a : Nat) : UInt8 := a.toUInt8
@[prod] def c_u8_to_nat (a : UInt8) : Nat := a.toNat
```

Golden for `c_int_to_nat (-5)` — it must be `0`.

- [ ] **Step 6: Assert in the compile-tests crate**

```rust
    assert_eq!(c_int_to_nat(-5), 0); // clamps, does not wrap
    assert_eq!(c_int_to_nat(5), 5);
    assert_eq!(c_nat_to_u8(300), 44); // truncates: 300 - 256
    assert_eq!(c_u8_to_nat(255), 255);
```

- [ ] **Step 7: Full gates and commit**

```bash
git add -A
git commit -m "Conversions between numeric kinds

The lossless and total set: Nat<->Int, UIntN->Nat, Nat->UIntN. Without
these, Int arithmetic ships largely unreachable, since nearly all Int
code starts by getting a Nat into an Int.

Int.toNat is the one with a wrong-by-default rendering: Lean clamps
negatives to 0, while a bare `as u64` cast wraps -5 to
18446744073709551611. Cross-width sized conversions are a deliberate
non-goal and are rejected.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

## Final verification

- [ ] **Run every gate from a clean tree**

```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just lint
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just fmt-check
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just wasm-check
git diff --check
git status --short
```

Expected: all green, `git status` clean. A dirty `lean/Conformance/golden.ir` or `specs/lean-for-production.md` means an unreviewed change slipped through.

- [ ] **Read the regenerated contract**

`specs/lean-for-production.md` must now list the `Int` and sized-integer operators, the conversions, and the deciders per kind — and the S1-era `Int` qualifier ("no Int operators are whitelisted") must be gone, because it is no longer true.

- [ ] **Update `AGENTS.md`**

Record: arithmetic nodes carry a `NumKind`; the three policies and why they differ; that `Int` division is Euclidean with the source citation; that sized shifts use `checked_shl(..).unwrap_or(0)` rather than `wrapping_shl` and why.

- [ ] **Mark Phase A done in the design doc**, and note that Phase B (invariant-carrying types and `Fin`) is now unblocked and should be planned against the arithmetic layer as it actually shipped.
