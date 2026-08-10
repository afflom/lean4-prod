# S2 Phase B1 — invariant-carrying types, Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Re-check at the crate boundary the invariants Lean erases — a structure whose `Prop` fields are all lowerable gets `pub(crate)` fields and a generated checked constructor.

**Architecture:** The exporter lowers a `Prop` field's *proposition* (not its proof) to a boolean IR expression over the structure's own fields, and carries it on the type declaration. Codegen renders that as a `new` returning `Result<Self, ComputeError>`. Generated code keeps constructing via struct literal — Lean already supplied a proof, so re-checking internally would turn proved-total functions fallible.

**Tech Stack:** Lean 4.30.0 (pinned, no mathlib), Rust 1.95, `nom` 7 parser, `prod-macros` proc macro, `just` + nix dev shell.

**Design doc:** `specs/designs/2026-08-09-s2-scalar-completeness-and-invariants.md`. This plan is **Phase B1 only** — the design's migration steps 6 and 8. **Step 7 (`Fin` literal specialisation) is Phase B2**, planned separately against what B1 ships, because `Fin` is a consumer of this machinery rather than a peer of it.

## Global Constraints

- NO mathlib. Pure Lean 4 core/Init. NO `sorry`, NO `axiom`.
- Generated artifacts are never hand-edited. `rust/prod-core/kernel.ir`, `goldens.ir`, `roots.json`, `coverage.md`, `subset.json` are gitignored — do NOT `git add` them, `git add` errors on an explicitly listed ignored path. `lean/Conformance/golden.ir`, `lean/Conformance/golden-rejected.ir` and `specs/lean-for-production.md` are committed but regenerated only by running the tooling.
- Generated code must not panic on caller-controlled input and must not allocate.
- `prod-ir` and `prod-codegen` stay `#![no_std]` and wasm32-clean. No `std`.
- `unsafe_code = "forbid"` workspace-wide except `prod-wasm` and `prod-alloc-counter`. `prod-core` additionally denies `clippy::{unwrap_used, expect_used, panic}` — **in its test targets too**, so migrated tests must propagate with `?`, never `.unwrap()` or `.expect()`.
- lean/lake are NOT on PATH. Always: `cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build`. Lean builds take MINUTES — use 600000ms timeouts.
- Gates before every commit: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod` from the repo root, plus from `rust/`: `cargo clippy --all-targets -- -D warnings`, `cargo fmt --all -- --check`, and `RUSTC=$(rustup which --toolchain stable rustc) rustup run stable cargo build -p prod-ir -p prod-codegen -p prod-wasm --target wasm32-unknown-unknown`.
- Commit at the end of every task. Do NOT `git push`.
- **This codebase compiles and runs its generated output.** `rust/prod-codegen-compile-tests` expands `prod_defs!` over the conformance golden AND `goldens.ir`, and `tests/goldens_consumed.rs` fails the build if a Lean-computed golden has no consumer. Do not weaken either to make something pass.

## File structure

| File | Responsibility in this plan |
|---|---|
| `lean/Prod/Lower.lean` | `builtinTypes` single source; `lowerProp`; invariant on the type declaration |
| `lean/Prod/Emit.lean` | `collectTypeDecls` and `subsetJson` consume `builtinTypes` |
| `rust/prod-ir/src/lib.rs` | `TypeDecl.invariant`, `Expr::{And,Or,Not}` |
| `rust/prod-ir/src/parser.rs` | `(invariant <expr>)`, `(and a b)`, `(or a b)`, `(not a)` |
| `rust/prod-codegen/src/lib.rs` | `pub(crate)` fields, `new`, accessors, connective rendering |
| `rust/prod-core/src/error.rs` | `InvariantViolated(&'static str)` |
| `rust/prod-core/tests/*.rs`, `rust/prod-codegen-compile-tests/tests/smoke.rs` | migrated construction sites |

---

### Task 1: One source of truth for builtin type names

Folded in from the Phase A follow-up list. `Fin` (Phase B2) adds a type that all three sites must know about, so this is the last cheap moment. Flagged three times across two milestones.

**Files:**
- Modify: `lean/Prod/Lower.lean`, `lean/Prod/Emit.lean`
- Modify: `specs/lean-for-production.md` (regenerated)

**Interfaces:**
- Produces: `Prod.builtinTypes : List (Name × String)` — (Lean type name, contract annotation); `Prod.isBuiltinType : Name → Bool`.

- [ ] **Step 1: Add the single list**

In `lean/Prod/Lower.lean`, next to `sizedKinds`:

```lean
/-- Types the IR handles natively, paired with their contract annotation.
    Single source of truth for three consumers that previously each carried
    their own copy: `collectTypeDecls`' exclusion test (a builtin must not be
    collected as a user inductive — `UInt8` is a structure over
    `toBitVec : BitVec 8`, and trying to describe that field aborts the
    export), and `subsetJson`'s published Types list.

    `lowerType` deliberately does NOT consume this: it maps each builtin to a
    *different* IR tag, which is a mapping rather than a membership test, and
    collapsing the two would make the list carry two unrelated jobs. -/
def builtinTypes : List (Name × String) :=
  [ (`Nat, "Nat"),
    (`Bool, "Bool"),
    (`Int, "Int (renders as i64; checked add/sub/mul/neg/pow, Euclidean checked div/mod (Int.ediv/Int.emod); shifts are not whitelisted for Int; Nat -> Int is supported, via the constructors Int.ofNat (n renders as (n as i64)) and Int.negSucc (n renders as -(n as i64) - 1) -- these are constructor applications, not conversion calls, so they never appear in the Conversions list below)"),
    (`Prod, "Prod (renders as a Rust tuple)"),
    (`List, "List (parameter: &[a]; return: a caller-owned output buffer)"),
    (`Option, "Option") ]
  ++ sizedKinds.map (fun p =>
       (p.1, s!"{p.1} (renders as {p.2.toLower}; wrapping add/sub/mul; total div/mod (zero divisor gives 0/the dividend, as for Nat); shiftLeft/shiftRight mask the shift amount mod the width rather than truncating to 0 (unlike Nat's shifts) -- none of this can fail; pow is not whitelisted for sized kinds)"))

/-- Is this constant a type the IR handles natively? -/
def isBuiltinType (n : Name) : Bool := builtinTypes.any (fun p => p.1 == n)
```

- [ ] **Step 2: Consume it in `collectTypeDecls`**

In `lean/Prod/Emit.lean`, replace the hand-written exclusion chain (`n != \`\`Nat && n != \`\`Bool && …` plus the `isSized` test) with:

```lean
        if !isBuiltinType n && !wanted.contains n then
          if (env.find? n).isSome then
            wanted := wanted.push n
```

Note this also removes the duplicated `!wanted.contains n` test the old code had twice.

- [ ] **Step 3: Consume it in `subsetJson`**

Replace the hand-written `types` literal with `builtinTypes.map (·.2)`, so a builtin cannot be added without appearing in the published contract. Keep any non-builtin entries (for example the "parameterless, non-recursive, single-constructor structures" line) appended after it.

- [ ] **Step 4: Rebuild, re-export, confirm the contract is unchanged**

Run:
```bash
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
```

`git diff specs/lean-for-production.md` should be **empty or purely cosmetic** — this task moves where the strings live, not what they say. A content change means an annotation was altered in transit; fix it rather than accepting it.

- [ ] **Step 5: Gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`, then clippy, fmt and the wasm32 build from `rust/`.

```bash
git add -A
git commit -m "One source of truth for builtin type names

The set of types the IR handles natively lived in three places: the
exclusion test in collectTypeDecls, the sized-kind test beside it, and
the published Types list. Flagged three times across two milestones,
and Phase B2's Fin would have had to touch all three.

lowerType deliberately still has its own match: it maps each builtin to
a different IR tag, which is a mapping rather than a membership test.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: Spike — what a `Prop` field's proposition actually looks like

Everything downstream lowers that proposition to a boolean expression. Guessing its shape is how this project has repeatedly shipped wrong renderings; two coordinator guesses at Lean constant names were already wrong in Phase A. Establish the shape before writing the lowering.

**Files:**
- Create then DELETE: a scratch Lean file
- Modify: `AGENTS.md` (record the finding)

**Interfaces:**
- Produces: a recorded description of the `Expr` shape for `UorAtlas.Instance.valid`'s type — the head constants for `∧` and `≥`, their arities, and how the proposition refers to earlier fields.

- [ ] **Step 1: Print the proposition**

Create `lean/Scratch.lean` (deleted in Step 4):

```lean
import Lean
import Example
open Lean

/-- Print the raw `Expr` of every constructor field's type for a structure,
    so the invariant lowering is written against what Lean actually produces
    rather than against what it is assumed to produce. -/
def dumpCtorTelescope (structName ctorName : Name) : CoreM Unit := do
  let env ← getEnv
  let some (.ctorInfo cv) := env.find? ctorName | throwError "not a ctor"
  IO.println s!"--- {structName} / {ctorName}: numParams={cv.numParams} numFields={cv.numFields}"
  let mut ty := cv.type
  let mut i := 0
  while i < cv.numFields do
    match ty with
    | .forallE n fieldTy rest _ =>
      IO.println s!"field {i} named {n}:"
      IO.println s!"  raw   : {fieldTy}"
      IO.println s!"  ctor  : {fieldTy.ctorName}"
      IO.println s!"  headFn: {fieldTy.getAppFn}"
      IO.println s!"  nargs : {fieldTy.getAppArgs.size}"
      IO.println s!"  args  : {fieldTy.getAppArgs.toList}"
      ty := rest
      i := i + 1
    | _ => i := cv.numFields

#eval dumpCtorTelescope `UorAtlas.Instance `UorAtlas.Instance.mk
#eval dumpCtorTelescope `Conformance.MidProp `Conformance.MidProp.mk
```

Run: `cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake env lean Scratch.lean`

- [ ] **Step 2: Record what you see**

`UorAtlas.Instance.valid` has type `q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1`. From the dump, determine and write down:

1. The head constant of the conjunction — `And`, and its argument count.
2. The head constant of `≥` — whether it is `GE.ge` with an instance argument still present, or already unfolded to `Nat.le`/`Nat.ble`, and how many arguments it carries.
3. **How the proposition refers to `q`, `T`, `O`.** They are earlier binders in the same telescope, so they arrive as `Expr.bvar` with de Bruijn indices, or as something else. Record which, and — if `bvar` — what index each field has relative to the binder depth. This is the part the lowering cannot guess.
4. Whether `1` is a raw `Expr.lit` or an `OfNat.ofNat` application.

- [ ] **Step 3: Record the finding in AGENTS.md**

Add a bullet to the "Verified Lean 4.30.0 API facts" list, filled in with what you observed:

```
- Structure `Prop` field propositions, as seen in the constructor telescope:
  conjunction is `<head constant>` with `<n>` args; `a ≥ b` appears as
  `<observed form>`; earlier fields are referenced as `<bvar with index
  rule | other>`; numeric literals appear as `<form>`. Verified by dumping
  `UorAtlas.Instance.mk` and `Conformance.MidProp.mk`. The invariant
  lowering (`lowerProp`) is written against exactly this shape, so a
  toolchain bump that changes it will show up as propositions no longer
  lowering — which degrades to "no checked constructor", never to a wrong
  check.
```

- [ ] **Step 4: Delete the scratch file, gates, commit**

```bash
rm lean/Scratch.lean
```

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`

```bash
git add AGENTS.md
git commit -m "Pin the shape of a Prop field's proposition

The invariant lowering reads a Prop field's proposition out of the
constructor telescope and turns it into a boolean expression. How Lean
represents that proposition — the conjunction's head constant, whether
the comparison still carries its instance argument, and above all how it
refers to earlier fields — is not guessable, and two guesses at Lean
constant names were already wrong in Phase A.

Recorded so the lowering is written against what Lean produces.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: IR surface for invariants

**Files:**
- Modify: `rust/prod-ir/src/lib.rs`, `rust/prod-ir/src/parser.rs`

**Interfaces:**
- Produces:
  - `Expr::And(Box<Expr>, Box<Expr>)`, `Expr::Or(Box<Expr>, Box<Expr>)`, `Expr::Not(Box<Expr>)`; grammar `(and a b)`, `(or a b)`, `(not a)`
  - `TypeDecl.invariant: Option<Expr>`; grammar `(type "Name" (ctor …) (invariant <expr>))`
  - The invariant expression refers to fields by name, as `Expr::Var("q")`.

- [ ] **Step 1: Write the failing parser tests**

Add to the `tests` module in `rust/prod-ir/src/parser.rs`:

```rust
#[test]
fn test_parse_connectives() {
    assert!(matches!(parse_expr("(and a b)").unwrap().1, Expr::And(_, _)));
    assert!(matches!(parse_expr("(or a b)").unwrap().1, Expr::Or(_, _)));
    assert!(matches!(parse_expr("(not a)").unwrap().1, Expr::Not(_)));
}

#[test]
fn test_parse_type_decl_with_invariant() {
    let input = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat))
    (invariant (and (le 1 q) (and (le 1 T) (le 1 O)))))
)
"#;
    let (rest, module) = parse_module(input).unwrap();
    assert!(rest.trim().is_empty());
    let decl = &module.types[0];
    assert_eq!(decl.ctors.len(), 1);
    assert!(decl.invariant.is_some(), "invariant must round-trip");
    assert!(matches!(decl.invariant.as_ref().unwrap(), Expr::And(_, _)));
}

#[test]
fn test_type_decl_without_invariant_still_parses() {
    // A structure with no lowerable Prop field carries no invariant. That is
    // the common case and must stay unaffected.
    let input = r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#;
    let (_, module) = parse_module(input).unwrap();
    assert!(module.types[0].invariant.is_none());
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cd rust && cargo test -p prod-ir`
Expected: FAIL — no `And`/`Or`/`Not` variants, no `invariant` field.

- [ ] **Step 3: Add the variants and the field**

In `rust/prod-ir/src/lib.rs`, add to `Expr`:

```rust
    /// Boolean conjunction. Produced only by the invariant lowering — Lean's
    /// computational `&&` reaches LCNF as `cases` on `Bool.true`/`Bool.false`
    /// and needs no node (verified in S2 Phase A). These exist because a
    /// `Prop` field's proposition is lowered to a boolean expression, and a
    /// conjunction of comparisons has no `cases` form to reuse.
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
```

And to `TypeDecl`:

```rust
    /// The structure's erased `Prop` invariant, lowered to a boolean
    /// expression over its own fields (referenced by name as `Expr::Var`).
    /// `None` when the structure has no `Prop` field, or has one whose
    /// proposition the exporter cannot lower — in which case the type keeps
    /// public fields and no checked constructor, exactly as before.
    pub invariant: Option<Expr>,
```

Every `TypeDecl` construction site must set it; the compiler will name them.

- [ ] **Step 4: Add the grammar**

In `rust/prod-ir/src/parser.rs`, add three arms to `parse_paren_expr`'s second `alt` group:

```rust
                map(
                    tuple((tag("and"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::And(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("or"), ws(parse_expr), ws(parse_expr))),
                    |(_, a, b)| Expr::Or(Box::new(a), Box::new(b)),
                ),
                map(
                    tuple((tag("not"), ws(parse_expr))),
                    |(_, a)| Expr::Not(Box::new(a)),
                ),
```

Add the invariant clause, and thread it into `parse_type_decl`:

```rust
/// `(invariant <expr>)` — the structure's erased Prop invariant, as a boolean
/// expression over its own field names.
fn parse_invariant(input: &str) -> IResult<&str, Expr> {
    delimited(
        char('('),
        map(tuple((tag("invariant"), ws(parse_expr))), |(_, e)| e),
        char(')'),
    )(input)
}
```

`parse_type_decl` gains `opt(ws(parse_invariant))` **after** `many0(ws(parse_ctor_decl))`, and sets the field.

Add `Expr::And(a, b) | Expr::Or(a, b)` to `children()`'s binary group and `Expr::Not(e)` to the unary pushes, in `prod-ir`'s `Expr::children`.

- [ ] **Step 5: Run tests, gates, commit**

Run: `cd rust && cargo test --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`, plus the wasm32 build.

```bash
git add rust/prod-ir/src
git commit -m "IR: invariants on type declarations, and boolean connectives

A structure's erased Prop invariant rides on its type declaration as a
boolean expression over its own field names. Additive: a declaration
without one parses exactly as before, which is the common case.

And/Or/Not exist only for this. Lean's computational && reaches LCNF as
cases on Bool.true/Bool.false and needs no node — verified in Phase A —
but a lowered proposition has no cases form to reuse.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: Lean lowers the proposition

**Files:**
- Modify: `lean/Prod/Lower.lean`
- Modify: `lean/Conformance/golden.ir` (regenerated)

**Interfaces:**
- Consumes: the `Expr`-shape finding recorded in `AGENTS.md` by Task 2.
- Produces: `Prod.lowerProp : Expr → Array String → Nat → LowerM (Option String)` — proposition, field names in binder order, current binder depth; returns the IR boolean expression or `none` when not lowerable. Helper `Prod.lowerPropOperand` has the same three-argument shape and must be defined BEFORE `lowerProp`, which calls it (Lean has no forward references outside a `mutual` block, and `lowerPropOperand` does not call back, so ordering is enough). `lowerTypeDecl` emits `(invariant …)` when every `Prop` field lowers.

- [ ] **Step 1: Write `lowerProp`**

In `lean/Prod/Lower.lean`, after `isPropType`. **Use the exact `Expr` shape Task 2 recorded** — the arities and the field-reference rule below are written for the expected shape and must be adjusted to the observed one:

```lean
/-- Lower a `Prop` to a boolean IR expression over a structure's own fields,
    or `none` if it is outside the lowerable fragment.

    `fields` holds the field names in binder order; a proposition refers to an
    earlier field by de Bruijn index, so `bvar i` at binder depth `d` names
    `fields[d - 1 - i]`. See AGENTS.md for the verified shape.

    Lowerable: conjunction, disjunction, negation, and comparisons on
    supported numeric kinds. Everything else — quantifiers, arbitrary
    predicates, anything mentioning a name that is not one of this
    structure's fields — returns `none`, and the structure then keeps public
    fields and no checked constructor. That is a strictly weaker outcome, not
    a wrong one. -/
partial def lowerProp (e : Expr) (fields : Array String) (depth : Nat)
    : LowerM (Option String) := do
  let arg? (i : Nat) : Option Expr := e.getAppArgs[i]?
  match e.getAppFn with
  | .const ``And _ => do
    let some a := arg? 0 | return none
    let some b := arg? 1 | return none
    let some a' ← lowerProp a fields depth | return none
    let some b' ← lowerProp b fields depth | return none
    return some s!"(and {a'} {b'})"
  | .const ``Or _ => do
    let some a := arg? 0 | return none
    let some b := arg? 1 | return none
    let some a' ← lowerProp a fields depth | return none
    let some b' ← lowerProp b fields depth | return none
    return some s!"(or {a'} {b'})"
  | .const ``Not _ => do
    let some a := arg? 0 | return none
    let some a' ← lowerProp a fields depth | return none
    return some s!"(not {a'})"
  | .const cmp _ =>
    -- Comparisons. `a ≥ b` is `b ≤ a` and `a > b` is `b < a`, so the two
    -- reversed forms map onto the IR's `le`/`lt` with their operands swapped
    -- rather than needing their own nodes.
    let swap? : Option (String × Bool) :=
      if cmp == ``LE.le || cmp == ``Nat.le then some ("le", false)
      else if cmp == ``GE.ge then some ("le", true)
      else if cmp == ``LT.lt || cmp == ``Nat.lt then some ("lt", false)
      else if cmp == ``GT.gt then some ("lt", true)
      else if cmp == ``Eq then some ("eq", false)
      else none
    let some (op, reversed) := swap? | return none
    -- Comparisons carry instance/type arguments ahead of the operands; take
    -- the LAST two arguments, which are the operands under every spelling.
    let args := e.getAppArgs
    if args.size < 2 then return none
    let some a ← lowerPropOperand args[args.size - 2]! fields depth | return none
    let some b ← lowerPropOperand args[args.size - 1]! fields depth | return none
    return some (if reversed then s!"({op} {b} {a})" else s!"({op} {a} {b})")
  | _ => return none

/-- An operand inside a proposition: either a reference to one of the
    structure's own fields, or a numeric literal. Anything else makes the
    whole proposition unlowerable. -/
partial def lowerPropOperand (e : Expr) (fields : Array String) (depth : Nat)
    : LowerM (Option String) := do
  match e with
  | .bvar i =>
    let idx := depth - 1 - i
    match fields[idx]? with
    | some name => return some name
    | none => return none
  | .lit (.natVal n) => return some (toString n)
  | _ =>
    -- `OfNat.ofNat`-wrapped literals: take the raw literal argument if there
    -- is one, otherwise decline.
    match e.getAppFn with
    | .const ``OfNat.ofNat _ =>
      match e.getAppArgs[1]? with
      | some (.lit (.natVal n)) => return some (toString n)
      | _ => return none
    | _ => return none
```

- [ ] **Step 2: Emit the invariant from `lowerTypeDecl`**

`lowerTypeDecl` already walks the constructor telescope, skipping `Prop` fields. Change it to also *collect* them: for each `Prop` field, call `lowerProp` with the computational field names gathered so far and the current binder depth. Then:

- if there is at least one `Prop` field and **every** one lowered, emit `(invariant <conjunction of them>)` after the ctor clause;
- if there are none, or any failed to lower, emit no invariant clause.

Conjoin multiple `Prop` fields with `(and …)`, left-associated.

**Important:** `fields` passed to `lowerProp` must be the names in **binder order including the `Prop` fields**, because de Bruijn indices count every binder. The output field list (which excludes `Prop` fields) is a different list — do not conflate them. Use a separate `allBinderNames : Array String`.

- [ ] **Step 3: Rebuild, re-export, read the invariant**

Run:
```bash
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
```

`rust/prod-core/kernel.ir` must now show, for `UorAtlas.Instance`, an `(invariant …)` clause equivalent to `q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1`. Quote it in your report and **check the operand order**: `q ≥ 1` must lower to `(le 1 q)`, not `(le q 1)`. Getting that backwards inverts the invariant and is exactly the kind of silent wrongness this project keeps producing — a reversed comparison still compiles and still returns a `bool`.

`Conformance.MidProp`'s `first ≥ 0` must also lower — it is trivially true, which makes it a good check that the machinery does not special-case anything.

- [ ] **Step 4: Gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`, then clippy, fmt and the wasm32 build.

```bash
git add -A
git commit -m "Lean lowers a Prop field's proposition to a boolean expression

The proof is erased, as it should be — it is a proof, not data. The
PROPOSITION is not: q >= 1 /\\ T >= 1 /\\ O >= 1 is a decidable statement
over the structure's own fields, and lowering it is what lets the
generated struct re-check at the crate boundary what Lean established at
construction.

Only conjunction, disjunction, negation and comparisons lower. Anything
else declines, and the structure then keeps public fields and no checked
constructor — a strictly weaker outcome, not a wrong one.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 5: Codegen renders the checked constructor

**Files:**
- Modify: `rust/prod-core/src/error.rs`
- Modify: `rust/prod-codegen/src/lib.rs`, `rust/prod-codegen/src/tests.rs`

**Interfaces:**
- Consumes: `TypeDecl.invariant`, `Expr::{And,Or,Not}`.
- Produces: `ComputeError::InvariantViolated(&'static str)`; invariant-carrying types render `pub(crate)` fields, a `pub fn new(..) -> Result<Self, crate::ComputeError>`, and one accessor per field.

- [ ] **Step 1: Write the failing tests**

Add to `rust/prod-codegen/src/tests.rs`:

```rust
#[test]
fn test_invariant_type_gets_private_fields_and_a_checked_constructor() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat))
    (invariant (and (le 1 q) (and (le 1 T) (le 1 O)))))
)
"#;
    let out = generate(ir);
    // Fields are pub(crate): generated code in this crate still constructs by
    // struct literal, because Lean already supplied the proof. Only external
    // callers are routed through the check.
    assert!(out.contains("pub(crate) q: u64"), "got: {}", out);
    assert!(!out.contains("pub q: u64"));
    assert!(out.contains(
        "pub fn new(q: u64, T: u64, O: u64) -> Result<Self, crate::ComputeError>"
    ));
    assert!(out.contains("if ((1 <= q) && ((1 <= T) && (1 <= O)))"));
    assert!(out.contains("crate::ComputeError::InvariantViolated(\"UorAtlas.Instance\")"));
    // One accessor per field, so external callers can still read.
    assert!(out.contains("pub fn q(&self) -> u64 { self.q }"));
    assert!(out.contains("pub fn T(&self) -> u64 { self.T }"));
}

#[test]
fn test_type_without_invariant_is_unchanged() {
    // The common case must not regress: public fields, no constructor, no
    // accessors.
    let ir = r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#;
    let out = generate(ir);
    assert!(out.contains("pub a: u64"));
    assert!(!out.contains("pub(crate)"));
    assert!(!out.contains("fn new("));
}

#[test]
fn test_connectives_render() {
    let ir = r#"
(module M
  (def f ((a Nat) (b Nat)) Bool (and (lt a b) (not (eq a b)))))
"#;
    assert!(generate(ir).contains("((a < b) && (!(a == b)))"));
}

#[test]
fn test_or_renders() {
    let ir = r#"(module M (def f ((a Nat) (b Nat)) Bool (or (lt a b) (eq a b))))"#;
    assert!(generate(ir).contains("((a < b) || (a == b))"));
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cd rust && cargo test -p prod-codegen`
Expected: FAIL — no connective rendering, no constructor.

- [ ] **Step 3: Add the error variant**

In `rust/prod-core/src/error.rs`:

```rust
    /// A generated checked constructor's invariant did not hold. The payload
    /// names the type; it is `&'static str` so the enum stays `Copy` and the
    /// error path stays allocation-free.
    InvariantViolated(&'static str),
```

`as_str` stays payload-free so it remains usable in `const` contexts:

```rust
            ComputeError::InvariantViolated(_) => "structure invariant violated",
```

and `Display` adds the name — this is the first variant whose `Display` differs from `as_str`:

```rust
impl fmt::Display for ComputeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ComputeError::InvariantViolated(name) => {
                write!(f, "{} for `{}`", self.as_str(), name)
            }
            _ => f.write_str(self.as_str()),
        }
    }
}
```

Extend the distinctness test in that file with the new variant, constructing it as `ComputeError::InvariantViolated("X")`.

- [ ] **Step 4: Render the connectives**

In `rust/prod-codegen/src/lib.rs`, in `render_value_leaf`:

```rust
            Expr::And(a, b) => Ok(format!("({} && {})", self.value(a)?, self.value(b)?)),
            Expr::Or(a, b) => Ok(format!("({} || {})", self.value(a)?, self.value(b)?)),
            Expr::Not(a) => Ok(format!("(!{})", self.value(a)?)),
```

Add `Expr::And(..) | Expr::Or(..) | Expr::Not(_)` to `children()` in `prod-codegen` if it maintains its own copy; if it now calls `prod_ir::Expr::children`, Task 3 already covered it.

- [ ] **Step 5: Render the constructor and accessors**

In `generate_type_decl` (`rust/prod-codegen/src/lib.rs:332`).

**Two structural things first, both of which the code below assumes:**

1. **The single-constructor branch returns early at line 362** (`return Ok(out);` right after `out.push_str("}\n")`). The invariant block goes immediately *before* that `return`, not after the function's other branches — appending at the end of the function would render it only for enums, which is exactly backwards.

2. **`Renderer` borrows with an explicit module lifetime** — `Renderer<'s, 'm>` with `value(&self, expr: &'m Expr)`. `generate_type_decl(decl: &TypeDecl, table: &TypeTable)` currently elides both, and `decl.invariant` must outlive the `Renderer`. Change the signature to tie them together:

```rust
fn generate_type_decl<'m>(decl: &'m TypeDecl, table: &TypeTable<'m>) -> Result<String, Error> {
```

and fix up the call site if the compiler asks. If this fights the borrow checker for more than a few minutes, report it rather than reaching for `clone()` on the expression — say what the compiler said.

Only single-constructor types can carry an invariant (a `Prop` field belongs to one constructor), so reject the multi-constructor case rather than rendering something half-right. Note that `short` is already bound at line 349 as a `&str`; the code below uses `rust_name` to avoid shadowing it:

```rust
    if let Some(invariant) = &decl.invariant {
        if decl.ctors.len() != 1 {
            return Err(Error::UnsupportedFieldType(format!(
                "`{}` carries an invariant but has {} constructors; only a \
                 single-constructor structure can have one",
                decl.name,
                decl.ctors.len()
            )));
        }
        let ctor = &decl.ctors[0];
        let rust_name = rust_ident(short);

        // Render the invariant with the constructor's parameters in scope: the
        // IR refers to fields by name, and `new`'s parameters carry those same
        // names, so `Var("q")` resolves without any rebinding.
        // `shapes` must be a named binding, not a temporary: `Renderer` holds
        // `&'s Signatures<'m>`, so `&BTreeMap::new()` inline would be dropped
        // at the end of the statement and fail to borrow-check.
        let no_shapes: Signatures = BTreeMap::new();
        let renderer = Renderer {
            shapes: &no_shapes,
            params: &[],
            types: table,
            ctx: JpContext::collect(invariant),
        };
        let predicate = renderer.value(invariant)?;

        let mut params = Vec::with_capacity(ctor.fields.len());
        let mut inits = Vec::with_capacity(ctor.fields.len());
        for (name, ty) in &ctor.fields {
            params.push(format!("{}: {}", rust_ident(name), type_to_rust(ty)?));
            inits.push(rust_ident(name));
        }

        out.push_str(&format!("impl {} {{\n", rust_name));
        out.push_str(&format!(
            "    /// Re-checks the invariant Lean proved at construction.\n\
             \x20   ///\n\
             \x20   /// Generated code does not call this: inside the generated world the\n\
             \x20   /// proof holds, and re-checking would turn proved-total functions\n\
             \x20   /// fallible. It exists for callers at the crate boundary, where the\n\
             \x20   /// proof is not available because it was erased on export.\n\
             \x20   pub fn new({}) -> Result<Self, crate::ComputeError> {{\n\
             \x20       if {} {{\n\
             \x20           Ok({} {{ {} }})\n\
             \x20       }} else {{\n\
             \x20           Err(crate::ComputeError::InvariantViolated({:?}))\n\
             \x20       }}\n\
             \x20   }}\n",
            params.join(", "),
            predicate,
            rust_name,
            inits.join(", "),
            decl.name
        ));
        for (name, ty) in &ctor.fields {
            out.push_str(&format!(
                "    pub fn {}(&self) -> {} {{ self.{} }}\n",
                rust_ident(name),
                type_to_rust(ty)?,
                rust_ident(name)
            ));
        }
        out.push_str("}\n");
    }
```

and make the struct-field visibility depend on the invariant:

```rust
        let vis = if decl.invariant.is_some() { "pub(crate)" } else { "pub" };
```

used in place of the hard-coded `pub` in the struct-field loop.

- [ ] **Step 6: Run tests, gates, commit**

Run: `cd rust && cargo test --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`, plus the wasm32 build.

```bash
git add rust/prod-core/src/error.rs rust/prod-codegen/src
git commit -m "Generate a checked constructor for invariant-carrying types

A structure whose Prop fields all lower gets pub(crate) fields, a
new() that re-checks the invariant, and one accessor per field.

Generated code does not call new(): fields stay reachable in-crate and
it keeps constructing by struct literal, because Lean already supplied a
proof and re-checking internally would turn proved-total functions
fallible. The check exists at the crate boundary, which is the honest
reading of what erasure means.

InvariantViolated carries a &'static str naming the type, so the enum
stays Copy and the error path stays allocation-free. It is the first
variant whose Display differs from as_str, which stays payload-free so
it remains const-usable.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 6: Migrate the construction sites and tell the truth in the contract

This is the blast radius. All of it is compiler-caught.

**Files:**
- Modify: `rust/prod-core/tests/macro_generation.rs`, `rust/prod-core/tests/no_alloc.rs`
- Modify: `rust/prod-codegen-compile-tests/tests/smoke.rs`
- Modify: `lean/Prod/Emit.lean` (contract prose), `specs/lean-for-production.md` (regenerated)
- Modify: `AGENTS.md`, `specs/designs/2026-08-09-s2-scalar-completeness-and-invariants.md`

**Interfaces:**
- Consumes: `Instance::new`, `Instance::q()/T()/O()`, `MidProp::new` from Task 5.

- [ ] **Step 1: Migrate `prod-core`'s tests**

`const CANONICAL: Instance = Instance { q: 4, T: 3, O: 8 };` no longer compiles — fields are `pub(crate)` and these are integration tests, which are external. A `const` cannot call a fallible constructor either.

Replace the three consts with per-test construction. Every test in the file already returns `Result<(), ComputeError>`, so use `?`:

```rust
    let canonical = Instance::new(4, 3, 8)?;
    let demo_small = Instance::new(2, 2, 4)?;
    let third = Instance::new(5, 1, 3)?;
```

`prod-core` denies `clippy::{unwrap_used, expect_used, panic}` in test targets too, so `?` is the only option — do not reach for `.unwrap()`.

Field reads become accessor calls: `inst.q` → `inst.q()`, `inst.T` → `inst.T()`, `inst.O` → `inst.O()`. `spectral.rs` is in-crate and needs no change; confirm that rather than assuming it.

`no_alloc.rs` has the same `CANONICAL` const and, additionally, constructs the degenerate `Instance { q: 1, t: 1, o: 70 }`-style values for the overflow tests. Those now go through `new` too — and `Instance::new(1, 1, 70)` **succeeds**, since `70 ≥ 1`, so the overflow assertions still hold.

**Watch for one thing:** `no_alloc.rs` asserts zero heap activity. Adding a constructor call inside the measured region would measure the constructor too. Construct outside `assert_no_allocation`, and add one measurement *of* `Instance::new` to prove the invariant check itself allocates nothing.

- [ ] **Step 2: Migrate `smoke.rs`**

`MidProp { first: 1, second: 2, third: 3 }` becomes `MidProp::new(1, 2, 3)?`. That test returns `Result`, so `?` works.

- [ ] **Step 3: Rewrite the contract's erased-invariants section**

`lean/Prod/Emit.lean`'s `subsetJson` currently states that `Prop` fields are erased and the generated struct does **not** enforce the invariant, so callers must re-check. **That is now backwards for every lowerable case** and must be rewritten, not appended to — this project has already shipped one documentation section that survived the change it described.

The replacement must say: `Prop` fields are still erased, because they are proofs; but when the proposition is lowerable, the struct's fields become `pub(crate)` and a checked `new` re-checks it at the crate boundary, with accessors for reading. When the proposition is not lowerable — quantifiers, arbitrary predicates, anything outside the structure's own fields — the type keeps public fields and the invariant genuinely is not enforced, exactly as before. Name which of the two a reader gets and how to tell.

- [ ] **Step 4: Update `AGENTS.md` and the design doc**

`AGENTS.md`: record that invariant-carrying types exist, that generated code bypasses the check by design and why, and that the lowerable fragment is conjunction/disjunction/negation/comparisons.

The design doc: mark Phase B1 done, and note that Phase B2 (`Fin` literal specialisation) is now unblocked and should be planned against the machinery as it shipped.

- [ ] **Step 5: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`, then clippy, fmt and the wasm32 build from `rust/`.

```bash
git add -A
git commit -m "Migrate construction sites; the contract stops saying the opposite

Instance and MidProp now have pub(crate) fields, so every external
construction site moves to the checked constructor and every external
field read moves to an accessor. spectral.rs is in-crate and unaffected.

The contract's erased-invariants section said the generated struct does
NOT enforce the invariant and callers must re-check. That is backwards
for every lowerable case now, so it is rewritten rather than appended
to — a stale section that survives the change it describes is a defect
this project has already shipped once.

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

- [ ] **Read the generated `Instance` and check the invariant is not inverted**

```bash
cd rust && cargo run -p prod-cli -- gen prod-core/kernel.ir | head -40
```

The predicate must read `1 <= q && 1 <= T && 1 <= O`, not the reverse. A reversed comparison compiles, returns a `bool`, and rejects exactly the values it should accept — verify `Instance::new(4, 3, 8)` succeeds and `Instance::new(0, 3, 8)` fails, which the migrated tests should already cover. If they do not, add it.

- [ ] **Confirm the contract no longer contradicts the code**

Read `specs/lean-for-production.md`'s invariants section as committed and check every sentence against what Task 5 renders.
