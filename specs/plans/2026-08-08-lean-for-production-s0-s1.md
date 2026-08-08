# Lean-for-production S0 + S1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make every unsupported Lean construct fail precisely instead of producing broken Rust, and generate Rust structs/enums from Lean inductives so the hard-wired `Instance` coupling can be deleted.

**Architecture:** Lean describes faithfully, Rust refuses to render what it cannot. `Lower.lean` gains type-declaration emission and resolves structure projections to *field names* (it has the environment; Rust does not), so the declaration and the projection come from one source of truth and swapped fields become impossible rather than merely tested for. `prod-codegen` gains a type table, renders struct/enum declarations ahead of functions, and turns every remaining unrenderable construct into a typed `Error`.

**Tech Stack:** Lean 4.30.0 (pinned, no mathlib), Rust 1.95, `nom` 7 parser, `prod-macros` proc macro, `just` + nix dev shell.

**Design doc:** `specs/designs/2026-08-08-lean-for-production-coverage.md`

## Global Constraints

- NO mathlib. Pure Lean 4 core/Init. NO `sorry`, NO `axiom`.
- Generated artifacts are never hand-edited: `rust/prod-core/kernel.ir`, `rust/prod-core/goldens.ir`, `roots.json`, `coverage.md`, `subset.json`. The one exception introduced here is `lean/Conformance/golden.ir`, which is committed but only ever regenerated via `just conformance-bless`.
- Generated code contract is unchanged: no panic on caller-controlled input, no heap allocation, `ComputeError` for runtime failure. `prod_codegen::Error` is the compile-time codegen error type and is a different thing.
- `prod-codegen` stays `#![no_std]` and wasm32-clean. No `std`, no threads.
- `unsafe_code = "forbid"` workspace-wide except `prod-wasm` and `prod-alloc-counter`.
- lean/lake are NOT on PATH. Always: `cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build`. Lean builds take minutes — use 300s+ timeouts.
- Every task ends green on: `cargo test --workspace`, `cargo clippy --all-targets -- -D warnings`, `cargo fmt --all -- --check` (run from `rust/`).
- Commit at the end of every task. Do not `git push`.

---

### Task 1: Golden-IR conformance harness

`lean/Prod/Lower.lean` has no tests at all. This task gives it some, and every later task is protected by them. Zero blast radius: nothing existing changes behaviour.

**Files:**
- Create: `lean/Conformance.lean`
- Create: `lean/Conformance/golden.ir` (generated, committed)
- Modify: `lean/Prod/Emit.lean:30-36` (module constants), `lean/Prod/Emit.lean:56-66` (`runExport`), `lean/Prod/Emit.lean:158-179` (`main`)
- Modify: `lean/lakefile.lean` (add `Conformance` to the library roots)
- Modify: `justfile`
- Modify: `.github/workflows/ci.yml`

**Interfaces:**
- Consumes: `Prod.emitKernelIr : LowerCtx → Array ExtractedDef → CoreM (String × Array DefReport)`, `Prod.extractTagged : Name → CoreM (Array ExtractedDef)`, `Prod.taggedNames : Environment → Name → List Name` (all existing).
- Produces: `Prod.conformanceModule : Name`; `runExport` returns a 4-tuple whose new last element is the conformance IR text; `just conformance` and `just conformance-bless`.

- [ ] **Step 1: Create the conformance module with the features that already work**

Create `lean/Conformance.lean`. One tiny definition per feature, each named after what it pins. Keep bodies minimal — this file is a change-detector, not a test of arithmetic.

```lean
-- Conformance cases for the Lean → IR lowering. One @[prod] def per feature.
-- The lowered output is diffed against lean/Conformance/golden.ir in CI, so a
-- change here or in Prod/Lower.lean shows up as a reviewable golden diff.
-- Regenerate with `just conformance-bless`. Never hand-edit the golden.
import Prod.Attribute

namespace Conformance

@[prod] def c_nat_add (a b : Nat) : Nat := a + b
@[prod] def c_nat_sub (a b : Nat) : Nat := a - b
@[prod] def c_nat_mul (a b : Nat) : Nat := a * b
@[prod] def c_nat_div (a b : Nat) : Nat := a / b
@[prod] def c_nat_mod (a b : Nat) : Nat := a % b
@[prod] def c_nat_pow (a b : Nat) : Nat := a ^ b

@[prod] def c_guard_lt (a b : Nat) : Nat := if a < b then 1 else 0
@[prod] def c_guard_le (a b : Nat) : Nat := if a ≤ b then 1 else 0
@[prod] def c_guard_eq (a b : Nat) : Nat := if a = b then 1 else 0

@[prod] def c_bool (a b : Nat) : Bool := a < b
@[prod] def c_option (a : Nat) : Option Nat := if a < 10 then some a else none
@[prod] def c_tuple (a b : Nat) : Nat × Nat := (a, b)

@[prod] def c_nat_rec (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if n < 2 then 1 else 1 + c_nat_rec fuel (n / 2)

@[prod] def c_list_build (fuel n : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n < 2 then [n] else n % 2 :: c_list_build fuel (n / 2)

@[prod] def c_list_consume : List Nat → Nat
  | [] => 0
  | h :: t => h + c_list_consume t

end Conformance
```

- [ ] **Step 2: Wire the conformance module into the exporter**

In `lean/Prod/Emit.lean`, add the import and the module constant next to the existing ones (after line 33):

```lean
import Conformance
```

```lean
/-- Module tree whose lowering is pinned by a committed golden IR file. -/
def conformanceModule : Name := `Conformance

/-- IR module name for the conformance export. -/
def conformanceIrModule : String := "Conformance"
```

Replace `runExport` (lines 56-66) so it also lowers the conformance module. The conformance `LowerCtx` deliberately has **no** `instanceType` binding of its own — pass `targetInstance` so behaviour matches the real export path exactly:

```lean
/-- The whole export, as a CoreM computation over the imported environment. -/
def runExport : CoreM (String × String × String × String) := do
  let env ← getEnv
  let ctx : LowerCtx := {
    instanceType := targetInstance
    tagged := (taggedNames env targetModule).toArray }
  let extracted ← extractTagged targetModule
  let (ir, reports) ← emitKernelIr ctx extracted
  let own := ownConstants env targetModule
  let roots := rootsJson (← computeRoots own)
  let coverage ← buildCoverage targetModule own reports
  let confCtx : LowerCtx := {
    instanceType := targetInstance
    tagged := (taggedNames env conformanceModule).toArray }
  let confExtracted ← extractTagged conformanceModule
  let (confIr, _) ← emitKernelIr confCtx confExtracted
  return (ir, roots, coverage, confIr)
```

`emitKernelIr` hardcodes `targetIrModule` in its header; change line 41 to take the module name from a new parameter so the conformance export is not labelled `UorAtlas.Kernel`:

```lean
def emitKernelIr (ctx : LowerCtx) (irModule : String) (extracted : Array ExtractedDef)
    : CoreM (String × Array DefReport) := do
  let mut ir := s!";; Generated by prod-export: LCNF → sexp IR.\n(module {irModule}\n"
```

Update both call sites to pass `targetIrModule` and `conformanceIrModule` respectively.

- [ ] **Step 3: Write the conformance IR from `main`**

In `lean/Prod/Emit.lean`, update the destructuring and paths in `main` (lines 165-179):

```lean
  let (ir, roots, coverage, confIr) ← match result with
    | Except.ok (Except.ok outputs, _st) => pure outputs
    | Except.ok (Except.error msg, _st) => throw (IO.userError s!"prod-export failed: {msg}")
    | Except.error _ => throw (IO.userError "prod-export failed: uncaught exception")
  let (irPath, rootsPath, covPath, goldensPath, confPath) := match parseOutDir args with
    | some dir =>
      (dir / "kernel.ir", dir / "roots.json", dir / "coverage.md", dir / "goldens.ir",
       dir / "conformance-golden.ir")
    | none =>
      ("../rust/prod-core/kernel.ir", "../roots.json", "../coverage.md",
       "../rust/prod-core/goldens.ir", "Conformance/golden.ir")
  IO.FS.writeFile irPath ir
  IO.FS.writeFile rootsPath roots
  IO.FS.writeFile covPath coverage
  IO.FS.writeFile goldensPath Prod.emitGoldensIr
  IO.FS.writeFile confPath confIr
  IO.println s!"prod-export: wrote {irPath}, {rootsPath}, {covPath}, {goldensPath}, {confPath}"
```

Also add the library to `lean/lakefile.lean` so `lake build` compiles it, next to the existing `Example` stanza:

```lean
@[default_target]
lean_lib Conformance where
  roots := #[`Conformance]
```

- [ ] **Step 4: Build and generate the golden for the first time**

Run:
```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
```
Expected: exit 0, and `lean/Conformance/golden.ir` now exists.

**Review it by eye before committing.** Every def must lower with no `(opaque ...)` node. If any case is opaque, that is a genuine coverage gap: either drop that case from `Conformance.lean` with a comment saying which milestone will cover it, or fix the lowering. Do not commit a golden containing `opaque`.

- [ ] **Step 5: Verify the golden actually detects a change**

Temporarily edit `lean/Conformance.lean` to change `c_nat_add` to `a + b + 1`, rebuild, re-export, and confirm `git diff lean/Conformance/golden.ir` is non-empty. Then revert the edit and re-export so the golden matches `main` again.

Run: `git diff --exit-code lean/Conformance/golden.ir`
Expected after revert: exit 0 (no diff).

- [ ] **Step 6: Add the just lanes and the CI gate**

In `justfile`, after the `prod-export` recipe:

```make
# The conformance golden pins Lean-side lowering. `prod-export` rewrites it; this
# fails if the rewrite changed anything, so lowering changes surface as a diff.
conformance:
    cd lean && lake exe prod-export
    git diff --exit-code lean/Conformance/golden.ir

# Accept the current lowering as the new golden. Review the diff before running.
conformance-bless:
    cd lean && lake exe prod-export
    git add lean/Conformance/golden.ir
```

Add `conformance` to the `prod` recipe's dependency list, after `prod-export`:

```make
prod: prod-export conformance test test-assertions no-alloc roots-check
```

In `.github/workflows/ci.yml`, no new step is needed — `just prod` covers it.

- [ ] **Step 7: Verify the whole pipeline**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`
Expected: all lanes pass, including the new `conformance` lane.

- [ ] **Step 8: Commit**

```bash
git add lean/Conformance.lean lean/Conformance/golden.ir lean/Prod/Emit.lean lean/lakefile.lean justfile
git commit -m "Add golden-IR conformance harness for the Lean lowerer

Lower.lean had no tests; the Lean half of the pipeline was verified only
by the one example kernel happening to work. lean/Conformance.lean holds
one small @[prod] def per supported feature, and its lowered IR is
committed as a golden that prod-export rewrites and CI diffs, so any
change in lowering surfaces as a reviewable diff rather than silently.

The golden is generated, committed, and regenerated only via
just conformance-bless. It is never hand-edited.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: Projection index spike

The highest-risk item in the milestone. A wrong field mapping produces *silently wrong answers*, not a compile error. This task establishes the rule and records it before any code depends on it.

**Files:**
- Create: `lean/Conformance/Structures.lean`
- Modify: `lean/Conformance.lean` (import the new file)
- Modify: `AGENTS.md` (record the verified rule)
- Modify: `lean/Conformance/golden.ir` (regenerated)

**Interfaces:**
- Consumes: nothing new.
- Produces: a documented rule in `AGENTS.md` under the verified-API section, and conformance cases that would fail if field order were mis-mapped.

- [ ] **Step 1: Write the probe structures**

Create `lean/Conformance/Structures.lean`. The point is a structure whose `Prop` field is **not last**, and fields whose values are distinguishable so a swap cannot pass.

```lean
-- Probes for the Lean-structure-field → LCNF-projection-index correspondence.
-- Fields carry distinguishable values on purpose: if the mapping were wrong,
-- c_proj_middle_prop would return the fields in the wrong order and the golden
-- would change. See AGENTS.md for the rule these pin down.
import Prod.Attribute

namespace Conformance

/-- Prop field in the MIDDLE, not at the end: the case the existing
    `UorAtlas.Instance` (whose proof field is last) does not exercise. -/
structure MidProp where
  first  : Nat
  ok     : first ≥ 0
  second : Nat
  third  : Nat

/-- All-computational structure, as a control. -/
structure NoProp where
  alpha : Nat
  beta  : Nat

@[prod] def c_proj_middle_prop (m : MidProp) : Nat × Nat × Nat :=
  (m.first, m.second, m.third)

@[prod] def c_proj_no_prop (n : NoProp) : Nat × Nat :=
  (n.alpha, n.beta)

end Conformance
```

Add `import Conformance.Structures` to the top of `lean/Conformance.lean`.

- [ ] **Step 2: Export and read off the indices**

Run:
```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
```
Then read the emitted `c_proj_middle_prop` in `lean/Conformance/golden.ir`.

Determine which of these holds:
- **(A) Indices are into the erased field list** — `first`→0, `second`→1, `third`→2, and `ok` has no index.
- **(B) Indices are into the declared field list** — `first`→0, `second`→2, `third`→3, and index 1 is the erased proof.

The existing `UorAtlas.Instance` cannot distinguish these because its `Prop` field is last. Record which one you observed, with the exact IR line as evidence.

- [ ] **Step 3: Confirm the rule against Lean's introspection API**

Do not rely on one observation. In a scratch Lean file, check what the environment reports so the exporter can compute the same mapping in Task 5:

```lean
import Lean
open Lean
#eval do
  let env ← getEnv
  -- Which fields does Lean consider the structure to have, and in what order?
  IO.println s!"{getStructureFields env `Conformance.MidProp}"
  -- Constructor arity: numParams (type params) and numFields (value fields).
  match env.find? `Conformance.MidProp.mk with
  | some (.ctorInfo cv) => IO.println s!"numParams={cv.numParams} numFields={cv.numFields}"
  | _ => IO.println "not a constructor"
```

Expected: `getStructureFields` returns the declared field names in declaration order, and `numFields` is the declared count. If `getStructureFields` is not resolvable under 4.30 in this context, find the equivalent (`Lean.getStructureInfo?` or reading `InductiveVal.ctors` and walking the constructor type telescope) and record what actually worked.

Record in `AGENTS.md`, in the "Verified Lean 4.30.0 API facts" list, a bullet of this form with the observed answer filled in:

```
- Structure projection indices: LCNF `.proj typeName idx fvar` indexes into the
  <erased | declared> field list — verified with `Conformance.MidProp`, whose
  `Prop` field sits in the middle (`Conformance/Structures.lean`). Field names
  come from `<the API that worked>`; `Prop` fields are <erased | retained>.
  Getting this wrong swaps struct fields SILENTLY, so any change here must
  re-run that conformance case.
```

- [ ] **Step 4: Verify the golden and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`
Expected: green. The golden now contains the two probe defs.

```bash
git add lean/Conformance/Structures.lean lean/Conformance.lean lean/Conformance/golden.ir AGENTS.md
git commit -m "Pin the structure-field to LCNF-projection-index rule

The existing UorAtlas.Instance has its Prop field last, so it cannot
distinguish indices-into-erased-fields from indices-into-declared-fields.
Conformance.MidProp puts a Prop field in the middle and returns three
distinguishable fields, so a mis-mapping changes the golden instead of
silently swapping struct fields at runtime.

The observed rule is recorded in AGENTS.md; Task 5 computes field names
from it.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: IR type declarations

Adds the IR surface for generated types. Additive only — `Type::Instance` still exists and still works, so nothing breaks.

**Files:**
- Modify: `rust/prod-ir/src/lib.rs`
- Modify: `rust/prod-ir/src/parser.rs`

**Interfaces:**
- Produces:
  - `prod_ir::TypeDecl { pub name: String, pub ctors: Vec<CtorDecl> }`
  - `prod_ir::CtorDecl { pub name: String, pub fields: Vec<(String, Type)> }`
  - `prod_ir::Module { pub name: String, pub types: Vec<TypeDecl>, pub definitions: Vec<Definition> }` — note the new `types` field; every construction site of `Module` must be updated.
  - `prod_ir::Type::Named(String)`
  - Grammar: `(type "Full.Name" (ctor "Full.Name.mk" (field Type)...)...)` and `(named "Full.Name")`.

- [ ] **Step 1: Write the failing parser tests**

Add to the `tests` module in `rust/prod-ir/src/parser.rs`:

```rust
#[test]
fn test_parse_type_decl_single_ctor() {
    let input = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
)
"#;
    let (rest, module) = parse_module(input).unwrap();
    assert!(rest.trim().is_empty());
    assert_eq!(module.types.len(), 1);
    assert_eq!(module.types[0].name, "UorAtlas.Instance");
    assert_eq!(module.types[0].ctors.len(), 1);
    assert_eq!(module.types[0].ctors[0].name, "UorAtlas.Instance.mk");
    assert_eq!(
        module.types[0].ctors[0].fields,
        vec![
            ("q".to_string(), Type::Nat),
            ("T".to_string(), Type::Nat),
            ("O".to_string(), Type::Nat),
        ]
    );
}

#[test]
fn test_parse_type_decl_multi_ctor_and_named_type() {
    let input = r#"
(module M
  (type "M.Shape"
    (ctor "M.Shape.circle" (radius Nat))
    (ctor "M.Shape.rect" (w Nat) (h Nat)))
  (def area ((s (named "M.Shape"))) Nat 0)
)
"#;
    let (rest, module) = parse_module(input).unwrap();
    assert!(rest.trim().is_empty());
    assert_eq!(module.types[0].ctors.len(), 2);
    assert_eq!(module.types[0].ctors[1].fields.len(), 2);
    assert_eq!(
        module.definitions[0].params[0].1,
        Type::Named("M.Shape".to_string())
    );
}

#[test]
fn test_parse_ctor_with_no_fields() {
    let input = r#"(module M (type "M.Unit" (ctor "M.Unit.mk")))"#;
    let (_, module) = parse_module(input).unwrap();
    assert!(module.types[0].ctors[0].fields.is_empty());
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cd rust && cargo test -p prod-ir`
Expected: FAIL — `no field \`types\` on type \`Module\``, `no variant \`Named\``.

- [ ] **Step 3: Add the AST types**

In `rust/prod-ir/src/lib.rs`, add the `Named` variant to `Type` (leave `Instance` in place; Task 7 removes it):

```rust
    /// A type declared in this module's `types` list, by full Lean name.
    /// Renders as a generated Rust struct or enum.
    Named(String),
```

And add the declaration types plus the new `Module` field:

```rust
/// One constructor of a generated type: `(ctor "Full.Name.mk" (field Type)...)`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CtorDecl {
    /// Full Lean constructor name, e.g. `UorAtlas.Instance.mk`.
    pub name: String,
    /// Value fields in declaration order. `Prop` fields are erased by the
    /// exporter and never appear here.
    pub fields: Vec<(String, Type)>,
}

/// A Lean inductive rendered as a Rust type: one ctor means a struct, several
/// mean an enum with named-field variants.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeDecl {
    /// Full Lean type name, e.g. `UorAtlas.Instance`.
    pub name: String,
    pub ctors: Vec<CtorDecl>,
    /// Set when the exporter reached this type but cannot describe it, with
    /// the reason. The type is still declared so that codegen can reject a
    /// reference to it *precisely* rather than reporting a generic unknown
    /// name. `ctors` is empty when this is set.
    pub unsupported: Option<String>,
}
```

```rust
pub struct Module {
    pub name: String,
    /// Type declarations, emitted before the definitions that use them.
    pub types: Vec<TypeDecl>,
    pub definitions: Vec<Definition>,
}
```

- [ ] **Step 4: Add the parser rules**

In `rust/prod-ir/src/parser.rs`, add `(named "...")` to `parse_type`'s `alt` list (place it before the `opaque` arm):

```rust
        map(
            delimited(
                char('('),
                tuple((tag("named"), ws(quoted_ident))),
                char(')'),
            ),
            |(_, n)| Type::Named(n),
        ),
```

Add the declaration parsers above `parse_definition`:

```rust
/// `(name Type)` — one field of a constructor declaration.
fn parse_field(input: &str) -> IResult<&str, (String, Type)> {
    delimited(char('('), tuple((ws(ident), ws(parse_type))), char(')'))(input)
}

/// `(ctor "Full.Name.mk" (field Type)...)`
fn parse_ctor_decl(input: &str) -> IResult<&str, CtorDecl> {
    map(
        delimited(
            char('('),
            tuple((tag("ctor"), ws(quoted_ident), many0(ws(parse_field)))),
            char(')'),
        ),
        |(_, name, fields)| CtorDecl { name, fields },
    )(input)
}

/// `(unsupported "reason")` — a type the exporter reached but cannot describe.
fn parse_unsupported(input: &str) -> IResult<&str, String> {
    delimited(
        char('('),
        map(tuple((tag("unsupported"), ws(quoted_reason))), |(_, r)| r),
        char(')'),
    )(input)
}

/// A double-quoted free-text reason (unlike `quoted_ident`, spaces allowed).
fn quoted_reason(input: &str) -> IResult<&str, String> {
    delimited(
        char('"'),
        map(take_till(|c| c == '"'), String::from),
        char('"'),
    )(input)
}

/// `(type "Full.Name" (ctor ...)...)` or `(type "Full.Name" (unsupported "why"))`
fn parse_type_decl(input: &str) -> IResult<&str, TypeDecl> {
    map(
        delimited(
            char('('),
            tuple((
                terminated(tag("type"), multispace1),
                ws(quoted_ident),
                opt(ws(parse_unsupported)),
                many0(ws(parse_ctor_decl)),
            )),
            char(')'),
        ),
        |(_, name, unsupported, ctors)| TypeDecl {
            name,
            ctors,
            unsupported,
        },
    )(input)
}
```

Add a test for the new form:

```rust
#[test]
fn test_parse_unsupported_type_decl() {
    let input = r#"(module M (type "M.Poly" (unsupported "type parameters")))"#;
    let (_, module) = parse_module(input).unwrap();
    assert_eq!(
        module.types[0].unsupported.as_deref(),
        Some("type parameters")
    );
    assert!(module.types[0].ctors.is_empty());
}
```

Note the `terminated(tag("type"), multispace1)`: a bare `tag("type")` is fine here because no other keyword starts with `type`, but the delimiter guard costs nothing and matches the defensive pattern already used for `le` (see `test_parse_le_does_not_eat_let`).

Update `parse_module` to accept type declarations before definitions, and update the import list to include `CtorDecl, TypeDecl`:

```rust
pub fn parse_module(input: &str) -> IResult<&str, Module> {
    let (rest, (_, name, types, definitions)) = ws(delimited(
        char('('),
        tuple((
            tag("module"),
            ws(ident),
            many0(ws(parse_type_decl)),
            many0(ws(parse_definition)),
        )),
        char(')'),
    ))(input)?;

    Ok((
        rest,
        Module {
            name,
            types,
            definitions,
        },
    ))
}
```

- [ ] **Step 5: Fix every `Module` construction site**

Run: `cd rust && cargo build --workspace`
Expected: errors listing each place that builds a `Module` without `types`. Add `types: Vec::new()` (or `types: alloc::vec::Vec::new()` in `no_std` crates) at each. There is at least one in `parse_module`; the compiler will name the rest.

- [ ] **Step 6: Run the tests**

Run: `cd rust && cargo test -p prod-ir`
Expected: PASS, including the three new tests.

- [ ] **Step 7: Run the full gates and commit**

Run:
```bash
cd rust && cargo test --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check
```
Expected: all green.

```bash
git add rust/prod-ir/src/lib.rs rust/prod-ir/src/parser.rs
git commit -m "IR: type declarations and Type::Named

Adds (type \"Full.Name\" (ctor ...)...) declarations and the (named
\"Full.Name\") type reference to the IR grammar, so a module can carry
the Lean inductives its definitions mention. Additive: Type::Instance
still exists and still parses, so nothing changes behaviour yet.

Fields are (name Type) pairs in declaration order. Prop fields never
appear — the exporter erases them before emitting.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: Render type declarations as Rust structs and enums

**Files:**
- Modify: `rust/prod-codegen/src/lib.rs`
- Modify: `rust/prod-codegen/src/tests.rs`

**Interfaces:**
- Consumes: `prod_ir::{TypeDecl, CtorDecl, Type::Named}` from Task 3.
- Produces:
  - `Error::RecursiveType(String)`, `Error::PolymorphicType(String)`, `Error::UnsupportedFieldType(String)`, `Error::DuplicateTypeName(String)`
  - `fn rust_ident(name: &str) -> String` — raw-identifier-escaping helper used by field and variant rendering.
  - `generate_module` emits type declarations before functions.
  - `Type::Named(n)` renders as `crate::<last component of n>`.

- [ ] **Step 1: Write the failing tests**

Add to `rust/prod-codegen/src/tests.rs`:

```rust
#[test]
fn test_generate_struct_from_single_ctor_type() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
  (def stride ((i (named "UorAtlas.Instance"))) Nat 0)
)
"#;
    let out = generate(ir);
    assert!(out.contains(
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub struct Instance {\n    pub q: u64,\n    pub T: u64,\n    pub O: u64,\n}\n"
    ));
    assert!(out.contains("pub fn stride(i: crate::Instance) -> u64 {"));
}

#[test]
fn test_generate_enum_from_multi_ctor_type() {
    let ir = r#"
(module M
  (type "M.Shape"
    (ctor "M.Shape.circle" (radius Nat))
    (ctor "M.Shape.rect" (w Nat) (h Nat)))
)
"#;
    let out = generate(ir);
    assert!(out.contains(
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub enum Shape {\n    circle { radius: u64 },\n    rect { w: u64, h: u64 },\n}\n"
    ));
}

#[test]
fn test_generate_fieldless_ctor_renders_unit_variant() {
    let ir = r#"
(module M
  (type "M.Flag" (ctor "M.Flag.off") (ctor "M.Flag.on")))
"#;
    let out = generate(ir);
    assert!(out.contains("pub enum Flag {\n    off,\n    on,\n}\n"));
}

#[test]
fn test_rust_keyword_field_names_are_raw_escaped() {
    // A Lean field named `type` or `fn` is legal Lean and illegal Rust.
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (type Nat) (fn Nat))))
"#;
    let out = generate(ir);
    assert!(out.contains("pub r#type: u64"));
    assert!(out.contains("pub r#fn: u64"));
}

#[test]
fn test_recursive_type_is_rejected() {
    let ir = r#"
(module M
  (type "M.Tree"
    (ctor "M.Tree.leaf")
    (ctor "M.Tree.node" (left (named "M.Tree")) (right (named "M.Tree")))))
"#;
    assert_eq!(
        generate_err(ir),
        Error::RecursiveType("M.Tree".to_string())
    );
}

#[test]
fn test_duplicate_last_component_is_rejected() {
    let ir = r#"
(module M
  (type "A.Thing" (ctor "A.Thing.mk" (x Nat)))
  (type "B.Thing" (ctor "B.Thing.mk" (y Nat))))
"#;
    assert_eq!(generate_err(ir), Error::DuplicateTypeName("Thing".to_string()));
}

#[test]
fn test_polymorphic_type_is_rejected_with_its_reason() {
    // The exporter cannot describe a parameterised inductive, so it declares
    // the type as unsupported rather than omitting it — that turns a generic
    // "unknown type" into a rejection that names monomorphization.
    let ir = r#"(module M (type "M.Box" (unsupported "type parameters")))"#;
    assert_eq!(
        generate_err(ir),
        Error::PolymorphicType("M.Box".to_string())
    );
}
```

`Error::OpaqueType` is introduced here (a one-line addition) because `check_field_type` needs it for an undeclared field type. Task 10 wires it to `Type::Opaque`, and Task 7 adds the parameter-position test — parameter types only route through the table once `Type::Instance` is gone, so testing it here would require an `#[ignore]`, and a disabled test is worse than a test that arrives one task later.

- [ ] **Step 2: Run to verify failure**

Run: `cd rust && cargo test -p prod-codegen`
Expected: FAIL — unknown `Error` variants, and no struct/enum in the output.

- [ ] **Step 3: Add the error variants**

In `rust/prod-codegen/src/lib.rs`, extend `Error` and its `Display`:

```rust
    /// A type is defined in terms of itself; needs the tier-1 memory profile.
    RecursiveType(String),
    /// A type takes type parameters; needs monomorphization (S5).
    PolymorphicType(String),
    /// A field's type cannot appear in an allocation-free generated type.
    UnsupportedFieldType(String),
    /// Two Lean types share a last name component, so they would collide.
    DuplicateTypeName(String),
    /// A type reached codegen with no rendering.
    OpaqueType(String),
```

```rust
            Error::RecursiveType(s) => write!(
                f,
                "recursive type `{}` cannot be rendered allocation-free (needs the tier-1 profile)",
                s
            ),
            Error::PolymorphicType(s) => write!(
                f,
                "type `{}` has type parameters; monomorphization is not implemented",
                s
            ),
            Error::UnsupportedFieldType(s) => {
                write!(f, "field type is not allowed in a generated type: {}", s)
            }
            Error::DuplicateTypeName(s) => write!(
                f,
                "two Lean types share the last name component `{}`",
                s
            ),
            Error::OpaqueType(s) => write!(f, "no Rust rendering for type: {}", s),
```

- [ ] **Step 4: Add the identifier helper and the type table**

```rust
/// Rust keywords that a Lean field or constructor name may legitimately be.
/// Escaped with the raw-identifier prefix rather than renamed, so the Rust
/// name still matches the Lean name exactly.
const RUST_KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum",
    "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move",
    "mut", "pub", "ref", "return", "self", "static", "struct", "super", "trait", "true", "type",
    "unsafe", "use", "where", "while", "abstract", "become", "box", "do", "final", "macro",
    "override", "priv", "typeof", "unsized", "virtual", "yield", "try", "gen",
];

/// A Lean identifier as a Rust identifier, raw-escaped if it is a keyword.
fn rust_ident(name: &str) -> String {
    if RUST_KEYWORDS.contains(&name) {
        format!("r#{}", name)
    } else {
        String::from(name)
    }
}

/// Last dot-separated component of a full Lean name.
fn last_component(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// Full Lean type name → its declaration, for the module being rendered.
type TypeTable<'m> = BTreeMap<&'m str, &'m TypeDecl>;

fn type_table<'m>(types: &'m [TypeDecl]) -> Result<TypeTable<'m>, Error> {
    let mut by_full: TypeTable<'m> = BTreeMap::new();
    let mut short_seen: BTreeMap<&'m str, &'m str> = BTreeMap::new();
    for decl in types {
        let short = last_component(&decl.name);
        if let Some(previous) = short_seen.insert(short, &decl.name) {
            if previous != decl.name {
                return Err(Error::DuplicateTypeName(String::from(short)));
            }
        }
        by_full.insert(decl.name.as_str(), decl);
    }
    Ok(by_full)
}
```

- [ ] **Step 5: Render declarations, with eligibility checked**

```rust
/// Render one type declaration: a struct if it has exactly one constructor,
/// otherwise an enum with named-field variants.
///
/// Every generated type is `Copy`, which is what keeps it inside the
/// allocation-free tier: a type is eligible only if every field is a scalar, a
/// tuple of eligible types, or another eligible generated type.
fn generate_type_decl(decl: &TypeDecl, table: &TypeTable) -> Result<String, Error> {
    // The exporter reached this type but could not describe it. It is declared
    // anyway so that the rejection names a reason instead of an unknown type.
    if let Some(reason) = &decl.unsupported {
        return Err(match reason.as_str() {
            "type parameters" => Error::PolymorphicType(decl.name.clone()),
            "recursive" => Error::RecursiveType(decl.name.clone()),
            other => Error::OpaqueType(format!("{} ({})", decl.name, other)),
        });
    }
    for ctor in &decl.ctors {
        for (_, ty) in &ctor.fields {
            check_field_type(ty, &decl.name, table)?;
        }
    }

    let mut out = String::from("#[derive(Debug, Clone, Copy, PartialEq, Eq)]\n");
    let short = last_component(&decl.name);

    if decl.ctors.len() == 1 {
        let ctor = &decl.ctors[0];
        out.push_str(&format!("pub struct {} {{\n", rust_ident(short)));
        for (name, ty) in &ctor.fields {
            out.push_str(&format!(
                "    pub {}: {},\n",
                rust_ident(name),
                type_to_rust(ty)?
            ));
        }
        out.push_str("}\n");
        return Ok(out);
    }

    out.push_str(&format!("pub enum {} {{\n", rust_ident(short)));
    for ctor in &decl.ctors {
        let variant = rust_ident(last_component(&ctor.name));
        if ctor.fields.is_empty() {
            out.push_str(&format!("    {},\n", variant));
            continue;
        }
        let mut fields = Vec::with_capacity(ctor.fields.len());
        for (name, ty) in &ctor.fields {
            fields.push(format!("{}: {}", rust_ident(name), type_to_rust(ty)?));
        }
        out.push_str(&format!("    {} {{ {} }},\n", variant, fields.join(", ")));
    }
    out.push_str("}\n");
    Ok(out)
}

/// A field type must be renderable and must not make the type recursive.
fn check_field_type(ty: &Type, owner: &str, table: &TypeTable) -> Result<(), Error> {
    match ty {
        Type::Named(n) => {
            if n == owner {
                return Err(Error::RecursiveType(String::from(owner)));
            }
            match table.get(n.as_str()) {
                // One level of indirection is enough to catch the mutual case
                // too: B referring back to A makes A reachable from A.
                Some(other) => {
                    for ctor in &other.ctors {
                        for (_, inner) in &ctor.fields {
                            if let Type::Named(m) = inner {
                                if m == owner {
                                    return Err(Error::RecursiveType(String::from(owner)));
                                }
                            }
                        }
                    }
                    Ok(())
                }
                None => Err(Error::OpaqueType(n.clone())),
            }
        }
        // A sequence field would need owned storage, which the allocation-free
        // tier does not have. Lists are supported as borrowed parameters and
        // caller-owned output buffers only, never as owned struct fields.
        Type::List(_) => Err(Error::UnsupportedFieldType(String::from(
            "a list field would need owned storage",
        ))),
        Type::Vec(_) => Err(Error::UnsupportedFieldType(String::from(
            "a vector field would need heap storage",
        ))),
        Type::Tuple(items) => {
            for item in items {
                check_field_type(item, owner, table)?;
            }
            Ok(())
        }
        Type::Option(inner) => check_field_type(inner, owner, table),
        _ => Ok(()),
    }
}
```

- [ ] **Step 6: Wire `Type::Named` into `type_to_rust` and declarations into `generate_module`**

`type_to_rust` has no access to the table, and does not need one — an unknown name is caught by `check_field_type` and by the parameter/return path in Task 7. Add:

```rust
        Type::Named(n) => format!("crate::{}", rust_ident(last_component(n))),
```

And in `generate_module`:

```rust
pub fn generate_module(module: &Module) -> Result<String, Error> {
    let table = type_table(&module.types)?;
    let shapes = signatures(&module.definitions);
    let mut out = String::new();
    for decl in &module.types {
        out.push_str(&generate_type_decl(decl, &table)?);
        out.push('\n');
    }
    for def in &module.definitions {
        out.push_str(&generate_def_in(def, &shapes)?);
        out.push('\n');
    }
    Ok(out)
}
```

- [ ] **Step 7: Run the tests**

Run: `cd rust && cargo test -p prod-codegen`
Expected: PASS, all of them. The parameter-position rejection test lives in Task 7, not here — parameter types only route through the type table once `Type::Instance` is gone.

- [ ] **Step 8: Full gates and commit**

Run: `cd rust && cargo test --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`

```bash
git add rust/prod-codegen/src/lib.rs rust/prod-codegen/src/tests.rs
git commit -m "codegen: render Lean inductives as Rust structs and enums

One constructor becomes a struct, several become an enum with
named-field variants. Every generated type derives Copy, which is what
keeps it in the allocation-free tier: a type is eligible only if every
field is a scalar, a tuple of eligible types, or another eligible
generated type.

Recursive types are rejected rather than boxed — same slices-and-buffers
line the list lowering draws, applied to user data. Field and variant
names that collide with Rust keywords are raw-escaped rather than
renamed, so the Rust name still matches the Lean name.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 5: Lean emits type declarations

**Files:**
- Modify: `lean/Prod/Lower.lean`
- Modify: `lean/Prod/Emit.lean`
- Modify: `lean/Conformance/golden.ir` (regenerated)

**Interfaces:**
- Consumes: the field-name API confirmed in Task 2; `LowerCtx`, `LowerM`, `lowerType` (existing).
- Produces: `Prod.collectTypeDecls : LowerCtx → Array ExtractedDef → CoreM (Array String)` returning rendered `(type ...)` sexps, called by `emitKernelIr` and emitted before the defs.

- [ ] **Step 1: Add type-declaration lowering**

In `lean/Prod/Lower.lean`, after `lowerType`, add. Use whichever field-name API Task 2 recorded in `AGENTS.md` — the shape below assumes `getStructureFields` worked; adjust the two marked lines if Task 2 found otherwise.

```lean
/-- Is this expression a `Prop`? Prop-valued structure fields are erased and
    never reach the IR. Runs in `MetaM` because `isProp` needs the local
    context machinery. -/
def isPropType (e : Expr) : LowerM Bool :=
  liftM (MetaM.run' (Lean.Meta.isProp e))

/-- Render one inductive as an IR `(type ...)` declaration, erasing `Prop`
    fields.

    A type outside the supported fragment is still declared, carrying the
    reason: codegen then rejects a reference to it by name ("needs
    monomorphization") instead of reporting a generic unknown type. Returns
    `none` only when the constant is not an inductive at all. -/
def lowerTypeDecl (typeName : Name) : LowerM (Option String) := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? typeName | return none
  let unsupported? : Option String :=
    if iv.numParams != 0 then some "type parameters"
    else if iv.numIndices != 0 then some "type indices"
    else if iv.all.length != 1 then some "mutual inductive block"
    else if iv.isRec then some "recursive"
    else none
  if let some reason := unsupported? then
    return some s!"(type \"{typeName}\" (unsupported \"{reason}\"))"
  let mut ctorSexps : Array String := #[]
  for ctorName in iv.ctors do
    let some (.ctorInfo cv) := env.find? ctorName | return none
    -- Walk the constructor telescope past the (zero) type params to reach the
    -- value fields, pairing each with its declared name.
    let fieldNames := getStructureFields env typeName          -- ← Task 2 API
    let mut fields : Array String := #[]
    let mut ty := cv.type
    let mut i := 0
    while i < cv.numFields do
      match ty with
      | .forallE _ fieldTy rest _ =>
        if !(← isPropType fieldTy) then
          let nm := match fieldNames[i]? with
            | some n => sanitize n                              -- ← Task 2 API
            | none => s!"field_{i}"
          fields := fields.push s!"({nm} {← lowerType fieldTy})"
        ty := rest
        i := i + 1
      | _ => i := cv.numFields
    ctorSexps := ctorSexps.push s!"(ctor \"{ctorName}\"{spaced fields})"
  return some s!"(type \"{typeName}\"{spaced ctorSexps})"
```

- [ ] **Step 2: Collect the types reachable from tagged definitions**

Also in `Lower.lean`:

```lean
/-- Every named type mentioned in a declaration's parameter or return types.
    Only the head constant matters — parameterised types are out of scope. -/
def declTypeNames (d : Decl .pure) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for p in d.params do
    if let .const n _ := p.type.getAppFn then out := out.push n
  if let .const n _ := (stripForalls d.params.size d.type).getAppFn then
    out := out.push n
  return out
```

In `lean/Prod/Emit.lean`, add the collector and call it from `emitKernelIr`:

```lean
/-- Rendered `(type ...)` declarations for every inductive reachable from the
    extracted definitions' signatures, deduplicated and in sorted order. -/
def collectTypeDecls (ctx : LowerCtx) (extracted : Array ExtractedDef)
    : CoreM (Array String) := do
  let env ← getEnv
  let mut wanted : Array Name := #[]
  for ed in extracted do
    if let some decl := ed.decl? then
      for n in declTypeNames decl do
        -- Builtins already have IR types; only user inductives need declaring.
        if n != ``Nat && n != ``Bool && n != ``Int && n != ``Prod
            && n != ``List && n != ``Option && !wanted.contains n then
          if (env.find? n).isSome && !wanted.contains n then
            wanted := wanted.push n
  let sorted := wanted.qsort fun a b => Name.quickCmp a b == .lt
  let mut out : Array String := #[]
  for n in sorted do
    let (rendered, _) ← (((lowerTypeDecl n).run ctx).run {})
    if let some sexp := rendered then out := out.push sexp
  return out
```

In `emitKernelIr`, emit them right after the module header:

```lean
  let typeDecls ← collectTypeDecls ctx extracted
  for decl in typeDecls do
    ir := ir ++ "\n" ++ indent 2 decl ++ "\n"
```

- [ ] **Step 3: Build and inspect**

Run:
```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
```
Expected: `rust/prod-core/kernel.ir` now opens with

```
  (type "UorAtlas.Instance" (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
```

with **no** `valid` field. If `valid` appears, `isPropType` is not firing — fix before continuing, because Task 7 depends on the field list being exactly the computational fields.

Also confirm `lean/Conformance/golden.ir` now declares `Conformance.MidProp` and `Conformance.NoProp`, and that `MidProp` has exactly `first`, `second`, `third`.

- [ ] **Step 4: Verify the IR still parses**

Run: `cd rust && cargo run -p prod-cli -- parse prod-core/kernel.ir`
Expected: exit 0, module listed.

- [ ] **Step 5: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod`

```bash
git add lean/Prod/Lower.lean lean/Prod/Emit.lean lean/Conformance/golden.ir
git commit -m "Lean: emit (type ...) declarations for reachable inductives

The exporter now declares every user inductive its tagged definitions
mention, with Prop fields erased — UorAtlas.Instance emits q/T/O and
drops its validity proof. Types with parameters, indices, or mutual
blocks are skipped, leaving a dangling (named ...) reference that
codegen rejects, which is the honest failure the milestone wants.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 6: Projections carry field names, not indices

**Files:**
- Modify: `lean/Prod/Lower.lean:195-197` (the `.proj` case)
- Modify: `rust/prod-ir/src/lib.rs` (`Expr::Proj` payload)
- Modify: `rust/prod-ir/src/parser.rs`
- Modify: `rust/prod-codegen/src/lib.rs` (delete `instance_field`)
- Modify: `rust/prod-codegen/src/tests.rs`
- Modify: `lean/Conformance/golden.ir` (regenerated)

**Interfaces:**
- Produces: `Expr::Proj(String, String, Box<Expr>)` — type name, **field name**, value. Grammar becomes `(proj "Type.Name" "field" expr)`.

- [ ] **Step 1: Write the failing codegen test**

Replace `test_generate_instance_projection_and_prod_tuple` in `rust/prod-codegen/src/tests.rs` and add a keyword case:

```rust
#[test]
fn test_generate_projection_uses_field_names() {
    let ir = r#"
(module UorAtlas.Kernel
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
  (def decode ((i (named "UorAtlas.Instance"))) (Tuple Nat (Tuple Nat Nat))
    (ctor "Prod.mk" (proj "UorAtlas.Instance" "q" i)
      (ctor "Prod.mk" (proj "UorAtlas.Instance" "O" i) 1)))
)
"#;
    let out = generate(ir);
    assert!(out.contains("((i).q, ((i).O, 1))"));
}

#[test]
fn test_projection_of_keyword_field_is_raw_escaped() {
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (type Nat)))
  (def get ((r (named "M.Rec"))) Nat (proj "M.Rec" "type" r)))
"#;
    let out = generate(ir);
    assert!(out.contains("(r).r#type"));
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cd rust && cargo test -p prod-codegen`
Expected: FAIL — the parser still expects a numeric index.

- [ ] **Step 3: Change the IR**

In `rust/prod-ir/src/lib.rs`:

```rust
    /// Structure projection: `(proj "TypeName" "fieldName" <expr>)`.
    ///
    /// The field *name*, not an index: the exporter resolves it against Lean's
    /// own structure info, so the declaration and the projection cannot
    /// disagree. An index-based form would need a second table in codegen that
    /// has to be kept in sync, and getting that wrong swaps fields silently.
    Proj(String, String, Box<Expr>),
```

In `rust/prod-ir/src/parser.rs`, change the `proj` rule:

```rust
                map(
                    tuple((
                        tag("proj"),
                        ws(quoted_ident),
                        ws(quoted_ident),
                        ws(parse_expr),
                    )),
                    |(_, ty, field, e)| Expr::Proj(ty, field, Box::new(e)),
                ),
```

Update `test_parse_proj` to the new grammar:

```rust
    #[test]
    fn test_parse_proj() {
        let (rest, expr) = parse_expr(r#"(proj "Pair" "fst" (ctor "Pair" 1 2))"#).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Proj(ty, field, e) => {
                assert_eq!(ty, "Pair");
                assert_eq!(field, "fst");
                assert!(matches!(*e, Expr::Ctor(..)));
            }
            _ => panic!("Expected Proj, got {:?}", expr),
        }
    }
```

- [ ] **Step 4: Change codegen**

In `rust/prod-codegen/src/lib.rs`, delete `instance_field` entirely and replace the `Proj` arm in `render_value_leaf`:

```rust
            Expr::Proj(_, field, e) => {
                Ok(format!("({}).{}", self.value(e)?, rust_ident(field)))
            }
```

Update the `children` function's `Expr::Proj(_, _, e)` pattern — the arity changed but the pattern already ignores the first two elements, so confirm it still compiles.

- [ ] **Step 5: Change the Lean lowerer**

In `lean/Prod/Lower.lean`, replace the `.proj` case of `lowerLetValue` (lines 195-197):

```lean
  | .proj typeName idx struct => do
    let s ← lookupFVar struct
    let env ← getEnv
    -- Resolve the index to a field name here, where the environment is
    -- available. Emitting the index instead would force codegen to keep a
    -- parallel table, and a disagreement between the two swaps fields
    -- silently. See AGENTS.md for the index convention this relies on.
    let fields := getStructureFields env typeName               -- ← Task 2 API
    let field := match fields[idx]? with
      | some n => sanitize n
      | none => s!"field_{idx}"
    return s!"(proj \"{typeName}\" \"{field}\" {s})"
```

**Important:** if Task 2 found that LCNF indices are into the *declared* field list while `getStructureFields` returns declared fields too, this direct lookup is correct. If Task 2 found indices are into the *erased* list, filter `fields` to the non-`Prop` ones before indexing. Use whichever Task 2 recorded.

- [ ] **Step 6: Rebuild, re-export, verify**

Run:
```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
cd rust && cargo test --workspace
```

Inspect `lean/Conformance/golden.ir` for `c_proj_middle_prop`: it must project `first`, `second`, `third` — in that order, by name. This is the case that would have caught a swap.

- [ ] **Step 7: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod && cd rust && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`

```bash
git add lean/Prod/Lower.lean rust/prod-ir/src rust/prod-codegen/src lean/Conformance/golden.ir
git commit -m "Projections carry field names instead of indices

Lower.lean has the environment, so it resolves .proj's index to a field
name at lowering time. That deletes codegen's instance_field table and
removes the class of bugs where the type declaration and the projection
table disagree — which produces silently swapped struct fields rather
than a compile error.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 7: Flip `Instance` to a generated type; delete `coordinate.rs`

**Files:**
- Modify: `lean/Prod/Lower.lean` (`lowerType`: drop the `Instance` special case)
- Modify: `rust/prod-ir/src/lib.rs` (delete `Type::Instance`)
- Modify: `rust/prod-ir/src/parser.rs`
- Modify: `rust/prod-codegen/src/lib.rs`
- Delete: `rust/prod-core/src/coordinate.rs`
- Modify: `rust/prod-core/src/lib.rs`, `rust/prod-core/src/spectral.rs`
- Modify: `rust/prod-core/tests/macro_generation.rs`, `rust/prod-core/tests/no_alloc.rs`

**Interfaces:**
- Produces: `crate::Instance` is now generated from `kernel.ir` with fields `q`, `T`, `O`. `prod_ir::Type::Instance` no longer exists.

- [ ] **Step 1: Remove the `Instance` special case from the Lean lowerer**

In `lean/Prod/Lower.lean`, `lowerType`: delete both `if n == ctx.instanceType then return "Instance"` branches. Any inductive now lowers to `(named "Full.Name")` — including unsupported ones, because Task 5 declares those with a reason and codegen rejects them precisely. Only non-inductives remain opaque:

```lean
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.inductInfo _) => return s!"(named \"{n}\")"
    | _ => opaqueType n
```

Apply the same change to the `e.getAppFn` fallback branch at the end of `lowerType`.

`LowerCtx.instanceType` is now unused; delete the field and its uses in `Emit.lean` (including the two `LowerCtx` literals in `runExport` added by Task 1).

- [ ] **Step 2: Delete `Type::Instance` from the IR and codegen**

Remove the `Instance` variant from `prod_ir::Type`, the `value(Type::Instance, tag("Instance"))` line from `parse_type`, and the `Type::Instance => String::from("crate::Instance")` arm from `type_to_rust`. The compiler will point at every remaining use.

Update `rust/prod-codegen/src/tests.rs`: every fixture using `Instance` as a type becomes a `(type "UorAtlas.Instance" ...)` declaration plus `(named "UorAtlas.Instance")`, and field accesses use names. Work through the failures the test run reports.

- [ ] **Step 3: Delete `coordinate.rs` and rewire `prod-core`**

```bash
git rm rust/prod-core/src/coordinate.rs
```

In `rust/prod-core/src/lib.rs`, remove `pub mod coordinate;` and `pub use coordinate::Instance;`. `Instance` now comes from the `prod_defs!` expansion at the crate root, so nothing needs re-exporting.

In `rust/prod-core/src/spectral.rs`, change `use crate::coordinate::Instance;` to `use crate::Instance;` and rename every `inst.t` → `inst.T` and `inst.o` → `inst.O`. Add a module-level note:

```rust
//! Hand-written analysis support. Unlike everything else in this crate, this
//! module is NOT downstream of Lean — `SpectralOperator` has no `@[prod]`
//! counterpart yet. Port it to Lean and delete this file when it does.
```

- [ ] **Step 4: Update the tests to the generated field names**

In both `rust/prod-core/tests/macro_generation.rs` and `rust/prod-core/tests/no_alloc.rs`, every `Instance { q: 4, t: 3, o: 8 }` becomes `Instance { q: 4, T: 3, O: 8 }`. The loop bounds in `generated_definitions_roundtrip_lean_examples` use `inst.t` and `inst.o` — update those to `inst.T` and `inst.O`.

- [ ] **Step 5: Add the parameter-position rejection test**

Parameter types only route through the type table now that `Type::Instance` is gone, so this test can be written here and pass on arrival. Add to `rust/prod-codegen/src/tests.rs`:

```rust
#[test]
fn test_undeclared_named_type_in_a_signature_is_rejected() {
    let ir = r#"(module M (def f ((x (named "M.Nope"))) Nat 0))"#;
    assert!(matches!(generate_err(ir), Error::OpaqueType(_)));
}
```

If it does not fail correctly, thread `&TypeTable` through `param_type_to_rust` and `generate_def_in` so an undeclared name is caught, and record the signature change in the task report.

- [ ] **Step 6: Rebuild everything**

Run:
```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
cd rust && cargo test --workspace
```
Expected: green. `cargo run -p prod-cli -- gen prod-core/kernel.ir` should now print a `pub struct Instance { pub q: u64, pub T: u64, pub O: u64 }` ahead of the functions.

- [ ] **Step 7: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod && cd rust && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`

```bash
git add -A
git commit -m "Instance is generated; delete coordinate.rs

Instance stops being special. Type::Instance, LowerCtx.instanceType and
the crate::Instance hand-written struct are all gone — Lean declares the
inductive, codegen renders the struct, and the proof field is erased on
the way through.

coordinate.rs is deleted outright: it hand-duplicated stride,
class_count, belt, class_index and class_decode, which kernel.ir has
generated since M4, so the copies were dead code and a live risk of
drifting from Lean. spectral.rs stays and is now marked as the one
module in prod-core that is not downstream of Lean.

Field names come from Lean, so tests move from { q, t, o } to { q, T, O }.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 8: Named construction and enum patterns

**Files:**
- Modify: `rust/prod-codegen/src/lib.rs`
- Modify: `rust/prod-codegen/src/tests.rs`

**Interfaces:**
- Consumes: `TypeTable` from Task 4.
- Produces: `Renderer` gains a `types: &'s TypeTable<'m>` field; `(ctor "Full.Name.mk" args...)` renders named-field construction and `cases` renders enum patterns.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn test_generate_named_struct_construction() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))
  (def mk ((a Nat) (b Nat) (c Nat)) (named "UorAtlas.Instance")
    (ctor "UorAtlas.Instance.mk" a b c)))
"#;
    let out = generate(ir);
    assert!(out.contains("crate::Instance { q: a, T: b, O: c }"));
}

#[test]
fn test_generate_enum_construction_and_patterns() {
    let ir = r#"
(module M
  (type "M.Shape"
    (ctor "M.Shape.circle" (radius Nat))
    (ctor "M.Shape.rect" (w Nat) (h Nat)))
  (def area ((s (named "M.Shape"))) Nat
    (cases s
      (alt "M.Shape.circle" (r) r)
      (alt "M.Shape.rect" (w h) (mul w h))))
  (def unit ((r Nat)) (named "M.Shape") (ctor "M.Shape.circle" r)))
"#;
    let out = generate(ir);
    assert!(out.contains("crate::Shape::circle { radius: r } => r,"));
    assert!(out.contains("crate::Shape::rect { w: w, h: h } =>"));
    assert!(out.contains("crate::Shape::circle { radius: r }"));
}

#[test]
fn test_ctor_arity_mismatch_is_an_error() {
    let ir = r#"
(module M
  (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat)))
  (def f ((x Nat)) (named "M.Pair") (ctor "M.Pair.mk" x)))
"#;
    assert!(matches!(generate_err(ir), Error::UnsupportedFieldType(_)));
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cd rust && cargo test -p prod-codegen`
Expected: FAIL — ctors still render tuple-style.

- [ ] **Step 3: Thread the type table into the renderer**

Add `types: &'s TypeTable<'m>` to `Renderer`, build it once in `generate_module`, and pass it to `generate_def_in`. `generate_def` (the single-definition entry point) passes an empty table — document that named types are unavailable there, matching how it already treats cross-definition fallibility.

Add a lookup that finds a constructor by its full name across all declared types:

```rust
impl<'m> Renderer<'_, 'm> {
    /// The declaration of a constructor, by its full Lean name.
    fn ctor_decl(&self, name: &str) -> Option<(&'m TypeDecl, &'m CtorDecl)> {
        self.types.values().find_map(|decl| {
            decl.ctors
                .iter()
                .find(|c| c.name == name)
                .map(|c| (*decl, c))
        })
    }
}
```

- [ ] **Step 4: Render named construction**

In `render_value_leaf`'s `Expr::Ctor` arm, check the table *before* the existing special cases fall through to tuple-style rendering (but after `Prod.mk`, `Bool.*` and `Option.*`, which stay special):

```rust
                } else if let Some((decl, cdecl)) = self.ctor_decl(name) {
                    if args.len() != cdecl.fields.len() {
                        return Err(Error::UnsupportedFieldType(format!(
                            "`{}` takes {} field(s) but got {} argument(s)",
                            name,
                            cdecl.fields.len(),
                            args.len()
                        )));
                    }
                    let path = if decl.ctors.len() == 1 {
                        format!("crate::{}", rust_ident(last_component(&decl.name)))
                    } else {
                        format!(
                            "crate::{}::{}",
                            rust_ident(last_component(&decl.name)),
                            rust_ident(last_component(&cdecl.name))
                        )
                    };
                    if cdecl.fields.is_empty() {
                        Ok(path)
                    } else {
                        let mut bound = Vec::with_capacity(args.len());
                        for ((field, _), arg) in cdecl.fields.iter().zip(args.iter()) {
                            bound.push(format!("{}: {}", rust_ident(field), arg));
                        }
                        Ok(format!("{} {{ {} }}", path, bound.join(", ")))
                    }
                }
```

- [ ] **Step 5: Render enum patterns**

In `render_match`, before the final fallback arms, add a table-driven case. The alt's binders are positional, so zip them against the declared field names:

```rust
                // A declared constructor whose binder count disagrees with its
                // declared field count is an error, symmetric with the
                // construction side. Amended mid-execution: this originally
                // fell through to the positional fallback, which emits
                // `M.Shape.circle(r, extra)` — a dotted name used as a Rust
                // path, which does not compile. A milestone whose thesis is
                // "reject precisely rather than emit code that cannot compile"
                // cannot keep a path that does exactly that. An UNDECLARED
                // constructor still falls through untouched: that is how
                // `Nat.succ`, the List slice patterns, and the Bool/Option
                // arms continue to work.
                _ => match self.ctor_decl(&alt.ctor) {
                    Some((_, cdecl)) if alt.binders.len() != cdecl.fields.len() => {
                        return Err(Error::UnsupportedFieldType(format!(
                            "`{}` declares {} field(s) but the match arm binds {}",
                            alt.ctor,
                            cdecl.fields.len(),
                            alt.binders.len()
                        )))
                    }
                    Some((decl, cdecl)) => {
                        let path = if decl.ctors.len() == 1 {
                            format!("crate::{}", rust_ident(last_component(&decl.name)))
                        } else {
                            format!(
                                "crate::{}::{}",
                                rust_ident(last_component(&decl.name)),
                                rust_ident(last_component(&cdecl.name))
                            )
                        };
                        if cdecl.fields.is_empty() {
                            format!("        {} => {},\n", path, body)
                        } else {
                            let mut bound = Vec::with_capacity(alt.binders.len());
                            for ((field, _), binder) in
                                cdecl.fields.iter().zip(alt.binders.iter())
                            {
                                bound.push(format!("{}: {}", rust_ident(field), binder));
                            }
                            format!(
                                "        {} {{ {} }} => {},\n",
                                path,
                                bound.join(", "),
                                body
                            )
                        }
                    }
                    _ if alt.binders.is_empty() => {
                        format!("        {} => {},\n", alt.ctor, body)
                    }
                    _ => format!(
                        "        {}({}) => {},\n",
                        alt.ctor,
                        alt.binders.join(", "),
                        body
                    ),
                },
```

- [ ] **Step 6: Run tests, gates, commit**

Run: `cd rust && cargo test --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`

```bash
git add rust/prod-codegen/src
git commit -m "codegen: named-field construction and enum patterns

Constructors and match arms stop being positional. A ctor application
renders crate::Instance { q: a, T: b, O: c }, and cases on a
multi-constructor type renders a real enum pattern instead of a bare
ctor name that only compiled if a matching enum had been hand-written.

Arity mismatches between an application and its declaration are an
error rather than a truncated rendering.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 9: Unresolved calls become an error

The first of the two rejection tasks. Nothing before this point changes what is accepted.

**Files:**
- Modify: `lean/Prod/Lower.lean:210-215`
- Modify: `rust/prod-ir/src/lib.rs`, `rust/prod-ir/src/parser.rs`
- Modify: `rust/prod-codegen/src/lib.rs`, `rust/prod-codegen/src/tests.rs`
- Modify: `rust/prod-cli/src/main.rs` (the `Validate` subcommand)

**Interfaces:**
- Produces: `Expr::Extern(String, Vec<Expr>)`, grammar `(extern "Full.Lean.Name" args...)`; `Error::UnresolvedCall(String)`.

- [ ] **Step 1: Write the failing tests**

In `rust/prod-ir/src/parser.rs` tests:

```rust
    #[test]
    fn test_parse_extern() {
        let (rest, expr) = parse_expr(r#"(extern "Foo.bar" 1 2)"#).unwrap();
        assert!(rest.is_empty());
        match expr {
            Expr::Extern(name, args) => {
                assert_eq!(name, "Foo.bar");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Extern, got {:?}", expr),
        }
    }
```

In `rust/prod-codegen/src/tests.rs`:

```rust
#[test]
fn test_extern_call_is_rejected_not_emitted() {
    // Before this, an untagged callee still rendered as a plain Rust call to a
    // function nobody defined, and the failure surfaced far away in rustc.
    let ir = r#"(module M (def f ((x Nat)) Nat (extern "Foo.helper" x)))"#;
    assert_eq!(
        generate_err(ir),
        Error::UnresolvedCall("Foo.helper".to_string())
    );
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cd rust && cargo test -p prod-ir -p prod-codegen`
Expected: FAIL — no `Extern` variant.

- [ ] **Step 3: Add the IR node**

In `rust/prod-ir/src/lib.rs`:

```rust
    /// A call the exporter could not resolve: the callee is neither
    /// `@[prod]`-tagged nor on the operator whitelist. Deliberately distinct
    /// from `Call` so codegen rejects it instead of emitting a Rust call to a
    /// function that does not exist.
    Extern(String, Vec<Expr>),
```

In `parser.rs`, add to the second `alt` group:

```rust
                map(
                    tuple((tag("extern"), ws(quoted_ident), many0(ws(parse_expr)))),
                    |(_, name, args)| Expr::Extern(name, args),
                ),
```

Add `Expr::Extern(_, args)` to the `children` function's `Call | Ctor | Jmp` arm in `prod-codegen`.

- [ ] **Step 4: Reject it in codegen**

Add the variant and `Display` arm:

```rust
    /// The exporter could not resolve a callee to a generated definition.
    UnresolvedCall(String),
```

```rust
            Error::UnresolvedCall(s) => write!(
                f,
                "`{}` is neither @[prod]-tagged nor a whitelisted operator, so there is nothing to call",
                s
            ),
```

In `render`, before the catch-all:

```rust
            Expr::Extern(name, _) => Err(Error::UnresolvedCall(name.clone())),
```

- [ ] **Step 5: Emit it from Lean**

In `lean/Prod/Lower.lean`, `lowerLetValue`'s `.const` case, replace the final `none` branch (lines 210-215):

```lean
    | none =>
      if (← read).tagged.contains declName then
        return s!"(call {lastComponent declName}{spaced args'})"
      modify fun st => { st with externs := st.externs.push (toString declName) }
      -- Emit a distinct node rather than a `call`: codegen must refuse this,
      -- not render a Rust call to a function nobody generated.
      return s!"(extern \"{declName}\"{spaced args'})"
```

- [ ] **Step 6: Make `prod validate` report the whole set**

In `rust/prod-cli/src/main.rs`, the `Validate` arm currently counts opaque bodies. Extend it to walk every expression and collect `Extern` names, so a developer sees the complete list in one run rather than one error at a time:

```rust
                    let mut unresolved: Vec<String> = Vec::new();
                    for def in &module.definitions {
                        collect_externs(&def.body, &mut unresolved);
                    }
                    unresolved.sort();
                    unresolved.dedup();
                    if !unresolved.is_empty() {
                        println!("✗ {} unresolved call(s):", unresolved.len());
                        for name in &unresolved {
                            println!("    {}", name);
                        }
                        std::process::exit(1);
                    }
```

with a helper in the same file:

```rust
/// Collect every unresolved callee name reachable from an expression.
fn collect_externs(expr: &prod_ir::Expr, out: &mut Vec<String>) {
    if let prod_ir::Expr::Extern(name, _) = expr {
        out.push(name.clone());
    }
    // `prod_ir` does not expose a child iterator, so match the recursive
    // shapes this command needs to see through.
    match expr {
        prod_ir::Expr::Let(_, v, b) => {
            collect_externs(v, out);
            collect_externs(b, out);
        }
        prod_ir::Expr::If(c, t, f) => {
            collect_externs(c, out);
            collect_externs(t, out);
            collect_externs(f, out);
        }
        prod_ir::Expr::Match { scrut, alts, default } => {
            collect_externs(scrut, out);
            for alt in alts {
                collect_externs(&alt.body, out);
            }
            if let Some(d) = default {
                collect_externs(d, out);
            }
        }
        prod_ir::Expr::Call(_, args)
        | prod_ir::Expr::Ctor(_, args)
        | prod_ir::Expr::Extern(_, args) => {
            for a in args {
                collect_externs(a, out);
            }
        }
        _ => {}
    }
}
```

- [ ] **Step 7: Re-export and check nothing legitimate trips**

Run:
```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake exe prod-export
cd rust && cargo run -p prod-cli -- validate prod-core/kernel.ir
```
Expected: no unresolved calls. If any appear, they are genuine gaps — either whitelist the operator in `opWhitelist`, tag the callee `@[prod]`, or record the gap in the design doc's roadmap before proceeding.

- [ ] **Step 8: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod && cd rust && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`

```bash
git add -A
git commit -m "Unresolved calls are an error, not a rendered call

Lower.lean emitted (call name ...) even when it had just recorded the
callee as an extern, so codegen rendered a Rust call to a function
nobody generated and the failure surfaced far away inside rustc. It now
emits a distinct (extern ...) node that codegen refuses, naming the Lean
constant.

prod validate reports the whole set at once, so a developer sees every
gap in one run instead of one error at a time.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 10: Opaque types are an error

**Files:**
- Modify: `rust/prod-codegen/src/lib.rs`, `rust/prod-codegen/src/tests.rs`

**Interfaces:**
- Consumes: `Error::OpaqueType` from Task 4.
- Produces: `Type::Opaque` no longer renders.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn test_opaque_type_is_rejected_not_injected() {
    // Previously rendered the raw Lean name as a Rust type, which exploded
    // inside syn::parse_str with an error pointing nowhere near the cause.
    let ir = r#"(module M (def f ((x (opaque "Foo.Bar"))) Nat 0))"#;
    assert_eq!(generate_err(ir), Error::OpaqueType("Foo.Bar".to_string()));
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cd rust && cargo test -p prod-codegen test_opaque_type_is_rejected`
Expected: FAIL — currently succeeds and emits `Foo.Bar` as a type.

- [ ] **Step 3: Reject it**

In `type_to_rust`, replace the `Type::Opaque(s) => s.clone()` arm:

```rust
        Type::Opaque(s) => return Err(Error::OpaqueType(s.clone())),
```

- [ ] **Step 4: Run tests**

Run: `cd rust && cargo test --workspace`
Expected: PASS. If any existing fixture used an opaque type as a stand-in, convert it to a declared `(type ...)` or delete it.

- [ ] **Step 5: Reject a projection naming a field the type does not declare**

Added mid-execution, because Task 6 shipped an IR in which `(type "UorAtlas.Instance" ... (T Nat) (O Nat))` coexisted with `(proj "UorAtlas.Instance" "t" ...)` — the declaration and the projection disagreeing inside one file, which is the exact failure the field-name lowering exists to prevent. Every gate passed, because a transitional guard suppressed the generated struct so the projections resolved against a hand-written type. Nothing in the pipeline checks that the IR is internally consistent; this step adds that check.

Write the failing test first, in `rust/prod-codegen/src/tests.rs`:

```rust
#[test]
fn test_projection_of_an_undeclared_field_is_rejected() {
    // A projection must name a field its type actually declares. Without this,
    // a declaration and a projection can disagree inside one IR file and still
    // compile, as long as something else supplies a type with the other
    // spelling.
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (alpha Nat)))
  (def f ((r (named "M.Rec"))) Nat (proj "M.Rec" "beta" r)))
"#;
    assert_eq!(
        generate_err(ir),
        Error::UnknownField("M.Rec".to_string(), "beta".to_string())
    );
}

#[test]
fn test_projection_of_a_declared_field_still_renders() {
    let ir = r#"
(module M
  (type "M.Rec" (ctor "M.Rec.mk" (alpha Nat)))
  (def f ((r (named "M.Rec"))) Nat (proj "M.Rec" "alpha" r)))
"#;
    assert!(generate(ir).contains("(r).alpha"));
}
```

Run `cd rust && cargo test -p prod-codegen` and confirm the first fails before implementing.

Add the error variant and its `Display` arm:

```rust
    /// A projection names a field the declared type does not have. Catches a
    /// declaration and a projection disagreeing within one IR file.
    UnknownField(String, String),
```

```rust
            Error::UnknownField(ty, field) => write!(
                f,
                "type `{}` declares no field `{}`",
                ty, field
            ),
```

Enforce it in the `Proj` arm of `render_value_leaf`. A projection on a type this module does not declare stays permissive — the type may be supplied by the host crate, which is how `Instance` worked before it was generated:

```rust
            Expr::Proj(ty, field, e) => {
                if let Some(decl) = self.types.get(ty.as_str()) {
                    let declared = decl
                        .ctors
                        .iter()
                        .any(|c| c.fields.iter().any(|(name, _)| name == field));
                    if !declared {
                        return Err(Error::UnknownField(ty.clone(), field.clone()));
                    }
                }
                Ok(format!("({}).{}", self.value(e)?, rust_ident(field)))
            }
```

This needs `self.types`, which Task 8 also threads into `Renderer`. If Task 8 has not landed, thread it here and note it in the report so Task 8 does not duplicate the work.

Run `cd rust && cargo test -p prod-codegen` again: both new tests pass, nothing else regresses.

- [ ] **Step 6: Gates and commit**

Run: `cd rust && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`

```bash
git add rust/prod-codegen/src
git commit -m "Opaque types are a codegen error

Type::Opaque rendered its payload as a Rust type, injecting a raw Lean
name like UorAtlas.Foo into the token stream and failing inside
syn::parse_str with an error pointing nowhere near the cause. It now
fails as Error::OpaqueType, symmetric with the existing Expr::Opaque
handling.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

---

### Task 11: Generated subset contract

**Files:**
- Modify: `lean/Prod/Coverage.lean` (or a new `lean/Prod/Subset.lean`), `lean/Prod/Emit.lean`
- Modify: `rust/prod-cli/src/main.rs`
- Create: `specs/lean-for-production.md` (generated, committed)
- Modify: `justfile`, `.gitignore`

**Interfaces:**
- Produces: `subset.json` (generated, gitignored), `prod subset <subset.json>` writing markdown to stdout or `--output`, `just subset` and `just subset-check`.

- [ ] **Step 1: Emit `subset.json` from the exporter**

Add to `lean/Prod/Emit.lean` a renderer that reports what `Lower.lean` can lower. Hand-rolled JSON, no dependencies, matching how `rootsJson` is built:

```lean
/-- Machine-readable description of the Lean-side lowering surface, consumed by
    `prod subset` to render the published contract. Hand-rolled JSON (no deps),
    same as `rootsJson`. -/
def subsetJson : String :=
  let ops := ["Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod",
              "Nat.shiftLeft", "Nat.pow"]
  let deciders := ["Nat.decLt", "Nat.decLe", "Nat.decEq", "instDecidableEqNat"]
  let types := ["Nat", "Bool", "Int", "Prod", "List", "Option",
                "parameterless single inductives"]
  let quoted (xs : List String) : String :=
    String.intercalate ", " (xs.map fun s => s!"\"{s}\"")
  s!"\{\n  \"operators\": [{quoted ops}],\n  \"deciders\": [{quoted deciders}],\n  \"types\": [{quoted types}]\n\}\n"
```

Keep these lists **derived from the same definitions the lowerer uses** where possible — if `opWhitelist` is a match on names, extract the name list into a `def natOpNames : List Name` that both `opWhitelist` and `subsetJson` consume, so they cannot drift. Do that refactor as part of this step.

Write it from `main` alongside the other outputs, defaulting to `../subset.json`.

- [ ] **Step 2: Gitignore the generated JSON**

Add `subset.json` to `.gitignore` next to the other generated artifacts.

- [ ] **Step 3: Add the `prod subset` subcommand**

In `rust/prod-cli/src/main.rs`, add to `Commands`:

```rust
    /// Render the published Lean-for-production subset contract.
    Subset {
        /// Path to subset.json, written by prod-export
        path: String,
        /// Output path for the rendered markdown
        #[arg(short, long)]
        output: Option<String>,
    },
```

Implement it by deserializing the JSON and rendering markdown that merges the Lean half with codegen's rejection list:

```rust
#[derive(Debug, serde::Deserialize)]
struct SubsetFile {
    operators: Vec<String>,
    deciders: Vec<String>,
    types: Vec<String>,
}

/// Render the published subset contract. Generated, never hand-written: a
/// hand-maintained contract drifts from the implementation, and a drifted
/// contract is worse than none.
fn render_subset(subset: &SubsetFile) -> String {
    let mut out = String::from(
        "# Lean-for-production: the supported subset\n\n\
         <!-- GENERATED by `just subset`. Do not edit by hand. -->\n\n\
         This is the fragment of Lean 4 that `prod-export` lowers and\n\
         `prod-codegen` renders. Anything outside it is rejected with the\n\
         named error rather than silently mis-compiled.\n\n\
         ## Types\n\n",
    );
    for t in &subset.types {
        out.push_str(&format!("- `{}`\n", t));
    }
    out.push_str("\n## Operators\n\n");
    for op in &subset.operators {
        out.push_str(&format!("- `{}`\n", op));
    }
    out.push_str("\n## Decidable guards\n\n");
    for d in &subset.deciders {
        out.push_str(&format!("- `{}`\n", d));
    }
    out.push_str("\n## Rejections\n\nEverything else fails, precisely:\n\n| Error | Cause |\n|---|---|\n");
    for (variant, cause) in prod_codegen::REJECTIONS {
        out.push_str(&format!("| `{}` | {} |\n", variant, cause));
    }
    out
}
```

The rejection list lives in `prod-codegen`, next to the `Error` enum it describes, so the two stay together:

```rust
// in prod-codegen/src/lib.rs
/// The rejections the generator makes, for the published subset contract.
/// Keep in step with `Error`; the contract is rendered from this.
pub const REJECTIONS: &[(&str, &str)] = &[
    ("UnresolvedCall", "callee is neither @[prod]-tagged nor a whitelisted operator"),
    ("OpaqueType", "a type with no Rust rendering"),
    ("RecursiveType", "inductive refers to itself; needs the tier-1 profile"),
    ("PolymorphicType", "inductive has type parameters; needs monomorphization"),
    ("UnsupportedFieldType", "a field type not allowed in a generated type"),
    ("DuplicateTypeName", "two Lean types share a last name component"),
    ("UnsupportedList", "a list value outside a supported position"),
    ("HeapType", "a type that would require a heap allocation"),
    ("OpaqueExpr", "an expression with no Rust rendering"),
    ("ParamOutOfBounds", "a parameter index outside the definition's list"),
];
```

- [ ] **Step 4: Add the just lanes and generate the contract**

```make
# The published subset contract is generated from the implementation, so it
# cannot describe a fragment the code does not implement.
subset:
    cd rust && cargo run -p prod-cli -- subset ../subset.json --output ../specs/lean-for-production.md

subset-check: subset
    git diff --exit-code specs/lean-for-production.md
```

Add `subset-check` to the `prod` recipe.

Run `just subset` and **read the generated document**. It must not claim anything the conformance suite does not cover.

- [ ] **Step 5: Full gates and commit**

Run: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod && cd rust && cargo clippy --all-targets -- -D warnings && cargo fmt --all -- --check`

```bash
git add -A
git commit -m "Generate the published Lean-for-production subset contract

The subset document is rendered from the implementation rather than
maintained by hand, for the same reason coverage.md is computed by
Lean's own shouldGenerateCode: a hand-written contract drifts, and a
drifted contract is worse than none. The exporter describes the Lean
half in subset.json, prod-cli merges it with codegen's rejection list,
and CI diffs the rendered markdown.

A feature cannot appear in the contract unless both halves implement it.

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
Expected: all green, and `git status` clean — a dirty `lean/Conformance/golden.ir` or `specs/lean-for-production.md` means an unreviewed change slipped through.

- [ ] **Update `AGENTS.md`**

Add a status entry recording: `Instance` is generated, `coordinate.rs` is gone, projections carry field names, unresolved calls and opaque types are hard errors, and the conformance golden plus subset contract are the two committed generated artifacts with their bless workflows.

- [ ] **Update the design doc status**

Mark `specs/designs/2026-08-08-lean-for-production-coverage.md` S0 and S1 as implemented, with any deviations recorded the way the best-practices plan did.
