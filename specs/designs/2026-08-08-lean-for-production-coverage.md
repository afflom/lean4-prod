# Design: Lean-for-production coverage — honest boundary + generated types

**Date:** 2026-08-08
**Status:** Approved design. Implementation plan to follow.
**Scope:** Milestone S0 + S1 of the coverage roadmap below.

## Why this exists

The question that started this: "how do we get to full coverage over Lean 4 —
can we read the Lean 4 grammar and generate production code from it?"

The grammar is the wrong layer, and the project already has a better one.
Lean 4's surface syntax is user-extensible (`syntax`, `macro`, `notation`,
custom elaborators), so there is no fixed grammar to enumerate; any parser is
obsolete as soon as a user writes a DSL. This project extracts from **LCNF**
instead — post-elaboration, post-erasure — where `Code` has exactly seven
constructors, all seven of which `lean/Prod/Lower.lean` already handles.
Coverage of Lean *syntax* is therefore already complete and stays complete as
Lean grows, because Lean's own elaborator does the work. Building a
grammar-driven front end would be a large regression.

The real gaps are in the **value and type surface**, not the code shape:

- `lowerType` maps only `Nat`, `Bool`, `Int`, `Prod`, `List`, `Option`, and one
  hard-wired `Instance` name. Everything else becomes `opaque`: user inductives
  and structures, `String`, `Array`, `Float`, `UInt*`, `Fin`, `Subtype`, `Sum`,
  function types, and type variables.
- Type arguments are silently dropped by `lowerArgs`, so there is no
  polymorphism story at all.
- `Code.fun` lowers to `opaque`: no closures, so no higher-order code.
- Operators are Nat-only. `.lit (.nat n)` is the only literal; string literals
  are opaque.
- An untagged callee still emits `(call name ...)` (`Lower.lean:214`), so
  codegen renders a Rust call to a function nobody defined. It is *recorded* in
  `coverage.md` but not *rejected*.
- `Instance` is hard-wired in three places (IR `Type::Instance`, codegen's
  `instance_field` table, a hand-written struct in `prod-core`). There is no
  Lean-inductive-to-Rust-type generator, so `cases` on a user type emits
  patterns that only compile if a matching enum was hand-written.
- `Lower.lean` has **no tests**. The entire Lean half of the pipeline is
  verified only by the one example kernel happening to work.

## Decisions

Four decisions frame everything below.

**1. Tiered memory profiles.** Allocation-free stays the default and the only
provably heapless tier. Higher tiers (caller-supplied arena, then full `alloc`)
are opt-in and selected per `@[prod]` definition or per build. Coverage grows
as you opt in; tier 0 keeps its `no_alloc` certification. The tier mechanism
itself is *not* built in this milestone — it is built when a scheduled
subsystem needs it.

**2. Coverage means a published subset, not all of Lean.** The deliverable is
"Lean-for-production": an explicit set of types and features that are IN, each
with a conformance test, and a precise rejection for everything else. Coverage
becomes a checkable contract that grows deliberately.

**3. Rust types are generated from Lean inductives.** The hard-wired `Instance`
coupling is deleted; `Instance` becomes just another generated type. This
honours the repo's "nothing hand-written downstream of Lean" rule and is the
keystone that unblocks user-defined data.

**4. `prod-core` sheds what Lean now owns.** `coordinate.rs` is deleted
outright — `Instance`, `stride`/`class_count`/`belt`, and
`class_index`/`class_decode` are all generated now, and keeping hand-written
copies is both dead code and a live risk of the two drifting apart.
`spectral.rs` has no Lean counterpart, so it stays, explicitly marked as
hand-written analysis support that is *not* downstream of Lean.

## Goals

- No construct can reach generated Rust without a rendering. Failures are
  precise codegen or export errors naming the Lean constant responsible.
- Lean structures and non-recursive inductives generate Rust types, with the
  hard-wired `Instance` path deleted.
- `Lower.lean` gains its first tests.
- The subset contract is generated from the implementation, not hand-written.

## Non-goals

Written down so that scope creep is a decision rather than a drift.

- **No general-purpose Lean backend.** Not competing with Lean's C backend. The
  differentiator is generated Rust that provably does not panic or allocate,
  with computed coverage and proof-graph metadata — breadth dilutes it.
- **No grammar or surface-syntax front end, ever.** LCNF is the extraction
  point, permanently.
- **`String`, `Array`, closures, and recursive inductives (S4/S6/S7) are not
  scheduled** and may never be. Tier 1+ exists as a concept; its mechanism is
  only built when something earns it.
- **No polymorphism** in this milestone (S5).
- **No data-parallel output in this milestone.** It is scheduled as S8 (see
  below), not built here.
- `roots.json` and the proof-graph analysis are untouched.
- No change to the *generated-code* error contract (`ComputeError`) or the
  memory profile established by
  `specs/plans/2026-08-06-best-practices-alignment.md`. This milestone does add
  variants to `prod_codegen::Error`, which is the compile-time codegen error
  type and a different thing entirely.

## Roadmap context

Each row is its own spec → plan → implementation cycle. This document covers
S0 and S1 only.

| | Subsystem | Tier | Unblocks |
|---|---|---|---|
| S0 | Honest boundary: precise rejection, generated subset contract, conformance suite | 0 | every coverage claim |
| S1 | Generated types: Lean inductives → Rust structs/enums | 0 (non-recursive) | user-defined data |
| S2 | Scalar completeness: typed `Int`, `Bool` connectives, `UInt8/16/32/64`, `Fin` | 0 | most real kernel code |
| S3 | Profile mechanism: tiers in the IR, per-definition selection | — | everything below |
| S4 | Sequences and strings: `Array`, `String` | 1+ | not scheduled |
| S5 | Polymorphism: monomorphize at export | 0 | generic definitions |
| S6 | Closures: `Code.fun` | 0/1 | not scheduled |
| S7 | Recursive inductives and general recursion | 1+ | not scheduled |
| S8 | Proof-carrying data parallelism | 0 | parallel generated output |

S2 is the most likely next milestone: it is what real kernels hit first and it
is entirely inside tier 0.

### S8 — proof-carrying data parallelism (scheduled, after S1)

Promoted from "principles recorded only" to scheduled work. It cannot come
before S1: parallel output needs somewhere to write results, the only heapless
answer is the caller-owned `&mut [T]` discipline the list lowering already
established, and that is only worth more than `u64`-sized work once element
types exist.

The design commitment that makes this defensible rather than a heuristic: the
generator does not *infer* that a traversal is parallelisable. Lean **proves**
the elementwise independence or the associativity of the fold, and that proof
is the licence to emit the chunked form. The proof obligation is discharged on
the Lean side and recorded in `roots.json` like any other root, so the parallel
lowering inherits the project's existing evidence story.

The runtime shape stays inside tier 0 and follows the standard's parallelism
rules directly:

- Input `&[T]`, output `&mut [U]`, split with `split_at_mut` into disjoint
  chunks. No allocation: chunks are sub-slices.
- Bounded worker count fixed at the call site. No unbounded queues.
- Each worker writes only its own index range, so the output is bit-identical
  regardless of scheduling — canonical bytes never depend on thread interleaving.

Open questions for that spec, not this one: which Lean surface signals the
intent (an `@[prod parallel]` attribute carrying the independence proof is the
current favourite over inferring map/fold shapes from LCNF), whether the
threading primitive is generated or supplied by the caller, and how it composes
with S5's monomorphisation.

## S0 — The honest boundary

Keep the existing layering: **Lean describes faithfully, Rust refuses to
generate what it cannot render.**

### Unresolved calls

`Lower.lean` emits a new IR node `(extern "Full.Lean.Name" args...)` instead of
disguising an unresolved callee as `(call ...)`. A callee is unresolved when it
is neither `@[prod]`-tagged nor on the operator whitelist.

`prod-codegen` rejects `Expr::Extern` with `Error::UnresolvedCall`, naming both
the Lean constant and the definition that reached it. `prod validate` reports
the complete set without generating, so the node remains useful for diagnosis
and for `coverage.md`.

### Opaque types

`Type::Opaque` currently renders as `s.clone()` — a raw Lean name such as
`UorAtlas.Foo` injected verbatim as a Rust type, which fails inside
`syn::parse_str` with an error pointing nowhere near the cause. It becomes
`Error::OpaqueType`, symmetric with the existing `Expr::Opaque` handling.

### Generated subset contract

The exporter writes `subset.json` next to `coverage.md`, describing what
`Lower.lean` can lower: the operator whitelist, the decider ops, and the type
mapping. A new `prod subset` subcommand merges that with `prod-codegen`'s own
tables and renders `specs/lean-for-production.md`. Like the other exporter
outputs, `subset.json` is a generated artifact and is gitignored; the rendered
markdown is committed and diffed in CI. A
feature cannot appear in the contract unless both halves implement it, which is
why the document is generated rather than maintained by hand — the same reason
`coverage.md` is computed by Lean's own `shouldGenerateCode`.

### Consequence

Definitions that compile today will stop compiling — loudly, at export or
codegen, instead of silently producing broken Rust. That is the point of the
milestone. The strict rejection is nevertheless turned on **last** in the
migration order, so that it lands only once nothing legitimate trips it.

## S1 — Generated types

### Projections resolve to field names in Lean

`Lower.lean` has the environment, so it resolves `.proj typeName idx struct`
into a field *name* at lowering time: `(proj "UorAtlas.Instance" "q" x)`.

This deletes codegen's `instance_field` table outright and makes the
silently-swapped-fields failure mode impossible by construction — the type
declaration and the projection come from one source of truth instead of two
tables that have to agree. Swapped fields are the worst failure mode available
to this project, because they produce wrong answers rather than a compile
error.

### IR surface

A module gains type declarations alongside definitions:

```
(module UorAtlas.Kernel
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat)))

  (def stride ((i (named "UorAtlas.Instance"))) Nat
    ...))
```

One `ctor` renders a Rust struct; several render a Rust enum with named-field
variants. `Type::Instance` and `instance_field` are deleted. `Type::Named`
replaces them and renders as `crate::<LastComponent>`, keeping the existing
convention so that `goldens.ir` can reference types declared in `kernel.ir`
without redeclaring them — type declarations are emitted into `kernel.ir` only.

### Erasure

`Prop` fields are dropped, so `Instance`'s
`valid : q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1` never reaches Rust. Field names come from Lean
(`q`, `T`, `O`), replacing today's lowercased `t`/`o`; `#![allow(non_snake_case)]`
already covers the naming.

### Copy discipline keeps this in tier 0

A type is tier-0-eligible iff every field is a scalar, a tuple of eligible
types, or another eligible generated type. Eligible types derive
`Debug, Clone, Copy, PartialEq, Eq` and pass by value exactly as `Instance`
does today. Recursive inductives are not eligible and are rejected with
`Error::RecursiveType`. This is the same slices-and-buffers line the list
lowering already draws, applied to user data.

### Construction and matching stop being positional

`(ctor "UorAtlas.Instance.mk" a b c)` renders
`crate::Instance { q: a, T: b, O: c }`. `cases` on a multi-constructor type
renders real enum patterns rather than today's bare ctor names. `Prod.mk` keeps
its tuple special-case, and the `Bool`/`Option`/`List` special-cases are
unchanged.

### Rejected in this milestone

Each with its own error variant and conformance case: recursive inductives,
type-parameterized inductives (S5), mutual inductives, indexed families, and
structures with a field of an unsupported type.

## Error variants

New in `prod_codegen::Error`, each with a conformance case asserting it:

| Variant | Cause |
|---|---|
| `UnresolvedCall` | callee is neither `@[prod]`-tagged nor whitelisted |
| `OpaqueType` | a type with no rendering reached codegen |
| `RecursiveType` | inductive refers to itself; needs tier 1+ (S7) |
| `PolymorphicType` | inductive has type parameters; needs S5 |
| `UnsupportedFieldType` | a field's type is not tier-0-eligible |
| `DuplicateTypeName` | two Lean types share a last component |

## Testing

Two conformance halves, at the two layers that break independently.

**Golden IR (Lean side).** `lean/Conformance/` holds one small `@[prod]`
definition per feature. The exporter writes `conformance.ir`, and a committed
golden file is diffed in CI. The golden is generated, committed, regenerated
only by `just conformance-bless`, and never hand-edited — it is a review
surface for Lean-side changes, which currently have none.

**Rejection matrix (Rust side).** IR fixtures in `prod-codegen` unit tests
assert that each unsupported construct yields its specific `Error` variant.
Fast, and it pins the contract independently of the Lean build.

**Existing gates carry over unchanged and get stronger for free.** A generated
type must be `Copy`, so `tests/no_alloc.rs` now certifies user data types too.
`just prod` (tests, `test-assertions`, `no-alloc`, roots check), `just lint`,
`just fmt-check`, and `just wasm-check` all continue to apply.

## Migration order

Chosen so the tree stays green at every step.

1. **Golden-IR harness.** Zero blast radius, and it protects every step after.
2. **Projection spike.** Confirm against Lean's sources that LCNF projection
   indices are into the *erased* field list, including when a `Prop` field is
   not last, and for multi-constructor inductives. The result is recorded in
   `AGENTS.md`. If the rule differs from the assumption, revisit the S1 design
   before continuing.
3. **Type declarations** in the IR and codegen, alongside the existing
   hard-wired path so both work.
4. **Flip `Instance` to generated.** Delete `coordinate.rs`; update
   `spectral.rs`, which imports `coordinate::Instance` and uses `.t`/`.o` that
   become `.T`/`.O`; update tests.
5. **Field-name projections** replace indices; delete `instance_field`.
6. **Strict rejection**, last: the `(extern ...)` node and `Type::Opaque`
   errors, once nothing legitimate trips them.
7. **Generated subset contract** and its CI gate.

## Risks

- **Projection index semantics** (step 2) is the highest-risk item, because a
  wrong mapping produces silently wrong code. Mitigated by resolving names in
  Lean rather than indices in Rust, by the spike, and by a conformance case
  built to catch a field swap.
- **The strict rejection is a breaking change** for any Lean definition that
  currently relies on an unresolved call rendering as a plain Rust call.
  Mitigated by ordering it last and by `prod validate` reporting the full set
  first.
- **The committed golden brushes against the repo's rule** that generated
  artifacts are never hand-edited. Mitigated by the `just conformance-bless`
  workflow and by treating any unexplained golden diff as a defect.
