# Multi-backend code generation: the IR as a hub

**Status:** Plan 1 (the split) DONE, 2026-08-17. Plan 2 (Python end-to-end)
not started.
**Supersedes nothing.** Extends the pipeline described in
`specs/designs/2026-08-08-lean-for-production-coverage.md` and builds on the
invariant machinery from `specs/designs/2026-08-09-s2-scalar-completeness-and-invariants.md`.

## Goal

Turn the LCNF-derived IR into a hub that produces source in several languages,
rather than a Rust-shaped pipeline with Rust at the end. Concretely: split
`prod-codegen` into a language-neutral core plus a backend interface, keep Rust
at behavioural parity, and prove the seam with one new backend — Python — that
executes Lean's own golden values.

## Why now

The IR is already close to language-neutral at the expression level:
arithmetic, comparisons, `cases`, constructors, projections, `let`, calls and
join points carry no Rust in them. What is Rust-shaped is everything wrapped
around those nodes — the fallibility fixpoint, the list-buffer policy, the
`ComputeError` type, and one method (`NumKind::rust_type`) that sits in
`prod-ir` itself. Those are separable, and separating them is cheaper now than
after a second backend has been bolted on beside them.

## Decisions taken, and why

These four were settled during design and are load-bearing for everything below.

### 1. Each language uses its natural numeric type

Lean's `Nat` is arbitrary precision. Rust renders it `u64`, which is why
`ComputeError::AddOverflow` exists at all — the error is an artifact of the
representation, not a fact about Lean. Python's `int` is arbitrary precision
and needs no such error.

**Decision:** `Nat` maps to `u64` in Rust and C, to `int` in Python, to
`bigint` in TypeScript. Each backend is idiomatic.

**Consequence, stated plainly:** the SDKs are **not interchangeable above
2^64**. Rust returns an error where Python returns the mathematically correct
answer. This is a deliberate trade of cross-backend uniformity for idiomatic,
fast output in each language, and it is the reason the divergence registry
below exists.

**Architectural consequence:** fallibility becomes a property of the *backend*,
not of the IR. The `Shape` fixpoint must be parameterised rather than computed
once.

### 2. wasm is a build target, not a backend

Emitting wasm directly is a compiler — stack machine, linear memory, hand-rolled
layout for structures, an owned calling convention — and is comparable in size
to everything else in this design combined.

**Decision:** wasm is reached by compiling generated Rust (`--target
wasm32-unknown-unknown`, which already works today) or generated C (via
clang/wasi-sdk). Direct wasm emission is an explicit non-goal.

Note for readers of the codebase: `prod-wasm` is the *generator* compiled to
wasm so it can run in a browser. It is not a wasm backend, and its name invites
that misreading.

### 3. Statement-level lowering, not a renderer trait

The deciding case is `f (g a) (h b)` where all three are fallible:

```rust
f(g(a)?, h(b)?)                               // Rust: expression-level
```
```python
f(g(a), h(b))                                 # Python: exceptions, invisible
```
```c
uint64_t t0, t1, t2;                          /* C: statement-level */
if (g(a, &t0) != PROD_OK) return PROD_ERR;
if (h(b, &t1) != PROD_OK) return PROD_ERR;
if (f(t0, t1, &t2) != PROD_OK) return PROD_ERR;
```

Today's renderer returns a `String` per expression node. **That shape cannot
produce the C column** — no method returning a string for `Call` can emit three
statements before the expression it is embedded in. A backend trait over the
existing renderer would therefore need an escape hatch that unravels the
abstraction the first time C is attempted.

**Decision:** insert a lowering pass producing an imperative Target IR, then
write thin per-language printers over it.

### 4. Behavioural equivalence replaces byte-identity for Rust

Routing Rust through a new lowering will change generated formatting.

**Decision:** the Rust regression test becomes behavioural — the existing
compile-tests must still compile, and every Lean golden must still execute to
the same value. Byte-identity is dropped as a constraint.

### 5. Deliverable is a source file, not a package

Packaging (`pyproject.toml`, `__init__.py`, type stubs, `package.json`,
`.d.ts`) is real work, orthogonal to whether the codegen is correct, and
cleanly separable.

**Decision:** this design delivers generated source per backend. Packaging gets
its own spec.

## Architecture

```
lean/  (unchanged)
  └─> module.ir ─────────────── language-neutral, LCNF-derived
                    │
        ┌───────────▼────────────┐
        │  prod-lower            │   the only place semantics live
        │   · Shape fixpoint, parameterised by TargetProfile
        │   · error propagation made explicit
        │   · temporaries introduced
        │   · List strategy (borrow / buffer / native sequence)
        │   · sized-integer masking
        └───────────┬────────────┘
                    │  Target IR — imperative
        ┌───────────┼───────────┐
        ▼           ▼           ▼
   emit-rust   emit-python   (emit-c, emit-ts — designed, not built)
```

### Crates

| Crate | Responsibility | Status |
|---|---|---|
| `prod-ir` | LCNF surface. **Loses `NumKind::rust_type`** | DONE (plan 1) |
| `prod-lower` | Target IR + lowering + `TargetProfile` + name injectivity | DONE (plan 1) |
| `prod-emit-python` | Python printer | plan 2 |
| `prod-codegen` | Thin facade plus internal Rust printer, preserving today's public API | DONE (plan 1) |
| `prod-runtime-python` | Hand-written Python prelude | plan 2 |

`prod-codegen` must keep its current surface so `prod-cli`, `prod-macros`,
`prod-wasm` and `prod-codegen-compile-tests` do not churn. The proc macro in
particular is consumed by two test crates and a published contract.

## Target IR

**Central invariant: expressions are total by construction.** Anything that can
fail is a statement. This is what gives C a place to put its check, and what
lets the fallibility decision be made once in the lowering rather than
re-derived by every printer.

```
Stmt  ::= Let      { name, ty, value: TExpr }        -- infallible binding
        | TryLet   { name, ty, op: FallibleOp }      -- the only failure point
        | If       { cond: TExpr, then: [Stmt], else: [Stmt] }
        | Switch   { scrut: TExpr, arms: [Arm], default: Option<[Stmt]> }
        | Return   TExpr
        | Fail     ErrorCode                          -- Unreachable, explicit failure
        | Push     { seq, value: TExpr }               -- list construction

TExpr ::= Lit Value | Var name
        | BinOp  kind op TExpr TExpr                  -- infallible ops ONLY
        | Ctor   type ctor [TExpr]
        | Proj   type field TExpr
        | Call   name [TExpr]                         -- total callees ONLY
        | Not TExpr | And TExpr TExpr | Or TExpr TExpr
```

`Switch` arms carry constructor binders, so destructuring is explicit and a
printer never invents names.

`Push` is deliberately abstract over the list strategy, because the strategy is
a *lowering* input rather than a printing one. Under the native-sequence
strategy it lowers to one `Push` per element. Under the caller-buffer strategy
the lowering additionally emits the index arithmetic and an **explicit bounds
check** — an `If` guarding a `Fail OutputTooSmall` — rather than leaving the
check for the printer to remember.

That placement is forced by the total-expressions invariant: running out of
buffer is a failure, so it must appear as a statement. Today that check lives
inside the Rust renderer, which is exactly the kind of per-printer obligation
this design exists to eliminate — with three printers it would be three
opportunities to forget it.

The Target IR also carries a **declared type table**, including types
synthesised for targets that lack structural equivalents (C has no `Option`, no
tuples, no ADTs). Letting each printer improvise its own would put type
construction in N places.

### The lowering always emits explicit temporaries

One canonical Target IR shape regardless of target. Printers whose language
allows it re-inline single-use temporaries.

This split matters for testability: the Target IR for a given module is **the
same tree** for any two backends whose *lowering-side* profile fields agree —
Rust and C, for instance, which share `nat_repr`, fallible-op set, list
strategy, masking and division rows, and differ only in printer-side fields. So
a printer bug cannot masquerade as a lowering bug. It also means temporary-inlining cannot silently
change semantics, because it no longer touches the tree.

### Hard invariant: temporaries never cross a control-flow boundary

If `h b` appears only in the `else` branch, hoisting its `TryLet` to the top
evaluates it unconditionally — turning a short-circuit into eager evaluation,
and possibly producing an error where Lean has none.

Statements land in the block where their value is used. This gets a dedicated
test with a fallible operation in one arm of a conditional; straight-line
examples cannot catch it.

## TargetProfile

The seam. A small declarative value, split by which stage reads it.

| Read by the **lowering** | Read by the **printer** |
|---|---|
| `nat_repr` (drives fallibility) | error transport (`?` / exception / out-param) |
| fallible-op set | temporary inlining permitted |
| list strategy | type names, syntax, naming convention |
| sized-mask required | |
| host division semantics | |

| Field | Rust | Python | C (designed) |
|---|---|---|---|
| `nat_repr` | `u64`, bounded | native `int`, exact | `uint64_t`, bounded |
| fallible ops | checked add/mul/pow/shl | **none** | checked add/mul/pow/shl |
| error transport | `Result` + `?` | exception | out-param + status |
| inline temporaries | yes | yes | **no** |
| list strategy | caller buffer | native list | caller buffer |
| sized mask required | no (native widths) | **yes** | no |
| host division | truncate | floor | truncate |

Decision 1 falls out of one row: Python's fallible-op set is empty, so its
`Shape` fixpoint marks those definitions `Value` where Rust marks them
`Fallible`, and Python's generated functions have no error path at all. That is
not a special case in the emitter — it is the fixpoint reading a different
profile.

## Semantics: a hand-written runtime prelude per backend

Rather than inlining a correction wherever a host language disagrees with Lean,
each backend ships a small **hand-written, human-reviewed** shim containing only
the operations whose host semantics differ: Euclidean `ediv`/`emod`,
sized-integer wrap helpers, and the error type.

Three reasons this beats inlining: it is small enough to actually read; it is
directly conformance-testable without generating anything; and the *generated*
code then contains no cleverness, so a reviewer diffing generated Python sees
calls to named helpers rather than open-coded bit twiddling.

**Rust keeps its current inline forms.** They are already correct and tested,
and rewriting them to route through a new prelude would be churn with a
regression risk and no benefit. This asymmetry is deliberate.

### Division

Lean's `Int` division is Euclidean (`Int.ediv`/`Int.emod`). Hosts disagree
three ways, and one pairing is a trap:

| | `-12 / 7` | `12 / -7` |
|---|---|---|
| Lean (Euclidean) | `-2` rem `2` | `-1` rem `5` |
| Python (floor) | `-2` rem `2` ✓ | `-2` rem `-2` ✗ |
| C (truncate) | `-1` rem `-5` ✗ | `-1` rem `5` |

Floor and Euclidean **agree only when the divisor is positive**. A Python
backend mapping `Int.ediv` to `//` passes every test with a positive divisor
and is wrong for negative ones.

**Decision:** route all non-Euclidean hosts through the prelude. This removes
the sharp edge rather than relying on a conformance case to catch it.

### Sized-integer masking

Python and TypeScript have no fixed-width integers, so every sized operation
needs an explicit mask (`& 0xFF`, or `BigInt.asUintN`).

**Decision:** the lowering inserts a mask after **each** sized operation, not
once at the end — masking a sequence differs from masking each step, and this
is the kind of thing that is right for `+` and wrong for `*`.

### Shift-left on exact `Nat`

Bounded backends return `ShiftOverflow` for a huge shift amount. Python will
attempt `1 << 10**9` and exhaust memory.

**Decision: cap it and raise**, matching the bounded backends. This overrides
Decision 1 in this one case, because the natural behaviour is a hang rather
than a wrong answer, and a hang is a worse failure than an error. Recorded in
the contract as a deliberate divergence from Lean, which *would* compute the
value.

### Recursion depth

No tail-call elimination exists anywhere in this pipeline. Rust and C overflow
the stack at some depth; **Python raises `RecursionError` at ~1000 frames**,
shallow enough to hit real inputs — a fold over a few thousand elements works
in Rust and fails in Python.

**Decision:** do not fix it; trampolining is its own project. The conformance
suite **measures** achievable depth per backend and publishes the number, so
the limit is a documented fact rather than a production surprise. Raising
`sys.setrecursionlimit` from inside a library is global mutation and is
rejected.

## Name policy

Each backend declares its keyword set and escape strategy. Rust escapes with
`r#`. Python and C must **rename**, which is irreversible. C has no namespaces,
so names flatten to globally unique symbols.

**The injectivity check lives in core**, and it is the point of the component:
distinct Lean names must map to distinct target names, verified, with a named
rejection when they do not.

This is not hypothetical. Today's `last_component()` is already lossy — two
Lean types sharing a final segment in different namespaces would collide
silently in Rust *today*. Flattening for C makes it dramatically more likely.
Collisions are the silent-wrongness class this repo keeps shipping, so the
guarantee belongs in one place with a test rather than in N backends' good
intentions.

## The contract becomes per-backend

`specs/lean-for-production-<lang>.md`, rendered from a shared core plus a
backend section.

This is forced, not stylistic. The contract currently asserts *"Outside the
crate, `new` is the only way to build the type."* That is true in Rust,
compile-time-only in TypeScript, and **false in Python**, where `_field` is a
convention and nothing prevents assignment. Shipping one contract across
backends would reproduce, deliberately and at N× scale, the exact defect PR #4
just fixed.

## Verification

### Generated assertions

Lean computes goldens into `goldens.ir`; Rust asserts them by hand;
`goldens_consumed.rs` text-checks that every golden is *mentioned* somewhere —
a deliberate weak link, because the consumers live in crates that cannot see
each other.

Hand-writing that per backend is N × 40 assertions and will not survive contact.

**Decision:** generate each backend's assertion suite from the golden list
itself. An unconsumed golden then stops being possible by construction rather
than being caught by a text search. This was already a recorded Phase A
follow-up ("generate golden assertions from the same table that generates
values"); the multi-backend requirement forces the fix rather than adding debt.

### Five layers

| Layer | What it catches |
|---|---|
| **Lowering** — Target IR snapshots | Semantic bugs, printer-independent |
| **Printer** — generated-source snapshots | Syntax and formatting churn |
| **Execution** — generated assertions run in each language | Does generated Python compute what Lean computed |
| **Differential** — cross-backend comparison | Backends disagreeing where they should agree |
| **Rust regression** — existing compile-tests + goldens | That the refactor preserved behaviour |

The prelude is tested **directly**, not only through generated code — it is
hand-written, so it is the one place a human error cannot be blamed on the
generator.

### The divergence registry

Decision 1 means Rust and Python legitimately disagree above 2^64. "These SDKs
sometimes differ" is unfalsifiable as stated, and unfalsifiable claims are how
this repo has shipped every one of its defects.

**Backends must agree on every input except those in an explicit registry**,
where each entry names the input, the divergent outputs, and the reason.
`2^64 + 1` under bounded `nat_repr` is an entry. A capped shift-left is an
entry. **Anything that diverges without an entry is a test failure.**

The per-backend contract sections are generated from the registry, so they
cannot drift from what is actually tested.

## Scope

**In:** the `prod-lower` split; `TargetProfile`; Target IR; Rust printer at
behavioural parity; Python backend end-to-end with executed goldens; the Python
prelude; name-injectivity checking in core; per-backend contracts; the
divergence registry; Python in the nix shell and CI.

**Out, each separable:**
- C and TypeScript backends — *designed against* (the C column is
  paper-asserted so the seam is stressed by more than Python), not built
- Direct wasm emission — wasm is a build target of Rust or C
- Packaging and distribution
- Tail-call elimination or trampolining
- Any change to `lean/`

## Implementation sequencing

This design is deliberately larger than one comfortable branch: a crate split,
a new IR, two printers, a prelude, conformance in two languages, per-backend
contracts, the registry, and CI. **It should be executed as two plans**, both
written from this document:

1. **The split.** `prod-lower`, Target IR, `TargetProfile`, name injectivity,
   the internal Rust printer at behavioural parity, printer snapshots. Nothing new ships
   to users; the deliverable is that Rust still works through the new seam.
   **DONE 2026-08-17**, plan `specs/plans/2026-08-11-multi-backend-split.md`.
   The old renderer is deleted; `prod-codegen` is a facade over `prod-lower` +
   the internal Rust printer with `prod-codegen`'s public API unchanged. Parity is *behavioural* and
   what certifies it is `just prod`, which compiles the generated Rust and
   executes every Lean-computed golden. Text differs in five known places:
   flat statement lists rather than nested braces, `return` terminators in
   branches rather than block values, branch-local temporaries never folded
   into their single use, a `__len` cursor rather than nested
   `split_first_mut`, and an elided rather than unit-bound join-point `let`.
2. **Python end-to-end.** `prod-emit-python`, the prelude, generated
   assertions, the divergence registry, per-backend contracts, nix and CI.

This is *not* the "refactor only, one implementation" approach rejected during
design. That risk was about **designing** a seam against a single backend. The
seam here is designed against Rust, Python and a paper-asserted C before either
plan is written, so splitting *execution* does not reintroduce it — it only
avoids a single long branch in which the seam keeps shifting under later work.

If plan 1 finishes and the profile still looks right, that is weak evidence.
The real test is plan 2, and any profile change it forces should be treated as
information about the design rather than as churn.

## Risks

**The seam may still be Rust-and-Python-shaped.** Both chosen languages
propagate errors implicitly (`?`, exceptions); C is the one that cannot.
Paper-asserting the C column is the mitigation, and it is real but partial. If
the profile is wrong, it surfaces at backend three.

**`prod-codegen` as a facade could rot.** If the facade drifts from what the
new crates do, it becomes a second source of truth. It should be a thin
re-export, and anything that cannot be expressed as one is a signal the split
is in the wrong place.

**Behavioural parity is weaker than byte-identity.** Dropping byte-identity
means a formatting-only regression is invisible. The printer snapshot layer is
what replaces it, and it needs to exist from the first commit of the Rust
printer rather than being added later.

## Follow-ups recorded, not scheduled

- Packaging spec (`pyproject.toml`, stubs, `package.json`, `.d.ts`)
- C backend, which is the real test of `TargetProfile`
- TypeScript backend
- Trampolining, if measured recursion limits prove too shallow in practice
