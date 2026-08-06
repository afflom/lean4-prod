# lean4-prod

Generate real, raw, performant Rust from actual Lean 4 — automatically, with
whole-language coverage inherited from Lean's own compiler.

## How it works

You tag definitions in Lean. Lean's compiler lowers **every** compilable
definition to LCNF (Lean Compiler Normal Form) — a tiny typed IR with seven
constructors. `prod-export` walks that LCNF and emits a compact s-expression
IR. Pure `no_std` Rust libraries parse the IR and generate zero-cost Rust,
consumed through a proc-macro, a CLI, or a WebAssembly playground.

```
Lean 4 project (native — the Lean toolchain cannot run in wasm)
@[prod] def foo ...        theorem bar ...
        │  lake exe prod-export
        ▼
kernel.ir (sexp)   roots.json   coverage.md   goldens.ir
        │
════════ portable half: no_std + alloc, wasm32-clean ════════
        ▼
prod-ir ─────────────► prod-codegen          (pure Rust libraries)
(AST + nom parser     (IR → Rust source,
 + sexp writer)        single source of truth)
    │          │            │
    ▼          ▼            ▼
prod-macros  prod-cli    prod-wasm
(thin host   (native:    (wasm-bindgen shell:
 proc-macro   parse/gen/  browser playground)
 wrapper)     roots)
```

### Why LCNF (whole-language coverage without rebuilding anything)

We do **not** parse or lower Lean's surface syntax or elaborated `Expr`
ourselves. Lean's own compiler performs the hard lowering — typeclass
dictionaries become explicit arguments, recursors and `match` become `cases`,
higher-order functions become closures and join points, proofs and `Prop`s
are erased. We lower the result — seven `Code` cases — so coverage of the
compilable fragment of Lean comes from Lean itself and grows as Lean grows.

The coverage report (`coverage.md`) classifies every constant in the module
using Lean's own `Lean.Compiler.LCNF.shouldGenerateCode`, so "covered" means
what Lean means.

### Honest limits

- Proofs/`Prop`s are erased by design — they are metadata (see `roots.json`),
  not code.
- `noncomputable` definitions, `@[extern]` FFI, and `unsafe`/`partial`
  runtime tricks are exported as opaque signatures and counted in
  `coverage.md`.
- We couple to Lean's internal LCNF API. The toolchain is pinned
  (`leanprover/lean4:v4.30.0`) and CI-gated against API drift.
- Generated `Nat` code uses bounded `u64`: addition, multiplication, shifts,
  and powers fail explicitly on overflow (including shift/power exponents that
  do not fit `u32`); subtraction truncates at zero; and division/modulo by zero
  return zero. Exact arbitrary-precision `Nat` output is future work.
- The wasm package houses the portable half (parse + codegen + roots). The
  Lean extractor itself is native-only.

## Quick start

```sh
nix develop              # lean4 + rust + just (or: install lean4 4.30.0 and rust manually)
just prod                # lake exe prod-export && cargo test
```

Lean side:

```lean
@[prod] def stride (inst : Instance) : Nat := inst.t * inst.o
```

```sh
cd lean && lake exe prod-export   # → rust/prod-core/{kernel,goldens}.ir, roots.json, coverage.md
```

Rust side:

```rust
prod_macros::prod_defs! { ir = "kernel.ir" }   // typed, zero-cost Rust fns
```

## Roots (proof-graph analysis)

Every theorem is a root. `Roots.lean` exports each root's dependency edges,
proof-term size, and kernel depth to `roots.json`. The CLI computes what the
registry claims:

```sh
prod roots check     # DAG acyclicity + coverage (actually computed)
prod roots pareto    # Pareto front over (proof size, kernel depth, check time)
prod roots connect   # hypothesized bridges between roots sharing kernel deps
```

The roots commands operate on the generated registry directly:

```sh
cd rust
cargo run -p prod-cli -- roots check ../roots.json
cargo run -p prod-cli -- roots pareto ../roots.json
cargo run -p prod-cli -- roots connect ../roots.json
```

The Pareto analysis currently uses proof-term size and kernel depth; the Lean
export does not yet record check-time measurements. Compact theorem IDs may
repeat when Lean generates private helper theorems, and `roots check` reports
those as warnings while using the dependency names to resolve graph edges.

## Layout

- `lean/Prod/` — the extractor: attribute, LCNF extraction, lowering, roots,
  coverage, emit. Generic; not tied to the example.
- `lean/Example/` — worked example: the UOR Atlas coordinate kernel with
  machine-checked proofs (no mathlib — `decide`/`omega`/`rfl` discipline).
- `rust/prod-ir`, `rust/prod-codegen` — `no_std` + `alloc` portable core.
- `rust/prod-macros`, `rust/prod-cli` — thin native shells.
- `rust/prod-wasm` — wasm-bindgen API: `generate(ir)` and `roots_pareto(json)`.
- `rust/prod-core` — runtime types + generated definitions + golden tests.

## Roadmap

- TF1-style claim registry: claims typed by the proof that discharges them
  (build / open / definition), executable checks, mutation testing for
  non-vacuity.
- LCNF impure-phase fidelity (unboxed scalars, refcount elision notes) for
  tighter codegen.
