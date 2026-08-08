# Plan: align generated code with the Rust best-practices standard

**Status: DOCUMENTED ONLY — implementation deferred at user request
(2026-08-06). Pick up from here later. Do not implement without the user's
go-ahead.**

Source standard: https://gist.github.com/auser/c3161f55a8393faa8af5ddda68c6befa
(normative MUST/SHOULD engineering guide: memory profiles, no panic on
recoverable conditions, checked arithmetic, lint/CI discipline).

User directive (also saved in AGENTS.md): the goal is to generate
production-ready, parallelized, secure code, and to **always prefer not
allocating any heap memory in the generated code**.

## Audit findings (current state vs standard)

1. **Overflow panics** — generated code uses `.expect("Lean Nat ... overflow")`
   on `checked_add/mul/shl/pow` and `u32::try_from(...).expect(...)`.
   Violates §4.2 (`expect_used = "deny"`) and is a DoS surface on
   caller-controlled input ("secure" goal). Sites in
   `rust/prod-codegen/src/lib.rs` (`checked_binop` / `saturating_binop` /
   `checked_shift` / `Pow`), plus expected-string assertions in codegen unit
   tests and `rust/prod-wasm/src/lib.rs` (the `generate` test).
2. **Heap allocation in generated code** — `List` support renders Lean lists
   as `prod_core::List<T>` (`Box`-linked), and `rust/prod-core/src/lib.rs`
   carries `extern crate alloc`. Violates §2 (default runtime profile is
   strict heapless / allocation-free steady state).
3. **Latent parser panic** — `rust/prod-ir/src/parser.rs`:
   `parse_i64` does `digits.parse::<i64>().unwrap()` and negates, which
   panics on the `i64::MIN` digit string.
4. **Missing guardrails** — no `forbid(unsafe_code)`, no workspace clippy
   restriction lints, no `release-assertions` profile, no allocation-counting
   test (§12, §13.5, §17).
5. **Consequence for roadmap** — arbitrary-precision `Nat` via bigint is OFF
   the table (heap); bounded-`u64` Nat becomes the deliberate documented
   policy. Typed `Int` → `i64` remains heap-free and stays on the list.

## Design decisions

- **Error model (§4.3, §2.9):** one small `Copy` heapless error enum in
  `prod-core`, referenced by generated code as `crate::ComputeError`:
  variants `AddOverflow | MulOverflow | ShiftOverflow | PowOverflow |
  ShiftExponentTooLarge | PowExponentTooLarge | OutputTooSmall { required,
  provided }`. `Display` writes directly to the formatter (no `String`).
- **Fallibility is precise, not uniform:** a generated fn returns
  `Result<T, crate::ComputeError>` only if its body contains a checked op
  (`add/mul/shl/pow`) or calls a fallible def; otherwise it keeps its plain
  return type. Fixpoint over the module's call graph in codegen. Goldens
  (literal zero-arg defs) stay infallible.
- **List without heap (§2.2, §2.5):**
  - `(List α)` in **param position** → `&[α]`. `List.nil` match arm → `[]`
    pattern; `List.cons (h t)` arm → `[h, t @ ..]` slice pattern (recursion
    passes `rest` directly — zero-cost, no rebind hack).
  - `(List α)` in **return position** → caller-owned output buffer
    (§2.5): signature gains `output: &mut [α]`, returns
    `Result<usize, ComputeError>` (initialized prefix length). Rendering is a
    "builder mode" threaded through the body: `List.nil` → `Ok(0)`;
    `List.cons h t` → bounds-check, `output[0] = h`, recurse `t` into
    `&mut output[1..]`, `Ok(1 + k)`; `if`/`let`/`cases` recurse into builder
    mode. An intermediate `let`-bound List value or List-typed `call` result
    is a **codegen error** (honest failure; not needed by current defs).
  - Zero-arg golden defs returning `(List α)` → `&'static [α]` from a static
    array (`&[3, 5]`) — no buffer param needed.
  - `prod_core::List<T>` enum and `extern crate alloc` are REMOVED.
- **Recursion boundedness (§2.3):** generated recursion is structurally
  bounded by fuel/data arguments; documented as part of the contract.
- **Parallelism (§8.5, §16):** no parallel codegen yet; generated fns are
  pure/`Send`/`Sync` by construction. Principle for later: bounded workers,
  deterministic merge order, no unbounded queues; canonical bytes must not
  depend on thread scheduling.

## Steps (when resumed)

1. **AGENTS.md rules** — DONE (goal statement saved 2026-08-06). On resume:
   fold in memory-profile/lint details as they are implemented.
2. **prod-core** — add `ComputeError` (+`Display`, `core::error::Error` under
   std); remove `List<T>` and `extern crate alloc`.
3. **prod-ir** — fix `parse_i64` unwrap/MIN-negation (e.g. parse via `i128`
   + checked conversion); no grammar change.
4. **prod-codegen** —
   a. checked/shift/pow render `.ok_or(crate::ComputeError::X)?`; calls to
      fallible defs render `f(args)?`; fallibility fixpoint per module.
   b. List: param `&[α]`, slice-pattern match arms, return-position builder
      mode with `output: &mut [α]`; zero-arg List goldens → `&'static [α]`.
   c. `Option`/`Bool`/Nat renderings unchanged.
   d. Update all expect-bearing unit-test strings + List/Option tests;
      add tests: fallibility propagation, buffer-mode digits rendering,
      unsupported-intermediate-List error.
5. **prod-core tests** (`macro_generation.rs`) — assertions become
   `assert_eq!(stride(CANONICAL), Ok(24))` style; digits via buffer:
   `let mut buf = [0u64; 8]; let n = digits(10, 43, CANONICAL, &mut buf)?;`
   `assert_eq!(&buf[..n], &[3, 5])`; digitSum takes `&[u64]`; golden List
   returns `&[3, 5]`.
6. **wasm** — update `generate` test string expectation (no `.expect(`);
   `roots_pareto` untouched.
7. **Lint/CI hardening** —
   a. `rust/Cargo.toml` `[workspace.lints]`: `unsafe_code = "forbid"`,
      `unused_must_use = "deny"`; per-crate `[lints] workspace = true`;
      prod-core additionally denies `clippy::{unwrap_used, expect_used, panic}`
      (verify macro-expanded code doesn't trip them; if it does, scope to
      non-generated modules with a comment).
   b. `[profile.release-assertions]` in workspace Cargo.toml
      (§5.7/§17.1); new `just test-assertions` lane; add to `just prod`.
   c. `rust/prod-core/tests/no_alloc.rs` — CountingAllocator test (§13.5)
      certifying `stride`/`classIndex`/`digitSum`/buffer-`digits` perform zero
      heap activity (serial: `--test-threads=1`); new `just no-alloc` lane.
   d. `cargo fmt` pass; `just lint` already uses `-D warnings`.
8. **Docs** — README "Honest limits": generated-code memory profile
   (allocation-free; List = slices + caller buffers), error contract, bounded
   recursion, Nat=u64 as deliberate policy. AGENTS.md status entry.
9. **Gates** — `lake build`, `lake exe prod-export`, `just prod` (incl.
   roots check + release-assertions lane), `just wasm-check`, `just lint`,
   `just no-alloc`, `git diff --check`.

## Out of scope (recorded)

- Typed `Int` → `i64` (next milestone; heap-free, unaffected by this plan).
- Closures (`Code.fun` → opaque).
- Arbitrary-precision Nat — rejected by the no-heap directive.
- Data-parallel codegen — principles recorded in AGENTS.md only.
