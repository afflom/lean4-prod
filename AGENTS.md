# lean4-prod — agent handoff / project guide

You are working in `/Users/auser/work/rust/mine/lean4-prod`: a Lean 4 → production
Rust generator. Tag `@[prod]` definitions in Lean; a metaprogram extracts them via
Lean's OWN compiler frontend (LCNF — Lean Compiler Normal Form), emits a sexp IR;
pure `no_std` Rust libraries parse it and generate zero-cost Rust (proc-macro, CLI,
wasm shells). Theorem "roots" metadata (deps, proof-term size, kernel depth,
kernel re-check time) feeds Pareto/connection analysis in the CLI. Full
architecture: see README.md.

## Goal and engineering standard

The goal is to generate production-ready, parallelized, secure code. We
_always_ prefer NOT allocating any heap memory in the generated code. Follow
the Rust best-practices standard (normative MUST/SHOULD guide: memory
profiles, no panic on recoverable conditions, checked arithmetic, lint/CI
discipline):
https://gist.github.com/auser/c3161f55a8393faa8af5ddda68c6befa

Current generated code does NOT yet comply (overflow `expect()` panics,
`Box`-linked `List`, missing lint/profile guardrails). The alignment plan is
documented in `specs/plans/2026-08-06-best-practices-alignment.md` —
implementation deferred at user request; resume from that file.

## Rules (hard)

- NO mathlib. Pure Lean 4 core/Init; `decide`/`omega`/`rfl` discipline.
- NO `sorry`, NO `axiom` in anything claimed as proved.
- Nothing hand-written downstream of Lean: kernel.ir/goldens.ir/roots.json/
  coverage.md are generated artifacts (gitignored). Never edit them by hand.
- The old repo at `~/work/rust/mine/lean-four-prod/` is READ-ONLY reference.
- No `git add`/`git commit`/other git mutations without the user's explicit go-ahead.
- Verify gates below must actually pass before claiming a milestone done.

## Toolchain quirks (IMPORTANT)

- lean/lake are NOT on PATH. Always run via the nix dev shell.
- Flakes only see git-tracked files and this repo has untracked files, so ALWAYS
  use the `path:` prefix:
  - Build Lean: `cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build`
  - Run exporter: `... --command lake exe prod-export`
- If `nix` is "not found": `/nix/var/nix/profiles/default/bin/nix`.
- cargo/rustc ARE on PATH (Homebrew). wasm32 target: use
  `RUSTC=$(rustup which --toolchain stable rustc) rustup run stable cargo build ... --target wasm32-unknown-unknown`
  (Homebrew rustc can't see rustup targets).
- Lean builds take minutes; use generous timeouts (300s+).

## Status: M0–M6 DONE for the current example pipeline

- M0 skeleton, M1 Rust core (all green: 24 tests, clippy clean, wasm32 check),
  M2 Lean Example (lake build exit 0, no mathlib), M3 LCNF extractor,
  M4 exporter-generated goldens, M5 computed roots analysis, and M6 wasm/CI.
- roots.json root ids are FULL Lean names (unique by kernel construction);
  each root carries an `"auto"` flag marking Lean-generated machinery
  (equation lemmas `*.eq_<n>`, `*_proof_*` certificates, `sizeOf_spec`/`inj`/
  `injEq` lemmas, structure projections like `UorAtlas.Instance.valid`).
  `roots check|pareto|connect` skip `auto: true` roots by default (`--all`
  includes them); a missing `auto` field (older files) parses as `false`.
- Each root carries `check_time_ns`: wall time for re-typechecking its proof
  term with `Lean.Kernel.check` (empty local context), taken as the MINIMUM
  over 16 exporter-side repetitions — single-shot µs timings flip root
  orderings between runs, the min is reproducible. Machine-dependent; a
  relative signal only. `roots pareto` is a three-objective front over
  (proof_term_size, kernel_depth, check_time_ns); a missing `check_time_ns`
  parses as `0`, which reduces dominance to the old two-objective rule when
  uniformly absent.
- The Pareto front of hand-written roots is currently just `digits_lt_stride`:
  it dominates the other two real theorems on all three objectives — smaller
  (776 nodes), shallower (depth 4), and genuinely cheaper to re-check
  (~110µs vs ~130µs/~400µs, stable across runs). A non-trivial front needs a
  theorem that beats it on at least one objective.
- RECURSION works end-to-end (first recursive `@[prod]` def: `UorAtlas.digitCount`,
  fuel-bounded digit count, in `lean/Example/Kernel.lean`). Three latent bugs
  had to die for it:
  1. `Prod.depthOf` (Roots.lean) assumed a DAG and stack-overflowed on the
     self-cycle of a recursive def — now DFS with a `visiting` set; back edges
     contribute 0 (longest chain over the cycle-condensed graph).
  2. `if a < b then … else …` compiles to `Nat.decLt` + `cases` over
     `Decidable.isFalse/isTrue` — unrenderable in Rust. `decidableIf?` in
     Lower.lean rewrites the immediately-bound shape to IR `(if (lt a b) t f)`.
  3. prod-codegen rendered `Nat.zero`/`Nat.succ` alts as Rust enum patterns
     (invalid on u64) and `checked_add/mul`/`saturating_sub` failed method
     resolution (E0689) on let-bound-literal receivers — now `0` / `_` + pred
     via `saturating_sub(1)`, and receivers pinned with `as u64` (same trick
     `Pow` already used).
  digitCount has goldens (2, 3, and the fuel-0 short-circuit) asserted in
  `rust/prod-core/tests/macro_generation.rs`.
- DECIDABLE GUARDS + OPTION work end-to-end (`UorAtlas.sameClass` uses `=`,
  `UorAtlas.smallEnough` uses `≤`, `UorAtlas.tryClassDecode : … → Option (Nat
  × Nat × Nat)`). `decidableIf?` recognizes `Nat.decLt`/`Nat.decLe`/
  `Nat.decEq`/`instDecidableEqNat` (the eq instance wrapper is NOT unfolded by
  the simplifier — match both) → IR `(if (lt|le|eq a b) t f)`. prod-ir gained
  a `le` expr — NOTE: the parser must delimiter-terminate `tag("le")`, bare
  tag prefix-matches `let` and kills the enclosing alt (regression test:
  `test_parse_le_does_not_eat_let`). Codegen maps `Bool.true`/`Bool.false`
  and `Option.none`/`Option.some` ctors+match arms to `true`/`false`/
  `None`/`Some(v)`; `lowerType` handles `Option α`.
- LISTS work end-to-end too (`UorAtlas.digits : … → List Nat`,
  `UorAtlas.digitSum : List Nat → Nat` in Kernel.lean): prod-ir gained a
  `(List type)` form (`Type::List`), the Lean lowerer maps `List α` to it,
  and codegen renders `List.nil`/`List.cons` ctors and match arms onto the
  hand-maintained runtime type `prod_core::List<T>` (`Nil`/`Cons(T,
  Box<List<T>>)` — same "runtime type + codegen mapping" pattern as
  `Instance`; the cons-arm tail rebinds unboxed). List goldens
  (`digits 10 43 canonical = [3,5]`, `digitSum = 8`) roundtrip in
  macro_generation.rs.

Known remaining limitations: typed Lean `Int` semantics and arbitrary-precision
Nat are NOT implemented (generated Nat is u64 with the bounded policy:
checked add/mul/shl/pow, saturating sub, total div/mod-by-zero). Closures
(`Code.fun`) still lower to opaque. `cases` on user-defined inductive types
other than Nat/List/Option/Bool still render ctor names as Rust patterns,
which only compile if a matching runtime enum exists.

## M3 spec — the LCNF extractor (the defensible core)

Create under `lean/Prod/`: `Attribute.lean` (`@[prod]` via `Lean.registerTagAttribute`;
enumerate tagged names by folding the attribute extension state), `Extract.lean`,
`Lower.lean`, `Roots.lean`, `Coverage.lean`, `Emit.lean` (replaces the stub main),
plus root `lean/Prod.lean` importing the Prod submodules (NOT Example — keep ProdLib
example-agnostic; `Prod.Emit` imports Example). Tag the five kernel defs
(`UorAtlas.stride/class_count/belt/classIndex/classDecode`) with `@[prod]`, replacing
their `-- M3:` comments.

Verified Lean 4.30.0 API facts (from leanprover/lean4 v4.30.0 sources — trust these):

- `Lean.Compiler.LCNF.toDecl : Name → CompilerM (Decl .pure)` — runs toLCNF:
  matches/recursors already `cases`, dictionaries explicit, instance wrappers unfolded.
- `Lean.Compiler.LCNF.CompilerM.run (x : CompilerM α) (s : State := {}) (phase : Phase := .base) : CoreM α`.
- Pure-phase shapes (`Lean/Compiler/LCNF/Basic.lean`):
  `Code := let (LetDecl) (Code) | fun (FunDecl) (Code) | jp (FunDecl) (Code) | jmp FVarId (Array Arg) | cases Cases | return FVarId | unreach Expr`
  `LetValue := lit LitValue | erased | proj Name Nat FVarId | const Name (List Level) (Array Arg) | fvar FVarId (Array Arg)`
  `Arg := erased | fvar FVarId | type Expr` — drop `erased`/`type` args, count them.
  `Alt := alt (ctorName) (params) (code) | default (code)`; `Cases := mk typeName resultType discr alts`.
  `Decl extends Signature` with `value : DeclValue .pure` — `#check DeclValue` and handle all constructors.
- `Lean.Compiler.LCNF.shouldGenerateCode (n : Name) : CoreM Bool` — coverage criterion.
- Module's own constants: iterate `env.constants.map₁` (imports live in map₂).
- Theorem deps: `ConstantInfo.value?` → `Expr.getUsedConstants`; size = Expr node
  count (document the counting); kernel_depth = longest chain in the module's own
  dependency graph.

Lowerer requirements:
- Emit sexp matching `rust/prod-ir` grammar EXACTLY — read `rust/sample.ir`,
  `rust/prod-ir/src/lib.rs`, `rust/prod-ir/src/parser.rs` first. Only extend the
  Rust parser if a needed form is missing; if you do, add tests, keep `cargo test` green.
- Def names: last component (`UorAtlas.stride` → `stride`), full name in a `;;` comment
  above each def (parser skips `;;` comments). Sanitize fvar binderNames to stable
  short idents (per-def counter fine); carry an `FVarId → String` map while descending.
- Operator whitelist (check parser.rs for exact keywords first):
  `Nat.add/sub/mul/div/mod/shiftLeft/shiftRight/pow/ble/blt` → arith/cmp nodes;
  unmapped consts → `(call name ...)` + counted as extern calls in coverage.
- `cases`→`cases` node, `proj`→`proj`, `jp/jmp`→`jp`/`jmp`, `return x`→value,
  `unreach`→`unreachable`, `fun`(lambda)→`opaque` + coverage note (closures are phase-2).
- Type lowering: `Nat/Bool/Int`→same, `UorAtlas.Instance`→`Instance`, else opaque-type
  form per parser.

Emit defaults (cwd is `lean/`): `../rust/prod-core/kernel.ir`, `../roots.json`,
`../coverage.md`; support `--out DIR`. Hand-rolled JSON with escaping (no deps).
Coverage classes: EXPORTED / EXPORTED-WITH-OPAQUE (list them) / SKIPPED (with
`shouldGenerateCode` reason guess). Include theorems (skipped: prop) and Instance
ctors/projections in coverage.md.

M3 verify gates:
- `lake build` exit 0; `lake exe prod-export` writes the three files.
- `cd rust && cargo run -p prod-cli -- parse ../rust/prod-core/kernel.ir` succeeds.
- All five kernel defs lower with ZERO opaque nodes (they're Nat arith + projections;
  if anything is opaque, find out why — don't accept it).
- `roots.json` has classIndex_bijective, classDecode_encode, digits_lt_stride with
  non-empty deps; validates with `python3 -m json.tool`.
- Semantic eyeball: classIndex = stride*h2 + O*d + l, belt = class_count * 2^(O-1)
  (association may differ from the legacy fixture — M4 tests values, not shapes).

## M4–M6 (after M3)

- M4: prod-core generated defs come ONLY from kernel.ir via `prod_defs!`; exporter
  `--goldens` dumps Lean `#eval` values; Rust tests assert equality
  (classIndex(1,2,3)=43, stride=24, class_count=96, belt=12288, decode∘encode
  roundtrips on instances (4,3,8), (2,2,4), (5,1,3)). `just prod` green. Watch for:
  `proj "UorAtlas.Instance" idx` vs prod-core's named-field struct — either extend
  the codegen field map or generate the struct from Lean; decide then, document it.
- M5: port roots analysis from old repo's `uor-atlas-roots/lib/{graph,pareto,connect}.ml`
  (OCaml, read-only reference) into prod-cli: `prod roots check|pareto|connect` on
  roots.json — actually compute (the old OCaml CLI printed canned strings; don't
  replicate that). Unit tests for dominates/pareto_front/bridge synthesis.
- M6: prod-wasm (wasm-bindgen: `generate(ir)`, `roots_pareto(json)`), CI for
  `just prod` + no_std/wasm32 build check, README final pass.
