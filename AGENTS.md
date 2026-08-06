# lean4-prod — agent handoff / project guide

You are working in `/Users/auser/work/rust/mine/lean4-prod`: a Lean 4 → production
Rust generator. Tag `@[prod]` definitions in Lean; a metaprogram extracts them via
Lean's OWN compiler frontend (LCNF — Lean Compiler Normal Form), emits a sexp IR;
pure `no_std` Rust libraries parse it and generate zero-cost Rust (proc-macro, CLI,
wasm shells). Theorem "roots" metadata (deps, proof-term size, kernel depth) feeds
Pareto/connection analysis in the CLI. Full architecture: see README.md.

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
  The Pareto front of hand-written roots is currently just `digits_lt_stride`
  (it dominates the other two real theorems on size and depth).
- Pareto uses proof-term size and kernel depth because check-time data is not in
  the current exporter schema.

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
