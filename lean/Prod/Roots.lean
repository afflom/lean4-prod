import Lean
import Prod.Extract
import Prod.Lower

/-!
# Proof-root metadata (`roots.json`)

Every theorem defined by the target module is a *root*. For each root we emit:

- `id` — the theorem's FULL Lean name (`UorAtlas.classIndex_bijective`,
  `_private.Example.Proofs.S1.0.UorAtlas.digits_lt_stride`). Full names are
  unique by kernel construction, so root ids never collide; short display
  names are derived CLI-side;
- `auto` — `true` for Lean-generated machinery (see `isAutoRoot`), `false`
  for hand-written theorems. All roots stay in the JSON (completeness for
  coverage); filtering happens CLI-side;
- `dependencies` — direct constant dependencies of the proof term
  (`Expr.getUsedConstants` on `ConstantInfo.value?`), full names, sorted;
- `proof_term_size` — node count of the proof `Expr` (apps, binders, mdata and
  projections count 1 plus their children; atoms count 1);
- `kernel_depth` — longest dependency chain through module-own constants,
  computed over the module's own dependency graph. Theorem graphs are DAGs,
  but recursive definitions self-cycle; back edges to a node on the current
  DFS stack contribute 0 (longest chain over the cycle-condensed graph);
- `check_time_ns` — wall time (monotonic clock, nanoseconds) for re-typechecking
  the proof term with the actual kernel (`Lean.Kernel.check`, empty local
  context), taken as the minimum over 16 repetitions to suppress µs-scale
  scheduling noise. Machine-dependent; meaningful only as a *relative* cost
  signal within one export run. This is the third Pareto objective.

JSON is hand-rolled (no external deps) with minimal string escaping.
-/

open Lean

namespace Prod

/-- Expression node count; see module doc for the counting rule. -/
partial def termSize : Expr → Nat
  | .app f a => 1 + termSize f + termSize a
  | .lam _ t b _ => 1 + termSize t + termSize b
  | .forallE _ t b _ => 1 + termSize t + termSize b
  | .letE _ t v b _ => 1 + termSize t + termSize v + termSize b
  | .mdata _ b => 1 + termSize b
  | .proj _ _ b => 1 + termSize b
  | _ => 1

/-- Module-own dependency edges: name → module-own constants its value uses.
    (`allowOpaque := true` so theorem proofs count as values.) -/
def ownDepMap (own : Array (Name × ConstantInfo)) : Std.HashMap Name (Array Name) :=
  let ownNames : Std.HashSet Name := own.foldl (fun s (n, _) => s.insert n) {}
  own.foldl (init := {}) fun m (n, ci) =>
    match ci.value? (allowOpaque := true) with
    | some v => m.insert n (v.getUsedConstants.filter ownNames.contains)
    | none => m.insert n #[]

/-- Longest dependency chain starting at `n`, memoized in `m`, with `visiting`
    holding the current DFS stack. The graph is a DAG for theorems (Lean proofs
    cannot self-reference), but recursive DEFINITIONS (e.g. `digitCount`) have
    self-cycles; a back edge to a node already on the stack contributes 0 —
    the recursive call is one node in the chain, not infinitely many. This is
    longest-chain semantics over the cycle-condensed graph. -/
partial def depthOf (deps : Std.HashMap Name (Array Name)) (m : Std.HashMap Name Nat)
    (visiting : Std.HashSet Name) (n : Name)
    : Std.HashMap Name Nat × Std.HashSet Name × Nat :=
  match m[n]? with
  | some d => (m, visiting, d)
  | none =>
    if visiting.contains n then (m, visiting, 0)
    else
      let (m', visiting', best) := (deps.getD n #[]).foldl
        (init := (m, visiting.insert n, 0)) fun (m, vis, best) d =>
          let (m', vis', dd) := depthOf deps m vis d
          (m', vis', max best (dd + 1))
      (m'.insert n best, visiting'.erase n, best)

/-- One proof root. -/
structure RootInfo where
  id : String
  auto : Bool
  dependencies : Array Name
  size : Nat
  depth : Nat
  checkTimeNs : Nat

/-- String components of a name (numeric components skipped; order irrelevant
    for the checks below). -/
def nameComponents : Name → List String
  | .anonymous => []
  | .str p s => s :: nameComponents p
  | .num p _ => nameComponents p

/-- Heuristic: is this theorem auto-generated Lean machinery rather than a
    hand-written proof root?

    A theorem counts as *auto* when:
    - any name component starts with `_proof_` (omega/decide certificates,
      e.g. `UorAtlas.classIndex_bijective._proof_1_1`);
    - any component is `eq_` followed by digits (equation lemmas, `f.eq_1`);
    - any component is exactly `sizeOf_spec`, `inj`, or `injEq`
      (compiler-generated sizeOf / injectivity lemmas);
    - its parent prefix is a module-own inductive type (structure projections
      to `Prop`, e.g. `UorAtlas.Instance.valid`).

    Everything else — including `_private.…`-mangled names of hand-written
    `private theorem`s such as `digits_lt_stride` — stays a genuine root
    (`auto := false`). When in doubt we prefer `false`: a spurious root is
    only noise in the analysis, while a wrongly hidden root loses real
    coverage data. -/
def isAutoRoot (inductives : Std.HashSet Name) (n : Name) : Bool :=
  let comps := nameComponents n
  comps.any (fun c =>
    c.startsWith "_proof_" || c == "sizeOf_spec" || c == "inj" || c == "injEq" ||
    (c.length > 3 && c.startsWith "eq_" && (c.drop 3).all Char.isDigit)) ||
  inductives.contains n.getPrefix

/-- Kernel re-check wall time of one proof term, in nanoseconds: the MINIMUM
    over `reps` repetitions of `Lean.Kernel.check` on the value in an empty
    local context. Single-shot timings at this granularity (µs) are dominated
    by scheduling/GC noise and flipped root orderings between runs; taking the
    minimum (standard micro-benchmarking practice — best case = least
    interference) makes the ordering reproducible enough to serve as the third
    Pareto objective. Each `match` forces the `Except` (and with it the extern
    kernel call) before the clock is read again. Failing to re-check a term
    the kernel has already accepted is an exporter bug, so we throw. -/
def kernelCheckTimeNs (env : Environment) (v : Expr) (reps : Nat := 16) : CoreM Nat := do
  let mut best := 0
  for _ in [:reps] do
    let t0 ← liftM (m := IO) (IO.monoNanosNow : BaseIO Nat)
    match Kernel.check env {} v with
    | .ok _ => pure ()
    | .error _ => throwError "kernel re-check failed for a previously accepted proof term"
    let t1 ← liftM (m := IO) (IO.monoNanosNow : BaseIO Nat)
    let dt := t1 - t0
    if best == 0 || dt < best then
      best := dt
  return best

/-- Extract every theorem of the target module as a proof root. -/
def computeRoots (own : Array (Name × ConstantInfo)) : CoreM (Array RootInfo) := do
  let env ← getEnv
  let depMap := ownDepMap own
  let inductives : Std.HashSet Name := own.foldl (init := {}) fun s (n, ci) =>
    match ci with
    | .inductInfo _ => s.insert n
    | _ => s
  let mut depths : Std.HashMap Name Nat := {}
  for (n, _) in own do
    depths := (depthOf depMap depths {} n).1
  let mut roots := #[]
  for (n, ci) in own do
    if ci.isTheorem then
      if let some v := ci.value? (allowOpaque := true) then
        let checkTimeNs ← kernelCheckTimeNs env v
        roots := roots.push {
          id := toString n
          auto := isAutoRoot inductives n
          dependencies := v.getUsedConstants.qsort (Name.quickCmp · · == .lt)
          size := termSize v
          depth := depths.getD n 0
          checkTimeNs }
  return roots

/-- Escape a string for JSON (quotes and backslashes; names never contain
    control characters). -/
def jsonEscape (s : String) : String :=
  String.ofList <| s.toList.flatMap fun
    | '"' => ['\\', '"']
    | '\\' => ['\\', '\\']
    | c => [c]

/-- Render roots as JSON:
    `{"roots":[{"id":...,"auto":B,"dependencies":[...],"proof_term_size":N,"kernel_depth":K,"check_time_ns":T},...]}` -/
def rootsJson (roots : Array RootInfo) : String :=
  let entries := roots.toList.map fun r =>
    let deps := r.dependencies.toList.map fun d => s!"\"{jsonEscape (toString d)}\""
    "    {\"id\":\"" ++ jsonEscape r.id ++ "\",\"auto\":" ++
    (if r.auto then "true" else "false") ++ ",\"dependencies\":[" ++
    String.intercalate "," deps ++ "],\"proof_term_size\":" ++ toString r.size ++
    ",\"kernel_depth\":" ++ toString r.depth ++
    ",\"check_time_ns\":" ++ toString r.checkTimeNs ++ "}"
  let body := if entries.isEmpty then "" else "\n" ++ String.intercalate ",\n" entries ++ "\n  "
  "{\n  \"roots\": [" ++ body ++ "]\n}\n"

end Prod
