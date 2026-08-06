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
  computed over the module's own dependency graph (Lean's kernel guarantees
  acyclicity, so a memoized fold terminates).

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

/-- Longest dependency chain starting at `n`, memoized in `m`.
    The graph is a DAG (Lean forbids circular definitions). -/
partial def depthOf (deps : Std.HashMap Name (Array Name)) (m : Std.HashMap Name Nat)
    (n : Name) : Std.HashMap Name Nat × Nat :=
  match m[n]? with
  | some d => (m, d)
  | none =>
    let (m', best) := (deps.getD n #[]).foldl (init := (m, 0)) fun (m, best) d =>
      let (m', dd) := depthOf deps m d
      (m', max best (dd + 1))
    (m'.insert n best, best)

/-- One proof root. -/
structure RootInfo where
  id : String
  auto : Bool
  dependencies : Array Name
  size : Nat
  depth : Nat

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

/-- Extract every theorem of the target module as a proof root. -/
def computeRoots (own : Array (Name × ConstantInfo)) : Array RootInfo := Id.run do
  let depMap := ownDepMap own
  let inductives : Std.HashSet Name := own.foldl (init := {}) fun s (n, ci) =>
    match ci with
    | .inductInfo _ => s.insert n
    | _ => s
  let mut depths : Std.HashMap Name Nat := {}
  for (n, _) in own do
    depths := (depthOf depMap depths n).1
  let mut roots := #[]
  for (n, ci) in own do
    if ci.isTheorem then
      if let some v := ci.value? (allowOpaque := true) then
        roots := roots.push {
          id := toString n
          auto := isAutoRoot inductives n
          dependencies := v.getUsedConstants.qsort (Name.quickCmp · · == .lt)
          size := termSize v
          depth := depths.getD n 0 }
  return roots

/-- Escape a string for JSON (quotes and backslashes; names never contain
    control characters). -/
def jsonEscape (s : String) : String :=
  String.ofList <| s.toList.flatMap fun
    | '"' => ['\\', '"']
    | '\\' => ['\\', '\\']
    | c => [c]

/-- Render roots as JSON:
    `{"roots":[{"id":...,"auto":B,"dependencies":[...],"proof_term_size":N,"kernel_depth":K},...]}` -/
def rootsJson (roots : Array RootInfo) : String :=
  let entries := roots.toList.map fun r =>
    let deps := r.dependencies.toList.map fun d => s!"\"{jsonEscape (toString d)}\""
    "    {\"id\":\"" ++ jsonEscape r.id ++ "\",\"auto\":" ++
    (if r.auto then "true" else "false") ++ ",\"dependencies\":[" ++
    String.intercalate "," deps ++ "],\"proof_term_size\":" ++ toString r.size ++
    ",\"kernel_depth\":" ++ toString r.depth ++ "}"
  let body := if entries.isEmpty then "" else "\n" ++ String.intercalate ",\n" entries ++ "\n  "
  "{\n  \"roots\": [" ++ body ++ "]\n}\n"

end Prod
