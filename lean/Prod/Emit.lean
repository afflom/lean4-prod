import Lean
import Prod
import Example
import Conformance

/-!
# prod-export — entry point

Imports the target module (`Example`), extracts every `@[prod]`-tagged
definition through Lean's own LCNF pipeline (`Prod.Extract`), lowers the
pure-phase declarations to the sexp IR (`Prod.Lower`), and writes:

- `kernel.ir` — the lowered definitions (parsed by Rust `prod-ir`);
- `roots.json` — proof-root metadata (`Prod.Roots`);
- `coverage.md` — per-constant coverage report (`Prod.Coverage`);
- `goldens.ir` — golden values for the kernel defs, computed by running the
  actual compiled Lean definitions on the TF1 instances (same evaluation
  `decide`-checked proofs quantify over). Each golden is a zero-arg def;
  Rust tests assert the generated fns reproduce these values.

Usage: `lake exe prod-export [--out DIR]`. Defaults (cwd = `lean/`):
`../rust/prod-core/kernel.ir`, `../roots.json`, `../coverage.md`,
`../rust/prod-core/goldens.ir`.
-/

open Lean

namespace Prod

/-- Module tree analyzed/exported by this run of prod-export. -/
def targetModule : Name := `Example

/-- IR module name (kept identical to the legacy fixture for continuity). -/
def targetIrModule : String := "UorAtlas.Kernel"

/-- Module tree whose lowering is pinned by a committed golden IR file. -/
def conformanceModule : Name := `Conformance

/-- IR module name for the conformance export. -/
def conformanceIrModule : String := "Conformance"

/-- Module whose lowering is pinned but whose codegen is a deliberate
    rejection. Separate from `conformanceModule` so that corpus can promise
    that everything in it also generates Rust which compiles — enforced by
    `rust/prod-codegen-compile-tests`. -/
def conformanceRejectedModule : Name := `ConformanceRejected

/-- IR module name for the rejected-conformance export. -/
def conformanceRejectedIrModule : String := "ConformanceRejected"

/-! ## Published subset contract

Machine-readable description of the Lean-side lowering surface, consumed by
`prod subset` to render `specs/lean-for-production.md`. Hand-rolled JSON, no
dependencies, matching how `rootsJson` is built. The operator and decider
lists are derived from `numOpNames`/`deciderNames` (`Prod.Lower`) — the same
association lists `opWhitelist`/`deciderOp` consume to decide what actually
lowers — so the published contract cannot describe more, or less, than the
lowerer accepts. -/

/-- Machine-readable description of what `Lower.lean` can lower: operators,
    decidable guards, and the supported type shapes. Consumed by `prod
    subset` (`prod-cli`), which merges it with codegen's rejection list to
    render the published contract. -/
def subsetJson : String :=
  let ops := numOpNames.map fun r => toString r.1
  let deciders := deciderNames.map fun p => toString p.1
  -- `Nat`/`Bool`/`Int`/`Prod`/`List`/`Option` are built into the IR type
  -- grammar (`lowerType`); anything else is a user inductive, and
  -- `lowerTypeDecl` supports exactly parameterless, non-recursive,
  -- single-block inductives with a single constructor (`Prop` fields
  -- erased) — the only shape the conformance suite exercises
  -- (`Conformance.MidProp`, `Conformance.NoProp`, `UorAtlas.Instance`).
  let types := ["Nat", "Bool", "Int (renders as i64; checked add/sub/mul/neg/pow, Euclidean checked div/mod (Int.ediv/Int.emod); shifts are not whitelisted for Int)",
                "Prod", "List", "Option",
                "parameterless, non-recursive, single-constructor structures (Prop fields erased)"]
  let quoted (xs : List String) : String :=
    String.intercalate ", " (xs.map fun s => "\"" ++ jsonEscape s ++ "\"")
  "{\n  \"operators\": [" ++ quoted ops ++ "],\n  \"deciders\": [" ++ quoted deciders ++
    "],\n  \"types\": [" ++ quoted types ++ "]\n}\n"

/-- Rendered `(type ...)` declarations for every inductive reachable from the
    extracted definitions — from their signatures *and* from the constructor
    applications and projections in their bodies (`declTypeNames`) —
    deduplicated and in sorted order. -/
def collectTypeDecls (ctx : LowerCtx) (extracted : Array ExtractedDef)
    : CoreM (Array String) := do
  let env ← getEnv
  let mut wanted : Array Name := #[]
  for ed in extracted do
    if let some decl := ed.decl? then
      for n in declTypeNames env decl do
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

/-- Assemble the full `kernel.ir` text and per-definition reports. -/
def emitKernelIr (ctx : LowerCtx) (irModule : String) (extracted : Array ExtractedDef)
    : CoreM (String × Array DefReport) := do
  let mut ir := s!";; Generated by prod-export: LCNF → sexp IR.\n(module {irModule}\n"
  let typeDecls ← collectTypeDecls ctx extracted
  for decl in typeDecls do
    ir := ir ++ "\n" ++ indent 2 decl ++ "\n"
  let mut reports : Array DefReport := #[]
  for ed in extracted do
    match ed.decl? with
    | some decl =>
      let (sexp, st) ← lowerDecl ctx decl
      let arityNote := if st.dropped == 0 then "" else s!"\n  ;; arity: {st.dropped} erased/type args dropped"
      ir := ir ++ s!"\n  ;; full: {ed.name}{arityNote}\n" ++ indent 2 sexp ++ "\n"
      reports := reports.push
        { name := ed.name, lowered := true, opaques := st.opaques, externs := st.externs }
    | none =>
      reports := reports.push { name := ed.name, lowered := false, skipReason := ed.skipReason }
  return (ir ++ ")\n", reports)

/-- The whole export, as a CoreM computation over the imported environment. -/
def runExport : CoreM (String × String × String × String × String) := do
  let env ← getEnv
  let ctx : LowerCtx := { tagged := (taggedNames env targetModule).toArray }
  let extracted ← extractTagged targetModule
  let (ir, reports) ← emitKernelIr ctx targetIrModule extracted
  let own := ownConstants env targetModule
  let roots := rootsJson (← computeRoots own)
  let coverage ← buildCoverage targetModule own reports
  let confCtx : LowerCtx := { tagged := (taggedNames env conformanceModule).toArray }
  let confExtracted ← extractTagged conformanceModule
  let (confIr, _) ← emitKernelIr confCtx conformanceIrModule confExtracted
  let rejCtx : LowerCtx := { tagged := (taggedNames env conformanceRejectedModule).toArray }
  let rejExtracted ← extractTagged conformanceRejectedModule
  let (rejIr, _) ← emitKernelIr rejCtx conformanceRejectedIrModule rejExtracted
  return (ir, roots, coverage, confIr, rejIr)

/-- `runExport` with exceptions rendered to strings (while CoreM context for
    pretty-printing is still available). -/
def runExportSafe : CoreM (Except String (String × String × String × String × String)) := do
  try
    pure (.ok (← runExport))
  catch e =>
    pure (.error (← e.toMessageData.toString))

/-! ## Goldens (M4)

Golden values are computed by *calling the compiled Lean definitions* — the
very functions the theorems quantify over, compiled by the same toolchain —
on the three TF1 instances. Each golden is emitted as a zero-arg sexp `def`
in a second IR module (`goldens.ir`), so Rust can consume it with the same
`prod_defs!` machinery and assert the generated fns reproduce Lean's values.
`classDecode`'s pair value is expressed as nested `(ctor "Prod.mk" ...)`
literal exprs, matching the IR's `Tuple` type. -/

/-- TF1 canonical instance (q=4, T=3, O=8); validity discharged by `decide`. -/
def instCanonical : UorAtlas.Instance := ⟨4, 3, 8, by decide⟩
/-- TF1 demo-small instance (q=2, T=2, O=4). -/
def instDemoSmall : UorAtlas.Instance := ⟨2, 2, 4, by decide⟩
/-- TF1 third instance (q=5, T=1, O=3). -/
def instThird : UorAtlas.Instance := ⟨5, 1, 3, by decide⟩

/-- One golden: a zero-arg def name, its IR return type, and its value body. -/
structure GoldenEntry where
  name : String
  ret : String := "Nat"
  value : String

/-- Render a `List Nat` value as nested IR ctor sexps (`List.cons`/`List.nil`),
    matching how the lowerer emits constructor applications. -/
partial def listCtorSexp : List Nat → String
  | [] => "(ctor \"List.nil\")"
  | h :: t => s!"(ctor \"List.cons\" {h} {listCtorSexp t})"

/-- Render an `Option (Nat × Nat × Nat)` value as nested IR ctor sexps. -/
def optTripleSexp : Option (Nat × Nat × Nat) → String
  | some (h2, d, l) => s!"(ctor \"Option.some\" (ctor \"Prod.mk\" {h2} (ctor \"Prod.mk\" {d} {l})))"
  | none => "(ctor \"Option.none\")"

/-- All goldens: `stride`/`class_count`/`belt` on each TF1 instance, plus
    `classIndex 1 2 3` and `classDecode 43` at the canonical instance. -/
def goldenEntries : Array GoldenEntry := Id.run do
  let mut out := #[]
  for (label, inst) in
      [("canonical", instCanonical), ("demo_small", instDemoSmall), ("third", instThird)] do
    out := out.push { name := s!"golden_stride_{label}", value := toString (UorAtlas.stride inst) }
    out := out.push { name := s!"golden_class_count_{label}", value := toString (UorAtlas.class_count inst) }
    out := out.push { name := s!"golden_belt_{label}", value := toString (UorAtlas.belt inst) }
  let c := instCanonical
  out := out.push { name := "golden_classIndex_1_2_3_canonical", value := toString (UorAtlas.classIndex 1 2 3 c) }
  let (h2, dl) := UorAtlas.classDecode 43 c
  let (d, l) := dl
  out := out.push { name := "golden_classDecode_43_canonical", ret := "(Tuple Nat (Tuple Nat Nat))", value := s!"(ctor \"Prod.mk\" {h2} (ctor \"Prod.mk\" {d} {l}))" }
  out := out.push { name := "golden_digitCount_43_canonical", value := toString (UorAtlas.digitCount 10 43 c) }
  out := out.push { name := "golden_digitCount_511_canonical", value := toString (UorAtlas.digitCount 10 511 c) }
  out := out.push { name := "golden_digitCount_zero_fuel_canonical", value := toString (UorAtlas.digitCount 0 999 c) }
  out := out.push { name := "golden_digits_43_canonical", ret := "(List Nat)", value := listCtorSexp (UorAtlas.digits 10 43 c) }
  out := out.push { name := "golden_digitSum_digits_43_canonical", value := toString (UorAtlas.digitSum (UorAtlas.digits 10 43 c)) }
  out := out.push { name := "golden_sameClass_43_44_canonical", ret := "Bool", value := toString (UorAtlas.sameClass 43 44 c) }
  out := out.push { name := "golden_sameClass_43_67_canonical", ret := "Bool", value := toString (UorAtlas.sameClass 43 67 c) }
  out := out.push { name := "golden_smallEnough_100_canonical", ret := "Bool", value := toString (UorAtlas.smallEnough 100 c) }
  out := out.push { name := "golden_smallEnough_20000_canonical", ret := "Bool", value := toString (UorAtlas.smallEnough 20000 c) }
  out := out.push { name := "golden_tryClassDecode_43_canonical", ret := "(Option (Tuple Nat (Tuple Nat Nat)))", value := optTripleSexp (UorAtlas.tryClassDecode 43 c) }
  out := out.push { name := "golden_tryClassDecode_100_canonical", ret := "(Option (Tuple Nat (Tuple Nat Nat)))", value := optTripleSexp (UorAtlas.tryClassDecode 100 c) }
  -- Euclidean, not truncating: computed by calling the compiled `Int` `/`/`%`
  -- instances (`Int.ediv`/`Int.emod`) themselves, so the golden comes from
  -- Lean, not from anyone's expectation of what Euclidean division gives.
  out := out.push { name := "golden_int_ediv_neg_12_7", ret := "Int",
                    value := toString (Conformance.c_int_ediv (-12) 7) }
  out := out.push { name := "golden_int_emod_neg_12_7", ret := "Int",
                    value := toString (Conformance.c_int_emod (-12) 7) }
  return out

/-- Assemble the `goldens.ir` text: one zero-arg def per golden. -/
def emitGoldensIr : String := Id.run do
  let mut ir := s!";; Generated by prod-export (M4): golden values computed by the compiled\n\
    ;; Lean kernel defs on the TF1 instances (canonical/demo_small/third).\n(module UorAtlas.Goldens\n"
  for e in goldenEntries do
    ir := ir ++ s!"\n  (def {e.name} () {e.ret} {e.value})\n"
  return ir ++ ")\n"

end Prod

private def parseOutDir : List String → Option System.FilePath
  | "--out" :: dir :: _ => some dir
  | _ :: rest => parseOutDir rest
  | [] => none

/-- `unsafe` because `Lean.enableInitializersExecution` is an unsafe
    primitive: running imported modules' initializers is required for
    `importModules (loadExts := true)`, which loads env-extension data
    (LCNF `baseExt`, class/instance attribute states) that the simplifier
    needs to unfold instance wrappers (`instHMul`/`instMulNat` chains) to
    kernel calls (`Nat.mul`, ...). -/
unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := Prod.targetModule }, { module := Prod.conformanceModule },
      { module := Prod.conformanceRejectedModule }]
    {} (leakEnv := true) (loadExts := true)
  let coreCtx : Core.Context := { fileName := "prod-export", fileMap := default }
  let eio := (ReaderT.run Prod.runExportSafe coreCtx).run { env := env }
  let result ← EIO.toIO' eio
  let (ir, roots, coverage, confIr, rejIr) ← match result with
    | Except.ok (Except.ok outputs, _st) => pure outputs
    | Except.ok (Except.error msg, _st) => throw (IO.userError s!"prod-export failed: {msg}")
    | Except.error _ => throw (IO.userError "prod-export failed: uncaught exception")
  let (irPath, rootsPath, covPath, goldensPath, confPath, rejPath, subsetPath) := match parseOutDir args with
    | some dir =>
      (dir / "kernel.ir", dir / "roots.json", dir / "coverage.md", dir / "goldens.ir",
       dir / "conformance-golden.ir", dir / "conformance-golden-rejected.ir",
       dir / "subset.json")
    | none =>
      ("../rust/prod-core/kernel.ir", "../roots.json", "../coverage.md",
       "../rust/prod-core/goldens.ir", "Conformance/golden.ir",
       "Conformance/golden-rejected.ir", "../subset.json")
  IO.FS.writeFile irPath ir
  IO.FS.writeFile rootsPath roots
  IO.FS.writeFile covPath coverage
  IO.FS.writeFile goldensPath Prod.emitGoldensIr
  IO.FS.writeFile confPath confIr
  IO.FS.writeFile rejPath rejIr
  IO.FS.writeFile subsetPath Prod.subsetJson
  IO.println s!"prod-export: wrote {irPath}, {rootsPath}, {covPath}, {goldensPath}, {confPath}, {rejPath}, {subsetPath}"
