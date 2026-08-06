import Lean
import Prod.Attribute

/-!
# LCNF extraction for `@[prod]`-tagged definitions

`extractTagged` runs Lean's own `toLCNF` translation (`Lean.Compiler.LCNF.toDecl`)
on every tagged definition. At this point matches/recursors are already `cases`,
typeclass dictionaries are explicit arguments, instance wrappers are unfolded,
and proofs appear as erased arguments — we never touch surface syntax ourselves.

Also provides `ownConstants`: the constants defined by the target module
(identified via module indices, since after `importModules` everything lives in
the imported-constants map, not `map₁`).
-/

open Lean Compiler LCNF

namespace Prod

/-- Result of attempting LCNF extraction for one tagged name. -/
structure ExtractedDef where
  name       : Name
  decl?      : Option (Decl .pure)
  /-- Why extraction was skipped ("" when `decl?` is `some`). -/
  skipReason : String

/-- All constants defined by the module tree rooted at `moduleRoot`
    (e.g. `Example` covers `Example.Kernel`, `Example.Proofs.S1`, ...),
    sorted by name for deterministic output. -/
def ownConstants (env : Environment) (moduleRoot : Name) : Array (Name × ConstantInfo) :=
  let mods := env.allImportedModuleNames
  let own := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      match mods[idx]? with
      | some mn => if mn.getRoot == moduleRoot then acc.push (n, ci) else acc
      | none => acc
    | none => acc  -- not part of any imported module (none in this env)
  own.qsort fun (a, _) (b, _) => Name.quickCmp a b == .lt

/-- The tagged names, in deterministic (sorted) order.

    NOTE: `prodAttr.ext.getState env` is empty in 4.30 even though the
    attribute is applied (async env-extension entries are not folded into
    `getState` here); `TagAttribute.hasTag` is the reliable query, so we
    enumerate the module's own constants and filter by it. -/
def taggedNames (env : Environment) (moduleRoot : Name) : List Name :=
  (ownConstants env moduleRoot).toList.filterMap fun (n, _) =>
    if prodAttr.hasTag env n then some n else none

/-- Extract the pure-phase LCNF declaration for every `@[prod]`-tagged name.

    Names are skipped (with a logged note) when they have no value or when
    Lean's own `shouldGenerateCode` criterion rejects them (Props, type
    formers, `macro_inline`, matchers, ...). -/
def extractTagged (moduleRoot : Name) : CoreM (Array ExtractedDef) := do
  let env ← getEnv
  let mut out := #[]
  for name in taggedNames env moduleRoot do
    let some ci := env.find? name
      | logInfo m!"prod: skipping {name} (not in environment)"
        continue
    if ci.value?.isNone then
      logInfo m!"prod: skipping {name} (no value)"
      out := out.push { name, decl? := none, skipReason := "no-value" }
      continue
    if !(← shouldGenerateCode name) then
      logInfo m!"prod: skipping {name} (shouldGenerateCode = false)"
      out := out.push { name, decl? := none, skipReason := "no-codegen" }
      continue
    let decl ← CompilerM.run do
      let d ← toDecl name
      -- The base toLCNF translation keeps overloaded operators as instance
      -- wrappers (`instHMul`/`instMulNat` chains, `OfNat` literals). Lean's own
      -- simplifier pass reduces them to kernel calls (`Nat.mul`, `Nat.pow`, ...)
      -- and raw literals.
      d.simp {}
    out := out.push { name, decl? := some decl, skipReason := "" }
  return out

end Prod
