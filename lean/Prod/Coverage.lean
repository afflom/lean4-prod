import Lean
import Prod.Extract
import Prod.Lower

/-!
# Coverage report (`coverage.md`)

Classifies every constant defined by the target module using Lean's own
`Lean.Compiler.LCNF.shouldGenerateCode` criterion:

- **EXPORTED** — `@[prod]`-tagged and lowered with no opaque nodes and no
  extern calls;
- **EXPORTED-WITH-OPAQUE** — tagged and lowered, but the body contains opaque
  markers and/or extern calls (listed in the details column);
- **SKIPPED** — everything else (theorems/Props, type formers, constructors,
  recursors, untagged definitions), with a reason guess.
-/

open Lean Compiler LCNF

namespace Prod

/-- Per-definition lowering report, fed by the emit driver after lowering. -/
structure DefReport where
  name : Name
  lowered : Bool
  opaques : Array String := #[]
  externs : Array String := #[]
  skipReason : String := ""

/-- Reason guess for a SKIPPED constant. -/
def skipReasonOf (n : Name) (ci : ConstantInfo) : CoreM String := do
  if ci.isTheorem then return "prop (theorem)"
  match ci with
  | .thmInfo _ => return "prop (theorem)"
  | .inductInfo _ => return "type-former (inductive)"
  | .ctorInfo _ => return "constructor (runtime primitive)"
  | .recInfo _ => return "recursor (internal)"
  | .quotInfo _ => return "quot (internal)"
  | .opaqueInfo _ => return "no-value (opaque)"
  | .defnInfo _ =>
    if !(← shouldGenerateCode n) then
      return "no-codegen (shouldGenerateCode = false)"
    return "untagged (no @[prod])"
  | _ => return "no-value (constant without definition)"

private def row (name : Name) (status detail : String) : String :=
  let detail := if detail.isEmpty then "—" else detail
  s!"| `{name}` | {status} | {detail} |"

/-- Build the markdown coverage report. -/
def buildCoverage (moduleRoot : Name)
    (own : Array (Name × ConstantInfo)) (reports : Array DefReport) : CoreM String := do
  let mut rows : Array String := #[]
  let mut (exported, withOpaque, skipped) := (0, 0, 0)
  for (n, ci) in own do
    match reports.find? (·.name == n) with
    | some r =>
      if !r.lowered then
        skipped := skipped + 1
        rows := rows.push (row n "SKIPPED" r.skipReason)
      else if r.opaques.isEmpty && r.externs.isEmpty then
        exported := exported + 1
        rows := rows.push (row n "EXPORTED" "")
      else
        withOpaque := withOpaque + 1
        let opaques := r.opaques.toList.map ("opaque: " ++ ·)
        let externs := r.externs.toList.map ("extern: " ++ ·)
        rows := rows.push (row n "EXPORTED-WITH-OPAQUE" (String.intercalate ", " (opaques ++ externs)))
    | none =>
      skipped := skipped + 1
      rows := rows.push (row n "SKIPPED" (← skipReasonOf n ci))
  let header := String.intercalate "\n" [
    "# prod-export coverage report",
    "",
    s!"Module root: `{moduleRoot}` — classification via Lean's own `LCNF.shouldGenerateCode`.",
    "",
    s!"- Total module-own constants: {own.size}",
    s!"- EXPORTED: {exported}",
    s!"- EXPORTED-WITH-OPAQUE: {withOpaque}",
    s!"- SKIPPED: {skipped}",
    "",
    "| Constant | Status | Details |",
    "| --- | --- | --- |"]
  return header ++ "\n" ++ String.intercalate "\n" rows.toList ++ "\n"

end Prod
