import Prod.Lower

open Lean Compiler LCNF

run_meta do
  let erased := mkConst ``lcErased
  let decision := mkApp (mkConst ``Decidable) erased
  let input : FVarId := ⟨`input⟩
  let proof : Param .pure := ⟨⟨`proof⟩, `proof, erased, false⟩
  let output : FVarId := ⟨`output⟩
  let state : Prod.LowerState := {
    names := ({} : Std.HashMap Name String).insert input.name "input"
    fvarTypes := ({} : Std.HashMap Name Expr).insert input.name decision
  }
  let run := fun action => (action.run { tagged := #[] }).run state
  for (name, expected) in [(``Decidable.isFalse, "false"), (``Decidable.isTrue, "true")] do
    let (text, facts) ← run (Prod.lowerLetValue (.const name [] #[.erased, .erased]) (some decision))
    unless text == expected && facts.dropped == 2 && facts.externs.isEmpty && facts.opaques.isEmpty do
      throwError "incorrect decision tag: {name}: {text}"
  let (ty, _) ← run (Prod.lowerType decision)
  unless ty == "Bool" do throwError "decision type did not retain its Bool tag"
  let body := Code.return output
  let cases := fun (name : Name) (params : Array (Param .pure)) (branch : Code .pure) =>
    Code.cases (.mk ``Decidable (mkConst ``Nat) input
      #[.alt name params branch, .default body])
  let (text, facts) ← run (Prod.lowerCode (cases ``Decidable.isTrue #[proof] body))
  unless text == "(cases input (alt \"Bool.true\" () output) (default output))" && facts.dropped == 1 do
    throwError "decision case did not erase exactly the proof: {text}"
  let reject := fun (label : String) (action : Prod.LowerM String) => do
    let rejected ← try
      let _ ← run action
      pure false
    catch _ => pure true
    unless rejected do throwError "unsafe decision shape accepted: {label}"
  for (label, args, result) in [
      ("missing argument", #[Arg.erased], some decision),
      ("extra erased argument", #[Arg.erased, .erased, .erased], some decision),
      ("computational proposition", #[Arg.fvar input, .erased], some decision),
      ("computational proof", #[Arg.erased, .fvar input], some decision),
      ("type instead of proof", #[Arg.erased, .type erased], some decision),
      ("wrong result", #[Arg.erased, .erased], some (mkConst ``Nat)),
      ("missing result", #[Arg.erased, .erased], none)] do
    for name in [``Decidable.isFalse, ``Decidable.isTrue] do
      reject label (Prod.lowerLetValue (.const name [] args) result)
  for (label, code) in [
      ("missing proof binder", cases ``Decidable.isTrue #[] body),
      ("extra proof binder", cases ``Decidable.isTrue #[proof, proof] body),
      ("computational binder", cases ``Decidable.isTrue #[{ proof with type := mkConst ``Nat }] body),
      ("returned proof", cases ``Decidable.isTrue #[proof] (.return proof.fvarId)),
      ("wrong constructor", cases ``Bool.true #[proof] body)] do
    reject label (Prod.lowerCode code)
  let wrongType : Prod.LowerM String := do
    modify fun st => { st with fvarTypes := st.fvarTypes.insert input.name (mkConst ``Nat) }
    Prod.lowerCode (cases ``Decidable.isFalse #[proof] body)
  reject "wrong discriminant type" wrongType
  unless (Prod.decidableTag? `Other.Decidable.isTrue #[.erased, .erased] (some decision)).isNone do
    throwError "decision recognition admitted an unrelated name"
  logInfo "shared decisions: exact tags/type/proof erasure and 21 rejection cases passed"
