import Prod.Lower

open Lean Compiler LCNF

run_meta do
  let input : FVarId := ⟨`input⟩
  let run := fun (name : Name) (inputType resultType : Expr) (arguments : Array (Arg .pure)) => do
    let state : Prod.LowerState := {
      names := ({} : Std.HashMap Name String).insert input.name "input"
      fvarTypes := ({} : Std.HashMap Name Expr).insert input.name inputType
    }
    ((Prod.lowerLetValue (.const name [] arguments) (some resultType)).run { tagged := #[] }).run state
  for (name, arguments) in [
      (``String.length, #[Arg.fvar input]),
      (`Fixture.LexLeanRuntime.length, #[Arg.type (mkConst ``String), .erased, .fvar input])] do
    let (text, state) ← run name (mkConst ``String) (mkConst ``Nat) arguments
    unless text == "(string-length input)" && state.externs.isEmpty do
      throwError "string length lost exact meaning: {text}"
  let (text, state) ← run `Fixture.LexLeanRuntime.length (mkConst ``ByteArray) (mkConst ``Nat)
    #[.type (mkConst ``ByteArray), .erased, .fvar input]
  unless text == "(length input)" && state.externs.isEmpty do
    throwError "byte length changed meaning: {text}"
  for (inputType, resultType) in [(mkConst ``ByteArray, mkConst ``Nat), (mkConst ``String, mkConst ``Bool)] do
    let (_, state) ← run ``String.length inputType resultType #[.fvar input]
    unless !state.externs.isEmpty do throwError "incorrectly typed String.length admitted"
  logInfo "typed scalar length: direct, runtime wrapper, byte distinction and two rejection cases passed"
