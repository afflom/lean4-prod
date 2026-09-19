import Prod.Lower
import IndexFixture.Main

open Lean Compiler LCNF

run_meta do
  CompilerM.run do
    let name := `IndexFixture.Bytes.LexLeanRuntime.slice._at_.IndexFixture.Bytes.sliceBytes.spec_0
    let some decl ← getMonoDecl? name | throwError "missing real imported slice specialization"
    unless Prod.isExactByteSlice decl do throwError "real byte slice rejected"
    unless Prod.isExactByteSlice { decl with name := `DifferentName } do
      throwError "recognition depends on specialization spelling"
    let #[input, start, count] := decl.params | throwError "unexpected params"
    let .code (.let upper (.let size (.let guard (.cases cases)))) := decl.value
      | throwError "unexpected body"
    let #[.alt falseName falseParams (.let missing (.return no)),
          .alt trueName trueParams (.let slice (.let present (.return yes)))] := cases.alts
      | throwError "unexpected branches"
    let body := fun upper size guard cases =>
      DeclValue.code (.let upper (.let size (.let guard (.cases cases))))
    let arms := fun missing slice present no yes =>
      #[Alt.alt falseName falseParams (.let missing (.return no)),
        Alt.alt trueName trueParams (.let slice (.let present (.return yes)))]
    let mutants : Array (String × Decl .pure) := #[
      ("input type", { decl with params := #[{ input with type := mkConst ``String }, start, count] }),
      ("start type", { decl with params := #[input, { start with type := mkConst ``UInt64 }, count] }),
      ("count type", { decl with params := #[input, start, { count with type := mkConst ``UInt64 }] }),
      ("arity", { decl with params := #[input, start] }),
      ("return type", { decl with type := mkConst ``Nat }),
      ("subtract bound", { decl with value := body { upper with value := .const ``Nat.sub [] #[.fvar start.fvarId, .fvar count.fvarId] } size guard cases }),
      ("doubled start", { decl with value := body { upper with value := .const ``Nat.add [] #[.fvar start.fvarId, .fvar start.fvarId] } size guard cases }),
      ("wrong measured input", { decl with value := body upper { size with value := .const ``ByteArray.size [] #[.fvar start.fvarId] } guard cases }),
      ("strict bound", { decl with value := body upper size { guard with value := .const ``Nat.decLt [] #[.fvar upper.fvarId, .fvar size.fvarId] } cases }),
      ("reversed bound", { decl with value := body upper size { guard with value := .const ``Nat.decLe [] #[.fvar size.fvarId, .fvar upper.fvarId] } cases }),
      ("wrong discriminant", { decl with value := body upper size guard (.mk cases.typeName cases.resultType start.fvarId cases.alts) }),
      ("wrong case type", { decl with value := body upper size guard (.mk cases.typeName (mkConst ``Nat) cases.discr cases.alts) }),
      ("reversed branches", { decl with value := body upper size guard (cases.updateAlts cases.alts.reverse) }),
      ("default branch", { decl with value := body upper size guard (cases.updateAlts #[.default (.return no)]) }),
      ("wrong source", { decl with value := body upper size guard (cases.updateAlts (arms missing { slice with value := .const ``ByteArray.extract [] #[.fvar start.fvarId, .fvar start.fvarId, .fvar upper.fvarId] } present no yes)) }),
      ("wrong start", { decl with value := body upper size guard (cases.updateAlts (arms missing { slice with value := .const ``ByteArray.extract [] #[.fvar input.fvarId, .fvar count.fvarId, .fvar upper.fvarId] } present no yes)) }),
      ("wrong upper", { decl with value := body upper size guard (cases.updateAlts (arms missing { slice with value := .const ``ByteArray.extract [] #[.fvar input.fvarId, .fvar start.fvarId, .fvar count.fvarId] } present no yes)) }),
      ("wrong some payload", { decl with value := body upper size guard (cases.updateAlts (arms missing slice { present with value := .const ``Option.some [] #[.erased, .fvar input.fvarId] } no yes)) }),
      ("wrong none return", { decl with value := body upper size guard (cases.updateAlts (arms missing slice present yes yes)) }),
      ("wrong some return", { decl with value := body upper size guard (cases.updateAlts (arms missing slice present no no)) }),
      ("extra work", { decl with value := .code (.let upper (.let size (.let guard (.let size (.cases cases))))) })
    ]
    for (label, mutant) in mutants do
      if Prod.isExactByteSlice mutant then throwError "altered slice accepted: {label}"
    logInfo m!"byte-slice recognition: real body, renamed body and {mutants.size} rejection cases passed"
