import Prod.Lower
import IndexFixture.Main

open Lean Compiler LCNF

run_meta do
  CompilerM.run do
    let name := `IndexFixture.Bytes.LexLeanRuntime.index._at_.IndexFixture.Bytes.byteAt.spec_0
    let some decl ← getMonoDecl? name | throwError "missing real imported index specialization"
    unless Prod.isExactByteIndex decl do throwError "real byte index rejected"
    unless Prod.isExactByteIndex { decl with name := `DifferentName } do
      throwError "recognition depends on specialization spelling"
    let #[input, offset] := decl.params | throwError "unexpected params"
    let .code (.let data (.let size (.let guard (.cases cases)))) := decl.value
      | throwError "unexpected body"
    let #[.alt falseName falseParams (.let missing (.return no)),
          .alt trueName trueParams (.let element (.let present (.return yes)))] := cases.alts
      | throwError "unexpected branches"
    let body := fun data size guard cases =>
      DeclValue.code (.let data (.let size (.let guard (.cases cases))))
    let arms := fun missing element present no yes =>
      #[Alt.alt falseName falseParams (.let missing (.return no)),
        Alt.alt trueName trueParams (.let element (.let present (.return yes)))]
    let mutants : Array (String × Decl .pure) := #[
      ("input type", { decl with params := #[{ input with type := mkConst ``Nat }, offset] }),
      ("offset type", { decl with params := #[input, { offset with type := mkConst ``UInt64 }] }),
      ("arity", { decl with params := #[input] }),
      ("return type", { decl with type := .forallE `input input.type (.forallE `offset offset.type (mkConst ``Nat) .default) .default }),
      ("data source", { decl with value := body { data with value := .const ``ByteArray.data [] #[.fvar offset.fvarId] } size guard cases }),
      ("array length", { decl with value := body data { size with value := .const ``Array.size [] #[.erased, .fvar input.fvarId] } guard cases }),
      ("inclusive bound", { decl with value := body data size { guard with value := .const ``Nat.decLe [] #[.fvar offset.fvarId, .fvar size.fvarId] } cases }),
      ("reversed bound", { decl with value := body data size { guard with value := .const ``Nat.decLt [] #[.fvar size.fvarId, .fvar offset.fvarId] } cases }),
      ("wrong discriminant", { decl with value := body data size guard (.mk cases.typeName cases.resultType offset.fvarId cases.alts) }),
      ("wrong case type", { decl with value := body data size guard (.mk cases.typeName (mkConst ``Nat) cases.discr cases.alts) }),
      ("reversed branches", { decl with value := body data size guard (cases.updateAlts cases.alts.reverse) }),
      ("default branch", { decl with value := body data size guard (cases.updateAlts #[.default (.return no)]) }),
      ("wrong element index", { decl with value := body data size guard (cases.updateAlts (arms missing { element with value := .const ``Array.getInternal [] #[.erased, .fvar data.fvarId, .fvar size.fvarId, .erased] } present no yes)) }),
      ("wrong element array", { decl with value := body data size guard (cases.updateAlts (arms missing { element with value := .const ``Array.getInternal [] #[.erased, .fvar input.fvarId, .fvar offset.fvarId, .erased] } present no yes)) }),
      ("wrong some payload", { decl with value := body data size guard (cases.updateAlts (arms missing element { present with value := .const ``Option.some [] #[.erased, .fvar offset.fvarId] } no yes)) }),
      ("wrong none return", { decl with value := body data size guard (cases.updateAlts (arms missing element present yes yes)) }),
      ("wrong some return", { decl with value := body data size guard (cases.updateAlts (arms missing element present no no)) }),
      ("extra work", { decl with value := .code (.let data (.let size (.let guard (.let size (.cases cases))))) })
    ]
    for (label, mutant) in mutants do
      if Prod.isExactByteIndex mutant then throwError "altered index accepted: {label}"
    logInfo m!"byte-index recognition: real body, renamed body and {mutants.size} rejection cases passed"
