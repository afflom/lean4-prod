import Lean
import Prod.Attribute

/-!
# LCNF → sexp IR lowering

Lowers pure-phase `Lean.Compiler.LCNF.Decl` values to the s-expression grammar
parsed by the Rust `prod-ir` crate (`prod-ir/src/parser.rs`). One sexp `def`
per LCNF declaration; `let`/`cases`/`jp`/`jmp`/`return`/`unreach` map to the
corresponding IR nodes. Design decisions:

- **Names**: definitions are stripped to their last component
  (`UorAtlas.stride` → `stride`); the full name is recorded by the caller in a
  `;; full:` comment (the parser skips `;;` comments). LCNF fvarIds are
  resolved to sanitized binder names (`_x.1` → `_x_1`, collisions get a
  `_<counter>` suffix) via a per-definition `FVarId → String` map.
- **Erased/type arguments** (`Arg.erased`, `Arg.type`): dropped from calls,
  counted in `LowerState.dropped` so the caller can emit an arity note.
  `let` bindings with `LetValue.erased` values (proofs) register their binder
  name but emit no binding and no opaque marker — proofs are erased by design.
- **Operator whitelist**: `Nat.add/sub/mul/div/mod/shiftLeft/pow` map to the
  IR binary ops (`pow` was added to prod-ir in M3 for `belt`). Any other
  constant becomes `(call <last-component> ...)`; if the callee is not itself
  `@[prod]`-tagged it is recorded as an *extern call* for the coverage report.
- **Constructors** (detected via the environment, e.g. `Prod.mk`) become
  `(ctor "Full.Name" ...)`; structure projections resolve their LCNF index to
  the declared field name here, where the environment is available, and
  become `(proj "Full.TypeName" "fieldName" x)`.
- **Decidable-if rewrite**: `if a < b then T else F` (and the `≤`/`=`
  analogues) compiles to `let c := Nat.decLt/Nat.decLe/Nat.decEq/
  instDecidableEqNat a b` followed by `cases c` over `Decidable.isFalse`/
  `isTrue` (with erased proof-hypothesis binders). Lowered directly to the IR
  `(if (lt|le|eq a b) T F)`; without this rewrite the scrutinee would surface
  as an extern `decLt` call and `Decidable.*` ctor patterns, neither of which
  has a Rust rendering. Only the immediately-bound shape is recognized;
  anything else still lowers as an extern call.
- **Closures** (`Code.fun`) lower to `(opaque "<name>-closure")` plus a
  coverage note — closures are phase-2 work. Impure-phase-only constructors
  never occur at the pure phase; wildcard arms keep the matches total.
-/

open Lean Compiler LCNF

namespace Prod

/-- Static lowering configuration. -/
structure LowerCtx where
  /-- `@[prod]`-tagged names: calls to these are internal, not extern. -/
  tagged : Array Name

/-- Per-definition lowering state: name resolution plus coverage facts. -/
structure LowerState where
  names   : Std.HashMap Name String := {}  -- keyed on `FVarId.name`
  used    : Std.HashSet String := {}
  /-- Compiler-generated Nat dictionaries which are semantically operators. -/
  knownOps : Std.HashMap String String := {}
  counter : Nat := 0
  opaques : Array String := #[]            -- opaque markers emitted
  externs : Array String := #[]            -- non-tagged, non-whitelisted calls
  dropped : Nat := 0                       -- erased/type args dropped

abbrev LowerM := ReaderT LowerCtx (StateRefT LowerState CoreM)

/-- Last dot-separated component of a name as a string. -/
def lastComponent : Name → String
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => "v"

private def isIdentChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 95

/-- Sanitize a Lean name into a Rust-ish identifier: keep [A-Za-z0-9_], map
    everything else to `_`, prefix `v` if empty or starting with a digit.
    `_x.1` → `_x_1`. -/
def sanitize (n : Name) : String :=
  let t := String.ofList (n.toString.toList.map fun c => if isIdentChar c then c else '_')
  if t.isEmpty || t.front.isDigit then "v" ++ t else t

/-- Resolve an fvarId to its emitted name, registering (sanitized, deduped)
    on first use. -/
def registerFVar (fvarId : FVarId) (binderName : Name) : LowerM String := do
  let st ← get
  if let some s := st.names[fvarId.name]? then return s
  let base := sanitize binderName
  let mut s := base
  let mut st := st
  while st.used.contains s do
    st := { st with counter := st.counter + 1 }
    s := s!"{base}_{st.counter}"
  set { st with used := st.used.insert s, names := st.names.insert fvarId.name s }
  return s

/-- Look up an already-registered fvarId (falls back to registering its raw
    name, which is still a valid identifier). -/
def lookupFVar (fvarId : FVarId) : LowerM String :=
  registerFVar fvarId fvarId.name

/-- Names used by Lean's Nat typeclass dictionaries in pure LCNF output. -/
def natDictOp : Name → Option String
  | `instAddNat => some "add"
  | `instSubNat => some "sub"
  | `instMulNat => some "mul"
  | `instDiv => some "div"
  | `instMod => some "mod"
  | `instNatPowNat => some "pow"
  | `Nat.add => some "add"
  | `Nat.sub => some "sub"
  | `Nat.mul => some "mul"
  | `Nat.div => some "div"
  | `Nat.mod => some "mod"
  | `Nat.pow => some "pow"
  | _ => none

/-- Lift a Nat dictionary through its overloaded-operation wrapper. -/
def natHDictOp : Name → Option String
  | `instHAdd => some "add"
  | `instHSub => some "sub"
  | `instHMul => some "mul"
  | `instHDiv => some "div"
  | `instHMod => some "mod"
  | `instHPow => some "pow"
  | `instPowNat => some "pow"
  | _ => none

/-- The operation represented by an already-lowered local value. -/
def knownOpOf (v : LetValue .pure) : LowerM (Option String) := do
  let st ← get
  match v with
  | .const n _ args =>
    match natDictOp n with
    | some op => if args.isEmpty then return some op else return none
    | none =>
      match natHDictOp n, args.toList with
      | some op, [.fvar f] =>
        let nm ← lookupFVar f
        match st.knownOps[nm]? with
        | some existing => return some existing
        | none => return some op
      | _, _ => return none
  | .proj _ _ f =>
    let nm ← lookupFVar f
    return st.knownOps[nm]?
  | .fvar f args =>
    if !args.isEmpty then return none
    let nm ← lookupFVar f
    return st.knownOps[nm]?
  | _ => return none

/-- Emit an `(opaque "...")` expression node and record it for coverage. -/
def opaqueNode (what : String) : LowerM String := do
  modify fun st => { st with opaques := st.opaques.push what }
  return s!"(opaque \"{what}\")"

/-- Emit an `(opaque "...")` type node and record it for coverage. -/
def opaqueType (n : Name) : LowerM String := do
  modify fun st => { st with opaques := st.opaques.push s!"type:{n}" }
  return s!"(opaque \"{n}\")"

/-- Lower call arguments, dropping `erased`/`type` args (counted). -/
def lowerArgs (args : Array (Arg .pure)) : LowerM (Array String) := do
  let mut out := #[]
  for a in args do
    match a with
    | .fvar id => out := out.push (← lookupFVar id)
    | _ => modify fun st => { st with dropped := st.dropped + 1 }
  return out

private def spaced (xs : Array String) : String :=
  if xs.isEmpty then "" else " " ++ String.intercalate " " xs.toList

/-- `.const` operator whitelist: Lean kernel Nat ops → IR binary ops. -/
def opWhitelist : Name → Option String
  | `Nat.add => some "add"
  | `Nat.sub => some "sub"
  | `Nat.mul => some "mul"
  | `Nat.div => some "div"
  | `Nat.mod => some "mod"
  | `Nat.shiftLeft => some "shl"
  | `Nat.pow => some "pow"
  | _ => none

private def isCtorName (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.ctorInfo _) => true
  | _ => false

def lowerLetValue (v : LetValue .pure) : LowerM String := do
  match v with
  | .lit (.nat n) => return toString n
  | .lit _ => opaqueNode "literal"
  | .erased => opaqueNode "erased"
  | .proj typeName idx struct => do
    let s ← lookupFVar struct
    let env ← getEnv
    -- Resolve the index to a field name here, where the environment is
    -- available. Emitting the index instead would force codegen to keep a
    -- parallel table, and a disagreement between the two swaps fields
    -- silently. LCNF projection indices are into the *declared* field list
    -- (including `Prop` fields), which is exactly what `getStructureFields`
    -- returns, so no filtering is applied before indexing. No name-keyed
    -- special cases here, not even for `UorAtlas.Instance`: the declared
    -- spelling passes through unmodified for every structure, so the
    -- `(type ...)` declaration and the `(proj ...)` reference can never
    -- disagree — both are generated from the same `getStructureFields` call.
    let fields := getStructureFields env typeName
    let field := match fields[idx]? with
      | some n => sanitize n
      | none => s!"field_{idx}"
    return s!"(proj \"{typeName}\" \"{field}\" {s})"
  | .const declName _ args => do
    let env ← getEnv
    let args' ← lowerArgs args
    if isCtorName env declName then
      return s!"(ctor \"{declName}\"{spaced args'})"
    match opWhitelist declName with
    | some op =>
      if args'.size == 2 then
        return s!"({op} {args'[0]!} {args'[1]!})"
      -- partial/unusual application of a whitelisted op: keep it callable
      modify fun st => { st with externs := st.externs.push s!"{declName} (unusual application)" }
      return s!"(call {lastComponent declName}{spaced args'})"
    | none =>
      if (← read).tagged.contains declName then
        -- internal call to another @[prod]-tagged definition
        return s!"(call {lastComponent declName}{spaced args'})"
      modify fun st => { st with externs := st.externs.push (toString declName) }
      return s!"(call {lastComponent declName}{spaced args'})"
  | .fvar f args => do
    let nm ← lookupFVar f
    let args' ← lowerArgs args
    match (← get).knownOps[nm]? with
    | some op =>
      if args'.size == 2 then return s!"({op} {args'[0]!} {args'[1]!})"
      return s!"(call {nm}{spaced args'})"
    | none => return s!"(call {nm}{spaced args'})"
  | _ => opaqueNode "letvalue"  -- impure-phase-only constructors

/-- The decider constants recognized by `decidableIf?`, mapped to their IR
    comparison operator. `instDecidableEqNat` appears in LCNF when the
    instance wrapper is not unfolded (unlike the arithmetic dictionaries). -/
def deciderOp : Name → Option String
  | ``Nat.decLt => some "lt"
  | ``Nat.decLe => some "le"
  | ``Nat.decEq => some "eq"
  | ``instDecidableEqNat => some "eq"
  | _ => none

/-- Recognize the LCNF shape of `if a < b then T else F` (and the `≤`/`=`
    analogues): `let c := <decider> a b` immediately followed by `cases c`
    with exactly the `Decidable.isFalse`/`isTrue` alternatives (either
    order). Returns the IR comparison operator, the compared fvars, and the
    (else, then) branch codes. The alternatives' proof-hypothesis binders are
    dropped by the caller — they are proof-irrelevant and never occur in
    computational code. -/
def decidableIf? (decl : LetDecl .pure) (k : Code .pure)
    : Option (String × FVarId × FVarId × Code .pure × Code .pure) := do
  let .const decider _ #[.fvar a, .fvar b] := decl.value | failure
  let op ← deciderOp decider
  let .cases c := k | failure
  guard (c.discr == decl.fvarId)
  if c.alts.size != 2 then failure
  let mut else? : Option (Code .pure) := none
  let mut then? : Option (Code .pure) := none
  for alt in c.alts do
    match alt with
    | .alt ``Decidable.isFalse _ code => else? := some code
    | .alt ``Decidable.isTrue _ code => then? := some code
    | _ => failure
  return (op, a, b, ← else?, ← then?)

partial def lowerCode : Code .pure → LowerM String
  | .let decl k => do
    let nm ← registerFVar decl.fvarId decl.binderName
    match decidableIf? decl k with
    | some (op, a, b, elseCode, thenCode) =>
      let a' ← lookupFVar a
      let b' ← lookupFVar b
      let else' ← lowerCode elseCode
      let then' ← lowerCode thenCode
      return s!"(if ({op} {a'} {b'}) {then'} {else'})"
    | none =>
    match decl.value with
    | .erased =>
      -- proof/irrelevant binding: register the name (it may occur in erased
      -- positions we drop) but emit no binding and no opaque marker
      lowerCode k
    | value =>
      if let some op ← knownOpOf value then
        -- Dictionary construction is pure and has no runtime meaning;
        -- retain only its semantic operator for later applications.
        modify fun st => { st with knownOps := st.knownOps.insert nm op }
        lowerCode k
      else
        let val ← lowerLetValue value
        let body ← lowerCode k
        return s!"(let {nm} {val} {body})"
  | .fun (.mk fid bn _ _ _) k => do
    let nm ← registerFVar fid bn
    let val ← opaqueNode s!"{nm}-closure"
    let body ← lowerCode k
    return s!"(let {nm} {val} {body})"
  | .jp (.mk fid bn ps _ v) k => do
    let nm ← registerFVar fid bn
    let pnames ← ps.mapM fun p => registerFVar p.fvarId p.binderName
    let jpBody ← lowerCode v
    let body ← lowerCode k
    -- The IR `jp` node is an expression with no continuation slot; the LCNF
    -- continuation is preserved as a `let` around the join-point declaration.
    return s!"(let {nm} (jp {nm} ({String.intercalate " " pnames.toList}) {jpBody}) {body})"
  | .jmp f args => do
    let nm ← lookupFVar f
    let args' ← lowerArgs args
    return s!"(jmp {nm}{spaced args'})"
  | .cases (.mk _tn _rt discr alts) => do
    let scrut ← lookupFVar discr
    let mut parts : Array String := #[]
    for a in alts do
      match a with
      | .alt ctorName ps c =>
        let pnames ← ps.mapM fun p => registerFVar p.fvarId p.binderName
        let body ← lowerCode c
        parts := parts.push s!"(alt \"{ctorName}\" ({String.intercalate " " pnames.toList}) {body})"
      | .default c =>
        parts := parts.push s!"(default {← lowerCode c})"
      | _ => parts := parts.push (← opaqueNode "ctorAlt")  -- impure phase only
    return s!"(cases {scrut}{spaced parts})"
  | .return f => lookupFVar f
  | .unreach _ => return "(unreachable)"
  | _ => opaqueNode "impure-code"  -- impure-phase-only constructors

/-- Lower an LCNF type expression to the IR type grammar. -/
partial def lowerType (e : Expr) : LowerM String := do
  match e with
  | .const ``Nat _ => return "Nat"
  | .const ``Bool _ => return "Bool"
  | .const ``Int _ => return "Int"
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.inductInfo _) => return s!"(named \"{n}\")"
    | _ => opaqueType n
  | .app (.app (.const ``Prod _) a) b =>
    return s!"(Tuple {← lowerType a} {← lowerType b})"
  | .app (.const ``List _) a =>
    return s!"(List {← lowerType a})"
  | .app (.const ``Option _) a =>
    return s!"(Option {← lowerType a})"
  | _ =>
    match e.getAppFn with
    | .const n _ =>
      match (← getEnv).find? n with
      | some (.inductInfo _) => return s!"(named \"{n}\")"
      | _ => opaqueType n
    | _ => opaqueNode "type-expr"

/-- Strip exactly `n` leading `∀`-binders: the LCNF `Signature.type` is the
    full telescope, and the result type lies under the declaration's params. -/
def stripForalls : Nat → Expr → Expr
  | 0, e => e
  | n + 1, .forallE _ _ b _ => stripForalls n b
  | _, e => e

/-- Lower one pure-phase LCNF declaration to a sexp `def`, returning the sexp
    and the collected lowering state (opaque/extern/dropped facts). -/
def lowerDecl (ctx : LowerCtx) (d : Decl .pure) : CoreM (String × LowerState) := do
  let go : LowerM String := do
    let mut ps : Array String := #[]
    for p in d.params do
      let nm ← registerFVar p.fvarId p.binderName
      let ty ← lowerType p.type
      ps := ps.push s!"({nm} {ty})"
    let ret ← lowerType (stripForalls d.params.size d.type)
    let body ← match d.value with
      | .code c => lowerCode c
      | .extern _ => opaqueNode "extern"
    return s!"(def {lastComponent d.name} ({String.intercalate " " ps.toList}) {ret}\n  {body})"
  (go.run ctx).run {}

/-- Indent every line of `s` by `n` spaces. -/
def indent (n : Nat) (s : String) : String :=
  let pad := String.ofList (List.replicate n ' ')
  String.intercalate "\n" ((s.splitOn "\n").map (pad ++ ·))

/-- Is this expression a `Prop`? Prop-valued structure fields are erased and
    never reach the IR. Runs in `MetaM` because `isProp` needs the local
    context machinery. -/
def isPropType (e : Expr) : LowerM Bool :=
  liftM (Lean.Meta.MetaM.run' (Lean.Meta.isProp e))

/-- Render one inductive as an IR `(type ...)` declaration, erasing `Prop`
    fields.

    A type outside the supported fragment is still declared, carrying the
    reason: codegen then rejects a reference to it by name ("needs
    monomorphization") instead of reporting a generic unknown type. Returns
    `none` only when the constant is not an inductive at all. -/
def lowerTypeDecl (typeName : Name) : LowerM (Option String) := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? typeName | return none
  let unsupported? : Option String :=
    if iv.numParams != 0 then some "type parameters"
    else if iv.numIndices != 0 then some "type indices"
    else if iv.all.length != 1 then some "mutual inductive block"
    else if iv.isRec then some "recursive"
    else none
  if let some reason := unsupported? then
    return some s!"(type \"{typeName}\" (unsupported \"{reason}\"))"
  let mut ctorSexps : Array String := #[]
  for ctorName in iv.ctors do
    let some (.ctorInfo cv) := env.find? ctorName | return none
    -- Walk the constructor telescope past the (zero) type params to reach the
    -- value fields, pairing each with its declared name.
    let fieldNames := getStructureFields env typeName
    let mut fields : Array String := #[]
    let mut ty := cv.type
    let mut i := 0
    while i < cv.numFields do
      match ty with
      | .forallE _ fieldTy rest _ =>
        if !(← isPropType fieldTy) then
          let nm := match fieldNames[i]? with
            | some n => sanitize n
            | none => s!"field_{i}"
          fields := fields.push s!"({nm} {← lowerType fieldTy})"
        ty := rest
        i := i + 1
      | _ => i := cv.numFields
    ctorSexps := ctorSexps.push s!"(ctor \"{ctorName}\"{spaced fields})"
  return some s!"(type \"{typeName}\"{spaced ctorSexps})"

/-- Every named type mentioned in a declaration's parameter or return types.
    Only the head constant matters — parameterised types are out of scope. -/
def declTypeNames (d : Decl .pure) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for p in d.params do
    if let .const n _ := p.type.getAppFn then out := out.push n
  if let .const n _ := (stripForalls d.params.size d.type).getAppFn then
    out := out.push n
  return out

end Prod
