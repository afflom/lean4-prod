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
- **Operator whitelist**: `Nat.add/sub/mul/div/mod/shiftLeft/shiftRight/pow`
  map to the IR binary ops, each tagged with its numeric kind — `(add Nat a
  b)`, not bare `(add a b)` — since the IR grammar carries the kind
  explicitly rather than inferring it (`pow` was added to prod-ir in M3 for
  `belt`; `shiftRight` maps to `shr`, a total/infallible IR node distinct
  from `shl` — `a >>> b = 0` for `b ≥ 64` since `Nat` is unbounded, so there
  is no overflow case to report). `Nat.shiftRight` reaches lowering both from
  `>>>` written directly and from LCNF's `n / 2` peephole (division by a
  power-of-two literal); either way it is just another whitelisted name by
  the time lowering sees it. Any other constant becomes an *unresolved
  call*: if the callee is `@[prod]`-tagged it is `(call <last-component>
  ...)`, otherwise it is recorded for the coverage report and emitted as
  `(extern "Full.Name" ...)` — a node codegen refuses, rather than a `call`
  to a function nobody generated.
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
- **Decidable-as-Bool rewrite**: `a < b : Bool` (no surrounding `if`) compiles
  to the same decider call followed by `Decidable.decide c` rather than
  `cases`. Lowered directly to the IR comparison expression `(lt|le|eq a b)`,
  which is valid outside an `if` too. Same immediately-bound-shape caveat as
  above; anything else still lowers as an extern call to `decide`.
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
  /-- Compiler-generated Nat dictionaries which are semantically operators,
      as (IR op, IR kind). -/
  knownOps : Std.HashMap String (String × String) := {}
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

/-- Names used by Lean's Nat typeclass dictionaries in pure LCNF output.
    Every one of these is a `Nat` dictionary, so the kind is always `"Nat"`. -/
def natDictOp : Name → Option (String × String)
  | `instAddNat => some ("add", "Nat")
  | `instSubNat => some ("sub", "Nat")
  | `instMulNat => some ("mul", "Nat")
  | `instDiv => some ("div", "Nat")
  | `instMod => some ("mod", "Nat")
  | `instNatPowNat => some ("pow", "Nat")
  | `Nat.add => some ("add", "Nat")
  | `Nat.sub => some ("sub", "Nat")
  | `Nat.mul => some ("mul", "Nat")
  | `Nat.div => some ("div", "Nat")
  | `Nat.mod => some ("mod", "Nat")
  | `Nat.pow => some ("pow", "Nat")
  | _ => none

/-- Lift a Nat dictionary through its overloaded-operation wrapper. Every one
    of these is a `Nat` dictionary too, so the kind is always `"Nat"`. -/
def natHDictOp : Name → Option (String × String)
  | `instHAdd => some ("add", "Nat")
  | `instHSub => some ("sub", "Nat")
  | `instHMul => some ("mul", "Nat")
  | `instHDiv => some ("div", "Nat")
  | `instHMod => some ("mod", "Nat")
  | `instHPow => some ("pow", "Nat")
  | `instPowNat => some ("pow", "Nat")
  | _ => none

/-- The operation (IR op, IR kind) represented by an already-lowered local
    value. -/
def knownOpOf (v : LetValue .pure) : LowerM (Option (String × String)) := do
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

/-- `.const` operator whitelist as an (LCNF constant name, IR operator, IR
    numeric kind) association list. Single source of truth for both
    `opWhitelist` (what the lowerer accepts) and `subsetJson` (the published
    contract, `Prod.Emit`) — extracted so the two cannot drift apart. `pow`
    was added to prod-ir in M3 for `belt`; `shiftRight` maps to `shr`, a
    total/infallible IR node distinct from `shl` — `a >>> b = 0` for `b ≥ 64`
    since `Nat` is unbounded, so there is no overflow case to report.

    Sized-integer rows are generated rather than typed out: every `UIntN`
    shares the same operation names (`sizedOpRows` below), so listing them by
    hand would be four near-identical blocks that can drift. -/
def natOpRows : List (Name × String × String) :=
  [ (`Nat.add, "add", "Nat"), (`Nat.sub, "sub", "Nat"), (`Nat.mul, "mul", "Nat"),
    (`Nat.div, "div", "Nat"), (`Nat.mod, "mod", "Nat"),
    (`Nat.shiftLeft, "shl", "Nat"), (`Nat.shiftRight, "shr", "Nat"),
    (`Nat.pow, "pow", "Nat") ]

/-- Operation suffixes shared by every sized integer type: `UInt8.add`,
    `UInt16.add`, … all exist under the same suffix, so this is the shared
    half of `sizedOpRows`'s generation rather than typed out four times. -/
def sizedOpSuffixes : List (Name × String) :=
  [ (`add, "add"), (`sub, "sub"), (`mul, "mul"), (`div, "div"), (`mod, "mod"),
    (`shiftLeft, "shl"), (`shiftRight, "shr") ]

/-- Lean sized-integer types and their IR kind tags. Also used by `lowerType`
    (mapping `UInt8`…`UInt64` to `U8`…`U64`) and `deciderNames` below, so a
    fifth sized kind would only need adding here. -/
def sizedKinds : List (Name × String) :=
  [ (`UInt8, "U8"), (`UInt16, "U16"), (`UInt32, "U32"), (`UInt64, "U64") ]

/-- Types the IR handles natively, paired with their contract annotation.
    Single source of truth for three consumers that previously each carried
    their own copy: `collectTypeDecls`' exclusion test (a builtin must not be
    collected as a user inductive — `UInt8` is a structure over
    `toBitVec : BitVec 8`, and trying to describe that field aborts the
    export), and `subsetJson`'s published Types list.

    `lowerType` deliberately does NOT consume this: it maps each builtin to a
    *different* IR tag, which is a mapping rather than a membership test, and
    collapsing the two would make the list carry two unrelated jobs. -/
def builtinTypes : List (Name × String) :=
  [ (`Nat, "Nat"),
    (`Bool, "Bool"),
    (`Int, "Int (renders as i64; checked add/sub/mul/neg/pow, Euclidean checked div/mod (Int.ediv/Int.emod); shifts are not whitelisted for Int; Nat -> Int is supported, via the constructors Int.ofNat (n renders as (n as i64)) and Int.negSucc (n renders as -(n as i64) - 1) -- these are constructor applications, not conversion calls, so they never appear in the Conversions list below)"),
    (`Prod, "Prod (renders as a Rust tuple)"),
    (`List, "List (parameter: &[a]; return: a caller-owned output buffer)"),
    (`Option, "Option") ]
  ++ sizedKinds.map (fun p =>
       (p.1, s!"{p.1} (renders as {p.2.toLower}; wrapping add/sub/mul; total div/mod (zero divisor gives 0/the dividend, as for Nat); shiftLeft/shiftRight mask the shift amount mod the width rather than truncating to 0 (unlike Nat's shifts) -- none of this can fail; pow is not whitelisted for sized kinds)"))

/-- Is this constant a type the IR handles natively? -/
def isBuiltinType (n : Name) : Bool := builtinTypes.any (fun p => p.1 == n)

/-- The cross product of `sizedKinds` and `sizedOpSuffixes`: every
    sized-integer operator row, e.g. `UInt8.add` ↦ `("add", "U8")`. This is
    what makes the "generated rather than typed out" claim above true. -/
def sizedOpRows : List (Name × String × String) :=
  sizedKinds.flatMap fun (ty, kind) =>
    sizedOpSuffixes.map fun (suffix, ir) => (ty ++ suffix, ir, kind)

/-- `Int` operator whitelist. `Int.ediv`/`Int.emod` are the actual `Div
    Int`/`Mod Int` instance implementations (Euclidean, not truncating —
    `Init/Data/Int/DivMod/Basic.lean`, "for compatibility with SMT-LIB"), so
    they are the names that reach LCNF for `a / b`/`a % b` on `Int`, not
    `Int.div`/`Int.mod` (which are the truncating operations and are never
    invoked by the `/`/`%` notation). Shifts are deliberately absent: `Int`
    shifts are not lowered (see `prod-codegen`'s `Expr::Shl`/`Expr::Shr`). -/
def intOpRows : List (Name × String × String) :=
  [ (`Int.add, "add", "Int"), (`Int.sub, "sub", "Int"), (`Int.mul, "mul", "Int"),
    (`Int.ediv, "div", "Int"), (`Int.emod, "mod", "Int"),
    (`Int.neg, "neg", "Int"), (`Int.pow, "pow", "Int") ]

def numOpNames : List (Name × String × String) := natOpRows ++ intOpRows ++ sizedOpRows

/-- `.const` operator whitelist: Lean constant → (IR operator, IR kind). -/
def opWhitelist (n : Name) : Option (String × String) :=
  (numOpNames.find? (fun p => p.1 == n)).map (fun p => (p.2.1, p.2.2))

/-- (Lean constant, from-kind, to-kind). Unary; emitted as `(convert F T x)`.
    A conversion carries two kinds, not one, so this is a separate table from
    `numOpNames` rather than another row shape squeezed into it.

    `Int.ofNat` is deliberately **absent** here even though it converts
    `Nat → Int`: `Int` is `inductive Int | ofNat : Nat → Int | negSucc : Nat →
    Int`, so `Int.ofNat` is a constructor, and `lowerLetValue` below checks
    `isCtorName` *before* consulting this table. Every occurrence — an
    explicit call, or a `Nat`-typed literal elaborating into an `Int`
    position — is intercepted there and lowered as `(ctor "Int.ofNat" ...)`,
    never reaching this table; a row for it here would be dead. Confirmed by
    export: `Int.ofNat a` lowers to `(ctor "Int.ofNat" a)` even when this
    table is consulted first for every other `.const`. `prod-codegen`'s
    `Expr::Ctor` arm already renders that ctor as `((n) as i64)` — identical
    to what `Expr::Convert`'s `(Nat, Int)` arm renders — so the two would be
    indistinguishable in output even if both existed; only one does.

    `Int.toNat` and the `UIntN.toNat` half below are genuine `def`s, so the
    constructed spelling (`ty ++ \`toNat`) is exactly the constant that
    reaches lowering. The `Nat → UIntN` half is NOT `Nat.toUIntN`, despite
    that spelling existing (`Nat.toUInt8`, `Init/Data/UInt/BasicAux.lean`):
    every one of `Nat.toUInt8`/16/32/64 is declared as
    `abbrev Nat.toUIntN := UIntN.ofNat`, and Lean's compiler unfolds the
    abbrev before the constant reaches LCNF — confirmed by export: a
    conformance def using `a.toUInt8`/`a.toUInt16`/`a.toUInt32`/`a.toUInt64`
    lowers to `extern "UInt8.ofNat"`/`"UInt16.ofNat"`/`"UInt32.ofNat"`/
    `"UInt64.ofNat"`, never `extern "Nat.toUIntN"`. So the row is `ty ++
    \`ofNat`, not the constructed `Nat.toUIntN` name the source-level spelling
    would suggest. -/
def conversionNames : List (Name × String × String) :=
  [ (`Int.toNat, "Int", "Nat") ]
  ++ sizedKinds.flatMap fun (ty, kind) =>
       [ (ty ++ `toNat, kind, "Nat"), (ty ++ `ofNat, "Nat", kind) ]

/-- `.const` conversion whitelist: Lean constant → (from-kind, to-kind). -/
def conversionWhitelist (n : Name) : Option (String × String) :=
  (conversionNames.find? (fun p => p.1 == n)).map (fun p => (p.2.1, p.2.2))

private def isCtorName (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.ctorInfo _) => true
  | _ => false

def lowerLetValue (v : LetValue .pure) : LowerM String := do
  match v with
  | .lit (.nat n) => return toString n
  -- Sized-integer literals are a *distinct* `LitValue` constructor from
  -- `.nat` (`Lean/Compiler/LCNF/Basic.lean`: `LitValue` has `nat`, `str`,
  -- `uint8`, `uint16`, `uint32`, `uint64`, `usize`), not a `Nat` literal
  -- wrapped in a `UIntN` — discovered because `c_u8_guard_lt`'s `then 1 else
  -- 0` branches (the first sized literals in the conformance suite) fell
  -- through to the opaque catch-all below and would have made codegen
  -- reject the whole definition (`Expr::Opaque` → `Error::OpaqueExpr`). The
  -- IR grammar's numeric literals are untagged decimal tokens either way
  -- (`prod-ir`'s `parse_u64`/`Expr::Nat`), so the same rendering as `.nat`
  -- is exact: the sized-integer receiver already pins the Rust type via the
  -- surrounding `(add U8 ...)`/return-type context, same as `Nat`'s.
  | .lit (.uint8 n) => return toString n
  | .lit (.uint16 n) => return toString n
  | .lit (.uint32 n) => return toString n
  | .lit (.uint64 n) => return toString n
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
    | some (op, kind) =>
      -- `Int.neg` is unary, unlike every other whitelisted operator.
      if op == "neg" && args'.size == 1 then
        return s!"(neg {kind} {args'[0]!})"
      if args'.size == 2 then
        return s!"({op} {kind} {args'[0]!} {args'[1]!})"
      -- partial/unusual application of a whitelisted op: not a 2-arg operator
      -- use, and not necessarily `@[prod]`-tagged either, so it is the same
      -- kind of unresolved callee as the `none` case below.
      modify fun st => { st with externs := st.externs.push s!"{declName} (unusual application)" }
      return s!"(extern \"{declName}\"{spaced args'})"
    | none =>
    match conversionWhitelist declName with
    | some (from_, to) =>
      -- Conversions are unary, unlike the (mostly) binary `numOpNames`.
      if args'.size == 1 then
        return s!"(convert {from_} {to} {args'[0]!})"
      modify fun st => { st with externs := st.externs.push s!"{declName} (unusual application)" }
      return s!"(extern \"{declName}\"{spaced args'})"
    | none =>
      if (← read).tagged.contains declName then
        -- internal call to another @[prod]-tagged definition
        return s!"(call {lastComponent declName}{spaced args'})"
      modify fun st => { st with externs := st.externs.push (toString declName) }
      -- Emit a distinct node rather than a `call`: codegen must refuse this,
      -- not render a Rust call to a function nobody generated.
      return s!"(extern \"{declName}\"{spaced args'})"
  | .fvar f args => do
    let nm ← lookupFVar f
    let args' ← lowerArgs args
    match (← get).knownOps[nm]? with
    | some (op, kind) =>
      if args'.size == 2 then return s!"({op} {kind} {args'[0]!} {args'[1]!})"
      return s!"(call {nm}{spaced args'})"
    | none => return s!"(call {nm}{spaced args'})"
  | _ => opaqueNode "letvalue"  -- impure-phase-only constructors

/-- The decider constants recognized by `decidableIf?`/`decideOf?`, paired
    with their IR comparison operator. Single source of truth for both
    `deciderOp` and `subsetJson` (`Prod.Emit`), so the published contract
    cannot list a decider the lowerer does not actually accept, or omit one
    it does. `instDecidableEqNat`/`Int.instDecidableEq` appear in LCNF when
    the `DecidableEq` instance wrapper is not unfolded (unlike the arithmetic
    dictionaries) — `Int` has the structurally identical anonymous instance
    (`Init/Data/Int/Basic.lean`: `instance : DecidableEq Int := Int.decEq`,
    declared inside `namespace Int`) as `Nat`, so it needs the same second
    row. The auto-generated name is `Int.instDecidableEq`, not
    `instDecidableEqInt`: Lean drops the redundant `Int` argument suffix
    because the instance already sits inside `namespace Int` (confirmed by
    enumerating the environment's constants — `instDecidableEqInt` does not
    exist and fails the build with `unknown constant`).

    The sized-integer types are the opposite case from `Int`: their
    `instance : DecidableEq UIntN := UIntN.decEq` declarations sit at the top
    level of `Init/Prelude.lean`, with no enclosing `namespace UIntN` block
    (confirmed by grepping for `^namespace` in that file — none precedes any
    of the `UInt8`…`UInt64` declarations). So, like `Nat`, the auto-generated
    name keeps the full `UIntN` suffix: `instDecidableEqUInt8`, not
    `UInt8.instDecidableEq`. Confirmed by `#check`ing all sixteen sized names
    directly against the toolchain (`UInt8.decLt`/`decLe`/`decEq` … `UInt64.…`
    plus `instDecidableEqUInt8` … `instDecidableEqUInt64`) — every one
    resolves, unlike `instDecidableEqInt`. -/
def deciderNames : List (Name × String) :=
  [ (``Nat.decLt, "lt"), (``Nat.decLe, "le"), (``Nat.decEq, "eq"),
    (``instDecidableEqNat, "eq"),
    (``Int.decLt, "lt"), (``Int.decLe, "le"), (``Int.decEq, "eq"),
    (``Int.instDecidableEq, "eq"),
    (``UInt8.decLt, "lt"), (``UInt8.decLe, "le"), (``UInt8.decEq, "eq"),
    (``instDecidableEqUInt8, "eq"),
    (``UInt16.decLt, "lt"), (``UInt16.decLe, "le"), (``UInt16.decEq, "eq"),
    (``instDecidableEqUInt16, "eq"),
    (``UInt32.decLt, "lt"), (``UInt32.decLe, "le"), (``UInt32.decEq, "eq"),
    (``instDecidableEqUInt32, "eq"),
    (``UInt64.decLt, "lt"), (``UInt64.decLe, "le"), (``UInt64.decEq, "eq"),
    (``instDecidableEqUInt64, "eq") ]

/-- The decider constants recognized by `decidableIf?`, mapped to their IR
    comparison operator. -/
def deciderOp (n : Name) : Option String :=
  (deciderNames.find? (fun p => p.1 == n)).map (·.2)

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

/-- Recognize the LCNF shape of a decidable comparison used as a plain `Bool`
    value (as opposed to the `if`-consuming shape `decidableIf?` handles):
    `let c := <decider> a b` immediately followed by `let x := Decidable.decide
    c`. Binds `x` directly to the IR comparison expression, skipping the
    intermediate decider binding — `Eq`/`Lt`/`Le`/`Gt` are already valid IR
    expressions outside an `if`, not just inside one. Returns the operator,
    the compared fvars, the `decide` binding, and its continuation. Only the
    immediately-bound shape is recognized; anything else still lowers as an
    extern call to `decide`. -/
def decideOf? (decl : LetDecl .pure) (k : Code .pure)
    : Option (String × FVarId × FVarId × LetDecl .pure × Code .pure) := do
  let .const decider _ #[.fvar a, .fvar b] := decl.value | failure
  let op ← deciderOp decider
  let .let decl2 k2 := k | failure
  let .const ``Decidable.decide _ #[.erased, .fvar f] := decl2.value | failure
  guard (f == decl.fvarId)
  return (op, a, b, decl2, k2)

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
    match decideOf? decl k with
    | some (op, a, b, decl2, k2) =>
      let nm2 ← registerFVar decl2.fvarId decl2.binderName
      let a' ← lookupFVar a
      let b' ← lookupFVar b
      let body ← lowerCode k2
      return s!"(let {nm2} ({op} {a'} {b'}) {body})"
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
    -- `sizedKinds` doubles as the `UInt8`…`UInt64` → `U8`…`U64` type map, so
    -- a fifth sized kind would only need adding there.
    match sizedKinds.find? (fun p => p.1 == n) with
    | some (_, tag) => return tag
    | none =>
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

/-- An operand inside a proposition: either a reference to one of the
    structure's own fields, or a numeric literal. Anything else makes the
    whole proposition unlowerable.

    Defined before `lowerProp`, which calls it: Lean has no forward references
    outside a `mutual` block, and this function never calls back, so ordering
    is enough. -/
partial def lowerPropOperand (e : Expr) (fields : Array String) (depth : Nat)
    : LowerM (Option String) := do
  match e with
  | .bvar i =>
    -- Decline an index at or beyond the binder depth BEFORE computing `idx`.
    -- `Nat` subtraction truncates, so `depth - 1 - i` silently yields `0` for
    -- every such index and resolves to `fields[0]` instead of declining —
    -- a comparison that compiles, returns a `bool`, and is wrong.
    --
    -- Unreachable today: `lowerTypeDecl` rejects `numParams != 0` before the
    -- telescope walk, so every `bvar` in a field type is an earlier field.
    -- It stops being unreachable the moment a proposition may mention a type
    -- parameter, which is exactly Phase B2: `Fin n`'s `isLt : val < n`
    -- references `n`, a binder outside the field telescope. For `Fin`,
    -- `fields[0]` is `val`, so the truncated read would lower `val < n` to
    -- `(lt val val)` — always false, and green everywhere.
    if i ≥ depth then return none
    let idx := depth - 1 - i
    match fields[idx]? with
    | some name => return some name
    | none => return none
  | .lit (.natVal n) => return some (toString n)
  | _ =>
    -- `OfNat.ofNat`-wrapped literals: take the raw literal argument if there
    -- is one, otherwise decline. This is the shape numeric literals actually
    -- take in a constructor telescope (`OfNat.ofNat Nat n (instOfNatNat n)`);
    -- the raw `.lit` arm above is a harmless belt-and-braces case.
    match e.getAppFn with
    | .const ``OfNat.ofNat _ =>
      let raw? : Option Expr := e.getAppArgs[1]?
      match raw? with
      | some (.lit (.natVal n)) => return some (toString n)
      | _ => return none
    | _ => return none

/-- The types a lowered comparison may range over: the numeric kinds the IR
    compares natively. Built from `sizedKinds` so a fifth sized kind is picked
    up automatically, the same way `lowerType` and `deciderNames` consume it.

    This exists because `lowerProp`'s docstring scopes the fragment to
    "comparisons on supported numeric kinds" and nothing used to enforce it: a
    polymorphic `LE.le`/`Eq` over any type at all lowered to an IR comparison
    as long as both operands happened to be field references. Equality between
    two `Bool` fields is the reachable case — it produced `(eq a b)`, a scalar
    comparison node, for a type the fragment never claimed. A documented
    restriction the code does not apply is the defect shape this project keeps
    shipping, so the claim is now checked rather than reworded. -/
def propCmpKinds : List Name := [``Nat, ``Int] ++ sizedKinds.map (·.1)

/-- Lower a `Prop` to a boolean IR expression over a structure's own fields,
    or `none` if it is outside the lowerable fragment.

    `fields` holds the field names in binder order — **including** `Prop`
    fields, since de Bruijn indices count every binder. A proposition refers
    to an earlier field by de Bruijn index, so `bvar i` at binder depth `d`
    (the `Prop` field's own 0-indexed telescope position) names
    `fields[d - 1 - i]`. See AGENTS.md for the verified shape.

    Lowerable: conjunction, disjunction, negation, and comparisons on
    supported numeric kinds. Everything else — quantifiers, arbitrary
    predicates, anything mentioning a name that is not one of this
    structure's fields — returns `none`, and the structure then keeps public
    fields and no checked constructor. That is a strictly weaker outcome, not
    a wrong one. -/
partial def lowerProp (e : Expr) (fields : Array String) (depth : Nat)
    : LowerM (Option String) := do
  let arg? (i : Nat) : Option Expr := e.getAppArgs[i]?
  match e.getAppFn with
  | .const ``And _ => do
    let some a := arg? 0 | return none
    let some b := arg? 1 | return none
    let some a' ← lowerProp a fields depth | return none
    let some b' ← lowerProp b fields depth | return none
    return some s!"(and {a'} {b'})"
  | .const ``Or _ => do
    let some a := arg? 0 | return none
    let some b := arg? 1 | return none
    let some a' ← lowerProp a fields depth | return none
    let some b' ← lowerProp b fields depth | return none
    return some s!"(or {a'} {b'})"
  | .const ``Not _ => do
    let some a := arg? 0 | return none
    let some a' ← lowerProp a fields depth | return none
    return some s!"(not {a'})"
  | .const cmp _ =>
    -- Comparisons. `a ≥ b` is `b ≤ a` and `a > b` is `b < a`, so the two
    -- reversed forms map onto the IR's `le`/`lt` with their operands swapped
    -- rather than needing their own nodes.
    let swap? : Option (String × Bool) :=
      if cmp == ``LE.le || cmp == ``Nat.le then some ("le", false)
      else if cmp == ``GE.ge then some ("le", true)
      else if cmp == ``LT.lt || cmp == ``Nat.lt then some ("lt", false)
      else if cmp == ``GT.gt then some ("lt", true)
      else if cmp == ``Eq then some ("eq", false)
      else none
    let some (op, reversed) := swap? | return none
    -- Comparisons carry instance/type arguments ahead of the operands; take
    -- the LAST two arguments, which are the operands under every spelling.
    let args := e.getAppArgs
    if args.size < 2 then return none
    -- Enforce the "supported numeric kinds" scope the docstring claims. A
    -- polymorphic comparison (`LE.le α inst a b`, `Eq α a b`) carries its type
    -- as the first argument and must name a kind the IR compares natively; the
    -- monomorphic spellings (`Nat.le a b`) carry only the two operands, and
    -- are already pinned to `Nat` by their own name.
    let kindOk : Bool :=
      if args.size ≥ 3 then
        match args[0]! with
        | .const ty _ => propCmpKinds.contains ty
        | _ => false   -- e.g. `Eq (Nat × Nat) p q`: an applied type, not a kind
      else true
    if !kindOk then return none
    let some a ← lowerPropOperand args[args.size - 2]! fields depth | return none
    let some b ← lowerPropOperand args[args.size - 1]! fields depth | return none
    return some (if reversed then s!"({op} {b} {a})" else s!"({op} {a} {b})")
  | _ => return none

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
  -- Propositions collected from `Prop` fields, and whether every one lowered.
  -- A single unlowerable `Prop` field suppresses the whole `(invariant ...)`
  -- clause: emitting a partial invariant would claim the generated
  -- constructor checks everything Lean proved when it does not.
  let mut invProps : Array String := #[]
  let mut invOk := true
  for ctorName in iv.ctors do
    let some (.ctorInfo cv) := env.find? ctorName | return none
    -- Walk the constructor telescope past the (zero) type params to reach the
    -- value fields, pairing each with its declared name.
    let fieldNames := getStructureFields env typeName
    -- Two different lists, deliberately kept apart. `fields` is the OUTPUT
    -- field list and excludes `Prop` fields (they are erased). `binderNames`
    -- is every telescope binder in order, `Prop` fields included, because de
    -- Bruijn indices inside a proposition count every binder — conflating the
    -- two shifts every index and silently references the wrong field.
    let mut fields : Array String := #[]
    let mut binderNames : Array String := #[]
    let mut ty := cv.type
    let mut i := 0
    while i < cv.numFields do
      match ty with
      | .forallE _ fieldTy rest _ =>
        let nm := match fieldNames[i]? with
          | some n => sanitize n
          | none => s!"field_{i}"
        if ← isPropType fieldTy then
          -- `i` is this `Prop` field's own 0-indexed telescope position,
          -- which is exactly the binder depth its bvars are relative to.
          match ← lowerProp fieldTy binderNames i with
          | some p => invProps := invProps.push p
          | none => invOk := false
        else
          fields := fields.push s!"({nm} {← lowerType fieldTy})"
        binderNames := binderNames.push nm
        ty := rest
        i := i + 1
      | _ =>
        -- The telescope ran out before `numFields` binders were consumed.
        -- Defensive: unreachable for a well-formed constructor. Any `Prop`
        -- field already collected would otherwise stay in `invProps` while
        -- the unvisited ones were silently dropped, emitting an invariant
        -- that omits conjuncts Lean proved — a partial check presented as a
        -- complete one, which is exactly the outcome the fragment must never
        -- produce. Decline the whole invariant instead.
        invOk := false
        i := cv.numFields
    ctorSexps := ctorSexps.push s!"(ctor \"{ctorName}\"{spaced fields})"
  -- Only a single-constructor type gets an invariant: with several
  -- constructors the field references would belong to different telescopes.
  let invariant : String :=
    if iv.ctors.length == 1 && invOk && !invProps.isEmpty then
      -- Left-associated: `p0`, `(and p0 p1)`, `(and (and p0 p1) p2)`, …
      let conj := (invProps.extract 1 invProps.size).foldl
        (init := invProps[0]!) fun acc p => s!"(and {acc} {p})"
      s!" (invariant {conj})"
    else ""
  return some s!"(type \"{typeName}\"{spaced ctorSexps}{invariant})"

/-- Type names a single LCNF `LetValue` mentions: a constructor application
    names its inductive, a projection names the structure it projects from.
    These are exactly the two places `lowerLetValue` emits a full Lean type or
    constructor name into the IR, so they are exactly the places codegen needs
    a matching `(type ...)` declaration for. -/
def letValueTypeNames (env : Environment) (v : LetValue .pure) : Array Name :=
  match v with
  | .proj typeName _ _ => #[typeName]
  | .const declName _ _ =>
    match env.find? declName with
    | some (.ctorInfo cv) => #[cv.induct]
    | _ => #[]
  | _ => #[]

/-- Every type name constructed or projected anywhere in a definition's body. -/
partial def codeTypeNames (env : Environment) : Code .pure → Array Name
  | .let decl k => letValueTypeNames env decl.value ++ codeTypeNames env k
  | .fun (.mk _ _ _ _ v) k => codeTypeNames env v ++ codeTypeNames env k
  | .jp (.mk _ _ _ _ v) k => codeTypeNames env v ++ codeTypeNames env k
  | .cases (.mk _ _ _ alts) =>
    alts.foldl (init := #[]) fun acc a =>
      match a with
      | .alt _ _ c => acc ++ codeTypeNames env c
      | .default c => acc ++ codeTypeNames env c
  | _ => #[]

/-- Every named type a declaration needs declared: the head constant of each
    parameter and return type, **plus** every type its body constructs or
    projects. Only the head constant matters — parameterised types are out of
    scope.

    The body half is not an optimization. A definition like
    `def f (n : Nat) := (NoProp.mk n n).alpha` mentions `NoProp` nowhere in its
    signature, so a signature-only walk never declares it; codegen then has no
    declaration to resolve `(ctor "Conformance.NoProp.mk" ...)` against and
    used to fall through to emitting the dotted Lean name as if it were a Rust
    path. Declaring body-reachable types is what makes that definition
    generate real Rust. (Codegen refuses the dotted path outright now too —
    that is the backstop for IR this function did not produce.) -/
def declTypeNames (env : Environment) (d : Decl .pure) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for p in d.params do
    if let .const n _ := p.type.getAppFn then out := out.push n
  if let .const n _ := (stripForalls d.params.size d.type).getAppFn then
    out := out.push n
  match d.value with
  | .code c => return out ++ codeTypeNames env c
  | _ => return out

end Prod
