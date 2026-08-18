-- Probes for the Lean-structure-field → LCNF-projection-index correspondence,
-- and for the `Prop`-field invariant lowering (`Prod.lowerProp`).
-- Fields carry distinguishable values on purpose: if the mapping were wrong,
-- c_proj_middle_prop would return the fields in the wrong order and the golden
-- would change. See AGENTS.md for the rule these pin down.
--
-- The invariant probes below are load-bearing regression guards, NOT clutter.
-- `lean/Conformance/golden.ir` is committed and diffed by `just conformance`,
-- so each one's expected `(invariant ...)` clause is pinned there and a
-- lowering change that alters it fails the build. Every structure's doc
-- comment names the specific way lowering could go wrong that only that
-- structure can see. Deleting one silently removes the only thing watching
-- for its failure — which is how this project shipped a backwards shift
-- rendering green. Read the doc comment before removing anything here.
import Prod.Attribute

namespace Conformance

/-- Prop field in the MIDDLE, not at the end: the case the existing
    `UorAtlas.Instance` (whose proof field is last) does not exercise. -/
structure MidProp where
  first  : Nat
  ok     : first ≥ 0
  second : Nat
  third  : Nat

/-- All-computational structure, as a control. -/
structure NoProp where
  alpha : Nat
  beta  : Nat

/-- A swapping comparison beside two non-swapping ones.

    Every comparison elsewhere in the committed corpus is `≥`, so a change
    that made the operand swap unconditional — `LE.le ↦ ("le", true)`, or a
    blanket reversal — would leave `golden.ir` and `kernel.ir` byte-identical
    and pass every gate. This structure is the only thing that can see it:
    `lo ≥ 2` must swap while `hi ≤ 7` and `lo < hi` beside it must not, so
    "always swap", "never swap" and "swap only `≥`/`>`" all produce visibly
    different goldens.

    `lo < hi` additionally pins two DISTINCT field references resolved at the
    same binder depth inside one comparison (`lo`→`#1`, `hi`→`#0`).
    `UorAtlas.Instance` has three references but each sits at its own depth,
    and `MidProp` has a single field, so neither can catch an index that is
    off by a constant. -/
structure MixedCompare where
  lo     : Nat
  hi     : Nat
  bounds : lo ≥ 2 ∧ hi ≤ 7 ∧ lo < hi
  extra  : Nat

/-- Two SEPARATE `Prop` fields, interleaved with the computational ones.

    Pins two things nothing else does. First, the left-associated fold that
    conjoins several `Prop` fields into one `(invariant ...)` clause — every
    other structure in the corpus has at most one `Prop` field, so the fold is
    otherwise never run. Second, and more important, `hb` refers to `a` ACROSS
    the intervening `ha` binder (`a`→`#2` at depth 3). De Bruijn indices count
    every binder including `Prop` ones, so this is the case that fails if the
    binder-name array is ever confused with the emitted field list — the exact
    conflation `lowerTypeDecl` keeps two separate arrays to prevent. -/
structure SplitInvariant where
  a  : Nat
  ha : a ≥ 1
  b  : Nat
  hb : b ≥ a

/-- Disjunction and negation, the two connectives no other structure reaches.

    `¬ (limit = 0)` is deliberately spelled with `¬` and `=` rather than the
    idiomatic `limit ≠ 0`: `≠` is `Ne`, which is outside the lowerable
    fragment and would decline the whole invariant (see `UnlowerableProp`
    below, which pins exactly that). The two spellings denote the same
    proposition and lower differently, which is itself worth having recorded
    in the corpus. -/
structure TaggedMode where
  mode  : Nat
  limit : Nat
  ok    : (mode = 0 ∨ mode = 1) ∧ ¬ (limit = 0)

/-- The only `Int` invariant in the corpus.

    The published contract (`specs/lean-for-production.md`) says comparisons
    lower "only on `Nat`, `Int` and the sized kinds", and `propCmpKinds`
    admits `Int` — but every other `(invariant ...)` in the repo is over
    `Nat`, so `Int` was a published guarantee nothing ran. Dropping `Int`
    from `propCmpKinds` would have left every golden byte-identical.

    `hi ≤ 100` additionally pins that an `Int` numeric literal reaches
    `lowerPropOperand` as an `OfNat.ofNat` application whose raw argument is
    the value — the same shape as `Nat`'s, on a different kind. -/
structure IntRange where
  lo : Int
  hi : Int
  ok : lo ≤ hi ∧ hi ≤ 100

/-- The only sized-kind invariant in the corpus, and the only place a
    comparison on a bounded kind is exercised at all.

    Same "published but unexecuted" gap as `IntRange`, plus one that is
    specific to the sized kinds: `lowerPropOperand` reads an `OfNat` numeral
    *before* interpretation, so a literal is lowered as its written digits.
    For `Nat` that is exact — a `Nat` literal is its value — but for `UInt8`
    it is only exact while the literal is in range: `(256 : UInt8)` is `0`
    and would lower as `256`. `cap ≤ 200` is in range and therefore correct;
    it is here so that the sized-kind path is executed at all, and so that a
    future in-range/out-of-range distinction has something to sit beside.
    (An out-of-range literal is not added deliberately: it would pin wrong
    output as expected output.)

    `used ≤ cap` beside it pins a field-to-field comparison on a sized kind,
    which no literal-only bound can distinguish from a constant fold. -/
structure ByteWindow where
  used : UInt8
  cap  : UInt8
  fits : used ≤ cap ∧ cap ≤ 200

/-- One lowerable `Prop` field and one unlowerable one, in the same type.

    `UnlowerableProp` and `NonNumericCompare` each have a SINGLE, wholly
    unlowerable `Prop` field, so both only ever exercise "zero conjuncts
    survive". This is the only structure that exercises "one survives, one
    does not" — the sole input under which a PARTIAL invariant could ever be
    emitted, which the contract and `AGENTS.md` both publish as impossible
    ("a type re-checks its whole proposition or none of it"; "Never a partial
    check").

    `h1 : x ≥ 1` lowers on its own — it is the same shape as
    `SplitInvariant`'s first conjunct — and `h2 : x ≠ y` does not (`≠` is
    `Ne`). The required outcome is that this type appears in `golden.ir`
    DECLARED WITH ITS FIELDS and with NO `(invariant ...)` clause at all:
    not `(invariant (le 1 x))`, which would be a check presented as
    complete, and not absent. `lowerTypeDecl`'s `invOk := false` on any
    decline is what makes that true; nothing else in the corpus can tell it
    from a version that simply skipped the unlowerable conjunct. -/
structure PartialProp where
  x  : Nat
  y  : Nat
  h1 : x ≥ 1
  h2 : x ≠ y

/-- The DECLINE path: a `Prop` field outside the fragment.

    `≠` is `Ne`, which is not a connective or comparison `lowerProp` handles.
    The whole invariant is then dropped and this type must appear in the
    golden DECLARED WITH ITS FIELDS and with no `(invariant ...)` clause at
    all — a strictly weaker outcome (public fields, no checked constructor),
    never a wrong one. That fallback is the fragment's central safety property
    and nothing in the corpus exercised it before this. Note the invariant is
    dropped ENTIRELY rather than partially: a partial invariant would be a
    check presented as complete. -/
structure UnlowerableProp where
  x  : Nat
  y  : Nat
  ne : x ≠ y

/-- The decline path for a comparison on a type outside the numeric fragment.

    `lowerProp` is scoped to comparisons on supported numeric kinds. `Bool`
    equality is the reachable case that scope excludes while still being a
    field type the IR renders natively, so it is the one structure that can
    tell an enforced restriction from a merely documented one: before the
    check existed this lowered to `(eq flagA flagB)`, a scalar comparison node
    for a type the fragment never claimed to cover. Must appear with no
    `(invariant ...)` clause. -/
structure NonNumericCompare where
  flagA : Bool
  flagB : Bool
  agree : flagA = flagB

@[prod] def c_proj_middle_prop (m : MidProp) : Nat × Nat × Nat :=
  (m.first, m.second, m.third)

@[prod] def c_proj_no_prop (n : NoProp) : Nat × Nat :=
  (n.alpha, n.beta)

-- The structures above are collected into the IR only if some `@[prod]`
-- definition mentions them (`Prod.Emit.collectTypeDecls` walks reachable
-- types), so each needs a witness. They are deliberately trivial projections:
-- what is under test is the `(type ...)` declaration these force into the
-- golden, not the function bodies.

@[prod] def c_mixed_compare (m : MixedCompare) : Nat :=
  m.lo + m.hi + m.extra

@[prod] def c_split_invariant (s : SplitInvariant) : Nat :=
  s.a + s.b

@[prod] def c_tagged_mode (t : TaggedMode) : Nat :=
  t.mode + t.limit

@[prod] def c_unlowerable_prop (u : UnlowerableProp) : Nat :=
  u.x + u.y

@[prod] def c_non_numeric_compare (v : NonNumericCompare) : Bool :=
  v.flagA

@[prod] def c_int_range (r : IntRange) : Int :=
  r.lo + r.hi

@[prod] def c_byte_window (b : ByteWindow) : UInt8 :=
  b.used + b.cap

@[prod] def c_partial_prop (p : PartialProp) : Nat :=
  p.x + p.y

end Conformance
