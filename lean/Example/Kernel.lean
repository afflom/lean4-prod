-- Ported from uor-atlas-lean/UorAtlas/Kernel.lean.
-- Pure Lean 4 core/Init only.

import Prod.Attribute

namespace UorAtlas

/-- Instance parameters: scope q, modality T, context O -/
structure Instance where
  q : Nat
  T : Nat
  O : Nat
  valid : q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1

@[prod]
def stride (i : Instance) : Nat := i.T * i.O

@[prod]
def class_count (i : Instance) : Nat := i.q * stride i

@[prod]
def belt (i : Instance) : Nat := class_count i * 2^(i.O - 1)

/-- Mixed-radix class index: (h2, d, l) ↦ index -/
@[prod]
def classIndex (h2 d l : Nat) (i : Instance) : Nat :=
  stride i * h2 + i.O * d + l

/-- Inverse: index ↦ (h2, d, l) -/
@[prod]
def classDecode (idx : Nat) (i : Instance) : Nat × Nat × Nat :=
  let h2 := idx / stride i
  let rem := idx % stride i
  let d := rem / i.O
  let l := rem % i.O
  (h2, d, l)

/-- Base-`O` digit count of `n` (0 ↦ 1), bounded by `fuel` (structural
    recursion — no termination proof needed). Pipeline probe: first recursive
    `@[prod]` definition; exercises LCNF `cases` on Nat, the decidable `<`
    guard, division, and a self-call through lowering and codegen. -/
@[prod]
def digitCount (fuel n : Nat) (i : Instance) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if n < i.O then 1 else 1 + digitCount fuel (n / i.O) i

/-- Base-`O` digits of `n`, least-significant first, bounded by `fuel`.
    Pipeline probe: first `List`-valued `@[prod]` definition (constructor
    building + recursion). -/
@[prod]
def digits (fuel n : Nat) (i : Instance) : List Nat :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n < i.O then [n] else n % i.O :: digits fuel (n / i.O) i

/-- Sum of a digit list. Pipeline probe: first `cases` on `List`
    (nil/cons pattern matching). -/
@[prod]
def digitSum : List Nat → Nat
  | [] => 0
  | d :: rest => d + digitSum rest

/-- Are two indices in the same class (equal quotient by `stride`)?
    Pipeline probe: decidable `=` guard (`Nat.decEq`). -/
@[prod]
def sameClass (a b : Nat) (i : Instance) : Bool :=
  if a / stride i = b / stride i then true else false

/-- Does `idx` fit under the belt bound? Pipeline probe: decidable `≤`
    guard (`Nat.decLe`). -/
@[prod]
def smallEnough (idx : Nat) (i : Instance) : Bool :=
  if idx ≤ belt i then true else false

/-- `classDecode` guarded by the class-count bound. Pipeline probe:
    first `Option`-valued `@[prod]` definition. -/
@[prod]
def tryClassDecode (idx : Nat) (i : Instance) : Option (Nat × Nat × Nat) :=
  if idx < class_count i then some (classDecode idx i) else none

end UorAtlas
