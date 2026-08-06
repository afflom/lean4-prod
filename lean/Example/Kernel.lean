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

end UorAtlas
