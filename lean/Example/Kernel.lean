-- Ported from uor-atlas-lean/UorAtlas/Kernel.lean.
-- mathlib-free: pure Lean 4 core/Init only.

namespace UorAtlas

/-- Instance parameters: scope q, modality T, context O -/
structure Instance where
  q : Nat
  T : Nat
  O : Nat
  valid : q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1

-- M3: will be tagged @[prod]
def stride (i : Instance) : Nat := i.T * i.O

-- M3: will be tagged @[prod]
def class_count (i : Instance) : Nat := i.q * stride i

-- M3: will be tagged @[prod]
def belt (i : Instance) : Nat := class_count i * 2^(i.O - 1)

-- M3: will be tagged @[prod]
/-- Mixed-radix class index: (h2, d, l) ↦ index -/
def classIndex (h2 d l : Nat) (i : Instance) : Nat :=
  stride i * h2 + i.O * d + l

-- M3: will be tagged @[prod]
/-- Inverse: index ↦ (h2, d, l) -/
def classDecode (idx : Nat) (i : Instance) : Nat × Nat × Nat :=
  let h2 := idx / stride i
  let rem := idx % stride i
  let d := rem / i.O
  let l := rem % i.O
  (h2, d, l)

end UorAtlas
