import Example.Kernel

-- Ported from uor-atlas-lean/UorAtlas/Proofs/S1.lean.
-- Pure core: `nlinarith` replaced by explicit `Nat.mul_le_mul_left` /
-- `Nat.mul_succ` steps feeding `omega`; div/mod facts via Init's
-- `Nat.add_mul_div_left` / `Nat.add_mul_mod_self_left`.
-- Note: `stride`/`class_count` are used in prefix form (`stride i`) since
-- dot notation requires membership in `Instance`'s namespace.

namespace UorAtlas

/-- Auxiliary: the low two digits fit inside one stride.
    (Was an inline `have` in the source proofs; factored out since both
    theorems need it. Pure core: no nlinarith.) -/
private theorem digits_lt_stride (i : Instance) {d l : Nat}
    (hT : d < i.T) (hO : l < i.O) : i.O * d + l < stride i := by
  have hsucc : i.O * (d + 1) = i.O * d + i.O := Nat.mul_succ i.O d
  have hle : i.O * (d + 1) ≤ i.O * i.T := by
    apply Nat.mul_le_mul_left
    omega
  have hcomm : i.O * i.T = stride i := by
    rw [stride]; exact Nat.mul_comm _ _
  omega

/-- S-1: classIndex is a bijection onto [0, qTO) -/
theorem classIndex_bijective (i : Instance) :
    ∀ h2 d l, h2 < i.q → d < i.T → l < i.O →
      classIndex h2 d l i < class_count i := by
  intro h2 d l hq hT hO
  have h1 : i.O * d + l < stride i := digits_lt_stride i hT hO
  have hsucc : stride i * (h2 + 1) = stride i * h2 + stride i :=
    Nat.mul_succ (stride i) h2
  have hle : stride i * (h2 + 1) ≤ stride i * i.q := by
    apply Nat.mul_le_mul_left
    omega
  have hcc : stride i * i.q = class_count i := by
    rw [class_count]; exact Nat.mul_comm _ _
  have hdef : classIndex h2 d l i = stride i * h2 + i.O * d + l := rfl
  omega

/-- Decode inverts encode -/
theorem classDecode_encode (i : Instance) (h2 d l : Nat)
    (hq : h2 < i.q) (hT : d < i.T) (hO : l < i.O) :
    classDecode (classIndex h2 d l i) i = (h2, d, l) := by
  obtain ⟨-, hT1, hO1⟩ := i.valid
  have h1 : i.O * d + l < stride i := digits_lt_stride i hT hO
  have hs_pos : 0 < stride i := by
    show 0 < i.T * i.O
    exact Nat.mul_pos hT1 hO1
  have e1 : stride i * h2 + i.O * d + l = i.O * d + l + stride i * h2 := by
    omega
  have hdiv : (stride i * h2 + i.O * d + l) / stride i = h2 := by
    rw [e1, Nat.add_mul_div_left _ _ hs_pos, Nat.div_eq_of_lt h1, Nat.zero_add]
  have hmod : (stride i * h2 + i.O * d + l) % stride i = i.O * d + l := by
    rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have e2 : i.O * d + l = l + i.O * d := Nat.add_comm _ _
  have hdiv2 : (i.O * d + l) / i.O = d := by
    rw [e2, Nat.add_mul_div_left _ _ hO1, Nat.div_eq_of_lt hO, Nat.zero_add]
  have hmod2 : (i.O * d + l) % i.O = l := by
    rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hO]
  simp only [classDecode, classIndex, hdiv, hmod, hdiv2, hmod2]

end UorAtlas
