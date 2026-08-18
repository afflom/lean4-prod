-- Probes for the Lean-structure-field → LCNF-projection-index correspondence.
-- Fields carry distinguishable values on purpose: if the mapping were wrong,
-- c_proj_middle_prop would return the fields in the wrong order and the golden
-- would change. See AGENTS.md for the rule these pin down.
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

@[prod] def c_proj_middle_prop (m : MidProp) : Nat × Nat × Nat :=
  (m.first, m.second, m.third)

@[prod] def c_proj_no_prop (n : NoProp) : Nat × Nat :=
  (n.alpha, n.beta)

end Conformance
