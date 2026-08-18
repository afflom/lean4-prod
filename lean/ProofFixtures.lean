import Prod.Attribute

/-!
# Proof fixtures

Small, real Lean declarations used to exercise proof compilation independently
of the worked example and the lowering conformance corpus. These are fixtures,
not production definitions: `Prod.Emit` does not import this library, so adding
one here cannot silently change the committed export artifacts.

Every theorem below is kernel-checked Lean, with no `sorry` or `axiom`. Keep
fixtures minimal and name them after the proof shape they pin; if a pipeline
test needs a new proof form, add it here before relying on a generated artifact.
-/

namespace ProofFixtures

@[prod]
def add (a b : Nat) : Nat := a + b

@[prod]
def boundedStep (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel + 1 => boundedStep fuel (n + 1)

/- A definitional equality fixture: the proof is checked by reduction alone. -/
theorem add_zero (n : Nat) : add n 0 = n := by
  rfl

/- An arithmetic proof fixture: the proof is kernel-checked rather than being
   represented by a hand-written Rust or IR assertion. -/
theorem add_succ (a b : Nat) : add a (b + 1) = add a b + 1 := by
  simp [add, Nat.add_assoc]

/- A bounded-recursion fixture: the definition is total, while the theorem
   records the value of its zero-fuel base case. -/
theorem boundedStep_zero (n : Nat) : boundedStep 0 n = n := by
  rfl

/- A proof fixture over a symbolic variable: Lean's arithmetic tactic discharges
   it in the fixture library. -/
theorem positive_successor (n : Nat) : 0 < n + 1 := by
  omega

end ProofFixtures
