-- Conformance cases for the Lean → IR lowering. One @[prod] def per feature.
-- The lowered output is diffed against lean/Conformance/golden.ir in CI, so a
-- change here or in Prod/Lower.lean shows up as a reviewable golden diff.
-- Regenerate with `just conformance-bless`. Never hand-edit the golden.
import Prod.Attribute
import Conformance.Structures

namespace Conformance

@[prod] def c_nat_add (a b : Nat) : Nat := a + b
@[prod] def c_nat_sub (a b : Nat) : Nat := a - b
@[prod] def c_nat_mul (a b : Nat) : Nat := a * b
@[prod] def c_nat_div (a b : Nat) : Nat := a / b
@[prod] def c_nat_mod (a b : Nat) : Nat := a % b
@[prod] def c_nat_pow (a b : Nat) : Nat := a ^ b
-- `shiftRight` also reaches lowering via `c_nat_rec`/`c_list_build`'s `n / 2`
-- peephole below, but that is an indirect witness; these two are the direct
-- `<<</>>>` analogue of the six ops above, so the published subset contract
-- (`specs/lean-for-production.md`) can claim both operators on the strength
-- of a dedicated conformance case, not just the operator whitelist.
@[prod] def c_nat_shl (a b : Nat) : Nat := a <<< b
@[prod] def c_nat_shr (a b : Nat) : Nat := a >>> b

@[prod] def c_guard_lt (a b : Nat) : Nat := if a < b then 1 else 0
@[prod] def c_guard_le (a b : Nat) : Nat := if a ≤ b then 1 else 0
@[prod] def c_guard_eq (a b : Nat) : Nat := if a = b then 1 else 0

@[prod] def c_bool (a b : Nat) : Bool := a < b
@[prod] def c_option (a : Nat) : Option Nat := if a < 10 then some a else none
@[prod] def c_tuple (a b : Nat) : Nat × Nat := (a, b)

@[prod] def c_nat_rec (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if n < 2 then 1 else 1 + c_nat_rec fuel (n / 2)

@[prod] def c_list_build (fuel n : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel + 1 => if n < 2 then [n] else n % 2 :: c_list_build fuel (n / 2)

@[prod] def c_list_consume : List Nat → Nat
  | [] => 0
  | h :: t => h + c_list_consume t

-- Bool connectives. `&&`/`||` are `@[macro_inline]` in Lean and elaborate
-- through `match`, so the expectation is that they reach LCNF as `cases` on
-- `Bool.true`/`Bool.false` and need no IR node at all. These pin whichever
-- answer is true.
@[prod] def c_bool_and (a b : Nat) : Bool := (a < b) && (b < 10)
@[prod] def c_bool_or  (a b : Nat) : Bool := (a < b) || (b < 10)
@[prod] def c_bool_not (a b : Nat) : Bool := !(a < b)

-- Int. The negative-operand cases are the point: Lean's / and % are Euclidean
-- (Int.ediv / Int.emod), Rust's truncate, and they differ only when an operand
-- is negative. Lean's own doctest gives (-12) % 7 = 2; Rust's % gives -5.
@[prod] def c_int_add (a b : Int) : Int := a + b
@[prod] def c_int_sub (a b : Int) : Int := a - b
@[prod] def c_int_mul (a b : Int) : Int := a * b
@[prod] def c_int_ediv (a b : Int) : Int := a / b
@[prod] def c_int_emod (a b : Int) : Int := a % b
@[prod] def c_int_neg (a : Int) : Int := -a
@[prod] def c_int_guard_lt (a b : Int) : Int := if a < b then 1 else 0
@[prod] def c_int_guard_eq (a b : Int) : Int := if a = b then 1 else 0

-- Sized integers. The boundary cases are the point: wrapping is Lean's
-- semantics (BitVec arithmetic), so a case that stays in range would pass
-- under a checked rendering too.
@[prod] def c_u8_add (a b : UInt8) : UInt8 := a + b
@[prod] def c_u8_sub (a b : UInt8) : UInt8 := a - b
@[prod] def c_u8_mul (a b : UInt8) : UInt8 := a * b
@[prod] def c_u8_div (a b : UInt8) : UInt8 := a / b
@[prod] def c_u8_shl (a b : UInt8) : UInt8 := a <<< b

end Conformance
