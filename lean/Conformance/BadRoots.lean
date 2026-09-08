module
public import Init

namespace Conformance.BadRoots

public theorem theoremRoot : True := True.intro

public unsafe def unsafeRoot (value : Nat) : Nat := value

public partial def partialRoot (value : Nat) : Nat := partialRoot value

public opaque noncomputableRoot : Nat

public def typeValuedRoot : Type := Nat

public def alpha (value : Nat) : Nat := value

public def zeta (value : Nat) : Nat := alpha value

public def belowLimit (value : Nat) : Bool := value < 4

public def matchedCallee : List Nat → Bool
  | [] => true
  | value :: rest => belowLimit value && matchedCallee rest

public structure NestedMember where
  value : Nat

public structure NestedOwner where
  members : List NestedMember

public def nestedOwnerMembers (owner : NestedOwner) : List NestedMember := owner.members

public structure ProjectionLeft where
  id : Nat

public structure ProjectionRight where
  id : Nat

public def sumProjectionIds (left : ProjectionLeft) (right : ProjectionRight) : Nat :=
  left.id + right.id

end Conformance.BadRoots
