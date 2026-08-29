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

end Conformance.BadRoots
