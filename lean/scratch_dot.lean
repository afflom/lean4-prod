structure Foo where
  x : Nat

namespace FooNS

structure Bar where
  x : Nat

def bar_twice (b : Bar) : Nat := b.x + b.x

end FooNS

def use_it (b : FooNS.Bar) : Nat := b.bar_twice

#check use_it
