/- Original constructive fixture for compact mathematical natural literals.
   No axioms, admissions, native_decide, or bounded-integer approximations. -/
namespace NaturalSource

def huge : Nat := 184467440737095516160

theorem reflexive : huge = 184467440737095516160 := rfl

theorem successor : Nat.succ huge = 184467440737095516161 := rfl

def predecessor : Nat -> Nat
  | 0 => 0
  | Nat.succ n => n

theorem predecessorComputes : predecessor huge = 184467440737095516159 := rfl

def zeroOrNot : Nat -> Nat
  | 0 => 0
  | Nat.succ _ => 1

theorem constructorDiscriminates : zeroOrNot huge = 1 := rfl

def beyondU128 : Nat := 123456789012345678901234567890123456789012345678901234567890

theorem largerSuccessor : Nat.succ beyondU128 =
    123456789012345678901234567890123456789012345678901234567891 := rfl

end NaturalSource
