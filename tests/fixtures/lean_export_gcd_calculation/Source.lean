import Init.Data.Nat.Gcd
namespace GcdCalculationSource
theorem closed : Nat.gcd 84 30 = 6 :=
  calc
    Nat.gcd 84 30 = Nat.gcd 30 84 := Nat.gcd_succ 83 30
    _ = Nat.gcd 24 30 := Nat.gcd_succ 29 84
    _ = Nat.gcd 6 24 := Nat.gcd_succ 23 30
    _ = Nat.gcd 0 6 := Nat.gcd_succ 5 24
    _ = 6 := Nat.gcd_zero_left 6
end GcdCalculationSource
