import Init.Data.Nat.Gcd
namespace GcdSource
theorem zeroLeft (n : Nat) : Nat.gcd 0 n = n := Nat.gcd_zero_left n
theorem successor (x y : Nat) : Nat.gcd (Nat.succ x) y = Nat.gcd (y % Nat.succ x) (Nat.succ x) := Nat.gcd_succ x y
theorem zeroRight (n : Nat) : Nat.gcd n 0 = n := Nat.gcd_zero_right n
end GcdSource
