import Init.Data.Nat.Gcd
namespace GcdProbe
theorem zeroLeft (n : Nat) : Nat.gcd 0 n = n := Nat.gcd_zero_left n
theorem self (n : Nat) : Nat.gcd n n = n := Nat.gcd_self n
theorem closed : Nat.gcd 84 30 = 6 := rfl
end GcdProbe
