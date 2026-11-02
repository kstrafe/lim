import Init.Data.Nat.Gcd
namespace GcdSelfSource
theorem self (n : Nat) : Nat.gcd n n = n := Nat.gcd_self n
end GcdSelfSource
