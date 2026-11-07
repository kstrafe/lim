import Init.Data.Nat.Bitwise.Basic
namespace ShiftLeftProbe
theorem small : Nat.shiftLeft 13 2 = 52 := rfl
theorem zero (n : Nat) : Nat.shiftLeft n 0 = n := rfl
theorem large : Nat.shiftLeft 340282366920938463463374607431768211579 65 = 12554203470773361527671578846415332836742609931060618723328 := rfl
theorem general (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
end ShiftLeftProbe
