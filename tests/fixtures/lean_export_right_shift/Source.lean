import Init.Data.Nat.Bitwise.Basic
namespace ShiftRightProbe
theorem small : Nat.shiftRight 13 3 = 1 := rfl
theorem zero (n : Nat) : Nat.shiftRight n 0 = n := rfl
theorem large : Nat.shiftRight 340282366920938463463374607431768211579 64 = 18446744073709551616 := rfl
theorem boundary : Nat.shiftRight 13 4 = 0 := rfl
end ShiftRightProbe
