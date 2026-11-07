import Init.Data.Nat.Bitwise.Basic
namespace BitwiseProbe
theorem and_small : Nat.land 13 11 = 9 := rfl
theorem or_small : Nat.lor 13 11 = 15 := rfl
theorem xor_small : Nat.xor 13 11 = 6 := rfl
end BitwiseProbe
