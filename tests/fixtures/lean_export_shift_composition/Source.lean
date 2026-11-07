import Init.Data.Nat.Bitwise.Basic
namespace ShiftCompositionProbe
theorem general (m n k : Nat) : Nat.shiftRight m (n + k) = Nat.shiftRight (Nat.shiftRight m n) k := Nat.shiftRight_add m n k
end ShiftCompositionProbe
