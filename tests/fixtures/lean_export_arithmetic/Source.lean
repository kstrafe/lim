/- Genuine standard natural arithmetic computations using Lean's Nat.add and
   Nat.mul. No axioms, admissions, imports, or native-decision shortcuts. -/
namespace ArithmeticSource

theorem addition : Nat.add 184467440737095516160 340282366920938463463374607431768211456 =
    340282366920938463647842048168863727616 := rfl

theorem multiplication : Nat.mul 184467440737095516160 100000000000000000000 =
    18446744073709551616000000000000000000000 := rfl

theorem zeroProduct : Nat.mul 0 340282366920938463463374607431768211456 = 0 := rfl

theorem zeroRight (value : Nat) : Nat.add value 0 = value := rfl

theorem nested : Nat.add (Nat.mul 184467440737095516160 100000000000000000000) 7 =
    18446744073709551616000000000000000000007 := rfl

end ArithmeticSource
