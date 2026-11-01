/- Genuine standard natural arithmetic computations using Nat.add, Nat.mul,
   and Nat.pow. No axioms, admissions, or native-decision shortcuts. -/
namespace ArithmeticSource

theorem addition : Nat.add 184467440737095516160 340282366920938463463374607431768211456 =
    340282366920938463647842048168863727616 := rfl

theorem multiplication : Nat.mul 184467440737095516160 100000000000000000000 =
    18446744073709551616000000000000000000000 := rfl

theorem zeroProduct : Nat.mul 0 340282366920938463463374607431768211456 = 0 := rfl

theorem zeroRight (value : Nat) : Nat.add value 0 = value := rfl

theorem nested : Nat.add (Nat.mul 184467440737095516160 100000000000000000000) 7 =
    18446744073709551616000000000000000000007 := rfl

theorem power : Nat.pow 2 128 = 340282366920938463463374607431768211456 := rfl

theorem zeroBase : Nat.pow 0 128 = 0 := rfl

theorem zeroExponent (value : Nat) : Nat.pow value 0 = 1 := rfl

-- Let Lean evaluate this fixed one-base power instead of unfolding a million cases.
set_option exponentiation.threshold 1000000 in
theorem oneBase : Nat.pow 1 1000000 = 1 := rfl

theorem nestedPower : Nat.add (Nat.pow 2 128) 7 =
    340282366920938463463374607431768211463 := rfl

def affine (count : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ value => Nat.add (Nat.mul 2 value) 1) count

set_option maxRecDepth 2048 in
theorem affineGrowth : affine 128 = 340282366920938463463374607431768211455 := rfl

end ArithmeticSource
