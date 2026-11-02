/- Genuine standard natural arithmetic computations using Nat.add, Nat.mul,
   Nat.pow, Nat.sub, Nat.ble and Nat.beq. No axioms, admissions or native-decision shortcuts. -/
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

theorem subtraction : Nat.sub 340282366920938463463374607431768211456 18446744073709551616 =
    340282366920938463444927863358058659840 := rfl

theorem subtractToZero : Nat.sub 7 340282366920938463463374607431768211456 = 0 := rfl

theorem subtractSelf : Nat.sub 340282366920938463463374607431768211456
    340282366920938463463374607431768211456 = 0 := rfl

theorem zeroMinus : Nat.sub 0 340282366920938463463374607431768211456 = 0 := rfl

theorem subtractZero (value : Nat) : Nat.sub value 0 = value := rfl

theorem nestedSubtraction : Nat.add
    (Nat.sub 340282366920938463463374607431768211456 18446744073709551616) 7 =
    340282366920938463444927863358058659847 := rfl

theorem booleanControl : Nat.ble 2 1 = false := rfl

theorem booleanLess : Nat.ble 340282366920938463463374607431768211456
    340282366920938463463374607431768211457 = true := rfl

theorem booleanEqual : Nat.ble 340282366920938463463374607431768211456
    340282366920938463463374607431768211456 = true := rfl

theorem booleanGreater : Nat.ble 340282366920938463463374607431768211457
    340282366920938463463374607431768211456 = false := rfl

theorem booleanZeroLeft : Nat.ble 0 340282366920938463463374607431768211456 = true := rfl

theorem booleanZeroRight : Nat.ble 340282366920938463463374607431768211456 0 = false := rfl

theorem booleanGenericZero (value : Nat) : Nat.ble 0 value = true := rfl

theorem booleanNested : Nat.ble
    (Nat.sub 340282366920938463463374607431768211456 18446744073709551616)
    (Nat.add 340282366920938463444927863358058659840 1) = true := rfl

theorem equalControl : Nat.beq 1 1 = true := rfl

theorem equalLarge : Nat.beq 340282366920938463463374607431768211456
    340282366920938463463374607431768211456 = true := rfl

theorem unequalLarge : Nat.beq 340282366920938463463374607431768211456
    340282366920938463463374607431768211457 = false := rfl

theorem unequalReverse : Nat.beq 340282366920938463463374607431768211457
    340282366920938463463374607431768211456 = false := rfl

theorem equalZero : Nat.beq 0 0 = true := rfl

end ArithmeticSource
