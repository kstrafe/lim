namespace RemainderSource

theorem zero : Nat.mod 0 0 = 0 := rfl

theorem hugeZero : Nat.mod 340282366920938463463374607431768211579 0 = 340282366920938463463374607431768211579 := rfl

theorem below : Nat.mod 3 5 = 3 := rfl

theorem equal : Nat.mod 5 5 = 0 := rfl

theorem exact : Nat.mod 21 3 = 0 := rfl

theorem withRemainder : Nat.mod 21 5 = 1 := rfl

theorem large : Nat.mod 340282366920938463463374607431768211579 18446744073709551616 = 123 := rfl

theorem largeEqualPowers : Nat.mod 340282366920938463463374607431768211579 (2 ^ 128) = 123 := rfl

theorem computed : Nat.mod (2 ^ 128 + 123) (2 ^ 64) = 123 := rfl

theorem computedEqualPowers : Nat.mod (2 ^ 128) (2 ^ 128) = 0 := rfl

theorem computedBelow : Nat.mod (2 ^ 10) (2 ^ 12) = 1024 := rfl

theorem computedZero : Nat.mod (2 ^ 128) 0 = 2 ^ 128 := rfl

theorem zeroLeft (n : Nat) : Nat.mod 0 n = 0 := rfl

theorem zeroDivisor (n : Nat) : Nat.mod n 0 = n := by
  cases n with
  | zero => rfl
  | succ n => unfold Nat.mod Nat.modCore; rfl

end RemainderSource
