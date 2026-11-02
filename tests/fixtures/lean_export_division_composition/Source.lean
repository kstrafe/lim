namespace DivisionCompositionSource

theorem small : Nat.div (2 ^ 6) (2 ^ 3) = 8 := rfl

theorem dividend : Nat.div (2 ^ 128) 18446744073709551616 = 18446744073709551616 := rfl

theorem divisor : Nat.div 340282366920938463463374607431768211456 (2 ^ 64) = 18446744073709551616 := rfl

theorem both : Nat.div (2 ^ 128) (2 ^ 64) = 18446744073709551616 := rfl

theorem equal : Nat.div (2 ^ 128) (2 ^ 128) = 1 := rfl

theorem below : Nat.div (2 ^ 10) (2 ^ 12) = 0 := rfl

theorem zero : Nat.div (2 ^ 128) 0 = 0 := rfl

theorem zeroDivZero : Nat.div 0 0 = 0 := rfl

theorem hugeDivZero : Nat.div 340282366920938463463374607431768211579 0 = 0 := rfl

theorem belowDivisor : Nat.div 2 5 = 0 := rfl

theorem equalDivisor : Nat.div 5 5 = 1 := rfl

theorem exactDivision : Nat.div 21 3 = 7 := rfl

theorem divisionWithRemainder : Nat.div 21 5 = 4 := rfl

theorem largeQuotient : Nat.div 340282366920938463463374607431768211456 18446744073709551616 = 18446744073709551616 := rfl

theorem largeRemainder : Nat.div 340282366920938463463374607431768211579 18446744073709551616 = 18446744073709551616 := rfl

end DivisionCompositionSource
