use super::{Natural, Result, MAX_DIGITS};

impl Natural {
    /// Subtracts with saturation at zero.
    ///
    /// Callers must budget operand digit work and result allocation before calling,
    /// matching the budgeting required by `add` and `multiply`.
    pub(super) fn truncated_subtract(&self, other: &Self) -> Self {
        let left = self.0.as_bytes();
        let right = other.0.as_bytes();
        if left.len() < right.len() || (left.len() == right.len() && left < right) {
            return Self("0".into());
        }

        let mut result = vec![b'0'; left.len()];
        let (mut i, mut j, mut borrow) = (left.len(), right.len(), 0i16);
        while i > 0 {
            i -= 1;
            let a = i16::from(left[i] - b'0');
            let b = if j > 0 {
                j -= 1;
                i16::from(right[j] - b'0')
            } else {
                0
            };
            let mut digit = a - b - borrow;
            if digit < 0 {
                digit += 10;
                borrow = 1;
            } else {
                borrow = 0;
            }
            result[i] = b'0' + digit as u8;
        }

        let first = result
            .iter()
            .position(|&digit| digit != b'0')
            .unwrap_or(result.len() - 1);
        if first > 0 {
            result.copy_within(first.., 0);
            result.truncate(result.len() - first);
        }
        Self(String::from_utf8(result).expect("decimal subtraction"))
    }

    pub(super) fn halve(&self) -> (Self, bool) {
        let bytes = self.0.as_bytes();
        let odd = (bytes[bytes.len() - 1] - b'0') % 2 != 0;
        let mut quotient = Vec::with_capacity(bytes.len());
        let mut carry = 0u8;

        for &byte in bytes {
            let value = carry * 10 + (byte - b'0');
            let digit = value / 2;
            carry = value % 2;
            if !quotient.is_empty() || digit != 0 {
                quotient.push(b'0' + digit);
            }
        }

        if quotient.is_empty() {
            quotient.push(b'0');
        }
        (
            Self(String::from_utf8(quotient).expect("decimal halving")),
            odd,
        )
    }

    pub(super) fn add(&self, other: &Self) -> Result<Self> {
        let left = self.0.as_bytes();
        let right = other.0.as_bytes();
        let capacity = left.len().max(right.len()) + 1;
        let mut reversed = Vec::with_capacity(capacity);
        let (mut i, mut j, mut carry) = (left.len(), right.len(), 0u8);

        while i > 0 || j > 0 || carry != 0 {
            let a = if i > 0 {
                i -= 1;
                left[i] - b'0'
            } else {
                0
            };
            let b = if j > 0 {
                j -= 1;
                right[j] - b'0'
            } else {
                0
            };
            let sum = a + b + carry;
            reversed.push(b'0' + sum % 10);
            carry = sum / 10;
        }

        if reversed.len() > MAX_DIGITS {
            return Err(format!(
                "natural arithmetic digit limit exceeded ({MAX_DIGITS})"
            ));
        }
        reversed.reverse();
        Ok(Self(String::from_utf8(reversed).expect("decimal addition")))
    }

    pub(super) fn multiply(&self, other: &Self) -> Result<Self> {
        if self.0 == "0" || other.0 == "0" {
            return Ok(Self("0".into()));
        }

        let left = self.0.as_bytes();
        let right = other.0.as_bytes();
        let mut digits = vec![0u8; left.len() + right.len()];
        for i in (0..left.len()).rev() {
            let a = left[i] - b'0';
            let mut carry = 0u16;
            for j in (0..right.len()).rev() {
                let index = i + j + 1;
                let product =
                    u16::from(a) * u16::from(right[j] - b'0') + u16::from(digits[index]) + carry;
                digits[index] = (product % 10) as u8;
                carry = product / 10;
            }
            digits[i] = carry as u8;
        }

        let first = digits
            .iter()
            .position(|&digit| digit != 0)
            .unwrap_or(digits.len() - 1);
        let significant = &digits[first..];
        if significant.len() > MAX_DIGITS {
            return Err(format!(
                "natural arithmetic digit limit exceeded ({MAX_DIGITS})"
            ));
        }
        let decimal: Vec<u8> = significant.iter().map(|&digit| b'0' + digit).collect();
        Ok(Self(
            String::from_utf8(decimal).expect("decimal multiplication"),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn natural(value: &str) -> Natural {
        Natural::parse(value).unwrap()
    }

    #[test]
    fn arithmetic_matches_small_integer_reference_for_all_small_pairs() {
        for a in 0..=100u128 {
            for b in 0..=100u128 {
                let left = natural(&a.to_string());
                let right = natural(&b.to_string());
                assert_eq!(left.add(&right).unwrap().decimal(), (a + b).to_string());
                assert_eq!(
                    left.truncated_subtract(&right).decimal(),
                    a.saturating_sub(b).to_string()
                );
                assert_eq!(
                    left.multiply(&right).unwrap().decimal(),
                    (a * b).to_string()
                );
            }
        }
    }

    #[test]
    fn arithmetic_is_exact_above_u128() {
        let a = natural("340282366920938463463374607431768211456");
        let b = natural("999999999999999999999999999999999999999");
        assert_eq!(
            a.add(&b).unwrap().decimal(),
            "1340282366920938463463374607431768211455"
        );
        assert_eq!(
            a.multiply(&natural("2")).unwrap().decimal(),
            "680564733841876926926749214863536422912"
        );
        assert_eq!(
            a.multiply(&a).unwrap().decimal(),
            "115792089237316195423570985008687907853269984665640564039457584007913129639936"
        );
        assert_eq!(
            natural("1000000000000000000000000000000000000000")
                .truncated_subtract(&a)
                .decimal(),
            "659717633079061536536625392568231788544"
        );
        assert_eq!(a.truncated_subtract(&a).decimal(), "0");
        let nines = natural(&"9".repeat(1000));
        assert_eq!(
            nines.multiply(&nines).unwrap().decimal(),
            format!("{}8{}1", "9".repeat(999), "0".repeat(999))
        );
    }

    #[test]
    fn subtraction_handles_zero_ordering_and_maximum_length_borrow() {
        let huge = natural(&format!("1{}", "0".repeat(MAX_DIGITS - 1)));
        assert_eq!(natural("0").truncated_subtract(&huge).decimal(), "0");
        assert_eq!(
            huge.truncated_subtract(&natural("0")).decimal(),
            huge.decimal()
        );
        assert_eq!(
            huge.truncated_subtract(&natural("1")).decimal(),
            "9".repeat(MAX_DIGITS - 1)
        );

        let nines = natural(&"9".repeat(MAX_DIGITS));
        assert_eq!(
            nines.truncated_subtract(&natural("1")).decimal(),
            format!("{}8", "9".repeat(MAX_DIGITS - 1))
        );
        assert_eq!(nines.truncated_subtract(&nines).decimal(), "0");
    }

    #[test]
    fn output_limit_checks_carries_and_actual_product_length() {
        let max = natural(&"9".repeat(MAX_DIGITS));
        let one = natural("1");
        let error = max.add(&one).unwrap_err();
        assert!(error.contains("natural arithmetic digit limit"));

        let nines = natural(&"9".repeat(MAX_DIGITS / 2));
        let error = nines
            .multiply(&natural(&"99".repeat(MAX_DIGITS / 2)))
            .unwrap_err();
        assert!(error.contains("natural arithmetic digit limit"));

        // Operand lengths sum to 4097, but the exact product has 4096 digits.
        let a = natural(&format!("1{}", "0".repeat(MAX_DIGITS / 2 - 1)));
        let b = natural(&format!("1{}", "0".repeat(MAX_DIGITS / 2)));
        let product = a.multiply(&b).unwrap();
        assert_eq!(
            product.decimal(),
            format!("1{}", "0".repeat(MAX_DIGITS - 1))
        );
        assert_eq!(product.decimal().len(), MAX_DIGITS);
    }

    #[test]
    fn zero_multiplication_is_canonical_even_at_maximum_operand_size() {
        let huge = natural(&"9".repeat(MAX_DIGITS));
        assert_eq!(natural("0").multiply(&huge).unwrap().decimal(), "0");
        assert_eq!(huge.multiply(&natural("0")).unwrap().decimal(), "0");
    }

    #[test]
    fn halving_matches_small_integer_reference() {
        for value in 0..10_000u128 {
            let (quotient, odd) = natural(&value.to_string()).halve();
            assert_eq!(quotient.decimal(), (value / 2).to_string());
            assert_eq!(odd, value % 2 != 0);
        }
        assert_eq!(natural("0").halve(), (natural("0"), false));
        assert_eq!(natural("1").halve(), (natural("0"), true));
    }

    #[test]
    fn halving_handles_powers_of_ten_and_values_above_u128() {
        for exponent in 1..=100 {
            let value = format!("1{}", "0".repeat(exponent));
            let expected = format!("5{}", "0".repeat(exponent - 1));
            assert_eq!(natural(&value).halve(), (natural(&expected), false));
        }

        let even = natural("340282366920938463463374607431768211456");
        assert_eq!(
            even.halve(),
            (natural("170141183460469231731687303715884105728"), false)
        );
        let odd = natural("340282366920938463463374607431768211457");
        assert_eq!(
            odd.halve(),
            (natural("170141183460469231731687303715884105728"), true)
        );
    }

    #[test]
    fn halving_maximum_length_nines_is_exact() {
        let nines = natural(&"9".repeat(MAX_DIGITS));
        let (quotient, odd) = nines.halve();
        assert_eq!(
            quotient.decimal(),
            format!("4{}", "9".repeat(MAX_DIGITS - 1))
        );
        assert!(odd);
    }

    #[test]
    fn repeated_halving_of_two_to_128_takes_exactly_128_steps() {
        let mut value = natural("340282366920938463463374607431768211456");
        let mut steps = 0;
        while value.decimal() != "1" {
            let (next, odd) = value.halve();
            assert!(!odd);
            value = next;
            steps += 1;
        }
        assert_eq!(steps, 128);
        assert_eq!(value.decimal(), "1");
        assert_eq!(value.halve(), (natural("0"), true));

        for original in [0u128, 1, 2, 3, 17, 255, 1024, 65_537, 1_000_000] {
            let mut current = natural(&original.to_string());
            let mut rebuilt = 0u128;
            let mut place = 1u128;
            while current.decimal() != "0" {
                let (next, odd) = current.halve();
                if odd {
                    rebuilt += place;
                }
                place *= 2;
                current = next;
            }
            assert_eq!(rebuilt, original);
        }
    }
}
