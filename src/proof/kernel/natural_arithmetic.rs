use super::{Natural, Result, MAX_DIGITS};

impl Natural {
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
        let nines = natural(&"9".repeat(1000));
        assert_eq!(
            nines.multiply(&nines).unwrap().decimal(),
            format!("{}8{}1", "9".repeat(999), "0".repeat(999))
        );
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
}
