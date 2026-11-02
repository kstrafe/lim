use super::Natural;

impl Natural {
    /// Computes Euclidean quotient and remainder using exact decimal arithmetic.
    ///
    /// Callers must budget digit work and allocations before calling. Division
    /// keeps one bounded remainder buffer and performs at most nine in-place
    /// subtractions for each dividend digit.
    pub(super) fn divide_remainder(&self, divisor: &Self) -> (Self, Self) {
        if divisor.0 == "0" {
            return (Self("0".into()), self.clone());
        }

        let divisor_digits = divisor.0.as_bytes();
        let mut quotient = Vec::with_capacity(self.0.len());
        let mut remainder = Vec::with_capacity(divisor_digits.len() + 1);

        for &digit in self.0.as_bytes() {
            if remainder == b"0" {
                remainder.clear();
            }
            remainder.push(digit);

            let mut quotient_digit = 0u8;
            while decimal_cmp(&remainder, divisor_digits) != std::cmp::Ordering::Less {
                subtract_in_place(&mut remainder, divisor_digits);
                quotient_digit += 1;
            }
            quotient.push(b'0' + quotient_digit);
        }

        let first = quotient.iter().position(|&digit| digit != b'0');
        let quotient = match first {
            Some(first) => quotient.split_off(first),
            None => vec![b'0'],
        };
        (
            Self(String::from_utf8(quotient).expect("decimal quotient")),
            Self(String::from_utf8(remainder).expect("decimal remainder")),
        )
    }
}

fn decimal_cmp(left: &[u8], right: &[u8]) -> std::cmp::Ordering {
    left.len().cmp(&right.len()).then_with(|| left.cmp(right))
}

/// Subtracts `right` from a known-larger-or-equal canonical decimal in place.
fn subtract_in_place(left: &mut Vec<u8>, right: &[u8]) {
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
        left[i] = b'0' + digit as u8;
    }

    let first = left
        .iter()
        .position(|&digit| digit != b'0')
        .unwrap_or(left.len() - 1);
    if first > 0 {
        left.copy_within(first.., 0);
        left.truncate(left.len() - first);
    }
}

#[cfg(test)]
mod tests {
    use super::super::MAX_DIGITS;
    use super::*;

    fn natural(value: &str) -> Natural {
        Natural::parse(value).unwrap()
    }

    fn check_reconstruction(dividend: &Natural, divisor: &Natural) {
        let (quotient, remainder) = dividend.divide_remainder(divisor);
        let reconstructed = quotient.multiply(divisor).unwrap().add(&remainder).unwrap();
        assert_eq!(reconstructed, *dividend);
        assert!(
            remainder.decimal() == "0"
                || decimal_cmp(remainder.0.as_bytes(), divisor.0.as_bytes()).is_lt()
        );
    }

    #[test]
    fn division_matches_deterministic_small_integer_references() {
        for a in 0..=128u128 {
            for b in 0..=32u128 {
                let (q, r) = natural(&a.to_string()).divide_remainder(&natural(&b.to_string()));
                let expected_q = if b == 0 { 0 } else { a / b };
                let expected_r = if b == 0 { a } else { a % b };
                assert_eq!(q.decimal(), expected_q.to_string());
                assert_eq!(r.decimal(), expected_r.to_string());
            }
        }

        let mut state = 0x9e3779b97f4a7c15u128;
        for _ in 0..512 {
            state = state
                .wrapping_mul(0xda942042e4dd58b5)
                .wrapping_add(0x94d049bb133111eb);
            let a = state;
            state = state.rotate_left(37).wrapping_add(0x2545f4914f6cdd1d);
            let b = state % 1_000_000_007 + 1;
            let (q, r) = natural(&a.to_string()).divide_remainder(&natural(&b.to_string()));
            assert_eq!(q.decimal(), (a / b).to_string());
            assert_eq!(r.decimal(), (a % b).to_string());
        }
    }

    #[test]
    fn division_handles_binary_boundaries_and_large_decimal_identity() {
        let two_128 = natural("340282366920938463463374607431768211456");
        let two_64 = natural("18446744073709551616");
        assert_eq!(
            two_128.divide_remainder(&two_64),
            (two_64.clone(), natural("0"))
        );
        assert_eq!(
            natural("340282366920938463463374607431768211455").divide_remainder(&two_64),
            (
                natural("18446744073709551615"),
                natural("18446744073709551615")
            )
        );

        let dividend = natural(&format!("{}", "9".repeat(200)));
        let divisor = natural(&format!("1{}1", "0".repeat(99)));
        assert_eq!(
            dividend.divide_remainder(&divisor),
            (natural(&format!("{}", "9".repeat(100))), natural("0"))
        );
    }

    #[test]
    fn maximum_length_division_and_large_reconstruction_are_exact() {
        let dividend = natural(&format!("1{}", "0".repeat(MAX_DIGITS - 1)));
        assert_eq!(
            dividend.divide_remainder(&natural("9")),
            (natural(&"1".repeat(MAX_DIGITS - 1)), natural("1"))
        );

        let dividend = natural(&format!("{}7", "8".repeat(900)));
        let divisor = natural(&format!("{}3", "7".repeat(450)));
        check_reconstruction(&dividend, &divisor);
    }

    #[test]
    fn zero_divisor_returns_zero_and_the_original_dividend() {
        let dividend = natural(&"8".repeat(MAX_DIGITS));
        assert_eq!(
            dividend.divide_remainder(&natural("0")),
            (natural("0"), dividend)
        );
    }
}
