//! Binary iteration of a checked constant-affine natural recurrence.
use super::*;

impl Kernel {
    pub(super) fn natural_iterate(
        &mut self,
        mut value: Affine,
        mut coefficient: Natural,
        mut offset: Affine,
        mut count: Natural,
        depth: usize,
    ) -> Result<Affine> {
        self.tick(depth)?;
        // Avoid constructing an enormous power when every result stays zero.
        if value.is_zero() && offset.is_zero() {
            return Ok(value);
        }
        while count.decimal() != "0" {
            self.tick(depth)?;
            self.natural_arithmetic_budget(
                count.decimal().len(),
                128 + count.decimal().len(),
                depth + 1,
            )?;
            let (remaining, odd) = count.halve();
            if odd {
                let scaled = self.natural_affine_scale(&value, &coefficient, depth + 1)?;
                value = self.natural_affine_sum(&scaled, &offset, depth + 1)?;
            }
            if remaining.decimal() == "0" {
                break;
            }
            // (a*x+b) composed with itself is a*a*x + (a*b+b).
            // Do not square after the last bit: that power is never used.
            let scaled = self.natural_affine_scale(&offset, &coefficient, depth + 1)?;
            offset = self.natural_affine_sum(&scaled, &offset, depth + 1)?;
            coefficient = self.natural_product(&coefficient, &coefficient, depth + 1)?;
            count = remaining;
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn number(n: u128) -> Natural {
        Natural::parse(&n.to_string()).unwrap()
    }
    fn scalar(n: u128) -> Affine {
        Affine {
            coefficients: vec![],
            constant: number(n),
        }
    }

    #[test]
    fn binary_composition_matches_independent_repeated_iteration() {
        let mut kernel = Kernel::new();
        for a in 0..=4u128 {
            for b in 0..=3u128 {
                for initial in 0..=3u128 {
                    for count in 0..=7u128 {
                        kernel.reset_budget();
                        let mut expected = initial;
                        for _ in 0..count {
                            expected = a * expected + b;
                        }
                        let result = kernel
                            .natural_iterate(
                                scalar(initial),
                                number(a),
                                scalar(b),
                                number(count),
                                0,
                            )
                            .unwrap();
                        assert!(result.coefficients.is_empty());
                        assert_eq!(result.constant.decimal(), expected.to_string());
                    }
                }
            }
        }
    }

    #[test]
    fn outer_affine_offsets_remain_distinct_from_the_accumulator() {
        let mut kernel = Kernel::new();
        let initial = Affine {
            coefficients: vec![number(1)],
            constant: number(7),
        };
        let offset = Affine {
            coefficients: vec![number(3)],
            constant: number(2),
        };
        let result = kernel
            .natural_iterate(initial, number(2), offset, number(5), 0)
            .unwrap();
        assert_eq!(result.coefficients[0].decimal(), "125");
        assert_eq!(result.constant.decimal(), "286");
        for x in 0..=30u128 {
            let mut expected = x + 7;
            for _ in 0..5 {
                expected = 2 * expected + 3 * x + 2;
            }
            assert_eq!(125 * x + 286, expected);
        }
    }

    #[test]
    fn the_last_unused_square_and_zero_fixed_point_are_not_computed() {
        let mut kernel = Kernel::new();
        let huge = Natural::parse(&"9".repeat(4096)).unwrap();
        let result = kernel
            .natural_iterate(scalar(1), huge.clone(), scalar(0), number(1), 0)
            .unwrap();
        assert_eq!(result.constant, huge);
        kernel.reset_budget();
        let result = kernel
            .natural_iterate(scalar(0), number(3), scalar(0), huge, 0)
            .unwrap();
        assert!(result.is_zero());
    }

    #[test]
    fn iteration_preserves_digit_work_and_allocation_limits() {
        let mut kernel = Kernel::new();
        let huge = Affine {
            coefficients: vec![],
            constant: Natural::parse(&"9".repeat(4096)).unwrap(),
        };
        assert!(kernel
            .natural_iterate(huge, number(2), scalar(0), number(1), 0)
            .unwrap_err()
            .contains("digit limit"));
        kernel.reset_budget();
        kernel.work = WORK - 2;
        assert!(kernel
            .natural_iterate(scalar(1), number(2), scalar(1), number(128), 0)
            .unwrap_err()
            .contains("resource limit"));
        kernel.reset_budget();
        kernel.transformed_bytes = 64 * 1024 * 1024 - 1;
        assert!(kernel
            .natural_iterate(scalar(1), number(2), scalar(1), number(128), 0)
            .unwrap_err()
            .contains("allocation limit"));
    }
}
