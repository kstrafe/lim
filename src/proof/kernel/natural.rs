//! Compact canonical naturals, with only checked zero/successor semantics.
use super::*;

#[path = "natural_arithmetic.rs"]
mod arithmetic;
#[path = "natural_fold.rs"]
mod fold;

pub(in crate::proof::kernel) const MAX_DIGITS: usize = 4096;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::proof::kernel) struct Natural(String);

impl Natural {
    pub(in crate::proof::kernel) fn parse(decimal: &str) -> Result<Self> {
        if decimal.len() > MAX_DIGITS {
            return Err("natural literal digit limit exceeded (4096)".into());
        }
        if decimal.is_empty()
            || !decimal.bytes().all(|digit| digit.is_ascii_digit())
            || decimal.len() > 1 && decimal.starts_with('0')
        {
            return Err("natural literals require a canonical unsigned decimal string".into());
        }
        Ok(Self(decimal.into()))
    }

    pub(in crate::proof::kernel) fn decimal(&self) -> &str {
        &self.0
    }

    fn predecessor(&self) -> Option<Self> {
        if self.0 == "0" {
            return None;
        }
        let mut digits = self.0.as_bytes().to_vec();
        for digit in digits.iter_mut().rev() {
            if *digit != b'0' {
                *digit -= 1;
                break;
            }
            *digit = b'9';
        }
        if digits.len() > 1 && digits[0] == b'0' {
            digits.remove(0);
        }
        // Input and every edited byte are ASCII decimal digits.
        Some(Self(
            String::from_utf8(digits).expect("decimal predecessor"),
        ))
    }
}

impl Kernel {
    /// A numeral abbreviates constructors of this exact nominal family. No
    /// theorem or alias can make an arbitrary datatype into natural numbers.
    pub(super) fn natural_family(&mut self, name: &str, depth: usize) -> Result<Family> {
        self.tick(depth)?;
        if self.provisional_family(name) || self.nested.contains_key(name) {
            return Err("natural literal requires a completed natural-number family".into());
        }
        let (family, _) = self.family(name, &[], depth + 1)?;
        if family.group != [name]
            || !family.parameters.is_empty()
            || !family.indices.is_empty()
            || !family.sort.equivalent(&Level::number(1)?)?
            || family.constructors.len() != 2
            || !family.constructors[0].fields.is_empty()
            || !family.constructors[0].result_indices.is_empty()
            || family.constructors[1].fields.len() != 1
            || !family.constructors[1].result_indices.is_empty()
            || !matches!(family.constructors[1].fields[0].as_ref(),Term::Global(actual,levels) if actual == name && levels.is_empty())
        {
            return Err("natural literal requires a parameterless Type-0 family with zero and successor constructors".into());
        }
        Ok(family)
    }

    /// Expose one constructor only when induction/conversion needs it. General
    /// normalization keeps the compact value rather than expanding its magnitude.
    pub(super) fn natural_constructor(&mut self, value: &T, depth: usize) -> Result<T> {
        let Term::NatLiteral {
            family,
            value: number,
        } = value.as_ref()
        else {
            return Ok(value.clone());
        };
        let desc = self.natural_family(family, depth + 1)?;
        self.charge_transformation(
            256usize
                .saturating_add(family.len().saturating_mul(2))
                .saturating_add(number.decimal().len()),
        )?;
        let (ordinal, fields) = match number.predecessor() {
            None => (0, vec![]),
            Some(value) => (
                1,
                vec![term(Term::NatLiteral {
                    family: family.clone(),
                    value,
                })],
            ),
        };
        self.charge_transformation(desc.constructors[ordinal].name.len())?;
        Ok(term(Term::Ctor {
            family: family.clone(),
            levels: vec![],
            parameters: vec![],
            constructor: desc.constructors[ordinal].name.clone(),
            fields,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_predecessors_handle_borrows_without_machine_integer_limits() {
        for (value, previous) in [
            ("0", None),
            ("1", Some("0")),
            ("9", Some("8")),
            ("10", Some("9")),
            ("1000", Some("999")),
            ("184467440737095516160", Some("184467440737095516159")),
        ] {
            assert_eq!(
                Natural::parse(value)
                    .unwrap()
                    .predecessor()
                    .as_ref()
                    .map(Natural::decimal),
                previous
            );
        }
        let value = format!("1{}", "0".repeat(MAX_DIGITS - 1));
        assert_eq!(
            Natural::parse(&value)
                .unwrap()
                .predecessor()
                .unwrap()
                .decimal(),
            "9".repeat(MAX_DIGITS - 1)
        );
        for number in 0..=10000u64 {
            assert_eq!(
                Natural::parse(&number.to_string())
                    .unwrap()
                    .predecessor()
                    .map(|n| n.decimal().to_owned()),
                number.checked_sub(1).map(|n| n.to_string())
            );
        }
    }

    #[test]
    fn noncanonical_and_oversized_naturals_are_rejected_before_allocation() {
        for value in ["", "00", "01", "-1", "+1", " 1", "1_000", "１", "1.0"] {
            assert!(Natural::parse(value).is_err(), "{value}");
        }
        assert!(Natural::parse(&"9".repeat(MAX_DIGITS)).is_ok());
        assert!(Natural::parse(&"9".repeat(MAX_DIGITS + 1))
            .unwrap_err()
            .contains("digit limit"));
    }

    #[test]
    fn transformations_charge_the_full_compact_decimal_payload() {
        let mut kernel = Kernel::new();
        let value = term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse(&"9".repeat(MAX_DIGITS)).unwrap(),
        });
        let bytes = 128 + "#pt-nat".len() + MAX_DIGITS;
        kernel.transformed_bytes = 64 * 1024 * 1024 - bytes;
        kernel.shift(&value, 1, 0, 0).unwrap();
        assert_eq!(kernel.transformed_bytes, 64 * 1024 * 1024);
        let why = kernel.shift(&value, 1, 0, 0).unwrap_err();
        assert!(why.contains("allocation limit"), "{why}");
    }
}
