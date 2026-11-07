//! Compact canonical naturals, with only checked zero/successor semantics.
use super::*;

#[path = "natural_arithmetic.rs"]
mod arithmetic;
#[path = "natural_comparison.rs"]
mod comparison;
#[path = "delayed.rs"]
mod delayed;
#[path = "natural_division_arithmetic.rs"]
mod division_arithmetic;
#[path = "natural_euclidean.rs"]
mod euclidean;
use euclidean::EuclideanModel;
#[path = "natural_fold.rs"]
mod fold;
#[path = "natural_fusion.rs"]
mod fusion;
#[path = "natural_probe.rs"]
mod probe;

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
        if self.provisional_family(name) || self.nested.contains_key(name)? {
            return Err("natural literal requires a completed natural-number family".into());
        }
        let (family, _) = self.family(name, &[], depth + 1)?;
        if !natural_shape(name, &family)? {
            return Err("natural literal requires a parameterless Type-0 family with zero and successor constructors".into());
        }
        Ok(family)
    }

    /// Speculative normalization must leave other checked inductives alone.
    pub(super) fn natural_recursor_family(
        &mut self,
        name: &str,
        depth: usize,
    ) -> Result<Option<Family>> {
        self.tick(depth)?;
        if self.provisional_family(name) || self.nested.contains_key(name)? {
            return Ok(None);
        }
        let Some(declaration) = self.declarations.get(name)? else {
            return Ok(None);
        };
        if !declaration.universes.is_empty() {
            return Ok(None);
        }
        let Some(family) = &declaration.family else {
            return Ok(None);
        };
        Ok(natural_shape(name, family)?.then(|| family.clone()))
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

pub(super) fn natural_shape(name: &str, family: &Family) -> Result<bool> {
    Ok(family.group == [name]
        && family.parameters.is_empty()
        && family.indices.is_empty()
        && family.sort.equivalent(&Level::number(1)?)?
        && family.constructors.len() == 2
        && family.constructors[0].fields.is_empty()
        && family.constructors[0].result_indices.is_empty()
        && family.constructors[1].fields.len() == 1
        && family.constructors[1].result_indices.is_empty()
        && matches!(family.constructors[1].fields[0].as_ref(),Term::Global(actual,levels) if actual == name && levels.is_empty()))
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
    fn sharing_a_compact_leaf_avoids_a_copy_but_new_payloads_still_pay() {
        let mut kernel = Kernel::new();
        let value = term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse(&"9".repeat(MAX_DIGITS)).unwrap(),
        });
        kernel.transformed_bytes = 64 * 1024 * 1024;
        let shared = kernel.shift(&value, 1, 0, 0).unwrap();
        assert!(Arc::ptr_eq(&value, &shared));
        assert_eq!(kernel.transformed_bytes, 64 * 1024 * 1024);
        let why = kernel.natural_constructor(&value, 0).unwrap_err();
        assert!(why.contains("allocation limit"), "{why}");
    }
}
