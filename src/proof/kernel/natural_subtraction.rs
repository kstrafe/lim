//! Exact conversion for a checked predecessor and repeated predecessors.
use super::*;

impl Kernel {
    #[expect(clippy::too_many_arguments)]
    pub(super) fn natural_decreasing_fold(
        &mut self,
        desc: &Family,
        family: &str,
        step: &T,
        base: &T,
        count: &Affine,
        variables: &[usize],
        depth: usize,
    ) -> Result<Option<Affine>> {
        self.tick(depth)?;
        // Truncated subtraction of an unknown variable is piecewise, not
        // affine. In particular, never substitute zero for a selected local.
        if !count.is_constant() {
            return Ok(None);
        }
        let predecessor = matches!(step.as_ref(), Term::Var(1));
        if !predecessor {
            let Some(subject) = self.natural_predecessor_subject(family, step, depth + 1)? else {
                return Ok(None);
            };
            // Both outer branch binders are still in scope: 0 is the
            // accumulator, 1 is its predecessor, and 2+ are outer locals.
            if !matches!(subject.as_ref(), Term::Var(0)) {
                return Ok(None);
            }
        }
        let Some(base) = self.natural_affine(desc, family, base, variables, depth + 1)? else {
            return Ok(None);
        };
        if !base.is_constant() || (predecessor && !base.is_zero()) {
            return Ok(None);
        }
        let one = Natural::parse("1")?;
        let (left, right) = if predecessor {
            (&count.constant, &one)
        } else {
            (&base.constant, &count.constant)
        };
        let value = self.natural_difference(left, right, depth + 1)?;
        Ok(Some(self.natural_affine_constant(
            &value,
            variables.len(),
            depth + 1,
        )?))
    }

    fn natural_difference(
        &mut self,
        left: &Natural,
        right: &Natural,
        depth: usize,
    ) -> Result<Natural> {
        self.natural_arithmetic_budget(
            left.decimal().len().max(right.decimal().len()),
            256 + left.decimal().len() + right.decimal().len(),
            depth + 1,
        )?;
        Ok(left.truncated_subtract(right))
    }

    /// The exact zero/successor recursor, with constant natural motive,
    /// zero base, and successor branch returning its predecessor. Source
    /// inference still checks all domains, branches, lets and ignored terms.
    pub(in crate::proof::kernel) fn natural_predecessor_subject(
        &mut self,
        family: &str,
        value: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        let (motive, branches, subject) = match value.as_ref() {
            Term::Induct {
                family: actual,
                levels,
                parameters,
                indices,
                motive,
                branches,
                subject,
            } if actual == family
                && levels.is_empty()
                && parameters.is_empty()
                && indices.is_empty() =>
            {
                (motive, branches, subject)
            }
            Term::MutualInduct {
                family: actual,
                levels,
                parameters,
                indices,
                cases,
                subject,
            } if actual == family
                && levels.is_empty()
                && parameters.is_empty()
                && indices.is_empty()
                && cases.len() == 1
                && cases[0].family == family =>
            {
                (&cases[0].motive, &cases[0].branches, subject)
            }
            _ => return Ok(None),
        };
        if branches.len() != 2 {
            return Ok(None);
        }
        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, range) = motive.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)?
            || !self.natural_type(range, family, depth + 1)?
        {
            return Ok(None);
        }
        let base = self.natural_head(&branches[0], depth + 1)?;
        let zero = matches!(base.as_ref(), Term::NatLiteral { family: actual, value }
            if actual == family && value.decimal() == "0")
            || matches!(base.as_ref(), Term::Ctor { family: actual, levels, parameters,
                constructor, fields }
                if actual == family && levels.is_empty() && parameters.is_empty()
                    && fields.is_empty()
                    && self.natural_family(family, depth + 1)?.constructors[0].name == *constructor);
        if !zero {
            return Ok(None);
        }
        let branch = self.natural_head(&branches[1], depth + 1)?;
        let Term::Lam(domain, body) = branch.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let branch = self.natural_head(body, depth + 1)?;
        let Term::Lam(domain, body) = branch.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let body = self.natural_head(body, depth + 1)?;
        if !matches!(body.as_ref(), Term::Var(1)) {
            return Ok(None);
        }
        Ok(Some(self.natural_head(subject, depth + 1)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat() -> T {
        term(Term::Global("#pt-nat".into(), vec![]))
    }
    fn literal(n: usize) -> T {
        term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse(&n.to_string()).unwrap(),
        })
    }
    fn unary(n: usize) -> T {
        let mut value = term(Term::Ctor {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            constructor: "zero".into(),
            fields: vec![],
        });
        for _ in 0..n {
            value = term(Term::Ctor {
                family: "#pt-nat".into(),
                levels: vec![],
                parameters: vec![],
                constructor: "succ".into(),
                fields: vec![value],
            });
        }
        value
    }
    fn fold(base: T, step: T, count: T) -> T {
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat(), nat())),
            branches: vec![base, term(Term::Lam(nat(), term(Term::Lam(nat(), step))))],
            subject: count,
        })
    }
    fn predecessor(value: T) -> T {
        fold(unary(0), term(Term::Var(1)), value)
    }

    #[test]
    fn decreasing_folds_match_unbatched_constructor_iota_and_integer_reference() {
        let mut kernel = Kernel::new();
        for base in 0..=5usize {
            for count in 0..=5 {
                kernel.reset_budget();
                let fast = fold(
                    literal(base),
                    predecessor(term(Term::Var(0))),
                    literal(count),
                );
                let slow = fold(unary(base), predecessor(term(Term::Var(0))), unary(count));
                kernel.check(&[], &fast, &nat(), 0).unwrap();
                kernel.check(&[], &slow, &nat(), 0).unwrap();
                let result = kernel.whnf(&[], &fast, 0).unwrap();
                assert!(
                    matches!(result.as_ref(), Term::NatLiteral { value, .. } if value.decimal() == base.saturating_sub(count).to_string())
                );
                assert!(kernel.convertible(&[], &result, &slow, 0).unwrap());
            }
        }
    }

    #[test]
    fn subtracting_does_not_capture_a_predecessor_or_an_outer_variable() {
        let mut kernel = Kernel::new();
        let desc = kernel.natural_family("#pt-nat", 0).unwrap();
        let count = Affine {
            coefficients: vec![],
            constant: Natural::parse("1000").unwrap(),
        };
        for slot in [1, 2, 3] {
            kernel.reset_budget();
            assert!(kernel
                .natural_decreasing_fold(
                    &desc,
                    "#pt-nat",
                    &predecessor(term(Term::Var(slot))),
                    &literal(7),
                    &count,
                    &[],
                    0
                )
                .unwrap()
                .is_none());
        }
    }

    #[test]
    fn difference_charges_work_and_payload_before_allocating() {
        let mut kernel = Kernel::new();
        let large = Natural::parse(&"9".repeat(4096)).unwrap();
        kernel.work = WORK - 4096;
        assert!(kernel
            .natural_difference(&large, &large, 0)
            .unwrap_err()
            .contains("resource limit"));
        kernel.reset_budget();
        kernel.transformed_bytes = 64 * 1024 * 1024 - 256 - 4096 * 2;
        assert_eq!(
            kernel
                .natural_difference(&large, &large, 0)
                .unwrap()
                .decimal(),
            "0"
        );
        assert!(kernel
            .natural_difference(&large, &large, 0)
            .unwrap_err()
            .contains("allocation limit"));
    }
}
