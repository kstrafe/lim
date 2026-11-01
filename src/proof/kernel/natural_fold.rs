//! Acceleration of checked natural-number recursors, independent of names.
//!
//! A fold with a constant natural motive, base b, and step ih + k computes
//! b + n*k. Recognize that syntax (including nested translation folds) after
//! beta/delta/zeta and constructor projections. Other motives,
//! predecessor-dependent steps, opaque functions and nonlinear steps keep the
//! ordinary bounded iota evaluator.
use super::*;

struct Affine {
    coefficient: Natural,
    constant: Natural,
}

impl Kernel {
    /// All source terms still pass ordinary inference before conversion. This
    /// does not make an unchecked body, annotation or erased let acceptable.
    #[expect(clippy::too_many_arguments)]
    pub(in crate::proof::kernel) fn natural_fold(
        &mut self,
        name: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        cases: &[RecursionCase],
        subject: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let Term::NatLiteral { family, .. } = subject.as_ref() else {
            return Ok(None);
        };
        if family != name
            || !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || cases.len() != 1
            || cases[0].family != name
        {
            return Ok(None);
        }
        let desc = self.natural_family(name, depth + 1)?;
        let Some(result) = self.natural_affine_fold(
            &desc,
            name,
            &cases[0].motive,
            &cases[0].branches,
            subject,
            None,
            depth + 1,
        )?
        else {
            return Ok(None);
        };
        debug_assert_eq!(result.coefficient.decimal(), "0");
        self.charge_transformation(128 + name.len() + result.constant.decimal().len())?;
        // Preserve the exact nominal family of the subject, not builtin Nat.
        Ok(Some(term(Term::NatLiteral {
            family: name.into(),
            value: result.constant,
        })))
    }

    /// Deliberately stop before recursor iota. Expanding an inner addition by
    /// a huge closed count would destroy the recurrence we need to recognize.
    fn natural_head(&mut self, value: &T, depth: usize) -> Result<T> {
        self.tick(depth)?;
        let mut value = value.clone();
        loop {
            self.tick(depth)?;
            match value.as_ref() {
                Term::Global(name, levels) => {
                    let (decl, map) = self.specialization(name, levels, depth + 1)?;
                    let Some(body) = decl.value else {
                        return Ok(value);
                    };
                    value = self.universes(&body, &map, depth + 1)?;
                }
                Term::App(function, argument) => {
                    let function = self.natural_head(function, depth + 1)?;
                    let Term::Lam(_, body) = function.as_ref() else {
                        return Ok(value);
                    };
                    value = self.instantiate(body, argument, depth + 1)?;
                }
                Term::Let(_, definition, body) => {
                    value = self.instantiate(body, definition, depth + 1)?;
                }
                Term::Project {
                    family,
                    index,
                    subject,
                } => {
                    let projected = self.natural_head(subject, depth + 1)?;
                    let Term::Ctor {
                        family: actual,
                        fields,
                        ..
                    } = projected.as_ref()
                    else {
                        return Ok(value);
                    };
                    if actual != family {
                        return Ok(value);
                    }
                    value = fields
                        .get(*index)
                        .cloned()
                        .ok_or("invalid record field index")?;
                }
                Term::First(pair) | Term::Second(pair) => {
                    let pair = self.natural_head(pair, depth + 1)?;
                    let Term::Pair(_, first, second) = pair.as_ref() else {
                        return Ok(value);
                    };
                    value = if matches!(value.as_ref(), Term::First(_)) {
                        first.clone()
                    } else {
                        second.clone()
                    };
                }
                _ => return Ok(value),
            }
        }
    }

    fn natural_type(&mut self, value: &T, family: &str, depth: usize) -> Result<bool> {
        let value = self.natural_head(value, depth + 1)?;
        Ok(
            matches!(value.as_ref(), Term::Global(name, levels) if name == family && levels.is_empty()),
        )
    }

    fn natural_affine(
        &mut self,
        desc: &Family,
        family: &str,
        value: &T,
        variable: Option<usize>,
        depth: usize,
    ) -> Result<Option<Affine>> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        match value.as_ref() {
            Term::Var(index) if Some(*index) == variable => Ok(Some(Affine {
                coefficient: Natural::parse("1")?,
                constant: Natural::parse("0")?,
            })),
            Term::NatLiteral {
                family: actual,
                value,
            } if actual == family => {
                self.charge_transformation(128 + value.decimal().len())?;
                Ok(Some(Affine {
                    coefficient: Natural::parse("0")?,
                    constant: value.clone(),
                }))
            }
            Term::Ctor {
                family: actual,
                levels,
                parameters,
                constructor,
                fields,
            } if actual == family && levels.is_empty() && parameters.is_empty() => {
                if constructor == &desc.constructors[0].name && fields.is_empty() {
                    Ok(Some(Affine {
                        coefficient: Natural::parse("0")?,
                        constant: Natural::parse("0")?,
                    }))
                } else if constructor == &desc.constructors[1].name && fields.len() == 1 {
                    let Some(mut affine) =
                        self.natural_affine(desc, family, &fields[0], variable, depth + 1)?
                    else {
                        return Ok(None);
                    };
                    affine.constant =
                        self.natural_sum(&affine.constant, &Natural::parse("1")?, depth + 1)?;
                    Ok(Some(affine))
                } else {
                    Ok(None)
                }
            }
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
                self.natural_affine_fold(
                    desc,
                    family,
                    motive,
                    branches,
                    subject,
                    variable,
                    depth + 1,
                )
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
                self.natural_affine_fold(
                    desc,
                    family,
                    &cases[0].motive,
                    &cases[0].branches,
                    subject,
                    variable,
                    depth + 1,
                )
            }
            _ => Ok(None),
        }
    }

    #[expect(clippy::too_many_arguments)]
    fn natural_affine_fold(
        &mut self,
        desc: &Family,
        family: &str,
        motive: &T,
        branches: &[T],
        subject: &T,
        variable: Option<usize>,
        depth: usize,
    ) -> Result<Option<Affine>> {
        self.tick(depth)?;
        if branches.len() != 2 {
            return Ok(None);
        }
        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, codomain) = motive.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)?
            || !self.natural_type(codomain, family, depth + 1)?
        {
            return Ok(None);
        }
        let Some(count) = self.natural_affine(desc, family, subject, variable, depth + 1)? else {
            return Ok(None);
        };
        // Iota at zero never executes the step. In particular, do not spend
        // a digit budget evaluating a well-typed but unused huge computation.
        if count.coefficient.decimal() == "0" && count.constant.decimal() == "0" {
            return self.natural_affine(desc, family, &branches[0], variable, depth + 1);
        }
        let step = self.natural_head(&branches[1], depth + 1)?;
        let Term::Lam(domain, body) = step.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let step = self.natural_head(body, depth + 1)?;
        let Term::Lam(domain, body) = step.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        // Only the innermost accumulator is admitted. The predecessor and
        // every free outer variable are intentionally absent from this scope.
        let Some(step) = self.natural_affine(desc, family, body, Some(0), depth + 1)? else {
            return Ok(None);
        };
        if step.coefficient.decimal() != "1" {
            return Ok(None);
        }
        // A nontranslation step can ignore the base entirely. Only evaluate
        // it once the translation shape has established that it is needed.
        let Some(base) = self.natural_affine(desc, family, &branches[0], variable, depth + 1)?
        else {
            return Ok(None);
        };
        let coefficient = self.natural_product(&count.coefficient, &step.constant, depth + 1)?;
        let constant = self.natural_product(&count.constant, &step.constant, depth + 1)?;
        Ok(Some(Affine {
            coefficient: self.natural_sum(&base.coefficient, &coefficient, depth + 1)?,
            constant: self.natural_sum(&base.constant, &constant, depth + 1)?,
        }))
    }

    fn natural_arithmetic_budget(&mut self, work: usize, bytes: usize, depth: usize) -> Result<()> {
        self.work = self.work.saturating_add(work);
        self.tick(depth)?;
        self.charge_transformation(bytes)
    }

    fn natural_sum(&mut self, a: &Natural, b: &Natural, depth: usize) -> Result<Natural> {
        let digits = a.decimal().len().max(b.decimal().len()) + 1;
        self.natural_arithmetic_budget(digits, 256 + digits, depth + 1)?;
        a.add(b)
    }

    fn natural_product(&mut self, a: &Natural, b: &Natural, depth: usize) -> Result<Natural> {
        let (work, digits) = if a.decimal() == "0" || b.decimal() == "0" {
            (1, 1)
        } else {
            (
                a.decimal().len().saturating_mul(b.decimal().len()),
                a.decimal().len() + b.decimal().len(),
            )
        };
        self.natural_arithmetic_budget(work, 256 + digits * 2, depth + 1)?;
        a.multiply(b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat() -> T {
        term(Term::Global("#pt-nat".into(), vec![]))
    }
    fn literal(value: usize) -> T {
        term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse(&value.to_string()).unwrap(),
        })
    }
    fn constructor(name: &str, fields: Vec<T>) -> T {
        term(Term::Ctor {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            constructor: name.into(),
            fields,
        })
    }
    fn unary(value: usize) -> T {
        (0..value).fold(constructor("zero", vec![]), |previous, _| {
            constructor("succ", vec![previous])
        })
    }
    fn fold(base: usize, increment: usize, subject: T) -> T {
        let step = (0..increment).fold(term(Term::Var(0)), |previous, _| {
            constructor("succ", vec![previous])
        });
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat(), nat())),
            branches: vec![
                literal(base),
                term(Term::Lam(nat(), term(Term::Lam(nat(), step)))),
            ],
            subject,
        })
    }

    #[test]
    fn accelerated_values_agree_with_actual_unbatched_iota_reduction() {
        let mut kernel = Kernel::new();
        for base in 0..=3 {
            for increment in 0..=3 {
                for count in 0..=6 {
                    kernel.reset_budget();
                    let fast = fold(base, increment, literal(count));
                    let slow = fold(base, increment, unary(count));
                    kernel.check(&[], &fast, &nat(), 0).unwrap();
                    kernel.check(&[], &slow, &nat(), 0).unwrap();
                    let fast = kernel.whnf(&[], &fast, 0).unwrap();
                    assert!(
                        matches!(fast.as_ref(), Term::NatLiteral { value, .. } if value.decimal() == (base + increment * count).to_string())
                    );
                    // The slow input has no compact literal anywhere on its
                    // constructor spine, so every recursion step uses iota.
                    assert!(kernel.convertible(&[], &fast, &slow, 0).unwrap());
                }
            }
        }
    }

    #[test]
    fn arithmetic_charges_work_and_allocation_before_computing() {
        let mut kernel = Kernel::new();
        let a = Natural::parse("12345").unwrap();
        kernel.work = WORK - 24;
        assert!(kernel
            .natural_product(&a, &a, 0)
            .unwrap_err()
            .contains("resource limit"));
        kernel.reset_budget();
        kernel.transformed_bytes = 64 * 1024 * 1024 - 1;
        assert!(kernel
            .natural_sum(&a, &a, 0)
            .unwrap_err()
            .contains("allocation limit"));
        kernel.reset_budget();
        assert_eq!(
            kernel.natural_product(&a, &a, 0).unwrap().decimal(),
            "152399025"
        );
    }
}
