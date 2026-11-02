//! Acceleration of checked natural-number recursors, independent of names.
//!
//! A fold with a constant natural motive and affine step a*ih+b can be
//! evaluated with bounded exact arithmetic. Recognize nested affine folds after
//! beta/delta/zeta and constructor projections. Other motives,
//! unrecognized predecessor-dependent steps, opaque functions and nonlinear
//! steps keep the ordinary bounded iota evaluator. Exact predecessor folds
//! are handled separately, since truncated subtraction is not affine.
use super::*;

#[path = "natural_iteration.rs"]
mod iteration;
#[path = "natural_subtraction.rs"]
mod subtraction;

#[derive(Debug)]
struct Affine {
    coefficients: Vec<Natural>,
    constant: Natural,
}

impl Affine {
    fn is_constant(&self) -> bool {
        self.coefficients.iter().all(|n| n.decimal() == "0")
    }
    fn is_zero(&self) -> bool {
        self.is_constant() && self.constant.decimal() == "0"
    }
}

impl Kernel {
    /// Speculative arithmetic must not normalize an open term using an empty
    /// typing context. The affine recognizer instead refuses unknown locals.
    pub(super) fn natural_closed_number(
        &mut self,
        family: &str,
        value: &T,
        depth: usize,
    ) -> Result<Option<Natural>> {
        let Some(desc) = self.natural_recursor_family(family, depth + 1)? else {
            return Ok(None);
        };
        Ok(self
            .natural_affine(&desc, family, value, &[], depth + 1)?
            .map(|value| value.constant))
    }

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
            &[],
            depth + 1,
        )?
        else {
            return Ok(None);
        };
        debug_assert!(result.coefficients.is_empty());
        self.charge_transformation(128 + name.len() + result.constant.decimal().len())?;
        // Preserve the exact nominal family of the subject, not builtin Nat.
        Ok(Some(term(Term::NatLiteral {
            family: name.into(),
            value: result.constant,
        })))
    }

    /// Deliberately stop before recursor iota. Expanding an inner addition by
    /// a huge closed count would destroy the recurrence we need to recognize.
    pub(in crate::proof::kernel) fn natural_head(&mut self, value: &T, depth: usize) -> Result<T> {
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
                        if let Some(fused) =
                            self.natural_apply_fusion(&function, argument, depth + 1)?
                        {
                            value = fused;
                            continue;
                        }
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
                        if *index == 0 {
                            if let Some(fused) =
                                self.natural_project_fusion(family, &projected, depth + 1)?
                            {
                                value = fused;
                                continue;
                            }
                        }
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
                Term::Induct {
                    family,
                    levels,
                    parameters,
                    indices,
                    motive,
                    branches,
                    subject,
                } if levels.is_empty() && parameters.is_empty() && indices.is_empty() => {
                    let subject = self.natural_head(subject, depth + 1)?;
                    let subject = if matches!(subject.as_ref(), Term::NatLiteral { value, .. } if value.decimal() == "0")
                    {
                        self.natural_constructor(&subject, depth + 1)?
                    } else {
                        subject
                    };
                    let Term::Ctor {
                        family: actual,
                        levels,
                        parameters,
                        constructor,
                        fields,
                    } = subject.as_ref()
                    else {
                        return Ok(value);
                    };
                    if actual != family || !levels.is_empty() || !parameters.is_empty() {
                        return Ok(value);
                    }
                    let Some(desc) = self.natural_recursor_family(family, depth + 1)? else {
                        return Ok(value);
                    };
                    if branches.len() != 2 {
                        return Ok(value);
                    }
                    if constructor == &desc.constructors[0].name && fields.is_empty() {
                        value = branches[0].clone();
                    } else if constructor == &desc.constructors[1].name && fields.len() == 1 {
                        self.charge_transformation(384 + family.len())?;
                        let ih = term(Term::Induct {
                            family: family.clone(),
                            levels: vec![],
                            parameters: vec![],
                            indices: vec![],
                            motive: motive.clone(),
                            branches: branches.clone(),
                            subject: fields[0].clone(),
                        });
                        value = apps(branches[1].clone(), &[fields[0].clone(), ih]);
                    } else {
                        return Ok(value);
                    }
                }
                _ => return Ok(value),
            }
        }
    }

    pub(super) fn natural_type(&mut self, value: &T, family: &str, depth: usize) -> Result<bool> {
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
        variables: &[usize],
        depth: usize,
    ) -> Result<Option<Affine>> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        match value.as_ref() {
            Term::Var(index) => {
                let Some(position) = variables.iter().position(|variable| variable == index) else {
                    return Ok(None);
                };
                let mut affine = self.natural_affine_constant(
                    &Natural::parse("0")?,
                    variables.len(),
                    depth + 1,
                )?;
                affine.coefficients[position] = Natural::parse("1")?;
                Ok(Some(affine))
            }
            Term::NatLiteral {
                family: actual,
                value,
            } if actual == family => Ok(Some(self.natural_affine_constant(
                value,
                variables.len(),
                depth + 1,
            )?)),
            Term::Ctor {
                family: actual,
                levels,
                parameters,
                constructor,
                fields,
            } if actual == family && levels.is_empty() && parameters.is_empty() => {
                if constructor == &desc.constructors[0].name && fields.is_empty() {
                    Ok(Some(self.natural_affine_constant(
                        &Natural::parse("0")?,
                        variables.len(),
                        depth + 1,
                    )?))
                } else if constructor == &desc.constructors[1].name && fields.len() == 1 {
                    let Some(mut affine) =
                        self.natural_affine(desc, family, &fields[0], variables, depth + 1)?
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
                    variables,
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
                    variables,
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
        variables: &[usize],
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
        let Some(count) = self.natural_affine(desc, family, subject, variables, depth + 1)? else {
            return Ok(None);
        };
        // Iota at zero never executes the step. In particular, do not spend
        // a digit budget evaluating a well-typed but unused huge computation.
        if count.is_zero() {
            return self.natural_affine(desc, family, &branches[0], variables, depth + 1);
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
        // Introduce this accumulator and shift the already selected outer
        // variables past both binders. No predecessor enters the variable map.
        self.natural_arithmetic_budget(variables.len() + 1, 128 + variables.len() * 8, depth + 1)?;
        let mut inner = vec![0];
        inner.extend(variables.iter().map(|index| index + 2));
        let Some(mut step) = self.natural_affine(desc, family, body, &inner, depth + 1)? else {
            return self.natural_decreasing_fold(
                desc,
                family,
                body,
                &branches[0],
                &count,
                variables,
                depth + 1,
            );
        };
        let coefficient = step.coefficients.remove(0);
        // A positive reset fold discards its base. Its source still undergoes
        // full typing before conversion. Unknown counts may be zero.
        if coefficient.decimal() == "0" {
            return Ok(count.is_constant().then_some(step));
        }
        if coefficient.decimal() != "1" && !count.is_constant() {
            return Ok(None);
        }
        let translation = if coefficient.decimal() == "1" {
            let Some(product) = self.natural_affine_product(&count, &step, depth + 1)? else {
                return Ok(None);
            };
            Some(product)
        } else {
            None
        };
        let Some(base) = self.natural_affine(desc, family, &branches[0], variables, depth + 1)?
        else {
            return Ok(None);
        };
        match translation {
            Some(product) => Ok(Some(self.natural_affine_sum(&base, &product, depth + 1)?)),
            None => Ok(Some(self.natural_iterate(
                base,
                coefficient,
                step,
                count.constant,
                depth + 1,
            )?)),
        }
    }

    fn natural_affine_constant(
        &mut self,
        constant: &Natural,
        dimensions: usize,
        depth: usize,
    ) -> Result<Affine> {
        self.natural_arithmetic_budget(
            dimensions + 1,
            128 + constant.decimal().len() + dimensions * 128,
            depth + 1,
        )?;
        Ok(Affine {
            coefficients: vec![Natural::parse("0")?; dimensions],
            constant: constant.clone(),
        })
    }

    fn natural_affine_sum(&mut self, a: &Affine, b: &Affine, depth: usize) -> Result<Affine> {
        self.natural_arithmetic_budget(
            a.coefficients.len(),
            128 + a.coefficients.len() * 32,
            depth,
        )?;
        debug_assert_eq!(a.coefficients.len(), b.coefficients.len());
        let coefficients = a
            .coefficients
            .iter()
            .zip(&b.coefficients)
            .map(|(a, b)| self.natural_sum(a, b, depth + 1))
            .collect::<Result<Vec<_>>>()?;
        Ok(Affine {
            coefficients,
            constant: self.natural_sum(&a.constant, &b.constant, depth + 1)?,
        })
    }

    fn natural_affine_scale(
        &mut self,
        value: &Affine,
        factor: &Natural,
        depth: usize,
    ) -> Result<Affine> {
        self.natural_arithmetic_budget(
            value.coefficients.len(),
            128 + value.coefficients.len() * 32,
            depth,
        )?;
        let coefficients = value
            .coefficients
            .iter()
            .map(|value| self.natural_product(value, factor, depth + 1))
            .collect::<Result<Vec<_>>>()?;
        Ok(Affine {
            coefficients,
            constant: self.natural_product(&value.constant, factor, depth + 1)?,
        })
    }

    /// Naturals have no coefficient cancellation: two variable-dependent
    /// affine factors would create a genuinely nonlinear polynomial.
    fn natural_affine_product(
        &mut self,
        a: &Affine,
        b: &Affine,
        depth: usize,
    ) -> Result<Option<Affine>> {
        self.tick(depth)?;
        if a.is_constant() {
            Ok(Some(self.natural_affine_scale(
                b,
                &a.constant,
                depth + 1,
            )?))
        } else if b.is_constant() {
            Ok(Some(self.natural_affine_scale(
                a,
                &b.constant,
                depth + 1,
            )?))
        } else {
            Ok(None)
        }
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

    fn add(left: T, right: T) -> T {
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat(), nat())),
            branches: vec![
                left,
                term(Term::Lam(
                    nat(),
                    term(Term::Lam(
                        nat(),
                        constructor("succ", vec![term(Term::Var(0))]),
                    )),
                )),
            ],
            subject: right,
        })
    }
    fn multiply(kernel: &mut Kernel, left: T, right: T) -> T {
        let shifted = kernel.shift(&left, 2, 0, 0).unwrap();
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat(), nat())),
            branches: vec![
                literal(0),
                term(Term::Lam(
                    nat(),
                    term(Term::Lam(nat(), add(term(Term::Var(0)), shifted))),
                )),
            ],
            subject: right,
        })
    }

    #[test]
    fn nested_folds_track_each_selected_outer_variable_without_capture() {
        let mut kernel = Kernel::new();
        let left = multiply(&mut kernel, literal(3), term(Term::Var(3)));
        let right = multiply(&mut kernel, term(Term::Var(0)), literal(2));
        let value = add(left, right);
        kernel
            .check(&[nat(), nat(), nat(), nat()], &value, &nat(), 0)
            .unwrap();
        let family = kernel.natural_family("#pt-nat", 0).unwrap();
        let result = kernel
            .natural_affine(&family, "#pt-nat", &value, &[3, 0], 0)
            .unwrap()
            .unwrap();
        assert_eq!(
            result
                .coefficients
                .iter()
                .map(Natural::decimal)
                .collect::<Vec<_>>(),
            ["3", "2"]
        );
        assert_eq!(result.constant.decimal(), "0");
        assert!(kernel
            .natural_affine(&family, "#pt-nat", &term(Term::Var(1)), &[3, 0], 0)
            .unwrap()
            .is_none());
    }

    #[test]
    fn products_of_two_variable_factors_are_not_mistaken_for_affine_values() {
        let mut kernel = Kernel::new();
        let family = kernel.natural_family("#pt-nat", 0).unwrap();
        for right in [term(Term::Var(0)), term(Term::Var(1))] {
            kernel.reset_budget();
            let value = multiply(&mut kernel, term(Term::Var(0)), right);
            kernel.check(&[nat(), nat()], &value, &nat(), 0).unwrap();
            assert!(kernel
                .natural_affine(&family, "#pt-nat", &value, &[0, 1], 0)
                .unwrap()
                .is_none());
        }
    }

    #[test]
    fn affine_payload_accounting_includes_owned_digits_and_variable_slots() {
        let mut kernel = Kernel::new();
        let value = Natural::parse(&"9".repeat(4096)).unwrap();
        let bytes = 128 + 4096 + 2 * 128;
        kernel.transformed_bytes = 64 * 1024 * 1024 - bytes;
        let affine = kernel.natural_affine_constant(&value, 2, 0).unwrap();
        assert_eq!(affine.constant, value);
        assert_eq!(affine.coefficients.len(), 2);
        assert_eq!(kernel.transformed_bytes, 64 * 1024 * 1024);
        assert!(kernel
            .natural_affine_constant(&value, 2, 0)
            .unwrap_err()
            .contains("allocation limit"));
    }
}
