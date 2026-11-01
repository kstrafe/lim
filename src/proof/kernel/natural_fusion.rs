//! Checked observational fusion for natural recursors.
//!
//! Projecting the first record field commutes with a fold only if its step
//! observes the previous state exclusively through that same projection.
//! Applying a fixed argument commutes only when every use of the old function
//! applies that exact argument. Neither rule depends on declaration names.
use super::*;

impl Kernel {
    pub(super) fn natural_project_fusion(
        &mut self,
        record: &str,
        value: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let Term::Induct {
            family,
            levels,
            parameters,
            indices,
            motive,
            branches,
            subject,
        } = value.as_ref()
        else {
            return Ok(None);
        };
        if !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || branches.len() != 2
        {
            return Ok(None);
        }
        if self.natural_recursor_family(family, depth + 1)?.is_none() {
            return Ok(None);
        }
        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, body) = motive.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let shape = self.natural_head(body, depth + 1)?;
        let Some((actual, record_levels, arguments, desc)) = self.record_type(&shape, depth + 1)?
        else {
            return Ok(None);
        };
        if actual != record
            || arguments.is_empty()
            || desc.constructors[0].fields.is_empty()
            || !matches!(desc.constructors[0].fields[0].as_ref(), Term::Var(index) if *index == arguments.len() - 1)
        {
            return Ok(None);
        }
        let (_, map) = self.family(record, &record_levels, depth + 1)?;
        if !desc
            .sort
            .substitute(&map)?
            .zero_implies_zero(&Level::number(1)?)?
        {
            return Ok(None);
        }
        let Some(observed_type) =
            self.natural_observation_type(&arguments[0], family, depth + 1)?
        else {
            return Ok(None);
        };
        let constructor = &desc.constructors[0];
        let step = self.natural_head(&branches[1], depth + 1)?;
        let Term::Lam(domain, rest) = step.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let rest = self.natural_head(rest, depth + 1)?;
        let Term::Lam(_, body) = rest.as_ref() else {
            return Ok(None);
        };
        let body = self.natural_head(body, depth + 1)?;
        let Term::Ctor {
            family: step_family,
            constructor: step_constructor,
            fields: step_fields,
            ..
        } = body.as_ref()
        else {
            return Ok(None);
        };
        if step_family != record
            || step_constructor != &constructor.name
            || step_fields.len() != constructor.fields.len()
        {
            return Ok(None);
        }
        let mut refused = false;
        let observed = self.transform_nodes(
            &step_fields[0],
            0,
            depth + 1,
            &mut |kernel, value, binders, depth| {
                if refused {
                    return Ok(ControlFlow::Break(value.clone()));
                }
                let value = kernel.natural_head(value, depth + 1)?;
                if let Term::Project {
                    family,
                    index: 0,
                    subject,
                } = value.as_ref()
                {
                    if family == record
                        && matches!(subject.as_ref(), Term::Var(index) if *index == binders)
                    {
                        return Ok(ControlFlow::Break(term(Term::Var(binders))));
                    }
                }
                if matches!(value.as_ref(), Term::Var(index) if *index == binders) {
                    refused = true;
                    return Ok(ControlFlow::Break(value));
                }
                Ok(ControlFlow::Continue(value))
            },
            &mut |_, index, _| Ok(term(Term::Var(index))),
            &mut |level| Ok(level.clone()),
        )?;
        if refused {
            return Ok(None);
        }
        let nat = term(Term::Global(family.clone(), vec![]));
        self.charge_transformation(1152 + record.len() + family.len() * 3)?;
        Ok(Some(term(Term::Induct {
            family: family.clone(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat.clone(), observed_type.clone())),
            branches: vec![
                term(Term::Project {
                    family: record.into(),
                    index: 0,
                    subject: branches[0].clone(),
                }),
                term(Term::Lam(nat, term(Term::Lam(observed_type, observed)))),
            ],
            subject: subject.clone(),
        })))
    }

    /// Only a constant Nat or Nat -> Nat observation is handled. A source
    /// motive depending on its index cannot silently become a constant type.
    fn natural_observation_type(
        &mut self,
        value: &T,
        family: &str,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let nat = term(Term::Global(family.into(), vec![]));
        if self.natural_type(value, family, depth + 1)? {
            return Ok(Some(nat));
        }
        let value = self.natural_head(value, depth + 1)?;
        if let Term::Pi(domain, range) = value.as_ref() {
            if self.natural_type(domain, family, depth + 1)?
                && self.natural_type(range, family, depth + 1)?
            {
                self.charge_transformation(384 + family.len() * 2)?;
                return Ok(Some(term(Term::Pi(nat.clone(), nat))));
            }
        }
        Ok(None)
    }

    pub(super) fn natural_apply_fusion(
        &mut self,
        value: &T,
        argument: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let Term::Induct {
            family,
            levels,
            parameters,
            indices,
            motive,
            branches,
            subject,
        } = value.as_ref()
        else {
            return Ok(None);
        };
        if !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || branches.len() != 2
        {
            return Ok(None);
        }
        if self.natural_recursor_family(family, depth + 1)?.is_none() {
            return Ok(None);
        }
        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, result) = motive.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let result = self.natural_head(result, depth + 1)?;
        let Term::Pi(domain, range) = result.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)?
            || !self.natural_type(range, family, depth + 1)?
        {
            return Ok(None);
        }
        let step = self.natural_head(&branches[1], depth + 1)?;
        let Term::Lam(domain, rest) = step.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let rest = self.natural_head(rest, depth + 1)?;
        let Term::Lam(domain, body) = rest.as_ref() else {
            return Ok(None);
        };
        if self
            .natural_observation_type(domain, family, depth + 1)?
            .is_none_or(|ty| !matches!(ty.as_ref(), Term::Pi(..)))
        {
            return Ok(None);
        }
        let shifted_argument = self.shift(argument, 2, 0, depth + 1)?;
        self.charge_transformation(128)?;
        let body = term(Term::App(body.clone(), shifted_argument));
        let mut refused = false;
        let specialized = self.transform_nodes(
            &body,
            0,
            depth + 1,
            &mut |kernel, value, binders, depth| {
                if refused {
                    return Ok(ControlFlow::Break(value.clone()));
                }
                let value = kernel.natural_head(value, depth + 1)?;
                if let Term::App(function, actual_argument) = value.as_ref() {
                    if matches!(function.as_ref(), Term::Var(index) if *index == binders) {
                        let expected = kernel.shift(argument, binders + 2, 0, depth + 1)?;
                        let same = if kernel.same_syntax(&expected, actual_argument)? {
                            true
                        } else {
                            let expected = kernel.natural_head(&expected, depth + 1)?;
                            let actual = kernel.natural_head(actual_argument, depth + 1)?;
                            kernel.same_syntax(&expected, &actual)?
                        };
                        if same {
                            return Ok(ControlFlow::Break(term(Term::Var(binders))));
                        }
                    }
                }
                if matches!(value.as_ref(), Term::Var(index) if *index == binders) {
                    refused = true;
                    return Ok(ControlFlow::Break(value));
                }
                Ok(ControlFlow::Continue(value))
            },
            &mut |_, index, _| Ok(term(Term::Var(index))),
            &mut |level| Ok(level.clone()),
        )?;
        if refused {
            return Ok(None);
        }
        let nat = term(Term::Global(family.clone(), vec![]));
        self.charge_transformation(1024 + family.len() * 4)?;
        Ok(Some(term(Term::Induct {
            family: family.clone(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat.clone(), nat.clone())),
            branches: vec![
                term(Term::App(branches[0].clone(), argument.clone())),
                term(Term::Lam(nat.clone(), term(Term::Lam(nat, specialized)))),
            ],
            subject: subject.clone(),
        })))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat() -> T {
        term(Term::Global("#pt-nat".into(), vec![]))
    }
    fn var(index: usize) -> T {
        term(Term::Var(index))
    }
    fn lam(domain: T, body: T) -> T {
        term(Term::Lam(domain, body))
    }
    fn function() -> T {
        term(Term::Pi(nat(), nat()))
    }
    fn literal(value: usize) -> T {
        term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse(&value.to_string()).unwrap(),
        })
    }
    fn successor(value: T) -> T {
        term(Term::Ctor {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            constructor: "succ".into(),
            fields: vec![value],
        })
    }
    fn unary(value: usize) -> T {
        (0..value).fold(
            term(Term::Ctor {
                family: "#pt-nat".into(),
                levels: vec![],
                parameters: vec![],
                constructor: "zero".into(),
                fields: vec![],
            }),
            |n, _| successor(n),
        )
    }
    fn project(index: usize, value: T) -> T {
        term(Term::Project {
            family: "Pair".into(),
            index,
            subject: value,
        })
    }
    fn pair_type() -> T {
        apps(term(Term::Global("Pair".into(), vec![])), &[nat(), nat()])
    }
    fn pair(first: T, second: T) -> T {
        term(Term::Ctor {
            family: "Pair".into(),
            levels: vec![],
            parameters: vec![nat(), nat()],
            constructor: "make".into(),
            fields: vec![first, second],
        })
    }
    fn kernel() -> Kernel {
        let mut kernel = Kernel::new();
        kernel
            .inductive(
                "Pair",
                vec![],
                vec![term(Term::Sort(Level::number(1).unwrap())); 2],
                Level::number(1).unwrap(),
                vec![("make".into(), vec![var(1), var(1)])],
            )
            .unwrap();
        kernel.reset_budget();
        kernel
    }
    fn record_fold(base: T, count: T, history: bool) -> T {
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), pair_type()),
            branches: vec![
                pair(base, literal(0)),
                lam(
                    nat(),
                    lam(
                        pair_type(),
                        pair(
                            successor(project(usize::from(history), var(0))),
                            successor(project(1, var(0))),
                        ),
                    ),
                ),
            ],
            subject: count,
        })
    }
    fn function_fold(count: T, changed: bool) -> T {
        let argument = if changed { successor(var(0)) } else { var(0) };
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), function()),
            branches: vec![
                lam(nat(), var(0)),
                lam(
                    nat(),
                    lam(
                        function(),
                        lam(nat(), successor(term(Term::App(var(1), argument)))),
                    ),
                ),
            ],
            subject: count,
        })
    }

    #[test]
    fn first_field_fusion_preserves_types_and_matches_unbatched_iota() {
        let mut kernel = kernel();
        for base in 0..=3 {
            for count in 0..=3 {
                kernel.reset_budget();
                let fast = project(0, record_fold(literal(base), literal(count), false));
                let slow = project(0, record_fold(literal(base), unary(count), false));
                kernel.check(&[], &fast, &nat(), 0).unwrap();
                kernel.check(&[], &slow, &nat(), 0).unwrap();
                let fused = kernel.natural_head(&fast, 0).unwrap();
                kernel.check(&[], &fused, &nat(), 0).unwrap();
                assert!(kernel.convertible(&[], &fast, &slow, 0).unwrap());
                assert!(kernel
                    .convertible(&[], &fast, &literal(base + count), 0)
                    .unwrap());
            }
        }
    }

    #[test]
    fn fixed_argument_fusion_preserves_types_and_matches_unbatched_iota() {
        let mut kernel = kernel();
        for argument in 0..=3 {
            for count in 0..=3 {
                kernel.reset_budget();
                let fast = term(Term::App(
                    function_fold(literal(count), false),
                    literal(argument),
                ));
                let slow = term(Term::App(
                    function_fold(unary(count), false),
                    literal(argument),
                ));
                kernel.check(&[], &fast, &nat(), 0).unwrap();
                kernel.check(&[], &slow, &nat(), 0).unwrap();
                let fused = kernel.natural_head(&fast, 0).unwrap();
                kernel.check(&[], &fused, &nat(), 0).unwrap();
                assert!(kernel.convertible(&[], &fast, &slow, 0).unwrap());
                assert!(kernel
                    .convertible(&[], &fast, &literal(argument + count), 0)
                    .unwrap());
            }
        }
    }

    #[test]
    fn reading_a_different_history_field_is_not_the_observed_recurrence() {
        let mut kernel = kernel();
        let fold = record_fold(literal(42), literal(3), true);
        let value = project(0, fold.clone());
        kernel.check(&[], &value, &nat(), 0).unwrap();
        assert!(kernel
            .natural_project_fusion("Pair", &fold, 0)
            .unwrap()
            .is_none());
        assert!(kernel.convertible(&[], &value, &literal(3), 0).unwrap());
        assert!(!kernel.convertible(&[], &value, &literal(45), 0).unwrap());
    }

    #[test]
    fn a_recursive_call_at_another_argument_is_not_a_fixed_argument_fold() {
        let mut kernel = kernel();
        let fold = function_fold(literal(3), true);
        let value = term(Term::App(fold.clone(), literal(2)));
        kernel.check(&[], &value, &nat(), 0).unwrap();
        assert!(kernel
            .natural_apply_fusion(&fold, &literal(2), 0)
            .unwrap()
            .is_none());
        assert!(kernel.convertible(&[], &value, &literal(8), 0).unwrap());
        assert!(!kernel.convertible(&[], &value, &literal(5), 0).unwrap());
    }

    #[test]
    fn fixed_outer_arguments_and_bases_do_not_capture_recursion_binders() {
        let mut kernel = kernel();
        let context = [nat()];
        for value in [
            project(0, record_fold(var(0), literal(3), false)),
            term(Term::App(function_fold(literal(3), false), var(0))),
        ] {
            kernel.reset_budget();
            kernel.check(&context, &value, &nat(), 0).unwrap();
            let fused = kernel.natural_head(&value, 0).unwrap();
            kernel.check(&context, &fused, &nat(), 0).unwrap();
            let expected = successor(successor(successor(var(0))));
            assert!(kernel.convertible(&context, &value, &expected, 0).unwrap());
        }
    }
}
