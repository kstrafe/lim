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

    /// Observations have a closed scalar type, or Nat -> scalar type. Scalars
    /// are this natural family or a completed finite Type-0 data family. A
    /// motive depending on its index cannot silently become a constant type.
    fn natural_observation_type(
        &mut self,
        value: &T,
        family: &str,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        if let Some(scalar) = self.natural_scalar_type(value, family, depth + 1)? {
            return Ok(Some(scalar));
        }
        let value = self.natural_head(value, depth + 1)?;
        if let Term::Pi(domain, range) = value.as_ref() {
            if self.natural_type(domain, family, depth + 1)? {
                if let Some(scalar) = self.natural_scalar_type(range, family, depth + 1)? {
                    self.charge_transformation(384 + family.len())?;
                    return Ok(Some(term(Term::Pi(
                        term(Term::Global(family.into(), vec![])),
                        scalar,
                    ))));
                }
            }
        }
        Ok(None)
    }

    fn natural_scalar_type(&mut self, value: &T, family: &str, depth: usize) -> Result<Option<T>> {
        self.tick(depth)?;
        if self.natural_type(value, family, depth + 1)? {
            self.charge_transformation(128 + family.len())?;
            return Ok(Some(term(Term::Global(family.into(), vec![]))));
        }
        let value = self.natural_head(value, depth + 1)?;
        let Term::Global(name, levels) = value.as_ref() else {
            return Ok(None);
        };
        if !levels.is_empty() || self.provisional_family(name) || self.nested.contains_key(name) {
            return Ok(None);
        }
        let Some(declaration) = self.declarations.get(name) else {
            return Ok(None);
        };
        let Some(desc) = &declaration.family else {
            return Ok(None);
        };
        if !declaration.universes.is_empty()
            || desc.group.len() != 1
            || desc.group[0] != *name
            || !desc.parameters.is_empty()
            || !desc.indices.is_empty()
            || desc
                .constructors
                .iter()
                .any(|constructor| !constructor.fields.is_empty())
            || !desc.sort.equivalent(&Level::number(1)?)?
        {
            return Ok(None);
        }
        Ok(Some(value))
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
        if !self.natural_type(domain, family, depth + 1)? {
            return self.natural_case_apply_fusion(
                family,
                &result,
                branches,
                subject,
                argument,
                depth + 1,
            );
        }
        if !self.natural_type(range, family, depth + 1)? {
            let Some(ty) = self.natural_observation_type(&result, family, depth + 1)? else {
                return Ok(None);
            };
            return self.natural_comparison_fold(
                family,
                &ty,
                branches,
                subject,
                argument,
                depth + 1,
            );
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

    /// Applying a fixed argument also commutes with a nonrecursive natural
    /// case, even if the argument is a history record. Require an index-free
    /// function domain, a closed scalar range, and no use of the old function
    /// anywhere in the step body, including its annotations and erased values.
    #[expect(clippy::too_many_arguments)]
    fn natural_case_apply_fusion(
        &mut self,
        family: &str,
        ty: &T,
        branches: &[T],
        subject: &T,
        argument: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let Term::Pi(domain, range) = ty.as_ref() else {
            return Ok(None);
        };
        if self.natural_without_variable(domain, depth + 1)?.is_none() {
            return Ok(None);
        }
        let Some(range) = self.natural_scalar_type(range, family, depth + 1)? else {
            return Ok(None);
        };
        let step = self.natural_head(&branches[1], depth + 1)?;
        let Term::Lam(domain, body) = step.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let step = self.natural_head(body, depth + 1)?;
        let Term::Lam(_, body) = step.as_ref() else {
            return Ok(None);
        };
        let Some(body) = self.natural_without_variable(body, depth + 1)? else {
            return Ok(None);
        };
        let argument_under_step = self.shift(argument, 2, 0, depth + 1)?;
        self.charge_transformation(1024 + family.len() * 3)?;
        let nat = term(Term::Global(family.into(), vec![]));
        Ok(Some(term(Term::Induct {
            family: family.into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat.clone(), range.clone())),
            branches: vec![
                term(Term::App(branches[0].clone(), argument.clone())),
                term(Term::Lam(
                    nat,
                    term(Term::Lam(
                        range,
                        term(Term::App(body.clone(), argument_under_step)),
                    )),
                )),
            ],
            subject: subject.clone(),
        })))
    }

    /// Erase only checked definitional redexes before testing for a local.
    /// Return the rewritten term: reusing the original could retain that
    /// local in a discarded argument or type after changing the binder type.
    fn natural_without_variable(&mut self, value: &T, depth: usize) -> Result<Option<T>> {
        // Syntactic absence already proves independence. Only normalize when
        // a local actually occurs, retaining the rewritten body if it erases.
        if !self.uses_bound_variable(value, depth + 1)? {
            return Ok(Some(value.clone()));
        }
        let mut found = false;
        let value = self.transform_nodes(
            value,
            0,
            depth + 1,
            &mut |kernel, value, binders, depth| {
                if found {
                    return Ok(ControlFlow::Break(value.clone()));
                }
                let value = kernel.natural_head(value, depth + 1)?;
                if matches!(value.as_ref(), Term::Var(index) if *index == binders) {
                    found = true;
                    return Ok(ControlFlow::Break(value));
                }
                Ok(ControlFlow::Continue(value))
            },
            &mut |_, index, _| Ok(term(Term::Var(index))),
            &mut |level| Ok(level.clone()),
        )?;
        Ok((!found).then_some(value))
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

    fn record_case(count: T, body: T) -> T {
        let ty = term(Term::Pi(pair_type(), nat()));
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), ty.clone()),
            branches: vec![lam(pair_type(), literal(0)), lam(nat(), lam(ty, body))],
            subject: count,
        })
    }

    #[test]
    fn nonrecursive_case_application_uses_the_rewritten_body_after_erasing_a_local() {
        let mut kernel = kernel();
        let ty = term(Term::Pi(pair_type(), nat()));
        let body = term(Term::Let(ty.clone(), var(0), lam(pair_type(), literal(0))));
        let fold = record_case(literal(1000), body);
        kernel.check(&[], &fold, &ty, 0).unwrap();
        let value = pair(literal(7), literal(8));
        let fused = kernel
            .natural_apply_fusion(&fold, &value, 0)
            .unwrap()
            .unwrap();
        kernel.check(&[], &fused, &nat(), 0).unwrap();
        assert!(kernel.convertible(&[], &fused, &literal(0), 0).unwrap());
        // Before source typing, the same erased local with a false annotation
        // must still fail. Conversion is not permission to skip that check.
        let bad = record_case(
            literal(1000),
            term(Term::Let(nat(), var(0), lam(pair_type(), literal(0)))),
        );
        assert!(kernel
            .check(&[], &bad, &ty, 0)
            .unwrap_err()
            .contains("type mismatch"));
    }

    #[test]
    fn a_record_case_that_uses_the_old_function_is_not_nonrecursive() {
        let mut kernel = kernel();
        let fold = record_case(
            literal(3),
            lam(pair_type(), term(Term::App(var(1), var(0)))),
        );
        let ty = term(Term::Pi(pair_type(), nat()));
        kernel.check(&[], &fold, &ty, 0).unwrap();
        assert!(kernel
            .natural_apply_fusion(&fold, &pair(literal(1), literal(2)), 0)
            .unwrap()
            .is_none());
    }

    #[test]
    fn a_case_function_domain_cannot_depend_on_its_recursion_index() {
        let mut kernel = kernel();
        kernel
            .inductive(
                "Indexed",
                vec![],
                vec![nat()],
                Level::number(1).unwrap(),
                vec![("make".into(), vec![])],
            )
            .unwrap();
        let indexed = |n: T| term(Term::App(term(Term::Global("Indexed".into(), vec![])), n));
        let ty = |n: T| term(Term::Pi(indexed(n), nat()));
        let fold = term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), ty(var(0))),
            branches: vec![
                lam(indexed(literal(0)), literal(0)),
                lam(
                    nat(),
                    lam(ty(var(0)), lam(indexed(successor(var(1))), literal(0))),
                ),
            ],
            subject: literal(3),
        });
        kernel.check(&[], &fold, &ty(literal(3)), 0).unwrap();
        let argument = term(Term::Ctor {
            family: "Indexed".into(),
            levels: vec![],
            parameters: vec![literal(3)],
            constructor: "make".into(),
            fields: vec![],
        });
        assert!(kernel
            .natural_apply_fusion(&fold, &argument, 0)
            .unwrap()
            .is_none());
    }

    #[test]
    fn finite_observations_are_nominal_completed_data_and_never_propositions() {
        let mut kernel = kernel();
        kernel
            .inductive(
                "Flag",
                vec![],
                vec![],
                Level::number(1).unwrap(),
                vec![("off".into(), vec![]), ("on".into(), vec![])],
            )
            .unwrap();
        kernel
            .inductive(
                "Proof",
                vec![],
                vec![],
                Level::number(0).unwrap(),
                vec![("witness".into(), vec![])],
            )
            .unwrap();
        let flag = term(Term::Global("Flag".into(), vec![]));
        assert!(kernel
            .natural_observation_type(&flag, "#pt-nat", 0)
            .unwrap()
            .is_some());
        assert!(kernel
            .natural_observation_type(&term(Term::Pi(nat(), flag)), "#pt-nat", 0)
            .unwrap()
            .is_some());
        assert!(kernel
            .natural_observation_type(&term(Term::Global("Proof".into(), vec![])), "#pt-nat", 0)
            .unwrap()
            .is_none());
        assert!(kernel
            .natural_observation_type(&pair_type(), "#pt-nat", 0)
            .unwrap()
            .is_none());
        assert!(kernel
            .natural_observation_type(&var(0), "#pt-nat", 0)
            .unwrap()
            .is_none());
    }

    #[test]
    fn syntactically_independent_bodies_are_kept_without_unfolding() {
        let mut kernel = kernel();
        let body = lam(nat(), term(Term::Let(nat(), literal(7), var(0))));
        kernel
            .definition("kept-body", vec![], function(), body, false)
            .unwrap();
        let value = term(Term::Global("kept-body".into(), vec![]));
        let kept = kernel.natural_without_variable(&value, 0).unwrap().unwrap();
        assert!(Arc::ptr_eq(&value, &kept));
        // A binding's occurrence in a type still prevents raw independence.
        assert!(kernel
            .natural_without_variable(&lam(var(0), literal(0)), 0)
            .unwrap()
            .is_none());
    }
}
