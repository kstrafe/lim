//! Simultaneous substitution for consecutive, already checked lambda binders.
use super::*;

#[cfg(test)]
#[path = "explicit_beta_tests.rs"]
mod explicit_tests;

impl Kernel {
    pub(super) fn natural_beta_spine(&mut self, value: &T, depth: usize) -> Result<Option<T>> {
        self.beta_spine(value, true, depth)
    }

    pub(super) fn explicit_beta_spine(&mut self, value: &T, depth: usize) -> Result<Option<T>> {
        self.beta_spine(value, false, depth)
    }

    fn beta_spine(&mut self, value: &T, delta: bool, depth: usize) -> Result<Option<T>> {
        let mut head = value;
        let mut count = 0;
        while let Term::App(function, _) = head.as_ref() {
            count += 1;
            self.tick(depth + count)?;
            head = function;
        }
        let body = match head.as_ref() {
            Term::Lam(..) => Some(head.clone()),
            Term::Global(name, _) if delta => {
                self.declarations.get(name)?.and_then(|d| d.value.clone())
            }
            _ => None,
        };
        if count < 2
            || !matches!(body.as_ref().map(T::as_ref), Some(Term::Lam(_, body)) if matches!(body.as_ref(), Term::Lam(..)))
        {
            return Ok(None);
        }
        self.charge_transformation(count * 32)?;
        let mut arguments = Vec::with_capacity(count);
        let mut cursor = value;
        while let Term::App(function, argument) = cursor.as_ref() {
            self.tick(depth)?;
            arguments.push(argument.clone());
            cursor = function;
        }
        arguments.reverse();
        let mut body = if delta {
            self.natural_head(head, depth + count)?
        } else {
            head.clone()
        };
        let mut consumed = 0;
        while consumed < count {
            let Term::Lam(_, next) = body.as_ref() else {
                break;
            };
            body = next.clone();
            consumed += 1;
        }
        if consumed < 2 {
            return Ok(None);
        }
        // Preserve the deepest body position of the first ordinary beta
        // substitution. Argument walks use the maximum original shift depth.
        let result = self.instantiate_many(
            &body,
            &arguments[..consumed],
            depth + count + consumed - 1,
            depth + count + 1,
        )?;
        self.charge_transformation((count - consumed) * 128)?;
        Ok(Some(apps(result, &arguments[consumed..])))
    }

    fn instantiate_many(
        &mut self,
        body: &T,
        arguments: &[T],
        depth: usize,
        argument_depth: usize,
    ) -> Result<T> {
        let mut shifted = HashMap::<(usize, usize), T>::new();
        self.charge_transformation(128 + arguments.len())?;
        let mut invariant = vec![false; arguments.len()];
        self.transform(
            body,
            0,
            depth,
            &mut |kernel, index, binders| {
                if index >= binders && index - binders < arguments.len() {
                    let argument = arguments.len() - 1 - (index - binders);
                    if invariant[argument] {
                        return Ok(arguments[argument].clone());
                    }
                    let key = (argument, binders);
                    if let Some(value) = shifted.get(&key) {
                        return Ok(value.clone());
                    }
                    let (value, unchanged) = kernel.beta_shift_argument(
                        &arguments[argument],
                        binders,
                        argument_depth,
                    )?;
                    kernel.charge_transformation(256)?;
                    if unchanged {
                        invariant[argument] = true;
                    } else {
                        shifted.insert(key, value.clone());
                    }
                    Ok(value)
                } else {
                    Ok(term(Term::Var(if index >= binders {
                        index - arguments.len()
                    } else {
                        index
                    })))
                }
            },
            &mut |level| Ok(level.clone()),
        )
    }

    /// A zero shift is identity, without establishing that a compound term is
    /// closed. Discover invariance during a needed nonzero shift by inspecting
    /// every annotation and bound-variable scope. Universe variables are
    /// unaffected. Reuse remains local to this argument and substitution batch.
    fn beta_shift_argument(&mut self, value: &T, amount: usize, depth: usize) -> Result<(T, bool)> {
        if amount == 0 {
            self.tick(depth)?;
            // An identity shift proves nothing about free variables in a
            // compound argument. Only these leaves are known invariant.
            let invariant = matches!(
                value.as_ref(),
                Term::Sort(_) | Term::Global(..) | Term::NatLiteral { .. }
            );
            return Ok((value.clone(), invariant));
        }
        let mut invariant = true;
        let shifted = self.transform(
            value,
            0,
            depth,
            &mut |_, index, binders| {
                let index = if index >= binders {
                    invariant = false;
                    index.checked_add(amount).ok_or("variable index overflow")?
                } else {
                    index
                };
                Ok(term(Term::Var(index)))
            },
            &mut |level| Ok(level.clone()),
        )?;
        Ok((if invariant { value.clone() } else { shifted }, invariant))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(i: usize) -> T {
        term(Term::Var(i))
    }
    fn nat() -> T {
        term(Term::Global("#pt-nat".into(), vec![]))
    }
    fn number(n: usize) -> T {
        term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse(&n.to_string()).unwrap(),
        })
    }
    fn lam(a: T, b: T) -> T {
        term(Term::Lam(a, b))
    }
    fn app(a: T, b: T) -> T {
        term(Term::App(a, b))
    }
    fn pi(a: T, b: T) -> T {
        term(Term::Pi(a, b))
    }
    fn sequential(kernel: &mut Kernel, body: &T, arguments: &[T]) -> T {
        let mut value = body.clone();
        for _ in arguments {
            value = lam(nat(), value);
        }
        for argument in arguments {
            let Term::Lam(_, body) = value.as_ref() else {
                panic!("missing lambda")
            };
            value = kernel.instantiate(body, argument, 0).unwrap();
        }
        value
    }

    #[test]
    fn simultaneous_substitution_matches_sequential_beta_across_binder_scopes() {
        for count in 0..=4 {
            let arguments = (0..count)
                .map(|i| match i % 3 {
                    0 => var(i),
                    1 => lam(nat(), var(i + 1)),
                    _ => app(var(i), var(i + 1)),
                })
                .collect::<Vec<_>>();
            let mut bodies = (0..count + 3).map(var).collect::<Vec<_>>();
            bodies.extend([
                app(var(0), var(count)),
                lam(var(0), app(var(1), var(count + 1))),
                term(Term::Let(var(0), var(count), app(var(0), var(count + 1)))),
                term(Term::Sigma(var(0), app(var(1), var(count + 1)))),
                term(Term::Eq(var(0), var(count), var(count + 1))),
            ]);
            for body in bodies {
                let mut kernel = Kernel::new();
                let expected = sequential(&mut kernel, &body, &arguments);
                kernel.reset_budget();
                let actual = kernel.instantiate_many(&body, &arguments, 0, 1).unwrap();
                assert!(
                    kernel.same_syntax(&actual, &expected).unwrap(),
                    "count {count}"
                );
            }
        }
    }

    #[test]
    fn argument_order_sharing_and_capture_are_preserved() {
        let mut kernel = Kernel::new();
        let body = app(var(0), app(var(1), var(0)));
        let result = kernel
            .instantiate_many(&body, &[var(8), var(9)], 0, 1)
            .unwrap();
        let Term::App(first, rest) = result.as_ref() else {
            panic!("application")
        };
        let Term::App(second, third) = rest.as_ref() else {
            panic!("application")
        };
        assert!(matches!(first.as_ref(), Term::Var(9)));
        assert!(matches!(second.as_ref(), Term::Var(8)));
        assert!(Arc::ptr_eq(first, third));
        let body = lam(nat(), app(var(0), var(2)));
        let actual = kernel
            .instantiate_many(&body, &[var(0), var(1)], 0, 1)
            .unwrap();
        assert!(kernel
            .same_syntax(&actual, &lam(nat(), app(var(0), var(1))))
            .unwrap());
    }

    #[test]
    fn invariant_arguments_are_shared_at_distinct_binder_depths() {
        let mut kernel = Kernel::new();
        let argument = lam(nat(), var(0));
        let body = app(var(0), lam(nat(), var(1)));
        let result = kernel
            .instantiate_many(&body, &[number(0), argument.clone()], 0, 1)
            .unwrap();
        let Term::App(first, second) = result.as_ref() else {
            panic!("application")
        };
        let Term::Lam(_, under_binder) = second.as_ref() else {
            panic!("lambda")
        };
        assert!(Arc::ptr_eq(first, &argument));
        assert!(Arc::ptr_eq(under_binder, &argument));
    }

    #[test]
    fn a_free_variable_in_an_annotation_still_requires_shifting() {
        let mut kernel = Kernel::new();
        let argument = lam(var(0), var(0));
        let body = app(var(0), lam(nat(), var(1)));
        let result = kernel
            .instantiate_many(&body, &[number(0), argument], 0, 1)
            .unwrap();
        let expected = app(lam(var(0), var(0)), lam(nat(), lam(var(1), var(0))));
        assert!(kernel.same_syntax(&result, &expected).unwrap());
    }

    #[test]
    fn discovering_invariance_keeps_depth_overflow_and_universe_payloads() {
        let mut kernel = Kernel::new();
        assert!(kernel
            .beta_shift_argument(&lam(nat(), var(0)), 1, DEPTH)
            .unwrap_err()
            .contains("resource limit"));
        kernel.reset_budget();
        assert!(kernel
            .beta_shift_argument(&var(usize::MAX), 1, 0)
            .unwrap_err()
            .contains("variable index overflow"));
        kernel.reset_budget();
        let argument = term(Term::Global(
            "polymorphic".into(),
            vec![Level::variable("u".into())],
        ));
        let (shifted, invariant) = kernel.beta_shift_argument(&argument, 4, 0).unwrap();
        assert!(invariant && Arc::ptr_eq(&shifted, &argument));
    }

    #[test]
    fn batched_partial_and_overapplication_have_the_original_types_and_values() {
        let mut kernel = Kernel::new();
        let choose = lam(nat(), lam(nat(), lam(nat(), var(2))));
        let value = apps(choose, &[var(0), var(1)]);
        let ty = pi(nat(), nat());
        kernel.check(&[nat(), nat()], &value, &ty, 0).unwrap();
        let reduced = kernel.natural_beta_spine(&value, 0).unwrap().unwrap();
        kernel.check(&[nat(), nat()], &reduced, &ty, 0).unwrap();
        assert!(kernel.same_syntax(&reduced, &lam(nat(), var(1))).unwrap());

        kernel
            .definition("identity", vec![], ty, lam(nat(), var(0)), false)
            .unwrap();
        let choose = lam(
            nat(),
            lam(nat(), term(Term::Global("identity".into(), vec![]))),
        );
        let value = apps(choose, &[number(3), number(4), number(5)]);
        kernel.check(&[], &value, &nat(), 0).unwrap();
        let reduced = kernel.natural_head(&value, 0).unwrap();
        assert!(kernel.same_syntax(&reduced, &number(5)).unwrap());
    }

    #[test]
    fn dependent_domains_are_checked_before_batching() {
        let mut kernel = Kernel::new();
        let universe = term(Term::Sort(Level::number(1).unwrap()));
        let function = lam(universe, lam(var(0), lam(var(1), var(0))));
        let value = apps(function, &[nat(), number(7), number(8)]);
        kernel.check(&[], &value, &nat(), 0).unwrap();
        let reduced = kernel.natural_head(&value, 0).unwrap();
        kernel.check(&[], &reduced, &nat(), 0).unwrap();
        assert!(kernel.same_syntax(&reduced, &number(8)).unwrap());
    }

    #[test]
    fn erased_bad_arguments_annotations_and_let_values_still_fail_source_typing() {
        for (index, value) in [
            apps(
                lam(nat(), lam(nat(), number(0))),
                &[term(Term::Sort(Level::number(0).unwrap())), number(0)],
            ),
            apps(
                lam(
                    nat(),
                    lam(term(Term::Sort(Level::number(0).unwrap())), number(0)),
                ),
                &[number(0), number(0)],
            ),
            apps(lam(nat(), lam(var(42), number(0))), &[number(0), number(0)]),
            apps(
                lam(
                    nat(),
                    lam(
                        nat(),
                        term(Term::Let(
                            nat(),
                            term(Term::Sort(Level::number(0).unwrap())),
                            number(0),
                        )),
                    ),
                ),
                &[number(0), number(0)],
            ),
            apps(
                lam(
                    nat(),
                    lam(
                        term(Term::Sort(Level::variable("unbound".into()))),
                        number(0),
                    ),
                ),
                &[number(0), number(0)],
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut kernel = Kernel::new();
            let name = format!("bad-{index}");
            let why = kernel
                .definition(&name, vec![], nat(), value, false)
                .unwrap_err();
            assert!(!why.contains("resource limit"), "{why}");
            assert!(!kernel.contains(&name));
        }
    }

    #[test]
    fn opaque_bodies_and_wrong_explicit_universe_arity_are_not_bypassed() {
        let mut kernel = Kernel::new();
        let ty = pi(nat(), pi(nat(), nat()));
        let body = lam(nat(), lam(nat(), var(1)));
        kernel
            .opaque_definition("sealed", vec![], ty.clone(), body.clone())
            .unwrap();
        let opaque = apps(
            term(Term::Global("sealed".into(), vec![])),
            &[number(0), number(1)],
        );
        assert!(kernel.natural_beta_spine(&opaque, 0).unwrap().is_none());
        assert!(!kernel.convertible(&[], &opaque, &number(0), 0).unwrap());
        kernel
            .definition("visible", vec![], ty, body, false)
            .unwrap();
        let wrong = apps(
            term(Term::Global(
                "visible".into(),
                vec![Level::number(1).unwrap()],
            )),
            &[number(0), number(1)],
        );
        assert!(kernel
            .natural_beta_spine(&wrong, 0)
            .unwrap_err()
            .contains("explicit universe"));
    }

    #[test]
    fn batch_substitution_respects_both_walk_depths_overflow_and_allocation() {
        let mut kernel = Kernel::new();
        let why = kernel
            .instantiate_many(&lam(nat(), var(1)), &[number(0), number(1)], DEPTH, 0)
            .unwrap_err();
        assert!(why.contains("resource limit"), "{why}");
        kernel.reset_budget();
        let why = kernel
            .instantiate_many(
                &lam(nat(), var(1)),
                &[number(0), lam(nat(), var(1))],
                0,
                DEPTH,
            )
            .unwrap_err();
        assert!(why.contains("resource limit"), "{why}");
        kernel.reset_budget();
        let why = kernel
            .instantiate_many(&lam(nat(), var(1)), &[number(0), var(usize::MAX)], 0, 0)
            .unwrap_err();
        assert!(why.contains("variable index overflow"), "{why}");
        kernel.reset_budget();
        kernel.transformed_bytes = 64 * 1024 * 1024 - 511;
        let why = kernel
            .instantiate_many(&var(0), &[var(1), var(2)], 0, 0)
            .unwrap_err();
        assert!(why.contains("allocation limit"), "{why}");
    }
}

#[cfg(test)]
#[path = "identity_shift_tests.rs"]
mod identity_tests;
