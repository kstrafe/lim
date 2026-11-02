//! Checked paired-predecessor recursion with closed finite-data results.
//!
//! F(0,0)=a, F(0,y+1)=b, F(x+1,0)=c, F(x+1,y+1)=F(x,y). Compare the two
//! counts and select the actual terminal. A constant F(0,y) has a=b.
//! Check the full recurrence; no function or constructor name
//! authorizes comparison, and fixed-argument fusion stays unchanged.
use super::*;

impl Kernel {
    /// Called only after checking a natural recursor and a constant motive
    /// whose result is Nat -> R, for a completed finite Type-0 data family R.
    #[expect(clippy::too_many_arguments)]
    pub(super) fn natural_comparison_fold(
        &mut self,
        family: &str,
        function_type: &T,
        branches: &[T],
        left: &T,
        right: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let Some([at_equal, at_less, at_right_zero]) =
            self.natural_comparison_terminals(family, function_type, branches, depth + 1)?
        else {
            return Ok(None);
        };
        let Some(left) = self.natural_closed_number(family, left, depth + 1)? else {
            return Ok(None);
        };
        let Some(right) = self.natural_closed_number(family, right, depth + 1)? else {
            return Ok(None);
        };
        self.work = self
            .work
            .saturating_add(left.decimal().len().max(right.decimal().len()));
        self.tick(depth + 1)?;
        let order =
            (left.decimal().len(), left.decimal()).cmp(&(right.decimal().len(), right.decimal()));
        Ok(Some(match order {
            std::cmp::Ordering::Less => at_less,
            std::cmp::Ordering::Equal => at_equal,
            std::cmp::Ordering::Greater => at_right_zero,
        }))
    }

    /// Return equal/less/greater terminals only after verifying the complete
    /// paired-predecessor recurrence. This also supports symbolic observations
    /// without inferring a comparison from sampled input values.
    pub(super) fn natural_comparison_terminals(
        &mut self,
        family: &str,
        function_type: &T,
        branches: &[T],
        depth: usize,
    ) -> Result<Option<[T; 3]>> {
        self.tick(depth)?;
        let Term::Pi(_, result_type) = function_type.as_ref() else {
            return Ok(None);
        };
        let Term::Global(result_family, result_levels) = result_type.as_ref() else {
            return Ok(None);
        };
        if !result_levels.is_empty() || branches.len() != 2 {
            return Ok(None);
        }
        let Some(base) = self.comparison_nat_lambda(&branches[0], family, depth + 1)? else {
            return Ok(None);
        };
        let Some((at_equal, at_less)) =
            self.comparison_left_terminals(&base, family, result_type, result_family, depth + 1)?
        else {
            return Ok(None);
        };
        let Some(step) = self.comparison_nat_lambda(&branches[1], family, depth + 1)? else {
            return Ok(None);
        };
        let step = self.natural_head(&step, depth + 1)?;
        let Term::Lam(domain, body) = step.as_ref() else {
            return Ok(None);
        };
        let Some(domain) =
            self.natural_comparison_function_type(domain, family, result_family, depth + 1)?
        else {
            return Ok(None);
        };
        if !self.same_syntax(&domain, function_type)? {
            return Ok(None);
        }
        let Some(body) = self.comparison_nat_lambda(body, family, depth + 1)? else {
            return Ok(None);
        };
        let body = self.natural_head(&body, depth + 1)?;
        let Term::Induct {
            family: actual,
            levels,
            parameters,
            indices,
            motive,
            branches,
            subject,
        } = body.as_ref()
        else {
            return Ok(None);
        };
        if actual != family
            || !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || branches.len() != 2
        {
            return Ok(None);
        }
        let subject = self.natural_head(subject, depth + 1)?;
        if !matches!(subject.as_ref(), Term::Var(0)) {
            return Ok(None);
        }
        let Some(range) = self.comparison_nat_lambda(motive, family, depth + 1)? else {
            return Ok(None);
        };
        let range = self.natural_head(&range, depth + 1)?;
        if !self.same_syntax(&range, result_type)? {
            return Ok(None);
        }
        let Some(at_right_zero) =
            self.comparison_terminal(&branches[0], result_family, depth + 1)?
        else {
            return Ok(None);
        };
        let Some(step) = self.comparison_nat_lambda(&branches[1], family, depth + 1)? else {
            return Ok(None);
        };
        let step = self.natural_head(&step, depth + 1)?;
        let Term::Lam(domain, body) = step.as_ref() else {
            return Ok(None);
        };
        let domain = self.natural_head(domain, depth + 1)?;
        if !self.same_syntax(&domain, result_type)? {
            return Ok(None);
        }
        let body = self.natural_head(body, depth + 1)?;
        let Term::App(previous_function, previous_right) = body.as_ref() else {
            return Ok(None);
        };
        // Under the two outer step binders, right argument, and two inner
        // step binders: old function is 3, right predecessor is 1. Neither
        // the outer predecessor (4) nor either accumulator may replace them.
        if !matches!(previous_function.as_ref(), Term::Var(3))
            || !matches!(previous_right.as_ref(), Term::Var(1))
        {
            return Ok(None);
        }
        Ok(Some([at_equal, at_less, at_right_zero]))
    }

    fn comparison_left_terminals(
        &mut self,
        value: &T,
        family: &str,
        result_type: &T,
        result_family: &str,
        depth: usize,
    ) -> Result<Option<(T, T)>> {
        self.tick(depth)?;
        if let Some(value) = self.comparison_terminal(value, result_family, depth + 1)? {
            return Ok(Some((value.clone(), value)));
        }
        let value = self.natural_head(value, depth + 1)?;
        let Term::Induct {
            family: actual,
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
        if actual != family
            || !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || branches.len() != 2
        {
            return Ok(None);
        }
        let subject = self.natural_head(subject, depth + 1)?;
        if !matches!(subject.as_ref(), Term::Var(0)) {
            return Ok(None);
        }
        let Some(range) = self.comparison_nat_lambda(motive, family, depth + 1)? else {
            return Ok(None);
        };
        let range = self.natural_head(&range, depth + 1)?;
        if !self.same_syntax(&range, result_type)? {
            return Ok(None);
        }
        let Some(at_equal) = self.comparison_terminal(&branches[0], result_family, depth + 1)?
        else {
            return Ok(None);
        };
        let Some(step) = self.comparison_nat_lambda(&branches[1], family, depth + 1)? else {
            return Ok(None);
        };
        let step = self.natural_head(&step, depth + 1)?;
        let Term::Lam(domain, body) = step.as_ref() else {
            return Ok(None);
        };
        let domain = self.natural_head(domain, depth + 1)?;
        if !self.same_syntax(&domain, result_type)? {
            return Ok(None);
        }
        let Some(at_less) = self.comparison_terminal(body, result_family, depth + 1)? else {
            return Ok(None);
        };
        Ok(Some((at_equal, at_less)))
    }

    fn comparison_nat_lambda(
        &mut self,
        value: &T,
        family: &str,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        let Term::Lam(domain, body) = value.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        Ok(Some(body.clone()))
    }

    fn comparison_terminal(&mut self, value: &T, family: &str, depth: usize) -> Result<Option<T>> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        if matches!(value.as_ref(), Term::Ctor { family: actual, levels, parameters, fields, .. }
            if actual == family && levels.is_empty() && parameters.is_empty() && fields.is_empty())
        {
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    fn natural_comparison_function_type(
        &mut self,
        value: &T,
        family: &str,
        result: &str,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        let Term::Pi(domain, range) = value.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let range = self.natural_head(range, depth + 1)?;
        if !matches!(range.as_ref(), Term::Global(name, levels) if name == result && levels.is_empty())
        {
            return Ok(None);
        }
        self.charge_transformation(384 + family.len())?;
        Ok(Some(term(Term::Pi(
            term(Term::Global(family.into(), vec![])),
            range,
        ))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn nat() -> T {
        term(Term::Global("#pt-nat".into(), vec![]))
    }
    fn flag() -> T {
        term(Term::Global("Flag".into(), vec![]))
    }
    fn var(n: usize) -> T {
        term(Term::Var(n))
    }
    fn lam(ty: T, body: T) -> T {
        term(Term::Lam(ty, body))
    }
    fn function() -> T {
        term(Term::Pi(nat(), flag()))
    }
    fn literal(n: usize) -> T {
        term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse(&n.to_string()).unwrap(),
        })
    }
    fn constructor(family: &str, name: &str, fields: Vec<T>) -> T {
        term(Term::Ctor {
            family: family.into(),
            levels: vec![],
            parameters: vec![],
            constructor: name.into(),
            fields,
        })
    }
    fn terminal(n: bool) -> T {
        constructor("Flag", if n { "on" } else { "off" }, vec![])
    }
    fn unary(n: usize) -> T {
        (0..n).fold(constructor("#pt-nat", "zero", vec![]), |n, _| {
            constructor("#pt-nat", "succ", vec![n])
        })
    }
    fn fold(ty: T, base: T, body: T, count: T) -> T {
        term(Term::Induct {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), ty.clone()),
            branches: vec![base, lam(nat(), lam(ty, body))],
            subject: count,
        })
    }
    fn comparison(left: T, right: T, inverted: bool) -> T {
        let inner = fold(
            flag(),
            terminal(inverted),
            term(Term::App(var(3), var(1))),
            var(0),
        );
        let outer = fold(
            function(),
            lam(nat(), terminal(!inverted)),
            lam(nat(), inner),
            left,
        );
        term(Term::App(outer, right))
    }
    fn kernel() -> Kernel {
        let mut kernel = Kernel::new();
        kernel
            .inductive(
                "Flag",
                vec![],
                vec![],
                Level::number(1).unwrap(),
                vec![
                    ("off".into(), vec![]),
                    ("on".into(), vec![]),
                    ("equal".into(), vec![]),
                ],
            )
            .unwrap();
        kernel.reset_budget();
        kernel
    }

    #[test]
    fn paired_recursion_matches_unbatched_constructor_iota_and_actual_terminals() {
        let mut kernel = kernel();
        for inverted in [false, true] {
            for left in 0..=5 {
                for right in 0..=5 {
                    kernel.reset_budget();
                    let fast = comparison(literal(left), literal(right), inverted);
                    let slow = comparison(unary(left), unary(right), inverted);
                    kernel.check(&[], &fast, &flag(), 0).unwrap();
                    kernel.check(&[], &slow, &flag(), 0).unwrap();
                    let fast = kernel.whnf(&[], &fast, 0).unwrap();
                    kernel.check(&[], &fast, &flag(), 0).unwrap();
                    assert!(kernel
                        .convertible(&[], &fast, &terminal((left <= right) != inverted), 0)
                        .unwrap());
                    assert!(kernel.convertible(&[], &fast, &slow, 0).unwrap());
                }
            }
        }
    }

    #[test]
    fn three_distinct_terminals_preserve_trichotomy_and_constructor_order() {
        let mut kernel = kernel();
        let make = |left: T, right: T| {
            let base = fold(
                flag(),
                constructor("Flag", "equal", vec![]),
                terminal(false),
                var(0),
            );
            let step = fold(
                flag(),
                terminal(true),
                term(Term::App(var(3), var(1))),
                var(0),
            );
            term(Term::App(
                fold(function(), lam(nat(), base), lam(nat(), step), left),
                right,
            ))
        };
        for left in 0..=5 {
            for right in 0..=5 {
                kernel.reset_budget();
                let fast = make(literal(left), literal(right));
                let slow = make(unary(left), unary(right));
                kernel.check(&[], &fast, &flag(), 0).unwrap();
                kernel.check(&[], &slow, &flag(), 0).unwrap();
                let expected = constructor(
                    "Flag",
                    if left < right {
                        "off"
                    } else if left == right {
                        "equal"
                    } else {
                        "on"
                    },
                    vec![],
                );
                assert!(kernel.convertible(&[], &fast, &expected, 0).unwrap());
                assert!(kernel.convertible(&[], &fast, &slow, 0).unwrap());
            }
        }
    }

    #[test]
    fn selected_operands_remain_open_in_their_real_typing_context() {
        let mut kernel = kernel();
        for value in [
            comparison(var(0), literal(1), false),
            comparison(literal(1), var(0), false),
        ] {
            kernel.reset_budget();
            kernel.check(&[nat()], &value, &flag(), 0).unwrap();
            let reduced = kernel.natural_head(&value, 0).unwrap();
            kernel.check(&[nat()], &reduced, &flag(), 0).unwrap();
            assert!(!kernel
                .convertible(&[nat()], &reduced, &terminal(true), 0)
                .unwrap());
            assert!(!kernel
                .convertible(&[nat()], &reduced, &terminal(false), 0)
                .unwrap());
        }
    }

    #[test]
    fn a_zero_left_case_cannot_capture_an_outer_value_as_its_operand() {
        let mut kernel = kernel();
        let base = fold(
            flag(),
            constructor("Flag", "equal", vec![]),
            terminal(false),
            var(1),
        );
        let step = fold(
            flag(),
            terminal(true),
            term(Term::App(var(3), var(1))),
            var(0),
        );
        let value = term(Term::App(
            fold(function(), lam(nat(), base), lam(nat(), step), literal(2)),
            literal(2),
        ));
        kernel.check(&[nat()], &value, &flag(), 0).unwrap();
        let reduced = kernel.natural_head(&value, 0).unwrap();
        kernel.check(&[nat()], &reduced, &flag(), 0).unwrap();
        // It can be equal or off depending on the outer local, so it is not
        // the ordinary equality recurrence even though both operands are 2.
        let why = kernel
            .convertible(&[nat()], &reduced, &constructor("Flag", "equal", vec![]), 0)
            .unwrap();
        assert!(!why);
    }

    #[test]
    fn paired_conversion_still_obeys_work_and_transformation_budgets() {
        let mut kernel = kernel();
        let value = comparison(literal(1000), literal(1001), false);
        kernel.check(&[], &value, &flag(), 0).unwrap();
        kernel.reset_budget();
        kernel.work = WORK;
        assert!(kernel
            .whnf(&[], &value, 0)
            .unwrap_err()
            .contains("resource limit"));
        kernel.reset_budget();
        kernel.transformed_bytes = 64 * 1024 * 1024 - 1;
        assert!(kernel
            .whnf(&[], &value, 0)
            .unwrap_err()
            .contains("allocation limit"));
    }
}
