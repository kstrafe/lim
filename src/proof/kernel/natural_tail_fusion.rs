//! Turn an identity-base function fold's tail composition into a scalar fold.
use super::*;

impl Kernel {
    /// For checked terms, F(0,x)=x and F(succ n,x)=F(n,U(x)) imply
    /// F(n,x)=iterate(U,n,x), provided U is independent of n and F(n).
    /// Only a computationally known count is optimized; an unknown count
    /// retains the original conversion rules. Arithmetic remains separate.
    /// Ordinary source inference must still check every discarded annotation
    /// and value, just as it does for fixed-argument and first-field fusion.
    pub(super) fn natural_tail_apply_fusion(
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
            || self.natural_recursor_family(family, depth + 1)?.is_none()
        {
            return Ok(None);
        }
        // With an unknown count, the two iterators are propositionally equal
        // by induction, not a new judgmental equality. Optimize only an
        // actual closed computation and retain the ordinary open-term rules.
        if self
            .natural_probe_number(family, subject, depth + 1)?
            .is_none()
        {
            return Ok(None);
        }
        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, range) = motive.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)?
            || !self.natural_tail_function_type(range, family, depth + 1)?
        {
            return Ok(None);
        }
        let base = self.natural_head(&branches[0], depth + 1)?;
        let Term::Lam(domain, body) = base.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)?
            || !matches!(self.natural_head(body, depth + 1)?.as_ref(), Term::Var(0))
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
        if !self.natural_tail_function_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let body = self.natural_head(body, depth + 1)?;
        let Term::Lam(domain, body) = body.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let body = self.natural_head(body, depth + 1)?;
        let Term::App(function, update) = body.as_ref() else {
            return Ok(None);
        };
        if !matches!(function.as_ref(), Term::Var(1)) {
            return Ok(None);
        }

        // U is scoped under predecessor, old function, and argument. Rewrite
        // it under predecessor and scalar accumulator instead: argument ->
        // accumulator, outer locals move down one, inner binders stay put.
        // Inspect the entire retained update, including types and erased lets.
        // No head-only independence test can justify changing these binders.
        let mut refused = false;
        let update = self.transform_shared(
            update,
            0,
            depth + 1,
            &mut |_, index, binders| {
                let index = if index < binders {
                    index
                } else {
                    match index - binders {
                        0 => index,
                        1 | 2 => {
                            refused = true;
                            index
                        }
                        _ => index - 1,
                    }
                };
                Ok(term(Term::Var(index)))
            },
            &mut |level| Ok(level.clone()),
        )?;
        if refused {
            return Ok(None);
        }
        self.charge_transformation(1024 + family.len() * 4)?;
        let nat = term(Term::Global(family.clone(), vec![]));
        Ok(Some(term(Term::Induct {
            family: family.clone(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: term(Term::Lam(nat.clone(), nat.clone())),
            branches: vec![
                argument.clone(),
                term(Term::Lam(nat.clone(), term(Term::Lam(nat, update)))),
            ],
            subject: subject.clone(),
        })))
    }

    /// Both parts normalize to this nominal natural family. In particular,
    /// neither the recursor index nor the function argument can affect them.
    fn natural_tail_function_type(
        &mut self,
        value: &T,
        family: &str,
        depth: usize,
    ) -> Result<bool> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        let Term::Pi(domain, range) = value.as_ref() else {
            return Ok(false);
        };
        Ok(self.natural_type(domain, family, depth + 1)?
            && self.natural_type(range, family, depth + 1)?)
    }
}

#[cfg(test)]
#[path = "natural_tail_fusion_tests.rs"]
mod tests;
