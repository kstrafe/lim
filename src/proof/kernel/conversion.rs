//! Compare common application heads before unfolding their definitions.
//!
//! Congruence uses ordinary conversion of every argument. A short right-hand
//! reduction chain can expose the same call through wrappers and selected
//! cases. Explicit lambda/let heads contract before an unrelated named worker
//! is unfolded, including under dependent proof and term binders.
//! Each speculative delta candidate has a bounded reduction attempt; refusing
//! it returns to the ordinary converter, with all spent work still charged.
//! No declaration name, cached receipt or unverified source term is authority.
use super::*;

// Completed reductions belong to this comparison's unchanged context only.
// A declined operation never publishes its partially built result.
pub(super) struct ConversionProgress {
    pub(super) equivalent: bool,
    pub(super) right: Option<T>,
}

impl Kernel {
    pub(super) fn conversion_progress(
        &mut self,
        ctx: &[T],
        a: &T,
        b: &T,
        depth: usize,
    ) -> Result<ConversionProgress> {
        if !matches!((a.as_ref(), b.as_ref()), (Term::App(..), Term::App(..))) {
            return Ok(ConversionProgress {
                equivalent: false,
                right: None,
            });
        }
        if self.application_congruence(ctx, a, b, depth + 1)? {
            return Ok(ConversionProgress {
                equivalent: true,
                right: None,
            });
        }
        let mut candidate = b.clone();
        // This is a heuristic, not a completeness limit: the original
        // converter still handles longer chains and nonmatching heads.
        for _ in 0..8 {
            let reduced = self
                .reduction_probe(depth, |kernel| {
                    kernel.conversion_candidate(ctx, &candidate, depth + 1)
                })?
                .flatten();
            let Some(reduced) = reduced else {
                break;
            };
            if self.same_syntax(a, &reduced)?
                || self.application_congruence(ctx, a, &reduced, depth + 1)?
            {
                return Ok(ConversionProgress {
                    equivalent: true,
                    right: None,
                });
            }
            candidate = reduced;
        }
        Ok(ConversionProgress {
            equivalent: false,
            right: (!Arc::ptr_eq(&candidate, b)).then_some(candidate),
        })
    }

    #[cfg(test)]
    fn conversion_congruence(&mut self, ctx: &[T], a: &T, b: &T, depth: usize) -> Result<bool> {
        self.conversion_progress(ctx, a, b, depth)
            .map(|progress| progress.equivalent)
    }

    fn application_spine<'a>(&mut self, value: &'a T, depth: usize) -> Result<(&'a T, Vec<&'a T>)> {
        let mut head = value;
        let mut arguments = Vec::new();
        while let Term::App(function, argument) = head.as_ref() {
            self.tick(depth + arguments.len())?;
            self.charge_transformation(32)?;
            arguments.push(argument);
            head = function;
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    fn application_congruence(&mut self, ctx: &[T], a: &T, b: &T, depth: usize) -> Result<bool> {
        if !matches!((a.as_ref(), b.as_ref()), (Term::App(..), Term::App(..))) {
            return Ok(false);
        }
        let (a_head, a_args) = self.application_spine(a, depth + 1)?;
        let (b_head, b_args) = self.application_spine(b, depth + 1)?;
        if a_args.len() != b_args.len()
            || !matches!(a_head.as_ref(), Term::Global(..) | Term::Var(..))
            || !self.same_syntax(a_head, b_head)?
        {
            return Ok(false);
        }
        for (a, b) in a_args.iter().zip(b_args) {
            if !self.convertible(ctx, a, b, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn conversion_candidate(&mut self, ctx: &[T], value: &T, depth: usize) -> Result<Option<T>> {
        if !matches!(value.as_ref(), Term::App(..)) {
            return Ok(None);
        }
        let (head, arguments) = self.application_spine(value, depth + 1)?;
        if matches!(head.as_ref(), Term::Lam(..) | Term::Let(..)) {
            // Contract the explicit beta/zeta redex, retaining a neutral
            // global call rather than expanding the worker on both sides.
            return self.whnf_delta(ctx, value, false, depth + 1).map(Some);
        }
        let Term::Global(name, levels) = head.as_ref() else {
            return Ok(None);
        };
        let (declaration, map) = self.specialization(name, levels, depth + 1)?;
        let Some(body) = declaration.value else {
            return Ok(None);
        };
        let body = if map.is_empty() {
            body
        } else {
            self.universes(&body, &map, depth + 1)?
        };
        self.charge_transformation(arguments.len() * 128)?;
        let arguments = arguments.into_iter().cloned().collect::<Vec<_>>();
        let applied = apps(body, &arguments);
        self.whnf_delta(ctx, &applied, false, depth + 1).map(Some)
    }
}

#[cfg(test)]
#[path = "conversion_tests.rs"]
mod tests;
