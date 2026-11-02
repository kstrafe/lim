//! Compare common application heads before unfolding their definitions.
//!
//! Congruence uses ordinary conversion of every argument. A short bounded
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
    pub(super) left: Option<T>,
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
                left: None,
            });
        }
        if self.application_congruence(ctx, a, b, depth + 1)? {
            return Ok(ConversionProgress {
                equivalent: true,
                right: None,
                left: None,
            });
        }
        let mut left = None;
        let mut candidate = b.clone();
        let mut attempts = 0;
        let mut left_blocked = false;
        // Both directions share the existing eight-candidate heuristic.
        while attempts < 8 {
            if !left_blocked {
                let compared_left = left.as_ref().unwrap_or(a);
                let mut attempted = false;
                let reduced = self
                    .reduction_probe(depth, |kernel| {
                        if kernel.wrapper_may_expose_head(compared_left, &candidate, depth + 1)? {
                            attempted = true;
                            kernel.conversion_candidate(ctx, compared_left, depth + 1)
                        } else {
                            Ok(None)
                        }
                    })?
                    .flatten();
                if attempted {
                    attempts += 1;
                    left_blocked = reduced.is_none();
                }
                if let Some(reduced) = reduced {
                    left = Some(reduced);
                    let compared_left = left.as_ref().unwrap();
                    if self.same_syntax(compared_left, &candidate)?
                        || self.application_congruence(ctx, compared_left, &candidate, depth + 1)?
                    {
                        return Ok(ConversionProgress {
                            equivalent: true,
                            right: None,
                            left: None,
                        });
                    }
                    // Reconsider a completed left reduction before expanding
                    // the other call: a selected branch may already be it.
                    continue;
                }
            }
            if attempts == 8 {
                break;
            }
            attempts += 1;
            let reduced = self
                .reduction_probe(depth, |kernel| {
                    kernel.conversion_candidate(ctx, &candidate, depth + 1)
                })?
                .flatten();
            let Some(reduced) = reduced else {
                break;
            };
            let compared_left = left.as_ref().unwrap_or(a);
            if self.same_syntax(compared_left, &reduced)?
                || self.application_congruence(ctx, compared_left, &reduced, depth + 1)?
            {
                return Ok(ConversionProgress {
                    equivalent: true,
                    right: None,
                    left: None,
                });
            }
            candidate = reduced;
        }
        Ok(ConversionProgress {
            equivalent: false,
            right: (!Arc::ptr_eq(&candidate, b)).then_some(candidate),
            left,
        })
    }

    fn wrapper_may_expose_head(&mut self, left: &T, right: &T, depth: usize) -> Result<bool> {
        // Inspect only heads. Argument vectors and universe substitution
        // belong to the real reduction, not this optional prediction.
        let mut a = left;
        let mut b = right;
        let mut steps = 0;
        while let Term::App(function, _) = a.as_ref() {
            self.tick(depth + 1 + steps)?;
            a = function;
            steps += 1;
        }
        steps = 0;
        while let Term::App(function, _) = b.as_ref() {
            self.tick(depth + 1 + steps)?;
            b = function;
            steps += 1;
        }
        let Term::Global(target, _) = b.as_ref() else {
            return Ok(false);
        };
        let body = match a.as_ref() {
            Term::Global(name, _) if name != target => {
                let Some(body) = self
                    .declarations
                    .get(name)
                    .and_then(|decl| decl.value.clone())
                else {
                    return Ok(false);
                };
                body
            }
            Term::Lam(..) | Term::Let(..) => a.clone(),
            _ => return Ok(false),
        };
        if self.computational_head_is(&body, target, depth + 1)? {
            return Ok(true);
        }
        // A conditional or selector may return one of its arguments. This
        // predicts only a useful reduction direction; every actual step and
        // final argument comparison still uses the ordinary checked rules.
        let mut value = left;
        let mut steps = 0;
        while let Term::App(function, argument) = value.as_ref() {
            self.tick(depth + 1 + steps)?;
            if self.computational_head_is(argument, target, depth + 1)? {
                return Ok(true);
            }
            value = function;
            steps += 1;
        }
        Ok(false)
    }

    fn computational_head_is(&mut self, value: &T, target: &str, depth: usize) -> Result<bool> {
        let mut cursor = value;
        for _ in 0..DEPTH {
            self.tick(depth)?;
            cursor = match cursor.as_ref() {
                Term::Lam(_, value) | Term::Let(_, _, value) | Term::App(value, _) => value,
                Term::Global(name, _) => return Ok(name == target),
                _ => return Ok(false),
            };
        }
        Ok(false)
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

#[cfg(test)]
#[path = "conversion_left_tests.rs"]
mod left_tests;
