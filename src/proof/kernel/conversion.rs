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

enum Congruence<'a> {
    Compared(bool),
    // These are complete spines borrowed from this comparison's original
    // inputs, not partially reduced or unchecked replacement expressions.
    Inductive(Vec<&'a T>, Vec<&'a T>),
}

impl Kernel {
    pub(super) fn completed_data_record(
        &mut self,
        name: &str,
        levels: &[Level],
        constructor: &str,
        parameters: usize,
        fields: usize,
        depth: usize,
    ) -> Result<bool> {
        if self.provisional_family(name) || self.nested.contains_key(name)? {
            return Ok(false);
        }
        let (family, map) = self.family(name, levels, depth)?;
        Ok(family.group.len() == 1
            && family.indices.is_empty()
            && family.parameters.len() == parameters
            && family.constructors.len() == 1
            && family.constructors[0].name == constructor
            && family.constructors[0].fields.len() == fields
            && family.constructors[0].recursive.iter().all(Option::is_none)
            // A symbolic sort may be Prop. Require exactly Type 0 after
            // specializing the checked family's universe arguments.
            && family.sort.substitute(&map)?.equivalent(&Level::number(1)?)?)
    }

    pub(super) fn conversion_progress(
        &mut self,
        ctx: &[T],
        a: &T,
        b: &T,
        depth: usize,
    ) -> Result<ConversionProgress> {
        let applications = matches!((a.as_ref(), b.as_ref()), (Term::App(..), Term::App(..)));
        if applications && self.congruence_probe(ctx, a, b, depth + 1)? {
            return Ok(ConversionProgress {
                equivalent: true,
                right: None,
                left: None,
            });
        }
        // Preserve the original complete scalar call before speculative
        // delta candidates replace its packing wrapper with an inner worker.
        // Congruence above still gets the cheaper comparison of shared heads.
        if ctx.is_empty() {
            if let Some(left) = self.delayed_record_wrapper(a, depth + 1)? {
                return Ok(ConversionProgress {
                    equivalent: false,
                    left: Some(left),
                    right: None,
                });
            }
            if let Some(right) = self.delayed_record_wrapper(b, depth + 1)? {
                return Ok(ConversionProgress {
                    equivalent: false,
                    left: None,
                    right: Some(right),
                });
            }
        }
        if !applications {
            return Ok(ConversionProgress {
                equivalent: false,
                left: None,
                right: None,
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
                        || self.congruence_probe(ctx, compared_left, &candidate, depth + 1)?
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
                || self.congruence_probe(ctx, compared_left, &reduced, depth + 1)?
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
                    .get(name)?
                    .as_ref()
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

    fn congruence_probe(&mut self, ctx: &[T], a: &T, b: &T, depth: usize) -> Result<bool> {
        if !ctx.is_empty() {
            return self.application_congruence(ctx, a, b, depth);
        }
        let result = self.reduction_probe(depth, |kernel| {
            let Some((head, a, b)) = kernel.common_application_arguments(a, b, depth + 1)? else {
                return Ok(Congruence::Compared(false));
            };
            if kernel.natural_index_arguments(head, &a, &b, depth + 2)? {
                // Compare natural indices of a checked datatype directly.
                // Structured data and proof-valued calls retain speculation.
                return Ok(Congruence::Inductive(a, b));
            }
            kernel
                .congruent_arguments(ctx, &a, &b, depth + 2)
                .map(Congruence::Compared)
        })?;
        match result {
            Some(Congruence::Compared(equivalent)) => Ok(equivalent),
            Some(Congruence::Inductive(a, b)) => self.congruent_arguments(ctx, &a, &b, depth + 1),
            None => Ok(false),
        }
    }

    fn application_congruence(&mut self, ctx: &[T], a: &T, b: &T, depth: usize) -> Result<bool> {
        let Some((_, a, b)) = self.common_application_arguments(a, b, depth)? else {
            return Ok(false);
        };
        self.congruent_arguments(ctx, &a, &b, depth + 1)
    }

    fn natural_index_arguments(
        &mut self,
        head: &T,
        a: &[&T],
        b: &[&T],
        depth: usize,
    ) -> Result<bool> {
        self.tick(depth)?;
        let Term::Global(name, _) = head.as_ref() else {
            return Ok(false);
        };
        let Some(declaration) = self.declarations.resident(name)? else {
            return Ok(false);
        };
        let Some(family) = &declaration.family else {
            return Ok(false);
        };
        if declaration.value.is_some()
            || family.parameters.is_empty()
            || !matches!(family.parameters[0].as_ref(), Term::Sort(..))
            || a.len() < 2
            || a.len() != family.parameters.len() + family.indices.len()
        {
            return Ok(false);
        }
        // Every remaining parameter/index has the same explicit type parameter;
        // each preceding argument shifts that parameter by one binder.
        for (index, domain) in family.parameters[1..]
            .iter()
            .chain(&family.indices)
            .enumerate()
        {
            self.tick(depth + 1)?;
            if !matches!(domain.as_ref(), Term::Var(actual) if *actual == index) {
                return Ok(false);
            }
        }
        if !self.same_syntax(a[0], b[0])? {
            return Ok(false);
        }
        let Term::Global(natural, levels) = a[0].as_ref() else {
            return Ok(false);
        };
        if !levels.is_empty()
            || self.provisional_family(natural)
            || self.nested.contains_key(natural)?
        {
            return Ok(false);
        }
        let Some(declaration) = self.declarations.resident(natural)? else {
            return Ok(false);
        };
        if !declaration.universes.is_empty() {
            return Ok(false);
        }
        match &declaration.family {
            Some(family) => natural::natural_shape(natural, family),
            None => Ok(false),
        }
    }

    #[expect(clippy::type_complexity)]
    fn common_application_arguments<'a>(
        &mut self,
        a: &'a T,
        b: &'a T,
        depth: usize,
    ) -> Result<Option<(&'a T, Vec<&'a T>, Vec<&'a T>)>> {
        if !matches!((a.as_ref(), b.as_ref()), (Term::App(..), Term::App(..))) {
            return Ok(None);
        }
        let (a_head, a_args) = self.application_spine(a, depth + 1)?;
        let (b_head, b_args) = self.application_spine(b, depth + 1)?;
        if a_args.len() != b_args.len()
            || !matches!(a_head.as_ref(), Term::Global(..) | Term::Var(..))
            || !self.same_syntax(a_head, b_head)?
        {
            return Ok(None);
        }
        Ok(Some((a_head, a_args, b_args)))
    }

    fn congruent_arguments(&mut self, ctx: &[T], a: &[&T], b: &[&T], depth: usize) -> Result<bool> {
        for (a, b) in a.iter().zip(b) {
            if !self.convertible(ctx, a, b, depth)? {
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
        self.charge_transformation(arguments.len() * TERM_NODE_BYTES)?;
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

#[cfg(test)]
#[path = "congruence_probe_tests.rs"]
mod probe_tests;
