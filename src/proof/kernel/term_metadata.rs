//! Immutable syntax with a cached upper bound on loose de Bruijn indices.
use super::{Level, NestedCase, RecursionCase, Term};
use std::{fmt, ops::Deref, sync::Arc};

pub(in crate::proof::kernel) const TERM_NODE_BYTES: usize = 128 + std::mem::size_of::<usize>();

#[derive(Clone)]
pub(in crate::proof::kernel) struct T(Arc<TermNode>);

pub(in crate::proof::kernel) struct TermNode {
    value: Term,
    scope: usize,
}
const UNIVERSES: usize = 1usize << (usize::BITS - 1);
const RANGE: usize = UNIVERSES - 1;

impl T {
    #[inline(always)]
    pub(in crate::proof::kernel) fn as_ref(&self) -> &Term {
        &self.0.value
    }
    #[inline(always)]
    pub(in crate::proof::kernel) fn loose_range(&self) -> usize {
        let range = self.0.scope & RANGE;
        if range == RANGE {
            usize::MAX
        } else {
            range
        }
    }
    #[inline(always)]
    pub(in crate::proof::kernel) fn has_universe_params(&self) -> bool {
        self.0.scope & UNIVERSES != 0
    }
    #[inline(always)]
    pub(in crate::proof::kernel) fn from_shared(value: Arc<TermNode>) -> Self {
        Self(value)
    }
}
impl Deref for T {
    type Target = Arc<TermNode>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl fmt::Debug for T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_ref(), f)
    }
}

pub(in crate::proof::kernel) fn term(value: Term) -> T {
    let scope = range(&value).min(RANGE) | if universes(&value) { UNIVERSES } else { 0 };
    T(Arc::new(TermNode { value, scope }))
}

fn many(values: &[T]) -> usize {
    values.iter().map(T::loose_range).max().unwrap_or(0)
}
fn under_binder(range: usize) -> usize {
    // Saturation is conservative even for deliberately invalid usize::MAX
    // variables: it must never turn an unknown range into proven closure.
    if range == usize::MAX {
        range
    } else {
        range.saturating_sub(1)
    }
}
fn range(value: &Term) -> usize {
    match value {
        Term::Sort(_)
        | Term::Global(_, _)
        | Term::NatLiteral {
            family: _,
            value: _,
        }
        | Term::SelfType => 0,
        Term::Var(index) => index.saturating_add(1),
        Term::Pi(a, b) | Term::Lam(a, b) | Term::Sigma(a, b) => {
            a.loose_range().max(under_binder(b.loose_range()))
        }
        Term::Let(ty, value, body) => ty
            .loose_range()
            .max(value.loose_range())
            .max(under_binder(body.loose_range())),
        Term::App(a, b) | Term::Refl(a, b) | Term::QuotType(_, a, b) => {
            a.loose_range().max(b.loose_range())
        }
        Term::Pair(a, b, c) | Term::Eq(a, b, c) | Term::QuotMake(_, a, b, c) => {
            a.loose_range().max(b.loose_range()).max(c.loose_range())
        }
        Term::First(a)
        | Term::Second(a)
        | Term::Project {
            family: _,
            index: _,
            subject: a,
        } => a.loose_range(),
        Term::QuotLift {
            ty,
            relation,
            target,
            function,
            respect,
            subject,
            source_level: _,
            target_level: _,
        } => [ty, relation, target, function, respect, subject]
            .into_iter()
            .map(|t| t.loose_range())
            .max()
            .unwrap_or(0),
        Term::QuotInduct {
            ty,
            relation,
            motive,
            branch,
            subject,
            level: _,
        } => [ty, relation, motive, branch, subject]
            .into_iter()
            .map(|t| t.loose_range())
            .max()
            .unwrap_or(0),
        Term::EqElim {
            ty,
            left,
            motive,
            base,
            right,
            proof,
        } => [ty, left, motive, base, right, proof]
            .into_iter()
            .map(|t| t.loose_range())
            .max()
            .unwrap_or(0),
        Term::Ctor {
            family: _,
            levels: _,
            parameters,
            constructor: _,
            fields,
        } => many(parameters).max(many(fields)),
        Term::Induct {
            family: _,
            levels: _,
            parameters,
            indices,
            motive,
            branches,
            subject,
        } => many(parameters)
            .max(many(indices))
            .max(motive.loose_range())
            .max(many(branches))
            .max(subject.loose_range()),
        Term::MutualInduct {
            family: _,
            levels: _,
            parameters,
            indices,
            cases,
            subject,
        } => many(parameters)
            .max(many(indices))
            .max(
                cases
                    .iter()
                    .map(
                        |RecursionCase {
                             family: _,
                             motive,
                             branches,
                         }| motive.loose_range().max(many(branches)),
                    )
                    .max()
                    .unwrap_or(0),
            )
            .max(subject.loose_range()),
        Term::NestedInduct {
            family: _,
            levels: _,
            parameters,
            selected: _,
            indices,
            cases,
            subject,
        } => many(parameters)
            .max(many(indices))
            .max(
                cases
                    .iter()
                    .map(
                        |NestedCase {
                             selector,
                             motive,
                             branches,
                         }| {
                            selector
                                .loose_range()
                                .max(motive.loose_range())
                                .max(many(branches))
                        },
                    )
                    .max()
                    .unwrap_or(0),
            )
            .max(subject.loose_range()),
        Term::SelfAt(indices) | Term::Recur(_, indices) => many(indices),
    }
}

fn level_params(level: &Level) -> bool {
    level.numeral().is_none()
}
fn list_params(values: &[T]) -> bool {
    values.iter().any(T::has_universe_params)
}
fn universes(value: &Term) -> bool {
    match value {
        Term::Var(_)
        | Term::NatLiteral {
            family: _,
            value: _,
        }
        | Term::SelfType => false,
        Term::Sort(level) => level_params(level),
        Term::Global(_, levels) => levels.iter().any(level_params),
        Term::Pi(a, b)
        | Term::Lam(a, b)
        | Term::Sigma(a, b)
        | Term::App(a, b)
        | Term::Refl(a, b) => a.has_universe_params() || b.has_universe_params(),
        Term::Let(a, b, c) | Term::Pair(a, b, c) | Term::Eq(a, b, c) => {
            a.has_universe_params() || b.has_universe_params() || c.has_universe_params()
        }
        Term::First(a)
        | Term::Second(a)
        | Term::Project {
            family: _,
            index: _,
            subject: a,
        } => a.has_universe_params(),
        Term::QuotType(l, a, b) => {
            level_params(l) || a.has_universe_params() || b.has_universe_params()
        }
        Term::QuotMake(l, a, b, c) => {
            level_params(l)
                || a.has_universe_params()
                || b.has_universe_params()
                || c.has_universe_params()
        }
        Term::QuotLift {
            source_level,
            target_level,
            ty,
            relation,
            target,
            function,
            respect,
            subject,
        } => {
            level_params(source_level)
                || level_params(target_level)
                || [ty, relation, target, function, respect, subject]
                    .into_iter()
                    .any(|t| t.has_universe_params())
        }
        Term::QuotInduct {
            level,
            ty,
            relation,
            motive,
            branch,
            subject,
        } => {
            level_params(level)
                || [ty, relation, motive, branch, subject]
                    .into_iter()
                    .any(|t| t.has_universe_params())
        }
        Term::EqElim {
            ty,
            left,
            motive,
            base,
            right,
            proof,
        } => [ty, left, motive, base, right, proof]
            .into_iter()
            .any(|t| t.has_universe_params()),
        Term::Ctor {
            family: _,
            levels,
            parameters,
            constructor: _,
            fields,
        } => levels.iter().any(level_params) || list_params(parameters) || list_params(fields),
        Term::Induct {
            family: _,
            levels,
            parameters,
            indices,
            motive,
            branches,
            subject,
        } => {
            levels.iter().any(level_params)
                || list_params(parameters)
                || list_params(indices)
                || motive.has_universe_params()
                || list_params(branches)
                || subject.has_universe_params()
        }
        Term::MutualInduct {
            family: _,
            levels,
            parameters,
            indices,
            cases,
            subject,
        } => {
            levels.iter().any(level_params)
                || list_params(parameters)
                || list_params(indices)
                || cases.iter().any(
                    |RecursionCase {
                         family: _,
                         motive,
                         branches,
                     }| motive.has_universe_params() || list_params(branches),
                )
                || subject.has_universe_params()
        }
        Term::NestedInduct {
            family: _,
            levels,
            parameters,
            selected: _,
            indices,
            cases,
            subject,
        } => {
            levels.iter().any(level_params)
                || list_params(parameters)
                || list_params(indices)
                || cases.iter().any(
                    |NestedCase {
                         selector,
                         motive,
                         branches,
                     }| {
                        selector.has_universe_params()
                            || motive.has_universe_params()
                            || list_params(branches)
                    },
                )
                || subject.has_universe_params()
        }
        Term::SelfAt(indices) | Term::Recur(_, indices) => list_params(indices),
    }
}

#[cfg(test)]
#[path = "term_metadata_tests.rs"]
mod tests;
