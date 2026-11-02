//! Source syntax storage, never checked evidence. Replay can release opaque
//! proof trees after their declaration check while retaining backward IDs.
//! Emission keeps the original eager graph because it needs every proof body.
use super::*;
use std::{cell::RefCell, sync::Weak};

pub(super) enum Expression {
    Var(usize),
    Sort(usize),
    Global(usize, Vec<usize>),
    App(usize, usize),
    Lam(usize, usize),
    Pi(usize, usize),
    Let(usize, usize, usize),
    Project(usize, usize, usize),
    Natural(Natural),
    Alias(usize),
}

struct Entry {
    expression: Expression,
    depth: usize,
    payload: usize,
}

#[derive(Default)]
struct Materialized {
    slots: Vec<Option<Weak<Term>>>,
    queued: Vec<bool>,
    recent: Vec<usize>,
}

pub(super) struct Expressions {
    storage: Storage,
}

enum Storage {
    Eager(Vec<(T, usize)>),
    Compact {
        entries: Vec<Entry>,
        materialized: RefCell<Materialized>,
    },
}

impl Expressions {
    pub(super) fn new(retain_bodies: bool) -> Self {
        Self {
            storage: if retain_bodies {
                Storage::Eager(Vec::new())
            } else {
                Storage::Compact {
                    entries: Vec::new(),
                    materialized: RefCell::new(Materialized::default()),
                }
            },
        }
    }

    pub(super) fn len(&self) -> usize {
        match &self.storage {
            Storage::Eager(values) => values.len(),
            Storage::Compact { entries, .. } => entries.len(),
        }
    }

    pub(super) fn depth(&self, id: usize) -> Option<usize> {
        match &self.storage {
            Storage::Eager(values) => values.get(id).map(|(_, depth)| *depth),
            Storage::Compact { entries, .. } => entries.get(id).map(|entry| entry.depth),
        }
    }

    pub(super) fn payload(&self, id: usize) -> Option<usize> {
        match &self.storage {
            Storage::Eager(values) => values.get(id).map(|(value, _)| payload(value)),
            Storage::Compact { entries, .. } => entries.get(id).map(|entry| entry.payload),
        }
    }

    pub(super) fn push(
        &mut self,
        mut expression: Expression,
        depth: usize,
        payload: usize,
        names: &[Name],
        levels: &[Level],
    ) -> Result<()> {
        match &mut self.storage {
            Storage::Eager(values) => {
                let value = construct(&expression, names, levels, &mut |id| {
                    values
                        .get(id)
                        .map(|(value, _)| value.clone())
                        .ok_or_else(reference_error)
                })?;
                values.push((value, depth));
            }
            Storage::Compact {
                entries,
                materialized,
            } => {
                // Metadata is transparent syntax. Flatten aliases on insertion
                // so arbitrarily many wrappers cannot deepen reconstruction.
                if let Expression::Alias(id) = &mut expression {
                    if let Expression::Alias(canonical) = entries[*id].expression {
                        *id = canonical;
                    }
                }
                entries.push(Entry {
                    expression,
                    depth,
                    payload,
                });
                let memo = materialized.get_mut();
                memo.slots.push(None);
                memo.queued.push(false);
            }
        }
        Ok(())
    }

    pub(super) fn get(&self, id: usize, names: &[Name], levels: &[Level]) -> Result<T> {
        match &self.storage {
            Storage::Eager(values) => values
                .get(id)
                .map(|(value, _)| value.clone())
                .ok_or_else(reference_error),
            Storage::Compact {
                entries,
                materialized,
            } => materialize(
                entries,
                &mut materialized.borrow_mut(),
                id,
                names,
                levels,
                0,
            ),
        }
    }

    pub(super) fn end_record(&mut self) {
        let Storage::Compact { materialized, .. } = &mut self.storage else {
            return;
        };
        let memo = materialized.get_mut();
        // Drop dead Weak handles too: they otherwise retain Arc allocations
        // after the opaque body itself has been destroyed. Live handles only
        // reuse syntax still owned elsewhere; no typing result is cached.
        while let Some(id) = memo.recent.pop() {
            memo.queued[id] = false;
            if memo.slots[id]
                .as_ref()
                .is_some_and(|value| value.strong_count() == 0)
            {
                memo.slots[id] = None;
            }
        }
    }
}

fn reference_error() -> String {
    "expression reference must refer to an earlier record".into()
}

fn materialize(
    entries: &[Entry],
    memo: &mut Materialized,
    id: usize,
    names: &[Name],
    levels: &[Level],
    depth: usize,
) -> Result<T> {
    if depth > MAX_EXPRESSION_DEPTH {
        return Err("export expression depth limit exceeded".into());
    }
    let entry = entries.get(id).ok_or_else(reference_error)?;
    let id = if let Expression::Alias(canonical) = entry.expression {
        canonical
    } else {
        id
    };
    if let Some(value) = memo.slots[id].as_ref().and_then(Weak::upgrade) {
        return Ok(value);
    }
    let value = construct(&entries[id].expression, names, levels, &mut |child| {
        materialize(entries, memo, child, names, levels, depth + 1)
    })?;
    memo.slots[id] = Some(Arc::downgrade(&value));
    if !memo.queued[id] {
        memo.queued[id] = true;
        memo.recent.push(id);
    }
    Ok(value)
}

fn construct(
    expression: &Expression,
    names: &[Name],
    levels: &[Level],
    get: &mut impl FnMut(usize) -> Result<T>,
) -> Result<T> {
    let value = match expression {
        Expression::Var(index) => Term::Var(*index),
        Expression::Sort(id) => Term::Sort(levels[*id].clone()),
        Expression::Global(id, arguments) => Term::Global(
            names[*id].key.clone(),
            arguments.iter().map(|id| levels[*id].clone()).collect(),
        ),
        Expression::App(a, b) => Term::App(get(*a)?, get(*b)?),
        Expression::Lam(a, b) => Term::Lam(get(*a)?, get(*b)?),
        Expression::Pi(a, b) => Term::Pi(get(*a)?, get(*b)?),
        Expression::Let(a, b, c) => Term::Let(get(*a)?, get(*b)?, get(*c)?),
        Expression::Project(name, index, subject) => Term::Project {
            family: names[*name].key.clone(),
            index: *index,
            subject: get(*subject)?,
        },
        Expression::Natural(value) => Term::NatLiteral {
            family: "$lean:s3:Nat".into(),
            value: value.clone(),
        },
        Expression::Alias(id) => return get(*id),
    };
    Ok(term(value))
}

pub(super) fn payload(value: &T) -> usize {
    match value.as_ref() {
        Term::NatLiteral { family, value } => family.len().saturating_add(value.decimal().len()),
        Term::Sort(level) => level.memory_weight(),
        Term::Global(name, levels) => levels.iter().fold(name.len(), |total, level| {
            total.saturating_add(level.memory_weight())
        }),
        Term::Project { family, .. } => family.len(),
        _ => 0,
    }
}

#[cfg(test)]
#[path = "export_expressions_tests.rs"]
mod tests;
