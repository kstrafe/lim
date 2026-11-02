//! Source syntax storage, never checked evidence. Replay can release opaque
//! proof trees after their declaration check while retaining backward IDs.
//! Emission keeps the original eager graph because it needs every proof body.
use super::*;
use std::{cell::RefCell, sync::Weak};

#[derive(Clone)]
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

#[derive(Clone)]
struct Entry {
    expression: Expression,
    depth: usize,
    payload: usize,
}

#[path = "export_spilled.rs"]
mod spilled;
use spilled::Entries;

#[derive(Default)]
struct Materialized {
    slots: Vec<Option<Weak<Term>>>,
    queued: Vec<bool>,
    recent: Vec<usize>,
    sparse: Option<HashMap<usize, (Weak<Term>, bool)>>,
}
impl Materialized {
    fn get(&self, id: usize) -> Option<T> {
        match &self.sparse {
            Some(slots) => slots.get(&id).and_then(|(value, _)| value.upgrade()),
            None => self
                .slots
                .get(id)
                .and_then(Option::as_ref)
                .and_then(Weak::upgrade),
        }
    }
    fn insert(&mut self, id: usize, value: &T) {
        if let Some(slots) = &mut self.sparse {
            let slot = slots
                .entry(id)
                .or_insert_with(|| (Arc::downgrade(value), false));
            slot.0 = Arc::downgrade(value);
            if !slot.1 {
                slot.1 = true;
                self.recent.push(id);
            }
        } else {
            self.slots[id] = Some(Arc::downgrade(value));
            if !self.queued[id] {
                self.queued[id] = true;
                self.recent.push(id);
            }
        }
    }
    fn spill(&mut self) {
        if self.sparse.is_some() {
            return;
        }
        let slots = std::mem::take(&mut self.slots);
        let queued = std::mem::take(&mut self.queued);
        let mut sparse = HashMap::new();
        for (id, slot) in slots.into_iter().enumerate() {
            if let Some(value) = slot.filter(|value| value.strong_count() > 0) {
                sparse.insert(id, (value, queued[id]));
            }
        }
        self.recent.retain(|id| sparse.contains_key(id));
        self.sparse = Some(sparse);
    }
    fn end_record(&mut self) {
        while let Some(id) = self.recent.pop() {
            if let Some(slots) = &mut self.sparse {
                if let Some((value, queued)) = slots.get_mut(&id) {
                    *queued = false;
                    if value.strong_count() == 0 {
                        slots.remove(&id);
                    }
                }
            } else {
                self.queued[id] = false;
                if self.slots[id]
                    .as_ref()
                    .is_some_and(|value| value.strong_count() == 0)
                {
                    self.slots[id] = None;
                }
            }
        }
    }
}

pub(super) struct Expressions {
    storage: Storage,
}

enum Storage {
    Eager(Vec<(T, usize)>),
    Compact {
        entries: Entries,
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
                    entries: Entries::new(),
                    materialized: RefCell::new(Materialized::default()),
                }
            },
        }
    }

    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(&self.storage, Storage::Compact { entries,.. } if entries.is_spilled())
    }
    pub(super) fn len(&self) -> usize {
        match &self.storage {
            Storage::Eager(values) => values.len(),
            Storage::Compact { entries, .. } => entries.len(),
        }
    }

    pub(super) fn depth(&self, id: usize) -> Result<usize> {
        match &self.storage {
            Storage::Eager(values) => values
                .get(id)
                .map(|(_, depth)| *depth)
                .ok_or_else(reference_error),
            Storage::Compact { entries, .. } => entries.meta(id).map(|meta| meta.depth),
        }
    }
    pub(super) fn payload(&self, id: usize) -> Result<usize> {
        match &self.storage {
            Storage::Eager(values) => values
                .get(id)
                .map(|(value, _)| payload(value))
                .ok_or_else(reference_error),
            Storage::Compact { entries, .. } => entries.meta(id).map(|meta| meta.payload),
        }
    }
    #[cfg(test)]
    pub(super) fn with_limit(retain_bodies: bool, limit: usize) -> Self {
        let mut result = Self::new(retain_bodies);
        if let Storage::Compact { entries, .. } = &mut result.storage {
            *entries = Entries::with_limit(limit);
        }
        result
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
                    *id = entries.meta(*id)?.canonical;
                }
                entries.push(Entry {
                    expression,
                    depth,
                    payload,
                })?;
                let memo = materialized.get_mut();
                if entries.is_spilled() {
                    memo.spill();
                } else {
                    memo.slots.push(None);
                    memo.queued.push(false);
                }
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
        // Dead weak handles must also be removed to reclaim Arc allocations.
        materialized.get_mut().end_record();
    }
}

fn reference_error() -> String {
    "expression reference must refer to an earlier record".into()
}

fn materialize(
    entries: &Entries,
    memo: &mut Materialized,
    id: usize,
    names: &[Name],
    levels: &[Level],
    depth: usize,
) -> Result<T> {
    if depth > MAX_EXPRESSION_DEPTH {
        return Err("export expression depth limit exceeded".into());
    }
    if let Some(value) = memo.get(id) {
        return Ok(value);
    }
    let entry = entries.get(id)?;
    let (id, entry) = if let Expression::Alias(canonical) = entry.expression {
        if let Some(value) = memo.get(canonical) {
            return Ok(value);
        }
        (canonical, entries.get(canonical)?)
    } else {
        (id, entry)
    };
    let value = construct(&entry.expression, names, levels, &mut |child| {
        materialize(entries, memo, child, names, levels, depth + 1)
    })?;
    memo.insert(id, &value);
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
        Expression::Sort(id) => Term::Sort(
            levels
                .get(*id)
                .ok_or("invalid source universe index")?
                .clone(),
        ),
        Expression::Global(id, arguments) => Term::Global(
            names
                .get(*id)
                .ok_or("invalid source name index")?
                .key
                .clone(),
            arguments
                .iter()
                .map(|id| {
                    levels
                        .get(*id)
                        .cloned()
                        .ok_or_else(|| "invalid source universe index".into())
                })
                .collect::<Result<_>>()?,
        ),
        Expression::App(a, b) => Term::App(get(*a)?, get(*b)?),
        Expression::Lam(a, b) => Term::Lam(get(*a)?, get(*b)?),
        Expression::Pi(a, b) => Term::Pi(get(*a)?, get(*b)?),
        Expression::Let(a, b, c) => Term::Let(get(*a)?, get(*b)?, get(*c)?),
        Expression::Project(name, index, subject) => Term::Project {
            family: names
                .get(*name)
                .ok_or("invalid source name index")?
                .key
                .clone(),
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

#[cfg(test)]
#[path = "export_expression_model_tests.rs"]
mod model_tests;
