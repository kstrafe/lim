//! Declaration initializers retain source expression IDs where possible.
//! This table stores syntax roots only; it contains no checked judgments.
//! Cold entries use invocation-local protected pages, never a replay cache.
use super::super::{declarations, scratch::Spool, Kernel};
use super::{expressions::Expressions, levels::Levels, names::Names, Result, T};
use std::cell::{Cell, RefCell};

const MEMORY_BYTES: usize = 1024 * 1024;
const INDEX_BYTES: usize = 24;
const MAX_NATIVE_BYTES: usize = 32 * 1024 * 1024;
const PAGE: usize = 64 * 1024;

#[derive(Clone)]
pub(super) enum Initializer {
    Source(usize),
    Native(T),
}

pub(super) struct Initializers {
    enabled: bool,
    storage: Storage,
    max_count: usize,
    scratch_limit: u64,
    poisoned: Cell<bool>,
}

enum Storage {
    Memory {
        entries: Vec<Option<Initializer>>,
        bytes: usize,
        limit: usize,
    },
    Spilled(Spilled),
}
struct Spilled {
    index: RefCell<Spool>,
    data: RefCell<Option<Spool>>,
    count: usize,
    scratch_limit: u64,
}

impl Initializers {
    pub(super) fn new(enabled: bool) -> Self {
        Self::with_limit(enabled, MEMORY_BYTES)
    }
    pub(super) fn with_limit(enabled: bool, limit: usize) -> Self {
        Self::build(
            enabled,
            limit,
            super::MAX_DECLARATIONS,
            super::super::scratch::DEFAULT_BYTES,
        )
    }
    pub(super) fn with_limits(enabled: bool, max_count: usize, max_scratch_bytes: u64) -> Self {
        Self::build(enabled, MEMORY_BYTES, max_count, max_scratch_bytes)
    }
    pub(super) fn with_count_limit(enabled: bool, max_count: usize) -> Self {
        if max_count == super::MAX_DECLARATIONS {
            Self::new(enabled)
        } else {
            Self::build(
                enabled,
                MEMORY_BYTES,
                max_count,
                super::super::scratch::DEFAULT_BYTES,
            )
        }
    }
    fn build(enabled: bool, limit: usize, max_count: usize, scratch_limit: u64) -> Self {
        Self {
            enabled,
            max_count,
            scratch_limit,
            storage: Storage::Memory {
                entries: vec![],
                bytes: 0,
                limit,
            },
            poisoned: Cell::new(false),
        }
    }
    pub(super) fn push(
        &mut self,
        report_id: usize,
        initializer: Option<Initializer>,
    ) -> Result<()> {
        self.healthy()?;
        if !self.enabled {
            return if initializer.is_none() {
                Ok(())
            } else {
                Err("declaration initializers are disabled".into())
            };
        }
        if report_id != self.len() {
            return Err("declaration initializer index is not contiguous".into());
        }
        if self.len() >= self.max_count {
            return Err("declaration initializer limit exceeded".into());
        }
        let result = self.append(initializer);
        self.checked(result)
    }
    fn append(&mut self, initializer: Option<Initializer>) -> Result<()> {
        if let Storage::Memory {
            entries,
            bytes,
            limit,
        } = &mut self.storage
        {
            // Source IDs and empty entries own no term graph. Count graph
            // allocation conservatively for native roots, including sharing.
            let owned = match &initializer {
                Some(Initializer::Native(value)) => {
                    declarations::term_weight(value, limit.saturating_sub(*bytes), &mut |_| Ok(()))?
                        .map(|(bytes, _)| bytes)
                }
                _ => Some(0),
            };
            let capacity = if entries.len() == entries.capacity() {
                entries.capacity().saturating_mul(2).max(4)
            } else {
                entries.capacity()
            };
            let projected = owned
                .and_then(|owned| bytes.checked_add(owned))
                .and_then(|bytes| {
                    capacity
                        .checked_mul(std::mem::size_of::<Option<Initializer>>())
                        .and_then(|slots| bytes.checked_add(slots))
                });
            if projected.is_some_and(|bytes| bytes <= *limit) {
                *bytes += owned.ok_or("missing initializer memory estimate")?;
                entries.push(initializer);
                return Ok(());
            }
            // Keep the old roots alive until every stored entry has been
            // independently restored and compared. Failure poisons the owner.
            let mut spilled = Spilled::new(self.scratch_limit)?;
            for entry in entries.iter() {
                spilled.push(entry)?;
            }
            self.storage = Storage::Spilled(spilled);
        }
        let Storage::Spilled(spilled) = &mut self.storage else {
            return Err("invalid declaration initializer storage state".into());
        };
        spilled.push(&initializer)
    }
    pub(super) fn get(
        &self,
        id: usize,
        expressions: &Expressions,
        names: &Names,
        levels: &Levels,
    ) -> Result<Option<T>> {
        if !self.enabled {
            self.healthy()?;
            return Ok(None);
        }
        match self.load(id)? {
            None => Ok(None),
            Some(Initializer::Source(expression_id)) => {
                expressions.get(expression_id, names, levels).map(Some)
            }
            Some(Initializer::Native(value)) => Ok(Some(value)),
        }
    }
    fn load(&self, id: usize) -> Result<Option<Initializer>> {
        self.healthy()?;
        // A caller's range error cannot corrupt otherwise valid storage.
        if id >= self.len() {
            return Err("declaration initializer index is out of range".into());
        }
        let result = match &self.storage {
            Storage::Memory { entries, .. } => Ok(entries[id].clone()),
            Storage::Spilled(spilled) => spilled.read_entry(id),
        };
        self.checked(result)
    }
    pub(super) fn len(&self) -> usize {
        match &self.storage {
            Storage::Memory { entries, .. } => entries.len(),
            Storage::Spilled(spilled) => spilled.count,
        }
    }
    fn healthy(&self) -> Result<()> {
        if self.poisoned.get() {
            Err("declaration initializer storage is invalid after a storage error".into())
        } else {
            Ok(())
        }
    }
    fn checked<V>(&self, result: Result<V>) -> Result<V> {
        if result.is_err() {
            self.poisoned.set(true);
        }
        result
    }
    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self.storage, Storage::Spilled(_))
    }
    #[cfg(test)]
    fn resident_bytes(&self) -> usize {
        match &self.storage {
            Storage::Memory { entries, bytes, .. } => {
                entries.capacity() * std::mem::size_of::<Option<Initializer>>() + bytes
            }
            Storage::Spilled(spilled) => {
                spilled.index.borrow().resident_bytes()
                    + spilled
                        .data
                        .borrow()
                        .as_ref()
                        .map_or(0, Spool::resident_bytes)
            }
        }
    }
    #[cfg(test)]
    fn corrupt_flushed_for_test(&mut self) -> Result<()> {
        let Storage::Spilled(spilled) = &mut self.storage else {
            return Err("test requires spilled initializers".into());
        };
        let mut data = spilled.data.borrow_mut();
        let spool = match data.as_mut() {
            Some(data) => data,
            None => spilled.index.get_mut(),
        };
        if spool.len() < PAGE as u64 {
            spool.append(&vec![0; PAGE - spool.len() as usize])?;
        }
        spool.overwrite_flushed(0, b"!")
    }
}

impl Spilled {
    fn new(scratch_limit: u64) -> Result<Self> {
        Ok(Self {
            index: RefCell::new(Spool::with_limit(scratch_limit)?),
            data: RefCell::new(None),
            count: 0,
            scratch_limit,
        })
    }
    fn push(&mut self, initializer: &Option<Initializer>) -> Result<()> {
        let mut index = [0u8; INDEX_BYTES];
        match initializer {
            None => (),
            Some(Initializer::Source(id)) => {
                index[0] = 1;
                let id = u64::try_from(*id).map_err(|_| "initializer source index overflow")?;
                index[8..16].copy_from_slice(&id.to_le_bytes());
            }
            Some(Initializer::Native(value)) => {
                let bytes = declarations::encode_term(value)?;
                if !(1..=MAX_NATIVE_BYTES).contains(&bytes.len()) {
                    return Err("initializer native record limit exceeded".into());
                }
                let data = self.data.get_mut();
                if data.is_none() {
                    *data = Some(Spool::with_limit(self.scratch_limit)?);
                }
                let offset = data
                    .as_mut()
                    .ok_or("missing initializer data file")?
                    .append(&bytes)?;
                index[0] = 2;
                index[8..16].copy_from_slice(&offset.to_le_bytes());
                index[16..].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
            }
        }
        let offset = self.index.get_mut().append(&index)?;
        if offset != self.count as u64 * INDEX_BYTES as u64 {
            return Err("initializer scratch index is not contiguous".into());
        }
        let decoded = self.read_entry(self.count)?;
        let same = match (initializer, &decoded) {
            (None, None) => true,
            (Some(Initializer::Source(a)), Some(Initializer::Source(b))) => a == b,
            (Some(Initializer::Native(a)), Some(Initializer::Native(b))) => {
                Kernel::with_budget(crate::ProofBudget::default()).same_syntax(a, b)?
            }
            _ => false,
        };
        if !same {
            return Err("initializer scratch round-trip mismatch".into());
        }
        // Publish the count only after data and directory read back exactly.
        self.count += 1;
        Ok(())
    }
    fn read_entry(&self, id: usize) -> Result<Option<Initializer>> {
        let mut index = [0; INDEX_BYTES];
        let offset = u64::try_from(id)
            .ok()
            .and_then(|id| id.checked_mul(INDEX_BYTES as u64))
            .ok_or("initializer index offset overflow")?;
        self.index.borrow_mut().read_into(offset, &mut index)?;
        if index[1..8] != [0; 7] {
            return Err("invalid initializer scratch padding".into());
        }
        let first = u64::from_le_bytes(index[8..16].try_into().unwrap());
        let second = u64::from_le_bytes(index[16..].try_into().unwrap());
        match (index[0], first, second) {
            (0, 0, 0) => Ok(None),
            (1, id, 0) => Ok(Some(Initializer::Source(
                usize::try_from(id).map_err(|_| "initializer source index overflow")?,
            ))),
            (2, offset, len) => {
                let len = usize::try_from(len).map_err(|_| "initializer native length overflow")?;
                let mut data = self.data.borrow_mut();
                let data = data.as_mut().ok_or("missing initializer data file")?;
                if !(1..=MAX_NATIVE_BYTES).contains(&len)
                    || offset
                        .checked_add(len as u64)
                        .is_none_or(|end| end > data.len())
                {
                    return Err("invalid initializer native scratch range".into());
                }
                let mut bytes = vec![0; len];
                for (page, chunk) in bytes.chunks_mut(PAGE).enumerate() {
                    data.read_into(offset + (page * PAGE) as u64, chunk)?;
                }
                declarations::decode_term(&bytes).map(|value| Some(Initializer::Native(value)))
            }
            _ => Err("invalid initializer scratch tag or fields".into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::{term, Kernel, Level, Term};
    use super::*;

    fn tables() -> (Expressions, Names, Levels) {
        (
            Expressions::with_limit(false, 0),
            Names::new(),
            Levels::new(),
        )
    }

    fn expression(
        expressions: &mut Expressions,
        expression: super::super::expressions::Expression,
        depth: usize,
        names: &Names,
        levels: &Levels,
    ) {
        expressions
            .push(expression, depth, 0, names, levels)
            .unwrap();
    }

    #[test]
    fn source_initializers_reconstruct_paged_expressions() {
        use super::super::expressions::Expression;
        let (mut expressions, names, levels) = tables();
        expression(&mut expressions, Expression::Sort(0), 1, &names, &levels);
        expression(&mut expressions, Expression::Var(0), 1, &names, &levels);
        expression(&mut expressions, Expression::Lam(0, 1), 2, &names, &levels);
        let mut initializers = Initializers::new(true);
        for id in 0..3 {
            initializers
                .push(id, Some(Initializer::Source(id)))
                .unwrap();
        }
        for id in 0..3 {
            let first = initializers
                .get(id, &expressions, &names, &levels)
                .unwrap()
                .unwrap();
            let weak = std::sync::Arc::downgrade(&first);
            drop(first);
            assert!(weak.upgrade().is_none());
            let second = initializers
                .get(id, &expressions, &names, &levels)
                .unwrap()
                .unwrap();
            let expected = match id {
                0 => term(Term::Sort(Level::number(0).unwrap())),
                1 => term(Term::Var(0)),
                2 => term(Term::Lam(
                    term(Term::Sort(Level::number(0).unwrap())),
                    term(Term::Var(0)),
                )),
                _ => unreachable!(),
            };
            assert!(Kernel::new().same_syntax(&second, &expected).unwrap());
        }
    }

    #[test]
    fn native_and_source_roots_are_distinct_storage_modes() {
        use super::super::expressions::Expression;
        let (mut expressions, names, levels) = tables();
        expression(&mut expressions, Expression::Var(0), 1, &names, &levels);
        let native = term(Term::Sort(Level::number(0).unwrap()));
        let mut initializers = Initializers::new(true);
        initializers
            .push(0, Some(Initializer::Native(native.clone())))
            .unwrap();
        initializers.push(1, Some(Initializer::Source(0))).unwrap();
        let got_native = initializers
            .get(0, &expressions, &names, &levels)
            .unwrap()
            .unwrap();
        let got_source = initializers
            .get(1, &expressions, &names, &levels)
            .unwrap()
            .unwrap();
        let mut kernel = Kernel::new();
        assert!(kernel.same_syntax(&got_native, &native).unwrap());
        assert!(!kernel.same_syntax(&got_native, &got_source).unwrap());
    }

    #[test]
    fn empty_slots_disabled_storage_and_indices() {
        let (expressions, names, levels) = tables();
        let mut empty = Initializers::new(true);
        assert!(empty.get(0, &expressions, &names, &levels).is_err());
        assert!(empty.push(1, None).is_err());
        empty.push(0, None).unwrap();
        assert!(empty
            .get(0, &expressions, &names, &levels)
            .unwrap()
            .is_none());

        let mut invalid_source = Initializers::new(true);
        invalid_source
            .push(0, Some(Initializer::Source(usize::MAX)))
            .unwrap();
        assert!(invalid_source
            .get(0, &expressions, &names, &levels)
            .is_err());

        let mut disabled = Initializers::new(false);
        disabled.push(100, None).unwrap();
        assert_eq!(disabled.len(), 0);
        assert!(disabled
            .get(0, &expressions, &names, &levels)
            .unwrap()
            .is_none());
        assert!(disabled
            .push(0, Some(Initializer::Native(term(Term::Var(0)))))
            .is_err());
    }

    #[test]
    fn declaration_capacity_is_checked() {
        let mut initializers = Initializers::new(true);
        for id in 0..super::super::MAX_DECLARATIONS {
            initializers.push(id, None).unwrap();
        }
        assert!(initializers
            .push(super::super::MAX_DECLARATIONS, None)
            .is_err());
    }

    #[test]
    fn selected_count_limit_caps_initializer_push() {
        let mut initializers = Initializers::with_count_limit(true, 1);
        initializers.push(0, None).unwrap();
        assert!(initializers.push(1, None).unwrap_err().contains("limit"));
        assert_eq!(initializers.len(), 1);
    }
}

#[cfg(test)]
#[path = "export_initializers_storage_tests.rs"]
mod storage_tests;
