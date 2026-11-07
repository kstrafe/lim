//! Invocation-local numeric candidate storage shared by name interning and
//! checked declaration lookup. Hashes select IDs only: every caller must
//! compare complete canonical identity bytes in its own protected inventory.
//! This index contains no proof judgment or declaration authority.
use super::{spool::Spool, Result};
use std::{
    cell::{Cell, RefCell},
    collections::{hash_map::RandomState, HashMap},
    hash::BuildHasher,
};

const BUCKETS: usize = 65_536;
const RECORD_BYTES: usize = 16;
const FILTER_WORDS: usize = 16_384;

pub(super) struct Index {
    storage: Storage,
    hasher: RandomState,
    count: usize,
    max_ids: usize,
    limit: usize,
    scratch_limit: u64,
    poisoned: Cell<bool>,
}

enum Storage {
    Memory {
        candidates: HashMap<u64, Ids>,
        owned_bytes: usize,
    },
    Spilled(RefCell<Spilled>),
}

/// Only bucket roots stay resident. Every immutable record links backwards
/// through the invocation-local, checksummed scratch file.
struct Spilled {
    heads: Vec<u32>,
    // Invocation-local negative filter only. A hit still requires protected
    // record reads and the caller's complete identity comparison.
    possible: Vec<u64>,
    records: Spool,
    count: u32,
}

enum Ids {
    One(usize),
    Many(Vec<usize>),
}

impl Ids {
    fn owned_bytes(&self) -> usize {
        match self {
            Self::One(_) => 0,
            Self::Many(ids) => ids.capacity().saturating_mul(std::mem::size_of::<usize>()),
        }
    }
    fn as_slice(&self) -> &[usize] {
        match self {
            Self::One(id) => std::slice::from_ref(id),
            Self::Many(ids) => ids,
        }
    }

    fn push(&mut self, id: usize) {
        match self {
            Self::One(first) => *self = Self::Many(vec![*first, id]),
            Self::Many(ids) => ids.push(id),
        }
    }
}

impl Index {
    pub(super) fn new(limit: usize, max_ids: usize) -> Self {
        Self::with_limits(limit, max_ids, super::super::scratch::DEFAULT_BYTES)
    }
    pub(super) fn with_limits(limit: usize, max_ids: usize, max_scratch_bytes: u64) -> Self {
        Self {
            storage: Storage::Memory {
                candidates: HashMap::new(),
                owned_bytes: 0,
            },
            hasher: RandomState::new(),
            count: 0,
            max_ids,
            limit,
            scratch_limit: max_scratch_bytes,
            poisoned: Cell::new(false),
        }
    }

    /// Seed a built-in root without performing fallible I/O in construction.
    pub(super) fn with_first(key: &str, limit: usize, max_ids: usize) -> Self {
        Self::with_first_limits(key, limit, max_ids, super::super::scratch::DEFAULT_BYTES)
    }
    pub(super) fn with_first_limits(
        key: &str,
        limit: usize,
        max_ids: usize,
        max_scratch_bytes: u64,
    ) -> Self {
        let mut result = Self::new(usize::MAX, max_ids);
        result
            .insert(key, 0)
            .expect("fresh memory-only candidate index accepts root");
        result.limit = limit;
        result.scratch_limit = max_scratch_bytes;
        result
    }

    pub(super) fn fingerprint(&self, key: &str) -> u64 {
        self.hasher.hash_one(key)
    }

    pub(super) fn find(
        &self,
        key: &str,
        matches: impl FnMut(usize) -> Result<bool>,
    ) -> Result<Option<usize>> {
        self.find_with_hash(self.fingerprint(key), matches)
    }

    pub(super) fn find_with_hash(
        &self,
        hash: u64,
        mut matches: impl FnMut(usize) -> Result<bool>,
    ) -> Result<Option<usize>> {
        self.healthy()?;
        let result = match &self.storage {
            Storage::Memory { candidates, .. } => {
                let mut found = Ok(None);
                if let Some(ids) = candidates.get(&hash) {
                    for &id in ids.as_slice() {
                        match matches(id) {
                            Ok(true) => {
                                found = Ok(Some(id));
                                break;
                            }
                            Ok(false) => {}
                            Err(error) => {
                                found = Err(error);
                                break;
                            }
                        }
                    }
                }
                found
            }
            Storage::Spilled(spilled) => spilled.borrow_mut().find(hash, &mut matches, self.count),
        };
        if result.is_err() {
            self.poisoned.set(true);
        }
        result
    }

    /// Append only after the caller has published the corresponding value.
    /// IDs must arrive in the same contiguous order as that value inventory.
    pub(super) fn insert(&mut self, key: &str, id: usize) -> Result<()> {
        let hash = self.hasher.hash_one(key);
        self.insert_with_hash(hash, id)
    }

    pub(super) fn insert_with_hash(&mut self, hash: u64, id: usize) -> Result<()> {
        self.healthy()?;
        if id != self.count {
            return Err("candidate IDs must be contiguous".into());
        }
        if self.count >= self.max_ids {
            return Err("candidate count limit exceeded".into());
        }
        let result = self.insert_candidate(hash, id);
        if result.is_err() {
            self.poisoned.set(true);
            return result;
        }
        self.count += 1;
        Ok(())
    }

    fn insert_candidate(&mut self, hash: u64, id: usize) -> Result<()> {
        let Storage::Memory {
            candidates,
            owned_bytes,
        } = &mut self.storage
        else {
            let Storage::Spilled(spilled) = &mut self.storage else {
                unreachable!()
            };
            return spilled.get_mut().push(hash, id);
        };
        match candidates.get_mut(&hash) {
            Some(ids) => {
                *owned_bytes -= ids.owned_bytes();
                ids.push(id);
                *owned_bytes = owned_bytes.saturating_add(ids.owned_bytes());
            }
            None => {
                candidates.insert(hash, Ids::One(id));
            }
        }
        // Conservatively cover spare hash buckets/control bytes as well as
        // collision vectors. Migration retains the old map until every record
        // has round-tripped through the protected store.
        let bytes = candidates
            .capacity()
            .saturating_mul(std::mem::size_of::<(u64, Ids)>() + 1)
            .saturating_mul(2)
            .saturating_add(*owned_bytes);
        if bytes <= self.limit {
            return Ok(());
        }
        let mut spilled = Spilled::new(self.scratch_limit)?;
        for (&hash, ids) in candidates.iter() {
            for &id in ids.as_slice() {
                spilled.push(hash, id)?;
            }
        }
        if spilled.count as usize != self.count + 1 {
            return Err("candidate scratch count mismatch".into());
        }
        self.storage = Storage::Spilled(RefCell::new(spilled));
        Ok(())
    }

    pub(super) fn healthy(&self) -> Result<()> {
        if self.poisoned.get() {
            Err("candidate index is invalid after a storage error".into())
        } else {
            Ok(())
        }
    }

    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self.storage, Storage::Spilled(_))
    }
    #[cfg(test)]
    pub(super) fn count(&self) -> usize {
        self.count
    }
    #[cfg(test)]
    pub(super) fn set_count_for_test(&mut self, count: usize) {
        self.count = count;
    }
    #[cfg(test)]
    pub(super) fn memory_ids(&self, hash: u64) -> Option<Vec<usize>> {
        let Storage::Memory { candidates, .. } = &self.storage else {
            return None;
        };
        candidates.get(&hash).map(|ids| ids.as_slice().to_vec())
    }
    #[cfg(test)]
    pub(super) fn corrupt_first_flushed_record(&mut self) -> Result<u64> {
        let Storage::Spilled(spilled) = &mut self.storage else {
            return Err("candidate index is not spilled".into());
        };
        let spilled = spilled.get_mut();
        let mut record = [0; RECORD_BYTES];
        spilled.records.read_into(0, &mut record)?;
        spilled.records.overwrite_flushed(8, &[record[8] ^ 128])?;
        Ok(u64::from_le_bytes(record[..8].try_into().unwrap()))
    }
    #[cfg(test)]
    pub(super) fn corrupt_root(&mut self, hash: u64, node: u32) {
        let Storage::Spilled(spilled) = &mut self.storage else {
            panic!("candidate index is not spilled");
        };
        spilled.get_mut().heads[hash as usize & (BUCKETS - 1)] = node;
    }
}

impl Spilled {
    fn new(scratch_limit: u64) -> Result<Self> {
        Ok(Self {
            heads: vec![0; BUCKETS],
            possible: vec![0; FILTER_WORDS],
            records: Spool::with_limit(scratch_limit)?,
            count: 0,
        })
    }

    fn push(&mut self, hash: u64, id: usize) -> Result<()> {
        let id = u32::try_from(id).map_err(|_| "candidate ID overflow")?;
        let node = self
            .count
            .checked_add(1)
            .ok_or("candidate scratch count overflow")?;
        let bucket = hash as usize & (BUCKETS - 1);
        let next = self.heads[bucket];
        let mut bytes = [0; RECORD_BYTES];
        bytes[..8].copy_from_slice(&hash.to_le_bytes());
        bytes[8..12].copy_from_slice(&id.to_le_bytes());
        bytes[12..].copy_from_slice(&next.to_le_bytes());
        let expected = self.count as u64 * RECORD_BYTES as u64;
        if self.records.append(&bytes)? != expected {
            return Err("candidate scratch records are not contiguous".into());
        }
        let mut restored = [0; RECORD_BYTES];
        self.records.read_into(expected, &mut restored)?;
        if restored != bytes {
            return Err("candidate scratch round-trip mismatch".into());
        }
        self.heads[bucket] = node;
        self.count = node;
        for bit in filter_bits(hash) {
            self.possible[bit / 64] |= 1u64 << (bit % 64);
        }
        Ok(())
    }

    fn may_contain(&self, hash: u64) -> bool {
        filter_bits(hash)
            .into_iter()
            .all(|bit| self.possible[bit / 64] & (1u64 << (bit % 64)) != 0)
    }

    fn find(
        &mut self,
        hash: u64,
        matches: &mut impl FnMut(usize) -> Result<bool>,
        count: usize,
    ) -> Result<Option<usize>> {
        if self.count as usize != count
            || self.records.len() != self.count as u64 * RECORD_BYTES as u64
        {
            return Err("candidate scratch count mismatch".into());
        }
        if !self.may_contain(hash) {
            return Ok(None);
        }
        let bucket = hash as usize & (BUCKETS - 1);
        let mut node = self.heads[bucket];
        let mut found = None;
        while node != 0 {
            if node > self.count {
                return Err("invalid candidate scratch link".into());
            }
            let mut bytes = [0; RECORD_BYTES];
            self.records
                .read_into((node as u64 - 1) * RECORD_BYTES as u64, &mut bytes)?;
            let candidate_hash = u64::from_le_bytes(bytes[..8].try_into().unwrap());
            let id = u32::from_le_bytes(bytes[8..12].try_into().unwrap()) as usize;
            let next = u32::from_le_bytes(bytes[12..].try_into().unwrap());
            if next >= node || id >= count || candidate_hash as usize & (BUCKETS - 1) != bucket {
                return Err("invalid candidate scratch record".into());
            }
            if candidate_hash == hash && matches(id)? {
                // The resident collision vector searches in insertion order.
                // Migration order and backwards links must not change which
                // exact match is returned if a caller supplies duplicate keys.
                found = Some(found.map_or(id, |previous: usize| previous.min(id)));
            }
            node = next;
        }
        Ok(found)
    }
}

fn filter_bits(hash: u64) -> [usize; 4] {
    let mask = FILTER_WORDS * 64 - 1;
    let start = hash as usize;
    let step = (hash >> 32) as usize | 1;
    std::array::from_fn(|index| start.wrapping_add(step.wrapping_mul(index)) & mask)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selected_scratch_capacity_failure_is_reported() {
        let mut index = Index::with_limits(0, 8, 8);
        assert!(index.insert("id", 0).is_err());
        assert_eq!(index.count(), 0);
    }

    #[test]
    fn first_root_limit_arguments_keep_root_resident_until_later_spill() {
        let mut index = Index::with_first_limits("root", 0, 8, 8);
        assert!(!index.is_spilled());
        assert!(index.insert("next", 1).is_err());
        assert_eq!(index.count(), 1);
    }

    #[test]
    fn candidate_storage_has_bounded_resident_state_as_numeric_records_grow() {
        // Storage stress only: these numbers are not admitted declarations.
        // Both public raw replay count caps remain unchanged.
        const COUNT: usize = 1_052_234;
        let mut spilled = Spilled::new(super::super::scratch::DEFAULT_BYTES).unwrap();
        for id in 0..COUNT {
            spilled
                .push((id as u64).wrapping_mul(0x9e3779b97f4a7c15), id)
                .unwrap();
        }
        spilled.records.clear_cache();
        assert_eq!(
            spilled.find(0, &mut |id| Ok(id == 0), COUNT).unwrap(),
            Some(0)
        );
        assert_eq!(spilled.heads.len(), BUCKETS);
        assert_eq!(spilled.records.len(), COUNT as u64 * RECORD_BYTES as u64);
        let retained = spilled.heads.capacity() * std::mem::size_of::<u32>()
            + spilled.possible.capacity() * std::mem::size_of::<u64>()
            + spilled.records.resident_bytes();
        assert!(
            retained < 1024 * 1024,
            "candidate storage retained {retained} bytes"
        );
    }

    #[test]
    fn callbacks_errors_poison_both_resident_and_paged_indexes() {
        for limit in [0, usize::MAX] {
            let mut index = Index::new(limit, 8);
            index.insert("key", 0).unwrap();
            assert_eq!(
                index
                    .find("key", |_| Err("untrusted value".into()))
                    .unwrap_err(),
                "untrusted value"
            );
            assert!(index
                .find("missing", |_| Ok(false))
                .unwrap_err()
                .contains("invalid after"));
            assert!(index.insert("later", 1).is_err());
        }
    }

    #[test]
    fn caller_count_limits_are_independent_and_root_seeding_needs_no_scratch() {
        let mut small = Index::with_first("root", 0, 2);
        assert!(!small.is_spilled());
        assert_eq!(small.find("root", |id| Ok(id == 0)).unwrap(), Some(0));
        small.insert("second", 1).unwrap();
        assert!(small.is_spilled());
        assert!(small
            .insert("third", 2)
            .unwrap_err()
            .contains("count limit"));
        assert_eq!(small.find("root", |id| Ok(id == 0)).unwrap(), Some(0));
        let mut large = Index::new(usize::MAX, 3);
        for id in 0..3 {
            large.insert(&format!("n{id}"), id).unwrap();
        }
        assert_eq!(large.count(), 3);
    }

    #[test]
    fn default_budget_migrates_before_all_name_candidates_accumulate_in_memory() {
        let mut index = Index::new(1024 * 1024, 100_000);
        for id in 0..100_000 {
            index.insert(&format!("name-{id}"), id).unwrap();
        }
        assert!(index.is_spilled());
        let Storage::Spilled(spilled) = &index.storage else {
            unreachable!()
        };
        let spilled = spilled.borrow();
        let resident = spilled.heads.capacity() * std::mem::size_of::<u32>()
            + spilled.possible.capacity() * std::mem::size_of::<u64>()
            + spilled.records.resident_bytes();
        assert!(
            resident < 1024 * 1024,
            "retained numeric index capacity {resident}"
        );
        drop(spilled);
        for id in (0..100_000).step_by(997) {
            assert_eq!(
                index
                    .find(&format!("name-{id}"), |candidate| Ok(candidate == id))
                    .unwrap(),
                Some(id)
            );
        }
    }

    #[test]
    fn negative_filter_never_discards_inserted_hashes_and_hits_prove_nothing() {
        let mut spilled = Spilled::new(super::super::scratch::DEFAULT_BYTES).unwrap();
        for id in 0..100_000 {
            spilled
                .push((id as u64).wrapping_mul(0x9e3779b97f4a7c15), id)
                .unwrap();
        }
        for id in 0..100_000 {
            assert!(spilled.may_contain((id as u64).wrapping_mul(0x9e3779b97f4a7c15)));
        }

        let mut collision = Spilled::new(super::super::scratch::DEFAULT_BYTES).unwrap();
        collision.push(7, 0).unwrap();
        let other = 7 | (1 << 20);
        assert!(collision.may_contain(other));
        assert_eq!(
            collision
                .find(
                    other,
                    &mut |_| panic!("filter hit is not a full hash match"),
                    1
                )
                .unwrap(),
            None
        );
        collision.push(other, 1).unwrap();
        assert_eq!(
            collision.find(other, &mut |id| Ok(id == 1), 2).unwrap(),
            Some(1)
        );
        assert_eq!(collision.find(other, &mut |_| Ok(false), 2).unwrap(), None);
    }
}
