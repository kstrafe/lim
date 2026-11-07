//! Phase-local syntax substitutions for already checked global bodies.
//! Every caller still retrieves and validates its declaration before reuse.
use super::*;
use std::sync::Weak;

const ENTRIES: usize = 64;
// Covers the complete bounded slot vector and source-address index, including
// hash table spare capacity. Reserve it before either table is allocated.
const TABLE_BYTES: usize = ENTRIES * 512;
const BYTES: usize = 2 * 1024 * 1024 - TABLE_BYTES;
const KEY_BYTES: usize = 64 * 1024;

#[derive(Default)]
pub(super) struct Cache {
    entries: Vec<Entry>,
    index: HashMap<usize, u64>,
    bytes: usize,
    clock: usize,
}
struct Entry {
    source: Weak<TermNode>,
    map: HashMap<String, Level>,
    height: usize,
    value: T,
    bytes: usize,
    age: usize,
}

impl Cache {
    #[cfg(test)]
    pub(super) fn usage(&self) -> (usize, usize) {
        assert_eq!(
            self.index
                .values()
                .map(|bits| bits.count_ones() as usize)
                .sum::<usize>(),
            self.entries.len()
        );
        for (source, bits) in &self.index {
            let mut slots = *bits;
            while slots != 0 {
                let slot = slots.trailing_zeros() as usize;
                assert_eq!(self.entries[slot].source.as_ptr() as usize, *source);
                slots &= slots - 1;
            }
        }
        (
            self.entries.len(),
            self.bytes
                + if self.entries.capacity() == 0 {
                    0
                } else {
                    TABLE_BYTES
                },
        )
    }
    pub(super) fn clear(&mut self) {
        *self = Self::default();
    }
    fn get(&mut self, source: &T, map: &HashMap<String, Level>) -> (Option<(T, usize)>, usize) {
        // The owned Weak keeps a dead source address from being reused. Dead
        // entries cannot match a live input and leave through bounded eviction.
        let mut slots = self
            .index
            .get(&(Arc::as_ptr(source) as usize))
            .copied()
            .unwrap_or(0);
        let mut work = 1;
        while slots != 0 {
            let slot = slots.trailing_zeros() as usize;
            let entry = &mut self.entries[slot];
            work += 1 + map.len();
            if entry.source.as_ptr() == Arc::as_ptr(source) && &entry.map == map {
                self.clock = self.clock.saturating_add(1);
                entry.age = self.clock;
                return (Some((entry.value.clone(), entry.height)), work);
            }
            slots &= slots - 1;
        }
        (None, work)
    }
    fn remove_index(&mut self, source: usize, slot: usize) {
        let bits = self
            .index
            .get_mut(&source)
            .expect("indexed specialization slot");
        *bits &= !(1u64 << slot);
        if *bits == 0 {
            self.index.remove(&source);
        }
    }
    fn remove(&mut self, slot: usize) {
        let last = self.entries.len() - 1;
        let old = self.entries.swap_remove(slot);
        self.bytes -= old.bytes;
        self.remove_index(old.source.as_ptr() as usize, slot);
        if slot != last {
            let moved = self.entries[slot].source.as_ptr() as usize;
            self.remove_index(moved, last);
            *self.index.entry(moved).or_default() |= 1u64 << slot;
        }
    }
    fn insert(&mut self, mut entry: Entry) -> usize {
        let mut work = 1;
        while self.entries.len() >= ENTRIES || self.bytes.saturating_add(entry.bytes) > BYTES {
            work += self.entries.len();
            let Some((slot, _)) = self.entries.iter().enumerate().min_by_key(|(_, e)| e.age) else {
                return work;
            };
            self.remove(slot);
            work += 3;
        }
        self.clock = self.clock.saturating_add(1);
        entry.age = self.clock;
        self.bytes += entry.bytes;
        *self
            .index
            .entry(entry.source.as_ptr() as usize)
            .or_default() |= 1u64 << self.entries.len();
        self.entries.push(entry);
        work
    }
}

fn key_weight(map: &HashMap<String, Level>) -> usize {
    map.iter().fold(
        512usize.saturating_add(map.capacity().saturating_mul(128)),
        |n, (name, level)| {
            n.saturating_add(name.capacity())
                .saturating_add(level.storage_memory_weight())
        },
    )
}

impl Kernel {
    /// No conversion judgment or declaration is cached here. The full map and
    /// original root identify a pure substitution. Its complete checked height
    /// verifies the depth allowance at each use, including shared descendants.
    pub(super) fn specialized_universes(
        &mut self,
        source: &T,
        map: &HashMap<String, Level>,
        depth: usize,
    ) -> Result<T> {
        self.charge_transformation(0)?;
        // Optional probes have a narrower depth allowance. A substitution
        // completed outside that probe cannot skip its descendant checks.
        // A body freshly decoded without resident ownership cannot retain its
        // source identity after this call. Do not allocate entries that cannot
        // be reused, including the deliberately zero-residency replay path.
        if self.reduction_probe_budget.is_some() || Arc::strong_count(source) == 1 {
            return self.universes(source, map, depth);
        }
        let key_bytes = key_weight(map);
        if key_bytes > KEY_BYTES {
            return self.universes(source, map, depth);
        }
        let (found, work) = self.specializations.get(source, map);
        self.charge_work(work)?;
        if let Some((value, height)) = found {
            if depth.saturating_add(height.saturating_sub(1)) <= DEPTH {
                self.tick(depth)?;
                return Ok(value);
            }
            // Preserve the original traversal's refusal and diagnostics.
            return self.universes(source, map, depth);
        }
        let before = self.work;
        let value = self.universes(source, map, depth)?;
        let visits = self.work.saturating_sub(before);
        // Universe-independent syntax is already reusable through its original
        // root. Retaining another identity entry only adds sizing and lookup
        // work to this constant-time substitution.
        if Arc::ptr_eq(source, &value) {
            return Ok(value);
        }
        let reserve = key_bytes.saturating_add(if self.specializations.entries.capacity() == 0 {
            TABLE_BYTES
        } else {
            0
        });
        if self
            .budget
            .phase_bytes()
            .saturating_sub(self.transformed_bytes)
            < reserve.saturating_add(visits.saturating_mul(512))
            || self.budget.work().saturating_sub(self.work)
                < visits
                    .saturating_mul(2)
                    .saturating_add(ENTRIES * (ENTRIES + 4))
        {
            return Ok(value);
        }
        // Substitution can share large universe-independent subtrees without
        // visiting them. Its visit count no longer bounds a complete sizing
        // walk, so enforce the reserved allowance as an optional probe. A
        // declined cache insertion must not reject the completed substitution;
        // all work and allocation already spent remain charged.
        let weight = self.reduction_probe_limits(
            depth,
            visits.saturating_mul(2),
            visits.saturating_mul(512),
            |kernel| {
                declarations::term_weight(&value, BYTES.saturating_sub(key_bytes), &mut |bytes| {
                    kernel.tick(0)?;
                    kernel.charge_transformation(bytes)
                })
            },
        )?;
        let Some((weight, height)) = weight.flatten() else {
            return Ok(value);
        };
        if self
            .budget
            .phase_bytes()
            .saturating_sub(self.transformed_bytes)
            < reserve
        {
            return Ok(value);
        }
        self.charge_transformation(key_bytes)?;
        if self.specializations.entries.capacity() == 0 {
            self.charge_transformation(TABLE_BYTES)?;
            self.specializations.entries = Vec::with_capacity(ENTRIES);
            self.specializations.index = HashMap::with_capacity(ENTRIES);
        }
        let work = self.specializations.insert(Entry {
            source: Arc::downgrade(source),
            map: map.clone(),
            height,
            value: value.clone(),
            bytes: weight.saturating_add(key_bytes),
            age: 0,
        });
        self.charge_work(work)?;
        Ok(value)
    }
}
