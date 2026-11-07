//! Resolve stable native declaration spellings from protected report IDs.
//! Cached spellings are syntax metadata, never typing judgments.
use super::*;
use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    collections::VecDeque,
};

const CACHE_ENTRIES: usize = 32;
const CACHE_BYTES: usize = 64 * 1024;

pub(super) struct Names<'a> {
    inventory: &'a inventory::Inventory,
    checked: &'a checked::Index,
    cache: RefCell<Cache>,
    poisoned: Cell<bool>,
}
#[derive(Default)]
struct Cache {
    entries: VecDeque<Entry>,
    bytes: usize,
}
struct Entry {
    id: usize,
    original: String,
    native: String,
}
impl Entry {
    fn weight(&self) -> usize {
        self.original.capacity() + self.native.capacity() + std::mem::size_of::<Self>()
    }
}
impl Cache {
    fn find(&mut self, mut matches: impl FnMut(&Entry) -> bool) -> Option<&Entry> {
        let at = self.entries.iter().position(&mut matches)?;
        let entry = self.entries.remove(at)?;
        self.entries.push_back(entry);
        self.entries.back()
    }
    fn remember(&mut self, entry: Entry) {
        if let Some(at) = self.entries.iter().position(|old| old.id == entry.id) {
            let old = self.entries.remove(at).unwrap();
            self.bytes -= old.weight();
        }
        let weight = entry.weight();
        if weight > CACHE_BYTES {
            return;
        }
        while self.entries.len() >= CACHE_ENTRIES || self.bytes + weight > CACHE_BYTES {
            let old = self.entries.pop_front().unwrap();
            self.bytes -= old.weight();
        }
        self.bytes += weight;
        self.entries.push_back(entry);
    }
}

impl<'a> Names<'a> {
    pub(super) fn new(inventory: &'a inventory::Inventory, checked: &'a checked::Index) -> Self {
        Self {
            inventory,
            checked,
            cache: RefCell::new(Cache::default()),
            poisoned: Cell::new(false),
        }
    }
    pub(super) fn len(&self) -> usize {
        self.inventory.len()
    }
    fn healthy(&self) -> Result<()> {
        if self.poisoned.get() {
            Err("native declaration names are invalid after a storage error".into())
        } else {
            self.checked.healthy()
        }
    }
    fn check<T>(&self, result: Result<T>) -> Result<T> {
        if result.is_err() {
            self.poisoned.set(true);
        }
        result
    }
    fn load(&self, id: usize) -> Result<Entry> {
        let result = self.inventory.name_identity(id);
        let (display, original) = self.check(result)?;
        Ok(Entry {
            id,
            original,
            native: native_name(id, &display),
        })
    }
    pub(super) fn forward(&self, original: &str) -> Result<String> {
        self.healthy()?;
        if let Some(native) = self
            .cache
            .borrow_mut()
            .find(|entry| entry.original == original)
            .map(|entry| entry.native.clone())
        {
            return Ok(native);
        }
        let id = self
            .check(self.checked.find(original, self.inventory))?
            .ok_or_else(|| {
                format!("source translation encountered an unmapped declaration {original:?}")
            })?;
        let entry = self.load(id)?;
        if entry.original != original {
            return self.check(Err(
                "native declaration identity differs from its index".into()
            ));
        }
        let native = entry.native.clone();
        self.cache.borrow_mut().remember(entry);
        Ok(native)
    }
    fn original_id(&self, native: &str) -> Result<usize> {
        self.healthy()?;
        if let Some(id) = self
            .cache
            .borrow_mut()
            .find(|entry| entry.native == native)
            .map(|entry| entry.id)
        {
            return Ok(id);
        }
        let id = native
            .strip_prefix("lean-")
            .and_then(|tail| tail.split_once('-'))
            .and_then(|(digits, _)| {
                if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
                    None
                } else {
                    digits.parse::<usize>().ok()
                }
            })
            .ok_or("unknown native declaration in translation")?;
        if id >= self.len() {
            return Err("unknown native declaration in translation".into());
        }
        let entry = self.load(id)?;
        if entry.native != native {
            return Err("unknown native declaration in translation".into());
        }
        self.cache.borrow_mut().remember(entry);
        Ok(id)
    }
    pub(super) fn original(&self, native: &str) -> Result<String> {
        let id = self.original_id(native)?;
        if let Some(original) = self
            .cache
            .borrow_mut()
            .find(|entry| entry.id == id)
            .map(|entry| entry.original.clone())
        {
            return Ok(original);
        }
        Ok(self.load(id)?.original)
    }
    pub(super) fn record(&self, native: &str) -> Result<(usize, Cow<'_, LeanDeclarationReport>)> {
        let id = self.original_id(native)?;
        let record = self.check(self.inventory.get(id))?;
        if native_name(id, &record.name) != native {
            return self.check(Err("native declaration name differs from its report".into()));
        }
        Ok((id, record))
    }
}

fn native_name(id: usize, display: &str) -> String {
    let display = display
        .chars()
        .take(64)
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '-'
            }
        })
        .collect::<String>();
    format!("lean-{id}-{display}")
}

#[cfg(test)]
mod tests {
    use super::*;
    fn setup(limit: usize, count: usize, long: bool) -> (inventory::Inventory, checked::Index) {
        let mut inventory = inventory::Inventory::with_limit(limit);
        let mut index = checked::Index::with_limit(limit);
        for id in 0..count {
            let report = LeanDeclarationReport {
                name: format!("命題.λ.{}.{id}", "N".repeat(70)),
                identity: format!(
                    "id.{}.{id}",
                    if long {
                        "x".repeat(12_000)
                    } else {
                        String::new()
                    }
                ),
                kind: "theorem".into(),
                line: id + 1,
                sha256: "ab".repeat(32),
                dependencies: vec![],
            };
            inventory.push(report.clone()).unwrap();
            index.insert(&report.identity, id).unwrap();
        }
        (inventory, index)
    }
    #[test]
    fn eager_and_paged_names_round_trip_truncated_colliding_displays_exactly() {
        for limit in [usize::MAX, 0] {
            let (inventory, index) = setup(limit, 80, false);
            let names = Names::new(&inventory, &index);
            for id in (0..80).rev().chain(0..80) {
                let report = inventory.get(id).unwrap();
                let native = native_name(id, &report.name);
                assert_eq!(names.forward(&report.identity).unwrap(), native);
                assert_eq!(names.original(&native).unwrap(), report.identity);
                let (actual_id, actual) = names.record(&native).unwrap();
                assert_eq!(actual_id, id);
                assert_eq!(actual.as_ref(), report.as_ref());
            }
            assert!(names.cache.borrow().entries.len() <= CACHE_ENTRIES);
            assert!(names.cache.borrow().bytes <= CACHE_BYTES);
        }
    }
    #[test]
    fn numeric_prefix_alone_does_not_identify_a_native_declaration() {
        let (inventory, index) = setup(0, 1, false);
        let names = Names::new(&inventory, &index);
        let native = names.forward(&inventory.get(0).unwrap().identity).unwrap();
        for invalid in [
            "native".into(),
            "lean-0-Wrong".into(),
            "lean-1-Wrong".into(),
            "lean-184467440737095516160-Wrong".into(),
            native.replacen("lean-0-", "lean-00-", 1),
            native.replacen("lean-0-", "lean-+0-", 1),
        ] {
            assert!(names.original(&invalid).is_err(), "{invalid}");
        }
        assert_eq!(
            names.original(&native).unwrap(),
            inventory.get(0).unwrap().identity
        );
    }
    #[test]
    fn long_originals_evict_within_the_cache_budget() {
        let (inventory, index) = setup(0, 80, true);
        let names = Names::new(&inventory, &index);
        for id in 0..80 {
            let report = inventory.get(id).unwrap();
            let native = names.forward(&report.identity).unwrap();
            assert_eq!(names.original(&native).unwrap(), report.identity);
            assert!(names.cache.borrow().bytes <= CACHE_BYTES);
        }
        assert!(names.cache.borrow().entries.len() < CACHE_ENTRIES);
        let first = inventory.get(0).unwrap();
        assert_eq!(
            names.forward(&first.identity).unwrap(),
            native_name(0, &first.name)
        );
    }
    #[test]
    fn a_failed_lookup_cannot_turn_into_missing_metadata_or_a_cache_hit() {
        let inventory = inventory::Inventory::new();
        let mut index = checked::Index::new();
        index.insert("absent", 0).unwrap();
        let names = Names::new(&inventory, &index);
        assert!(names.forward("absent").is_err());
        assert!(names
            .forward("other")
            .unwrap_err()
            .contains("invalid after"));
        assert!(names.original("lean-0-absent").is_err());
    }
    #[test]
    fn cached_aliases_do_not_survive_an_observed_candidate_storage_failure() {
        let (inventory, index) = setup(0, 1, false);
        let original = inventory.get(0).unwrap().identity.clone();
        let names = Names::new(&inventory, &index);
        let native = names.forward(&original).unwrap();
        assert!(index.find(&original, &inventory::Inventory::new()).is_err());
        assert!(names.forward(&original).is_err());
        assert!(names.original(&native).is_err());
        assert!(names.record(&native).is_err());
    }
}
