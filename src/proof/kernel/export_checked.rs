//! Invocation-local index for already checked declaration identities.
//!
//! Candidate hashes select IDs only. Complete canonical key bytes are always
//! compared in `Inventory`, including when either index has spilled.
use super::{candidates, inventory::Inventory, Result};

const MEMORY_BYTES: usize = 1024 * 1024;

pub(super) struct Index {
    candidates: candidates::Index,
}

impl Index {
    pub(super) fn new() -> Self {
        Self::with_limit(MEMORY_BYTES)
    }
    pub(super) fn with_limit(limit: usize) -> Self {
        Self {
            candidates: candidates::Index::new(limit, super::MAX_DECLARATIONS),
        }
    }
    pub(super) fn with_limits(max_count: usize, max_scratch_bytes: u64) -> Self {
        Self {
            candidates: candidates::Index::with_limits(MEMORY_BYTES, max_count, max_scratch_bytes),
        }
    }
    pub(super) fn with_count_limit(max_count: usize) -> Self {
        if max_count == super::MAX_DECLARATIONS {
            Self::new()
        } else {
            Self {
                candidates: candidates::Index::new(MEMORY_BYTES, max_count),
            }
        }
    }
    pub(super) fn find(&self, key: &str, inventory: &Inventory) -> Result<Option<usize>> {
        self.candidates
            .find(key, |id| inventory.matches_identity(id, key))
    }
    /// Add a report only after checking succeeds and it has been appended to
    /// the inventory. IDs therefore arrive in inventory order.
    pub(super) fn insert(&mut self, key: &str, id: usize) -> Result<()> {
        self.candidates.insert(key, id)
    }
    pub(super) fn healthy(&self) -> Result<()> {
        self.candidates.healthy()
    }
    #[cfg(test)]
    fn find_with_hash(&self, hash: u64, key: &str, inventory: &Inventory) -> Result<Option<usize>> {
        self.candidates
            .find_with_hash(hash, |id| inventory.matches_identity(id, key))
    }
    #[cfg(test)]
    fn insert_with_hash(&mut self, hash: u64, id: usize) -> Result<()> {
        self.candidates.insert_with_hash(hash, id)
    }
    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        self.candidates.is_spilled()
    }
    #[cfg(test)]
    fn candidate_count(&self) -> usize {
        self.candidates.count()
    }
    #[cfg(test)]
    fn set_candidate_count(&mut self, count: usize) {
        self.candidates.set_count_for_test(count);
    }
    #[cfg(test)]
    fn corrupt_first_flushed_record(&mut self) -> Result<u64> {
        self.candidates.corrupt_first_flushed_record()
    }
    #[cfg(test)]
    fn corrupt_root(&mut self, hash: u64, node: u32) {
        self.candidates.corrupt_root(hash, node);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::kernel::LeanDeclarationReport;

    fn report(name: &str, identity: &str) -> LeanDeclarationReport {
        LeanDeclarationReport {
            name: name.into(),
            identity: identity.into(),
            kind: "theorem".into(),
            line: 1,
            sha256: "a1".repeat(32),
            dependencies: Vec::new(),
        }
    }

    fn inventory_with(limit: usize, declarations: &[(&str, &str)]) -> Inventory {
        let mut inventory = Inventory::with_limit(limit);
        for &(name, identity) in declarations {
            inventory.push(report(name, identity)).unwrap();
        }
        inventory
    }

    #[test]
    fn forced_hash_collision_still_checks_exact_identity() {
        let inventory = inventory_with(
            usize::MAX,
            &[("Alpha display", "id.a"), ("Beta display", "id.b")],
        );
        let mut index = Index::new();
        index.insert_with_hash(7, 0).unwrap();
        index.insert_with_hash(7, 1).unwrap();
        assert_eq!(
            index.find_with_hash(7, "id.a", &inventory).unwrap(),
            Some(0)
        );
        assert_eq!(
            index.find_with_hash(7, "id.b", &inventory).unwrap(),
            Some(1)
        );
        assert_eq!(
            index
                .find_with_hash(7, "Alpha display", &inventory)
                .unwrap(),
            None
        );
        assert_eq!(
            index.find_with_hash(7, "id.missing", &inventory).unwrap(),
            None
        );
    }

    #[test]
    fn absent_names_and_bad_id_sequences_are_rejected() {
        let inventory = inventory_with(usize::MAX, &[("Present display", "id.present")]);
        let mut index = Index::new();
        index.insert("id.present", 0).unwrap();
        assert_eq!(index.find("id.missing", &inventory).unwrap(), None);
        assert_eq!(index.find("Present display", &inventory).unwrap(), None);
        assert!(index.insert("duplicate", 0).is_err());
        assert!(index.insert("future", 2).is_err());
        assert_eq!(index.candidate_count(), 1);
    }

    #[test]
    fn invalid_inventory_references_propagate_as_errors() {
        let inventory = Inventory::new();
        let mut index = Index::new();
        index.insert_with_hash(11, 0).unwrap();
        assert!(index.find_with_hash(11, "name", &inventory).is_err());
    }

    #[test]
    fn selected_candidate_scratch_limit_rejects_report_id() {
        let inventory = inventory_with(usize::MAX, &[("display", "canonical.identity")]);
        let mut index = Index {
            candidates: candidates::Index::with_limits(0, 8, 8),
        };
        assert!(index.insert("canonical.identity", 0).is_err());
        assert_eq!(index.candidate_count(), 0);
        let mut ordinary = Index::new();
        ordinary.insert("canonical.identity", 0).unwrap();
        assert_eq!(
            ordinary.find("canonical.identity", &inventory).unwrap(),
            Some(0)
        );
    }

    #[test]
    fn exact_identity_works_with_spilled_cold_inventory_pages() {
        let declarations = (0..33)
            .map(|id| {
                (
                    format!("display-{id}"),
                    format!("id.{id:02}.{}", "x".repeat(12_000)),
                )
            })
            .collect::<Vec<_>>();
        let refs = declarations
            .iter()
            .map(|(display, identity)| (display.as_str(), identity.as_str()))
            .collect::<Vec<_>>();
        let inventory = inventory_with(0, &refs);
        assert!(inventory.is_spilled());
        let mut index = Index::new();
        for (id, (_, key)) in declarations.iter().enumerate() {
            index.insert(key, id).unwrap();
        }
        assert_eq!(index.find(&declarations[0].1, &inventory).unwrap(), Some(0));
        assert_eq!(
            index.find(&declarations[32].1, &inventory).unwrap(),
            Some(32)
        );
        assert_eq!(index.find(&declarations[0].0, &inventory).unwrap(), None);
    }

    #[test]
    fn retained_index_state_contains_only_numeric_ids() {
        let inventory = inventory_with(
            usize::MAX,
            &[("Shared display", "id.one"), ("Shared display", "id.two")],
        );
        let mut index = Index::new();
        let hash = index.candidates.fingerprint("unused");
        index.insert_with_hash(hash, 0).unwrap();
        index.insert_with_hash(hash, 1).unwrap();
        assert_eq!(index.candidates.memory_ids(hash), Some(vec![0, 1]));
        assert_eq!(
            index.find_with_hash(hash, "id.one", &inventory).unwrap(),
            Some(0)
        );
        assert_eq!(
            index
                .find_with_hash(hash, "Shared display", &inventory)
                .unwrap(),
            None
        );
    }

    #[test]
    fn unicode_and_long_keys_match_exactly() {
        let long = format!("命題.λ.{}", "x".repeat(16_000));
        let inventory = inventory_with(
            usize::MAX,
            &[("Unicode display", "命題.λ"), ("Long display", &long)],
        );
        let mut index = Index::new();
        index.insert("命題.λ", 0).unwrap();
        index.insert(&long, 1).unwrap();
        assert_eq!(index.find("命題.λ", &inventory).unwrap(), Some(0));
        assert_eq!(index.find(&long, &inventory).unwrap(), Some(1));
        assert_eq!(index.find("Unicode display", &inventory).unwrap(), None);
        assert_eq!(index.find("Long display", &inventory).unwrap(), None);
    }

    #[test]
    fn migration_keeps_existing_and_new_exact_identity_lookups() {
        let entries = (0..128)
            .map(|i| (format!("display-{i}"), format!("id.{i}")))
            .collect::<Vec<_>>();
        let refs = entries
            .iter()
            .map(|(name, key)| (name.as_str(), key.as_str()))
            .collect::<Vec<_>>();
        let inventory = inventory_with(0, &refs);
        let mut index = Index::with_limit(1024);
        for (id, (_, key)) in entries.iter().enumerate() {
            index.insert(key, id).unwrap();
            assert_eq!(index.find(key, &inventory).unwrap(), Some(id));
            assert_eq!(index.find("id.0", &inventory).unwrap(), Some(0));
        }
        assert!(index.is_spilled());
        for (id, (name, key)) in entries.iter().enumerate() {
            assert_eq!(index.find(key, &inventory).unwrap(), Some(id));
            assert_eq!(index.find(name, &inventory).unwrap(), None);
        }
    }

    #[test]
    fn spilled_collisions_compare_full_hash_and_identity_and_keep_first_match() {
        let inventory = inventory_with(
            0,
            &[
                ("first", "id.a"),
                ("other hash", "id.b"),
                ("same hash", "id.c"),
                ("duplicate key", "id.a"),
            ],
        );
        let mut index = Index::with_limit(0);
        for (id, hash) in [7, 7 + 65_536, 7, 7].into_iter().enumerate() {
            index.insert_with_hash(hash, id).unwrap();
        }
        assert_eq!(
            index.find_with_hash(7, "id.a", &inventory).unwrap(),
            Some(0)
        );
        assert_eq!(
            index.find_with_hash(7, "id.c", &inventory).unwrap(),
            Some(2)
        );
        assert_eq!(index.find_with_hash(7, "id.b", &inventory).unwrap(), None);
        assert_eq!(
            index
                .find_with_hash(7 + 65_536, "id.b", &inventory)
                .unwrap(),
            Some(1)
        );
        assert_eq!(index.find_with_hash(7, "first", &inventory).unwrap(), None);
        assert_eq!(
            index.find_with_hash(7, "missing", &inventory).unwrap(),
            None
        );
    }

    #[test]
    fn spilled_unicode_long_keys_and_count_gate_preserve_existing_rules() {
        let long = format!("命題.λ.{}", "x".repeat(16_000));
        let inventory = inventory_with(0, &[("Unicode", "命題.λ"), ("Long", &long)]);
        let mut index = Index::with_limit(0);
        index.insert("命題.λ", 0).unwrap();
        index.insert(&long, 1).unwrap();
        assert_eq!(index.find("命題.λ", &inventory).unwrap(), Some(0));
        assert_eq!(index.find(&long, &inventory).unwrap(), Some(1));
        assert_eq!(index.find("Unicode", &inventory).unwrap(), None);
        assert!(index.insert("out-of-order", 3).is_err());
        assert_eq!(index.candidate_count(), 2);
        index.set_candidate_count(super::super::MAX_DECLARATIONS);
        assert!(index
            .insert("over-limit", super::super::MAX_DECLARATIONS)
            .unwrap_err()
            .contains("count limit"));
    }

    #[test]
    fn cold_page_checksum_failure_poisons_the_whole_candidate_index() {
        let entries = (0..super::super::MAX_DECLARATIONS)
            .map(|i| (format!("display-{i}"), format!("id.{i}")))
            .collect::<Vec<_>>();
        let refs = entries
            .iter()
            .map(|(name, key)| (name.as_str(), key.as_str()))
            .collect::<Vec<_>>();
        let inventory = inventory_with(0, &refs);
        let mut index = Index::with_limit(0);
        for (id, (_, key)) in entries.iter().enumerate() {
            index.insert(key, id).unwrap();
        }
        assert_eq!(index.find("id.0", &inventory).unwrap(), Some(0));
        index.corrupt_first_flushed_record().unwrap();
        assert!(index
            .find("id.0", &inventory)
            .unwrap_err()
            .contains("checksum"));
        assert!(index
            .find("absent", &inventory)
            .unwrap_err()
            .contains("invalid after"));
        assert!(index
            .insert("later", index.candidate_count())
            .unwrap_err()
            .contains("invalid after"));
    }

    #[test]
    fn invalid_spilled_roots_fail_closed_instead_of_following_arbitrary_links() {
        let inventory = inventory_with(0, &[("name", "id.name")]);
        let mut index = Index::with_limit(0);
        index.insert_with_hash(7, 0).unwrap();
        index.corrupt_root(7, 2);
        assert!(index
            .find_with_hash(7, "id.name", &inventory)
            .unwrap_err()
            .contains("scratch link"));
        assert!(index.find("absent", &inventory).is_err());
    }

    #[test]
    fn selected_count_limit_is_applied_to_candidates() {
        let mut index = Index::with_count_limit(1);
        index.insert("first", 0).unwrap();
        assert!(index
            .insert("second", 1)
            .unwrap_err()
            .contains("count limit"));
    }
}
