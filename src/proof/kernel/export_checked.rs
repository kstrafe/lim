//! Invocation-local index for already checked declaration identities.
//!
//! Hashes select candidate IDs only. Compare complete canonical key bytes in
//! `Inventory`, including when they have spilled. Neither an index hit nor a
//! receipt can establish a theorem or bypass ordinary declaration checking.
use super::{inventory::Inventory, Result};
use std::{collections::HashMap, hash::BuildHasher};

pub(super) struct Index {
    candidates: HashMap<u64, Ids>,
    count: usize,
}

enum Ids {
    One(usize),
    Many(Vec<usize>),
}

impl Ids {
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
    pub(super) fn new() -> Self {
        Self {
            candidates: HashMap::new(),
            count: 0,
        }
    }

    pub(super) fn find(&self, key: &str, inventory: &Inventory) -> Result<Option<usize>> {
        let hash = self.candidates.hasher().hash_one(key);
        self.find_with_hash(hash, key, inventory)
    }

    fn find_with_hash(&self, hash: u64, key: &str, inventory: &Inventory) -> Result<Option<usize>> {
        let Some(ids) = self.candidates.get(&hash) else {
            return Ok(None);
        };
        for &id in ids.as_slice() {
            if inventory.matches_identity(id, key)? {
                return Ok(Some(id));
            }
        }
        Ok(None)
    }

    /// Add a report only after its proof has passed checking and it has been
    /// appended to the inventory. IDs must therefore arrive in inventory order.
    pub(super) fn insert(&mut self, key: &str, id: usize) -> Result<()> {
        let hash = self.candidates.hasher().hash_one(key);
        self.insert_with_hash(hash, id)
    }

    fn insert_with_hash(&mut self, hash: u64, id: usize) -> Result<()> {
        if id != self.count {
            return Err("checked declaration IDs must be contiguous".into());
        }
        if self.count >= super::MAX_DECLARATIONS {
            return Err("checked declaration count limit exceeded".into());
        }
        match self.candidates.get_mut(&hash) {
            Some(ids) => ids.push(id),
            None => {
                self.candidates.insert(hash, Ids::One(id));
            }
        }
        self.count += 1;
        Ok(())
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
        assert_eq!(index.count, 1);
    }

    #[test]
    fn invalid_inventory_references_propagate_as_errors() {
        let inventory = Inventory::new();
        let mut index = Index::new();
        index.insert_with_hash(11, 0).unwrap();
        assert!(index.find_with_hash(11, "name", &inventory).is_err());
    }

    #[test]
    fn exact_identity_works_with_spilled_cold_inventory_pages() {
        let mut declarations = Vec::with_capacity(33);
        for id in 0..33 {
            let identity = format!("id.{id:02}.{}", "x".repeat(12_000));
            declarations.push((format!("display-{id}"), identity));
        }
        let refs = declarations
            .iter()
            .map(|(display, identity)| (display.as_str(), identity.as_str()))
            .collect::<Vec<_>>();
        let inventory = inventory_with(0, &refs);
        assert!(inventory.is_spilled());
        let mut index = Index::new();
        for id in 0..declarations.len() {
            index.insert(&declarations[id].1, id).unwrap();
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
        index.insert_with_hash(5, 0).unwrap();
        index.insert_with_hash(5, 1).unwrap();
        assert_eq!(index.candidates.len(), 1);
        assert!(matches!(index.candidates.values().next(), Some(Ids::Many(ids)) if ids == &[0, 1]));
        assert_eq!(
            index.find_with_hash(5, "id.one", &inventory).unwrap(),
            Some(0)
        );
        assert_eq!(
            index
                .find_with_hash(5, "Shared display", &inventory)
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
}
