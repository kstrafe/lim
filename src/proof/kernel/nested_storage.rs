//! Invocation-local storage for derived, scoped nested-family views.
//! Metadata lives in a separate storage-only declaration table. It never
//! enters the kernel's global environment or authorizes a new constant.
use super::{declarations::Declarations, nested::NestedFamily, term, Declaration, Result, Term};
use std::{cell::Cell, sync::Arc};

pub(super) struct Views {
    signatures: Declarations,
    metadata: Declarations,
    len: usize,
    poisoned: Cell<bool>,
}

impl Views {
    pub(super) fn new() -> Self {
        Self::with_scratch_limit(super::scratch::DEFAULT_BYTES)
    }
    pub(super) fn with_scratch_limit(max_file_bytes: u64) -> Self {
        Self {
            signatures: Declarations::with_scratch_limit(max_file_bytes),
            metadata: Declarations::with_scratch_limit(max_file_bytes),
            len: 0,
            poisoned: Cell::new(false),
        }
    }
    pub(super) fn healthy(&self) -> Result<()> {
        if self.poisoned.get() {
            Err("nested view storage is invalid after a storage error".into())
        } else {
            Ok(())
        }
    }
    pub(super) fn invalidate(&self) {
        self.poisoned.set(true);
    }
    fn checked<T>(&self, result: Result<T>) -> Result<T> {
        if result.is_err() {
            self.poisoned.set(true);
        }
        result
    }
    pub(super) fn enable_spilling(&mut self) {
        self.signatures.enable_spilling();
        self.metadata.enable_spilling();
    }
    pub(super) fn contains_key(&self, name: &str) -> Result<bool> {
        self.healthy()?;
        if self.len == 0 {
            return Ok(false);
        }
        self.checked((|| {
            let signature = self.signatures.contains_key(name)?;
            let metadata = self.metadata.contains_key(name)?;
            if signature != metadata {
                return Err("nested view signature and metadata membership differ".into());
            }
            Ok(signature)
        })())
    }
    pub(super) fn any(&self, names: &[String]) -> Result<bool> {
        self.healthy()?;
        for name in names {
            if self.contains_key(name)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    pub(super) fn roots(&self, names: &[String]) -> Result<Vec<String>> {
        self.healthy()?;
        let mut roots = Vec::new();
        for name in names {
            if !self.contains_key(name)? {
                roots.push(name.clone());
            }
        }
        Ok(roots)
    }
    pub(super) fn get(&self, name: &str) -> Result<Option<NestedFamily>> {
        self.healthy()?;
        if self.len == 0 {
            return Ok(None);
        }
        self.checked((|| {
            let signature = self.signatures.get(name)?;
            let metadata = self.metadata.get(name)?;
            match (signature, metadata) {
                (None, None) => Ok(None),
                (Some(signature), Some(metadata)) => {
                    // This envelope is only a codec container. Its payload is
                    // decoded exactly, never inferred as a mathematical term.
                    let Term::Ctor {
                        family,
                        levels,
                        parameters,
                        constructor,
                        fields,
                    } = metadata.ty.as_ref()
                    else {
                        return Err("invalid nested view metadata envelope".into());
                    };
                    if !metadata.universes.is_empty()
                        || metadata.value.is_some()
                        || metadata.family.is_some()
                        || !constructor.is_empty()
                        || !fields.is_empty()
                    {
                        return Err("invalid nested view metadata envelope".into());
                    }
                    Ok(Some(NestedFamily {
                        declaration: signature.as_ref().clone(),
                        source: family.clone(),
                        levels: levels.clone(),
                        arguments: parameters.clone(),
                    }))
                }
                _ => Err("nested view signature and metadata membership differ".into()),
            }
        })())
    }
    pub(super) fn declaration_mut(&mut self, name: &str) -> Result<Option<&mut Declaration>> {
        if !self.contains_key(name)? {
            return Ok(None);
        }
        let poisoned = &self.poisoned;
        self.signatures
            .get_mut(name)
            .inspect_err(|_| poisoned.set(true))
    }
    pub(super) fn declaration(&self, name: &str) -> Result<Option<Arc<Declaration>>> {
        if !self.contains_key(name)? {
            return Ok(None);
        }
        self.checked(self.signatures.get(name))
    }
    pub(super) fn insert(&mut self, name: String, view: NestedFamily) -> Result<()> {
        let existing = self.contains_key(&name)?;
        let result = (|| {
            self.signatures.insert(name.clone(), view.declaration)?;
            self.metadata.insert(
                name,
                Declaration {
                    universes: vec![],
                    ty: term(Term::Ctor {
                        family: view.source,
                        levels: view.levels,
                        parameters: view.arguments,
                        constructor: String::new(),
                        fields: vec![],
                    }),
                    value: None,
                    family: None,
                },
            )?;
            if !existing {
                self.len = self
                    .len
                    .checked_add(1)
                    .ok_or("nested view count overflow")?;
            }
            Ok(())
        })();
        self.checked(result)
    }
    pub(super) fn remove(&mut self, name: &str) -> Result<()> {
        if !self.contains_key(name)? {
            return Ok(());
        }
        let result = (|| {
            self.signatures.remove(name)?;
            self.metadata.remove(name)?;
            self.len = self
                .len
                .checked_sub(1)
                .ok_or("nested view count underflow")?;
            Ok(())
        })();
        self.checked(result)
    }
    /// The caller must have completed or rolled back the whole inductive group.
    pub(super) fn trim(&mut self) -> Result<bool> {
        self.healthy()?;
        if self.len == 0 {
            return Ok(false);
        }
        let result = (|| {
            let signatures = self.signatures.trim()?;
            let metadata = self.metadata.trim()?;
            Ok(signatures || metadata)
        })();
        self.checked(result)
    }
    #[cfg(test)]
    pub(super) fn set_limit(&mut self, limit: usize) {
        self.signatures.set_limit(limit);
        self.metadata.set_limit(limit);
    }
    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        self.signatures.directories_spilled() && self.metadata.directories_spilled()
    }
    #[cfg(test)]
    pub(super) fn resident_value_bytes(&self) -> usize {
        self.signatures.resident_value_bytes() + self.metadata.resident_value_bytes()
    }
    #[cfg(test)]
    pub(super) fn is_empty(&self) -> bool {
        self.len == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::kernel::core::{Kernel, Level};

    fn view(source: String) -> NestedFamily {
        NestedFamily {
            declaration: Declaration {
                universes: vec![],
                ty: term(Term::Global("#pt-nat".into(), vec![])),
                value: None,
                family: None,
            },
            source,
            levels: vec![Level::number(1).unwrap()],
            arguments: vec![term(Term::Var(2)), term(Term::Var(0))],
        }
    }

    #[test]
    fn spilled_metadata_retains_levels_argument_order_and_updated_signature() {
        let mut views = Views::new();
        views.set_limit(0);
        views
            .insert("scoped".into(), view("Container".into()))
            .unwrap();
        views.trim().unwrap();
        let before = views.get("scoped").unwrap().unwrap();
        assert_eq!(before.source, "Container");
        assert_eq!(before.levels, vec![Level::number(1).unwrap()]);
        assert!(matches!(before.arguments[0].as_ref(), Term::Var(2)));
        assert!(matches!(before.arguments[1].as_ref(), Term::Var(0)));
        views
            .declaration_mut("scoped")
            .unwrap()
            .unwrap()
            .universes
            .push("u".into());
        views.trim().unwrap();
        let after = views.get("scoped").unwrap().unwrap();
        assert_eq!(after.declaration.universes, vec!["u"]);
        assert_eq!(after.source, before.source);
        assert_eq!(views.resident_value_bytes(), 0);
    }

    #[test]
    fn selected_scratch_capacity_preserves_paged_nested_views() {
        let mut views = Views::with_scratch_limit(8 * 1024 * 1024);
        views.set_limit(0);
        let expected = view("ChosenFamily".into());
        views.insert("chosen".into(), expected.clone()).unwrap();
        views.trim().unwrap();
        let actual = views.get("chosen").unwrap().unwrap();
        assert_eq!(actual.source, expected.source);
        assert_eq!(actual.levels, expected.levels);
        assert_eq!(actual.arguments.len(), 2);
        assert!(matches!(actual.arguments[0].as_ref(), Term::Var(2)));
        assert!(matches!(actual.arguments[1].as_ref(), Term::Var(0)));
        assert!(actual.declaration.universes.is_empty());
        assert!(
            matches!(actual.declaration.ty.as_ref(), Term::Global(name, levels)
            if name == "#pt-nat" && levels.is_empty())
        );
        assert!(actual.declaration.value.is_none());
        assert!(actual.declaration.family.is_none());
    }

    #[test]
    fn mismatched_stores_poison_cached_missing_and_mutating_accesses() {
        let mut views = Views::new();
        views.insert("other".into(), view("Other".into())).unwrap();
        views
            .insert("damaged".into(), view("Container".into()))
            .unwrap();
        views.metadata.remove("damaged").unwrap();
        assert!(views
            .contains_key("damaged")
            .unwrap_err()
            .contains("membership differ"));
        assert!(views.get("other").is_err());
        assert!(views.declaration("other").is_err());
        assert!(views.declaration_mut("other").is_err());
        assert!(views.contains_key("absent").is_err());
        assert!(views.roots(&[]).is_err());
        assert!(views.any(&[]).is_err());
        assert!(views.insert("new".into(), view("New".into())).is_err());
        assert!(views.remove("other").is_err());
        assert!(views.trim().is_err());
    }

    #[test]
    fn corrupted_metadata_pages_invalidate_the_kernel_even_after_budget_reset() {
        let mut kernel = Kernel::new();
        kernel.nested.set_limit(0);
        kernel
            .nested
            .insert("scoped".into(), view("Container".into()))
            .unwrap();
        kernel.nested.trim().unwrap();
        kernel
            .nested
            .metadata
            .corrupt_stored_value("scoped")
            .unwrap();
        assert!(kernel
            .nested
            .get("scoped")
            .err()
            .unwrap()
            .contains("checksum"));
        assert!(kernel.nested.declaration("scoped").is_err());
        kernel.reset_budget();
        assert!(kernel
            .infer(&[], &term(Term::Sort(Level::number(0).unwrap())), 0)
            .is_err());
        assert!(kernel.contains("#pt-nat").is_err());
    }

    #[test]
    fn second_store_trim_failure_prevents_reusing_the_completed_first_store() {
        let mut views = Views::new();
        views.set_limit(0);
        // Storage-only adversarial metadata: the source string alone exceeds
        // the existing record bound. The signature can spill successfully.
        views
            .insert("oversized".into(), view("x".repeat(32 * 1024 * 1024)))
            .unwrap();
        assert!(views.trim().is_err());
        assert!(views.signatures.directories_spilled());
        assert!(views.contains_key("oversized").is_err());
        assert!(views.get("oversized").is_err());
        assert!(views.declaration_mut("oversized").is_err());
    }
}
