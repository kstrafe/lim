use super::super::{term, Constructor, Level, Term};
use super::*;

fn declaration(value: Option<T>) -> Declaration {
    Declaration {
        universes: vec![],
        ty: term(Term::Sort(Level::number(1).unwrap())),
        value,
        family: None,
    }
}

fn family() -> Family {
    Family {
        group: vec!["sample".into()],
        parameters: vec![],
        indices: vec![],
        sort: Level::number(1).unwrap(),
        constructors: vec![Constructor {
            name: "sample.mk".into(),
            fields: vec![term(Term::Sort(Level::number(0).unwrap()))],
            recursive: vec![None],
            result_indices: vec![],
        }],
        large: true,
    }
}

fn spill(declarations: &mut Declarations, limit: usize, entries: &[(&str, Declaration)]) {
    declarations.set_limit(limit);
    for (name, value) in entries {
        declarations.insert((*name).into(), value.clone()).unwrap();
    }
}

#[test]
fn spilling_preserves_transparent_opaque_values_and_releases_resident_arcs() {
    let transparent = declaration(Some(term(Term::Var(0))));
    let opaque = declaration(None);
    let mut declarations = Declarations::new();
    declarations
        .insert("transparent".into(), transparent.clone())
        .unwrap();
    declarations
        .insert("opaque".into(), opaque.clone())
        .unwrap();
    assert!(declarations.cold.get_mut().spool.is_none());

    let weak = Arc::downgrade(&declarations.entries.get("transparent").unwrap().value);
    declarations.set_limit(1);
    assert!(declarations.trim().unwrap());
    assert!(weak.upgrade().is_none());
    assert!(!declarations.entries.contains_key("transparent"));
    assert!(!declarations.entries.contains_key("opaque"));
    assert!(declarations.stored.get(b"transparent").unwrap().is_some());
    assert!(declarations.stored.get(b"opaque").unwrap().is_some());
    assert!(matches!(
        declarations
            .get("transparent")
            .unwrap()
            .unwrap()
            .value
            .as_ref()
            .map(T::as_ref),
        Some(Term::Var(0))
    ));
    assert!(declarations.get("opaque").unwrap().unwrap().value.is_none());
}

#[test]
fn selected_scratch_capacity_preserves_exact_paged_declarations() {
    let mut declarations = Declarations::with_scratch_limit(8 * 1024 * 1024);
    declarations
        .insert("paged".into(), declaration(Some(term(Term::Var(7)))))
        .unwrap();
    declarations.set_limit(0);
    declarations.trim().unwrap();
    assert!(declarations.directories_spilled());
    assert!(matches!(
        declarations
            .get("paged")
            .unwrap()
            .unwrap()
            .value
            .as_ref()
            .map(T::as_ref),
        Some(Term::Var(7))
    ));
}

#[test]
fn identical_blobs_keep_nominal_names_distinct_and_no_spill_precedes_limit() {
    let value = declaration(None);
    let mut declarations = Declarations::new();
    declarations.insert("left".into(), value.clone()).unwrap();
    declarations.insert("right".into(), value).unwrap();
    assert!(declarations.cold.get_mut().spool.is_none());
    declarations.set_limit(0);
    declarations.trim().unwrap();

    assert!(!declarations.entries.contains_key("left"));
    assert!(!declarations.entries.contains_key("right"));
    let left = declarations.stored.get(b"left").unwrap().unwrap();
    let right = declarations.stored.get(b"right").unwrap().unwrap();
    assert_eq!(left.digest, right.digest);
    assert_eq!(left.offset, right.offset);
    assert!(declarations.contains_key("left").unwrap());
    assert!(declarations.contains_key("right").unwrap());
    assert!(declarations.get("left").unwrap().is_some());
    assert!(declarations.get("right").unwrap().is_some());
    assert_eq!(declarations.cold.borrow().blobs.len(), 1);
}

#[test]
fn cold_cache_respects_available_resident_limit_and_skips_oversized_entries() {
    let entries = (0..12)
        .map(|index| {
            (
                format!("item-{index}"),
                declaration(Some(term(Term::Var(index)))),
            )
        })
        .collect::<Vec<_>>();
    let mut declarations = Declarations::new();
    let limit = 4 * resident_weight(&entries[0].0, &entries[0].1).unwrap();
    spill(
        &mut declarations,
        limit,
        &entries
            .iter()
            .map(|(name, value)| (name.as_str(), value.clone()))
            .collect::<Vec<_>>(),
    );
    declarations.trim().unwrap();
    assert!(declarations.stored.len() > 0);
    for (name, _) in &entries {
        declarations.get(name).unwrap();
        assert!(
            declarations.cold.borrow().bytes <= limit.saturating_sub(declarations.resident_bytes)
        );
    }
    assert!(!declarations.cold.borrow().cache.is_empty());

    let mut declarations = Declarations::new();
    spill(&mut declarations, 1, &[("oversized", declaration(None))]);
    declarations.trim().unwrap();
    declarations.get("oversized").unwrap();
    assert!(declarations.cold.borrow().cache.is_empty());
}

#[test]
fn mutable_lookup_replaces_stale_cold_representation() {
    let mut declarations = Declarations::new();
    declarations.set_limit(0);
    declarations
        .insert("item".into(), declaration(None))
        .unwrap();
    declarations.trim().unwrap();
    declarations.set_limit(4096);
    declarations.get("item").unwrap().unwrap();
    assert!(declarations.cold.borrow().cache.contains_key("item"));
    assert!(declarations.stored.get(b"item").unwrap().is_some());

    declarations.get_mut("item").unwrap().unwrap().value = Some(term(Term::Var(7)));
    assert!(declarations.entries.contains_key("item"));
    assert!(declarations.stored.get(b"item").unwrap().is_none());
    assert!(!declarations.cold.borrow().cache.contains_key("item"));
    assert!(declarations.cold.get_mut().spool.is_some());
    assert!(matches!(
        declarations
            .get("item")
            .unwrap()
            .unwrap()
            .value
            .as_ref()
            .map(T::as_ref),
        Some(Term::Var(7))
    ));
    declarations.set_limit(0);
    assert!(declarations.trim().unwrap());
    assert!(!declarations.entries.contains_key("item"));
    assert!(declarations.stored.get(b"item").unwrap().is_some());
    assert!(matches!(
        declarations
            .get("item")
            .unwrap()
            .unwrap()
            .value
            .as_ref()
            .map(T::as_ref),
        Some(Term::Var(7))
    ));
}

#[test]
fn provisional_group_residents_do_not_create_spill_io_until_trim() {
    let mut declarations = Declarations::new();
    declarations.set_limit(0);
    declarations
        .insert("provisional.a".into(), declaration(None))
        .unwrap();
    declarations
        .insert("provisional.b".into(), declaration(None))
        .unwrap();
    assert!(declarations.cold.get_mut().spool.is_none());
    assert!(declarations
        .pending
        .iter()
        .any(|name| name == "provisional.a"));
    assert!(declarations
        .pending
        .iter()
        .any(|name| name == "provisional.b"));
    // The kernel's group checker calls trim only after the group is complete.
    declarations.trim().unwrap();
    assert!(declarations.cold.get_mut().spool.is_some());
}

#[test]
fn corrupt_offsets_and_digests_fail_closed_and_poison_later_reads() {
    for corrupt_digest in [false, true] {
        let mut declarations = Declarations::new();
        declarations.set_limit(0);
        declarations
            .insert("stored".into(), declaration(None))
            .unwrap();
        declarations.trim().unwrap();
        let mut blob = declarations
            .stored
            .get(b"stored")
            .unwrap()
            .expect("declaration did not spill");
        if corrupt_digest {
            blob.digest[0] ^= 1;
        } else {
            blob.offset = 1 << 30;
        }
        declarations.stored.set(b"stored", Some(blob)).unwrap();
        let error = declarations.get("stored").err().unwrap();
        assert!(
            error.contains(if corrupt_digest { "checksum" } else { "range" }),
            "{error}"
        );
        assert!(declarations.cold.borrow().poisoned);
        assert!(declarations
            .get("missing")
            .err()
            .unwrap()
            .contains("invalid"));
        assert!(declarations.contains_key("stored").is_err());
    }
}

#[test]
fn structural_comparison_rejects_each_declaration_and_family_metadata_change() {
    let base = Declaration {
        universes: vec!["u".into()],
        ty: term(Term::Sort(Level::number(1).unwrap())),
        value: Some(term(Term::Var(0))),
        family: Some(family()),
    };
    let mut variants = Vec::new();
    let mut changed = base.clone();
    changed.universes.push("v".into());
    variants.push(changed);
    let mut changed = base.clone();
    changed.ty = term(Term::Var(3));
    variants.push(changed);
    let mut changed = base.clone();
    changed.value = None;
    variants.push(changed);
    let mut changed = base.clone();
    changed.family = None;
    variants.push(changed);
    for change in 0..8 {
        let mut changed = base.clone();
        let family = changed.family.as_mut().unwrap();
        match change {
            0 => family.group.push("other".into()),
            1 => family.sort = Level::number(0).unwrap(),
            2 => family.large = false,
            3 => family
                .parameters
                .push(term(Term::Sort(Level::number(0).unwrap()))),
            4 => family
                .indices
                .push(term(Term::Sort(Level::number(0).unwrap()))),
            5 => family.constructors[0].name.push_str(".changed"),
            6 => family.constructors[0].recursive[0] = Some("sample".into()),
            _ => family.constructors[0].fields[0] = term(Term::Var(1)),
        }
        variants.push(changed);
    }
    let mut changed = base.clone();
    changed.family.as_mut().unwrap().constructors[0]
        .result_indices
        .push(term(Term::Var(0)));
    variants.push(changed);
    let mut changed = base.clone();
    changed
        .family
        .as_mut()
        .unwrap()
        .constructors
        .push(Constructor {
            name: "sample.other".into(),
            fields: vec![],
            recursive: vec![],
            result_indices: vec![],
        });
    variants.push(changed);
    for changed in variants {
        assert!(!same_declaration(&base, &changed).unwrap());
    }
    assert!(same_declaration(&base, &base.clone()).unwrap());
}

#[test]
fn cold_remove_then_reinsert_cannot_resurrect_the_old_value() {
    let mut declarations = Declarations::new();
    declarations.set_limit(0);
    declarations
        .insert("same".into(), declaration(Some(term(Term::Var(1)))))
        .unwrap();
    declarations.trim().unwrap();
    assert!(declarations.stored.get(b"same").unwrap().is_some());
    declarations.remove("same").unwrap();
    assert!(declarations.stored.get(b"same").unwrap().is_none());
    declarations
        .insert("same".into(), declaration(Some(term(Term::Var(9)))))
        .unwrap();
    assert!(matches!(
        declarations
            .get("same")
            .unwrap()
            .unwrap()
            .value
            .as_ref()
            .map(T::as_ref),
        Some(Term::Var(9))
    ));
}

#[test]
fn old_arc_snapshot_survives_mutation_after_cold_reload() {
    let mut declarations = Declarations::new();
    declarations.set_limit(0);
    declarations
        .insert("snapshot".into(), declaration(Some(term(Term::Var(1)))))
        .unwrap();
    declarations.trim().unwrap();
    let snapshot = declarations.get("snapshot").unwrap().unwrap();
    declarations.get_mut("snapshot").unwrap().unwrap().value = Some(term(Term::Var(2)));
    assert!(matches!(
        snapshot.value.as_ref().map(T::as_ref),
        Some(Term::Var(1))
    ));
    assert!(matches!(
        declarations
            .get("snapshot")
            .unwrap()
            .unwrap()
            .value
            .as_ref()
            .map(T::as_ref),
        Some(Term::Var(2))
    ));
    assert!(declarations.stored.get(b"snapshot").unwrap().is_none());
}

#[test]
fn repeated_provisional_insert_remove_does_not_retain_pending_names() {
    let mut declarations = Declarations::new();
    declarations.set_limit(0);
    for _ in 0..8 {
        declarations
            .insert("temporary".into(), declaration(None))
            .unwrap();
        declarations.remove("temporary").unwrap();
    }
    assert!(declarations.pending.is_empty());
    assert!(declarations.order.is_empty());
    assert!(!declarations.entries.contains_key("temporary"));
    assert!(declarations.stored.get(b"temporary").unwrap().is_none());
}

#[test]
fn failed_cold_name_lookup_poisoning_blocks_definition_of_fresh_constant() {
    let mut kernel = Kernel::new();
    kernel.declarations.set_limit(0);
    // Cross a scratch page so the corruption changes disk bytes, rather than
    // trying to overwrite the still-resident pending tail.
    let name = "cold-bad".repeat(10_000);
    kernel
        .declarations
        .insert(name.clone(), declaration(None))
        .unwrap();
    kernel.declarations.trim().unwrap();
    kernel
        .declarations
        .stored
        .corrupt_flushed_record(name.as_bytes())
        .unwrap();
    let error = kernel.contains(&name).unwrap_err();
    assert!(error.contains("checksum"), "{error}");
    assert!(kernel.declarations.get("absent").is_err());
    let error = kernel
        .definition(
            "fresh-after-corruption",
            vec![],
            term(Term::Sort(Level::number(1).unwrap())),
            term(Term::Sort(Level::number(0).unwrap())),
            false,
        )
        .unwrap_err();
    assert!(error.contains("invalid after"), "{error}");
    assert!(kernel.contains("fresh-after-corruption").is_err());
}
