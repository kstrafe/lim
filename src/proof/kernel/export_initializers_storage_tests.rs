use super::super::{expressions::Expression, term, Kernel, Level, Term};
use super::*;

fn tables() -> (Expressions, Names, Levels) {
    (
        Expressions::with_limit(false, 0),
        Names::new(),
        Levels::new(),
    )
}

#[test]
fn forced_spill_restores_none_source_and_native_records_in_order() {
    let (mut expressions, names, levels) = tables();
    expressions
        .push(Expression::Var(0), 1, 0, &names, &levels)
        .unwrap();
    let expected_native = term(Term::Sort(Level::number(0).unwrap()));
    let mut values = Initializers::with_limit(true, 0);
    values.push(0, None).unwrap();
    values.push(1, Some(Initializer::Source(0))).unwrap();
    values
        .push(2, Some(Initializer::Native(expected_native.clone())))
        .unwrap();
    assert!(values.is_spilled());

    assert!(values.load(0).unwrap().is_none());
    assert!(matches!(
        values.load(1).unwrap(),
        Some(Initializer::Source(0))
    ));
    let Some(Initializer::Native(restored)) = values.load(2).unwrap() else {
        panic!("native initializer was not restored")
    };
    assert!(Kernel::new()
        .same_syntax(&restored, &expected_native)
        .unwrap());
}

#[test]
fn selected_scratch_capacity_failure_poisoned_on_first_spill() {
    let mut values = Initializers::build(true, 0, 8, 1);
    assert!(values.push(0, None).is_err());
    assert!(values.push(0, None).is_err());
}

#[test]
fn sparse_source_ids_reconstruct_exact_terms_after_forced_paging() {
    let (mut expressions, names, levels) = tables();
    expressions
        .push(Expression::Sort(0), 1, 0, &names, &levels)
        .unwrap();
    expressions
        .push(Expression::Var(0), 1, 0, &names, &levels)
        .unwrap();
    expressions
        .push(Expression::Lam(0, 1), 2, 0, &names, &levels)
        .unwrap();
    let mut values = Initializers::with_limit(true, 0);
    for id in 0..96 {
        let source = [2, 0, 1][id % 3];
        values.push(id, Some(Initializer::Source(source))).unwrap();
    }
    assert!(values.is_spilled());

    let expected = [
        term(Term::Lam(
            term(Term::Sort(Level::number(0).unwrap())),
            term(Term::Var(0)),
        )),
        term(Term::Sort(Level::number(0).unwrap())),
        term(Term::Var(0)),
    ];
    for id in 0..96 {
        let actual = values
            .get(id, &expressions, &names, &levels)
            .unwrap()
            .unwrap();
        assert!(Kernel::new()
            .same_syntax(&actual, &expected[id % 3])
            .unwrap());
    }
}

#[test]
fn native_roots_are_released_on_spill_and_decode_exactly() {
    let (expressions, names, levels) = tables();
    let original = term(Term::App(
        term(Term::Var(3)),
        term(Term::Sort(Level::number(0).unwrap())),
    ));
    let weak = std::sync::Arc::downgrade(&original);
    let mut values = Initializers::with_limit(true, 0);
    values
        .push(0, Some(Initializer::Native(original.clone())))
        .unwrap();
    drop(original);
    assert!(weak.upgrade().is_none());
    assert!(values.is_spilled());

    let decoded = values
        .get(0, &expressions, &names, &levels)
        .unwrap()
        .unwrap();
    let expected = term(Term::App(
        term(Term::Var(3)),
        term(Term::Sort(Level::number(0).unwrap())),
    ));
    assert!(Kernel::new().same_syntax(&decoded, &expected).unwrap());
}

#[test]
fn source_reference_errors_are_preserved_after_spill() {
    let (expressions, names, levels) = tables();
    let mut values = Initializers::with_limit(true, 0);
    for id in 0..8 {
        values
            .push(id, Some(Initializer::Source(usize::MAX)))
            .unwrap();
    }
    assert!(values.is_spilled());
    assert!(values.get(5, &expressions, &names, &levels).is_err());
}

#[test]
fn invalid_indices_and_declaration_limit_are_rejected() {
    let mut values = Initializers::with_limit(true, 0);
    assert!(values.push(1, None).is_err());
    for id in 0..super::super::MAX_DECLARATIONS {
        values.push(id, None).unwrap();
    }
    assert_eq!(values.len(), super::super::MAX_DECLARATIONS);
    assert!(values.push(super::super::MAX_DECLARATIONS, None).is_err());
}

#[test]
fn spilled_native_pages_cross_page_boundary_and_support_cold_rereads() {
    let (expressions, names, levels) = tables();
    let mut values = Initializers::with_limit(true, 0);
    let large = term(Term::Eq(
        term(Term::Var(7)),
        term(Term::App(term(Term::Var(1)), term(Term::Var(2)))),
        term(Term::Lam(term(Term::Var(3)), term(Term::Var(4)))),
    ));
    for id in 0..1024 {
        values
            .push(id, Some(Initializer::Native(large.clone())))
            .unwrap();
    }
    drop(large);
    assert!(values.is_spilled());
    assert_eq!(values.len(), 1024);
    let expected = term(Term::Eq(
        term(Term::Var(7)),
        term(Term::App(term(Term::Var(1)), term(Term::Var(2)))),
        term(Term::Lam(term(Term::Var(3)), term(Term::Var(4)))),
    ));
    for id in [0, 511, 512, 1023, 0, 700, 511] {
        let actual = values
            .get(id, &expressions, &names, &levels)
            .unwrap()
            .unwrap();
        assert!(Kernel::new().same_syntax(&actual, &expected).unwrap());
    }
}

#[test]
fn corruption_error_is_sticky_across_other_reads() {
    let (expressions, names, levels) = tables();
    let mut values = Initializers::with_limit(true, 0);
    for id in 0..16 {
        let record = match id % 3 {
            0 => None,
            1 => Some(Initializer::Native(term(Term::Var(id)))),
            _ => Some(Initializer::Source(usize::MAX)),
        };
        values.push(id, record).unwrap();
    }
    values.corrupt_flushed_for_test().unwrap();
    assert!(values.load(1).is_err());
    assert!(values.load(0).is_err());
    assert!(values.get(2, &expressions, &names, &levels).is_err());
    assert!(values.push(16, None).is_err());
}

#[test]
#[ignore]
fn initializer_storage_benchmark() {
    use std::time::Instant;

    let mode = std::env::var("LIM_INITIALIZER_BENCH_MODE").unwrap_or_else(|_| "paged".to_owned());
    let resident_limit = match mode.as_str() {
        "vec" => usize::MAX,
        "paged" => 0,
        other => panic!("unknown LIM_INITIALIZER_BENCH_MODE: {other}"),
    };
    let (expressions, names, levels) = tables();
    let mut values = Initializers::with_limit(true, resident_limit);
    let selected = [0, 1500, 2999];
    let started = Instant::now();
    for id in 0..3000 {
        let name = format!("{id:08}-{}", "x".repeat(4096));
        values
            .push(
                id,
                Some(Initializer::Native(term(Term::Global(name, Vec::new())))),
            )
            .unwrap();
        std::hint::black_box(&values);
    }
    for id in selected {
        let actual = values
            .get(id, &expressions, &names, &levels)
            .unwrap()
            .unwrap();
        let expected = format!("{id:08}-{}", "x".repeat(4096));
        assert!(matches!(
            actual.as_ref(),
            Term::Global(name, levels) if name == &expected && levels.is_empty()
        ));
        std::hint::black_box(actual);
    }
    let wall_ns = started.elapsed().as_nanos();
    let resident_bytes = values.resident_bytes();
    println!(
        "lim-initializer-benchmark {{\"mode\":\"{mode}\",\"rows\":3000,\"wall_ns\":{wall_ns},\"resident_bytes\":{resident_bytes}}}"
    );
}

#[test]
fn migration_restores_resident_records_before_releasing_native_roots() {
    let mut values = Initializers::with_limit(true, 1024);
    values.push(0, None).unwrap();
    values.push(1, Some(Initializer::Source(71))).unwrap();
    assert!(!values.is_spilled());
    let original = term(Term::Global("x".repeat(4096), vec![]));
    let weak = std::sync::Arc::downgrade(&original);
    values.push(2, Some(Initializer::Native(original))).unwrap();
    assert!(values.is_spilled());
    assert!(weak.upgrade().is_none());
    assert!(values.load(0).unwrap().is_none());
    assert!(matches!(
        values.load(1).unwrap(),
        Some(Initializer::Source(71))
    ));
    let Some(Initializer::Native(restored)) = values.load(2).unwrap() else {
        panic!()
    };
    assert!(
        matches!(restored.as_ref(), Term::Global(name, levels) if name == &"x".repeat(4096) && levels.is_empty())
    );
}

#[test]
fn failed_directory_publication_does_not_commit_a_native_record() {
    let mut values = Initializers::with_limit(true, 0);
    values.push(0, None).unwrap();
    let Storage::Spilled(spilled) = &mut values.storage else {
        panic!()
    };
    // Inject an extra byte after the committed directory. The next record's
    // data write succeeds, but its directory cannot publish contiguously.
    spilled.index.get_mut().append(b"!").unwrap();
    assert!(values
        .push(1, Some(Initializer::Native(term(Term::Var(1)))))
        .is_err());
    assert_eq!(values.len(), 1);
    assert!(values.load(0).is_err());
    assert!(values.push(1, None).is_err());
}

#[test]
fn native_storage_preserves_open_markers_and_shared_dags_without_checking_them() {
    let shared = term(Term::SelfAt(vec![term(Term::Var(9))]));
    let original = term(Term::Recur(
        "not-a-checked-global".into(),
        vec![shared.clone(), shared],
    ));
    let mut values = Initializers::with_limit(true, 0);
    values
        .push(0, Some(Initializer::Native(original.clone())))
        .unwrap();
    let Some(Initializer::Native(restored)) = values.load(0).unwrap() else {
        panic!()
    };
    assert!(Kernel::new().same_syntax(&original, &restored).unwrap());
    let Term::Recur(_, children) = restored.as_ref() else {
        panic!()
    };
    assert!(std::sync::Arc::ptr_eq(&children[0], &children[1]));
}

#[test]
fn observed_index_corruption_invalidates_empty_slots_and_appends() {
    let mut values = Initializers::with_limit(true, 0);
    for id in 0..3000 {
        values.push(id, None).unwrap();
    }
    values.corrupt_flushed_for_test().unwrap();
    assert!(values.load(0).is_err());
    assert!(values.load(2999).is_err());
    assert!(values.push(3000, None).is_err());
}
