use super::*;

fn record(replay: &mut Replay, value: &str) -> Result<()> {
    replay.expression_record(&crate::lsp::json::parse(value).unwrap())
}
fn slots_empty(values: &Expressions) -> bool {
    let Storage::Compact { materialized, .. } = &values.storage else {
        panic!("compact table")
    };
    let memo = materialized.borrow();
    match &memo.sparse {
        Some(slots) => slots.is_empty(),
        None => memo.slots.iter().all(Option::is_none),
    }
}
fn root_names() -> names::Names {
    names::Names::new()
}

#[test]
fn compact_storage_reuses_a_dag_then_releases_dead_weak_allocations() {
    let mut values = Expressions::new(false);
    let names = root_names();
    let levels = vec![Level::number(0).unwrap()];
    values
        .push(Expression::Var(0), 1, 0, &names, &levels)
        .unwrap();
    values
        .push(Expression::App(0, 0), 2, 0, &names, &levels)
        .unwrap();
    assert!(slots_empty(&values));
    let root = values.get(1, &names, &levels).unwrap();
    let Term::App(a, b) = root.as_ref() else {
        panic!("application")
    };
    assert!(Arc::ptr_eq(a, b));
    drop(root);
    values.end_record();
    assert!(slots_empty(&values));
    let owner = values.get(0, &names, &levels).unwrap();
    values.end_record();
    assert!(Arc::ptr_eq(
        &owner,
        &values.get(0, &names, &levels).unwrap()
    ));
    drop(owner);
    let again = values.get(0, &names, &levels).unwrap();
    assert!(matches!(again.as_ref(), Term::Var(0)));
    drop(again);
    values.end_record();
    assert!(slots_empty(&values));
}

#[test]
fn eviction_sweeps_dead_handles_from_earlier_records_in_both_memo_layouts() {
    for limit in [0, usize::MAX] {
        let names = root_names();
        let levels = [Level::number(0).unwrap()];
        let mut values = Expressions::with_limit(false, limit);
        values
            .push(Expression::Var(0), 1, 0, &names, &levels)
            .unwrap();
        let owner = values.get(0, &names, &levels).unwrap();
        // The declaration still owns the term at its original record boundary.
        values.end_record();
        assert!(!slots_empty(&values));
        drop(owner);
        // A later record's incremental sweep does not revisit that old slot.
        values.end_record();
        assert!(!slots_empty(&values));
        values.sweep_dead();
        assert!(slots_empty(&values));
        let rebuilt = values.get(0, &names, &levels).unwrap();
        assert!(matches!(rebuilt.as_ref(), Term::Var(0)));
    }
}

#[test]
fn compact_and_eager_modes_reconstruct_all_source_nodes_exactly() {
    let inputs = [
        r#"{"ie":0,"bvar":1}"#,
        r#"{"ie":1,"sort":0}"#,
        r#"{"ie":2,"const":{"name":1,"us":[0]}}"#,
        r#"{"ie":3,"natVal":"123"}"#,
        r#"{"ie":4,"app":{"fn":0,"arg":1}}"#,
        r#"{"ie":5,"lam":{"name":0,"type":1,"body":0,"binderInfo":"default"}}"#,
        r#"{"ie":6,"forallE":{"name":0,"type":1,"body":0,"binderInfo":"implicit"}}"#,
        r#"{"ie":7,"letE":{"name":0,"type":1,"value":2,"body":0,"nondep":false}}"#,
        r#"{"ie":8,"proj":{"typeName":1,"idx":7,"struct":0}}"#,
        r#"{"ie":9,"mdata":{"expr":8,"data":{}}}"#,
    ];
    let mut eager = Replay::with_retention(crate::ProofBudget::default(), true);
    let mut compact = Replay::with_retention(crate::ProofBudget::default(), false);
    for replay in [&mut eager, &mut compact] {
        replay
            .name_record(
                &crate::lsp::json::parse(r#"{"in":1,"str":{"pre":0,"str":"Foo"}}"#).unwrap(),
            )
            .unwrap();
        for input in inputs {
            record(replay, input).unwrap();
        }
    }
    for id in 0..inputs.len() {
        let a = eager.expression(&number_json(id as u64)).unwrap();
        let b = compact.expression(&number_json(id as u64)).unwrap();
        assert!(Kernel::new().same_syntax(&a, &b).unwrap());
        assert_eq!(
            eager.expressions.depth(id).unwrap(),
            compact.expressions.depth(id).unwrap()
        );
        assert_eq!(
            eager.expressions.payload(id),
            compact.expressions.payload(id)
        );
    }
    assert_eq!(eager.payload_bytes, compact.payload_bytes);
}

#[test]
fn long_metadata_alias_chains_preserve_depth_without_reconstruction_recursion() {
    let mut replay = Replay::new();
    record(&mut replay, r#"{"ie":0,"bvar":0}"#).unwrap();
    for id in 1..=4096 {
        let row = object([
            ("ie", number_json(id)),
            (
                "mdata",
                object([("expr", number_json(id - 1)), ("data", object([]))]),
            ),
        ]);
        replay.expression_record(&row).unwrap();
        assert_eq!(replay.expressions.depth(id as usize).unwrap(), 1);
    }
    let result = replay.expression(&number_json(4096)).unwrap();
    assert!(matches!(result.as_ref(), Term::Var(0)));
    let Storage::Compact { entries, .. } = &replay.expressions.storage else {
        unreachable!()
    };
    assert!(matches!(
        entries.get(entries.len() - 1).unwrap().expression,
        Expression::Alias(0)
    ));
}

#[test]
fn cached_open_syntax_never_caches_a_context_dependent_inference_result() {
    let mut replay = Replay::new();
    record(&mut replay, r#"{"ie":0,"bvar":0}"#).unwrap();
    let raw = replay.expression(&number_json(0)).unwrap();
    assert!(Arc::ptr_eq(
        &raw,
        &replay.expression(&number_json(0)).unwrap()
    ));
    let nat = term(Term::Global("#pt-nat".into(), vec![]));
    let prop = term(Term::Sort(Level::number(0).unwrap()));
    let mut kernel = Kernel::new();
    let a = kernel.infer(&[nat.clone()], &raw, 0).unwrap();
    let b = kernel.infer(&[prop.clone()], &raw, 0).unwrap();
    assert!(kernel.same_syntax(&a, &nat).unwrap());
    assert!(kernel.same_syntax(&b, &prop).unwrap());
    assert!(!kernel.same_syntax(&a, &b).unwrap());
    assert!(kernel.infer(&[], &raw, 0).unwrap_err().contains("unbound"));
}

#[test]
fn source_validation_is_eager_even_when_expression_trees_are_not_materialized() {
    for retain in [false, true] {
        for input in [
            r#"{"ie":0,"app":{"fn":1,"arg":1}}"#,
            r#"{"ie":0,"sort":1}"#,
            r#"{"ie":0,"const":{"name":1,"us":[]}}"#,
            r#"{"ie":0,"strVal":"x"}"#,
            r#"{"ie":0,"natVal":"01"}"#,
            r#"{"ie":0,"natVal":"-1"}"#,
            r#"{"ie":0,"lam":{"name":0,"type":0,"body":0,"binderInfo":"unknown"}}"#,
        ] {
            let mut replay = Replay::with_retention(crate::ProofBudget::default(), retain);
            assert!(record(&mut replay, input).is_err(), "{input}");
            assert_eq!(replay.expressions.len(), 0);
        }
        let mut chain = Replay::with_retention(crate::ProofBudget::default(), retain);
        record(&mut chain, r#"{"ie":0,"bvar":0}"#).unwrap();
        for id in 1..MAX_EXPRESSION_DEPTH {
            let input = format!(r#"{{"ie":{id},"app":{{"fn":{},"arg":0}}}}"#, id - 1);
            record(&mut chain, &input).unwrap();
        }
        let input = format!(
            r#"{{"ie":{},"app":{{"fn":{},"arg":0}}}}"#,
            MAX_EXPRESSION_DEPTH,
            MAX_EXPRESSION_DEPTH - 1
        );
        assert!(record(&mut chain, &input)
            .unwrap_err()
            .contains("expression depth"));
    }
}

#[test]
fn spilling_preserves_live_syntax_and_releases_dead_sparse_handles() {
    let names = root_names();
    let levels = [Level::number(0).unwrap()];
    let mut values = Expressions::with_limit(false, std::mem::size_of::<Entry>() * 12);
    values
        .push(Expression::Var(0), 1, 0, &names, &levels)
        .unwrap();
    let owner = values.get(0, &names, &levels).unwrap();
    for _ in 1..9 {
        values
            .push(Expression::Var(0), 1, 0, &names, &levels)
            .unwrap();
    }
    assert!(values.is_spilled());
    values.end_record();
    assert!(Arc::ptr_eq(
        &owner,
        &values.get(0, &names, &levels).unwrap()
    ));
    drop(owner);
    let root = values.get(0, &names, &levels).unwrap();
    drop(root);
    values.end_record();
    assert!(slots_empty(&values));
    let Storage::Compact { materialized, .. } = &values.storage else {
        unreachable!()
    };
    assert!(materialized.borrow().slots.is_empty());
    assert!(materialized.borrow().queued.is_empty());
}

#[test]
fn dead_weak_syntax_reconstructs_backward_references_to_spilled_source_names() {
    let mut replay = Replay::new();
    replay.names = names::Names::with_limit(0);
    replay.expressions = Expressions::with_limit(false, 0);
    for input in [
        r#"{"in":1,"str":{"pre":0,"str":"Foo"}}"#,
        r#"{"in":2,"str":{"pre":1,"str":"Bar"}}"#,
    ] {
        replay
            .name_record(&crate::lsp::json::parse(input).unwrap())
            .unwrap();
    }
    record(&mut replay, r#"{"ie":0,"const":{"name":2,"us":[]}}"#).unwrap();
    record(
        &mut replay,
        r#"{"ie":1,"proj":{"typeName":1,"idx":0,"struct":0}}"#,
    )
    .unwrap();
    assert!(replay.names.is_spilled());
    assert!(replay.expressions.is_spilled());

    let original = replay.expression(&number_json(1)).unwrap();
    let weak = Arc::downgrade(&original);
    drop(original);
    replay.expressions.end_record();
    assert!(weak.upgrade().is_none());
    assert!(slots_empty(&replay.expressions));

    let rebuilt = replay.expression(&number_json(1)).unwrap();
    let Term::Project {
        family, subject, ..
    } = rebuilt.as_ref()
    else {
        panic!("projection")
    };
    assert_eq!(family, "$lean:s3:Foo");
    assert!(matches!(subject.as_ref(), Term::Global(name, levels)
        if name == "$lean:s3:Foos3:Bar" && levels.is_empty()));
}

#[test]
fn forced_spill_preserves_failures_after_the_selected_target() {
    let original = include_str!("../../../tests/fixtures/lean_export/identity.ndjson");
    let invalids = [
        format!("{original}{{\"ie\":20,\"strVal\":\"unsupported\"}}\n"),
        format!("{original}{{\"ie\":20,\"natVal\":\"0\"}}\n"),
        original.replacen("\"levelParams\":[4]", "\"levelParams\":[]", 1),
    ];
    for source in invalids {
        let normal = check_lean_export(source.as_bytes(), "Audit.identity.theorem").unwrap_err();
        let mut replay = Replay::new();
        replay.names = names::Names::with_limit(0);
        replay.expressions = Expressions::with_limit(false, 0);
        let spilled = match replay_reader(source.as_bytes(), "Audit.identity.theorem", replay) {
            Ok(_) => panic!("invalid source accepted after spilling"),
            Err(error) => error,
        };
        assert_eq!(normal, spilled);
    }
}
