use super::*;

fn sort_var(name: &str) -> T {
    term(Term::Sort(Level::variable(name.into())))
}

fn nat() -> T {
    term(Term::Global("#pt-nat".into(), vec![]))
}

fn map(name: &str, value: u32) -> HashMap<String, Level> {
    HashMap::from([(name.to_owned(), Level::number(value).unwrap())])
}

#[test]
fn exact_source_map_and_depth_reuse_only_within_the_specialized_phase() {
    let mut k = Kernel::new();
    let source = sort_var("u");
    let _source_owner = source.clone();
    let substitution = map("u", 3);
    let first = k.specialized_universes(&source, &substitution, 0).unwrap();
    let work = k.work;
    let bytes = k.transformation_bytes();
    let second = k.specialized_universes(&source, &substitution, 0).unwrap();
    assert!(Arc::ptr_eq(&first, &second));
    assert!(k.work > work, "a cache hit still ticks the kernel budget");
    assert_eq!(k.transformation_bytes(), bytes);

    let other_map = k.specialized_universes(&source, &map("u", 4), 0).unwrap();
    let other_source = sort_var("u");
    let other_root = k
        .specialized_universes(&other_source, &substitution, 0)
        .unwrap();
    let other_depth = k.specialized_universes(&source, &substitution, 1).unwrap();
    assert!(!Arc::ptr_eq(&first, &other_map));
    assert!(!Arc::ptr_eq(&first, &other_root));
    assert!(Arc::ptr_eq(&first, &other_depth));

    // Ordinary scope substitutions deliberately remain fresh and uncached.
    let ordinary = k.universes(&source, &substitution, 0).unwrap();
    assert!(!Arc::ptr_eq(&first, &ordinary));
}

#[test]
fn undeclared_universe_error_is_not_hidden_by_a_warm_entry() {
    let mut k = Kernel::new();
    let source = sort_var("missing");
    let _source_owner = source.clone();
    let bad_map = HashMap::new();
    k.specialized_universes(&source, &map("missing", 1), 0)
        .unwrap();
    assert!(k.specialized_universes(&source, &bad_map, 0).is_err());
    assert!(k.specialized_universes(&source, &bad_map, 0).is_err());
}

#[test]
fn reset_budget_flushes_specialization_reuse() {
    let mut k = Kernel::new();
    let source = sort_var("u");
    let _source_owner = source.clone();
    let substitution = map("u", 2);
    let first = k.specialized_universes(&source, &substitution, 0).unwrap();
    k.reset_budget();
    let after_reset = k.specialized_universes(&source, &substitution, 0).unwrap();
    assert!(!Arc::ptr_eq(&first, &after_reset));
}

#[test]
fn unshared_sources_keep_the_ordinary_substitution_budget() {
    let source = sort_var("u");
    let substitution = map("u", 2);
    let mut ordinary = Kernel::new();
    ordinary.universes(&source, &substitution, 0).unwrap();
    let mut specialized = Kernel::new();
    specialized
        .specialized_universes(&source, &substitution, 0)
        .unwrap();
    assert_eq!(specialized.work, ordinary.work);
    assert_eq!(
        specialized.transformation_bytes(),
        ordinary.transformation_bytes()
    );
    assert_eq!(specialized.specializations.usage(), (0, 0));
}

#[test]
fn large_shared_closed_constructor_graph_skips_optional_cache_sizing() {
    let mut k = Kernel::new();
    k.inductive(
        "Tree",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![
            ("leaf".into(), vec![]),
            (
                "node".into(),
                vec![term(Term::SelfType), term(Term::SelfType)],
            ),
        ],
    )
    .unwrap();
    // A balanced tree with 3,001 distinct constructor nodes. Distinct leaves
    // ensure a complete optional sizing walk needs more than the 5,000-work
    // reserve, while substitution can retain this closed tree by identity.
    let mut layer = (0..1501)
        .map(|_| {
            term(Term::Ctor {
                family: "Tree".into(),
                levels: vec![],
                parameters: vec![],
                constructor: "leaf".into(),
                fields: vec![],
            })
        })
        .collect::<Vec<_>>();
    while layer.len() > 1 {
        let mut next = layer
            .chunks_exact(2)
            .map(|pair| {
                term(Term::Ctor {
                    family: "Tree".into(),
                    levels: vec![],
                    parameters: vec![],
                    constructor: "node".into(),
                    fields: pair.to_vec(),
                })
            })
            .collect::<Vec<_>>();
        if let Some(last) = layer.chunks_exact(2).remainder().first() {
            next.push(last.clone());
        }
        layer = next;
    }
    let closed_tree = layer.pop().unwrap();
    let source = term(Term::Lam(sort_var("u"), closed_tree.clone()));
    let _source_owner = source.clone();
    k.definition(
        "checked-specialization-source",
        vec!["u".into()],
        term(Term::Pi(
            sort_var("u"),
            term(Term::Global("Tree".into(), vec![])),
        )),
        source.clone(),
        false,
    )
    .unwrap();

    let budget = k.budget.work();
    k.work = budget - 5_000;
    let before = k.work;
    let result = k.specialized_universes(&source, &map("u", 0), 0).unwrap();
    assert!(matches!(result.as_ref(), Term::Lam(domain, body)
        if matches!(domain.as_ref(), Term::Sort(level) if level == &Level::number(0).unwrap())
            && Arc::ptr_eq(body, &closed_tree)));
    assert_eq!(k.specializations.usage(), (0, 0));
    assert!(
        k.work > before,
        "completed substitution work must remain charged"
    );
    assert!(
        k.work - before < 100,
        "substitution should touch only the changed domain"
    );
    assert!(
        k.work < budget,
        "optional sizing must decline before exhausting the reserve"
    );
}

#[test]
fn identity_substitution_does_not_retain_a_useless_cache_entry() {
    let mut k = Kernel::new();
    let source = term(Term::Sort(Level::number(0).unwrap()));
    let _source_owner = source.clone();
    let result = k
        .specialized_universes(&source, &HashMap::new(), 0)
        .unwrap();
    assert!(Arc::ptr_eq(&source, &result));
    assert_eq!(k.specializations.usage(), (0, 0));
}

#[test]
fn repeated_large_specializations_save_work_and_allocation() {
    let mut source = sort_var("u");
    for _ in 0..40 {
        source = term(Term::Lam(sort_var("u"), source));
    }
    let _owner = source.clone();
    let substitution = map("u", 2);
    let mut fresh = Kernel::new();
    let expected = fresh.universes(&source, &substitution, 0).unwrap();
    let fresh_work = fresh.work;
    let mut reused = Kernel::new();
    let first = reused
        .specialized_universes(&source, &substitution, 0)
        .unwrap();
    let before_work = reused.work;
    let before_bytes = reused.transformation_bytes();
    let second = reused
        .specialized_universes(&source, &substitution, 0)
        .unwrap();
    assert!(Arc::ptr_eq(&first, &second));
    assert!(fresh.same_syntax(&expected, &second).unwrap());
    assert!((reused.work - before_work) * 10 < fresh_work);
    assert_eq!(reused.transformation_bytes(), before_bytes);
}

#[test]
fn retained_specializations_do_not_keep_source_roots_alive() {
    let source = sort_var("u");
    let owner = source.clone();
    let weak = Arc::downgrade(&source);
    let mut k = Kernel::new();
    k.specialized_universes(&source, &map("u", 3), 0).unwrap();
    assert_eq!(k.specializations.usage().0, 1);
    drop(owner);
    drop(source);
    assert!(weak.upgrade().is_none());
    assert_eq!(k.specializations.usage().0, 1);
}

#[test]
fn warm_specialization_does_not_bypass_global_validation_or_opacity() {
    let mut k = Kernel::new();
    let poly_type = term(Term::Sort(Level::variable("v".into()).successor().unwrap()));
    k.definition(
        "poly",
        vec!["v".into()],
        poly_type,
        term(Term::Sort(Level::variable("v".into()))),
        false,
    )
    .unwrap();
    let valid = term(Term::Global("poly".into(), vec![Level::number(3).unwrap()]));
    k.whnf(&[], &valid, 0).unwrap();
    let wrong_arity = term(Term::Global("poly".into(), vec![]));
    let _ = k
        .specialized_universes(&wrong_arity, &HashMap::new(), 0)
        .unwrap();
    let err = k
        .definition(
            "bad-arity",
            vec![],
            wrong_arity.clone(),
            wrong_arity.clone(),
            false,
        )
        .unwrap_err();
    assert!(err.contains("explicit universe argument"), "{err}");
    assert!(k.whnf(&[], &wrong_arity, 0).is_err());
    assert!(k.natural_head(&wrong_arity, 0).is_err());

    let unknown = term(Term::Global("unchecked-source".into(), vec![]));
    let _ = k
        .specialized_universes(&unknown, &HashMap::new(), 0)
        .unwrap();
    let err = k
        .definition("bad-source", vec![], unknown.clone(), unknown, false)
        .unwrap_err();
    assert!(
        err.contains("unknown") || err.contains("unchecked"),
        "{err}"
    );

    k.opaque_definition(
        "sealed",
        vec![],
        nat(),
        term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse("7").unwrap(),
        }),
    )
    .unwrap();
    let sealed = term(Term::Global("sealed".into(), vec![]));
    let reduced = k.whnf(&[], &sealed, 0).unwrap();
    assert!(Arc::ptr_eq(&sealed, &reduced));
}

#[test]
fn exhausted_work_budget_rejects_a_specialization_cache_hit() {
    let mut k = Kernel::new();
    let source = sort_var("u");
    let _source_owner = source.clone();
    let substitution = map("u", 2);
    k.specialized_universes(&source, &substitution, 0).unwrap();
    k.work = k.budget.work();
    let err = k
        .specialized_universes(&source, &substitution, 0)
        .unwrap_err();
    assert!(
        err.contains("resource limit") || err.contains("work units"),
        "{err}"
    );
}

#[test]
fn exhausted_allocation_budget_rejects_a_warm_cache_hit() {
    let mut k = Kernel::new();
    let source = sort_var("u");
    let _source_owner = source.clone();
    let substitution = map("u", 2);
    k.specialized_universes(&source, &substitution, 0).unwrap();
    k.transformed_bytes = k.budget.phase_bytes() + 1;
    assert!(k
        .specialized_universes(&source, &substitution, 0)
        .unwrap_err()
        .contains("allocation limit"));
}

#[test]
fn recorded_height_checks_descendants_and_narrower_probe_limits() {
    let mut k = Kernel::new();
    let mut source = sort_var("u");
    for _ in 0..60 {
        source = term(Term::Lam(sort_var("u"), source));
    }
    let substitution = map("u", 2);
    let _source_owner = source.clone();
    let first = k.specialized_universes(&source, &substitution, 0).unwrap();
    let shifted_depth = k.specialized_universes(&source, &substitution, 4).unwrap();
    assert!(Arc::ptr_eq(&first, &shifted_depth));
    let too_deep = k
        .specialized_universes(&source, &substitution, 40)
        .unwrap_err();
    assert!(too_deep.contains("recursion depth 97 > 96"), "{too_deep}");
    k.work = 0;
    let probe = k
        .reduction_probe(0, |kernel| {
            kernel.specialized_universes(&source, &substitution, 0)
        })
        .unwrap();
    assert!(
        probe.is_none(),
        "ordinary cached height cannot bypass the probe's depth limit"
    );
}

#[test]
fn retained_results_obey_entry_and_byte_caps() {
    let mut k = Kernel::new();
    let substitution = map("u", 2);
    let roots = (0..80).map(|_| sort_var("u")).collect::<Vec<_>>();
    let _source_owners = roots.clone();
    let mut values = Vec::new();
    for root in &roots {
        values.push(k.specialized_universes(root, &substitution, 0).unwrap());
    }
    let (entries, bytes) = k.specializations.usage();
    assert_eq!(entries, 64);
    assert!(bytes <= 2 * 1024 * 1024);
    assert!(Arc::ptr_eq(
        &values[79],
        &k.specialized_universes(&roots[79], &substitution, 0)
            .unwrap()
    ));
    assert!(!Arc::ptr_eq(
        &values[0],
        &k.specialized_universes(&roots[0], &substitution, 0)
            .unwrap()
    ));

    k.reset_budget();
    let roots = (0..16)
        .map(|_| {
            term(Term::App(
                term(Term::Global("x".repeat(192 * 1024), vec![])),
                sort_var("u"),
            ))
        })
        .collect::<Vec<_>>();
    let _source_owners = roots.clone();
    for root in &roots {
        k.specialized_universes(root, &substitution, 0).unwrap();
    }
    let (entries, bytes) = k.specializations.usage();
    assert!(entries > 0 && entries < 16);
    assert!(bytes <= 2 * 1024 * 1024);
}

#[test]
fn same_source_maps_over_capacity_keep_recent_entries_and_miss_old_entries() {
    let mut k = Kernel::new();
    let source = sort_var("u");
    let _source_owner = source.clone();
    let mut values = Vec::new();
    for value in 0..80 {
        values.push(
            k.specialized_universes(&source, &map("u", value), 0)
                .unwrap(),
        );
    }
    assert_eq!(k.specializations.usage().0, 64);

    // The newest and a recently used map remain reusable after the slot
    // collection has been exercised beyond its bounded capacity.
    assert!(Arc::ptr_eq(
        &values[79],
        &k.specialized_universes(&source, &map("u", 79), 0).unwrap()
    ));
    assert!(Arc::ptr_eq(
        &values[70],
        &k.specialized_universes(&source, &map("u", 70), 0).unwrap()
    ));

    // The oldest map was evicted; looking it up must safely specialize afresh
    // and leave the bounded cache usable for another lookup.
    let old = k.specialized_universes(&source, &map("u", 0), 0).unwrap();
    assert!(!Arc::ptr_eq(&values[0], &old));
    assert!(Arc::ptr_eq(
        &values[79],
        &k.specialized_universes(&source, &map("u", 79), 0).unwrap()
    ));
    assert_eq!(k.specializations.usage().0, 64);
}

#[test]
fn declaration_term_weight_propagates_meter_errors() {
    let value = sort_var("u");
    let mut calls = 0;
    let result = super::declarations::term_weight(&value, usize::MAX, &mut |amount| {
        calls += 1;
        if amount == 0 {
            Ok(())
        } else {
            Err("meter stopped".to_owned())
        }
    });
    assert_eq!(calls, 2);
    assert_eq!(result.unwrap_err(), "meter stopped");
}

#[test]
fn oversized_values_and_low_reserves_use_fresh_substitution() {
    let mut k = Kernel::new();
    let substitution = map("u", 3);
    let source = term(Term::App(
        term(Term::Global("x".repeat(3 * 1024 * 1024), vec![])),
        sort_var("u"),
    ));
    let _source_owner = source.clone();
    let first = k.specialized_universes(&source, &substitution, 0).unwrap();
    let second = k.specialized_universes(&source, &substitution, 0).unwrap();
    assert!(!Arc::ptr_eq(&first, &second));
    assert_eq!(k.specializations.usage(), (0, 0));

    let mut limited = Kernel::with_budget(crate::ProofBudget::new(1000, 4096, 4096).unwrap());
    let source = sort_var("u");
    let _source_owner = source.clone();
    limited
        .specialized_universes(&source, &substitution, 0)
        .unwrap();
    assert_eq!(limited.specializations.usage(), (0, 0));
}

#[test]
fn cache_does_not_pin_source_and_immutable_root_replacement_cannot_reuse_stale_entry() {
    let mut k = Kernel::new();
    let mut source = sort_var("u");
    let _source_owner = source.clone();
    let first = k.specialized_universes(&source, &map("u", 3), 0).unwrap();
    // Replacing the immutable root creates a different source identity.
    source = term(Term::Sort(Level::variable("v".into())));
    let second = k.specialized_universes(&source, &map("v", 4), 0).unwrap();
    assert!(!Arc::ptr_eq(&first, &second));
    assert!(k
        .same_syntax(&second, &term(Term::Sort(Level::number(4).unwrap())))
        .unwrap());
    let weak = Arc::downgrade(&source);
    drop(source);
    assert!(weak.upgrade().is_none());
}
