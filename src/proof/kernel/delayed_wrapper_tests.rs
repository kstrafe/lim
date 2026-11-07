//! Complete observations hidden behind record-packing wrappers.
use super::*;

fn forwarder_body(builder: bool, ignore_start: bool) -> T {
    let fields = [var(1), if ignore_start { lit(3) } else { var(0) }];
    let record = if builder {
        apps(global("pack-loop-state"), &fields)
    } else {
        ctor("LoopState", "pack", fields.to_vec())
    };
    lam(nat(), lam(nat(), app(global("run-loop-state"), record)))
}

fn record_forwarders(k: &mut Kernel) {
    let function_ty = pi(nat(), nat());
    k.inductive(
        "LoopState",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![nat(), nat()])],
    )
    .unwrap();
    let field = |index| {
        term(Term::Project {
            family: "LoopState".into(),
            index,
            subject: var(0),
        })
    };
    let recursor = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), function_ty.clone()),
        branches: vec![
            lam(nat(), var(0)),
            lam(
                nat(),
                lam(function_ty, lam(nat(), app(var(1), succ(var(0))))),
            ),
        ],
        subject: field(0),
    });
    k.definition(
        "run-loop-state",
        vec![],
        pi(global("LoopState"), nat()),
        lam(global("LoopState"), app(recursor, field(1))),
        false,
    )
    .unwrap();
    k.definition(
        "pack-loop-state",
        vec![],
        pi(nat(), pi(nat(), global("LoopState"))),
        lam(
            nat(),
            lam(nat(), ctor("LoopState", "pack", vec![var(1), var(0)])),
        ),
        false,
    )
    .unwrap();
    for (name, builder, ignore) in [
        ("forward-record", false, false),
        ("forward-builder", true, false),
        ("forward-ignore", true, true),
    ] {
        k.definition(
            name,
            vec![],
            pi(nat(), pi(nat(), nat())),
            forwarder_body(builder, ignore),
            false,
        )
        .unwrap();
    }
}

fn forwarded(name: &str, count: usize, start: T) -> T {
    apps(global(name), &[lit(count), start])
}

#[test]
fn complete_record_wrapper_is_reduced_before_its_worker_is_exposed() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    for name in ["forward-record", "forward-builder"] {
        let small = forwarded(name, 3, lit(3));
        k.check(&[], &small, &nat(), 0).unwrap();
        assert!(
            matches!(agrees(&mut k, &small).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="6")
        );
        let source = forwarded(name, 64, lit(3));
        k.check(&[], &source, &nat(), 0).unwrap();
        k.reset_budget();
        assert!(k.convertible(&[], &source, &lit(67), 0).unwrap());
        assert!(k.delayed_wrapper_attempts > 0);
    }
}

#[test]
fn an_opaque_packing_wrapper_stays_neutral() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    k.opaque_definition(
        "sealed-forwarder",
        vec![],
        pi(nat(), pi(nat(), nat())),
        forwarder_body(true, false),
    )
    .unwrap();
    let source = forwarded("sealed-forwarder", 3, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert!(!k.convertible(&[], &source, &lit(6), 0).unwrap());
    assert_eq!(k.delayed_wrapper_attempts, 0);
}

#[test]
fn wrapper_observation_cannot_erase_ill_typed_caller_arguments() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let source = forwarded(
        "forward-ignore",
        0,
        term(Term::Sort(Level::number(0).unwrap())),
    );
    // Computation ignores the second argument. Source inference must not.
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_some());
    assert!(k
        .definition("bad-forwarded-call", vec![], nat(), source, false)
        .is_err());
    assert!(!k.contains("bad-forwarded-call").unwrap());
}

#[test]
fn a_selected_wrapper_still_checks_the_callers_explicit_universe_arity() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let bad = term(Term::Global(
        "forward-builder".into(),
        vec![Level::number(0).unwrap()],
    ));
    let source = apps(bad, &[lit(3), lit(3)]);
    assert!(k
        .delayed_record_wrapper(&source, 0)
        .unwrap_err()
        .contains("explicit universe"));
    assert!(!k.delayed_active);
    assert!(k.reduction_probe_budget.is_none());
    assert!(k.check(&[], &source, &nat(), 0).is_err());
}

#[test]
fn completed_wrapper_observations_share_a_finite_phase_allowance() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let source = forwarded("forward-builder", 3, lit(3));
    k.reset_budget();
    for _ in 0..4 {
        assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_some());
    }
    let spent = (k.work, k.transformed_bytes);
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert_eq!(spent, (k.work, k.transformed_bytes));
    k.reset_budget();
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_some());
}

#[test]
fn wide_wrapper_probes_obey_the_existing_hard_and_parent_limits() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let source = forwarded("forward-builder", 64, lit(3));
    k.reset_budget();
    assert!(k
        .reduction_probe(0, |k| k.delayed_record_wrapper(&source, 1))
        .unwrap()
        .unwrap()
        .is_none());
    assert_eq!(k.delayed_wrapper_attempts, 0);
    k.budget = crate::ProofBudget::new(500, 4096, 4096).unwrap();
    k.reset_budget();
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert!(k.work <= 500 && k.transformed_bytes <= 4096);
    assert!(!k.delayed_active);
    assert!(k.reduction_probe_budget.is_none());
}

#[test]
fn congruence_compares_wrapper_arguments_before_computing_the_worker() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let left = forwarded("forward-builder", 64, lit(3));
    let right = forwarded("forward-builder", 64, app(lam(nat(), var(0)), lit(3)));
    k.check(&[], &left, &nat(), 0).unwrap();
    k.check(&[], &right, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.convertible(&[], &left, &right, 0).unwrap());
    assert_eq!(k.delayed_wrapper_attempts, 0);
}

#[test]
fn a_failed_observation_is_not_retried_when_conversion_reaches_whnf() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    k.opaque_definition("blocked-scalar", vec![], nat(), lit(6))
        .unwrap();
    k.definition(
        "blocked-worker",
        vec![],
        pi(global("LoopState"), nat()),
        lam(global("LoopState"), global("blocked-scalar")),
        false,
    )
    .unwrap();
    k.definition(
        "blocked-forwarder",
        vec![],
        pi(nat(), pi(nat(), nat())),
        lam(
            nat(),
            lam(
                nat(),
                app(
                    global("blocked-worker"),
                    ctor("LoopState", "pack", vec![var(1), var(0)]),
                ),
            ),
        ),
        false,
    )
    .unwrap();
    let source = forwarded("blocked-forwarder", 3, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    let spent = (k.work, k.transformed_bytes);
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert_eq!(spent, (k.work, k.transformed_bytes));
    assert!(!k.convertible(&[], &source, &lit(6), 0).unwrap());
    assert_eq!(k.delayed_wrapper_attempts, 1);
    assert_eq!(k.failed_wrapper_roots.len(), 1);
    k.reset_budget();
    assert!(k.failed_wrapper_roots.is_empty());
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert_eq!(k.delayed_wrapper_attempts, 1);
}

#[test]
fn classifier_exhaustion_preserves_ordinary_reduction_and_resets_per_phase() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    k.definition(
        "ordinary-identity",
        vec![],
        pi(nat(), nat()),
        lam(nat(), var(0)),
        false,
    )
    .unwrap();
    let identity = app(global("ordinary-identity"), lit(3));
    k.reset_budget();
    for _ in 0..256 {
        assert!(k.delayed_record_wrapper(&identity, 0).unwrap().is_none());
    }
    let source = forwarded("forward-builder", 3, lit(3));
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert!(k.convertible(&[], &source, &lit(6), 0).unwrap());
    assert_eq!(k.delayed_wrapper_attempts, 0);
    k.reset_budget();
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_some());
}

#[test]
fn a_declined_wide_walk_leaves_budget_for_the_existing_fast_scalar_fold() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let field = |index| {
        term(Term::Project {
            family: "LoopState".into(),
            index,
            subject: var(0),
        })
    };
    let fold = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![field(1), lam(nat(), lam(nat(), succ(var(0))))],
        subject: field(0),
    });
    k.definition(
        "run-scalar-state",
        vec![],
        pi(global("LoopState"), nat()),
        lam(global("LoopState"), fold),
        false,
    )
    .unwrap();
    k.definition(
        "forward-scalar-state",
        vec![],
        pi(nat(), pi(nat(), nat())),
        lam(
            nat(),
            lam(
                nat(),
                app(
                    global("run-scalar-state"),
                    ctor("LoopState", "pack", vec![var(1), var(0)]),
                ),
            ),
        ),
        false,
    )
    .unwrap();
    let source = forwarded("forward-scalar-state", 1_000_000, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    // Linear iota evaluation cannot finish within the optional probe. The
    // ordinary affine recognizer computes the exact result in the remainder.
    assert!(k.convertible(&[], &source, &lit(1_000_003), 0).unwrap());
    assert_eq!(k.failed_wrapper_roots.len(), 1);
    assert!(k.work < k.budget.work());
    assert!(k.transformed_bytes < k.budget.phase_bytes());
}

#[test]
fn a_pure_transparent_alias_reaches_the_record_wrapper() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    k.definition(
        "record-alias",
        vec![],
        pi(nat(), pi(nat(), nat())),
        global("forward-builder"),
        false,
    )
    .unwrap();
    let source = forwarded("record-alias", 64, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(
        matches!(k.delayed_record_wrapper(&source, 0).unwrap().as_ref().map(T::as_ref), Some(Term::NatLiteral { family, value }) if family == NAT && value.decimal() == "67")
    );
    k.reset_budget();
    assert!(k.convertible(&[], &source, &lit(67), 0).unwrap());
}

#[test]
fn a_partial_application_alias_carries_its_captured_argument() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    k.definition(
        "partial-record-alias",
        vec![],
        pi(nat(), nat()),
        app(global("forward-builder"), lit(64)),
        false,
    )
    .unwrap();
    let source = app(global("partial-record-alias"), lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(
        matches!(k.delayed_record_wrapper(&source, 0).unwrap().as_ref().map(T::as_ref), Some(Term::NatLiteral { family, value }) if family == NAT && value.decimal() == "67")
    );
    k.reset_budget();
    assert!(k.convertible(&[], &source, &lit(67), 0).unwrap());
}

#[test]
fn a_record_tail_worker_can_capture_an_explicit_function_argument() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let function_ty = pi(nat(), nat());
    k.definition(
        "mapped-state-worker",
        vec![],
        pi(function_ty.clone(), pi(global("LoopState"), nat())),
        lam(
            function_ty,
            lam(
                global("LoopState"),
                app(var(1), app(global("run-loop-state"), var(0))),
            ),
        ),
        false,
    )
    .unwrap();
    k.definition(
        "mapped-state-forwarder",
        vec![],
        pi(pi(nat(), nat()), pi(nat(), pi(nat(), nat()))),
        lam(
            pi(nat(), nat()),
            lam(
                nat(),
                lam(
                    nat(),
                    apps(
                        global("mapped-state-worker"),
                        &[var(2), ctor("LoopState", "pack", vec![var(1), var(0)])],
                    ),
                ),
            ),
        ),
        false,
    )
    .unwrap();
    let increment = lam(nat(), succ(var(0)));
    let source = apps(
        global("mapped-state-forwarder"),
        &[increment, lit(3), lit(3)],
    );
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(
        matches!(k.delayed_record_wrapper(&source, 0).unwrap().as_ref().map(T::as_ref), Some(Term::NatLiteral { family, value }) if family == NAT && value.decimal() == "7")
    );
    k.reset_budget();
    assert!(k.convertible(&[], &source, &lit(7), 0).unwrap());
}

#[test]
fn an_opaque_intermediate_alias_declines_without_a_wide_attempt() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    k.opaque_definition(
        "sealed-record-alias",
        vec![],
        pi(nat(), pi(nat(), nat())),
        global("forward-builder"),
    )
    .unwrap();
    k.definition(
        "outer-record-alias",
        vec![],
        pi(nat(), pi(nat(), nat())),
        global("sealed-record-alias"),
        false,
    )
    .unwrap();
    let source = forwarded("outer-record-alias", 64, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert_eq!(k.delayed_wrapper_attempts, 0);
}

#[test]
fn forwarding_inspection_stops_at_its_fixed_hop_limit() {
    let mut k = Kernel::new();
    record_forwarders(&mut k);
    let mut previous = "forward-builder".to_owned();
    for index in 0..9 {
        let name = format!("bounded-record-alias-{index}");
        k.definition(
            &name,
            vec![],
            pi(nat(), pi(nat(), nat())),
            global(&previous),
            false,
        )
        .unwrap();
        previous = name;
    }
    let source = forwarded(&previous, 3, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.delayed_record_wrapper(&source, 0).unwrap().is_none());
    assert_eq!(k.delayed_wrapper_attempts, 0);
    assert!(k.convertible(&[], &source, &lit(6), 0).unwrap());
}
