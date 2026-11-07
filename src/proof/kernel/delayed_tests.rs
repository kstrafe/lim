//! Compare delayed operational reduction with the ordinary checker.
use super::*;

const NAT: &str = "#pt-nat";
fn var(i: usize) -> T {
    term(Term::Var(i))
}
fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn nat() -> T {
    global(NAT)
}
fn lit(n: usize) -> T {
    term(Term::NatLiteral {
        family: NAT.into(),
        value: Natural::parse(&n.to_string()).unwrap(),
    })
}
fn lam(a: T, b: T) -> T {
    term(Term::Lam(a, b))
}
fn pi(a: T, b: T) -> T {
    term(Term::Pi(a, b))
}
fn app(a: T, b: T) -> T {
    term(Term::App(a, b))
}
fn succ(n: T) -> T {
    ctor(NAT, "succ", vec![n])
}
fn ctor(family: &str, name: &str, fields: Vec<T>) -> T {
    term(Term::Ctor {
        family: family.into(),
        levels: vec![],
        parameters: vec![],
        constructor: name.into(),
        fields,
    })
}
fn eq(left: T, right: T) -> T {
    term(Term::Eq(nat(), left, right))
}
fn agrees(k: &mut Kernel, source: &T) -> Option<T> {
    let delayed = k.delayed_scalar(source, 0).unwrap();
    if let Some(result) = &delayed {
        let previous = k.delayed_active;
        k.delayed_active = true;
        let reference = k.reduction_probe(0, |k| {
            let ordinary = k.whnf(&[], source, 0)?;
            k.convertible(&[], result, &ordinary, 0)
        });
        k.delayed_active = previous;
        assert!(reference.unwrap().expect("small ordinary reference"));
    }
    delayed
}
fn fold(subject: T) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![lit(0), lam(nat(), lam(nat(), succ(var(0))))],
        subject,
    })
}

#[test]
fn captured_nested_lambda_and_let_keep_lexical_indices() {
    let mut k = Kernel::new();
    // The let captures a before y and x are bound; z is then at index 2.
    let body = term(Term::Let(nat(), var(0), lam(nat(), lam(nat(), var(2)))));
    let source = apps(lam(nat(), body), &[lit(9), lit(17), lit(23)]);
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="9")
    );
}

#[test]
fn record_and_sigma_projections_use_the_payloads_captured_environment() {
    let mut k = Kernel::new();
    let pair_ty = term(Term::Sigma(nat(), nat()));
    let pair = term(Term::Pair(pair_ty.clone(), lit(4), var(0)));
    let projected = term(Term::Second(var(0)));
    let source = app(lam(nat(), app(lam(pair_ty, projected), pair)), lit(8));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="8")
    );

    k.inductive(
        "DelayedRecord",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![nat(), nat()])],
    )
    .unwrap();
    let record = ctor("DelayedRecord", "pack", vec![lit(3), var(0)]);
    let projection = term(Term::Project {
        family: "DelayedRecord".into(),
        index: 1,
        subject: var(0),
    });
    let source = app(
        lam(nat(), app(lam(global("DelayedRecord"), projection), record)),
        lit(6),
    );
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="6")
    );
}

#[test]
fn canonical_nat_induction_fold_returns_the_ordinary_result() {
    let mut k = Kernel::new();
    let source = fold(lit(5));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, family }) if family==NAT && value.decimal()=="5")
    );
}

#[test]
fn nat_recursion_returns_a_function_with_a_captured_induction_hypothesis() {
    let mut k = Kernel::new();
    let function_ty = pi(nat(), nat());
    let recursor = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), function_ty.clone()),
        branches: vec![
            lam(nat(), var(0)),
            // pred / oldFn / x => oldFn (succ x).
            lam(
                nat(),
                lam(function_ty, lam(nat(), app(var(1), succ(var(0))))),
            ),
        ],
        subject: lit(5),
    });
    k.check(&[], &recursor, &pi(nat(), nat()), 0).unwrap();
    let source = app(recursor, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, family }) if family == NAT && value.decimal() == "8")
    );
}

#[test]
fn ordinary_conversion_uses_the_delayed_higher_order_fallback() {
    let mut k = Kernel::new();
    let function_ty = pi(nat(), nat());
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
                lam(function_ty, lam(nat(), succ(app(var(1), succ(var(0)))))),
            ),
        ],
        subject: lit(64),
    });
    let source = app(recursor, lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    // The successor outside the changed-argument call excludes both fixed
    // argument fusion and identity-base tail composition. The VM handles it.
    assert!(k.convertible(&[], &source, &lit(131), 0).unwrap());
    assert!(!k.delayed_active);
    assert!(k.reduction_probe_budget.is_none());
}

#[test]
fn a_partially_applied_higher_order_recursor_waits_for_its_scalar_consumer() {
    let mut k = Kernel::new();
    let function_ty = pi(nat(), pi(nat(), nat()));
    let recursor = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), function_ty.clone()),
        branches: vec![
            lam(nat(), lam(nat(), var(0))),
            lam(nat(), lam(function_ty, var(0))),
        ],
        subject: lit(5),
    });
    let partial = app(recursor, lit(3));
    k.check(&[], &partial, &pi(nat(), nat()), 0).unwrap();
    assert!(!k.delayed_candidate(&partial));
    assert!(k.delayed_scalar(&partial, 0).unwrap().is_none());
    let full = app(partial, lit(4));
    k.check(&[], &full, &nat(), 0).unwrap();
    assert!(k.delayed_candidate(&full));
    assert!(
        matches!(agrees(&mut k, &full).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="4")
    );
}

#[test]
fn recursive_record_state_preserves_sigma_payload_environments() {
    let mut k = Kernel::new();
    let pair_ty = term(Term::Sigma(nat(), nat()));
    k.inductive(
        "DelayedState",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![pair_ty.clone()])],
    )
    .unwrap();
    let payload = |subject| {
        term(Term::Project {
            family: "DelayedState".into(),
            index: 0,
            subject,
        })
    };
    // Each step captures oldState in a new record and sigma payload. The base
    // captures the outer seed, which has a different lexical environment.
    let base = ctor(
        "DelayedState",
        "pack",
        vec![term(Term::Pair(pair_ty.clone(), lit(0), var(0)))],
    );
    let step = lam(
        nat(),
        lam(
            global("DelayedState"),
            ctor(
                "DelayedState",
                "pack",
                vec![term(Term::Pair(
                    pair_ty,
                    succ(term(Term::First(payload(var(0))))),
                    succ(term(Term::Second(payload(var(0))))),
                ))],
            ),
        ),
    );
    let state = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), global("DelayedState")),
        branches: vec![base, step],
        subject: lit(5),
    });
    let source = app(lam(nat(), term(Term::Second(payload(state)))), lit(3));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, family }) if family == NAT && value.decimal() == "8")
    );
}

#[test]
fn canonical_families_keep_their_nominal_identity() {
    let mut k = Kernel::new();
    k.inductive(
        "OtherNat",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![
            ("zero".into(), vec![]),
            ("next".into(), vec![global("OtherNat")]),
        ],
    )
    .unwrap();
    let source = ctor("OtherNat", "zero", vec![]);
    k.check(&[], &source, &global("OtherNat"), 0).unwrap();
    let result = agrees(&mut k, &source).unwrap();
    assert!(
        matches!(result.as_ref(), Term::NatLiteral { family, value } if family=="OtherNat" && value.decimal()=="0")
    );
    k.check(&[], &result, &global("OtherNat"), 0).unwrap();
    assert!(k.check(&[], &result, &nat(), 0).is_err());
}

#[test]
fn an_altered_constructor_model_uses_actual_fields_without_a_natural_shortcut() {
    let mut k = Kernel::new();
    k.inductive(
        "NotNat",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("zero".into(), vec![]), ("next".into(), vec![nat()])],
    )
    .unwrap();
    let source = term(Term::Induct {
        family: "NotNat".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global("NotNat"), nat()),
        branches: vec![lit(0), lam(nat(), var(0))],
        subject: ctor("NotNat", "next", vec![lit(4)]),
    });
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, family }) if family==NAT && value.decimal()=="4")
    );
}

#[test]
fn equality_elimination_keeps_refl_and_convertible_endpoint_rules() {
    let mut k = Kernel::new();
    let proof = term(Term::Refl(nat(), lit(4)));
    k.opaque_definition("sealed-equality", vec![], eq(lit(4), lit(4)), proof.clone())
        .unwrap();
    for proof in [proof, global("sealed-equality")] {
        let source = term(Term::EqElim {
            ty: nat(),
            left: lit(4),
            right: app(lam(nat(), var(0)), lit(4)),
            motive: lam(nat(), lam(eq(lit(4), var(0)), nat())),
            base: lit(9),
            proof,
        });
        k.check(&[], &source, &nat(), 0).unwrap();
        assert!(
            matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="9")
        );
    }
}

fn indexed_family(family: &str, parameter: T, index: T) -> T {
    apps(global(family), &[parameter, index])
}

fn nullary_induction(
    family: &str,
    parameters: Vec<T>,
    indices: Vec<T>,
    motive: T,
    branch: T,
    subject: T,
) -> T {
    term(Term::Induct {
        family: family.into(),
        levels: vec![],
        parameters,
        indices,
        motive,
        branches: vec![branch],
        subject,
    })
}

fn declare_nullary_indexed_family(k: &mut Kernel, family: &str, sort: u32) {
    k.indexed_inductive(
        family,
        vec![],
        vec![nat()],
        vec![nat()],
        Level::number(sort).unwrap(),
        vec![("witness".into(), vec![], vec![var(0)])],
    )
    .unwrap();
}

fn indexed_witness(family: &str, parameter: T) -> T {
    term(Term::Ctor {
        family: family.into(),
        levels: vec![],
        parameters: vec![parameter],
        constructor: "witness".into(),
        fields: vec![],
    })
}

#[test]
fn neutral_nullary_unindexed_unit_reduces_to_its_branch() {
    let mut k = Kernel::new();
    k.inductive(
        "KUnit",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("unit".into(), vec![])],
    )
    .unwrap();
    k.opaque_definition(
        "sealed-unit",
        vec![],
        global("KUnit"),
        ctor("KUnit", "unit", vec![]),
    )
    .unwrap();
    let source = nullary_induction(
        "KUnit",
        vec![],
        vec![],
        lam(global("KUnit"), nat()),
        lit(7),
        global("sealed-unit"),
    );
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, family }) if family == NAT && value.decimal() == "7")
    );
}

#[test]
fn neutral_prop_k_specializes_constructor_indices_with_value_parameters() {
    let mut k = Kernel::new();
    declare_nullary_indexed_family(&mut k, "KIndex", 0);
    k.opaque_definition(
        "sealed-indexed-proof",
        vec![],
        indexed_family("KIndex", lit(4), lit(4)),
        indexed_witness("KIndex", lit(4)),
    )
    .unwrap();
    let motive = lam(nat(), lam(indexed_family("KIndex", lit(4), var(0)), nat()));
    let source = nullary_induction(
        "KIndex",
        vec![lit(4)],
        vec![app(lam(nat(), var(0)), lit(4))],
        motive.clone(),
        lit(8),
        global("sealed-indexed-proof"),
    );
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, family }) if family == NAT && value.decimal() == "8")
    );

    // Operational reduction must compare the requested fibre with the
    // specialized constructor result even before the checker rejects it.
    let wrong = nullary_induction(
        "KIndex",
        vec![lit(4)],
        vec![lit(5)],
        motive,
        lit(8),
        global("sealed-indexed-proof"),
    );
    assert!(k.delayed_scalar(&wrong, 0).unwrap().is_none());
    assert!(k.check(&[], &wrong, &nat(), 0).is_err());
}

#[test]
fn neutral_indexed_type_one_stays_stuck_even_at_the_constructor_index() {
    let mut k = Kernel::new();
    declare_nullary_indexed_family(&mut k, "KDataIndex", 1);
    k.opaque_definition(
        "sealed-indexed-data",
        vec![],
        indexed_family("KDataIndex", lit(2), lit(2)),
        indexed_witness("KDataIndex", lit(2)),
    )
    .unwrap();
    let source = nullary_induction(
        "KDataIndex",
        vec![lit(2)],
        vec![lit(2)],
        lam(
            nat(),
            lam(indexed_family("KDataIndex", lit(2), var(0)), nat()),
        ),
        lit(9),
        global("sealed-indexed-data"),
    );
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(agrees(&mut k, &source).is_none());
    let previous = k.delayed_active;
    k.delayed_active = true;
    let ordinary = k.reduction_probe(0, |k| k.whnf(&[], &source, 0));
    k.delayed_active = previous;
    assert!(matches!(
        ordinary.unwrap().expect("small ordinary reference").as_ref(),
        Term::Induct { family, .. } if family == "KDataIndex"
    ));
}

fn declare_universe_sensitive_k(k: &mut Kernel) {
    let u = Level::variable("u".into());
    let family = |parameter, index| {
        apps(
            term(Term::Global("UniverseK".into(), vec![u.clone()])),
            &[parameter, index],
        )
    };
    k.indexed_inductive(
        "UniverseK",
        vec!["u".into()],
        vec![nat()],
        vec![nat()],
        u.clone(),
        vec![("witness".into(), vec![], vec![var(0)])],
    )
    .unwrap();
    k.opaque_definition(
        "sealed-universe-proof",
        vec!["u".into()],
        pi(nat(), family(var(0), var(0))),
        lam(
            nat(),
            term(Term::Ctor {
                family: "UniverseK".into(),
                levels: vec![u.clone()],
                parameters: vec![var(0)],
                constructor: "witness".into(),
                fields: vec![],
            }),
        ),
    )
    .unwrap();
    let source = term(Term::Induct {
        family: "UniverseK".into(),
        levels: vec![u.clone()],
        parameters: vec![lit(4)],
        indices: vec![lit(4)],
        motive: lam(nat(), lam(family(lit(4), var(0)), nat())),
        branches: vec![lit(9)],
        subject: app(
            term(Term::Global(
                "sealed-universe-proof".into(),
                vec![u.clone()],
            )),
            lit(4),
        ),
    });
    k.definition(
        "universe-dependent-scalar",
        vec!["u".into()],
        nat(),
        source,
        false,
    )
    .unwrap();
}

fn universe_scalar(level: u32) -> T {
    term(Term::Global(
        "universe-dependent-scalar".into(),
        vec![Level::number(level).unwrap()],
    ))
}

fn identity_fold(base: T, subject: T) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![base, lam(nat(), lam(nat(), var(0)))],
        subject,
    })
}

#[test]
fn repeated_polymorphic_bodies_keep_their_checked_prop_specialization() {
    let mut k = Kernel::new();
    declare_universe_sensitive_k(&mut k);
    let source = identity_fold(universe_scalar(0), universe_scalar(0));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="9")
    );
}

#[test]
fn cached_prop_body_cannot_turn_a_type_singleton_into_a_k_reduction() {
    let mut k = Kernel::new();
    declare_universe_sensitive_k(&mut k);
    // Evaluating the count first caches the Prop body. The base uses the
    // SAME declaration at Type: its opaque indexed subject must stay stuck.
    let source = identity_fold(universe_scalar(1), universe_scalar(0));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(k.delayed_scalar(&source, 0).unwrap().is_none());
}

fn direct_list(parameter: T, constructor: &str, fields: Vec<T>) -> T {
    term(Term::Ctor {
        family: "DirectList".into(),
        levels: vec![],
        parameters: vec![parameter],
        constructor: constructor.into(),
        fields,
    })
}

#[test]
fn direct_parameterized_list_fold_preserves_captured_fields() {
    let mut k = Kernel::new();
    k.inductive(
        "DirectList",
        vec![],
        vec![term(Term::Sort(Level::number(1).unwrap()))],
        Level::number(1).unwrap(),
        vec![
            ("nil".into(), vec![]),
            (
                "cons".into(),
                vec![var(0), app(global("DirectList"), var(1))],
            ),
        ],
    )
    .unwrap();
    let list_type = app(global("DirectList"), nat());
    let list = direct_list(
        nat(),
        "cons",
        vec![var(0), direct_list(nat(), "nil", vec![])],
    );
    // Returning the head tests that a captured value remains in its source
    // environment while the tail and its recursive result are added.
    let fold = term(Term::Induct {
        family: "DirectList".into(),
        levels: vec![],
        parameters: vec![nat()],
        indices: vec![],
        motive: lam(list_type.clone(), nat()),
        branches: vec![lit(0), lam(nat(), lam(list_type, lam(nat(), var(2))))],
        subject: list,
    });
    let source = app(lam(nat(), fold), lit(19));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(matches!(agrees(&mut k, &source).as_ref().map(T::as_ref),
        Some(Term::NatLiteral {value, ..}) if value.decimal()=="19"));
}

#[test]
fn direct_recursive_fields_keep_induction_hypotheses_interleaved() {
    let mut k = Kernel::new();
    k.inductive(
        "DirectTree",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![
            ("leaf".into(), vec![]),
            (
                "fork".into(),
                vec![global("DirectTree"), nat(), global("DirectTree")],
            ),
        ],
    )
    .unwrap();
    let source = term(Term::Induct {
        family: "DirectTree".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global("DirectTree"), nat()),
        branches: vec![
            lit(0),
            lam(
                global("DirectTree"),
                lam(
                    nat(),
                    lam(nat(), lam(global("DirectTree"), lam(nat(), var(2)))),
                ),
            ),
        ],
        subject: ctor(
            "DirectTree",
            "fork",
            vec![
                ctor("DirectTree", "leaf", vec![]),
                lit(23),
                ctor("DirectTree", "leaf", vec![]),
            ],
        ),
    });
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(matches!(agrees(&mut k, &source).as_ref().map(T::as_ref),
        Some(Term::NatLiteral {value, ..}) if value.decimal()=="23"));
}

#[test]
fn higher_order_recursive_fields_still_decline_delayed_evaluation() {
    let mut k = Kernel::new();
    k.inductive(
        "HigherTree",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![
            ("leaf".into(), vec![]),
            ("fork".into(), vec![pi(nat(), global("HigherTree"))]),
        ],
    )
    .unwrap();
    let source = term(Term::Induct {
        family: "HigherTree".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global("HigherTree"), nat()),
        branches: vec![
            lit(0),
            lam(
                pi(nat(), global("HigherTree")),
                lam(pi(nat(), nat()), lit(7)),
            ),
        ],
        subject: ctor(
            "HigherTree",
            "fork",
            vec![lam(nat(), ctor("HigherTree", "leaf", vec![]))],
        ),
    });
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(k.delayed_scalar(&source, 0).unwrap().is_none());
    k.delayed_active = true;
    assert!(k.convertible(&[], &source, &lit(7), 0).unwrap());
}

#[test]
fn neutral_prop_k_accepts_an_applied_opaque_proof_head() {
    let mut k = Kernel::new();
    declare_nullary_indexed_family(&mut k, "KIndex", 0);
    // The second argument is arbitrary; both result indices use the first.
    // This is a checked proof function, with no assumption about unequal fibres.
    k.opaque_definition(
        "sealed-proof-function",
        vec![],
        pi(nat(), pi(nat(), indexed_family("KIndex", var(1), var(1)))),
        lam(nat(), lam(nat(), indexed_witness("KIndex", var(1)))),
    )
    .unwrap();
    let source = nullary_induction(
        "KIndex",
        vec![lit(3)],
        vec![lit(3)],
        lam(nat(), lam(indexed_family("KIndex", lit(3), var(0)), nat())),
        lit(11),
        apps(global("sealed-proof-function"), &[lit(3), lit(7)]),
    );
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(
        matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, family }) if family == NAT && value.decimal() == "11")
    );
}

#[test]
fn equality_endpoints_do_not_collapse_unequal_opaque_applications() {
    let mut k = Kernel::new();
    k.opaque_definition(
        "sealed-data-function",
        vec![],
        pi(nat(), pi(nat(), nat())),
        lam(nat(), lam(nat(), lit(0))),
    )
    .unwrap();
    let left = apps(global("sealed-data-function"), &[lit(1), lit(2)]);
    let right = apps(global("sealed-data-function"), &[lit(1), lit(3)]);
    k.opaque_definition(
        "sealed-data-reflexivity",
        vec![],
        eq(left.clone(), left.clone()),
        term(Term::Refl(nat(), left.clone())),
    )
    .unwrap();
    let source = term(Term::EqElim {
        ty: nat(),
        left: left.clone(),
        right,
        motive: lam(nat(), lam(eq(left, var(0)), nat())),
        base: lit(12),
        proof: global("sealed-data-reflexivity"),
    });
    assert!(k.delayed_scalar(&source, 0).unwrap().is_none());
    assert!(k.check(&[], &source, &nat(), 0).is_err());
}

#[test]
fn a_stuck_proof_projection_reaches_the_outer_equality_rule() {
    let mut k = Kernel::new();
    let equality = eq(lit(4), lit(4));
    let proof = term(Term::Refl(nat(), lit(4)));
    k.inductive(
        "ProofRecord",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![equality.clone()])],
    )
    .unwrap();
    k.opaque_definition(
        "sealed-proof-record",
        vec![],
        global("ProofRecord"),
        ctor("ProofRecord", "pack", vec![proof.clone()]),
    )
    .unwrap();
    let sigma = term(Term::Sigma(nat(), equality));
    k.opaque_definition(
        "sealed-proof-pair",
        vec![],
        sigma.clone(),
        term(Term::Pair(sigma, lit(0), proof)),
    )
    .unwrap();
    for proof in [
        term(Term::Project {
            family: "ProofRecord".into(),
            index: 0,
            subject: global("sealed-proof-record"),
        }),
        term(Term::Second(global("sealed-proof-pair"))),
    ] {
        let source = term(Term::EqElim {
            ty: nat(),
            left: lit(4),
            right: lit(4),
            motive: lam(nat(), lam(eq(lit(4), var(0)), nat())),
            base: lit(13),
            proof,
        });
        k.check(&[], &source, &nat(), 0).unwrap();
        assert!(
            matches!(agrees(&mut k, &source).as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal()=="13")
        );
    }
}

#[test]
fn opacity_open_variables_and_unsupported_values_remain_neutral() {
    let mut k = Kernel::new();
    k.opaque_definition("sealed", vec![], pi(nat(), nat()), lam(nat(), lit(2)))
        .unwrap();
    let source = app(global("sealed"), lit(1));
    k.check(&[], &source, &nat(), 0).unwrap();
    assert!(agrees(&mut k, &source).is_none());
    assert!(k.delayed_scalar(&var(0), 0).unwrap().is_none());
    assert!(k.delayed_scalar(&lam(nat(), var(0)), 0).unwrap().is_none());
    assert!(k
        .delayed_scalar(&global("missing-delayed-global"), 0)
        .unwrap_err()
        .contains("unknown"));
    let bad_levels = term(Term::Global(NAT.into(), vec![Level::number(0).unwrap()]));
    assert!(k.delayed_scalar(&bad_levels, 0).is_err());
}

#[test]
fn operational_erasure_never_skips_definition_checking() {
    let mut k = Kernel::new();
    let malformed = apps(
        lam(
            nat(),
            lam(term(Term::Sort(Level::number(0).unwrap())), lit(0)),
        ),
        &[lit(1), lit(2)],
    );
    assert!(k.delayed_scalar(&malformed, 0).unwrap().is_some());
    assert!(k
        .definition("bad-delayed-erasure", vec![], nat(), malformed, false)
        .is_err());
    assert!(!k.contains("bad-delayed-erasure").unwrap());
}

#[test]
fn active_probe_depth_work_and_byte_limits_are_respected() {
    let mut k = Kernel::new();
    assert!(k
        .reduction_probe(0, |k| {
            let outer = k.reduction_probe_budget.unwrap();
            let result = k.delayed_scalar(&lit(1), 0)?;
            let restored = k.reduction_probe_budget.unwrap();
            assert_eq!(
                (outer.work, outer.bytes, outer.depth),
                (restored.work, restored.bytes, restored.depth)
            );
            Ok(result.is_some())
        })
        .unwrap()
        .unwrap());
    assert!(k
        .delayed_scalar(&lit(1), DEPTH + 1)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    k.work = k.budget.work();
    assert!(k
        .delayed_scalar(&lit(1), 0)
        .unwrap_err()
        .contains("work units"));
    k.reset_budget();
    let expensive = fold(lit(65_536));
    k.check(&[], &expensive, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.delayed_scalar(&expensive, 0).unwrap().is_none());
    assert!(k.work > 0 && k.work <= 65_537);
    assert!(k.transformed_bytes > 0 && k.transformed_bytes <= 8 * 1024 * 1024);
    assert!(k.reduction_probe_budget.is_none());
    assert!(!k.delayed_active);
    // The VM's larger allowance must never extend any enclosing cap. Exercise
    // work, allocation and depth refusals independently, preserving all caps.
    for parent in [
        ReductionProbeBudget {
            work: 24,
            bytes: 8 * 1024 * 1024,
            depth: 48,
        },
        ReductionProbeBudget {
            work: 65_537,
            bytes: 64,
            depth: 48,
        },
        ReductionProbeBudget {
            work: 65_537,
            bytes: 8 * 1024 * 1024,
            depth: 0,
        },
    ] {
        k.reset_budget();
        k.reduction_probe_budget = Some(parent);
        let result = k.delayed_scalar(&expensive, 0);
        let restored = k.reduction_probe_budget.unwrap();
        assert_eq!(
            (restored.work, restored.bytes, restored.depth),
            (parent.work, parent.bytes, parent.depth)
        );
        assert!(result.unwrap().is_none());
        assert!(k.work <= parent.work && k.transformed_bytes <= parent.bytes);
        assert!(!k.delayed_active);
        k.reduction_probe_budget = None;
    }
    k.reset_budget();
    k.transformed_bytes = k.budget.phase_bytes() + 1;
    assert!(k
        .delayed_scalar(&lit(1), 0)
        .unwrap_err()
        .contains("allocation limit"));
}

#[path = "delayed_wrapper_tests.rs"]
mod wrappers;
