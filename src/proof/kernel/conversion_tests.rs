//! Focused regressions for conversion before transparent unfolding.
use super::*;

fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn nat() -> T {
    global("#pt-nat")
}
fn var(index: usize) -> T {
    term(Term::Var(index))
}
fn app(function: T, argument: T) -> T {
    term(Term::App(function, argument))
}
fn lam(domain: T, body: T) -> T {
    term(Term::Lam(domain, body))
}
fn pi(domain: T, range: T) -> T {
    term(Term::Pi(domain, range))
}
fn zero() -> T {
    term(Term::Ctor {
        family: "#pt-nat".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "zero".into(),
        fields: vec![],
    })
}
fn succ(value: T) -> T {
    term(Term::Ctor {
        family: "#pt-nat".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "succ".into(),
        fields: vec![value],
    })
}

#[test]
fn opaque_and_local_heads_compare_arguments_by_conversion() {
    let mut k = Kernel::new();
    let function_type = pi(nat(), nat());
    k.opaque_definition("opaque", vec![], function_type.clone(), lam(nat(), var(0)))
        .unwrap();
    let opaque = global("opaque");
    let left = app(opaque.clone(), app(lam(nat(), var(0)), zero()));
    let right = app(opaque, zero());
    assert!(k.convertible(&[], &left, &right, 0).unwrap());

    let local = app(var(0), app(lam(nat(), var(0)), zero()));
    let local_other = app(var(0), zero());
    assert!(k
        .convertible(&[function_type], &local, &local_other, 0)
        .unwrap());
}

#[test]
fn unequal_opaque_arguments_reject_but_transparent_constant_falls_back() {
    let mut k = Kernel::new();
    let function_type = pi(nat(), nat());
    k.opaque_definition("opaque", vec![], function_type.clone(), lam(nat(), var(0)))
        .unwrap();
    assert!(!k
        .convertible(
            &[],
            &app(global("opaque"), zero()),
            &app(global("opaque"), succ(zero())),
            0
        )
        .unwrap());

    k.definition("constant", vec![], function_type, lam(nat(), zero()), false)
        .unwrap();
    assert!(k
        .convertible(
            &[],
            &app(global("constant"), zero()),
            &app(global("constant"), succ(zero())),
            0
        )
        .unwrap());
}

#[test]
fn beta_iota_and_zeta_keep_a_transparent_head_neutral_when_delta_is_disabled() {
    let mut k = Kernel::new();
    let worker_ty = pi(nat(), nat());
    k.definition("worker", vec![], worker_ty, lam(nat(), var(0)), false)
        .unwrap();
    let worker = global("worker");
    let beta = app(lam(nat(), app(worker.clone(), var(0))), zero());
    let direct = app(worker.clone(), zero());
    assert!(k.convertible(&[], &beta, &direct, 0).unwrap());
    let whnf = k.whnf_delta(&[], &beta, false, 0).unwrap();
    let (head, _) = k.application_spine(&whnf, 0).unwrap();
    assert!(matches!(head.as_ref(), Term::Global(name, _) if name == "worker"));
    assert!(k.infer(&[], &direct, 0).is_ok());

    let nat_type = nat();
    let zeta = term(Term::Let(
        nat_type.clone(),
        zero(),
        app(worker.clone(), var(0)),
    ));
    assert!(k.convertible(&[], &zeta, &direct, 0).unwrap());
    let iota = term(Term::Induct {
        family: "#pt-nat".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat_type.clone(), nat_type.clone()),
        branches: vec![
            app(worker.clone(), zero()),
            lam(nat_type.clone(), lam(nat_type, app(worker.clone(), var(0)))),
        ],
        subject: zero(),
    });
    assert!(k.convertible(&[], &iota, &direct, 0).unwrap());
}

#[test]
fn source_annotation_and_unused_let_corruption_is_rejected_before_reduction() {
    let mut k = Kernel::new();
    let erased_bad_annotation = term(Term::Let(global("#pt-false"), zero(), zero()));
    assert!(k
        .definition(
            "bad_annotation",
            vec![],
            nat(),
            erased_bad_annotation,
            false
        )
        .is_err());
    assert!(!k.contains("bad_annotation"));

    let bad_unused_value = term(Term::Let(nat(), global("#pt-false"), zero()));
    assert!(k
        .definition("bad_unused_value", vec![], nat(), bad_unused_value, false)
        .is_err());
    assert!(!k.contains("bad_unused_value"));
}

#[test]
fn conversion_keeps_nominal_globals_distinct() {
    let mut k = Kernel::new();
    // Each declaration is independently checked; their names remain nominal.
    k.opaque_definition("A", vec![], nat(), zero()).unwrap();
    k.opaque_definition("B", vec![], nat(), zero()).unwrap();
    assert!(!k.convertible(&[], &global("A"), &global("B"), 0).unwrap());
}

fn wrappers(k: &mut Kernel) -> (T, T) {
    k.definition(
        "worker",
        vec![],
        pi(nat(), nat()),
        lam(nat(), var(0)),
        false,
    )
    .unwrap();
    let mut previous = global("worker");
    for name in ["wrapper0", "wrapper1", "wrapper2"] {
        k.definition(name, vec![], pi(nat(), nat()), previous, false)
            .unwrap();
        previous = global(name);
    }
    (app(global("worker"), zero()), app(previous, zero()))
}

#[test]
fn a_delta_chain_exposes_the_common_call_without_unfolding_the_worker() {
    let mut k = Kernel::new();
    let (direct, wrapped) = wrappers(&mut k);
    k.reset_budget();
    assert!(k.conversion_congruence(&[], &direct, &wrapped, 0).unwrap());
    assert!(k.reduction_probe_budget.is_none());
    let different_local = [pi(nat(), nat()), pi(nat(), nat())];
    assert!(!k
        .convertible(
            &different_local,
            &app(var(0), zero()),
            &app(var(1), zero()),
            0
        )
        .unwrap());
}

#[test]
fn conversion_candidates_restore_nested_limits_and_propagate_real_failures() {
    let mut k = Kernel::new();
    let (direct, wrapped) = wrappers(&mut k);
    k.reset_budget();
    let enclosing = ReductionProbeBudget {
        work: 24,
        bytes: 4096,
        depth: 24,
    };
    k.reduction_probe_budget = Some(enclosing);
    let result = k
        .reduction_probe(0, |k| k.conversion_congruence(&[], &direct, &wrapped, 1))
        .unwrap();
    assert_ne!(result, Some(true));
    assert!(k.work <= enclosing.work && k.transformed_bytes <= enclosing.bytes);
    let restored = k.reduction_probe_budget.unwrap();
    assert_eq!(
        (restored.work, restored.bytes, restored.depth),
        (enclosing.work, enclosing.bytes, enclosing.depth)
    );
    k.reduction_probe_budget = None;
    k.reset_budget();
    k.work = WORK;
    assert!(k
        .conversion_congruence(&[], &direct, &wrapped, 0)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    assert!(k
        .conversion_congruence(&[], &direct, &wrapped, DEPTH + 1)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    let unknown = app(global("unknown"), zero());
    assert!(k
        .conversion_congruence(&[], &direct, &unknown, 0)
        .unwrap_err()
        .contains("unknown"));
    assert!(k.reduction_probe_budget.is_none());
}

#[test]
fn source_inference_rejects_bad_universe_arguments_before_any_congruence() {
    let mut k = Kernel::new();
    k.definition(
        "worker",
        vec![],
        pi(nat(), nat()),
        lam(nat(), var(0)),
        false,
    )
    .unwrap();
    let bad = term(Term::Global(
        "worker".into(),
        vec![Level::number(0).unwrap()],
    ));
    let body = app(bad, zero());
    let why = k
        .definition("bad_universe", vec![], nat(), body, false)
        .unwrap_err();
    assert!(why.contains("universe"), "{why}");
    assert!(!k.contains("bad_universe"));
}

#[test]
fn longer_delta_chains_keep_the_original_converter_as_fallback() {
    let mut k = Kernel::new();
    let (direct, mut wrapped) = wrappers(&mut k);
    let Term::App(head, _) = wrapped.as_ref() else {
        unreachable!()
    };
    let mut previous = head.clone();
    for i in 0..10 {
        let name = format!("long-wrapper-{i}");
        k.definition(&name, vec![], pi(nat(), nat()), previous, false)
            .unwrap();
        previous = global(&name);
    }
    wrapped = app(previous, zero());
    k.reset_budget();
    assert!(!k.conversion_congruence(&[], &direct, &wrapped, 0).unwrap());
    assert!(k.convertible(&[], &direct, &wrapped, 0).unwrap());
}

#[test]
fn common_dependent_heads_preserve_proof_irrelevance_in_the_real_scope() {
    let mut k = Kernel::new();
    let proposition = term(Term::Sort(Level::number(0).unwrap()));
    let identity_type = pi(proposition.clone(), pi(var(0), var(1)));
    k.opaque_definition(
        "proof_identity",
        vec![],
        identity_type,
        lam(proposition.clone(), lam(var(0), var(0))),
    )
    .unwrap();
    // P : Prop, p : P, q : P. All variable indices retain their real binder.
    let ctx = [proposition, var(0), var(1)];
    let head = app(global("proof_identity"), var(2));
    let left = app(head.clone(), var(1));
    let right = app(head, var(0));
    k.infer(&ctx, &left, 0).unwrap();
    k.infer(&ctx, &right, 0).unwrap();
    assert!(k.conversion_congruence(&ctx, &left, &right, 0).unwrap());
}
