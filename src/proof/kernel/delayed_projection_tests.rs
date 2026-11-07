//! Closed scalar projections use the existing closure evaluator, not unfolding copies.
use super::*;

const NAT: &str = "#pt-nat";
fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn var(index: usize) -> T {
    term(Term::Var(index))
}
fn lam(domain: T, body: T) -> T {
    term(Term::Lam(domain, body))
}
fn lit(value: usize) -> T {
    term(Term::NatLiteral {
        family: NAT.into(),
        value: Natural::parse(&value.to_string()).unwrap(),
    })
}
fn ctor(family: &str, fields: Vec<T>) -> T {
    term(Term::Ctor {
        family: family.into(),
        levels: vec![],
        parameters: vec![],
        constructor: "pack".into(),
        fields,
    })
}
fn project(family: &str, index: usize, subject: T) -> T {
    term(Term::Project {
        family: family.into(),
        index,
        subject,
    })
}
fn folded_record(k: &mut Kernel, size: usize) -> T {
    const RECORD: &str = "ProjectionFoldRecord";
    k.inductive(
        RECORD,
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![global(NAT), global(NAT)])],
    )
    .unwrap();
    let first = project(RECORD, 0, var(0));
    let second = project(RECORD, 1, var(0));
    let next = term(Term::Ctor {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        constructor: "succ".into(),
        fields: vec![first],
    });
    let fold = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global(NAT), global(RECORD)),
        branches: vec![
            ctor(RECORD, vec![lit(0), lit(17)]),
            lam(
                global(NAT),
                lam(global(RECORD), ctor(RECORD, vec![next, second])),
            ),
        ],
        subject: lit(size),
    });
    project(RECORD, 0, fold)
}

#[test]
fn a_projected_record_fold_reduces_without_recursive_substitution_depth() {
    let mut k = Kernel::new();
    let source = folded_record(&mut k, 32);
    k.check(&[], &source, &global(NAT), 0).unwrap();
    k.reset_budget();
    let reduced = k
        .delayed_record_projection(&source, 0)
        .unwrap()
        .expect("computed natural field");
    assert!(matches!(reduced.as_ref(), Term::NatLiteral { value, .. } if value.decimal() == "32"));
    k.reset_budget();
    k.check(
        &[],
        &term(Term::Refl(global(NAT), lit(32))),
        &term(Term::Eq(global(NAT), source.clone(), lit(32))),
        0,
    )
    .unwrap();
    k.reset_budget();
    assert!(!k.convertible(&[], &source, &lit(31), 0).unwrap());
}

#[test]
fn a_small_record_fold_agrees_with_ordinary_reduction() {
    let mut k = Kernel::new();
    let source = folded_record(&mut k, 2);
    let delayed = k.delayed_record_projection(&source, 0).unwrap().unwrap();
    k.reset_budget();
    k.delayed_active = true;
    let ordinary = k.whnf(&[], &source, 0).unwrap();
    k.delayed_active = false;
    assert!(k.convertible(&[], &delayed, &ordinary, 0).unwrap());
}

#[test]
fn a_nested_record_projection_preserves_its_captured_payload() {
    let mut k = Kernel::new();
    for (name, fields) in [
        ("NestedScalar", vec![global(NAT), global(NAT)]),
        ("NestedOwner", vec![global("NestedScalar"), global(NAT)]),
    ] {
        k.inductive(
            name,
            vec![],
            vec![],
            Level::number(1).unwrap(),
            vec![("pack".into(), fields)],
        )
        .unwrap();
    }
    let payload = ctor("NestedScalar", vec![lit(17), var(0)]);
    let owner = ctor("NestedOwner", vec![payload, lit(4)]);
    let computed = term(Term::App(lam(global(NAT), owner), lit(9)));
    let source = project("NestedScalar", 1, project("NestedOwner", 0, computed));
    k.check(&[], &source, &global(NAT), 0).unwrap();
    k.reset_budget();
    let delayed = k
        .delayed_record_projection(&source, 0)
        .unwrap()
        .expect("nested scalar observation");
    assert!(matches!(delayed.as_ref(), Term::NatLiteral { value, .. } if value.decimal()=="9"));
    k.reset_budget();
    k.delayed_active = true;
    let ordinary = k.whnf(&[], &source, 0).unwrap();
    k.delayed_active = false;
    assert!(k.convertible(&[], &delayed, &ordinary, 0).unwrap());
    assert!(!k.convertible(&[], &source, &lit(17), 0).unwrap());
}

#[test]
fn projection_attempts_are_bounded_and_reset_without_consuming_wrapper_attempts() {
    let mut k = Kernel::new();
    let source = folded_record(&mut k, 2);
    k.reset_budget();
    for _ in 0..4 {
        assert!(k.delayed_record_projection(&source, 0).unwrap().is_some());
    }
    assert!(k.delayed_record_projection(&source, 0).unwrap().is_none());
    assert_eq!(k.delayed_wrapper_attempts, 0);
    k.reset_budget();
    assert!(k.delayed_record_projection(&source, 0).unwrap().is_some());
}

#[test]
fn polymorphic_record_fields_decline_without_an_implicit_universe_instantiation() {
    let mut k = Kernel::new();
    k.inductive(
        "ProjectionPolymorphic",
        vec!["u".into()],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![global(NAT)])],
    )
    .unwrap();
    let record_ty = term(Term::Global(
        "ProjectionPolymorphic".into(),
        vec![Level::number(0).unwrap()],
    ));
    let packed = term(Term::Ctor {
        family: "ProjectionPolymorphic".into(),
        levels: vec![Level::number(0).unwrap()],
        parameters: vec![],
        constructor: "pack".into(),
        fields: vec![lit(7)],
    });
    let source = project(
        "ProjectionPolymorphic",
        0,
        term(Term::App(lam(record_ty, var(0)), packed)),
    );
    assert!(k.delayed_record_projection(&source, 0).unwrap().is_none());
    k.check(&[], &source, &global(NAT), 0).unwrap();
    assert!(k.convertible(&[], &source, &lit(7), 0).unwrap());
}
