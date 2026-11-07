//! Scalar conversion regressions for generic checked function applications.
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
fn checked_noninjective_nat_function_accepts_distinct_inputs() {
    let mut k = Kernel::new();
    k.definition(
        "scalar_constant",
        vec![],
        pi(nat(), nat()),
        lam(nat(), zero()),
        false,
    )
    .unwrap();
    let function = global("scalar_constant");
    assert!(k
        .convertible(
            &[],
            &app(function.clone(), zero()),
            &app(function, succ(zero())),
            0,
        )
        .unwrap());
}

#[test]
fn constructor_proof_fields_remain_irrelevant() {
    let mut k = Kernel::new();
    let proposition = term(Term::Sort(Level::number(0).unwrap()));
    k.inductive(
        "ScalarProofBox",
        vec![],
        vec![proposition.clone()],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![var(0)])],
    )
    .unwrap();
    // P : Prop, p : P, q : P. Both constructor applications have type Box P.
    let ctx = [proposition, var(0), var(1)];
    let boxed_type = app(global("ScalarProofBox"), var(2));
    let boxed = |proof| {
        term(Term::Ctor {
            family: "ScalarProofBox".into(),
            levels: vec![],
            parameters: vec![var(2)],
            constructor: "pack".into(),
            fields: vec![proof],
        })
    };
    k.check(&ctx, &boxed(var(1)), &boxed_type, 0).unwrap();
    k.check(&ctx, &boxed(var(0)), &boxed_type, 0).unwrap();
    assert!(k
        .convertible(&ctx, &boxed(var(1)), &boxed(var(0)), 0)
        .unwrap());
}

#[test]
fn opaque_functions_with_equal_bodies_stay_distinct() {
    let mut k = Kernel::new();
    let function_type = pi(nat(), nat());
    let body = lam(nat(), zero());
    k.opaque_definition(
        "scalar_opaque_a",
        vec![],
        function_type.clone(),
        body.clone(),
    )
    .unwrap();
    k.opaque_definition("scalar_opaque_b", vec![], function_type, body)
        .unwrap();
    assert!(!k
        .convertible(
            &[],
            &app(global("scalar_opaque_a"), zero()),
            &app(global("scalar_opaque_b"), zero()),
            0,
        )
        .unwrap());
}

#[test]
fn dependent_binder_reduction_does_not_capture_the_wrong_variable() {
    let mut k = Kernel::new();
    k.opaque_definition(
        "scalar_neutral",
        vec![],
        pi(nat(), nat()),
        lam(nat(), zero()),
    )
    .unwrap();
    let ctx = [nat()];
    let direct = app(global("scalar_neutral"), var(0));
    let wrong_capture = app(lam(nat(), app(global("scalar_neutral"), var(0))), zero());
    k.check(&ctx, &direct, &nat(), 0).unwrap();
    k.check(&ctx, &wrong_capture, &nat(), 0).unwrap();
    assert!(!k.convertible(&ctx, &direct, &wrong_capture, 0).unwrap());
}

#[test]
fn canonical_record_mismatch_respects_prop_universe_specialization() {
    let mut k = Kernel::new();
    k.inductive(
        "ScalarUniverseRecord",
        vec!["u".into()],
        vec![],
        Level::variable("u".into()),
        vec![("pack".into(), vec![nat()])],
    )
    .unwrap();
    for (universe, expected) in [(0, true), (1, false)] {
        let value = |n| {
            term(Term::Ctor {
                family: "ScalarUniverseRecord".into(),
                levels: vec![Level::number(universe).unwrap()],
                parameters: vec![],
                constructor: "pack".into(),
                fields: vec![n],
            })
        };
        let ty = term(Term::Global(
            "ScalarUniverseRecord".into(),
            vec![Level::number(universe).unwrap()],
        ));
        let (left, right) = (value(zero()), value(succ(zero())));
        k.check(&[], &left, &ty, 0).unwrap();
        k.check(&[], &right, &ty, 0).unwrap();
        assert_eq!(k.convertible(&[], &left, &right, 0).unwrap(), expected);
    }
}

#[test]
fn a_mismatching_data_field_does_not_erase_ill_typed_sibling_source() {
    let mut k = Kernel::new();
    let proposition = term(Term::Eq(nat(), zero(), zero()));
    k.inductive(
        "ScalarCheckedFields",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![nat(), proposition])],
    )
    .unwrap();
    let source = term(Term::Ctor {
        family: "ScalarCheckedFields".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "pack".into(),
        fields: vec![succ(zero()), global("undeclared-proof")],
    });
    let failure = k
        .check(&[], &source, &global("ScalarCheckedFields"), 0)
        .unwrap_err();
    assert!(
        failure.contains("unknown") || failure.contains("undeclared"),
        "{failure}"
    );
}

#[test]
fn a_constant_record_function_keeps_ordinary_reduction_after_argument_mismatch() {
    let mut k = Kernel::new();
    k.inductive(
        "ScalarConstantRecord",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![nat()])],
    )
    .unwrap();
    let record = term(Term::Ctor {
        family: "ScalarConstantRecord".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "pack".into(),
        fields: vec![zero()],
    });
    k.definition(
        "scalar-record-constant",
        vec![],
        pi(nat(), global("ScalarConstantRecord")),
        lam(nat(), record),
        false,
    )
    .unwrap();
    assert!(k
        .convertible(
            &[],
            &app(global("scalar-record-constant"), zero()),
            &app(global("scalar-record-constant"), succ(zero())),
            0
        )
        .unwrap());
}
