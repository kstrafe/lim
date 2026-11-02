use super::*;

fn var(index: usize) -> T {
    term(Term::Var(index))
}

fn nat() -> T {
    term(Term::Global("#pt-nat".into(), vec![]))
}

fn number(value: usize) -> T {
    term(Term::NatLiteral {
        family: "#pt-nat".into(),
        value: Natural::parse(&value.to_string()).unwrap(),
    })
}

fn lam(annotation: T, body: T) -> T {
    term(Term::Lam(annotation, body))
}

fn app(function: T, argument: T) -> T {
    term(Term::App(function, argument))
}

#[test]
fn zero_shift_shares_root_and_only_charges_one_work_unit() {
    let mut kernel = Kernel::new();
    let payload = (0..64).fold(var(0), |body, _| lam(nat(), body));
    let before = kernel.transformation_bytes();
    let work = kernel.work;
    let result = kernel.shift(&payload, 0, 0, 7).unwrap();
    assert!(Arc::ptr_eq(&payload, &result));
    assert_eq!(kernel.transformation_bytes(), before);
    assert_eq!(kernel.work, work + 1);

    kernel.reset_budget();
    let result = kernel.beta_shift_argument(&payload, 0, 9).unwrap();
    assert!(Arc::ptr_eq(&payload, &result.0));
    assert!(
        !result.1,
        "identity does not establish that a compound argument is closed"
    );
    assert_eq!(kernel.transformation_bytes(), 0);
    assert_eq!(kernel.work, 1);
}

#[test]
fn compound_zero_shift_does_not_hide_free_variables_between_binders() {
    let mut kernel = Kernel::new();
    let argument = app(var(0), nat());
    let body = app(var(0), lam(nat(), var(1)));
    let result = kernel
        .instantiate_many(&body, &[argument.clone()], 0, 1)
        .unwrap();
    let expected = app(argument, lam(nat(), app(var(1), nat())));
    assert!(kernel.same_syntax(&result, &expected).unwrap());
}

#[test]
fn closed_shift_leaves_are_recognized_as_invariant() {
    let mut kernel = Kernel::new();
    let values = [
        term(Term::Sort(Level::number(1).unwrap())),
        term(Term::Global(
            "poly".into(),
            vec![Level::variable("u".into())],
        )),
        number(123),
    ];
    for value in values {
        let (shifted, invariant) = kernel.beta_shift_argument(&value, 0, 0).unwrap();
        assert!(invariant);
        assert!(Arc::ptr_eq(&value, &shifted));
        kernel.reset_budget();
    }
}

#[test]
fn nonzero_shift_visits_annotations_and_respects_binder_scope() {
    let mut kernel = Kernel::new();
    let syntax = lam(var(0), app(var(0), var(2)));
    let shifted = kernel.shift(&syntax, 3, 0, 0).unwrap();
    let expected = lam(var(3), app(var(0), var(5)));
    assert!(kernel.same_syntax(&shifted, &expected).unwrap());

    kernel.reset_budget();
    let (shifted, invariant) = kernel.beta_shift_argument(&syntax, 3, 0).unwrap();
    assert!(!invariant);
    assert!(kernel.same_syntax(&shifted, &expected).unwrap());
}

#[test]
fn identity_shift_keeps_depth_and_nonzero_shift_keeps_overflow_checks() {
    let mut kernel = Kernel::new();
    assert!(kernel
        .shift(&var(0), 0, 0, DEPTH + 1)
        .unwrap_err()
        .contains("resource limit"));
    kernel.reset_budget();
    assert!(kernel
        .beta_shift_argument(&var(usize::MAX), 1, 0)
        .unwrap_err()
        .contains("variable index overflow"));
    kernel.reset_budget();
    assert!(kernel
        .beta_shift_argument(&lam(nat(), var(0)), 1, DEPTH)
        .unwrap_err()
        .contains("resource limit"));
}

#[test]
fn identity_reuse_does_not_bypass_declaration_scope_or_type_checks() {
    let mut kernel = Kernel::new();
    let bad_global = term(Term::Global("missing-symbol".into(), vec![]));
    let error = kernel
        .definition("bad-global", vec![], nat(), bad_global, false)
        .unwrap_err();
    assert!(
        error.contains("unknown") || error.contains("declaration"),
        "{error}"
    );
    assert!(!kernel.contains("bad-global"));

    let error = kernel
        .definition("bad-variable", vec![], nat(), var(0), false)
        .unwrap_err();
    assert!(error.contains("unbound"), "{error}");
    assert!(!kernel.contains("bad-variable"));

    let bad_let = term(Term::Let(
        nat(),
        term(Term::Sort(Level::number(0).unwrap())),
        number(0),
    ));
    let error = kernel
        .definition("bad-discarded-let", vec![], nat(), bad_let, false)
        .unwrap_err();
    assert!(!error.contains("resource limit"), "{error}");
    assert!(!kernel.contains("bad-discarded-let"));
}
