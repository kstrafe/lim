//! Focused regressions for retained head reductions in `natural_head`.
use super::*;

fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn nat() -> T {
    global("#pt-nat")
}
fn lam(domain: T, body: T) -> T {
    term(Term::Lam(domain, body))
}
fn sort(level: u32) -> T {
    term(Term::Sort(Level::number(level).unwrap()))
}

fn var(index: usize) -> T {
    term(Term::Var(index))
}

fn pi(domain: T, range: T) -> T {
    term(Term::Pi(domain, range))
}

fn app(function: T, argument: T) -> T {
    term(Term::App(function, argument))
}

fn project(family: &str, index: usize, subject: T) -> T {
    term(Term::Project {
        family: family.into(),
        index,
        subject,
    })
}

#[test]
fn stuck_application_retains_beta_reduced_open_function() {
    let mut k = Kernel::new();
    let function_ty = pi(nat(), nat());
    let ctx = vec![function_ty.clone(), nat()];
    // (fun f => f) f x has type Nat in this open context.
    let source = app(app(lam(function_ty, var(0)), var(1)), var(0));
    k.check(&ctx, &source, &nat(), 0).unwrap();

    let head = k.natural_head(&source, 0).unwrap();
    let expected = app(var(1), var(0));
    k.check(&ctx, &head, &nat(), 0).unwrap();
    assert!(k.same_syntax(&head, &expected).unwrap());
}

#[test]
fn stuck_project_retains_reduced_open_record_reference() {
    let mut k = Kernel::new();
    k.inductive(
        "HeadTestRecord",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![nat()])],
    )
    .unwrap();
    let record_ty = global("HeadTestRecord");
    let ctx = vec![record_ty.clone()];
    // The alias beta reduces to the local record variable, which remains stuck.
    let source = project("HeadTestRecord", 0, app(lam(record_ty, var(0)), var(0)));
    k.check(&ctx, &source, &nat(), 0).unwrap();

    let head = k.natural_head(&source, 0).unwrap();
    k.check(&ctx, &head, &nat(), 0).unwrap();
    assert!(k
        .same_syntax(&head, &project("HeadTestRecord", 0, var(0)))
        .unwrap());
}

#[test]
fn stuck_first_and_second_retain_reduced_open_sigma_reference() {
    let mut k = Kernel::new();
    let sigma = term(Term::Sigma(nat(), nat()));
    let ctx = vec![sigma.clone()];
    let alias = app(lam(sigma, var(0)), var(0));
    let first = term(Term::First(alias.clone()));
    let second = term(Term::Second(alias));
    k.check(&ctx, &first, &nat(), 0).unwrap();
    k.check(&ctx, &second, &nat(), 0).unwrap();

    let reduced_first = k.natural_head(&first, 0).unwrap();
    let reduced_second = k.natural_head(&second, 0).unwrap();
    k.check(&ctx, &reduced_first, &nat(), 0).unwrap();
    k.check(&ctx, &reduced_second, &nat(), 0).unwrap();
    assert!(k
        .same_syntax(&reduced_first, &term(Term::First(var(0))))
        .unwrap());
    assert!(k
        .same_syntax(&reduced_second, &term(Term::Second(var(0))))
        .unwrap());
}

#[test]
fn retained_head_reduction_keeps_opacity_and_source_validation() {
    let mut k = Kernel::new();
    let function_ty = pi(nat(), nat());
    let body = lam(nat(), var(0));
    k.opaque_definition("head_test_opaque", vec![], function_ty, body)
        .unwrap();
    let opaque = global("head_test_opaque");
    let reduced = k.natural_head(&opaque, 0).unwrap();
    assert!(Arc::ptr_eq(&opaque, &reduced));

    // This application is ill typed (its argument is a type, not a Nat).
    let invalid = app(lam(nat(), var(0)), sort(0));
    assert!(k.check(&[], &invalid, &nat(), 0).is_err());
}

#[test]
fn repeated_exposure_of_retained_application_is_pointer_stable() {
    let mut k = Kernel::new();
    let function_ty = pi(nat(), nat());
    let ctx = vec![function_ty.clone(), nat()];
    let source = app(app(lam(function_ty, var(0)), var(1)), var(0));
    k.check(&ctx, &source, &nat(), 0).unwrap();
    let first = k.natural_head(&source, 0).unwrap();
    let bytes_after_first = k.transformed_bytes;
    let second = k.natural_head(&first, 0).unwrap();
    assert!(Arc::ptr_eq(&first, &second));
    assert_eq!(k.transformed_bytes, bytes_after_first);
}

#[test]
fn natural_head_propagates_work_depth_and_transformation_byte_limits() {
    let function_ty = pi(nat(), nat());
    let source = app(app(lam(function_ty.clone(), var(0)), var(1)), var(0));
    let ctx = vec![function_ty, nat()];

    let mut work_limited = Kernel::new();
    work_limited.check(&ctx, &source, &nat(), 0).unwrap();
    work_limited.work = WORK;
    assert!(work_limited
        .natural_head(&source, 0)
        .unwrap_err()
        .contains("work units"));

    let mut depth_limited = Kernel::new();
    depth_limited.check(&ctx, &source, &nat(), 0).unwrap();
    assert!(depth_limited
        .natural_head(&source, DEPTH + 1)
        .unwrap_err()
        .contains("recursion depth"));

    let mut byte_limited = Kernel::new();
    byte_limited.check(&ctx, &source, &nat(), 0).unwrap();
    byte_limited.transformed_bytes = byte_limited.budget.phase_bytes();
    assert!(byte_limited
        .natural_head(&source, 0)
        .unwrap_err()
        .contains("allocation limit"));
}
