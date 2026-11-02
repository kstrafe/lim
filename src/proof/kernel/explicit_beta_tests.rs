//! Lazy batching preserves typing, capture and named reduction boundaries.
use super::*;

fn var(i: usize) -> T {
    term(Term::Var(i))
}
fn global(s: &str) -> T {
    term(Term::Global(s.into(), vec![]))
}
fn nat() -> T {
    global("#pt-nat")
}
fn number(n: usize) -> T {
    term(Term::NatLiteral {
        family: "#pt-nat".into(),
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
fn worker(k: &mut Kernel) {
    k.definition(
        "worker",
        vec![],
        pi(nat(), nat()),
        lam(nat(), var(0)),
        false,
    )
    .unwrap();
}

#[test]
fn lazy_batch_leaves_a_transparent_worker_neutral() {
    let mut k = Kernel::new();
    worker(&mut k);
    let expected = app(global("worker"), number(7));
    let source = apps(
        lam(nat(), lam(nat(), app(global("worker"), var(0)))),
        &[number(2), number(7)],
    );
    k.check(&[], &source, &nat(), 0).unwrap();
    let reduced = k.whnf_delta(&[], &source, false, 0).unwrap();
    assert!(k.same_syntax(&reduced, &expected).unwrap());
    let still_neutral = k.whnf_delta(&[], &reduced, false, 0).unwrap();
    assert!(k.same_syntax(&still_neutral, &expected).unwrap());
    let unfolded = k.whnf(&[], &reduced, 0).unwrap();
    assert!(k.same_syntax(&unfolded, &number(7)).unwrap());
}

#[test]
fn captured_value_and_dependent_domains_retain_their_outer_scope() {
    let mut k = Kernel::new();
    // Context: A : Type, a : A. Substitute A and a into two binders,
    // leaving a lambda whose domain is A and whose result captures a.
    let universe = term(Term::Sort(Level::number(1).unwrap()));
    let context = [universe.clone(), var(0)];
    let source = apps(
        lam(universe, lam(var(0), lam(var(1), var(3)))),
        &[var(1), var(0)],
    );
    let expected = lam(var(1), var(1));
    let ty = pi(var(1), var(2));
    k.check(&context, &source, &ty, 0).unwrap();
    let reduced = k.explicit_beta_spine(&source, 0).unwrap().unwrap();
    k.check(&context, &reduced, &ty, 0).unwrap();
    assert!(k.same_syntax(&reduced, &expected).unwrap());
    assert!(!k.same_syntax(&reduced, &lam(var(1), var(0))).unwrap());
}

#[test]
fn partial_and_overapplication_preserve_lambda_and_neutral_spines() {
    let mut k = Kernel::new();
    worker(&mut k);
    let partial = apps(
        lam(nat(), lam(nat(), lam(nat(), var(2)))),
        &[number(1), number(2)],
    );
    k.check(&[], &partial, &pi(nat(), nat()), 0).unwrap();
    let reduced = k.explicit_beta_spine(&partial, 0).unwrap().unwrap();
    assert!(k.same_syntax(&reduced, &lam(nat(), number(1))).unwrap());
    let head = lam(nat(), lam(nat(), global("worker")));
    let over = apps(head, &[number(2), number(3), number(7)]);
    k.check(&[], &over, &nat(), 0).unwrap();
    let reduced = k.explicit_beta_spine(&over, 0).unwrap().unwrap();
    assert!(k
        .same_syntax(&reduced, &app(global("worker"), number(7)))
        .unwrap());
}

#[test]
fn global_heads_stay_neutral_and_bad_erased_sources_still_fail() {
    let mut k = Kernel::new();
    let ty = pi(nat(), pi(nat(), nat()));
    let body = lam(nat(), lam(nat(), var(1)));
    k.definition("visible", vec![], ty.clone(), body.clone(), false)
        .unwrap();
    k.opaque_definition("sealed", vec![], ty, body).unwrap();
    for name in ["visible", "sealed"] {
        let call = apps(global(name), &[number(1), number(2)]);
        k.check(&[], &call, &nat(), 0).unwrap();
        assert!(k.explicit_beta_spine(&call, 0).unwrap().is_none());
        let neutral = k.whnf_delta(&[], &call, false, 0).unwrap();
        assert!(k.same_syntax(&neutral, &call).unwrap());
    }
    let malformed = apps(
        term(Term::Global(
            "visible".into(),
            vec![Level::number(0).unwrap()],
        )),
        &[number(1), number(2)],
    );
    let error = k
        .definition("bad-levels", vec![], nat(), malformed, false)
        .unwrap_err();
    assert!(error.contains("universe"), "{error}");
    assert!(!k.contains("bad-levels"));
    let source = apps(
        lam(
            nat(),
            lam(term(Term::Sort(Level::number(0).unwrap())), number(0)),
        ),
        &[number(0), number(0)],
    );
    let error = k
        .definition("bad-erased", vec![], nat(), source, false)
        .unwrap_err();
    assert!(error.contains("type mismatch"), "{error}");
    assert!(!k.contains("bad-erased"));
}

#[test]
fn explicit_spine_respects_depth_and_allocation_limits() {
    let mut k = Kernel::new();
    let value = apps(lam(nat(), lam(nat(), var(1))), &[number(0), number(1)]);
    assert!(k
        .explicit_beta_spine(&value, DEPTH)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    k.transformed_bytes = 64 * 1024 * 1024 - 511;
    assert!(k
        .explicit_beta_spine(&value, 0)
        .unwrap_err()
        .contains("allocation limit"));
}
