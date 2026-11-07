//! Mixed substitutions must keep callee and caller universes separate.
use super::*;

fn sort(level: Level) -> T {
    term(Term::Sort(level))
}
fn nat() -> T {
    term(Term::Global("#pt-nat".into(), vec![]))
}
fn var(index: usize) -> T {
    term(Term::Var(index))
}
fn lam(domain: T, body: T) -> T {
    term(Term::Lam(domain, body))
}
fn pi(domain: T, body: T) -> T {
    term(Term::Pi(domain, body))
}
fn global(name: &str, level: Level) -> T {
    term(Term::Global(name.into(), vec![level]))
}
fn number(n: usize) -> T {
    term(Term::NatLiteral {
        family: "#pt-nat".into(),
        value: Natural::parse(&n.to_string()).unwrap(),
    })
}
fn identity(k: &mut Kernel, name: &str, opaque: bool) -> T {
    let u = Level::variable("u".into());
    let ty = pi(sort(u.clone()), pi(var(0), var(1)));
    let body = lam(sort(u), lam(var(0), var(0)));
    if opaque {
        k.opaque_definition(name, vec!["u".into()], ty, body.clone())
            .unwrap();
    } else {
        k.definition(name, vec!["u".into()], ty, body.clone(), false)
            .unwrap();
    }
    body
}
fn sequential(k: &mut Kernel, body: &T, universe: &Level, arguments: &[T]) -> T {
    let mut body = k
        .universes(body, &HashMap::from([("u".into(), universe.clone())]), 0)
        .unwrap();
    for argument in arguments {
        let Term::Lam(_, inner) = body.as_ref() else {
            panic!("lambda")
        };
        body = k.instantiate(inner, argument, 0).unwrap();
    }
    body
}

#[test]
fn same_named_caller_universe_is_not_specialized_as_callee_syntax() {
    let mut k = Kernel::new();
    let body = identity(&mut k, "pick", false);
    let u = Level::variable("u".into());
    let actual = u.successor().unwrap().successor().unwrap();
    let arguments = [sort(u.successor().unwrap()), sort(u.clone())];
    let call = apps(global("pick", actual.clone()), &arguments);
    let ty = sort(u.successor().unwrap());
    k.definition(
        "caller-source",
        vec!["u".into()],
        ty.clone(),
        call.clone(),
        false,
    )
    .unwrap();
    k.reset_budget();
    let result = k.natural_beta_spine(&call, 0).unwrap().unwrap();
    let expected = sequential(&mut k, &body, &actual, &arguments);
    assert!(k.same_syntax(&result, &expected).unwrap());
    assert!(k.same_syntax(&result, &sort(u.clone())).unwrap());
    assert!(!k.same_syntax(&result, &sort(actual)).unwrap());
    k.definition("caller-result", vec!["u".into()], ty, result, false)
        .unwrap();
}

#[test]
fn retained_callee_universes_are_still_substituted() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let body = lam(nat(), lam(nat(), sort(u.clone())));
    k.definition(
        "constant-sort",
        vec!["u".into()],
        pi(nat(), pi(nat(), sort(u.successor().unwrap()))),
        body.clone(),
        false,
    )
    .unwrap();
    let zero = Level::number(0).unwrap();
    let arguments = [number(0), number(1)];
    let call = apps(global("constant-sort", zero.clone()), &arguments);
    k.check(&[], &call, &sort(Level::number(1).unwrap()), 0)
        .unwrap();
    k.reset_budget();
    let result = k.natural_beta_spine(&call, 0).unwrap().unwrap();
    let expected = sequential(&mut k, &body, &zero, &arguments);
    assert!(k.same_syntax(&result, &expected).unwrap());
    assert!(k.same_syntax(&result, &sort(zero)).unwrap());
}

#[test]
fn partial_application_preserves_the_remaining_domain_and_captured_local() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let body = lam(sort(u.clone()), lam(var(0), lam(var(1), var(1))));
    k.definition(
        "capture",
        vec!["u".into()],
        pi(sort(u), pi(var(0), pi(var(1), var(2)))),
        body.clone(),
        false,
    )
    .unwrap();
    let one = Level::number(1).unwrap();
    let arguments = [nat(), var(0)];
    let call = apps(global("capture", one.clone()), &arguments);
    let ty = pi(nat(), nat());
    k.check(&[nat()], &call, &ty, 0).unwrap();
    k.reset_budget();
    let result = k.natural_beta_spine(&call, 0).unwrap().unwrap();
    let expected = sequential(&mut k, &body, &one, &arguments);
    assert!(k.same_syntax(&result, &expected).unwrap());
    assert!(k.same_syntax(&result, &lam(nat(), var(1))).unwrap());
    assert!(!k.same_syntax(&result, &lam(nat(), var(0))).unwrap());
    k.check(&[nat()], &result, &ty, 0).unwrap();
}

#[test]
fn excess_arguments_stay_on_the_original_neutral_spine() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let function_type = pi(sort(u.clone()), sort(u.clone()));
    k.opaque_definition(
        "sealed",
        vec!["u".into()],
        function_type.clone(),
        lam(sort(u.clone()), var(0)),
    )
    .unwrap();
    k.definition(
        "worker",
        vec!["u".into()],
        pi(nat(), pi(nat(), function_type)),
        lam(nat(), lam(nat(), global("sealed", u))),
        false,
    )
    .unwrap();
    let zero = Level::number(0).unwrap();
    let proposition = term(Term::Eq(nat(), number(0), number(0)));
    let call = apps(
        global("worker", zero.clone()),
        &[number(0), number(1), proposition.clone()],
    );
    k.check(&[], &call, &sort(zero.clone()), 0).unwrap();
    let result = k.natural_beta_spine(&call, 0).unwrap().unwrap();
    let expected = apps(global("sealed", zero.clone()), &[proposition]);
    assert!(k.same_syntax(&result, &expected).unwrap());
    k.check(&[], &result, &sort(zero), 0).unwrap();
}

#[test]
fn opacity_arity_and_original_argument_typing_are_preserved() {
    let mut k = Kernel::new();
    identity(&mut k, "hidden", true);
    identity(&mut k, "visible", false);
    let one = Level::number(1).unwrap();
    let opaque = apps(global("hidden", one.clone()), &[nat(), number(0)]);
    k.check(&[], &opaque, &nat(), 0).unwrap();
    assert!(k.natural_beta_spine(&opaque, 0).unwrap().is_none());
    let wrong_arity = apps(
        term(Term::Global("visible".into(), vec![])),
        &[nat(), number(0)],
    );
    assert!(k
        .natural_beta_spine(&wrong_arity, 0)
        .unwrap_err()
        .contains("universe"));
    let bad = apps(
        global("visible", one),
        &[nat(), sort(Level::number(0).unwrap())],
    );
    assert!(k
        .definition("bad-original", vec![], nat(), bad, false)
        .is_err());
    assert!(!k.contains("bad-original").unwrap());
}

#[test]
fn combined_substitution_obeys_the_existing_hard_limits() {
    let mut k = Kernel::new();
    identity(&mut k, "pick", false);
    let call = apps(
        global("pick", Level::number(1).unwrap()),
        &[nat(), number(0)],
    );
    k.reset_budget();
    assert!(k
        .natural_beta_spine(&call, DEPTH)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    k.transformed_bytes = k.budget.phase_bytes() - 1;
    assert!(k
        .natural_beta_spine(&call, 0)
        .unwrap_err()
        .contains("allocation limit"));
}

fn arrows(count: usize, mut result: T) -> T {
    for _ in 0..count {
        result = pi(nat(), result);
    }
    result
}
fn lambdas(count: usize, mut body: T) -> T {
    for _ in 0..count {
        body = lam(nat(), body);
    }
    body
}

#[test]
fn contracted_body_obeys_the_exact_retained_depth_boundary() {
    let mut k = Kernel::new();
    for retained in [4, 5] {
        let name = format!("retained-{retained}");
        let u = Level::variable("u".into());
        k.definition(
            &name,
            vec!["u".into()],
            arrows(retained + 2, sort(u.successor().unwrap())),
            lambdas(retained + 2, sort(u)),
            false,
        )
        .unwrap();
        let call = apps(
            global(&name, Level::number(0).unwrap()),
            &[number(0), number(1)],
        );
        k.check(
            &[],
            &call,
            &arrows(retained, sort(Level::number(1).unwrap())),
            0,
        )
        .unwrap();
        k.reset_budget();
        let result = k.natural_beta_spine(&call, 92);
        if retained == 4 {
            assert!(result.unwrap().is_some());
        } else {
            assert!(result.unwrap_err().contains("recursion depth 97 > 96"));
        }
    }
}

#[test]
fn consumed_frames_do_not_relax_input_or_argument_shift_checks() {
    let mut k = Kernel::new();
    for polymorphic in [false, true] {
        let name = if polymorphic {
            "poly-depth"
        } else {
            "mono-depth"
        };
        k.definition(
            name,
            if polymorphic {
                vec!["u".into()]
            } else {
                vec![]
            },
            arrows(3, nat()),
            lambdas(3, var(2)),
            false,
        )
        .unwrap();
        let head = term(Term::Global(
            name.into(),
            if polymorphic {
                vec![Level::number(0).unwrap()]
            } else {
                vec![]
            },
        ));
        let call = apps(head, &[number(0), number(1)]);
        k.check(&[], &call, &arrows(1, nat()), 0).unwrap();
        k.reset_budget();
        assert!(k.natural_beta_spine(&call, 93).unwrap().is_some());
        k.reset_budget();
        assert!(k
            .natural_beta_spine(&call, 94)
            .unwrap_err()
            .contains("recursion depth 97 > 96"));
        k.reset_budget();
        assert!(k
            .natural_beta_spine(&call, 95)
            .unwrap_err()
            .contains("recursion depth 97 > 96"));
    }
}

#[test]
fn remaining_callee_domains_and_injected_caller_annotations_have_distinct_universes() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let body = lam(sort(u.clone()), lam(var(0), lam(sort(u.clone()), var(1))));
    k.definition(
        "mixed",
        vec!["u".into()],
        pi(sort(u.clone()), pi(var(0), pi(sort(u.clone()), var(2)))),
        body.clone(),
        false,
    )
    .unwrap();
    let argument_type = pi(sort(u.clone()), sort(u.clone()));
    let argument = lam(sort(u.clone()), var(0));
    let actual = u.successor().unwrap();
    let arguments = [argument_type.clone(), argument.clone()];
    let call = apps(global("mixed", actual.clone()), &arguments);
    let ty = pi(sort(actual.clone()), argument_type);
    k.definition(
        "mixed-caller-source",
        vec!["u".into()],
        ty.clone(),
        call.clone(),
        false,
    )
    .unwrap();
    k.reset_budget();
    let result = k.natural_beta_spine(&call, 0).unwrap().unwrap();
    let expected = lam(sort(actual.clone()), argument);
    let ordinary = sequential(&mut k, &body, &actual, &arguments);
    assert!(k.same_syntax(&result, &expected).unwrap());
    assert!(k.same_syntax(&result, &ordinary).unwrap());
    k.definition("mixed-caller-result", vec!["u".into()], ty, result, false)
        .unwrap();
}

#[test]
fn simultaneous_universe_replacements_are_not_recursively_reinterpreted() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let v = Level::variable("v".into());
    let both = u.maximum(&v).unwrap();
    k.definition(
        "two-levels",
        vec!["u".into(), "v".into()],
        arrows(2, sort(both.successor().unwrap())),
        lambdas(2, sort(both)),
        false,
    )
    .unwrap();
    let head = term(Term::Global(
        "two-levels".into(),
        vec![v.clone(), Level::number(0).unwrap()],
    ));
    let call = apps(head, &[number(0), number(1)]);
    let ty = sort(v.successor().unwrap());
    k.definition(
        "two-level-caller",
        vec!["v".into()],
        ty,
        call.clone(),
        false,
    )
    .unwrap();
    k.reset_budget();
    let result = k.natural_beta_spine(&call, 0).unwrap().unwrap();
    assert!(k.same_syntax(&result, &sort(v)).unwrap());
}

#[test]
fn combined_walks_preserve_narrower_probe_and_work_limits() {
    let mut k = Kernel::new();
    identity(&mut k, "probe-pick", false);
    let call = apps(
        global("probe-pick", Level::number(1).unwrap()),
        &[nat(), number(0)],
    );
    k.reset_budget();
    let result = k
        .reduction_probe_limits(0, 1, 1 << 20, |kernel| kernel.natural_beta_spine(&call, 1))
        .unwrap();
    assert!(result.is_none());
    assert!(k.reduction_probe_budget.is_none());
    k.reset_budget();
    k.work = k.budget.work() - 1;
    assert!(k
        .natural_beta_spine(&call, 0)
        .unwrap_err()
        .contains("resource limit"));
}

#[test]
fn retained_walk_and_open_argument_shift_fit_the_same_host_guard() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let nested = 20;
    let wrapped_type = pi(sort(u.clone()), pi(var(0), arrows(nested, var(nested + 1))));
    k.definition(
        "wrap",
        vec!["u".into()],
        wrapped_type,
        lam(sort(u.clone()), lam(var(0), lambdas(nested, var(nested)))),
        false,
    )
    .unwrap();
    let consume_type = pi(sort(u.clone()), pi(arrows(nested, var(nested)), nat()));
    k.opaque_definition(
        "consume",
        vec!["u".into()],
        consume_type,
        lam(sort(u), lam(arrows(nested, var(nested)), number(0))),
    )
    .unwrap();
    let one = Level::number(1).unwrap();
    let argument_type = arrows(nested, nat());
    let argument = lambdas(nested, var(nested));
    let call = apps(
        global("wrap", one.clone()),
        &[argument_type.clone(), argument],
    );
    let caller_body = apps(global("consume", one), &[argument_type, call.clone()]);
    k.definition(
        "shift-pressure-caller",
        vec![],
        pi(nat(), nat()),
        lam(nat(), caller_body),
        false,
    )
    .unwrap();
    k.reset_budget();
    let result = k.natural_beta_spine(&call, 0).unwrap().unwrap();
    let expected = lambdas(2 * nested, var(2 * nested));
    assert!(k.same_syntax(&result, &expected).unwrap());
    k.check(&[nat()], &result, &arrows(2 * nested, nat()), 0)
        .unwrap();
}

#[test]
fn arguments_use_their_own_positions_in_the_input_spine() {
    let mut k = Kernel::new();
    for selected in 0..=1 {
        let name = format!("position-{selected}");
        k.definition(
            &name,
            vec![],
            arrows(2, nat()),
            lambdas(2, var(1 - selected)),
            false,
        )
        .unwrap();
        let call = apps(
            term(Term::Global(name.clone(), vec![])),
            &[number(0), number(1)],
        );
        k.check(&[], &call, &nat(), 0).unwrap();
        k.reset_budget();
        let result = k.natural_beta_spine(&call, 94);
        if selected == 0 {
            assert!(result.unwrap_err().contains("recursion depth 97 > 96"));
        } else {
            assert!(k
                .same_syntax(&result.unwrap().unwrap(), &number(1))
                .unwrap());
        }
        k.reset_budget();
        assert!(k
            .natural_beta_spine(&call, 95)
            .unwrap_err()
            .contains("recursion depth 97 > 96"));
    }
    let bad = apps(
        term(Term::Global("position-1".into(), vec![])),
        &[sort(Level::number(0).unwrap()), number(1)],
    );
    assert!(k
        .definition("bad-discarded-argument", vec![], nat(), bad, false)
        .is_err());
    assert!(!k.contains("bad-discarded-argument").unwrap());
}
