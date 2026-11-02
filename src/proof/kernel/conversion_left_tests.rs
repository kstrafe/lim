//! Regressions for checked conversion candidates discovered from the left.
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

fn checked_worker_and_alias(k: &mut Kernel) {
    let function_type = pi(nat(), nat());
    k.opaque_definition(
        "left-opaque-worker",
        vec![],
        function_type.clone(),
        lam(nat(), var(0)),
    )
    .unwrap();
    k.definition(
        "left-transparent-alias",
        vec![],
        function_type,
        global("left-opaque-worker"),
        false,
    )
    .unwrap();
}

#[test]
fn transparent_left_alias_matches_opaque_call_in_progress_and_converter() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let left = app(global("left-transparent-alias"), zero());
    let right = app(global("left-opaque-worker"), zero());
    k.check(&[], &left, &nat(), 0).unwrap();
    k.check(&[], &right, &nat(), 0).unwrap();
    assert!(
        k.conversion_progress(&[], &left, &right, 0)
            .unwrap()
            .equivalent
    );
    assert!(
        k.conversion_progress(&[], &right, &left, 0)
            .unwrap()
            .equivalent
    );
    assert!(k.convertible(&[], &left, &right, 0).unwrap());
    assert!(k.convertible(&[], &right, &left, 0).unwrap());
}

#[test]
fn matching_left_hint_does_not_hide_unequal_arguments() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    // f(x) = g(h(x)): predicting g gives no authority to ignore h(x).
    let function_type = pi(nat(), nat());
    k.opaque_definition(
        "left-opaque-h",
        vec![],
        function_type.clone(),
        lam(nat(), var(0)),
    )
    .unwrap();
    k.opaque_definition(
        "left-opaque-g",
        vec![],
        function_type.clone(),
        lam(nat(), var(0)),
    )
    .unwrap();
    k.definition(
        "left-alias-g",
        vec![],
        function_type,
        lam(
            nat(),
            app(
                global("left-opaque-g"),
                app(global("left-opaque-h"), var(0)),
            ),
        ),
        false,
    )
    .unwrap();
    let left = app(global("left-alias-g"), zero());
    let right = app(global("left-opaque-g"), zero());
    k.check(&[], &left, &nat(), 0).unwrap();
    k.check(&[], &right, &nat(), 0).unwrap();
    assert!(
        !k.conversion_progress(&[], &left, &right, 0)
            .unwrap()
            .equivalent
    );
    assert!(!k.convertible(&[], &left, &right, 0).unwrap());
}

#[test]
fn left_lambda_substitution_preserves_captured_outer_variable() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let ctx = [nat()];
    let direct = app(global("left-opaque-worker"), var(0));
    // Under the lambda, Var(1) captures the surrounding context; applying the
    // lambda substitutes zero only for its own Var(0).
    let captured = app(
        lam(nat(), app(global("left-opaque-worker"), var(1))),
        zero(),
    );
    let incorrectly_substituted = app(
        lam(nat(), app(global("left-opaque-worker"), var(0))),
        zero(),
    );
    k.check(&ctx, &direct, &nat(), 0).unwrap();
    k.check(&ctx, &captured, &nat(), 0).unwrap();
    k.check(&ctx, &incorrectly_substituted, &nat(), 0).unwrap();
    assert!(
        k.conversion_progress(&ctx, &captured, &direct, 0)
            .unwrap()
            .equivalent
    );
    assert!(
        !k.conversion_progress(&ctx, &incorrectly_substituted, &direct, 0)
            .unwrap()
            .equivalent
    );
}

#[test]
fn opaque_left_declaration_never_exposes_its_body() {
    let mut k = Kernel::new();
    let function_type = pi(nat(), nat());
    k.opaque_definition(
        "left-hidden",
        vec![],
        function_type.clone(),
        lam(nat(), var(0)),
    )
    .unwrap();
    k.opaque_definition("left-target", vec![], function_type, lam(nat(), var(0)))
        .unwrap();
    let left = app(global("left-hidden"), zero());
    let right = app(global("left-target"), zero());
    assert!(
        !k.conversion_progress(&[], &left, &right, 0)
            .unwrap()
            .equivalent
    );
    assert!(!k.convertible(&[], &left, &right, 0).unwrap());
}

#[test]
fn left_hint_cannot_bypass_explicit_universe_arity_or_source_checking() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let malformed = term(Term::Global(
        "left-transparent-alias".into(),
        vec![Level::number(0).unwrap()],
    ));
    let body = app(malformed, zero());
    let error = k
        .definition("left-bad-universe-source", vec![], nat(), body, false)
        .unwrap_err();
    assert!(error.contains("universe"), "{error}");
    assert!(!k.contains("left-bad-universe-source"));
}

#[test]
fn right_reduction_can_expose_the_target_for_a_later_left_hint() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let ctx = [nat()];
    let left = app(
        lam(nat(), app(global("left-opaque-worker"), var(1))),
        succ(zero()),
    );
    let right = app(
        lam(nat(), app(global("left-transparent-alias"), var(1))),
        zero(),
    );
    k.check(&ctx, &left, &nat(), 0).unwrap();
    k.check(&ctx, &right, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(
        k.conversion_progress(&ctx, &left, &right, 0)
            .unwrap()
            .equivalent
    );
    assert!(k.reduction_probe_budget.is_none());
    assert!(k.convertible(&ctx, &left, &right, 0).unwrap());
}

fn selector(k: &mut Kernel) -> (T, T) {
    let choice = global("LeftChoice");
    k.inductive(
        "LeftChoice",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("off".into(), vec![]), ("on".into(), vec![])],
    )
    .unwrap();
    let ty = pi(choice.clone(), pi(nat(), pi(nat(), nat())));
    let body = lam(
        choice.clone(),
        lam(
            nat(),
            lam(
                nat(),
                term(Term::Induct {
                    family: "LeftChoice".into(),
                    levels: vec![],
                    parameters: vec![],
                    indices: vec![],
                    motive: lam(choice, nat()),
                    branches: vec![var(0), var(1)],
                    subject: var(2),
                }),
            ),
        ),
    );
    k.definition("left-selector", vec![], ty.clone(), body, false)
        .unwrap();
    k.definition(
        "left-selector-alias",
        vec![],
        ty.clone(),
        global("left-selector"),
        false,
    )
    .unwrap();
    let off = term(Term::Ctor {
        family: "LeftChoice".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "off".into(),
        fields: vec![],
    });
    (ty, off)
}

#[test]
fn several_checked_left_steps_can_select_the_unchanged_right_call() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let (_, off) = selector(&mut k);
    let right = app(global("left-opaque-worker"), zero());
    let left = apps(
        global("left-selector-alias"),
        &[off, succ(zero()), right.clone()],
    );
    k.check(&[], &left, &nat(), 0).unwrap();
    assert!(
        k.conversion_progress(&[], &left, &right, 0)
            .unwrap()
            .equivalent
    );
    assert!(k.convertible(&[], &left, &right, 0).unwrap());
}

#[test]
fn mentioning_the_right_head_in_an_unselected_branch_does_not_prove_equality() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let (_, _) = selector(&mut k);
    k.opaque_definition(
        "left-other-call",
        vec![],
        pi(nat(), nat()),
        lam(nat(), var(0)),
    )
    .unwrap();
    let on = term(Term::Ctor {
        family: "LeftChoice".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "on".into(),
        fields: vec![],
    });
    let right = app(global("left-opaque-worker"), zero());
    let other = app(global("left-other-call"), zero());
    let left = apps(global("left-selector-alias"), &[on, other, right.clone()]);
    k.check(&[], &left, &nat(), 0).unwrap();
    assert!(
        !k.conversion_progress(&[], &left, &right, 0)
            .unwrap()
            .equivalent
    );
    assert!(!k.convertible(&[], &left, &right, 0).unwrap());
}

#[test]
fn left_and_right_attempts_keep_the_same_eight_candidate_cutoff() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let (ty, off) = selector(&mut k);
    let mut head = global("left-selector-alias");
    for i in 0..9 {
        let name = format!("left-selector-chain-{i}");
        k.definition(&name, vec![], ty.clone(), head, false)
            .unwrap();
        head = global(&name);
    }
    let right = app(global("left-opaque-worker"), zero());
    let left = apps(head, &[off, succ(zero()), right.clone()]);
    k.check(&[], &left, &nat(), 0).unwrap();
    let progress = k.conversion_progress(&[], &left, &right, 0).unwrap();
    assert!(!progress.equivalent && progress.left.is_some());
    assert!(k.convertible(&[], &left, &right, 0).unwrap());
}

#[test]
fn an_unknown_selector_cannot_choose_a_branch_merely_containing_the_right_head() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let (_, _) = selector(&mut k);
    k.opaque_definition(
        "left-other-call",
        vec![],
        pi(nat(), nat()),
        lam(nat(), var(0)),
    )
    .unwrap();
    let ctx = [global("LeftChoice")];
    let right = app(global("left-opaque-worker"), zero());
    let left = apps(
        global("left-selector-alias"),
        &[
            var(0),
            app(global("left-other-call"), zero()),
            right.clone(),
        ],
    );
    k.check(&ctx, &left, &nat(), 0).unwrap();
    assert!(
        !k.conversion_progress(&ctx, &left, &right, 0)
            .unwrap()
            .equivalent
    );
    assert!(!k.convertible(&ctx, &left, &right, 0).unwrap());
}

#[test]
fn a_declined_left_step_retains_only_a_prior_completed_prefix() {
    let mut k = Kernel::new();
    checked_worker_and_alias(&mut k);
    let function = pi(nat(), nat());
    let composed = term(Term::Induct {
        family: "#pt-nat".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), function.clone()),
        branches: vec![
            lam(nat(), var(0)),
            lam(
                nat(),
                lam(
                    function.clone(),
                    lam(nat(), app(var(1), app(var(1), var(0)))),
                ),
            ),
        ],
        subject: term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse("512").unwrap(),
        }),
    });
    k.definition(
        "left-expensive",
        vec![],
        function.clone(),
        lam(nat(), app(composed, var(0))),
        false,
    )
    .unwrap();
    k.definition(
        "left-expensive-alias",
        vec![],
        function,
        global("left-expensive"),
        false,
    )
    .unwrap();
    let right = app(global("left-opaque-worker"), zero());
    let direct = app(global("left-expensive"), right.clone());
    let left = app(global("left-expensive-alias"), right.clone());
    k.check(&[], &left, &nat(), 0).unwrap();
    k.reset_budget();
    let progress = k.conversion_progress(&[], &left, &right, 0).unwrap();
    assert!(!progress.equivalent);
    assert!(k.same_syntax(&progress.left.unwrap(), &direct).unwrap());
    assert!(progress.right.is_none());
    assert!(k.work > 0 && k.transformed_bytes > 0);
    assert!(k.reduction_probe_budget.is_none());
}
