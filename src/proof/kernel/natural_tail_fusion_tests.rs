use super::*;

const NAT: &str = "#pt-nat";

fn nat() -> T {
    term(Term::Global(NAT.into(), vec![]))
}
fn var(index: usize) -> T {
    term(Term::Var(index))
}
fn lam(domain: T, body: T) -> T {
    term(Term::Lam(domain, body))
}
fn app(function: T, argument: T) -> T {
    term(Term::App(function, argument))
}
fn function() -> T {
    term(Term::Pi(nat(), nat()))
}
fn literal(value: &str) -> T {
    term(Term::NatLiteral {
        family: NAT.into(),
        value: Natural::parse(value).unwrap(),
    })
}
fn successor(value: T) -> T {
    term(Term::Ctor {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        constructor: "succ".into(),
        fields: vec![value],
    })
}
fn unary(count: usize) -> T {
    (0..count).fold(
        term(Term::Ctor {
            family: NAT.into(),
            levels: vec![],
            parameters: vec![],
            constructor: "zero".into(),
            fields: vec![],
        }),
        |count, _| successor(count),
    )
}
fn add(left: T, right: T) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![left, lam(nat(), lam(nat(), successor(var(0))))],
        subject: right,
    })
}
fn fold(base: T, body: T, count: T) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), function()),
        branches: vec![base, lam(nat(), lam(function(), lam(nat(), body)))],
        subject: count,
    })
}
fn tail(update: T, count: T) -> T {
    fold(lam(nat(), var(0)), app(var(1), update), count)
}

#[test]
fn identity_tail_doubling_uses_existing_affine_arithmetic() {
    let mut k = Kernel::new();
    // This is the function-valued shape exposed by the exported left shift.
    let source = tail(add(var(0), var(0)), literal("65"));
    let argument = literal("340282366920938463463374607431768211579");
    k.check(&[], &app(source.clone(), argument.clone()), &nat(), 0)
        .unwrap();
    k.reset_budget();
    // Exercise the existing apply-fusion fallback, not just the new helper.
    let fused = k
        .natural_apply_fusion(&source, &argument, 0)
        .unwrap()
        .unwrap();
    k.check(&[], &fused, &nat(), 0).unwrap();
    assert_eq!(
        k.natural_closed_number(NAT, &fused, 0)
            .unwrap()
            .unwrap()
            .decimal(),
        "12554203470773361527671578846415332836742609931060618723328"
    );
}

#[test]
fn first_field_history_observation_reaches_the_tail_fusion_fallback() {
    let mut k = Kernel::new();
    k.inductive(
        "FunctionHistory",
        vec![],
        vec![term(Term::Sort(Level::number(1).unwrap())); 2],
        Level::number(1).unwrap(),
        vec![("pack".into(), vec![var(1), var(1)])],
    )
    .unwrap();
    let history_type = apps(
        term(Term::Global("FunctionHistory".into(), vec![])),
        &[function(), nat()],
    );
    let pack = |function_value: T| {
        term(Term::Ctor {
            family: "FunctionHistory".into(),
            levels: vec![],
            parameters: vec![function(), nat()],
            constructor: "pack".into(),
            fields: vec![function_value, literal("0")],
        })
    };
    let first = |subject: T| {
        term(Term::Project {
            family: "FunctionHistory".into(),
            index: 0,
            subject,
        })
    };
    let history = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), history_type.clone()),
        branches: vec![
            pack(lam(nat(), var(0))),
            lam(
                nat(),
                lam(
                    history_type,
                    pack(lam(nat(), app(first(var(1)), add(var(0), var(0))))),
                ),
            ),
        ],
        subject: literal("5"),
    });
    let source = app(first(history), literal("13"));
    k.check(&[], &source, &nat(), 0).unwrap();
    let fused = k.natural_head(&source, 0).unwrap();
    k.check(&[], &fused, &nat(), 0).unwrap();
    assert_eq!(
        k.natural_closed_number(NAT, &fused, 0)
            .unwrap()
            .unwrap()
            .decimal(),
        "416"
    );
}

#[test]
fn affine_updates_match_small_numeric_references_and_preserve_types() {
    let mut k = Kernel::new();
    for count in 0..=3 {
        k.reset_budget();
        let update = successor(add(var(0), var(0)));
        let source = tail(update.clone(), literal(&count.to_string()));
        let slow = app(tail(update, unary(count)), literal("3"));
        let fused = k
            .natural_tail_apply_fusion(&source, &literal("3"), 0)
            .unwrap()
            .unwrap();
        k.check(&[], &source, &function(), 0).unwrap();
        k.check(&[], &fused, &nat(), 0).unwrap();
        k.check(&[], &slow, &nat(), 0).unwrap();
        assert!(k.convertible(&[], &fused, &slow, 0).unwrap());
        let expected = (4usize << count) - 1;
        assert_eq!(
            k.natural_closed_number(NAT, &fused, 0)
                .unwrap()
                .unwrap()
                .decimal(),
            expected.to_string()
        );
    }
}

#[test]
fn outer_updates_and_open_arguments_do_not_capture_branch_binders() {
    let mut k = Kernel::new();
    let context = [nat()];
    // Under pred, old function, x: #3 is the fixed outer parameter c.
    let source = tail(add(var(0), var(3)), literal("3"));
    let original = app(source.clone(), var(0));
    k.check(&context, &original, &nat(), 0).unwrap();
    let fused = k
        .natural_apply_fusion(&source, &var(0), 0)
        .unwrap()
        .unwrap();
    k.check(&context, &fused, &nat(), 0).unwrap();
    // Substitution closes the outer parameter in both the base and U.
    let closed_original = k.instantiate(&original, &literal("5"), 0).unwrap();
    let closed_fused = k.instantiate(&fused, &literal("5"), 0).unwrap();
    assert!(k
        .convertible(&[], &closed_original, &closed_fused, 0)
        .unwrap());
    assert!(k
        .convertible(&[], &closed_fused, &literal("20"), 0)
        .unwrap());
}

#[test]
fn update_binders_keep_both_their_locals_and_captured_argument() {
    let mut k = Kernel::new();
    // U(x) = x + ((lambda y => x+y) 1), with an inner bound y.
    let update = add(var(0), app(lam(nat(), add(var(1), var(0))), literal("1")));
    let source = tail(update, literal("3"));
    k.check(&[], &source, &function(), 0).unwrap();
    let fused = k
        .natural_tail_apply_fusion(&source, &literal("3"), 0)
        .unwrap()
        .unwrap();
    k.check(&[], &fused, &nat(), 0).unwrap();
    assert!(k.convertible(&[], &fused, &literal("31"), 0).unwrap());
}

#[test]
fn a_nonidentity_base_cannot_reverse_composition_order() {
    let mut k = Kernel::new();
    let source = fold(
        lam(nat(), successor(var(0))),
        app(var(1), add(var(0), var(0))),
        literal("2"),
    );
    k.check(&[], &source, &function(), 0).unwrap();
    assert!(k
        .natural_apply_fusion(&source, &literal("3"), 0)
        .unwrap()
        .is_none());
    // The original yields 2^2*3+1, not 2^2*(3+1).
    assert!(k
        .convertible(&[], &app(source, literal("3")), &literal("13"), 0)
        .unwrap());
}

#[test]
fn extra_old_function_calls_and_predecessor_updates_refuse() {
    let mut k = Kernel::new();
    for update in [
        add(var(0), app(var(1), var(0))),
        add(var(0), var(2)),
        // An old function hidden in a retained lambda's body still counts.
        add(var(0), app(lam(nat(), app(var(2), var(0))), var(0))),
        // Likewise a predecessor captured under another lambda.
        add(var(0), app(lam(nat(), var(3)), var(0))),
    ] {
        k.reset_budget();
        let source = tail(update, literal("2"));
        k.check(&[], &source, &function(), 0).unwrap();
        assert!(k
            .natural_tail_apply_fusion(&source, &literal("3"), 0)
            .unwrap()
            .is_none());
        assert!(k
            .natural_apply_fusion(&source, &literal("3"), 0)
            .unwrap()
            .is_none());
    }
}

#[test]
fn retained_types_and_erased_values_cannot_hide_a_forbidden_local() {
    let mut k = Kernel::new();
    let update = add(var(0), term(Term::Let(function(), var(1), var(1))));
    let source = tail(update, literal("2"));
    k.check(&[], &source, &function(), 0).unwrap();
    assert!(k
        .natural_tail_apply_fusion(&source, &literal("3"), 0)
        .unwrap()
        .is_none());

    // An index may occur only in an annotation, even for a constant value.
    let indexed_type = app(lam(nat(), nat()), var(2));
    let source = tail(
        add(var(0), term(Term::Let(indexed_type, literal("0"), var(1)))),
        literal("2"),
    );
    // This raw annotation is intentionally not normalized by the new rule.
    k.check(&[], &source, &function(), 0).unwrap();
    assert!(k
        .natural_tail_apply_fusion(&source, &literal("3"), 0)
        .unwrap()
        .is_none());
}

#[test]
fn a_different_nominal_natural_function_type_is_not_this_family() {
    let mut k = Kernel::new();
    let other = term(Term::Global("OtherNatural".into(), vec![]));
    k.inductive(
        "OtherNatural",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![
            ("stop".into(), vec![]),
            ("next".into(), vec![other.clone()]),
        ],
    )
    .unwrap();
    let other_function = term(Term::Pi(other.clone(), other.clone()));
    let next = term(Term::Ctor {
        family: "OtherNatural".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "next".into(),
        fields: vec![var(0)],
    });
    let source = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), other_function.clone()),
        branches: vec![
            lam(other.clone(), var(0)),
            lam(
                nat(),
                lam(other_function.clone(), lam(other, app(var(1), next))),
            ),
        ],
        subject: literal("2"),
    });
    k.check(&[], &source, &other_function, 0).unwrap();
    let argument = term(Term::Ctor {
        family: "OtherNatural".into(),
        levels: vec![],
        parameters: vec![],
        constructor: "stop".into(),
        fields: vec![],
    });
    assert!(k
        .natural_tail_apply_fusion(&source, &argument, 0)
        .unwrap()
        .is_none());
}

#[test]
fn a_nontail_body_and_an_ill_typed_erased_value_keep_their_checks() {
    let mut k = Kernel::new();
    let source = fold(
        lam(nat(), var(0)),
        successor(app(var(1), add(var(0), var(0)))),
        literal("2"),
    );
    k.check(&[], &source, &function(), 0).unwrap();
    assert!(k
        .natural_apply_fusion(&source, &literal("3"), 0)
        .unwrap()
        .is_none());
    let bad = tail(
        term(Term::Let(function(), literal("0"), successor(var(1)))),
        literal("2"),
    );
    assert!(k.check(&[], &bad, &function(), 0).is_err());
}

#[test]
fn tail_fusion_obeys_depth_and_nested_probe_limits() {
    let mut k = Kernel::new();
    let source = tail(add(var(0), var(0)), literal("65"));
    assert!(k
        .natural_tail_apply_fusion(&source, &literal("3"), DEPTH + 1)
        .unwrap_err()
        .contains("recursion depth"));
    k.reset_budget();
    let before = k.work;
    assert!(k
        .reduction_probe_limits(0, 8, 1024, |k| {
            k.natural_tail_apply_fusion(&source, &literal("3"), 1)
        })
        .unwrap()
        .flatten()
        .is_none());
    assert!(k.work > before);
    assert!(k.reduction_probe_budget.is_none());
    k.reset_budget();
    assert!(k
        .reduction_probe_limits(0, 16_384, 1, |k| {
            k.natural_tail_apply_fusion(&source, &literal("3"), 1)
        })
        .unwrap()
        .flatten()
        .is_none());
    assert!(k.reduction_probe_budget.is_none());
}

#[test]
fn an_unknown_iteration_count_does_not_add_an_open_conversion_rule() {
    let mut k = Kernel::new();
    let source = tail(add(var(0), var(0)), var(0));
    k.check(&[nat()], &source, &function(), 0).unwrap();
    k.reset_budget();
    assert!(k
        .natural_tail_apply_fusion(&source, &literal("3"), 0)
        .unwrap()
        .is_none());
    assert!(k
        .natural_apply_fusion(&source, &literal("3"), 0)
        .unwrap()
        .is_none());
}
