//! Kernel-only regressions. Register inside core.rs with:
//! #[cfg(test)] #[path = "core_tests.rs"] mod core_tests;
//! These tests intentionally require rejection of the audit counterexamples.
use super::*;

fn level(n: u32) -> Level {
    Level::number(n).unwrap()
}
fn sort(n: u32) -> T {
    term(Term::Sort(level(n)))
}
fn var(n: usize) -> T {
    term(Term::Var(n))
}
fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn nat() -> T {
    global("#pt-nat")
}
fn falsity() -> T {
    global("#pt-false")
}
fn pi(a: T, b: T) -> T {
    term(Term::Pi(a, b))
}
fn lam(a: T, b: T) -> T {
    term(Term::Lam(a, b))
}
fn app(a: T, b: T) -> T {
    term(Term::App(a, b))
}
fn eq(a: T, x: T, y: T) -> T {
    term(Term::Eq(a, x, y))
}
fn refl(a: T, x: T) -> T {
    term(Term::Refl(a, x))
}
fn ctor(family: &str, parameters: Vec<T>, constructor: &str, fields: Vec<T>) -> T {
    term(Term::Ctor {
        family: family.into(),
        levels: vec![],
        parameters,
        constructor: constructor.into(),
        fields,
    })
}
fn zero() -> T {
    ctor("#pt-nat", vec![], "zero", vec![])
}
fn succ(n: T) -> T {
    ctor("#pt-nat", vec![], "succ", vec![n])
}

#[test]
fn explicit_negative_family_reference_must_not_prove_false() {
    let mut k = Kernel::new();
    let bad = global("Bad");
    let function = pi(bad.clone(), falsity());
    // Unlike SelfType, this Global used to bypass contains_self completely.
    if k.inductive(
        "Bad",
        vec![],
        vec![],
        level(1),
        vec![("roll".into(), vec![function.clone()])],
    )
    .is_err()
    {
        return;
    }
    // d x := match x with roll f => f (roll f)
    let diagonal = lam(
        bad.clone(),
        term(Term::Induct {
            family: "Bad".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(bad.clone(), falsity()),
            branches: vec![lam(
                function.clone(),
                app(var(0), ctor("Bad", vec![], "roll", vec![var(0)])),
            )],
            subject: var(0),
        }),
    );
    k.reset_budget();
    k.definition("diagonal", vec![], function, diagonal, false)
        .unwrap();
    // No normalization of this divergent proof is necessary to check its type.
    let proof = app(
        global("diagonal"),
        ctor("Bad", vec![], "roll", vec![global("diagonal")]),
    );
    k.reset_budget();
    assert!(
        k.definition("absurd", vec![], falsity(), proof, true)
            .is_err(),
        "negative self-reference admitted a closed theorem of False"
    );
}

#[test]
fn nested_self_marker_is_rejected() {
    let mut k = Kernel::new();
    let negative = pi(term(Term::SelfType), falsity());
    assert!(k
        .inductive(
            "BadMarker",
            vec![],
            vec![],
            level(1),
            vec![("roll".into(), vec![negative])]
        )
        .is_err());
}

#[test]
fn equality_motive_must_bind_the_fresh_endpoint() {
    let mut k = Kernel::new();
    // At the elimination site: A=#2, a=#1, p=#0 : Eq(A,a,a).
    // Invalid J motive: lambda y:A. lambda q:Eq(A,a,a). Eq(Eq(A,a,a),refl,q).
    // The equality domain is constant in y. Even though proof irrelevance
    // validates K, a malformed J motive must still be rejected before use.
    let motive = lam(
        var(2),
        lam(
            eq(var(3), var(2), var(2)),
            eq(eq(var(4), var(3), var(3)), refl(var(4), var(3)), var(0)),
        ),
    );
    let elimination = term(Term::EqElim {
        ty: var(2),
        left: var(1),
        right: var(1),
        proof: var(0),
        motive,
        base: refl(eq(var(2), var(1), var(1)), refl(var(2), var(1))),
    });
    let ty = pi(
        sort(1),
        pi(
            var(0),
            pi(
                eq(var(1), var(0), var(0)),
                eq(eq(var(2), var(1), var(1)), refl(var(2), var(1)), var(0)),
            ),
        ),
    );
    let proof = lam(
        sort(1),
        lam(var(0), lam(eq(var(1), var(0), var(0)), elimination)),
    );
    assert!(
        k.definition("axiom-k", vec![], ty, proof, true).is_err(),
        "EqElim accepted a motive whose proof binder is not Eq(A,left,fresh_endpoint)"
    );
}

#[test]
fn valid_equality_elimination_reduces_on_refl() {
    let mut k = Kernel::new();
    // P(y,q) := Eq(Nat,y,zero), with q genuinely depending on y.
    let motive = lam(
        nat(),
        lam(eq(nat(), zero(), var(0)), eq(nat(), var(1), zero())),
    );
    let base = refl(nat(), zero());
    let value = term(Term::EqElim {
        ty: nat(),
        left: zero(),
        right: zero(),
        proof: refl(nat(), zero()),
        motive,
        base: base.clone(),
    });
    k.check(&[], &value, &eq(nat(), zero(), zero()), 0).unwrap();
    assert!(k.convertible(&[], &value, &base, 0).unwrap());
}

#[test]
fn polymorphic_datatype_at_prop_must_not_gain_large_elimination() {
    let mut k = Kernel::new();
    k.inductive(
        "Choice",
        vec!["u".into()],
        vec![],
        Level::variable("u".into()),
        vec![("left".into(), vec![]), ("right".into(), vec![])],
    )
    .unwrap();
    let prop_choice = term(Term::Global("Choice".into(), vec![level(0)]));
    let subject = term(Term::Ctor {
        family: "Choice".into(),
        levels: vec![level(0)],
        parameters: vec![],
        constructor: "left".into(),
        fields: vec![],
    });
    let elimination = term(Term::Induct {
        family: "Choice".into(),
        levels: vec![level(0)],
        parameters: vec![],
        indices: vec![],
        motive: lam(prop_choice, nat()),
        branches: vec![zero(), succ(zero())],
        subject,
    });
    assert!(
        k.infer(&[], &elimination, 0).is_err(),
        "unspecialized Family.sort/large allowed a two-constructor Prop to eliminate into Nat"
    );
}

#[test]
fn ordinary_multiconstructor_prop_cannot_eliminate_into_nat() {
    let mut k = Kernel::new();
    k.inductive(
        "ChoiceProp",
        vec![],
        vec![],
        level(0),
        vec![("left".into(), vec![]), ("right".into(), vec![])],
    )
    .unwrap();
    let elimination = term(Term::Induct {
        family: "ChoiceProp".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global("ChoiceProp"), nat()),
        branches: vec![zero(), succ(zero())],
        subject: ctor("ChoiceProp", vec![], "left", vec![]),
    });
    assert!(k.infer(&[], &elimination, 0).is_err());
}

#[test]
fn substitution_shifts_argument_and_removes_only_the_eliminated_binder() {
    let mut k = Kernel::new();
    // Under the lambda: #2 is above the removed binder; #1 names that binder.
    let body = lam(nat(), app(var(2), var(1)));
    let instantiated = k.instantiate(&body, &var(0), 0).unwrap();
    let expected = lam(nat(), app(var(1), var(1)));
    assert!(k.convertible(&[], &instantiated, &expected, 0).unwrap());
    let shifted = k.shift(&lam(nat(), app(var(1), var(0))), 2, 0, 0).unwrap();
    assert!(k
        .convertible(&[], &shifted, &lam(nat(), app(var(3), var(0))), 0)
        .unwrap());
}

#[test]
fn dependent_context_lookup_rebases_stored_types() {
    let mut k = Kernel::new();
    // A : Type1, a : A, p : Eq(A,a,a); each annotation lives before its binder.
    let ctx = vec![sort(1), var(0), eq(var(1), var(0), var(0))];
    let actual = k.infer(&ctx, &var(0), 0).unwrap();
    assert!(k
        .convertible(&[], &actual, &eq(var(2), var(1), var(1)), 0)
        .unwrap());
}

#[test]
fn parameterized_recursor_handles_ih_before_dependent_later_fields() {
    let mut k = Kernel::new();
    // Chain(A:Type1) : Type1
    // end(x:A); next(tag:Nat, child:Self, witness:Eq(Nat,tag,tag)).
    k.inductive(
        "Chain",
        vec![],
        vec![sort(1)],
        level(1),
        vec![
            ("end".into(), vec![var(0)]),
            (
                "next".into(),
                vec![nat(), term(Term::SelfType), eq(nat(), var(1), var(1))],
            ),
        ],
    )
    .unwrap();
    let chain = app(global("Chain"), nat());
    let end = ctor("Chain", vec![nat()], "end", vec![zero()]);
    let subject = ctor(
        "Chain",
        vec![nat()],
        "next",
        vec![zero(), end, refl(nat(), zero())],
    );
    // next branch: tag, child, IH, witness; witness's domain must see tag=#2.
    let next = lam(
        nat(),
        lam(
            chain.clone(),
            lam(nat(), lam(eq(nat(), var(2), var(2)), succ(var(1)))),
        ),
    );
    let eliminate = term(Term::Induct {
        family: "Chain".into(),
        levels: vec![],
        parameters: vec![nat()],
        indices: vec![],
        motive: lam(chain, nat()),
        branches: vec![lam(nat(), zero()), next],
        subject,
    });
    k.check(&[], &eliminate, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.convertible(&[], &eliminate, &succ(zero()), 0).unwrap());
}

#[test]
fn missing_recursive_ih_binder_is_rejected() {
    let mut k = Kernel::new();
    let elimination = term(Term::Induct {
        family: "#pt-nat".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![zero(), lam(nat(), zero())],
        subject: succ(zero()),
    });
    assert!(k.infer(&[], &elimination, 0).is_err());
}

#[test]
fn levels_maximum_and_substitution_preserve_natural_offsets() {
    let u = Level::variable("u".into());
    let v = Level::variable("v".into());
    let u2 = u.successor().unwrap().successor().unwrap();
    let level_expr = level(3).maximum(&u2).unwrap().maximum(&v).unwrap();
    assert!(!level_expr.at_most(&u2).unwrap());
    assert!(u.at_most(&u2).unwrap());
    assert!(!u2.at_most(&u).unwrap());
    let values = HashMap::from([("u".into(), level(4)), ("v".into(), level(1))]);
    assert_eq!(level_expr.substitute(&values).unwrap(), level(6));
    assert!(Level::number(LEVEL).unwrap().successor().is_err());
}

#[test]
fn proof_irrelevance_and_function_eta_do_not_introduce_cumulativity() {
    let mut k = Kernel::new();
    assert!(k.check(&[], &sort(0), &sort(2), 0).is_err());
    let function = pi(nat(), nat());
    let ctx = vec![function];
    let eta = lam(nat(), app(var(1), var(0)));
    k.infer(&ctx, &eta, 0).unwrap();
    assert!(k.convertible(&ctx, &var(0), &eta, 0).unwrap());
    assert!(k.convertible(&ctx, &eta, &var(0), 0).unwrap());
    k.inductive(
        "TwoProofs",
        vec![],
        vec![],
        level(0),
        vec![("a".into(), vec![]), ("b".into(), vec![])],
    )
    .unwrap();
    let a = ctor("TwoProofs", vec![], "a", vec![]);
    let b = ctor("TwoProofs", vec![], "b", vec![]);
    k.check(&[], &a, &global("TwoProofs"), 0).unwrap();
    k.check(&[], &b, &global("TwoProofs"), 0).unwrap();
    assert!(k.convertible(&[], &a, &b, 0).unwrap());
    k.definition(
        "opaque-proof",
        vec![],
        eq(nat(), zero(), zero()),
        refl(nat(), zero()),
        true,
    )
    .unwrap();
    let opaque = global("opaque-proof");
    assert!(
        matches!(k.whnf(&[], &opaque, 0).unwrap().as_ref(), Term::Global(name, _) if name == "opaque-proof")
    );
    assert!(k
        .convertible(&[], &opaque, &refl(nat(), zero()), 0)
        .unwrap());
}

#[test]
fn opaque_loop_equality_proofs_compute_but_arbitrary_endpoints_do_not() {
    let mut k = Kernel::new();
    let motive = lam(nat(), lam(eq(nat(), zero(), var(0)), nat()));
    for (right, computes) in [(zero(), true), (succ(zero()), false)] {
        let ctx = vec![eq(nat(), zero(), right.clone())];
        let value = term(Term::EqElim {
            ty: nat(),
            left: zero(),
            right,
            motive: motive.clone(),
            base: zero(),
            proof: var(0),
        });
        k.check(&ctx, &value, &nat(), 0).unwrap();
        assert_eq!(k.convertible(&ctx, &value, &zero(), 0).unwrap(), computes);
    }
}

#[test]
fn function_eta_shifts_outer_locals_without_capture() {
    let mut k = Kernel::new();
    let function_type = pi(nat(), nat());
    let ctx = vec![function_type.clone(), nat()];
    let function = var(1);
    let expanded = lam(nat(), app(var(2), var(0)));
    let captured = lam(nat(), app(var(2), var(1)));
    for value in [&function, &expanded, &captured] {
        k.check(&ctx, value, &function_type, 0).unwrap();
    }
    assert!(k.convertible(&ctx, &function, &expanded, 0).unwrap());
    assert!(k.convertible(&ctx, &expanded, &function, 0).unwrap());
    assert!(!k.convertible(&ctx, &function, &captured, 0).unwrap());
    assert!(!k.convertible(&ctx, &captured, &function, 0).unwrap());
}

#[test]
fn dependent_pair_eta_preserves_the_second_component_type() {
    let mut k = Kernel::new();
    let sigma = term(Term::Sigma(nat(), eq(nat(), var(0), var(0))));
    let ctx = vec![sigma.clone()];
    let pair = var(0);
    let first = term(Term::First(pair.clone()));
    let second = term(Term::Second(pair.clone()));
    let expanded = term(Term::Pair(sigma.clone(), first.clone(), second.clone()));
    k.check(&ctx, &expanded, &sigma, 0).unwrap();
    assert!(k.convertible(&ctx, &pair, &expanded, 0).unwrap());
    assert!(k.convertible(&ctx, &expanded, &pair, 0).unwrap());
    // Eta works inside dependent type indices, not just a top-level equality.
    let carrier = term(Term::Sigma(nat(), nat()));
    let ctx = vec![carrier.clone(), pi(carrier.clone(), sort(1))];
    let rebuilt = term(Term::Pair(
        carrier,
        term(Term::First(var(1))),
        term(Term::Second(var(1))),
    ));
    let direct = app(var(0), var(1));
    let through_eta = app(var(0), rebuilt);
    k.sort(&ctx, &direct, 0).unwrap();
    k.sort(&ctx, &through_eta, 0).unwrap();
    assert!(k.convertible(&ctx, &direct, &through_eta, 0).unwrap());
}

#[test]
fn eta_conversion_is_transitive_for_neutral_pairs_with_proof_components() {
    let mut k = Kernel::new();
    let proof = eq(nat(), zero(), zero());
    let sigma = term(Term::Sigma(proof.clone(), proof));
    let ctx = vec![sigma.clone(), sigma.clone()];
    let a = var(1);
    let b = var(0);
    let rebuilt = term(Term::Pair(
        sigma.clone(),
        term(Term::First(a.clone())),
        term(Term::Second(a.clone())),
    ));
    for value in [&a, &b, &rebuilt] {
        k.check(&ctx, value, &sigma, 0).unwrap();
    }
    for (left, right) in [(&a, &rebuilt), (&rebuilt, &b), (&a, &b), (&b, &a)] {
        assert!(k.convertible(&ctx, left, right, 0).unwrap());
    }
    // The same issue propagates through eta for functions returning pairs.
    let function_type = pi(nat(), sigma);
    let ctx = vec![function_type.clone(), function_type.clone()];
    let expanded = lam(nat(), app(var(2), var(0)));
    k.check(&ctx, &expanded, &function_type, 0).unwrap();
    assert!(k.convertible(&ctx, &var(1), &expanded, 0).unwrap());
    assert!(k.convertible(&ctx, &expanded, &var(0), 0).unwrap());
    assert!(k.convertible(&ctx, &var(1), &var(0), 0).unwrap());
}

#[test]
fn neutral_data_eta_comparisons_terminate_with_false() {
    let mut k = Kernel::new();
    let sigma = term(Term::Sigma(nat(), nat()));
    for ty in [pi(nat(), nat()), pi(nat(), sigma.clone()), sigma] {
        let ctx = vec![ty.clone(), ty.clone()];
        for value in [var(0), var(1)] {
            k.check(&ctx, &value, &ty, 0).unwrap();
        }
        for (a, b) in [(var(0), var(1)), (var(1), var(0))] {
            k.reset_budget();
            // Budget exhaustion is a failure, not a negative conversion.
            assert!(!k.convertible(&ctx, &a, &b, 0).unwrap());
        }
    }
    let nat_function = lam(nat(), zero());
    let prop_function = lam(sort(0), zero());
    k.infer(&[], &nat_function, 0).unwrap();
    k.infer(&[], &prop_function, 0).unwrap();
    assert!(!k
        .convertible(&[], &nat_function, &prop_function, 0)
        .unwrap());
}

#[test]
fn opaque_fieldless_singletons_have_the_constructor_computation_rule() {
    let mut k = Kernel::new();
    k.inductive(
        "ProofUnit",
        vec![],
        vec![],
        level(0),
        vec![("unit".into(), vec![])],
    )
    .unwrap();
    let ctx = vec![global("ProofUnit")];
    let value = term(Term::Induct {
        family: "ProofUnit".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global("ProofUnit"), nat()),
        branches: vec![zero()],
        subject: var(0),
    });
    k.check(&ctx, &value, &nat(), 0).unwrap();
    assert!(k.convertible(&ctx, &value, &zero(), 0).unwrap());
    k.inductive(
        "DataUnit",
        vec![],
        vec![],
        level(1),
        vec![("unit".into(), vec![])],
    )
    .unwrap();
    let data_context = vec![global("DataUnit")];
    let data_value = term(Term::Induct {
        family: "DataUnit".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global("DataUnit"), nat()),
        branches: vec![zero()],
        subject: var(0),
    });
    k.check(&data_context, &data_value, &nat(), 0).unwrap();
    assert!(k
        .convertible(&data_context, &data_value, &zero(), 0)
        .unwrap());
}

#[test]
fn fieldless_data_conversion_preserves_nominal_types_and_parameters() {
    let mut k = Kernel::new();
    for name in ["UnitA", "UnitB"] {
        k.inductive(
            name,
            vec![],
            vec![],
            level(1),
            vec![("only".into(), vec![])],
        )
        .unwrap();
    }
    let unit = global("UnitA");
    let value = ctor("UnitA", vec![], "only", vec![]);
    let ctx = vec![unit.clone(), unit.clone()];
    k.check(&ctx, &value, &unit, 0).unwrap();
    assert!(k.convertible(&ctx, &var(0), &var(1), 0).unwrap());
    assert!(k.convertible(&ctx, &var(0), &value, 0).unwrap());
    assert!(k.convertible(&ctx, &value, &var(0), 0).unwrap());
    assert!(!k.convertible(&[], &unit, &global("UnitB"), 0).unwrap());
    let other = ctor("UnitB", vec![], "only", vec![]);
    assert!(!k.convertible(&[], &value, &other, 0).unwrap());

    k.inductive(
        "Tag",
        vec![],
        vec![nat()],
        level(1),
        vec![("only".into(), vec![])],
    )
    .unwrap();
    assert!(!k.unit_type(&global("Tag"), 0).unwrap());
    let left = app(global("Tag"), zero());
    let right = app(global("Tag"), succ(zero()));
    assert!(k.unit_type(&left, 0).unwrap());
    let ctx = vec![left, right];
    k.infer(&ctx, &var(0), 0).unwrap();
    k.infer(&ctx, &var(1), 0).unwrap();
    assert!(!k.convertible(&ctx, &var(0), &var(1), 0).unwrap());
}

#[test]
fn fieldless_unit_conversion_composes_with_pi_and_sigma_eta() {
    let mut k = Kernel::new();
    k.inductive(
        "Unit",
        vec![],
        vec![],
        level(1),
        vec![("only".into(), vec![])],
    )
    .unwrap();
    let unit = global("Unit");
    for ty in [
        pi(nat(), unit.clone()),
        term(Term::Sigma(unit.clone(), unit)),
    ] {
        let ctx = vec![ty.clone(), ty.clone()];
        k.check(&ctx, &var(0), &ty, 0).unwrap();
        k.check(&ctx, &var(1), &ty, 0).unwrap();
        k.reset_budget();
        assert!(k.convertible(&ctx, &var(0), &var(1), 0).unwrap());
        assert!(k.convertible(&ctx, &var(1), &var(0), 0).unwrap());
    }
}

#[test]
fn unit_conversion_compares_universe_arguments_in_both_directions() {
    let mut k = Kernel::new();
    k.inductive(
        "UnitAt",
        vec!["u".into()],
        vec![],
        Level::variable("u".into()),
        vec![("only".into(), vec![])],
    )
    .unwrap();
    let mut values = vec![];
    for universe in [0, 1] {
        let ty = term(Term::Global("UnitAt".into(), vec![level(universe)]));
        let value = term(Term::Ctor {
            family: "UnitAt".into(),
            levels: vec![level(universe)],
            parameters: vec![],
            constructor: "only".into(),
            fields: vec![],
        });
        k.check(&[], &value, &ty, 0).unwrap();
        values.push(value);
    }
    assert!(!k.convertible(&[], &values[0], &values[1], 0).unwrap());
    assert!(!k.convertible(&[], &values[1], &values[0], 0).unwrap());
}

#[test]
fn proof_let_keeps_type_definitions_available_inside_its_body() {
    let mut k = Kernel::new();
    let value = term(Term::Let(sort(1), nat(), refl(var(0), zero())));
    k.definition(
        "let-type-alias",
        vec![],
        eq(nat(), zero(), zero()),
        value,
        true,
    )
    .unwrap();
}

#[test]
fn proof_let_substitution_shifts_values_and_binds_only_the_body() {
    let mut k = Kernel::new();
    let value = term(Term::Let(nat(), var(0), lam(nat(), var(1))));
    k.check(&[nat()], &value, &pi(nat(), nat()), 0).unwrap();
    assert!(k
        .convertible(&[nat()], &value, &lam(nat(), var(1)), 0)
        .unwrap());
    let shifted = k.shift(&value, 1, 0, 0).unwrap();
    let expected = term(Term::Let(nat(), var(1), lam(nat(), var(1))));
    assert!(k
        .convertible(&[nat(), nat()], &shifted, &expected, 0)
        .unwrap());
    let outer = term(Term::Let(nat(), var(0), lam(nat(), var(2))));
    let instantiated = k.instantiate(&outer, &zero(), 0).unwrap();
    k.check(&[], &instantiated, &pi(nat(), nat()), 0).unwrap();
    assert!(k
        .convertible(&[], &instantiated, &lam(nat(), zero()), 0)
        .unwrap());
}

#[test]
fn unused_proof_let_definitions_are_checked_before_zeta_reduction() {
    let mut k = Kernel::new();
    let expected = eq(nat(), zero(), zero());
    for (name, value) in [
        (
            "bad-let-value",
            term(Term::Let(nat(), refl(nat(), zero()), refl(nat(), zero()))),
        ),
        (
            "bad-let-type",
            term(Term::Let(zero(), zero(), refl(nat(), zero()))),
        ),
    ] {
        assert!(k
            .definition(name, vec![], expected.clone(), value, true)
            .is_err());
        assert!(!k.contains(name));
    }
}

#[test]
fn proof_lets_cannot_hide_negative_inductive_occurrences() {
    for hidden in [
        term(Term::Let(sort(0), pi(global("BadLet"), falsity()), var(0))),
        term(Term::Let(
            term(Term::Let(sort(0), pi(global("BadLet"), falsity()), nat())),
            zero(),
            nat(),
        )),
        term(Term::Let(nat(), zero(), pi(global("BadLet"), falsity()))),
    ] {
        let mut k = Kernel::new();
        let error = k
            .inductive(
                "BadLet",
                vec![],
                vec![],
                level(1),
                vec![("roll".into(), vec![hidden])],
            )
            .unwrap_err();
        assert!(error.contains("strict positivity"), "{error}");
        assert!(!k.contains("BadLet"));
    }
}

fn indexed_counter(k: &mut Kernel) {
    k.indexed_inductive(
        "Counter",
        vec![],
        vec![],
        vec![nat()],
        level(1),
        vec![
            ("zero".into(), vec![], vec![zero()]),
            (
                "step".into(),
                vec![nat(), term(Term::SelfAt(vec![var(0)]))],
                vec![succ(var(1))],
            ),
        ],
    )
    .unwrap();
}
fn counter(index: T) -> T {
    app(global("Counter"), index)
}
fn counter_motive() -> T {
    lam(nat(), lam(counter(var(0)), nat()))
}

#[test]
fn indexed_reduction_constructs_a_well_typed_child_recursor() {
    let mut k = Kernel::new();
    indexed_counter(&mut k);
    let motive = counter_motive();
    let (family, _) = k.family("Counter", &[], 0).unwrap();
    let branch = k
        .branch_type(
            &[],
            "Counter",
            &[],
            &[],
            &motive,
            &family.constructors[1],
            0,
        )
        .unwrap();
    let ctx = vec![branch];
    let child = ctor("Counter", vec![], "zero", vec![]);
    let subject = ctor("Counter", vec![], "step", vec![zero(), child]);
    let value = term(Term::Induct {
        family: "Counter".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![succ(zero())],
        motive,
        branches: vec![zero(), var(0)],
        subject,
    });
    k.check(&ctx, &value, &nat(), 0).unwrap();
    let reduced = k.whnf(&ctx, &value, 0).unwrap();
    // The neutral branch leaves its IH argument visible. Rechecking the
    // result detects a child recursor accidentally given its parent's index.
    k.check(&ctx, &reduced, &nat(), 0).unwrap();
    let Term::App(_, ih) = reduced.as_ref() else {
        panic!("expected the induction hypothesis argument")
    };
    let Term::Induct { indices, .. } = ih.as_ref() else {
        panic!("expected a recursive eliminator")
    };
    assert!(k.convertible(&ctx, &indices[0], &zero(), 0).unwrap());
}

#[test]
fn indexed_motives_must_use_fresh_generic_indices() {
    let mut k = Kernel::new();
    indexed_counter(&mut k);
    let frozen = lam(nat(), lam(counter(zero()), nat()));
    let value = term(Term::Induct {
        family: "Counter".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![zero()],
        motive: frozen,
        branches: vec![zero(), zero()],
        subject: ctor("Counter", vec![], "zero", vec![]),
    });
    let error = k.infer(&[], &value, 0).unwrap_err();
    assert!(error.contains("generic subject"), "{error}");
}

#[test]
fn indexed_constructor_results_reject_unbound_variables_without_installing_the_family() {
    for fields in [vec![], vec![nat()]] {
        let mut k = Kernel::new();
        let invalid_index = var(fields.len());
        let error = k
            .indexed_inductive(
                "BadIndex",
                vec![],
                vec![],
                vec![nat()],
                level(1),
                vec![("make".into(), fields, vec![invalid_index])],
            )
            .unwrap_err();
        assert!(error.contains("unbound kernel variable"), "{error}");
        assert!(!k.contains("BadIndex"));
    }
}

#[test]
fn indexed_fieldless_families_do_not_gain_unit_conversion_or_neutral_computation() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "OnlyZero",
        vec![],
        vec![],
        vec![nat()],
        level(1),
        vec![("make".into(), vec![], vec![zero()])],
    )
    .unwrap();
    let ty = app(global("OnlyZero"), zero());
    let ctx = vec![ty.clone(), ty];
    assert!(!k.convertible(&ctx, &var(0), &var(1), 0).unwrap());
    let value = term(Term::Induct {
        family: "OnlyZero".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![zero()],
        motive: lam(nat(), lam(app(global("OnlyZero"), var(0)), nat())),
        branches: vec![zero()],
        subject: var(0),
    });
    k.check(&ctx, &value, &nat(), 0).unwrap();
    assert!(!k.convertible(&ctx, &value, &zero(), 0).unwrap());
}

#[test]
fn indexed_singleton_proof_computation_requires_convertible_constructor_indices() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "ZeroProof",
        vec![],
        vec![],
        vec![nat()],
        level(0),
        vec![("make".into(), vec![], vec![zero()])],
    )
    .unwrap();
    let family = |index| app(global("ZeroProof"), index);
    let motive = lam(nat(), lam(family(var(0)), nat()));
    let eliminate = |index, subject| {
        term(Term::Induct {
            family: "ZeroProof".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![index],
            motive: motive.clone(),
            branches: vec![zero()],
            subject,
        })
    };
    for (ctx, index, reduces) in [
        (vec![family(zero())], zero(), true),
        // These assumptions may be uninhabited; that cannot let conversion
        // silently rewrite an arbitrary index to the constructor's index.
        (vec![family(succ(zero()))], succ(zero()), false),
        (vec![nat(), family(var(0))], var(1), false),
    ] {
        k.reset_budget();
        let value = eliminate(index, var(0));
        k.check(&ctx, &value, &nat(), 0).unwrap();
        assert_eq!(k.convertible(&ctx, &value, &zero(), 0).unwrap(), reduces);
    }
    // Beta-convertible indices count too, including a dependent result type.
    let index = app(lam(nat(), var(0)), zero());
    let value = term(Term::Induct {
        family: "ZeroProof".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![index.clone()],
        motive: lam(
            nat(),
            lam(family(var(0)), pi(eq(nat(), var(1), zero()), nat())),
        ),
        branches: vec![lam(eq(nat(), zero(), zero()), zero())],
        subject: var(0),
    });
    let ctx = vec![family(index.clone())];
    k.reset_budget();
    k.check(&ctx, &value, &pi(eq(nat(), index, zero()), nat()), 0)
        .unwrap();
    assert!(k
        .convertible(&ctx, &value, &lam(eq(nat(), zero(), zero()), zero()), 0)
        .unwrap());
}

#[test]
fn indexed_singleton_proof_computation_specializes_parameters_and_universes_once() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "AtParameter",
        vec!["u".into(), "v".into()],
        vec![term(Term::Sort(Level::variable("v".into()))), var(0)],
        vec![var(1)],
        Level::variable("u".into()),
        vec![("make".into(), vec![], vec![var(0)])],
    )
    .unwrap();
    for source_level in [0, 1] {
        let levels = vec![level(source_level), level(1)];
        let family = apps(
            term(Term::Global("AtParameter".into(), levels.clone())),
            &[nat(), var(0), var(0)],
        );
        let ctx = vec![nat(), family];
        let motive_family = apps(
            term(Term::Global("AtParameter".into(), levels.clone())),
            &[nat(), var(2), var(0)],
        );
        let value = term(Term::Induct {
            family: "AtParameter".into(),
            levels,
            parameters: vec![nat(), var(1)],
            indices: vec![var(1)],
            motive: lam(nat(), lam(motive_family, nat())),
            branches: vec![zero()],
            subject: var(0),
        });
        k.reset_budget();
        k.check(&ctx, &value, &nat(), 0).unwrap();
        assert_eq!(
            k.convertible(&ctx, &value, &zero(), 0).unwrap(),
            source_level == 0
        );
        // Substituting the constructor for the subject preserves typing and
        // iota computation, including when the source is data-valued.
        let constructor = term(Term::Ctor {
            family: "AtParameter".into(),
            levels: vec![level(source_level), level(1)],
            parameters: vec![nat(), var(0)],
            constructor: "make".into(),
            fields: vec![],
        });
        let applied = k.instantiate(&value, &constructor, 0).unwrap();
        k.check(&[nat()], &applied, &nat(), 0).unwrap();
        assert!(k.convertible(&[nat()], &applied, &zero(), 0).unwrap());
        // An ill-typed substitution must still fail before that reduction.
        let invalid = k.instantiate(&value, &zero(), 0).unwrap();
        assert!(k.check(&[nat()], &invalid, &nat(), 0).is_err());
    }
}

#[test]
fn indexed_elimination_checks_dependent_index_domains_and_result_types() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "Dependent",
        vec![],
        vec![],
        vec![sort(1), var(0)],
        level(2),
        vec![("make".into(), vec![sort(1), var(0)], vec![var(1), var(0)])],
    )
    .unwrap();
    let family = apps(global("Dependent"), &[var(1), var(0)]);
    let motive = lam(sort(1), lam(var(0), lam(family, var(2))));
    let value = term(Term::Induct {
        family: "Dependent".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![nat(), zero()],
        motive,
        branches: vec![lam(sort(1), lam(var(0), var(0)))],
        subject: ctor("Dependent", vec![], "make", vec![nat(), zero()]),
    });
    k.check(&[], &value, &nat(), 0).unwrap();
    assert!(k.convertible(&[], &value, &zero(), 0).unwrap());
}

#[test]
fn indexed_recursive_ih_insertion_preserves_later_index_dependent_fields() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "TaggedCounter",
        vec![],
        vec![],
        vec![nat()],
        level(1),
        vec![
            ("zero".into(), vec![], vec![zero()]),
            (
                "step".into(),
                vec![
                    nat(),
                    term(Term::SelfAt(vec![var(0)])),
                    eq(nat(), var(1), var(1)),
                ],
                vec![succ(var(2))],
            ),
        ],
    )
    .unwrap();
    let base = ctor("TaggedCounter", vec![], "zero", vec![]);
    let subject = ctor(
        "TaggedCounter",
        vec![],
        "step",
        vec![zero(), base, refl(nat(), zero())],
    );
    // After the IH binder, n and child are shifted in the later proof field.
    let branch = lam(
        nat(),
        lam(
            app(global("TaggedCounter"), var(0)),
            lam(nat(), lam(eq(nat(), var(2), var(2)), succ(var(1)))),
        ),
    );
    let motive = lam(nat(), lam(app(global("TaggedCounter"), var(0)), nat()));
    let value = term(Term::Induct {
        family: "TaggedCounter".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![succ(zero())],
        motive,
        branches: vec![zero(), branch],
        subject,
    });
    k.check(&[], &value, &nat(), 0).unwrap();
    assert!(k.convertible(&[], &value, &succ(zero()), 0).unwrap());
}

#[test]
fn recursive_function_fields_create_typed_lambda_hypotheses_in_open_contexts() {
    let mut k = Kernel::new();
    k.inductive(
        "Fan",
        vec![],
        vec![],
        level(1),
        vec![
            ("leaf".into(), vec![]),
            ("node".into(), vec![pi(nat(), term(Term::SelfType))]),
        ],
    )
    .unwrap();
    let fan = global("Fan");
    let motive = lam(fan.clone(), nat());
    let (family, _) = k.family("Fan", &[], 0).unwrap();
    let branch_type = k
        .branch_type(&[], "Fan", &[], &[], &motive, &family.constructors[1], 0)
        .unwrap();
    let ctx = vec![branch_type];
    let children = lam(nat(), ctor("Fan", vec![], "leaf", vec![]));
    let value = term(Term::Induct {
        family: "Fan".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive,
        branches: vec![zero(), var(0)],
        subject: ctor("Fan", vec![], "node", vec![children]),
    });
    k.check(&ctx, &value, &nat(), 0).unwrap();
    let reduced = k.whnf(&ctx, &value, 0).unwrap();
    k.check(&ctx, &reduced, &nat(), 0).unwrap();
    let Term::App(_, ih) = reduced.as_ref() else {
        panic!("expected a pointwise IH argument")
    };
    k.check(&ctx, ih, &pi(nat(), nat()), 0).unwrap();
    assert!(matches!(ih.as_ref(), Term::Lam(..)));
    assert!(k
        .convertible(&ctx, &app(ih.clone(), zero()), &zero(), 0)
        .unwrap());
}

#[test]
fn indexed_function_hypotheses_use_the_argument_index_not_the_parent() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "Path",
        vec![],
        vec![],
        vec![nat()],
        level(1),
        vec![
            ("leaf".into(), vec![nat()], vec![var(0)]),
            (
                "node".into(),
                vec![nat(), pi(nat(), term(Term::SelfAt(vec![var(0)])))],
                vec![var(1)],
            ),
        ],
    )
    .unwrap();
    let motive = lam(nat(), lam(app(global("Path"), var(0)), nat()));
    let (family, _) = k.family("Path", &[], 0).unwrap();
    let branch_type = k
        .branch_type(&[], "Path", &[], &[], &motive, &family.constructors[1], 0)
        .unwrap();
    let ctx = vec![branch_type];
    let value = term(Term::Induct {
        family: "Path".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![succ(zero())],
        motive,
        branches: vec![lam(nat(), zero()), var(0)],
        subject: ctor(
            "Path",
            vec![],
            "node",
            vec![
                succ(zero()),
                lam(nat(), ctor("Path", vec![], "leaf", vec![var(0)])),
            ],
        ),
    });
    k.check(&ctx, &value, &nat(), 0).unwrap();
    let reduced = k.whnf(&ctx, &value, 0).unwrap();
    k.check(&ctx, &reduced, &nat(), 0).unwrap();
    let Term::App(_, ih) = reduced.as_ref() else {
        panic!("expected pointwise IH")
    };
    let Term::Lam(_, body) = ih.as_ref() else {
        panic!("expected lambda IH")
    };
    let Term::Induct { indices, .. } = body.as_ref() else {
        panic!("expected child recursor")
    };
    assert!(matches!(indices[0].as_ref(), Term::Var(0)));
}

#[test]
fn dependent_function_hypotheses_shift_later_fields_and_uniform_parameters() {
    let mut k = Kernel::new();
    let function_field = pi(nat(), pi(eq(nat(), var(0), var(1)), term(Term::SelfType)));
    k.inductive(
        "DependentFan",
        vec![],
        vec![sort(1)],
        level(1),
        vec![
            ("leaf".into(), vec![]),
            (
                "node".into(),
                vec![nat(), function_field, eq(nat(), var(1), var(1))],
            ),
        ],
    )
    .unwrap();
    let family_at = |a| app(global("DependentFan"), a);
    let ctx = vec![sort(1)];
    let params = vec![var(0)];
    let children = lam(
        nat(),
        lam(
            eq(nat(), var(0), zero()),
            ctor("DependentFan", vec![var(2)], "leaf", vec![]),
        ),
    );
    let function_ty = pi(nat(), pi(eq(nat(), var(0), var(1)), family_at(var(3))));
    let ih_ty = pi(nat(), pi(eq(nat(), var(0), var(2)), nat()));
    let branch = lam(
        nat(),
        lam(
            function_ty,
            lam(
                ih_ty,
                lam(
                    eq(nat(), var(2), var(2)),
                    succ(app(app(var(1), var(3)), refl(nat(), var(3)))),
                ),
            ),
        ),
    );
    let value = term(Term::Induct {
        family: "DependentFan".into(),
        levels: vec![],
        parameters: params.clone(),
        indices: vec![],
        motive: lam(family_at(var(0)), nat()),
        branches: vec![zero(), branch],
        subject: ctor(
            "DependentFan",
            params,
            "node",
            vec![zero(), children, refl(nat(), zero())],
        ),
    });
    k.check(&ctx, &value, &nat(), 0).unwrap();
    assert!(k.convertible(&ctx, &value, &succ(zero()), 0).unwrap());
}

#[test]
fn positive_recursive_let_wrappers_cannot_erase_bad_definitions() {
    let field = |value| term(Term::Let(nat(), value, pi(nat(), term(Term::SelfType))));
    let mut k = Kernel::new();
    k.inductive(
        "LetFan",
        vec![],
        vec![],
        level(1),
        vec![("node".into(), vec![field(zero())])],
    )
    .unwrap();
    let error = k
        .inductive(
            "BadLetFan",
            vec![],
            vec![],
            level(1),
            vec![("node".into(), vec![field(refl(nat(), zero()))])],
        )
        .unwrap_err();
    assert!(error.contains("type mismatch"), "{error}");
    assert!(!k.contains("BadLetFan"));
}

#[test]
fn large_elimination_recovery_does_not_confuse_parameters_with_fields() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "HiddenField",
        vec![],
        vec![nat()],
        vec![nat()],
        level(0),
        vec![("make".into(), vec![nat()], vec![var(1)])],
    )
    .unwrap();
    let (desc, _) = k.family("HiddenField", &[], 0).unwrap();
    assert!(
        !desc.large,
        "the index is the parameter, not the hidden field"
    );
    let value = term(Term::Induct {
        family: "HiddenField".into(),
        levels: vec![],
        parameters: vec![zero()],
        indices: vec![zero()],
        motive: lam(
            nat(),
            lam(app(app(global("HiddenField"), zero()), var(0)), nat()),
        ),
        branches: vec![lam(nat(), var(0))],
        subject: ctor("HiddenField", vec![zero()], "make", vec![succ(zero())]),
    });
    let error = k.infer(&[], &value, 0).unwrap_err();
    assert!(error.contains("large elimination"), "{error}");
}

#[test]
fn index_recoverable_accessibility_uses_constructor_fields_without_synthetic_ih_binders() {
    let mut k = Kernel::new();
    k.indexed_inductive(
        "Access",
        vec![],
        vec![],
        vec![nat()],
        level(0),
        vec![(
            "intro".into(),
            vec![
                nat(),
                pi(nat(), pi(falsity(), term(Term::SelfAt(vec![var(1)])))),
            ],
            vec![var(1)],
        )],
    )
    .unwrap();
    let (desc, _) = k.family("Access", &[], 0).unwrap();
    assert!(desc.large);
    let motive = lam(nat(), lam(app(global("Access"), var(0)), nat()));
    let branch = k
        .branch_type(&[], "Access", &[], &[], &motive, &desc.constructors[0], 0)
        .unwrap();
    // The branch has point, lower, and a data-valued pointwise IH. That IH
    // is not a hidden constructor field and must not affect recoverability.
    k.sort(&[], &branch, 0).unwrap();
    k.check(
        &[],
        &lam(
            nat(),
            lam(
                pi(nat(), pi(falsity(), app(global("Access"), var(1)))),
                lam(pi(nat(), pi(falsity(), nat())), var(2)),
            ),
        ),
        &branch,
        0,
    )
    .unwrap();
}

#[test]
fn maximal_malformed_variable_index_returns_error_instead_of_panicking() {
    let mut k = Kernel::new();
    // Public declaration checking reaches infer(Var), whose index+1 must be checked.
    assert!(k
        .definition("bad-index", vec![], nat(), var(usize::MAX), false)
        .is_err());
}

#[test]
fn failed_declarations_do_not_extend_the_environment() {
    let mut k = Kernel::new();
    assert!(k
        .inductive(
            "bad",
            vec![],
            vec![],
            level(1),
            vec![("roll".into(), vec![pi(global("bad"), falsity())])]
        )
        .is_err());
    assert!(!k.contains("bad"));
    k.inductive("bad", vec![], vec![], level(1), vec![("ok".into(), vec![])])
        .unwrap();
    assert!(k
        .definition(
            "free-level",
            vec![],
            term(Term::Sort(Level::variable("missing".into()))),
            nat(),
            false
        )
        .is_err());
    assert!(!k.contains("free-level"));
}

#[test]
fn universe_ordering_never_accepts_a_false_concrete_inequality() {
    let u = Level::variable("u".into());
    let v = Level::variable("v".into());
    let mut levels = vec![level(0), level(1), level(3), u.clone(), v.clone()];
    levels.extend([
        u.successor().unwrap(),
        v.successor().unwrap(),
        u.maximum(&v).unwrap(),
        u.maximum(&level(2)).unwrap(),
        u.maximum(&v.successor().unwrap()).unwrap(),
    ]);
    for a in &levels {
        for b in &levels {
            if a.at_most(b).unwrap() {
                for x in 0..6 {
                    for y in 0..6 {
                        let map = HashMap::from([("u".into(), level(x)), ("v".into(), level(y))]);
                        let lhs = a.substitute(&map).unwrap().numeral().unwrap();
                        let rhs = b.substitute(&map).unwrap().numeral().unwrap();
                        assert!(lhs <= rhs, "{a:?} <= {b:?}, u={x}, v={y}");
                    }
                }
            }
        }
    }
}
