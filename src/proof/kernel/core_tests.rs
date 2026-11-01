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
fn equality_motive_constant_loop_binder_must_not_admit_axiom_k() {
    let mut k = Kernel::new();
    // At the elimination site: A=#2, a=#1, p=#0 : Eq(A,a,a).
    // Invalid J motive: lambda y:A. lambda q:Eq(A,a,a). Eq(Eq(A,a,a),refl,q).
    // The equality domain is constant in y; checking it only at y=a admits K.
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
fn proof_irrelevance_preserves_data_distinctions_without_eta_or_cumulativity() {
    let mut k = Kernel::new();
    assert!(k.check(&[], &sort(0), &sort(2), 0).is_err());
    let function = pi(nat(), nat());
    let ctx = vec![function];
    let eta = lam(nat(), app(var(1), var(0)));
    k.infer(&ctx, &eta, 0).unwrap();
    assert!(!k.convertible(&ctx, &var(0), &eta, 0).unwrap());
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
fn opaque_fieldless_singleton_proofs_have_the_constructor_computation_rule() {
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
        motive: lam(global("DataUnit"), nat()),
        branches: vec![zero()],
        subject: var(0),
    });
    k.check(&data_context, &data_value, &nat(), 0).unwrap();
    assert!(!k
        .convertible(&data_context, &data_value, &zero(), 0)
        .unwrap());
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
