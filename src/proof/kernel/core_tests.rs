//! Kernel-only regressions. Register inside core.rs with:
//! #[cfg(test)] #[path = "core_tests.rs"] mod core_tests;
//! These tests intentionally require rejection of the audit counterexamples.
use super::*;

fn level(n: u32) -> Level {
    Level::number(n).unwrap()
}

#[test]
fn shared_export_terms_cannot_expand_past_the_transformation_allocation_budget() {
    let mut k = Kernel::new();
    let name = "Tree".repeat(512);
    k.inductive(
        &name,
        vec![],
        vec![],
        level(1),
        vec![
            ("leaf".into(), vec![]),
            (
                "node".into(),
                vec![term(Term::SelfType), term(Term::SelfType)],
            ),
        ],
    )
    .unwrap();
    let leaf = ctor(&name, vec![], "leaf", vec![]);
    let mut tree = leaf.clone();
    for _ in 0..16 {
        tree = ctor(&name, vec![], "node", vec![tree.clone(), tree]);
    }
    k.reset_budget();
    let error = k
        .definition("oversized-tree", vec![], global(&name), tree, false)
        .unwrap_err();
    assert!(error.contains("allocation limit"), "{error}");
    assert!(!k.contains("oversized-tree"));
    k.reset_budget();
    k.definition("small-tree", vec![], global(&name), leaf, false)
        .unwrap();
}

fn mutual_input(
    name: &str,
    indices: Vec<T>,
    sort: Level,
    constructors: Vec<(String, Vec<T>, Vec<T>)>,
) -> InductiveInput {
    InductiveInput {
        name: name.into(),
        universes: vec![],
        parameters: vec![],
        indices,
        sort,
        constructors,
    }
}
fn recur(name: &str, indices: Vec<T>) -> T {
    term(Term::Recur(name.into(), indices))
}
fn mutual_fold(family: &str, indices: Vec<T>, cases: Vec<RecursionCase>, subject: T) -> T {
    term(Term::MutualInduct {
        family: family.into(),
        levels: vec![],
        parameters: vec![],
        indices,
        cases,
        subject,
    })
}

#[test]
fn mutual_groups_roll_back_every_member_on_cross_family_negative_occurrences() {
    let mut k = Kernel::new();
    k.inductive(
        "Kept",
        vec![],
        vec![],
        level(1),
        vec![("make".into(), vec![])],
    )
    .unwrap();
    let error = k
        .mutual_inductive(vec![
            mutual_input(
                "Left",
                vec![],
                level(1),
                vec![("make".into(), vec![recur("Right", vec![])], vec![])],
            ),
            mutual_input(
                "Right",
                vec![],
                level(1),
                vec![("bad".into(), vec![pi(global("Left"), falsity())], vec![])],
            ),
        ])
        .unwrap_err();
    assert_eq!(error.0, "Right");
    assert!(error.1.contains("strict positivity"), "{error:?}");
    assert!(!k.contains("Left") && !k.contains("Right"));
    assert!(k.contains("Kept"));
    // The failed provisional names can be reused, with no leftover metadata.
    k.reset_budget();
    k.mutual_inductive(vec![
        mutual_input(
            "Left",
            vec![],
            level(1),
            vec![("make".into(), vec![], vec![])],
        ),
        mutual_input(
            "Right",
            vec![],
            level(1),
            vec![("make".into(), vec![], vec![])],
        ),
    ])
    .unwrap();
}

#[test]
fn mutual_function_children_compute_with_the_sibling_index_and_motive() {
    let mut k = Kernel::new();
    k.mutual_inductive(vec![
        mutual_input(
            "Parent",
            vec![nat()],
            level(1),
            vec![(
                "make".into(),
                vec![pi(nat(), recur("Child", vec![var(0)]))],
                vec![zero()],
            )],
        ),
        mutual_input(
            "Child",
            vec![nat()],
            level(1),
            vec![("leaf".into(), vec![nat()], vec![var(0)])],
        ),
    ])
    .unwrap();
    let parent_motive = lam(nat(), lam(app(global("Parent"), var(0)), nat()));
    let child_motive = lam(nat(), lam(app(global("Child"), var(0)), nat()));
    let children_type = pi(nat(), app(global("Child"), var(0)));
    let cases = vec![
        RecursionCase {
            family: "Parent".into(),
            motive: parent_motive,
            branches: vec![lam(
                children_type,
                lam(pi(nat(), nat()), app(var(0), succ(zero()))),
            )],
        },
        RecursionCase {
            family: "Child".into(),
            motive: child_motive,
            branches: vec![lam(nat(), var(0))],
        },
    ];
    let children = lam(nat(), ctor("Child", vec![], "leaf", vec![var(0)]));
    let fold = mutual_fold(
        "Parent",
        vec![zero()],
        cases.clone(),
        ctor("Parent", vec![], "make", vec![children]),
    );
    k.check(&[], &fold, &nat(), 0).unwrap();
    assert!(k.convertible(&[], &fold, &succ(zero()), 0).unwrap());
    // A branch using the parent's motive for Child would accept the wrong
    // generic subject type. The independently checked sibling motive rejects it.
    let mut forged = cases;
    forged[1].motive = forged[0].motive.clone();
    let invalid = mutual_fold(
        "Parent",
        vec![zero()],
        forged,
        ctor(
            "Parent",
            vec![],
            "make",
            vec![lam(nat(), ctor("Child", vec![], "leaf", vec![var(0)]))],
        ),
    );
    k.reset_budget();
    assert!(k
        .infer(&[], &invalid, 0)
        .unwrap_err()
        .contains("generic subject"));
}

#[test]
fn mutual_elimination_validates_unused_sibling_motives_and_prop_guards() {
    let mut k = Kernel::new();
    k.mutual_inductive(vec![
        mutual_input("P", vec![], level(0), vec![("make".into(), vec![], vec![])]),
        mutual_input("Q", vec![], level(0), vec![("make".into(), vec![], vec![])]),
    ])
    .unwrap();
    let equality = eq(nat(), zero(), zero());
    let cases = vec![
        RecursionCase {
            family: "P".into(),
            motive: lam(global("P"), equality),
            branches: vec![refl(nat(), zero())],
        },
        RecursionCase {
            family: "Q".into(),
            motive: lam(global("Q"), nat()),
            branches: vec![zero()],
        },
    ];
    let invalid = mutual_fold("P", vec![], cases, ctor("P", vec![], "make", vec![]));
    let error = k.infer(&[], &invalid, 0).unwrap_err();
    assert!(error.contains("large elimination"), "{error}");
    // An impossible mutual group with no constructors cannot silently prove
    // False: elimination still needs a well-typed major premise.
    k.reset_budget();
    k.mutual_inductive(vec![
        mutual_input("EmptyA", vec![], level(0), vec![]),
        mutual_input("EmptyB", vec![], level(0), vec![]),
    ])
    .unwrap();
    let cases = vec![
        RecursionCase {
            family: "EmptyA".into(),
            motive: lam(global("EmptyA"), falsity()),
            branches: vec![],
        },
        RecursionCase {
            family: "EmptyB".into(),
            motive: lam(global("EmptyB"), falsity()),
            branches: vec![],
        },
    ];
    let attack = mutual_fold("EmptyA", vec![], cases, zero());
    assert!(k
        .definition("absurd-mutual", vec![], falsity(), attack, true)
        .is_err());
}

#[test]
fn mutual_dependent_indices_specialize_shared_parameters_and_swapped_universes_once() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let v = Level::variable("v".into());
    let source = u.successor().unwrap();
    let input = |name: &str, indices, constructors| InductiveInput {
        name: name.into(),
        universes: vec!["u".into(), "v".into()],
        parameters: vec![term(Term::Sort(u.clone()))],
        indices,
        sort: source.clone(),
        constructors,
    };
    k.mutual_inductive(vec![
        input(
            "IndexedA",
            vec![nat()],
            vec![(
                "make".into(),
                vec![var(0), recur("IndexedB", vec![var(0)])],
                vec![zero()],
            )],
        ),
        input(
            "IndexedB",
            vec![var(0)],
            vec![("leaf".into(), vec![var(0)], vec![var(0)])],
        ),
    ])
    .unwrap();
    let levels = vec![v.clone(), u.clone()];
    let family = |name: &str, params: &[T], indices: &[T]| {
        apps(
            apps(term(Term::Global(name.into(), levels.clone())), params),
            indices,
        )
    };
    let cases = vec![
        RecursionCase {
            family: "IndexedA".into(),
            motive: lam(nat(), lam(family("IndexedA", &[var(2)], &[var(0)]), nat())),
            branches: vec![lam(
                var(1),
                lam(family("IndexedB", &[var(2)], &[var(0)]), lam(nat(), var(0))),
            )],
        },
        RecursionCase {
            family: "IndexedB".into(),
            motive: lam(var(1), lam(family("IndexedB", &[var(2)], &[var(0)]), nat())),
            branches: vec![lam(var(1), zero())],
        },
    ];
    let child = term(Term::Ctor {
        family: "IndexedB".into(),
        levels: levels.clone(),
        parameters: vec![var(1)],
        constructor: "leaf".into(),
        fields: vec![var(0)],
    });
    let subject = term(Term::Ctor {
        family: "IndexedA".into(),
        levels: levels.clone(),
        parameters: vec![var(1)],
        constructor: "make".into(),
        fields: vec![var(0), child],
    });
    let fold = term(Term::MutualInduct {
        family: "IndexedA".into(),
        levels,
        parameters: vec![var(1)],
        indices: vec![zero()],
        cases,
        subject,
    });
    let ctx = vec![term(Term::Sort(v.clone())), var(0)];
    k.check(&ctx, &fold, &nat(), 0).unwrap();
    assert!(k.convertible(&ctx, &fold, &zero(), 0).unwrap());
    k.reset_budget();
    k.definition(
        "swapped-mutual",
        vec!["u".into(), "v".into()],
        pi(term(Term::Sort(v.clone())), pi(var(0), nat())),
        lam(term(Term::Sort(v)), lam(var(0), fold)),
        false,
    )
    .unwrap();
}

#[test]
fn mutual_groups_reject_changed_uniform_parameters_without_leaving_stubs() {
    let mut k = Kernel::new();
    let input = |name: &str, fields| InductiveInput {
        name: name.into(),
        universes: vec![],
        parameters: vec![sort(1)],
        indices: vec![],
        sort: level(1),
        constructors: vec![("make".into(), fields, vec![])],
    };
    let changed = app(global("UniformB"), nat());
    let error = k
        .mutual_inductive(vec![
            input("UniformA", vec![changed]),
            input("UniformB", vec![]),
        ])
        .unwrap_err();
    assert!(error.1.contains("uniform"), "{error:?}");
    assert!(!k.contains("UniformA") && !k.contains("UniformB"));
    k.reset_budget();
    // An unequal header cannot leave even the first family installed.
    let a = input("UniformA", vec![]);
    let mut b = input("UniformB", vec![]);
    b.parameters = vec![sort(2)];
    let error = k.mutual_inductive(vec![a, b]).unwrap_err();
    assert_eq!(error.0, "UniformB");
    assert!(error.1.contains("uniform parameter"), "{error:?}");
    assert!(!k.contains("UniformA") && !k.contains("UniformB"));
}

#[test]
fn mutual_sort_polymorphic_predicates_keep_correlated_elimination_guards() {
    let mut k = Kernel::new();
    let u = Level::variable("u".into());
    let input = |name: &str| InductiveInput {
        name: name.into(),
        universes: vec!["u".into()],
        parameters: vec![term(Term::Sort(u.clone()))],
        indices: vec![],
        sort: u.clone(),
        constructors: vec![("make".into(), vec![], vec![])],
    };
    k.mutual_inductive(vec![input("CorrelatedA"), input("CorrelatedB")])
        .unwrap();
    let family =
        |name: &str, parameter| app(term(Term::Global(name.into(), vec![u.clone()])), parameter);
    let cases = vec![
        RecursionCase {
            family: "CorrelatedA".into(),
            motive: lam(family("CorrelatedA", var(1)), var(2)),
            branches: vec![var(0)],
        },
        RecursionCase {
            family: "CorrelatedB".into(),
            motive: lam(family("CorrelatedB", var(1)), var(2)),
            branches: vec![var(0)],
        },
    ];
    let subject = term(Term::Ctor {
        family: "CorrelatedA".into(),
        levels: vec![u.clone()],
        parameters: vec![var(1)],
        constructor: "make".into(),
        fields: vec![],
    });
    let fold = term(Term::MutualInduct {
        family: "CorrelatedA".into(),
        levels: vec![u.clone()],
        parameters: vec![var(1)],
        indices: vec![],
        cases,
        subject,
    });
    let ctx = vec![term(Term::Sort(u)), var(0)];
    k.check(&ctx, &fold, &var(1), 0).unwrap();
    assert!(k.convertible(&ctx, &fold, &var(0), 0).unwrap());
}
#[test]
fn mutual_ih_insertion_preserves_later_index_dependent_fields() {
    let mut k = Kernel::new();
    k.mutual_inductive(vec![
        mutual_input(
            "LaterA",
            vec![],
            level(1),
            vec![(
                "make".into(),
                vec![
                    nat(),
                    recur("LaterB", vec![var(0)]),
                    eq(nat(), var(1), var(1)),
                ],
                vec![],
            )],
        ),
        mutual_input(
            "LaterB",
            vec![nat()],
            level(1),
            vec![("leaf".into(), vec![nat()], vec![var(0)])],
        ),
    ])
    .unwrap();
    let cases = vec![
        RecursionCase {
            family: "LaterA".into(),
            motive: lam(global("LaterA"), nat()),
            branches: vec![lam(
                nat(),
                lam(
                    app(global("LaterB"), var(0)),
                    lam(nat(), lam(eq(nat(), var(2), var(2)), var(1))),
                ),
            )],
        },
        RecursionCase {
            family: "LaterB".into(),
            motive: lam(nat(), lam(app(global("LaterB"), var(0)), nat())),
            branches: vec![lam(nat(), var(0))],
        },
    ];
    let ctx = vec![
        nat(),
        app(global("LaterB"), var(0)),
        eq(nat(), var(1), var(1)),
    ];
    let fold = mutual_fold(
        "LaterA",
        vec![],
        cases.clone(),
        ctor("LaterA", vec![], "make", vec![var(2), var(1), var(0)]),
    );
    k.check(&ctx, &fold, &nat(), 0).unwrap();
    let reduced = k.whnf(&ctx, &fold, 0).unwrap();
    k.check(&ctx, &reduced, &nat(), 0).unwrap();
    let expected = mutual_fold("LaterB", vec![var(2)], cases, var(1));
    assert!(k.convertible(&ctx, &reduced, &expected, 0).unwrap());
}

#[test]
fn mutual_families_do_not_bypass_the_remaining_nested_occurrence_restriction() {
    let mut k = Kernel::new();
    let error = k
        .mutual_inductive(vec![
            mutual_input(
                "NestedA",
                vec![],
                level(1),
                vec![(
                    "make".into(),
                    vec![
                        recur("NestedB", vec![]),
                        eq(global("NestedB"), var(0), var(0)),
                    ],
                    vec![],
                )],
            ),
            mutual_input(
                "NestedB",
                vec![],
                level(1),
                vec![("leaf".into(), vec![], vec![])],
            ),
        ])
        .unwrap_err();
    assert!(error.1.contains("strict positivity"), "{error:?}");
    assert!(!k.contains("NestedA") && !k.contains("NestedB"));
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

fn project(family: &str, index: usize, subject: T) -> T {
    term(Term::Project {
        family: family.into(),
        index,
        subject,
    })
}

#[test]
fn record_projection_instantiates_dependent_fields_and_preserves_substitution() {
    let mut k = Kernel::new();
    k.inductive(
        "Package",
        vec![],
        vec![],
        level(2),
        vec![("pack".into(), vec![sort(1), var(0)])],
    )
    .unwrap();
    let ctx = vec![global("Package")];
    let first = project("Package", 0, var(0));
    let second = project("Package", 1, var(0));
    k.check(&ctx, &first, &sort(1), 0).unwrap();
    k.check(&ctx, &second, &first, 0).unwrap();
    let value = ctor("Package", vec![], "pack", vec![nat(), zero()]);
    let substituted = k.instantiate(&second, &value, 0).unwrap();
    k.check(&[], &substituted, &nat(), 0).unwrap();
    assert!(k.convertible(&[], &substituted, &zero(), 0).unwrap());
    let rebuilt = ctor("Package", vec![], "pack", vec![first, second]);
    assert!(k.convertible(&ctx, &var(0), &rebuilt, 0).unwrap());
    assert!(k.convertible(&ctx, &rebuilt, &var(0), 0).unwrap());
}

#[test]
fn neutral_record_eta_and_induction_respect_proof_fields_without_collapsing_data() {
    let mut k = Kernel::new();
    k.inductive(
        "Evidence",
        vec![],
        vec![sort(0)],
        level(1),
        vec![("pack".into(), vec![var(0)])],
    )
    .unwrap();
    let family = app(global("Evidence"), var(0));
    let ctx = vec![sort(0), family.clone(), k.shift(&family, 1, 0, 0).unwrap()];
    assert!(k.convertible(&ctx, &var(0), &var(1), 0).unwrap());
    k.reset_budget();
    k.inductive(
        "Number",
        vec![],
        vec![],
        level(1),
        vec![("pack".into(), vec![nat()])],
    )
    .unwrap();
    let ctx = vec![global("Number"), global("Number")];
    assert!(!k.convertible(&ctx, &var(0), &var(1), 0).unwrap());
    let value = term(Term::Induct {
        family: "Number".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global("Number"), nat()),
        branches: vec![lam(nat(), var(0))],
        subject: var(0),
    });
    k.check(&ctx, &value, &nat(), 0).unwrap();
    assert!(k
        .convertible(&ctx, &value, &project("Number", 0, var(0)), 0)
        .unwrap());
    // Rigid subjects must stop repeated eta on neutral data projections.
    assert!(!k
        .convertible(
            &ctx,
            &project("Number", 0, var(0)),
            &project("Number", 0, var(1)),
            0
        )
        .unwrap());
}

#[test]
fn proof_record_projection_cannot_hide_data_in_a_later_dependent_type() {
    let mut k = Kernel::new();
    k.inductive(
        "ExistsNat",
        vec![],
        vec![],
        level(0),
        vec![("pack".into(), vec![nat(), eq(nat(), var(0), var(0))])],
    )
    .unwrap();
    let ctx = vec![global("ExistsNat")];
    for index in [0, 1] {
        let error = k
            .infer(&ctx, &project("ExistsNat", index, var(0)), 0)
            .unwrap_err();
        assert!(error.contains("cannot extract data"), "{error}");
    }
    k.reset_budget();
    // A completely independent proof can be projected without making the
    // hidden witness a valid intermediate projection.
    let equality = eq(nat(), zero(), zero());
    k.inductive(
        "Independent",
        vec![],
        vec![],
        level(0),
        vec![("pack".into(), vec![nat(), equality.clone()])],
    )
    .unwrap();
    k.check(
        &[global("Independent")],
        &project("Independent", 1, var(0)),
        &equality,
        0,
    )
    .unwrap();
    // Source propositions cannot leak proposition TYPES either.
    k.inductive(
        "HiddenProp",
        vec![],
        vec![],
        level(0),
        vec![("pack".into(), vec![sort(0)])],
    )
    .unwrap();
    let error = k
        .infer(
            &[global("HiddenProp")],
            &project("HiddenProp", 0, var(0)),
            0,
        )
        .unwrap_err();
    assert!(error.contains("cannot extract data"), "{error}");
}

#[test]
fn record_projection_guards_specialized_sorts_and_rejects_invalid_ordinals() {
    let mut k = Kernel::new();
    k.inductive(
        "MaybeProp",
        vec!["u".into()],
        vec![],
        Level::variable("u".into()),
        vec![("pack".into(), vec![nat()])],
    )
    .unwrap();
    for (universe, allowed) in [
        (level(0), false),
        (level(1), true),
        (Level::variable("v".into()), false),
    ] {
        k.reset_budget();
        let ty = term(Term::Global("MaybeProp".into(), vec![universe.clone()]));
        let ctx = vec![ty.clone()];
        let value = project("MaybeProp", 0, var(0));
        let inferred = k.infer(&ctx, &value, 0);
        if allowed {
            k.check(&ctx, &value, &nat(), 0).unwrap();
            // Although the generic family disallows large elimination at
            // Prop, its positive specialization has legal eta projections.
            let fold = term(Term::Induct {
                family: "MaybeProp".into(),
                levels: vec![universe],
                parameters: vec![],
                indices: vec![],
                motive: lam(ty, nat()),
                branches: vec![lam(nat(), var(0))],
                subject: var(0),
            });
            k.check(&ctx, &fold, &nat(), 0).unwrap();
            assert!(k.convertible(&ctx, &fold, &value, 0).unwrap());
        } else {
            assert!(inferred.unwrap_err().contains("cannot extract data"));
        }
    }
    let ty = term(Term::Global("MaybeProp".into(), vec![level(1)]));
    for index in [1, usize::MAX] {
        let error = k
            .infer(&[ty.clone()], &project("MaybeProp", index, var(0)), 0)
            .unwrap_err();
        assert!(error.contains("out of range"), "{error}");
    }
}

#[test]
fn record_eta_preserves_nominal_families_and_parameter_identity() {
    let mut k = Kernel::new();
    for name in ["TaggedA", "TaggedB"] {
        k.inductive(
            name,
            vec![],
            vec![nat()],
            level(1),
            vec![("pack".into(), vec![nat()])],
        )
        .unwrap();
    }
    let left = app(global("TaggedA"), zero());
    for right in [
        app(global("TaggedB"), zero()),
        app(global("TaggedA"), succ(zero())),
    ] {
        k.reset_budget();
        let ctx = vec![left.clone(), right];
        assert!(!k.convertible(&ctx, &var(0), &var(1), 0).unwrap());
    }
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

#[test]
fn checked_monomorphic_unfolding_shares_immutable_bodies_without_copying_graphs() {
    let mut kernel = Kernel::new();
    let body = lam(nat(), var(0));
    let ty = pi(nat(), nat());
    kernel
        .definition("identity", vec![], ty.clone(), body.clone(), false)
        .unwrap();
    kernel.reset_budget();
    let reduced = kernel.whnf(&[], &global("identity"), 0).unwrap();
    assert!(Arc::ptr_eq(&reduced, &body));
    assert_eq!(kernel.transformed_bytes, 0);
    let head = kernel.natural_head(&global("identity"), 0).unwrap();
    assert!(Arc::ptr_eq(&head, &body));
    assert_eq!(kernel.transformed_bytes, 0);
    kernel.check(&[], &head, &ty, 0).unwrap();
    assert!(kernel
        .convertible(
            &[],
            &app(
                global("identity"),
                term(Term::NatLiteral {
                    family: "#pt-nat".into(),
                    value: Natural::parse("4096").unwrap(),
                })
            ),
            &term(Term::NatLiteral {
                family: "#pt-nat".into(),
                value: Natural::parse("4096").unwrap()
            }),
            0
        )
        .unwrap());
}

#[test]
fn polymorphic_unfolding_still_substitutes_each_explicit_universe_without_mutation() {
    let mut kernel = Kernel::new();
    let universe = term(Term::Sort(Level::variable("u".into())));
    let body = lam(universe.clone(), lam(var(0), var(0)));
    kernel
        .definition(
            "polymorphic",
            vec!["u".into()],
            pi(universe, pi(var(0), var(1))),
            body.clone(),
            false,
        )
        .unwrap();
    for n in [0, 2, 1, 0] {
        kernel.reset_budget();
        let value = term(Term::Global("polymorphic".into(), vec![level(n)]));
        let reduced = kernel.whnf(&[], &value, 0).unwrap();
        assert!(!Arc::ptr_eq(&reduced, &body));
        let Term::Lam(domain, _) = reduced.as_ref() else {
            panic!("expected identity lambda");
        };
        assert!(
            matches!(domain.as_ref(), Term::Sort(actual) if actual.equivalent(&level(n)).unwrap())
        );
        kernel
            .check(&[], &reduced, &pi(sort(n), pi(var(0), var(1))), 0)
            .unwrap();
    }
    let Term::Lam(domain, _) = body.as_ref() else {
        panic!("expected source identity");
    };
    assert!(
        matches!(domain.as_ref(), Term::Sort(actual) if actual.equivalent(&Level::variable("u".into())).unwrap())
    );
}

#[test]
fn monomorphic_body_reuse_does_not_skip_scope_arity_or_opacity_checks() {
    let mut kernel = Kernel::new();
    let invalid = term(Term::Let(
        sort(0),
        term(Term::Sort(Level::variable("undeclared".into()))),
        term(Term::NatLiteral {
            family: "#pt-nat".into(),
            value: Natural::parse("0").unwrap(),
        }),
    ));
    let why = kernel
        .definition("bad", vec![], nat(), invalid, false)
        .unwrap_err();
    assert!(why.contains("universe"), "{why}");
    assert!(!kernel.contains("bad"));
    let ty = pi(nat(), nat());
    let body = lam(nat(), var(0));
    kernel
        .definition("visible", vec![], ty.clone(), body.clone(), false)
        .unwrap();
    let wrong = term(Term::Global("visible".into(), vec![level(1)]));
    assert!(kernel
        .whnf(&[], &wrong, 0)
        .unwrap_err()
        .contains("requires 0 explicit universe"));
    assert!(kernel
        .natural_head(&wrong, 0)
        .unwrap_err()
        .contains("requires 0 explicit universe"));
    kernel
        .opaque_definition("secret", vec![], ty, body)
        .unwrap();
    for value in [
        kernel.whnf(&[], &global("secret"), 0).unwrap(),
        kernel.natural_head(&global("secret"), 0).unwrap(),
    ] {
        assert!(
            matches!(value.as_ref(), Term::Global(name, levels) if name == "secret" && levels.is_empty())
        );
    }
}
