use super::*;
fn g(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn v(index: usize) -> T {
    term(Term::Var(index))
}
fn sort(level: u32) -> T {
    term(Term::Sort(Level::number(level).unwrap()))
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
fn succ(value: T) -> T {
    ctor("#pt-nat", vec![], "succ", vec![value])
}
fn nat() -> T {
    g("#pt-nat")
}
fn sequence() -> Kernel {
    let mut kernel = Kernel::new();
    kernel.enable_nested_replay();
    kernel
        .inductive(
            "Seq",
            vec![],
            vec![sort(1)],
            Level::number(1).unwrap(),
            vec![
                ("nil".into(), vec![]),
                ("cons".into(), vec![v(0), term(Term::SelfType)]),
            ],
        )
        .unwrap();
    kernel.reset_budget();
    kernel
}
fn tree(kernel: &mut Kernel, name: &str, fields: Vec<T>) -> Result<()> {
    kernel.inductive(
        name,
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("leaf".into(), vec![]), ("node".into(), fields)],
    )
}

#[test]
fn nested_views_are_scoped_and_repeated_specializations_share_one_case() {
    let mut kernel = sequence();
    let field = app(g("Seq"), g("Tree"));
    tree(&mut kernel, "Tree", vec![field.clone(), field]).unwrap();
    let (family, _) = kernel.family("Tree", &[], 0).unwrap();
    assert_eq!(family.group.len(), 2);
    assert_eq!(
        family.constructors[1].recursive,
        vec![Some(family.group[1].clone()), Some(family.group[1].clone())]
    );
    assert_eq!(kernel.family("Seq", &[], 0).unwrap().0.group, vec!["Seq"]);
    assert!(kernel
        .infer(&[], &g(&family.group[1]), 0)
        .unwrap_err()
        .contains("not a global"));
    assert!(kernel
        .infer(&[], &ctor(&family.group[1], vec![], "nil", vec![]), 0)
        .unwrap_err()
        .contains("original constructors"));
}

#[test]
fn nested_recursion_computes_with_the_parent_and_container_hypotheses() {
    let mut kernel = sequence();
    tree(&mut kernel, "Tree", vec![app(g("Seq"), g("Tree"))]).unwrap();
    kernel.reset_budget();
    kernel
        .definition(
            "plus",
            vec![],
            pi(nat(), pi(nat(), nat())),
            lam(
                nat(),
                lam(
                    nat(),
                    term(Term::Induct {
                        family: "#pt-nat".into(),
                        levels: vec![],
                        parameters: vec![],
                        indices: vec![],
                        motive: lam(nat(), nat()),
                        branches: vec![v(1), lam(nat(), lam(nat(), succ(v(0))))],
                        subject: v(0),
                    }),
                ),
            ),
            false,
        )
        .unwrap();
    let seq_type = app(g("Seq"), g("Tree"));
    let nil = || ctor("Seq", vec![g("Tree")], "nil", vec![]);
    let leaf = || ctor("Tree", vec![], "leaf", vec![]);
    let empty_node = ctor("Tree", vec![], "node", vec![nil()]);
    let rest = ctor("Seq", vec![g("Tree")], "cons", vec![empty_node, nil()]);
    let list = ctor("Seq", vec![g("Tree")], "cons", vec![leaf(), rest]);
    let subject = ctor("Tree", vec![], "node", vec![list]);
    let group = kernel.family("Tree", &[], 0).unwrap().0.group;
    let cases = vec![
        RecursionCase {
            family: "Tree".into(),
            motive: lam(g("Tree"), nat()),
            branches: vec![succ(zero()), lam(seq_type.clone(), lam(nat(), succ(v(0))))],
        },
        RecursionCase {
            family: group[1].clone(),
            motive: lam(seq_type.clone(), nat()),
            branches: vec![
                zero(),
                lam(
                    g("Tree"),
                    lam(
                        nat(),
                        lam(seq_type, lam(nat(), app(app(g("plus"), v(2)), v(0)))),
                    ),
                ),
            ],
        },
    ];
    let value = term(Term::MutualInduct {
        family: "Tree".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        cases,
        subject,
    });
    kernel.reset_budget();
    kernel.check(&[], &value, &nat(), 0).unwrap();
    kernel.reset_budget();
    assert!(kernel
        .convertible(&[], &value, &succ(succ(succ(zero()))), 0)
        .unwrap());
}

#[test]
fn transitive_nested_containers_form_a_finite_group() {
    let mut kernel = sequence();
    tree(
        &mut kernel,
        "Deep",
        vec![app(g("Seq"), app(g("Seq"), g("Deep")))],
    )
    .unwrap();
    let group = kernel.family("Deep", &[], 0).unwrap().0.group;
    assert_eq!(group.len(), 3);
    let outer = kernel.family(&group[1], &[], 0).unwrap().0;
    let inner = kernel.family(&group[2], &[], 0).unwrap().0;
    assert_eq!(
        outer.constructors[1].recursive,
        vec![Some(group[2].clone()), Some(group[1].clone())]
    );
    assert_eq!(
        inner.constructors[1].recursive,
        vec![Some("Deep".into()), Some(group[2].clone())]
    );
}

#[test]
fn contravariant_containers_fail_without_leaving_auxiliary_signatures() {
    let mut kernel = Kernel::new();
    kernel.enable_nested_replay();
    kernel
        .inductive(
            "Consumer",
            vec![],
            vec![sort(1)],
            Level::number(1).unwrap(),
            vec![("make".into(), vec![pi(v(0), nat())])],
        )
        .unwrap();
    kernel.reset_budget();
    let error = tree(&mut kernel, "Bad", vec![app(g("Consumer"), g("Bad"))]).unwrap_err();
    assert!(error.contains("strict positivity"), "{error}");
    assert!(!kernel.contains("Bad"));
    assert!(kernel.nested.is_empty());
    assert!(kernel.nested_build.is_none());
    assert!(kernel.contains("Consumer"));
}

#[test]
fn constructor_local_capture_and_changed_uniform_parameters_are_rejected() {
    let mut kernel = sequence();
    kernel
        .inductive(
            "Witness",
            vec![],
            vec![sort(1), v(0)],
            Level::number(1).unwrap(),
            vec![("make".into(), vec![])],
        )
        .unwrap();
    kernel.reset_budget();
    let error = tree(
        &mut kernel,
        "Captured",
        vec![g("Captured"), app(app(g("Witness"), g("Captured")), v(0))],
    )
    .unwrap_err();
    assert!(error.contains("constructor-local"), "{error}");
    assert!(kernel.nested.is_empty());
    assert!(!kernel.contains("Captured"));
    kernel.reset_budget();
    let error = kernel
        .inductive(
            "Changed",
            vec![],
            vec![sort(1)],
            Level::number(1).unwrap(),
            vec![("make".into(), vec![app(g("Seq"), app(g("Changed"), nat()))])],
        )
        .unwrap_err();
    assert!(error.contains("uniform"), "{error}");
    assert!(kernel.nested.is_empty());
    assert!(!kernel.contains("Changed"));
}

#[test]
fn nested_mutual_propositions_cannot_eliminate_into_data() {
    let mut kernel = Kernel::new();
    kernel.enable_nested_replay();
    kernel
        .inductive(
            "ProofBox",
            vec![],
            vec![sort(0)],
            Level::number(0).unwrap(),
            vec![("pack".into(), vec![v(0)])],
        )
        .unwrap();
    kernel.reset_budget();
    kernel
        .inductive(
            "Predicate",
            vec![],
            vec![],
            Level::number(0).unwrap(),
            vec![("roll".into(), vec![app(g("ProofBox"), g("Predicate"))])],
        )
        .unwrap();
    let group = kernel.family("Predicate", &[], 0).unwrap().0.group;
    assert_eq!(group.len(), 2);
    assert!(!kernel.family("Predicate", &[], 0).unwrap().0.large);
    assert!(!kernel.family(&group[1], &[], 0).unwrap().0.large);
    let boxed = app(g("ProofBox"), g("Predicate"));
    let value = term(Term::MutualInduct {
        family: "Predicate".into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        cases: vec![
            RecursionCase {
                family: "Predicate".into(),
                motive: lam(g("Predicate"), nat()),
                branches: vec![lam(boxed.clone(), lam(nat(), zero()))],
            },
            RecursionCase {
                family: group[1].clone(),
                motive: lam(boxed, nat()),
                branches: vec![lam(g("Predicate"), lam(nat(), zero()))],
            },
        ],
        subject: v(0),
    });
    kernel.reset_budget();
    let error = kernel.infer(&[g("Predicate")], &value, 0).unwrap_err();
    assert!(error.contains("large elimination"), "{error}");
}

#[test]
fn nested_headers_do_not_acquire_recursive_index_types() {
    let mut kernel = sequence();
    kernel
        .indexed_inductive(
            "Indexed",
            vec![],
            vec![sort(1)],
            vec![v(0)],
            Level::number(1).unwrap(),
            vec![("at".into(), vec![v(0)], vec![v(0)])],
        )
        .unwrap();
    kernel.reset_budget();
    let error = tree(
        &mut kernel,
        "HiddenIndex",
        vec![
            g("HiddenIndex"),
            app(app(g("Indexed"), g("HiddenIndex")), v(0)),
        ],
    )
    .unwrap_err();
    assert!(error.contains("nested index types"), "{error}");
    assert!(kernel.nested.is_empty());
    assert!(!kernel.contains("HiddenIndex"));
}

#[test]
fn requesting_a_later_source_mutual_member_preserves_declaration_order() {
    let mut kernel = sequence();
    kernel
        .mutual_inductive(vec![
            InductiveInput {
                name: "First".into(),
                universes: vec![],
                parameters: vec![sort(1)],
                indices: vec![],
                sort: Level::number(1).unwrap(),
                constructors: vec![("first".into(), vec![v(0)], vec![])],
            },
            InductiveInput {
                name: "Second".into(),
                universes: vec![],
                parameters: vec![sort(1)],
                indices: vec![],
                sort: Level::number(1).unwrap(),
                constructors: vec![("second".into(), vec![v(0)], vec![])],
            },
        ])
        .unwrap();
    kernel.reset_budget();
    tree(&mut kernel, "Outer", vec![app(g("Second"), g("Outer"))]).unwrap();
    let group = kernel.family("Outer", &[], 0).unwrap().0.group;
    assert_eq!(group.len(), 3);
    assert!(
        matches!(kernel.family_application(&group[1],&[],&[],&[],0).unwrap().as_ref(),Term::App(head,_) if matches!(head.as_ref(),Term::Global(name,_) if name=="First"))
    );
    assert!(
        matches!(kernel.family_application(&group[2],&[],&[],&[],0).unwrap().as_ref(),Term::App(head,_) if matches!(head.as_ref(),Term::Global(name,_) if name=="Second"))
    );
}

#[test]
fn erased_nonuniform_specializations_are_checked_before_beta_reduction() {
    let mut kernel = sequence();
    let argument = app(lam(sort(1), nat()), app(g("Wrong"), nat()));
    let error = kernel
        .inductive(
            "Wrong",
            vec![],
            vec![sort(1)],
            Level::number(1).unwrap(),
            vec![("make".into(), vec![app(g("Seq"), argument)])],
        )
        .unwrap_err();
    assert!(error.contains("uniform"), "{error}");
    assert!(!kernel.contains("Wrong"));
    assert!(kernel.nested.is_empty());
}

#[test]
fn checked_dependent_container_functions_are_instantiated_before_positivity() {
    let mut kernel = sequence();
    kernel
        .inductive(
            "Dependent",
            vec![],
            vec![sort(1), pi(v(0), sort(1))],
            Level::number(1).unwrap(),
            vec![("pair".into(), vec![v(1), app(v(1), v(0))])],
        )
        .unwrap();
    kernel.reset_budget();
    tree(
        &mut kernel,
        "SigmaTree",
        vec![app(app(g("Dependent"), nat()), lam(nat(), g("SigmaTree")))],
    )
    .unwrap();
    let group = kernel.family("SigmaTree", &[], 0).unwrap().0.group;
    assert_eq!(group.len(), 2);
    let view = kernel.family(&group[1], &[], 0).unwrap().0;
    assert_eq!(
        view.constructors[0].recursive,
        vec![None, Some("SigmaTree".into())]
    );
}

#[test]
fn phantom_parameters_cannot_hide_elimination_of_a_provisional_family() {
    let mut kernel = Kernel::new();
    kernel.enable_nested_replay();
    let falsity = g("#pt-false");
    kernel
        .inductive(
            "Callback",
            vec![],
            vec![sort(0), pi(v(0), falsity.clone())],
            Level::number(0).unwrap(),
            vec![("token".into(), vec![])],
        )
        .unwrap();
    kernel.reset_budget();
    let bogus = lam(
        g("Unfinished"),
        term(Term::Induct {
            family: "Unfinished".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(g("Unfinished"), falsity),
            branches: vec![],
            subject: v(0),
        }),
    );
    let field = app(app(g("Callback"), g("Unfinished")), bogus);
    let error = kernel
        .inductive(
            "Unfinished",
            vec![],
            vec![],
            Level::number(0).unwrap(),
            vec![("base".into(), vec![]), ("wrap".into(), vec![field])],
        )
        .unwrap_err();
    assert!(error.contains("provisional"), "{error}");
    assert!(!kernel.contains("Unfinished"));
    assert!(kernel.nested.is_empty());
}

#[test]
fn nested_universe_templates_substitute_levels_once_without_rewriting_caller_values() {
    let mut kernel = Kernel::new();
    kernel.enable_nested_replay();
    let u = Level::variable("u".into());
    let w = Level::variable("w".into());
    kernel
        .inductive(
            "Carrier",
            vec!["u".into(), "w".into()],
            vec![term(Term::Sort(u.clone())), term(Term::Sort(w.clone()))],
            u.clone(),
            vec![("carry".into(), vec![v(1)])],
        )
        .unwrap();
    kernel.reset_budget();
    let recursive = app(
        term(Term::Global("Swapped".into(), vec![u.clone(), w.clone()])),
        v(0),
    );
    let field = app(
        app(
            term(Term::Global("Carrier".into(), vec![u.clone(), w.clone()])),
            recursive,
        ),
        v(0),
    );
    kernel
        .inductive(
            "Swapped",
            vec!["u".into(), "w".into()],
            vec![term(Term::Sort(w.clone()))],
            u.clone(),
            vec![("roll".into(), vec![field])],
        )
        .unwrap();
    let original_levels = vec![u.clone(), w.clone()];
    let group = kernel
        .family("Swapped", &original_levels, 0)
        .unwrap()
        .0
        .group;
    let caller_levels = vec![w.clone(), u.successor().unwrap()];
    let caller_value = term(Term::Sort(u));
    kernel.reset_budget();
    let actual = kernel
        .family_application(
            &group[1],
            &caller_levels,
            std::slice::from_ref(&caller_value),
            &[],
            0,
        )
        .unwrap();
    let expected = app(
        app(
            term(Term::Global("Carrier".into(), caller_levels.clone())),
            app(
                term(Term::Global("Swapped".into(), caller_levels)),
                caller_value.clone(),
            ),
        ),
        caller_value,
    );
    assert!(kernel.same_syntax(&actual, &expected).unwrap());
    kernel.reset_budget();
    kernel
        .definition(
            "view",
            vec!["u".into(), "w".into()],
            term(Term::Sort(w)),
            actual,
            false,
        )
        .unwrap();
}
