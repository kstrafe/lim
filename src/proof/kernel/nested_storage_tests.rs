use super::*;

fn g(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}

fn sort(level: u32) -> T {
    term(Term::Sort(Level::number(level).unwrap()))
}

fn app(function: T, argument: T) -> T {
    term(Term::App(function, argument))
}

fn sequence() -> Kernel {
    let mut kernel = Kernel::new();
    kernel
        .inductive(
            "Seq",
            vec![],
            vec![sort(1)],
            Level::number(1).unwrap(),
            vec![
                ("nil".into(), vec![]),
                (
                    "cons".into(),
                    vec![term(Term::Var(0)), term(Term::SelfType)],
                ),
            ],
        )
        .unwrap();
    kernel.reset_budget();
    kernel
}

fn tree(kernel: &mut Kernel, name: &str) -> Result<()> {
    let nested_sequence = app(g("Seq"), g(name));
    kernel.inductive(
        name,
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![
            ("leaf".into(), vec![]),
            ("node".into(), vec![nested_sequence]),
        ],
    )
}

fn evict_nested_views(kernel: &mut Kernel) -> Result<()> {
    kernel.enable_declaration_spilling();
    kernel.nested.set_limit(0);
    kernel.trim_completed_declarations()?;
    Ok(())
}

#[test]
fn spilled_nested_views_resolve_for_application_and_inference() {
    let mut kernel = sequence();
    tree(&mut kernel, "Tree").unwrap();
    let group = kernel.family("Tree", &[], 0).unwrap().0.group;
    assert_eq!(group.len(), 2);

    evict_nested_views(&mut kernel).unwrap();
    assert!(kernel.nested.is_spilled());
    assert_eq!(kernel.nested.resident_value_bytes(), 0);

    let alias = &group[1];
    assert!(kernel.nested.get(alias).unwrap().is_some());
    assert!(kernel.nested.contains_key(alias).unwrap());
    let physical = kernel.family_application(alias, &[], &[], &[], 0).unwrap();
    assert!(kernel
        .same_syntax(&physical, &app(g("Seq"), g("Tree")))
        .unwrap());
    assert!(kernel.infer(&[], &g(alias), 0).is_err());
    let forged_constructor = term(Term::Ctor {
        family: alias.clone(),
        levels: vec![],
        parameters: vec![],
        constructor: "nil".into(),
        fields: vec![],
    });
    assert!(kernel
        .infer(&[], &forged_constructor, 0)
        .unwrap_err()
        .contains("original constructors"));
}

#[test]
fn failed_group_does_not_damage_previously_evicted_nested_views() {
    let mut kernel = sequence();
    tree(&mut kernel, "Tree").unwrap();
    let group = kernel.family("Tree", &[], 0).unwrap().0.group;
    evict_nested_views(&mut kernel).unwrap();

    let error = kernel
        .inductive(
            "Broken",
            vec![],
            vec![],
            Level::number(1).unwrap(),
            vec![(
                "bad".into(),
                vec![app(g("Seq"), g("Broken")), g("MissingType")],
            )],
        )
        .unwrap_err();
    assert!(!error.is_empty());
    assert!(!kernel.contains("Broken").unwrap());
    assert!(!kernel.nested.contains_key("$nested:6:Broken:1").unwrap());
    assert!(kernel.nested.contains_key(&group[1]).unwrap());
    assert!(kernel
        .family_application(&group[1], &[], &[], &[], 0)
        .is_ok());
}

#[test]
fn separate_nested_groups_keep_distinct_nominal_views_after_eviction() {
    let mut kernel = sequence();
    tree(&mut kernel, "Tree").unwrap();
    tree(&mut kernel, "Forest").unwrap();
    let tree_group = kernel.family("Tree", &[], 0).unwrap().0.group;
    let forest_group = kernel.family("Forest", &[], 0).unwrap().0.group;
    assert_ne!(tree_group[1], forest_group[1]);

    evict_nested_views(&mut kernel).unwrap();
    for (alias, root) in [(&tree_group[1], "Tree"), (&forest_group[1], "Forest")] {
        assert!(kernel.nested.get(alias).unwrap().is_some());
        let physical = kernel.family_application(alias, &[], &[], &[], 0).unwrap();
        assert!(kernel
            .same_syntax(&physical, &app(g("Seq"), g(root)))
            .unwrap());
        assert!(kernel.infer(&[], &g(alias), 0).is_err());
    }
}
