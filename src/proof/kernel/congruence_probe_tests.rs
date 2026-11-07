//! Regressions for the narrow natural-index congruence scheduling hint.
use super::*;

fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}

fn var(index: usize) -> T {
    term(Term::Var(index))
}

fn app(function: T, argument: T) -> T {
    term(Term::App(function, argument))
}

fn apps(function: T, arguments: impl IntoIterator<Item = T>) -> T {
    arguments.into_iter().fold(function, app)
}

fn ctor(family: &str, constructor: &str, fields: Vec<T>) -> T {
    term(Term::Ctor {
        family: family.into(),
        levels: vec![],
        parameters: vec![],
        constructor: constructor.into(),
        fields,
    })
}

fn zero() -> T {
    ctor("#pt-nat", "zero", vec![])
}

fn succ(value: T) -> T {
    ctor("#pt-nat", "succ", vec![value])
}

fn indexed_family(k: &mut Kernel) {
    k.indexed_inductive(
        "NaturalIndexProbe",
        vec![],
        vec![term(Term::Sort(Level::number(1).unwrap())), var(0)],
        vec![var(1)],
        Level::number(1).unwrap(),
        vec![("reflexive".into(), vec![], vec![var(0)])],
    )
    .unwrap();
}

#[test]
fn natural_indexed_family_uses_ordinary_comparison_with_outer_budget_restored() {
    let mut k = Kernel::new();
    indexed_family(&mut k);
    let left = apps(
        global("NaturalIndexProbe"),
        [global("#pt-nat"), zero(), zero()],
    );
    let right = apps(
        global("NaturalIndexProbe"),
        [global("#pt-nat"), zero(), zero()],
    );
    let family_type = term(Term::Sort(Level::number(1).unwrap()));
    k.check(&[], &left, &family_type, 0).unwrap();
    k.check(&[], &right, &family_type, 0).unwrap();
    let head = global("NaturalIndexProbe");
    let arguments = [global("#pt-nat"), zero(), zero()];
    let argument_refs = arguments.iter().collect::<Vec<_>>();
    assert!(k
        .natural_index_arguments(&head, &argument_refs, &argument_refs, 0)
        .unwrap());
    k.reset_budget();

    let outer = ReductionProbeBudget {
        work: 128,
        bytes: 8192,
        depth: 24,
    };
    k.reduction_probe_budget = Some(outer);
    assert!(k.conversion_congruence(&[], &left, &right, 0).unwrap());
    let restored = k.reduction_probe_budget.unwrap();
    assert_eq!(
        (restored.work, restored.bytes, restored.depth),
        (outer.work, outer.bytes, outer.depth)
    );
    k.reduction_probe_budget = None;
}

#[test]
fn eligibility_requires_a_canonical_natural_first_parameter_and_inductive_head() {
    let mut k = Kernel::new();
    indexed_family(&mut k);
    k.inductive(
        "ProbeBool",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("false".into(), vec![]), ("true".into(), vec![])],
    )
    .unwrap();
    k.opaque_definition(
        "opaque_natural_function",
        vec![],
        term(Term::Pi(global("#pt-nat"), global("#pt-nat"))),
        term(Term::Lam(global("#pt-nat"), var(0))),
    )
    .unwrap();

    let head = global("NaturalIndexProbe");
    let nat_args = [global("#pt-nat"), zero(), zero()];
    let nat_refs = nat_args.iter().collect::<Vec<_>>();
    assert!(k
        .natural_index_arguments(&head, &nat_refs, &nat_refs, 0)
        .unwrap());

    let bool_args = [
        global("ProbeBool"),
        ctor("ProbeBool", "false", vec![]),
        ctor("ProbeBool", "false", vec![]),
    ];
    let bool_application = apps(global("NaturalIndexProbe"), bool_args.clone());
    k.check(
        &[],
        &bool_application,
        &term(Term::Sort(Level::number(1).unwrap())),
        0,
    )
    .unwrap();
    let bool_refs = bool_args.iter().collect::<Vec<_>>();
    assert!(!k
        .natural_index_arguments(&head, &bool_refs, &bool_refs, 0)
        .unwrap());

    let opaque_head = global("opaque_natural_function");
    assert!(!k
        .natural_index_arguments(&opaque_head, &nat_refs, &nat_refs, 0)
        .unwrap());

    k.declarations.set_limit(0);
    k.trim_completed_declarations().unwrap();
    assert!(k
        .declarations
        .resident("NaturalIndexProbe")
        .unwrap()
        .is_none());
    let resident_bytes = k.declarations.resident_value_bytes();
    assert!(!k
        .natural_index_arguments(&head, &nat_refs, &nat_refs, 0)
        .unwrap());
    assert!(k
        .declarations
        .resident("NaturalIndexProbe")
        .unwrap()
        .is_none());
    assert_eq!(k.declarations.resident_value_bytes(), resident_bytes);
}

#[test]
fn opaque_proof_result_with_unequal_natural_arguments_uses_proof_irrelevance() {
    let mut k = Kernel::new();
    k.inductive(
        "TwoProofs",
        vec![],
        vec![],
        Level::number(0).unwrap(),
        vec![("first".into(), vec![]), ("second".into(), vec![])],
    )
    .unwrap();
    let proposition = global("TwoProofs");
    let first = ctor("TwoProofs", "first", vec![]);
    let second = ctor("TwoProofs", "second", vec![]);
    k.opaque_definition(
        "opaque_proof_function",
        vec![],
        term(Term::Pi(global("#pt-nat"), proposition.clone())),
        term(Term::Lam(global("#pt-nat"), first.clone())),
    )
    .unwrap();

    let left = app(global("opaque_proof_function"), zero());
    let right = app(global("opaque_proof_function"), succ(zero()));
    k.check(&[], &left, &proposition, 0).unwrap();
    k.check(&[], &right, &proposition, 0).unwrap();
    k.reset_budget();
    assert!(!k.conversion_congruence(&[], &left, &right, 0).unwrap());
    assert!(k.convertible(&[], &left, &right, 0).unwrap());
    assert!(!k.same_syntax(&first, &second).unwrap());
    assert!(k.reduction_probe_budget.is_none());
}
