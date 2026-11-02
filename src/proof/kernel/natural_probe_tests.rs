use super::*;

const NAT: &str = "#pt-nat";
fn nat() -> T {
    term(Term::Global(NAT.into(), vec![]))
}
fn var(i: usize) -> T {
    term(Term::Var(i))
}
fn lam(a: T, b: T) -> T {
    term(Term::Lam(a, b))
}
fn literal(n: &str) -> T {
    term(Term::NatLiteral {
        family: NAT.into(),
        value: Natural::parse(n).unwrap(),
    })
}
fn succ(value: T) -> T {
    term(Term::Ctor {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        constructor: "succ".into(),
        fields: vec![value],
    })
}
fn fold(base: T, body: T, count: T) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![base, lam(nat(), lam(nat(), body))],
        subject: count,
    })
}
fn power(count: &str) -> T {
    fold(
        literal("1"),
        fold(var(0), succ(var(0)), var(0)),
        literal(count),
    )
}

#[test]
fn probes_use_the_existing_checked_recurrence_rules() {
    let mut k = Kernel::new();
    let value = power("128");
    k.check(&[], &value, &nat(), 0).unwrap();
    k.reset_budget();
    assert_eq!(
        k.natural_probe_number(NAT, &value, 0)
            .unwrap()
            .unwrap()
            .decimal(),
        "340282366920938463463374607431768211456"
    );
    assert!(k.work > 0 && k.transformed_bytes > 0);
    assert!(k.reduction_probe_budget.is_none());
}

#[test]
fn declining_a_large_computation_keeps_spent_work_and_allocations() {
    let mut k = Kernel::new();
    assert!(k
        .natural_probe_number(NAT, &power("16384"), 0)
        .unwrap()
        .is_none());
    assert!(k.work > 0 && k.work <= 16_385, "{}", k.work);
    assert!(k.transformed_bytes > 0 && k.transformed_bytes <= 2 * 1024 * 1024);
    assert!(k.reduction_probe_budget.is_none());
    let spent = (k.work, k.transformed_bytes);
    assert!(k
        .natural_probe_number(NAT, &literal("7"), 0)
        .unwrap()
        .is_some());
    assert!(k.work > spent.0 && k.transformed_bytes > spent.1);
}

#[test]
fn an_unrepresentable_optional_result_is_not_a_proof_rule() {
    let mut k = Kernel::new();
    let large = succ(literal(&"9".repeat(MAX_DIGITS)));
    k.check(&[], &large, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k.natural_probe_number(NAT, &large, 0).unwrap().is_none());
    assert!(k.reduction_probe_budget.is_none());
    // A forced ordinary arithmetic result still fails its representation limit.
    k.reset_budget();
    assert!(k
        .natural_closed_number(NAT, &large, 0)
        .unwrap_err()
        .contains("digit limit"));
}

#[test]
fn a_nested_probe_cannot_extend_the_enclosing_attempt() {
    let mut k = Kernel::new();
    let outer = ReductionProbeBudget {
        work: 24,
        bytes: 4096,
        depth: 24,
    };
    k.reduction_probe_budget = Some(outer);
    assert!(k
        .natural_probe_number(NAT, &power("128"), 0)
        .unwrap()
        .is_none());
    assert!(k.work <= outer.work && k.transformed_bytes <= outer.bytes);
    let restored = k.reduction_probe_budget.unwrap();
    assert_eq!(
        (restored.work, restored.bytes, restored.depth),
        (outer.work, outer.bytes, outer.depth)
    );
    k.reduction_probe_budget = None;
}

#[test]
fn unknown_symbols_bad_universes_and_global_exhaustion_are_not_declines() {
    let mut k = Kernel::new();
    let unknown = term(Term::Global("missing".into(), vec![]));
    assert!(k
        .natural_probe_number(NAT, &unknown, 0)
        .unwrap_err()
        .contains("unknown"));
    assert!(k.reduction_probe_budget.is_none());
    let bad = term(Term::Global(NAT.into(), vec![Level::number(0).unwrap()]));
    assert!(k.natural_probe_number(NAT, &bad, 0).is_err());
    assert!(k.reduction_probe_budget.is_none());
    k.reset_budget();
    k.work = WORK;
    assert!(k
        .natural_probe_number(NAT, &literal("1"), 0)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    assert!(k
        .natural_probe_number(NAT, &literal("1"), DEPTH + 1)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    k.transformed_bytes = 64 * 1024 * 1024 + 1;
    assert!(k
        .natural_probe_number(NAT, &literal("1"), 0)
        .unwrap_err()
        .contains("allocation limit"));
    assert!(k.reduction_probe_budget.is_none());
}

#[test]
fn predicted_digit_work_is_refused_before_the_unperformed_operation() {
    let mut k = Kernel::new();
    k.reduction_probe_budget = Some(ReductionProbeBudget {
        work: 12,
        bytes: 1024,
        depth: 24,
    });
    k.tick(0).unwrap();
    let work = k.work;
    assert_eq!(k.charge_work(100).unwrap_err(), REDUCTION_PROBE_DECLINED);
    assert_eq!(k.work, work);
    assert_eq!(
        k.charge_transformation(2048).unwrap_err(),
        REDUCTION_PROBE_DECLINED
    );
    assert_eq!(k.transformed_bytes, 0);
    k.reduction_probe_budget = None;
}

#[test]
fn optional_computation_does_not_replace_initial_source_checking() {
    let mut k = Kernel::new();
    let malformed = term(Term::Let(nat(), nat(), literal("7")));
    assert!(k
        .natural_probe_number(NAT, &malformed, 0)
        .unwrap()
        .is_some());
    assert!(k.reduction_probe_budget.is_none());
    k.reset_budget();
    assert!(k
        .definition("bad", vec![], nat(), malformed, false)
        .is_err());
    assert!(!k.contains("bad"));
}
