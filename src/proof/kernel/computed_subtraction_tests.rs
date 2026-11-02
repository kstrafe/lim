use super::*;

const NAT: &str = "#pt-nat";
const FLAG: &str = "ComputedSubtractionFlag";

fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn nat() -> T {
    global(NAT)
}
fn var(index: usize) -> T {
    term(Term::Var(index))
}
fn lam(domain: T, body: T) -> T {
    term(Term::Lam(domain, body))
}
fn literal(n: usize) -> T {
    term(Term::NatLiteral {
        family: NAT.into(),
        value: Natural::parse(&n.to_string()).unwrap(),
    })
}
fn ctor(family: &str, name: &str) -> T {
    term(Term::Ctor {
        family: family.into(),
        levels: vec![],
        parameters: vec![],
        constructor: name.into(),
        fields: vec![],
    })
}
fn predecessor(value: T) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![literal(0), lam(nat(), lam(nat(), var(1)))],
        subject: value,
    })
}
fn subtraction(base: T, step_body: T, count: usize) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(nat(), nat()),
        branches: vec![base, lam(nat(), lam(nat(), step_body))],
        subject: literal(count),
    })
}
fn flag_number() -> T {
    term(Term::Induct {
        family: FLAG.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: lam(global(FLAG), nat()),
        branches: vec![literal(84), literal(3)],
        subject: ctor(FLAG, "first"),
    })
}
fn computed(base: T, step: T, count: usize) -> T {
    let mut k = Kernel::new();
    if count == 0 {
        return base;
    }
    k.natural_computed_subtraction(
        &[],
        NAT,
        &[],
        &[],
        &[],
        &[RecursionCase {
            family: NAT.into(),
            motive: lam(nat(), nat()),
            branches: vec![base, lam(nat(), lam(nat(), step))],
        }],
        &literal(count),
        0,
    )
    .unwrap()
    .unwrap()
}

#[test]
fn computed_flag_base_subtracts_compact_count_and_matches_unary_iota() {
    let mut k = Kernel::new();
    k.inductive(
        FLAG,
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("first".into(), vec![]), ("second".into(), vec![])],
    )
    .unwrap();
    let base = flag_number();
    let fast = subtraction(base.clone(), predecessor(var(0)), 30);
    k.check(&[], &fast, &nat(), 0).unwrap();
    let result = k.whnf(&[], &fast, 0).unwrap();
    assert!(matches!(result.as_ref(), Term::NatLiteral { value, .. } if value.decimal() == "54"));

    k.reset_budget();
    let exhausted = subtraction(base, predecessor(var(0)), 1000);
    k.check(&[], &exhausted, &nat(), 0).unwrap();
    let exhausted = k.whnf(&[], &exhausted, 0).unwrap();
    assert!(matches!(exhausted.as_ref(), Term::NatLiteral { value, .. } if value.decimal() == "0"));

    for (base_n, count) in [(0, 0), (0, 4), (5, 0), (5, 5), (5, 8), (9, 3)] {
        let optimized = computed(literal(base_n), predecessor(var(0)), count);
        let unary = |n: usize| {
            let mut t = ctor(NAT, "zero");
            for _ in 0..n {
                t = term(Term::Ctor {
                    family: NAT.into(),
                    levels: vec![],
                    parameters: vec![],
                    constructor: "succ".into(),
                    fields: vec![t],
                });
            }
            t
        };
        let slow = term(Term::Induct {
            family: NAT.into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), nat()),
            branches: vec![unary(base_n), lam(nat(), lam(nat(), predecessor(var(0))))],
            subject: unary(count),
        });
        let mut kernel = Kernel::new();
        kernel.check(&[], &optimized, &nat(), 0).unwrap();
        let observed = kernel.whnf(&[], &optimized, 0).unwrap();
        assert!(
            matches!(observed.as_ref(), Term::NatLiteral { value, .. } if value.decimal() == base_n.saturating_sub(count).to_string())
        );
        assert!(kernel.convertible(&[], &observed, &slow, 0).unwrap());
    }
}

#[test]
fn altered_steps_open_bases_and_opaque_bases_decline() {
    for altered in [predecessor(var(1)), predecessor(var(2))] {
        let mut k = Kernel::new();
        let cases = [RecursionCase {
            family: NAT.into(),
            motive: lam(nat(), nat()),
            branches: vec![literal(8), lam(nat(), lam(nat(), altered))],
        }];
        assert!(k
            .natural_computed_subtraction(&[], NAT, &[], &[], &[], &cases, &literal(2), 0)
            .unwrap()
            .is_none());
    }
    let mut k = Kernel::new();
    let cases = [RecursionCase {
        family: NAT.into(),
        motive: lam(nat(), nat()),
        branches: vec![var(0), lam(nat(), lam(nat(), predecessor(var(0))))],
    }];
    assert!(k
        .natural_computed_subtraction(&[nat()], NAT, &[], &[], &[], &cases, &literal(2), 0)
        .unwrap()
        .is_none());
    let open = subtraction(var(0), predecessor(var(0)), 2);
    k.reset_budget();
    k.check(&[nat()], &open, &nat(), 0).unwrap();
    assert!(!k.convertible(&[nat()], &open, &literal(0), 0).unwrap());
    k.opaque_definition("sealed_base", vec![], nat(), literal(8))
        .unwrap();
    let cases = [RecursionCase {
        family: NAT.into(),
        motive: lam(nat(), nat()),
        branches: vec![
            global("sealed_base"),
            lam(nat(), lam(nat(), predecessor(var(0)))),
        ],
    }];
    assert!(k
        .natural_computed_subtraction(&[], NAT, &[], &[], &[], &cases, &literal(2), 0)
        .unwrap()
        .is_none());
}

#[test]
fn source_check_and_resource_limits_are_preserved() {
    let mut k = Kernel::new();
    let malformed = term(Term::Let(nat(), nat(), literal(7)));
    let source = subtraction(malformed, predecessor(var(0)), 2);
    assert!(k.check(&[], &source, &nat(), 0).is_err());

    let discarded_bad = term(Term::Let(nat(), nat(), literal(7)));
    let bad_step = term(Term::Let(nat(), discarded_bad, var(1)));
    let source = subtraction(literal(8), bad_step, 2);
    assert!(k.check(&[], &source, &nat(), 0).is_err());

    let cases = [RecursionCase {
        family: NAT.into(),
        motive: lam(nat(), nat()),
        branches: vec![literal(8), lam(nat(), lam(nat(), predecessor(var(0))))],
    }];
    k.reset_budget();
    k.work = WORK;
    assert!(k
        .natural_computed_subtraction(&[], NAT, &[], &[], &[], &cases, &literal(2), 0)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    k.transformed_bytes = 64 * 1024 * 1024;
    assert!(k
        .natural_computed_subtraction(&[], NAT, &[], &[], &[], &cases, &literal(2), 0)
        .unwrap_err()
        .contains("allocation limit"));
    k.reset_budget();
    assert!(k
        .natural_computed_subtraction(&[], NAT, &[], &[], &[], &cases, &literal(2), DEPTH + 1)
        .unwrap_err()
        .contains("resource limit"));
}

#[test]
fn zero_count_does_not_inspect_the_unused_step() {
    let mut k = Kernel::new();
    let cases = [RecursionCase {
        family: NAT.into(),
        motive: lam(nat(), nat()),
        branches: vec![literal(8), global("unchecked_unused_step")],
    }];
    assert!(k
        .natural_computed_subtraction(&[], NAT, &[], &[], &[], &cases, &literal(0), 0)
        .unwrap()
        .is_none());
    assert_eq!(k.work, 0);
    assert_eq!(k.transformed_bytes, 0);
    // The optimization is not an authority to accept an untyped source branch.
    let malformed = term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive: cases[0].motive.clone(),
        branches: cases[0].branches.clone(),
        subject: literal(0),
    });
    assert!(k.check(&[], &malformed, &nat(), 0).is_err());
}

#[test]
fn modified_inner_recurrences_do_not_authorize_subtraction() {
    let mut k = Kernel::new();
    for modified in [
        term(Term::Induct {
            family: NAT.into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), nat()),
            branches: vec![literal(1), lam(nat(), lam(nat(), var(1)))],
            subject: var(0),
        }),
        term(Term::Induct {
            family: NAT.into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(nat(), nat()),
            branches: vec![literal(0), lam(nat(), lam(nat(), var(0)))],
            subject: var(0),
        }),
    ] {
        let cases = [RecursionCase {
            family: NAT.into(),
            motive: lam(nat(), nat()),
            branches: vec![literal(8), lam(nat(), lam(nat(), modified))],
        }];
        k.reset_budget();
        assert!(k
            .natural_computed_subtraction(&[], NAT, &[], &[], &[], &cases, &literal(2), 0)
            .unwrap()
            .is_none());
    }
}
