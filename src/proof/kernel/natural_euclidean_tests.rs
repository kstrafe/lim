//! Compare the observation with a separately materialized history fold.
use super::*;

const NAT: &str = "#pt-nat";
fn global(s: &str) -> T {
    term(Term::Global(s.into(), vec![]))
}
fn nat() -> T {
    global(NAT)
}
fn var(i: usize) -> T {
    term(Term::Var(i))
}
fn lam(a: T, b: T) -> T {
    term(Term::Lam(a, b))
}
fn pi(a: T, b: T) -> T {
    term(Term::Pi(a, b))
}
fn app(a: T, b: T) -> T {
    term(Term::App(a, b))
}
fn literal(n: usize) -> T {
    decimal(&n.to_string())
}
fn decimal(n: &str) -> T {
    term(Term::NatLiteral {
        family: NAT.into(),
        value: Natural::parse(n).unwrap(),
    })
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
fn succ(n: T) -> T {
    ctor(NAT, vec![], "succ", vec![n])
}
fn refl(n: T) -> T {
    term(Term::Refl(nat(), n))
}
fn equality(n: T) -> T {
    term(Term::Eq(nat(), n.clone(), n))
}
fn flag(b: bool) -> T {
    ctor("Tag", vec![], if b { "yes" } else { "no" }, vec![])
}
fn project(record: T, index: usize) -> T {
    term(Term::Project {
        family: "History".into(),
        index,
        subject: record,
    })
}
fn induction(motive: T, base: T, step: T, count: T) -> T {
    term(Term::Induct {
        family: NAT.into(),
        levels: vec![],
        parameters: vec![],
        indices: vec![],
        motive,
        branches: vec![base, step],
        subject: count,
    })
}
fn fold(ty: T, base: T, body: T, count: T) -> T {
    induction(
        lam(nat(), ty.clone()),
        base,
        lam(nat(), lam(ty, body)),
        count,
    )
}
// 2^n as a Nat induction: each step folds `succ` over the previous value.
fn power_of_two(count: T) -> T {
    fold(
        nat(),
        literal(1),
        fold(nat(), var(0), succ(var(0)), var(0)),
        count,
    )
}
fn le(left: T, right: T) -> T {
    let inner = fold(global("Tag"), flag(false), app(var(3), var(1)), var(0));
    app(
        fold(
            pi(nat(), global("Tag")),
            lam(nat(), flag(true)),
            lam(nat(), inner),
            left,
        ),
        right,
    )
}
fn predecessor(value: T) -> T {
    fold(nat(), literal(0), var(1), value)
}
fn signature(k: &mut Kernel, fuel: T) -> T {
    let shifted = k.shift(&fuel, 1, 0, 0).unwrap();
    pi(nat(), pi(equality(shifted), nat()))
}
fn history_type(k: &mut Kernel, fuel: T) -> T {
    apps(global("History"), &[signature(k, fuel), global("Unit")])
}
fn history(k: &mut Kernel, fuel: T, function: T) -> T {
    ctor(
        "History",
        vec![signature(k, fuel), global("Unit")],
        "pair",
        vec![function, ctor("Unit", vec![], "unit", vec![])],
    )
}
fn kernel() -> Kernel {
    let mut k = Kernel::new();
    for (family, constructors) in [
        ("Tag", vec![("no".into(), vec![]), ("yes".into(), vec![])]),
        ("Unit", vec![("unit".into(), vec![])]),
    ] {
        k.inductive(
            family,
            vec![],
            vec![],
            Level::number(1).unwrap(),
            constructors,
        )
        .unwrap();
    }
    k.inductive(
        "History",
        vec![],
        vec![term(Term::Sort(Level::number(1).unwrap())); 2],
        Level::number(1).unwrap(),
        vec![("pair".into(), vec![var(1), var(1)])],
    )
    .unwrap();
    k.reset_budget();
    k
}

#[derive(Clone)]
struct Recurrence {
    divisor: usize,
    decrement: usize,
    increment: usize,
    reversed: bool,
    history_index: usize,
    terminal: usize,
    terminal_state: bool,
    divisor_expression: Option<T>,
    decrement_expression: Option<T>,
    applied_update: bool,
}
impl Recurrence {
    fn division(divisor: usize) -> Self {
        Self {
            divisor,
            decrement: divisor,
            increment: 1,
            reversed: false,
            history_index: 0,
            terminal: 0,
            terminal_state: false,
            divisor_expression: None,
            decrement_expression: None,
            applied_update: false,
        }
    }
    fn remainder(divisor: usize) -> Self {
        Self {
            increment: 0,
            terminal_state: true,
            ..Self::division(divisor)
        }
    }
    fn parts(&self, k: &mut Kernel) -> (T, T, T) {
        let motive = lam(nat(), history_type(k, var(0)));
        // A deliberately nonzero base distinguishes insufficient fuel from
        // unbounded division, without relying on a false proof argument.
        let base = history(
            k,
            literal(0),
            lam(nat(), lam(equality(literal(0)), literal(99))),
        );
        let count = self
            .decrement_expression
            .clone()
            .unwrap_or_else(|| literal(self.decrement));
        let update = if self.applied_update {
            app(
                lam(nat(), fold(nat(), var(2), predecessor(var(0)), var(0))),
                count,
            )
        } else {
            fold(nat(), var(1), predecessor(var(0)), count)
        };
        let call = app(
            app(project(var(2), self.history_index), update),
            refl(var(3)),
        );
        let positive = (0..self.increment).fold(call, |n, _| succ(n));
        let divisor = self
            .divisor_expression
            .clone()
            .unwrap_or_else(|| literal(self.divisor));
        let guard = if self.reversed {
            le(var(1), divisor)
        } else {
            le(divisor, var(1))
        };
        let body = term(Term::Induct {
            family: "Tag".into(),
            levels: vec![],
            parameters: vec![],
            indices: vec![],
            motive: lam(global("Tag"), nat()),
            branches: vec![
                if self.terminal_state {
                    (0..self.terminal).fold(var(1), |value, _| succ(value))
                } else {
                    literal(self.terminal)
                },
                positive,
            ],
            subject: guard,
        });
        let function = lam(nat(), lam(equality(succ(var(2))), body));
        let step_body = history(k, succ(var(1)), function);
        let step_type = history_type(k, var(0));
        (motive, base, lam(nat(), lam(step_type, step_body)))
    }
    fn value(&self, k: &mut Kernel, input: T, fuel: T) -> T {
        let (motive, base, step) = self.parts(k);
        let record = induction(motive, base, step, fuel.clone());
        app(app(project(record, 0), input), refl(fuel))
    }
    fn materialized(&self, k: &mut Kernel, input: T, fuel: usize) -> T {
        let (_, mut record, step) = self.parts(k);
        for n in 0..fuel {
            record = app(app(step.clone(), literal(n)), record);
        }
        app(app(project(record, 0), input), refl(literal(fuel)))
    }
}

#[test]
fn open_dividends_decline_before_analyzing_the_recurrence() {
    let mut k = kernel();
    for recurrence in [Recurrence::division(3), Recurrence::remainder(3)] {
        let value = recurrence.value(&mut k, var(0), literal(4));
        k.reset_budget();
        k.check(&[nat()], &value, &nat(), 0).unwrap();
        k.reset_budget();
        assert!(k
            .natural_euclidean_observation(&value, 0)
            .unwrap()
            .is_none());
        assert!(k.work < 16, "open-input recognition should stop cheaply");
        assert_eq!(k.transformation_bytes(), 0);

        // Declining speculative arithmetic never validates the original term.
        let Term::App(function, _) = value.as_ref() else {
            panic!("proof application");
        };
        let invalid = app(function.clone(), global("unchecked-proof"));
        k.reset_budget();
        assert!(k.check(&[nat()], &invalid, &nat(), 0).is_err());
    }
}

#[test]
fn observations_match_materialized_records_without_the_observation_rule() {
    let mut k = kernel();
    for d in 1..=4 {
        for x in 0..=8 {
            let q = x / d;
            let recurrence = Recurrence::division(d);
            let fast = recurrence.value(&mut k, literal(x), literal(q + 1));
            let slow = recurrence.materialized(&mut k, literal(x), q + 1);
            k.reset_budget();
            k.check(&[], &fast, &nat(), 0).unwrap();
            k.reset_budget();
            k.check(&[], &slow, &nat(), 0).unwrap();
            k.reset_budget();
            let result = k
                .natural_euclidean_observation(&fast, 0)
                .unwrap()
                .expect("recognized recurrence");
            assert!(
                matches!(result.as_ref(),Term::NatLiteral { value,.. } if value.decimal()==q.to_string())
            );
            k.reset_budget();
            assert!(k.natural_euclidean_observation(&slow, 0).unwrap().is_none());
            k.reset_budget();
            assert!(
                k.convertible(&[], &slow, &result, 0).unwrap(),
                "x={x} d={d}"
            );
        }
    }
}

#[test]
fn exhausted_fuel_preserves_the_arbitrary_base_function() {
    let mut k = kernel();
    let recurrence = Recurrence::division(5);
    for fuel in 0..=4 {
        let fast = recurrence.value(&mut k, literal(21), literal(fuel));
        k.reset_budget();
        k.check(&[], &fast, &nat(), 0).unwrap();
        k.reset_budget();
        assert!(k.natural_euclidean_observation(&fast, 0).unwrap().is_none());
        let slow = recurrence.materialized(&mut k, literal(21), fuel);
        k.reset_budget();
        assert!(k.convertible(&[], &slow, &literal(99 + fuel), 0).unwrap());
    }
}

#[test]
fn structurally_computed_dividends_are_observed_with_successor_fuel() {
    let mut k = kernel();
    for (exponent, divisor, expected) in [(6, 8, 8), (12, 8, 512)] {
        let input = power_of_two(literal(exponent));
        let fuel = succ(input.clone());
        let value = Recurrence::division(divisor).value(&mut k, input, fuel);
        k.reset_budget();
        k.check(&[], &value, &nat(), 0).unwrap();
        k.reset_budget();
        let result = k.natural_euclidean_observation(&value, 0).unwrap();
        assert!(
            matches!(result.as_ref().map(T::as_ref), Some(Term::NatLiteral { value, .. }) if value.decimal() == expected.to_string())
        );
    }
}

#[test]
fn zero_and_insufficient_fuel_do_not_force_an_oversized_input() {
    let mut k = kernel();
    // This well-typed fold denotes a number far beyond the compact literal
    // limit, while the small fuel means observation can reject immediately.
    let input = power_of_two(literal(MAX_DIGITS * 4));
    let recurrence = Recurrence::division(8);
    for fuel in [literal(0), literal(1), literal(2)] {
        let value = recurrence.value(&mut k, input.clone(), fuel);
        k.reset_budget();
        k.check(&[], &value, &nat(), 0).unwrap();
        k.reset_budget();
        assert!(k
            .natural_euclidean_observation(&value, 0)
            .unwrap()
            .is_none());
    }
    let small = recurrence.materialized(&mut k, input, 0);
    k.reset_budget();
    assert!(k.convertible(&[], &small, &literal(99), 0).unwrap());
}

#[test]
fn different_guards_updates_and_constants_are_not_division() {
    let mut k = kernel();
    let mut cases = vec![Recurrence::division(0)];
    let original = Recurrence::division(3);
    for increment in [0, 2] {
        cases.push(Recurrence {
            increment,
            ..original.clone()
        });
    }
    for decrement in [0, 2, 4] {
        cases.push(Recurrence {
            decrement,
            ..original.clone()
        });
    }
    cases.push(Recurrence {
        reversed: true,
        ..original.clone()
    });
    cases.push(Recurrence {
        terminal: 1,
        ..original.clone()
    });
    for recurrence in cases {
        let value = recurrence.value(&mut k, literal(21), literal(30));
        k.reset_budget();
        k.check(&[], &value, &nat(), 0).unwrap();
        k.reset_budget();
        assert!(k
            .natural_euclidean_observation(&value, 0)
            .unwrap()
            .is_none());
    }
    let invalid = Recurrence {
        history_index: 1,
        ..original
    }
    .value(&mut k, literal(21), literal(30));
    k.reset_budget();
    assert!(k.check(&[], &invalid, &nat(), 0).is_err());
    k.reset_budget();
    assert!(k
        .natural_euclidean_observation(&invalid, 0)
        .unwrap()
        .is_none());
}

#[test]
fn compact_and_fuel_queries_do_not_force_unused_successor_tails() {
    let mut k = kernel();
    let huge = decimal(&"9".repeat(MAX_DIGITS));
    let overflow = succ(huge.clone());
    k.check(&[], &overflow, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k
        .euclidean_compact_number(NAT, &overflow, 0)
        .unwrap()
        .is_none());
    k.reset_budget();
    assert!(k
        .euclidean_has_fuel(NAT, &overflow, &Natural::parse("0").unwrap(), 0)
        .unwrap());
    let value = Recurrence::division(2).value(&mut k, literal(0), overflow);
    k.reset_budget();
    k.check(&[], &value, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k
        .natural_euclidean_observation(&value, 0)
        .unwrap()
        .is_some());
    k.reset_budget();
    assert!(!k
        .euclidean_has_fuel(
            NAT,
            &huge,
            &Natural::parse(&"9".repeat(MAX_DIGITS)).unwrap(),
            0
        )
        .unwrap());
}

#[test]
fn overflowing_compact_successor_charges_the_declined_digit_scan() {
    let mut k = kernel();
    let overflow = succ(decimal(&"9".repeat(MAX_DIGITS)));
    k.reset_budget();
    k.work = WORK - MAX_DIGITS / 2;
    let error = k.euclidean_compact_number(NAT, &overflow, 0).unwrap_err();
    assert!(error.contains("resource limit"), "{error}");
}

#[test]
fn fuel_comparison_charges_long_equal_digit_prefixes() {
    let mut k = kernel();
    let digits = "9".repeat(MAX_DIGITS);
    let fuel = decimal(&digits);
    let required = Natural::parse(&digits).unwrap();
    k.reset_budget();
    k.work = WORK - MAX_DIGITS / 2;
    let error = k.euclidean_has_fuel(NAT, &fuel, &required, 0).unwrap_err();
    assert!(error.contains("resource limit"), "{error}");
}

#[test]
fn observations_keep_nominal_opacity_and_resource_boundaries() {
    let mut k = kernel();
    k.opaque_definition("hidden", vec![], nat(), literal(21))
        .unwrap();
    let value = Recurrence::division(3).value(&mut k, global("hidden"), literal(8));
    k.reset_budget();
    assert!(k
        .natural_euclidean_observation(&value, 0)
        .unwrap()
        .is_none());
    let value = Recurrence::division(3).value(&mut k, literal(21), literal(8));
    k.reset_budget();
    k.work = WORK;
    assert!(k
        .natural_euclidean_observation(&value, 0)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    k.transformed_bytes = 64 * 1024 * 1024;
    assert!(k
        .natural_euclidean_observation(&value, 0)
        .unwrap_err()
        .contains("allocation limit"));
    k.reset_budget();
    assert!(k
        .natural_euclidean_observation(&value, DEPTH)
        .unwrap_err()
        .contains("resource limit"));
    k.reset_budget();
    let other = term(Term::NatLiteral {
        family: "Other".into(),
        value: Natural::parse("21").unwrap(),
    });
    assert!(k
        .euclidean_compact_number(NAT, &other, 0)
        .unwrap()
        .is_none());
}

#[test]
fn source_inference_still_checks_ignored_proofs_and_annotations() {
    let mut k = kernel();
    let good = Recurrence::division(3).value(&mut k, literal(21), literal(8));
    let Term::App(function, _) = good.as_ref() else {
        panic!("application")
    };
    let bad = app(function.clone(), var(999));
    k.reset_budget();
    assert!(k.check(&[], &bad, &nat(), 0).is_err());
    // A discarded let annotation also remains subject to inference.
    let bad = term(Term::Let(nat(), global("Unit"), good));
    k.reset_budget();
    assert!(k.check(&[], &bad, &nat(), 0).is_err());
    let not_a_proof = pi(
        nat(),
        pi(term(Term::Sort(Level::number(0).unwrap())), nat()),
    );
    k.reset_budget();
    assert!(!k.euclidean_function_type(&not_a_proof, NAT, 0).unwrap());
}

#[test]
fn decimal_work_is_charged_before_long_division_runs() {
    let mut k = kernel();
    let value = Recurrence::division(3).value(&mut k, decimal(&"9".repeat(MAX_DIGITS)), literal(8));
    // The operand is legal, but even the linear digit charge cannot fit.
    k.reset_budget();
    k.work = WORK - 10_000;
    assert!(k
        .natural_euclidean_observation(&value, 0)
        .unwrap_err()
        .contains("resource limit"));
}

#[test]
fn decision_tags_may_not_erase_data_fields_or_unfinished_families() {
    let mut k = kernel();
    k.inductive(
        "DataTag",
        vec![],
        vec![],
        Level::number(1).unwrap(),
        vec![("no".into(), vec![]), ("yes".into(), vec![nat()])],
    )
    .unwrap();
    k.reset_budget();
    assert!(k.euclidean_tag_shape("DataTag", 0).unwrap().is_none());
    assert!(k.euclidean_tag_shape("Missing", 0).unwrap().is_none());
    let proposition = term(Term::Sort(Level::number(0).unwrap()));
    k.inductive(
        "Decision",
        vec![],
        vec![proposition],
        Level::number(1).unwrap(),
        vec![
            ("positive".into(), vec![var(0)]),
            ("negative".into(), vec![pi(var(0), global("#pt-false"))]),
        ],
    )
    .unwrap();
    k.reset_budget();
    assert!(k.euclidean_tag_shape("Decision", 0).unwrap().is_some());
}

#[test]
fn remainder_observation_matches_materialized_history_records() {
    let mut k = kernel();
    for d in 1..=4 {
        for x in 0..=8 {
            let recurrence = Recurrence::remainder(d);
            let fuel = x / d + 1;
            let fast = recurrence.value(&mut k, literal(x), literal(fuel));
            let slow = recurrence.materialized(&mut k, literal(x), fuel);
            k.reset_budget();
            k.check(&[], &fast, &nat(), 0).unwrap();
            k.reset_budget();
            k.check(&[], &slow, &nat(), 0).unwrap();
            k.reset_budget();
            let result = k.natural_euclidean_observation(&fast, 0).unwrap().unwrap();
            assert!(
                matches!(result.as_ref(),Term::NatLiteral {value,..} if value.decimal()==(x%d).to_string())
            );
            k.reset_budget();
            assert!(k.natural_euclidean_observation(&slow, 0).unwrap().is_none());
            k.reset_budget();
            assert!(k.convertible(&[], &slow, &result, 0).unwrap());
        }
    }
}

#[test]
fn remainder_does_not_assume_that_proof_arguments_guarantee_fuel() {
    let mut k = kernel();
    let recurrence = Recurrence::remainder(5);
    for fuel in 0..=4 {
        let value = recurrence.value(&mut k, literal(21), literal(fuel));
        k.reset_budget();
        k.check(&[], &value, &nat(), 0).unwrap();
        k.reset_budget();
        assert!(k
            .natural_euclidean_observation(&value, 0)
            .unwrap()
            .is_none());
        let slow = recurrence.materialized(&mut k, literal(21), fuel);
        k.reset_budget();
        assert!(k.convertible(&[], &slow, &literal(99), 0).unwrap());
    }
    let value = recurrence.value(&mut k, literal(21), literal(5));
    k.reset_budget();
    assert!(
        matches!(k.natural_euclidean_observation(&value,0).unwrap().as_ref().map(T::as_ref),Some(Term::NatLiteral {value,..}) if value.decimal()=="1")
    );
}

#[test]
fn altered_remainder_conditions_updates_and_results_are_refused() {
    let mut k = kernel();
    let good = Recurrence::remainder(3);
    for bad in [
        Recurrence::remainder(0),
        Recurrence {
            increment: 1,
            ..good.clone()
        },
        Recurrence {
            terminal: 1,
            ..good.clone()
        },
        Recurrence {
            decrement: 2,
            ..good.clone()
        },
        Recurrence {
            decrement: 4,
            ..good.clone()
        },
        Recurrence {
            reversed: true,
            ..good.clone()
        },
        Recurrence {
            terminal_state: false,
            ..good.clone()
        },
    ] {
        let value = bad.value(&mut k, literal(21), literal(30));
        k.reset_budget();
        k.check(&[], &value, &nat(), 0).unwrap();
        k.reset_budget();
        assert!(k
            .natural_euclidean_observation(&value, 0)
            .unwrap()
            .is_none());
    }
}

#[test]
fn validated_divisor_reuse_preserves_argument_scope_and_equivalent_fallbacks() {
    let mut k = kernel();
    for computed_update in [false, true] {
        let d = power_of_two(literal(3));
        let recurrence = Recurrence {
            divisor_expression: Some(d.clone()),
            decrement_expression: Some(if computed_update { d } else { literal(8) }),
            applied_update: true,
            ..Recurrence::remainder(8)
        };
        let value = recurrence.value(&mut k, literal(21), literal(3));
        k.reset_budget();
        k.check(&[], &value, &nat(), 0).unwrap();
        k.reset_budget();
        let result = k.natural_euclidean_observation(&value, 0).unwrap().unwrap();
        assert!(matches!(result.as_ref(),Term::NatLiteral {value,..} if value.decimal()=="5"));
        let slow = recurrence.materialized(&mut k, literal(21), 3);
        k.reset_budget();
        assert!(k.convertible(&[], &result, &slow, 0).unwrap());
    }
}

#[test]
fn matching_a_guard_does_not_authorize_an_unrelated_decrement_argument() {
    let mut k = kernel();
    let recurrence = Recurrence {
        divisor_expression: Some(power_of_two(literal(3))),
        decrement_expression: Some(literal(9)),
        applied_update: true,
        ..Recurrence::remainder(8)
    };
    let value = recurrence.value(&mut k, literal(21), literal(3));
    k.reset_budget();
    k.check(&[], &value, &nat(), 0).unwrap();
    k.reset_budget();
    assert!(k
        .natural_euclidean_observation(&value, 0)
        .unwrap()
        .is_none());
    let slow = recurrence.materialized(&mut k, literal(21), 3);
    k.reset_budget();
    assert!(k.convertible(&[], &slow, &literal(3), 0).unwrap());
}

#[path = "delayed_euclidean_tests.rs"]
mod delayed_observations;
