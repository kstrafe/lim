//! Delayed scalar observations of the existing natural Euclidean recurrences.
use super::*;

fn delayed_result(k: &mut Kernel, source: &T) -> Option<T> {
    k.delayed_scalar(source, 0).unwrap()
}

fn assert_literal(value: &T, expected: usize) {
    assert!(matches!(value.as_ref(), Term::NatLiteral { family, value }
        if family == NAT && value.decimal() == expected.to_string()));
}

#[test]
fn shared_record_function_is_applied_twice_in_one_delayed_machine() {
    let mut k = kernel();
    for remainder in [false, true] {
        let recurrence = if remainder {
            Recurrence::remainder(2)
        } else {
            Recurrence::division(2)
        };
        let source = recurrence.value(&mut k, literal(23), literal(13));
        let Term::App(with_input, proof) = source.as_ref() else {
            panic!("proof");
        };
        let Term::App(function, _) = with_input.as_ref() else {
            panic!("input");
        };
        let function_type = signature(&mut k, literal(13));
        // f(f(23)) forces a shared projected function at two distinct inputs.
        // Its Update barrier must memoize a function, never its first result.
        let first = app(app(var(0), literal(23)), proof.clone());
        let second = app(app(var(0), first), proof.clone());
        let source = app(lam(function_type, second), function.clone());
        k.reset_budget();
        k.check(&[], &source, &nat(), 0).unwrap();
        k.reset_budget();
        let result = delayed_result(&mut k, &source).expect("shared function computes");
        assert_literal(&result, if remainder { 1 } else { 5 });
    }
}

#[test]
fn zero_exact_and_insufficient_fuel_follow_the_source_recurrence() {
    let mut k = kernel();
    for (remainder, fuel) in [
        (false, 0),
        (true, 0),
        (false, 11),
        (true, 11),
        (false, 10),
        (true, 10),
    ] {
        let recurrence = if remainder {
            Recurrence::remainder(2)
        } else {
            Recurrence::division(2)
        };
        let source = recurrence.value(&mut k, literal(21), literal(fuel));
        k.reset_budget();
        k.check(&[], &source, &nat(), 0).unwrap();
        let materialized = recurrence.materialized(&mut k, literal(21), fuel);
        k.reset_budget();
        k.check(&[], &materialized, &nat(), 0).unwrap();
        k.reset_budget();
        let result = delayed_result(&mut k, &source).expect("small fuel cases compute");
        let expected = if fuel >= 11 {
            if remainder {
                1
            } else {
                10
            }
        } else if remainder {
            99
        } else {
            99 + fuel
        };
        assert_literal(&result, expected);
        k.reset_budget();
        assert!(k.convertible(&[], &result, &materialized, 0).unwrap());
    }
}

#[test]
fn captured_outer_value_survives_delayed_euclidean_observation() {
    let mut k = kernel();
    // The recurrence's dividend is captured before the delayed consumer runs.
    let recurrence = Recurrence::remainder(2).value(&mut k, var(0), literal(13));
    let source = app(lam(nat(), recurrence), literal(23));
    k.reset_budget();
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    let result = delayed_result(&mut k, &source).expect("captured remainder computes");
    assert_literal(&result, 1);
}

#[test]
fn altered_recurrence_is_compared_with_its_source_defined_result() {
    let mut k = kernel();
    let source_recurrence = Recurrence {
        increment: 2,
        ..Recurrence::division(2)
    };
    let source = source_recurrence.value(&mut k, literal(7), literal(4));
    k.reset_budget();
    k.check(&[], &source, &nat(), 0).unwrap();
    let materialized = source_recurrence.materialized(&mut k, literal(7), 4);
    k.reset_budget();
    let result = delayed_result(&mut k, &source).expect("altered small recurrence computes");
    assert_literal(&result, 6);
    k.reset_budget();
    assert!(k.convertible(&[], &result, &materialized, 0).unwrap());
}

#[test]
fn delayed_division_handles_decimal_input_beyond_u128() {
    let mut k = kernel();
    let digits = "98765432101234567890987654321012345678909876543210123456789098765432101234567890";
    let input = decimal(digits);
    let fuel = succ(input.clone());
    let source = Recurrence::division(2).value(&mut k, input, fuel);
    k.reset_budget();
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    let result = delayed_result(&mut k, &source)
        .expect("large division is accelerated by delayed observation");
    assert!(matches!(result.as_ref(), Term::NatLiteral { family, value }
        if family == NAT && value.decimal() == "49382716050617283945493827160506172839454938271605061728394549382716050617283945"));
}

#[test]
fn delayed_attempt_does_not_validate_an_erased_invalid_source() {
    let mut k = kernel();
    let source = Recurrence::division(2).value(&mut k, literal(21), literal(11));
    let Term::App(function, _) = source.as_ref() else {
        panic!("expected proof application")
    };
    let invalid = app(function.clone(), global("unchecked-delayed-proof"));
    k.reset_budget();
    assert!(k.check(&[nat()], &invalid, &nat(), 0).is_err());
    k.reset_budget();
    // The VM is an evaluator, not a substitute for source inference.
    let _ = delayed_result(&mut k, &invalid);
}

#[test]
fn identical_code_with_different_captured_divisors_keeps_distinct_models() {
    let mut k = kernel();
    let recurrence = Recurrence {
        divisor_expression: Some(var(5)),
        decrement_expression: Some(var(5)),
        ..Recurrence::division(2)
    };
    // d / x surround the recurrence; its four internal binders precede them.
    let body = recurrence.value(&mut k, var(0), literal(1002));
    let function = lam(nat(), lam(nat(), body));
    let first = app(app(var(0), literal(2)), literal(1001));
    let second = app(app(var(0), literal(3)), first);
    let source = app(lam(pi(nat(), pi(nat(), nat())), second), function);
    k.reset_budget();
    k.check(&[], &source, &nat(), 0).unwrap();
    k.reset_budget();
    assert_literal(
        &delayed_result(&mut k, &source).expect("both captures compute"),
        166,
    );
}

#[test]
fn unrelated_history_folds_do_not_force_their_unused_fuel_tails() {
    let mut k = kernel();
    k.opaque_definition("opaque-fuel-tail", vec![], nat(), literal(5))
        .unwrap();
    for proof_parameter in [false, true] {
        let second_type = if proof_parameter {
            equality(literal(0))
        } else {
            nat()
        };
        let function_type = pi(nat(), pi(second_type.clone(), nat()));
        let history_type = apps(global("History"), &[function_type.clone(), global("Unit")]);
        let function = lam(nat(), lam(second_type, literal(7)));
        let record = ctor(
            "History",
            vec![function_type, global("Unit")],
            "pair",
            vec![function, ctor("Unit", vec![], "unit", vec![])],
        );
        let fold = induction(
            lam(nat(), history_type.clone()),
            record.clone(),
            lam(nat(), lam(history_type, record)),
            succ(global("opaque-fuel-tail")),
        );
        let argument = if proof_parameter {
            refl(literal(0))
        } else {
            literal(2)
        };
        let source = app(app(project(fold, 0), literal(1000)), argument);
        k.reset_budget();
        k.check(&[], &source, &nat(), 0).unwrap();
        k.reset_budget();
        assert_literal(
            &delayed_result(&mut k, &source).expect("unused predecessor remains lazy"),
            7,
        );
    }
}

#[test]
fn large_operands_with_short_fuel_preserve_the_arbitrary_base() {
    let mut k = kernel();
    for remainder in [false, true] {
        let recurrence = if remainder {
            Recurrence::remainder(2)
        } else {
            Recurrence::division(2)
        };
        let source = recurrence.value(
            &mut k,
            decimal("340282366920938463463374607431768211579"),
            literal(1),
        );
        k.reset_budget();
        k.check(&[], &source, &nat(), 0).unwrap();
        k.reset_budget();
        assert_literal(
            &delayed_result(&mut k, &source).expect("one step reaches arbitrary base"),
            if remainder { 99 } else { 100 },
        );
    }
}
