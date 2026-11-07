//! Signed c4 alternatives, prime coordinate cases and invalid-premise controls.
#[path = "support/flt_integral_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, fixture_with_prelude, term};

fn n(value: usize) -> String {
    if value <= 128 {
        format!("(#pt-numeral {value})")
    } else {
        term("add", &[&n(128), &n(value - 128)])
    }
}
fn int(value: isize) -> String {
    let magnitude = term("integer-of-natural", &[&n(value.unsigned_abs())]);
    if value < 0 {
        term("integer-negate", &[&magnitude])
    } else {
        magnitude
    }
}
fn refl(value: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(value))
}
fn idiv(divisor: &str, value: &str) -> String {
    term("integer-divides", &[divisor, value])
}
fn not(prop: &str) -> String {
    format!("(#pt-pi ((denied-proof {prop})) #pt-false)")
}
fn ipow(value: &str, exponent: &str) -> String {
    term("integer-power", &[value, exponent])
}
fn sub(first: &str, second: &str) -> String {
    term("integer-add", &[first, &term("integer-negate", &[second])])
}
fn product(first: isize, second: isize, third: isize) -> String {
    term(
        "integer-multiply",
        &[
            &term("integer-multiply", &[&int(first), &int(second)]),
            &int(third),
        ],
    )
}
fn div_expr(divisor: &str, value: &str, quotient: isize, cross: usize) -> String {
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use integer ()))) {})",
        term(
            "integer-equal",
            &[
                value,
                &term("integer-multiply", &[divisor, "candidate-factor"])
            ]
        )
    );
    format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {pred}) introduce ({} {}))",
        int(quotient),
        refl(cross)
    )
}
fn division(divisor: isize, value: isize, quotient: isize) -> String {
    div_expr(
        &int(divisor),
        &int(value),
        quotient,
        (value.max(0) + (-(divisor * quotient)).max(0)) as usize,
    )
}
fn prime(q: usize) -> String {
    term(if q == 3 { "prime-three" } else { "prime-two" }, &[])
}
fn positive(exponent: usize) -> String {
    let pred = format!(
        "(#pt-lambda ((candidate-gap #pt-nat)) (#pt-eq #pt-nat {} {}))",
        n(exponent),
        term("add", &[&n(1), "candidate-gap"])
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {pred}) introduce ({} {}))",
        n(exponent.saturating_sub(1)),
        refl(exponent)
    )
}
fn equation(first: isize, second: isize, third: isize, exponent: usize) -> String {
    let a = first.pow(exponent as u32);
    let b = second.pow(exponent as u32);
    let c = third.pow(exponent as u32);
    refl((a.max(0) + b.max(0) + (-c).max(0)) as usize)
}
fn gcd_one(first: isize, second: isize) -> String {
    let a = int(first);
    let b = int(second);
    let pa = idiv(&int(1), &a);
    let pb = idiv(&int(1), &b);
    let universal = format!(
        "(#pt-pi ((candidate-integer (#pt-use integer ())) (candidate-first {}) (candidate-second {})) {})",
        idiv("candidate-integer", &a), idiv("candidate-integer", &b), idiv("candidate-integer", &int(1))
    );
    let body = if first == 1 {
        "candidate-first".to_owned()
    } else if first == -1 {
        term(
            "integer-divides-negative-target",
            &["candidate-integer", &a, "candidate-first"],
        )
    } else if second == 1 {
        "candidate-second".to_owned()
    } else if second == -1 {
        term(
            "integer-divides-negative-target",
            &["candidate-integer", &b, "candidate-second"],
        )
    } else {
        // Deliberately invalid for the (2,2) negative control.
        "candidate-first".to_owned()
    };
    let proof = format!(
        "(#pt-lambda ((candidate-integer (#pt-use integer ())) (candidate-first {}) (candidate-second {})) {body})",
        idiv("candidate-integer", &a), idiv("candidate-integer", &b)
    );
    let tail = term("conjunction", &[&pb, &universal]);
    term(
        "conjunction-introduce",
        &[
            &pa,
            &tail,
            &division(1, first, first),
            &term(
                "conjunction-introduce",
                &[&pb, &universal, &division(1, second, second), &proof],
            ),
        ],
    )
}
fn c4_value(first: isize, second: isize, exponent: usize) -> String {
    term(
        "frey-integer-c4-value",
        &[&int(first), &int(second), &n(exponent)],
    )
}
fn product_divisor(q: usize, first: isize, second: isize, third: isize, quotient: isize) -> String {
    let value = first * second * third;
    div_expr(
        &int(q as isize),
        &product(first, second, third),
        quotient,
        (value.max(0) + (-((q as isize) * quotient)).max(0)) as usize,
    )
}
fn nondivisor(
    q: usize,
    first: isize,
    second: isize,
    third: isize,
    exponent: usize,
    quotient: isize,
) -> String {
    term(
        "frey-c4-prime-nondivisibility",
        &[
            &n(q),
            &int(first),
            &int(second),
            &int(third),
            &n(exponent),
            &prime(q),
            &positive(exponent),
            &gcd_one(first, second),
            &equation(first, second, third, exponent),
            &product_divisor(q, first, second, third, quotient),
        ],
    )
}

#[test]
fn a_prime_cannot_divide_integer_one() {
    for q in [2, 3] {
        fixture(
            &not(&idiv(&int(q), &int(1))),
            &term(
                "integer-prime-not-divides-one",
                &[&n(q as usize), &prime(q as usize)],
            ),
            true,
        );
    }
}

#[test]
fn signed_positive_power_divisibility_uses_an_actual_positive_exponent() {
    fixture(
        &idiv(&int(2), &ipow(&int(-6), &n(3))),
        &term(
            "integer-divides-positive-power",
            &[&int(2), &int(-6), &n(3), &positive(3), &division(2, -6, -3)],
        ),
        true,
    );
}

#[test]
fn exponent_zero_cannot_forge_positivity_in_the_c4_argument() {
    let value = c4_value(3, 1, 0);
    fixture(
        "#pt-false",
        &term(
            "frey-c4-prime-first-impossible",
            &[
                &n(3),
                &int(3),
                &int(1),
                &n(0),
                &prime(3),
                &positive(0),
                &gcd_one(3, 1),
                &division(3, 3, 1),
                &div_expr(&int(3), &value, 1, 3),
            ],
        ),
        false,
    );
}

#[test]
fn a_forged_gcd_one_certificate_cannot_discard_a_common_prime() {
    let value = c4_value(2, 2, 1);
    fixture(
        "#pt-false",
        &term(
            "frey-c4-prime-first-impossible",
            &[
                &n(2),
                &int(2),
                &int(2),
                &n(1),
                &prime(2),
                &positive(1),
                &gcd_one(2, 2),
                &division(2, 2, 1),
                &div_expr(&int(2), &value, 6, 12),
            ],
        ),
        false,
    );
}

#[test]
fn integer_one_cannot_borrow_a_certificate_for_prime_two() {
    let value = c4_value(1, 1, 1);
    fixture(
        "#pt-false",
        &term(
            "frey-c4-prime-first-impossible",
            &[
                &n(1),
                &int(1),
                &int(1),
                &n(1),
                &prime(1),
                &positive(1),
                &gcd_one(1, 1),
                &division(1, 1, 1),
                &div_expr(&int(1), &value, 3, 3),
            ],
        ),
        false,
    );
}

#[test]
fn all_three_coordinate_prime_divisors_give_actual_c4_nondivisibility() {
    for (q, first, second, third, quotient) in [
        (2, 16, 1, 17, 136),
        (2, -1, 16, 15, -120),
        (3, -1, 16, 15, -80),
    ] {
        fixture(
            &not(&idiv(&int(q as isize), &c4_value(first, second, 1))),
            &nondivisor(q, first, second, third, 1, quotient),
            true,
        );
    }
}

#[test]
fn signed_zero_coordinates_are_retained_in_the_prime_argument() {
    fixture(
        &not(&idiv(&int(3), &c4_value(-1, 0, 1))),
        &nondivisor(3, -1, 0, -1, 1, 0),
        true,
    );
}

#[test]
fn false_power_equations_are_rejected_before_the_c4_conclusion() {
    fixture(
        &not(&idiv(&int(2), &c4_value(-1, 16, 1))),
        &nondivisor(2, -1, 16, 14, 1, -112),
        false,
    );
}

#[test]
fn false_product_divisors_cannot_enter_the_coordinate_case_split() {
    fixture(
        &not(&idiv(&int(3), &c4_value(-1, 16, 1))),
        &nondivisor(3, -1, 16, 15, 1, -79),
        false,
    );
}

#[test]
fn alternate_c4_retains_the_actual_coordinate_power_equation() {
    let first = int(-1);
    let second = int(16);
    let third = int(15);
    let rhs = sub(
        &ipow(&ipow(&third, &n(1)), &n(2)),
        &ipow(&term("integer-multiply", &[&first, &second]), &n(1)),
    );
    fixture(
        &term("integer-equal", &[&c4_value(-1, 16, 1), &rhs]),
        &term(
            "frey-c4-power-equation-alternate",
            &[&first, &second, &third, &n(1), &equation(-1, 16, 15, 1)],
        ),
        true,
    );
}

#[test]
fn rational_alternate_c4_uses_the_exact_doubled_exponent() {
    let curve = term("frey-rational-curve", &[&int(-1), &int(16), &n(1)]);
    let rhs = sub(
        &ipow(&int(15), &term("multiply", &[&n(2), &n(1)])),
        &ipow(&term("integer-multiply", &[&int(-1), &int(16)]), &n(1)),
    );
    let left = term("rational-weierstrass-c4", &[&curve]);
    fixture(
        &term(
            "rational-equal",
            &[&left, &term("rational-of-integer", &[&rhs])],
        ),
        &term(
            "frey-rational-curve-c4-alternate",
            &[
                &int(-1),
                &int(16),
                &int(15),
                &n(1),
                &equation(-1, 16, 15, 1),
            ],
        ),
        true,
    );
}

fn model(zero: bool) -> String {
    term(
        "integer-frey-model",
        &[
            &int(if zero { 0 } else { 4 }),
            &int(if zero { 0 } else { 1 }),
        ],
    )
}
fn model_certificate(zero: bool) -> String {
    term(
        "integer-frey-quotients-map",
        &[
            &int(-1),
            &int(if zero { 0 } else { 16 }),
            &n(1),
            &int(if zero { 0 } else { 4 }),
            &int(if zero { 0 } else { 1 }),
            &refl(if zero { 1 } else { 17 }),
            &refl(if zero { 0 } else { 16 }),
        ],
    )
}
fn integral_c4(zero: bool) -> String {
    term("integer-weierstrass-c4", &[&model(zero)])
}
fn integral_delta(zero: bool) -> String {
    term("integer-weierstrass-discriminant", &[&model(zero)])
}

#[test]
fn actual_integral_alternate_c4_follows_from_the_witnessed_model() {
    let rhs = sub(
        &ipow(&ipow(&int(15), &n(1)), &n(2)),
        &ipow(&term("integer-multiply", &[&int(-1), &int(16)]), &n(1)),
    );
    fixture(
        &term("integer-equal", &[&integral_c4(false), &rhs]),
        &term(
            "integer-frey-c4-alternate",
            &[
                &int(-1),
                &int(16),
                &int(15),
                &n(1),
                &model(false),
                &model_certificate(false),
                &equation(-1, 16, 15, 1),
            ],
        ),
        true,
    );
}

fn integral_nondivisor(q: usize, zero: bool, product_quotient: isize) -> String {
    let second = if zero { 0 } else { 16 };
    let third = if zero { -1 } else { 15 };
    term(
        "integer-frey-c4-prime-nondivisibility",
        &[
            &n(q),
            &int(-1),
            &int(second),
            &int(third),
            &n(1),
            &prime(q),
            &positive(1),
            &gcd_one(-1, second),
            &equation(-1, second, third, 1),
            &model(zero),
            &model_certificate(zero),
            &product_divisor(q, -1, second, third, product_quotient),
        ],
    )
}

#[test]
fn actual_integral_c4_is_not_divisible_by_coordinate_primes() {
    for (q, quotient) in [(2, -120), (3, -80)] {
        fixture(
            &not(&idiv(&int(q as isize), &integral_c4(false))),
            &integral_nondivisor(q, false, quotient),
            true,
        );
    }
}

fn delta_divisor(zero: bool, quotient: isize) -> (String, String) {
    // The actual nonzero model has raw discriminant (289,64), value225;
    // the kernel checks its full polynomial and both cross components.
    let values = if zero { [1, 0, 0, 0] } else { [17, 2, 0, -1] };
    let actual = integral_delta(zero);
    let rendered: Vec<String> = values.iter().map(|v| int(*v)).collect();
    let arguments: Vec<&str> = rendered.iter().map(String::as_str).collect();
    let polynomial = term("integer-weierstrass-discriminant-value", &arguments);
    let mut prelude = String::new();
    for (name, value, cross) in [
        ("b2", values[0], if zero { 1 } else { 17 }),
        ("b4", values[1], if zero { 0 } else { 2 }),
        ("b6", values[2], 0),
        ("b8", values[3], if zero { 0 } else { 1 }),
    ] {
        let ty = term(
            "integer-equal",
            &[
                &term(&format!("integer-weierstrass-{name}"), &[&model(zero)]),
                &int(value),
            ],
        );
        prelude.push_str(&format!(
            "(#math-definition observed-{name} () {ty} {})\n",
            refl(cross)
        ));
    }
    let invariants = term(
        "integer-weierstrass-discriminant-evaluate",
        &[
            &model(zero),
            &int(values[0]),
            &int(values[1]),
            &int(values[2]),
            &int(values[3]),
            &term("observed-b2", &[]),
            &term("observed-b4", &[]),
            &term("observed-b6", &[]),
            &term("observed-b8", &[]),
        ],
    );
    let product = term("integer-multiply", &[&int(3), &int(quotient)]);
    let poly_type = term("integer-equal", &[&polynomial, &product]);
    prelude.push_str(&format!(
        "(#math-definition observed-polynomial () {poly_type} {})\n",
        refl(if zero { 0 } else { 289 })
    ));
    let equality = term(
        "integer-transitive",
        &[
            &actual,
            &polynomial,
            &product,
            &invariants,
            &term("observed-polynomial", &[]),
        ],
    );
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use integer ()))) {})",
        term(
            "integer-equal",
            &[
                &actual,
                &term("integer-multiply", &[&int(3), "candidate-factor"])
            ]
        )
    );
    let delta_type = term("integer-equal", &[&actual, &product]);
    prelude.push_str(&format!(
        "(#math-definition observed-delta () {delta_type} {equality})\n"
    ));
    let proof = format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {pred}) introduce ({} {}))",
        int(quotient),
        term("observed-delta", &[])
    );
    // The constructor consumes the separately checked equality certificate.
    (prelude, proof)
}

#[test]
fn actual_integral_discriminant_prime_divisors_reach_the_coordinate_product() {
    for zero in [true, false] {
        let second = if zero { 0 } else { 16 };
        let third = if zero { -1 } else { 15 };
        let (prelude, divisor) = delta_divisor(zero, if zero { 0 } else { 75 });
        let proof = term(
            "integer-frey-discriminant-prime-divisor",
            &[
                &n(3),
                &int(-1),
                &int(second),
                &int(third),
                &n(1),
                &model(zero),
                &model_certificate(zero),
                &prime(3),
                &equation(-1, second, third, 1),
                &divisor,
            ],
        );
        fixture_with_prelude(
            &prelude,
            &idiv(&int(3), &product(-1, second, third)),
            &proof,
            true,
        );
    }
}

#[test]
fn actual_discriminant_and_c4_have_no_common_prime_divisor() {
    for zero in [true, false] {
        let second = if zero { 0 } else { 16 };
        let third = if zero { -1 } else { 15 };
        let (prelude, divisor) = delta_divisor(zero, if zero { 0 } else { 75 });
        let proof = term(
            "integer-frey-discriminant-c4-prime-disjoint",
            &[
                &n(3),
                &int(-1),
                &int(second),
                &int(third),
                &n(1),
                &prime(3),
                &positive(1),
                &gcd_one(-1, second),
                &equation(-1, second, third, 1),
                &model(zero),
                &model_certificate(zero),
                &divisor,
            ],
        );
        fixture_with_prelude(
            &prelude,
            &not(&idiv(&int(3), &integral_c4(zero))),
            &proof,
            true,
        );
    }
}

#[test]
fn forged_discriminant_quotients_are_actual_proof_mismatches() {
    let (prelude, divisor) = delta_divisor(false, 74);
    let proof = term(
        "integer-frey-discriminant-prime-divisor",
        &[
            &n(3),
            &int(-1),
            &int(16),
            &int(15),
            &n(1),
            &model(false),
            &model_certificate(false),
            &prime(3),
            &equation(-1, 16, 15, 1),
            &divisor,
        ],
    );
    fixture_with_prelude(
        &prelude,
        &idiv(&int(3), &product(-1, 16, 15)),
        &proof,
        false,
    );
}
