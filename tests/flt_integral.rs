//! Actual quotient/model instances and mismatch controls for the direct source port.
#[path = "support/flt_integral_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};

fn n(value: usize) -> String {
    assert!(value <= 128);
    format!("(#pt-numeral {value})")
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
fn nz(value: usize) -> String {
    term("successor-not-zero", &[&n(value - 1)])
}
fn int_nz(value: isize) -> String {
    assert!(value != 0);
    let proof = term(
        "integer-natural-embedding-nonzero",
        &[&n(value.unsigned_abs()), &nz(value.unsigned_abs())],
    );
    if value < 0 {
        term("integer-negative-nonzero", &[&int(value.abs()), &proof])
    } else {
        proof
    }
}
fn ieq(x: &str, y: &str) -> String {
    term("integer-equal", &[x, y])
}
fn ipow(x: &str, exponent: usize) -> String {
    term("integer-power", &[x, &n(exponent)])
}
fn idiv(d: &str, x: &str) -> String {
    term("integer-divides", &[d, x])
}
fn qeq(x: &str, y: &str) -> String {
    term("rational-equal", &[x, y])
}
fn division(divisor: isize, value: isize, quotient: isize) -> String {
    let d = int(divisor);
    let x = int(value);
    let predicate = format!(
        "(#pt-lambda ((candidate-factor (#pt-use integer ()))) {})",
        ieq(&x, &term("integer-multiply", &[&d, "candidate-factor"]))
    );
    let cross = (value.max(0) + (-(divisor * quotient)).max(0)) as usize;
    format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {predicate}) introduce ({} {}))",
        int(quotient),
        refl(cross)
    )
}
fn strict(lower: usize, upper: usize, gap: usize) -> String {
    let predicate = format!(
        "(#pt-lambda ((candidate-gap #pt-nat)) (#pt-eq #pt-nat {} {}))",
        n(upper),
        term(
            "add",
            &[&format!("(#pt-succ {})", n(lower)), "candidate-gap"]
        )
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        n(gap),
        refl(upper)
    )
}
fn odd(exponent: usize, half: usize) -> String {
    let predicate = format!(
        "(#pt-lambda ((candidate-half #pt-nat)) (#pt-eq #pt-nat {} (#pt-succ {})))",
        n(exponent),
        term("multiply", &[&n(2), "candidate-half"])
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        n(half),
        refl(exponent)
    )
}
fn residue(value: isize, quotient: isize) -> String {
    let predicate = format!(
        "(#pt-lambda ((candidate-quotient (#pt-use integer ()))) {})",
        ieq(
            &int(value),
            &term(
                "integer-add",
                &[
                    &term("integer-multiply", &["candidate-quotient", &int(4)]),
                    &int(3),
                ]
            )
        )
    );
    let cross = (value.max(0) + (-(quotient * 4)).max(0)) as usize;
    format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {predicate}) introduce ({} {}))",
        int(quotient),
        refl(cross)
    )
}

#[test]
fn actual_signed_factors_pass_to_powers_including_zero_exponent() {
    for (divisor, value, quotient, exponent) in [(2, -6, -3, 3), (0, 0, 0, 0)] {
        fixture(
            &idiv(&ipow(&int(divisor), exponent), &ipow(&int(value), exponent)),
            &term(
                "integer-divides-product-powers",
                &[
                    &int(divisor),
                    &int(value),
                    &n(exponent),
                    &division(divisor, value, quotient),
                ],
            ),
            true,
        );
    }
}

#[test]
fn actual_exponent_gaps_construct_signed_prefix_factors() {
    fixture(
        &idiv(&ipow(&int(-2), 2), &ipow(&int(-2), 5)),
        &term(
            "integer-power-strict-prefix-divides",
            &[&int(-2), &n(2), &n(5), &strict(2, 5, 2)],
        ),
        true,
    );
}

#[test]
fn equal_exponents_cannot_forge_a_strict_gap() {
    fixture(
        &idiv(&ipow(&int(2), 2), &ipow(&int(2), 2)),
        &term(
            "integer-power-strict-prefix-divides",
            &[&int(2), &n(2), &n(2), &strict(2, 2, 0)],
        ),
        false,
    );
}

#[test]
fn signed_power_differences_retain_actual_modular_factors() {
    let difference = term(
        "integer-add",
        &[
            &ipow(&int(3), 5),
            &term("integer-negate", &[&ipow(&int(-1), 5)]),
        ],
    );
    fixture(
        &idiv(&int(4), &difference),
        &term(
            "integer-power-difference-divides",
            &[&int(4), &int(3), &int(-1), &n(5), &division(4, 4, 1)],
        ),
        true,
    );
}

#[test]
fn actual_negative_modulo_four_witnesses_produce_divisors() {
    for (value, quotient) in [(-1, -1), (3, 0)] {
        let target = term("integer-add", &[&int(value), &int(1)]);
        fixture(
            &idiv(&int(4), &target),
            &term(
                "integer-three-mod-four-plus-one-divisible",
                &[&int(value), &residue(value, quotient)],
            ),
            true,
        );
    }
}

#[test]
fn actual_odd_powers_preserve_minus_one_modulo_four() {
    let target = term("integer-add", &[&ipow(&int(-1), 5), &int(1)]);
    fixture(
        &idiv(&int(4), &target),
        &term(
            "integer-three-mod-four-odd-power-plus-one-divisible",
            &[&int(-1), &n(5), &odd(5, 2), &residue(-1, -1)],
        ),
        true,
    );
}

#[test]
fn even_exponents_cannot_use_forged_odd_evidence() {
    let target = term("integer-add", &[&ipow(&int(3), 2), &int(1)]);
    fixture(
        &idiv(&int(4), &target),
        &term(
            "integer-three-mod-four-odd-power-plus-one-divisible",
            &[&int(3), &n(2), &odd(2, 0), &residue(3, 0)],
        ),
        false,
    );
}

#[test]
fn large_even_powers_have_actual_sixteen_factors_including_zero() {
    for (value, quotient) in [(-2, -1), (0, 0)] {
        fixture(
            &idiv(&int(16), &ipow(&int(value), 5)),
            &term(
                "integer-even-large-power-divisible-sixteen",
                &[
                    &int(value),
                    &n(5),
                    &strict(4, 5, 0),
                    &division(2, value, quotient),
                ],
            ),
            true,
        );
    }
}

#[test]
fn a_small_power_cannot_forge_the_required_exponent_bound() {
    fixture(
        &idiv(&int(16), &ipow(&int(2), 3)),
        &term(
            "integer-even-large-power-divisible-sixteen",
            &[&int(2), &n(3), &strict(4, 3, 0), &division(2, 2, 1)],
        ),
        false,
    );
}

fn numerators(first: isize, second: isize, exponent: usize) -> (String, String) {
    let a = ipow(&int(first), exponent);
    let b = ipow(&int(second), exponent);
    (
        term(
            "integer-add",
            &[
                &term("integer-add", &[&b, &term("integer-negate", &[&int(1)])]),
                &term("integer-negate", &[&a]),
            ],
        ),
        term("integer-multiply", &[&term("integer-negate", &[&a]), &b]),
    )
}
fn coefficient_divisibility(first: isize, second: isize) -> String {
    term(
        "frey-integral-coefficients-divisible",
        &[
            &int(first),
            &int(second),
            &n(5),
            &strict(4, 5, 0),
            &odd(5, 2),
            &division(2, second, second / 2),
            &residue(first, if first == -1 { -1 } else { 0 }),
        ],
    )
}
fn coefficient_statement(first: isize, second: isize) -> String {
    let (a2, a4) = numerators(first, second, 5);
    term("conjunction", &[&idiv(&int(4), &a2), &idiv(&int(16), &a4)])
}

#[test]
fn actual_frey_coefficient_divisors_retain_both_signed_quotients() {
    fixture(
        &coefficient_statement(-1, 2),
        &coefficient_divisibility(-1, 2),
        true,
    );
}

#[test]
fn false_evenness_cannot_construct_integral_coefficients() {
    fixture(
        &coefficient_statement(-1, 1),
        &coefficient_divisibility(-1, 1),
        false,
    );
}

#[test]
fn false_modulo_four_evidence_cannot_construct_integral_coefficients() {
    fixture(
        &coefficient_statement(1, 2),
        &coefficient_divisibility(1, 2),
        false,
    );
}

#[test]
fn exact_integer_quotients_embed_as_the_actual_signed_fractions() {
    for (numerator, quotient, denominator) in [(32, 8, 4), (-32, -2, 16)] {
        let frac = format!(
            "(#pt-construct rational () () fraction ({} {} {}))",
            int(numerator),
            n(denominator),
            nz(denominator)
        );
        let cross = (numerator.max(0) + (-((denominator as isize) * quotient)).max(0)) as usize;
        fixture(
            &qeq(&term("rational-of-integer", &[&int(quotient)]), &frac),
            &term(
                "rational-exact-integer-quotient",
                &[
                    &int(numerator),
                    &int(quotient),
                    &n(denominator),
                    &nz(denominator),
                    &refl(cross),
                ],
            ),
            true,
        );
    }
}

#[test]
fn inexact_integer_quotients_are_proof_mismatches() {
    let frac = format!(
        "(#pt-construct rational () () fraction ({} {} {}))",
        int(3),
        n(4),
        nz(4)
    );
    fixture(
        &qeq(&term("rational-of-integer", &[&int(0)]), &frac),
        &term(
            "rational-exact-integer-quotient",
            &[&int(3), &int(0), &n(4), &nz(4), &refl(3)],
        ),
        false,
    );
}

fn model(q2: &str, q4: &str) -> String {
    term("integer-frey-model", &[q2, q4])
}
fn certificate(first: isize, second: isize, exponent: usize, model: &str) -> String {
    term(
        "integer-frey-model-certificate",
        &[&int(first), &int(second), &n(exponent), model],
    )
}
fn model_map(
    first: isize,
    second: isize,
    exponent: usize,
    q2: &str,
    q4: &str,
    cross2: usize,
    cross4: usize,
) -> String {
    term(
        "integer-frey-quotients-map",
        &[
            &int(first),
            &int(second),
            &n(exponent),
            q2,
            q4,
            &refl(cross2),
            &refl(cross4),
        ],
    )
}

#[test]
fn actual_integral_model_maps_to_the_exact_rational_coefficients() {
    let model = model(&int(8), &int(2));
    fixture(
        &certificate(-1, 2, 5, &model),
        &model_map(-1, 2, 5, &int(8), &int(2), 33, 32),
        true,
    );
}

#[test]
fn every_wrong_coefficient_quotient_is_a_proof_mismatch() {
    for (q2, q4) in [(7, 2), (8, 1)] {
        let model = model(&int(q2), &int(q4));
        fixture(
            &certificate(-1, 2, 5, &model),
            &model_map(-1, 2, 5, &int(q2), &int(q4), 33, 32),
            false,
        );
    }
}

#[test]
fn actual_coefficient_divisors_construct_an_integral_curve_witness() {
    let predicate = format!(
        "(#pt-lambda ((candidate-model (#pt-use integer-weierstrass-curve ()))) {})",
        certificate(-1, 2, 5, "candidate-model")
    );
    let statement = format!(
        "(#pt-app (#pt-use exists (0)) (#pt-use integer-weierstrass-curve ()) {predicate})"
    );
    let divisors = coefficient_divisibility(-1, 2);
    let first = format!("(#pt-project conjunction 0 {divisors})");
    let second = format!("(#pt-project conjunction 1 {divisors})");
    fixture(
        &statement,
        &term(
            "integer-frey-model-exists",
            &[&int(-1), &int(2), &n(5), &first, &second],
        ),
        true,
    );
}

fn noncanonical_models() -> (String, String, String, String) {
    let q2 = format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(9),
        n(1)
    );
    let q4 = format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(3),
        n(1)
    );
    (
        model(&int(8), &int(2)),
        model(&q2, &q4),
        model_map(-1, 2, 5, &int(8), &int(2), 33, 32),
        model_map(-1, 2, 5, &q2, &q4, 37, 48),
    )
}

#[test]
fn integral_model_uniqueness_respects_actual_integer_equivalence() {
    let (first, second, h1, h2) = noncanonical_models();
    fixture(
        &term("integer-weierstrass-equivalent", &[&first, &second]),
        &term(
            "integer-frey-model-unique",
            &[&int(-1), &int(2), &n(5), &first, &second, &h1, &h2],
        ),
        true,
    );
}

#[test]
fn coefficient_equivalence_does_not_identify_distinct_raw_models() {
    let (first, second, _, _) = noncanonical_models();
    let statement = format!("(#pt-eq (#pt-use integer-weierstrass-curve ()) {first} {second})");
    let proof = format!("(#pt-refl (#pt-use integer-weierstrass-curve ()) {first})");
    fixture(&statement, &proof, false);
}

#[test]
fn actual_integral_c4_reflects_the_signed_rational_identity() {
    let model = model(&int(8), &int(2));
    let a = ipow(&int(-1), 5);
    let b = ipow(&int(2), 5);
    let rhs = term(
        "integer-add",
        &[
            &term(
                "integer-add",
                &[&ipow(&a, 2), &term("integer-multiply", &[&a, &b])],
            ),
            &ipow(&b, 2),
        ],
    );
    fixture(
        &ieq(&term("integer-weierstrass-c4", &[&model]), &rhs),
        &term(
            "integer-frey-c4",
            &[
                &int(-1),
                &int(2),
                &n(5),
                &model,
                &model_map(-1, 2, 5, &int(8), &int(2), 33, 32),
            ],
        ),
        true,
    );
}

fn actual_discriminant_inputs(zero_second: bool) -> (String, String, String, isize, isize, usize) {
    if zero_second {
        let m = model(&int(0), &int(0));
        let h = model_map(-1, 0, 1, &int(0), &int(0), 1, 0);
        (m, h, refl(1), 0, -1, 1)
    } else {
        let m = model(&int(4), &int(1));
        let h = model_map(-1, 16, 1, &int(4), &int(1), 17, 16);
        (m, h, refl(16), 16, 15, 1)
    }
}

#[test]
fn actual_integral_discriminant_retains_the_exact_multiplier_identity() {
    let (model, h, equation, second, third, exponent) = actual_discriminant_inputs(false);
    let left = term(
        "integer-multiply",
        &[
            &term("integer-weierstrass-discriminant", &[&model]),
            &term("integer-of-natural", &[&term("power", &[&n(2), &n(8)])]),
        ],
    );
    let base = term(
        "integer-multiply",
        &[
            &term("integer-multiply", &[&int(-1), &int(second)]),
            &int(third),
        ],
    );
    let right = term(
        "integer-power",
        &[&base, &term("multiply", &[&n(2), &n(exponent)])],
    );
    fixture(
        &ieq(&left, &right),
        &term(
            "integer-frey-discriminant-multiplied",
            &[
                &int(-1),
                &int(second),
                &int(third),
                &n(exponent),
                &model,
                &h,
                &equation,
            ],
        ),
        true,
    );
}

#[test]
fn actual_integral_discriminant_nonzero_requires_all_coordinates() {
    for zero_second in [false, true] {
        let (model, h, equation, second, third, exponent) = actual_discriminant_inputs(zero_second);
        let statement = format!(
            "(#pt-pi ((zero-discriminant {})) #pt-false)",
            ieq(
                &term("integer-weierstrass-discriminant", &[&model]),
                &int(0)
            )
        );
        let proof = term(
            "integer-frey-discriminant-nonzero",
            &[
                &int(-1),
                &int(second),
                &int(third),
                &n(exponent),
                &model,
                &h,
                &equation,
                &int_nz(-1),
                &int_nz(if second == 0 { 1 } else { second }),
                &int_nz(third),
            ],
        );
        fixture(&statement, &proof, !zero_second);
    }
}
