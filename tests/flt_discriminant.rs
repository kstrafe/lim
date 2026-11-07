//! Concrete checks and genuine mismatch controls for the native Frey port.
#[path = "support/flt_discriminant_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};

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
fn nz(value: usize) -> String {
    assert!(value > 0);
    term("successor-not-zero", &[&n(value - 1)])
}
fn int_nz(value: isize) -> String {
    assert!(value != 0);
    let magnitude = term(
        "integer-natural-embedding-nonzero",
        &[&n(value.unsigned_abs()), &nz(value.unsigned_abs())],
    );
    if value < 0 {
        term("integer-negative-nonzero", &[&int(value.abs()), &magnitude])
    } else {
        magnitude
    }
}
fn fraction(numerator: &str, denominator: &str, nonzero: &str) -> String {
    format!("(#pt-construct rational () () fraction ({numerator} {denominator} {nonzero}))")
}
fn ratio(value: isize, denominator: usize) -> String {
    fraction(&int(value), &n(denominator), &nz(denominator))
}
fn embed(value: isize) -> String {
    term("rational-of-integer", &[&int(value)])
}
fn qeq(left: &str, right: &str) -> String {
    term("rational-equal", &[left, right])
}
fn nonzero(value: &str) -> String {
    format!(
        "(#pt-pi ((zero-evidence {})) #pt-false)",
        qeq(value, &term("rational-zero", &[]))
    )
}
fn fraction_nz(value: &str, numerator: isize) -> String {
    term("rational-fraction-nonzero", &[value, &int_nz(numerator)])
}
fn refl(value: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(value))
}

#[test]
fn sign_laws_handle_actual_signed_fractions() {
    let x = ratio(-2, 3);
    let y = ratio(3, 5);
    let left = term(
        "rational-multiply",
        &[
            &term("rational-negate", &[&x]),
            &term("rational-negate", &[&y]),
        ],
    );
    let right = term("rational-multiply", &[&x, &y]);
    fixture(
        &qeq(&left, &right),
        &term("rational-multiply-two-negatives", &[&x, &y]),
        true,
    );
}

#[test]
fn product_powers_handle_zero_and_odd_exponents() {
    let x = ratio(-2, 3);
    let y = ratio(1, 5);
    for exponent in [0, 3] {
        let left = term(
            "rational-power",
            &[&term("rational-multiply", &[&x, &y]), &n(exponent)],
        );
        let right = term(
            "rational-multiply",
            &[
                &term("rational-power", &[&x, &n(exponent)]),
                &term("rational-power", &[&y, &n(exponent)]),
            ],
        );
        fixture(
            &qeq(&left, &right),
            &term("rational-power-product", &[&x, &y, &n(exponent)]),
            true,
        );
    }
}

#[test]
fn actual_fraction_square_retains_the_nonzero_denominator() {
    let value = ratio(-2, 3);
    let squared_numerator = term("integer-power", &[&int(-2), &n(2)]);
    let squared_denominator = term("multiply", &[&n(3), &n(3)]);
    let denominator_nz = term("multiply-nonzero", &[&n(3), &n(3), &nz(3), &nz(3)]);
    let right = fraction(&squared_numerator, &squared_denominator, &denominator_nz);
    fixture(
        &qeq(&term("rational-power", &[&value, &n(2)]), &right),
        &term("rational-fraction-square", &[&int(-2), &n(3), &nz(3)]),
        true,
    );
}

#[test]
fn signed_integer_times_a_fraction_retains_its_actual_denominator() {
    let value = ratio(-2, 3);
    let right = fraction(
        &term("integer-multiply", &[&int(-2), &int(-5)]),
        &n(3),
        &nz(3),
    );
    fixture(
        &qeq(&term("rational-multiply", &[&value, &embed(-5)]), &right),
        &term(
            "rational-fraction-times-integer",
            &[&int(-2), &n(3), &int(-5), &nz(3)],
        ),
        true,
    );
}

#[test]
fn squared_integer_powers_keep_the_exact_doubled_exponent() {
    for exponent in [0, 3] {
        let left = term(
            "integer-power",
            &[&term("integer-power", &[&int(-2), &n(exponent)]), &n(2)],
        );
        let right = term(
            "integer-power",
            &[&int(-2), &term("multiply", &[&n(2), &n(exponent)])],
        );
        let statement = term("integer-equal", &[&left, &right]);
        fixture(
            &statement,
            &term("integer-power-square", &[&int(-2), &n(exponent)]),
            true,
        );
    }
}

fn zero_curve(third_coefficient: &str) -> String {
    let zero = term("rational-zero", &[]);
    format!("(#pt-construct rational-weierstrass-curve () () coefficients ({zero} {zero} {third_coefficient} {zero} {zero}))")
}
fn reduced_discriminant(curve: &str) -> String {
    let b2 = term("rational-weierstrass-b2", &[curve]);
    let b4 = term("rational-weierstrass-b4", &[curve]);
    let b8 = term("rational-weierstrass-b8", &[curve]);
    let first = term(
        "rational-multiply",
        &[
            &term("rational-negate", &[&term("rational-power", &[&b2, &n(2)])]),
            &b8,
        ],
    );
    let second = term(
        "rational-multiply",
        &[&embed(8), &term("rational-power", &[&b4, &n(3)])],
    );
    term(
        "rational-add",
        &[&first, &term("rational-negate", &[&second])],
    )
}

#[test]
fn zero_sixth_invariant_reduction_accepts_actual_evidence() {
    let zero = term("rational-zero", &[]);
    let curve = zero_curve(&zero);
    let sixth = term("rational-weierstrass-b6", &[&curve]);
    let statement = qeq(
        &term("rational-weierstrass-discriminant", &[&curve]),
        &reduced_discriminant(&curve),
    );
    fixture(
        &statement,
        &term(
            "weierstrass-discriminant-zero-b6",
            &[&curve, &term("rational-reflexive", &[&sixth])],
        ),
        true,
    );
}

#[test]
fn nonzero_sixth_invariant_cannot_use_forged_zero_evidence() {
    let curve = zero_curve(&term("rational-one", &[]));
    let statement = qeq(
        &term("rational-weierstrass-discriminant", &[&curve]),
        &reduced_discriminant(&curve),
    );
    fixture(
        &statement,
        &term("weierstrass-discriminant-zero-b6", &[&curve, &refl(0)]),
        false,
    );
}

fn curve(first: isize, second: isize, exponent: usize) -> String {
    term(
        "frey-rational-curve",
        &[&int(first), &int(second), &n(exponent)],
    )
}
fn discriminant(first: isize, second: isize, exponent: usize) -> String {
    term(
        "rational-weierstrass-discriminant",
        &[&curve(first, second, exponent)],
    )
}
fn expected_discriminant(first: isize, second: isize, third: isize, exponent: usize) -> String {
    let base = term(
        "integer-multiply",
        &[
            &term("integer-multiply", &[&int(first), &int(second)]),
            &int(third),
        ],
    );
    let numerator = term(
        "integer-power",
        &[&base, &term("multiply", &[&n(2), &n(exponent)])],
    );
    let denominator = term("power", &[&n(2), &n(8)]);
    let nonzero = term("power-nonzero", &[&n(2), &n(8), &nz(2)]);
    fraction(&numerator, &denominator, &nonzero)
}
fn equation(first: isize, second: isize, third: isize, exponent: usize) -> String {
    let first = first.pow(exponent as u32);
    let second = second.pow(exponent as u32);
    let third = third.pow(exponent as u32);
    // The native checker validates the opposite cross component itself.
    refl((first.max(0) + second.max(0) + (-third).max(0)) as usize)
}
fn formula(first: isize, second: isize, third: isize, exponent: usize) -> String {
    term(
        "frey-rational-curve-discriminant",
        &[
            &int(first),
            &int(second),
            &int(third),
            &n(exponent),
            &equation(first, second, third, exponent),
        ],
    )
}

#[test]
fn exact_discriminant_formula_accepts_actual_positive_coordinates() {
    fixture(
        &qeq(&discriminant(1, 1, 1), &expected_discriminant(1, 1, 2, 1)),
        &formula(1, 1, 2, 1),
        true,
    );
}

#[test]
fn exact_discriminant_formula_accepts_actual_opposite_signed_coordinates() {
    fixture(
        &qeq(&discriminant(2, -1, 1), &expected_discriminant(2, -1, 1, 1)),
        &formula(2, -1, 1, 1),
        true,
    );
}

fn concrete_discriminant_value(expected_numerator: isize, valid: bool) {
    let left = discriminant(1, 1, 1);
    let middle = expected_discriminant(1, 1, 2, 1);
    let right = ratio(expected_numerator, 64);
    let proof = term(
        "rational-transitive",
        &[&left, &middle, &right, &formula(1, 1, 2, 1), &refl(256)],
    );
    fixture(&qeq(&left, &right), &proof, valid);
}

#[test]
fn actual_frey_discriminant_has_value_one_over_sixty_four() {
    concrete_discriminant_value(1, true);
}

#[test]
fn wrong_actual_discriminant_value_is_a_proof_mismatch() {
    concrete_discriminant_value(2, false);
}

#[test]
fn false_coordinate_power_equation_is_a_proof_mismatch() {
    fixture(
        &qeq(&discriminant(1, 1, 1), &expected_discriminant(1, 1, 1, 1)),
        &formula(1, 1, 1, 1),
        false,
    );
}

fn discriminant_nz(first: isize, second: isize, third: isize) -> String {
    term(
        "frey-rational-curve-discriminant-nonzero",
        &[
            &int(first),
            &int(second),
            &int(third),
            &n(1),
            &equation(first, second, third, 1),
            &int_nz(if first == 0 { 1 } else { first }),
            &int_nz(if second == 0 { 1 } else { second }),
            &int_nz(if third == 0 { 1 } else { third }),
        ],
    )
}

#[test]
fn nonzero_discriminant_uses_the_actual_signed_nonzero_coordinates() {
    fixture(
        &nonzero(&discriminant(2, -1, 1)),
        &discriminant_nz(2, -1, 1),
        true,
    );
}

#[test]
fn every_zero_coordinate_rejects_forged_nonzero_evidence() {
    for (first, second, third) in [(0, 1, 1), (1, 0, 1), (1, -1, 0)] {
        fixture(
            &nonzero(&discriminant(first, second, 1)),
            &discriminant_nz(first, second, third),
            false,
        );
    }
}

#[test]
fn nonzero_rationals_construct_actual_two_sided_inverse_witnesses() {
    for numerator in [2, -2] {
        let value = ratio(numerator, 3);
        fixture(
            &term("rational-is-unit", &[&value]),
            &term(
                "rational-nonzero-is-unit",
                &[&value, &fraction_nz(&value, numerator)],
            ),
            true,
        );
    }
}

#[test]
fn actual_two_sided_units_are_nonzero() {
    let value = ratio(-2, 3);
    let unit = term(
        "rational-nonzero-is-unit",
        &[&value, &fraction_nz(&value, -2)],
    );
    fixture(
        &nonzero(&value),
        &term("rational-unit-is-nonzero", &[&value, &unit]),
        true,
    );
}

#[test]
fn inverse_witnesses_cover_noncanonical_signed_numerators() {
    let numerator = format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(4),
        n(2)
    );
    let value = fraction(&numerator, &n(3), &nz(3));
    let zero = term("integer-zero", &[]);
    let raw_zero = term("integer-equal", &[&numerator, &zero]);
    let two_to_raw = term("integer-symmetric", &[&numerator, &int(2), &refl(4)]);
    let two_to_zero = term(
        "integer-transitive",
        &[&int(2), &numerator, &zero, &two_to_raw, "zero-numerator"],
    );
    let numerator_nz = format!(
        "(#pt-lambda ((zero-numerator {raw_zero})) (#pt-app {} {two_to_zero}))",
        int_nz(2)
    );
    let value_nz = term("rational-fraction-nonzero", &[&value, &numerator_nz]);
    fixture(
        &term("rational-is-unit", &[&value]),
        &term("rational-nonzero-is-unit", &[&value, &value_nz]),
        true,
    );
}

#[test]
fn zero_cannot_use_a_forged_nonzero_certificate_to_construct_a_unit() {
    let zero = term("rational-zero", &[]);
    let one = term("rational-one", &[]);
    fixture(
        &term("rational-is-unit", &[&zero]),
        &term("rational-nonzero-is-unit", &[&zero, &fraction_nz(&one, 1)]),
        false,
    );
}

#[test]
fn missing_reverse_inverse_equation_does_not_construct_a_unit() {
    let value = embed(1);
    let inverse = term("rational-one", &[]);
    let product = term("rational-multiply", &[&value, &inverse]);
    let predicate = format!(
        "(#pt-lambda ((candidate-inverse (#pt-use rational ()))) (#pt-app (#pt-use conjunction ()) {} {}))",
        qeq(&term("rational-multiply", &[&value, "candidate-inverse"]), &inverse),
        qeq(&term("rational-multiply", &["candidate-inverse", &value]), &inverse),
    );
    let proof = format!(
        "(#pt-construct exists (0) ((#pt-use rational ()) {predicate}) introduce ({inverse} {}))",
        term("rational-reflexive", &[&product]),
    );
    fixture(&term("rational-is-unit", &[&value]), &proof, false);
}

#[test]
fn exact_nonzero_frey_discriminant_constructs_an_ellipticity_certificate() {
    let curve = curve(1, 1, 1);
    fixture(
        &term("rational-weierstrass-is-elliptic", &[&curve]),
        &term(
            "rational-weierstrass-nonzero-discriminant-is-elliptic",
            &[&curve, &discriminant_nz(1, 1, 2)],
        ),
        true,
    );
}

#[test]
fn zero_discriminant_cannot_use_forged_ellipticity_evidence() {
    let zero = term("rational-zero", &[]);
    let one = term("rational-one", &[]);
    let curve = zero_curve(&zero);
    let delta = term("rational-weierstrass-discriminant", &[&curve]);
    // Keep the large discriminant expression identical in the premise type.
    // The attempted false body must fail on its closed 1=0 certificate;
    // exhausting the work budget while comparing curve values cannot pass.
    let forged_nonzero = format!(
        "(#pt-lambda ((zero-discriminant {})) (#pt-app {} {}))",
        qeq(&delta, &zero),
        fraction_nz(&one, 1),
        refl(0)
    );
    fixture(
        &term("rational-weierstrass-is-elliptic", &[&curve]),
        &term(
            "rational-weierstrass-nonzero-discriminant-is-elliptic",
            &[&curve, &forged_nonzero],
        ),
        false,
    );
}
