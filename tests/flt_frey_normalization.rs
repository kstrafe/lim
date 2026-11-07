//! Concrete Frey-normalization witnesses and forged-premise controls.
#[path = "support/flt_frey_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};

fn n(value: usize) -> String {
    format!("(#pt-numeral {value})")
}
fn refl(value: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(value))
}
fn nat_eq(x: &str, y: &str) -> String {
    format!("(#pt-eq #pt-nat {x} {y})")
}
fn power(x: usize, exponent: usize) -> String {
    term("power", &[&n(x), &n(exponent)])
}
fn nz(value: usize) -> String {
    term("successor-not-zero", &[&n(value - 1)])
}
fn positive(value: usize) -> String {
    term("zero-less-successor", &[&n(value - 1)])
}
fn sol(exponent: usize, a: usize, b: usize, c: usize) -> String {
    term(
        "natural-power-solution",
        &[&n(exponent), &n(a), &n(b), &n(c)],
    )
}
fn solution(exponent: usize, a: usize, b: usize, c: usize) -> String {
    format!(
        "(#pt-construct natural-power-solution () ({} {} {} {}) introduce ({} {} {} {}))",
        n(exponent),
        n(a),
        n(b),
        n(c),
        nz(a),
        nz(b),
        nz(c),
        refl(c.pow(exponent as u32))
    )
}
fn staged_solution(exponent: usize, a: usize, b: usize, c: usize) -> String {
    format!(
        "(#theorem input-solution (#universes) (#parameters) (#statement {}) (#proof {}))\n",
        sol(exponent, a, b, c),
        solution(exponent, a, b, c)
    )
}
fn coprime(a: usize, b: usize) -> String {
    if a == 1 {
        return term("coprime-one-left", &[&n(b)]);
    }
    if b == 1 {
        return term(
            "coprime-symmetric",
            &[&n(1), &n(a), &term("coprime-one-left", &[&n(a)])],
        );
    }
    assert_eq!((a, b), (3, 4));
    let three_one = term(
        "coprime-symmetric",
        &[&n(1), &n(3), &term("coprime-one-left", &[&n(3)])],
    );
    term("coprime-add-left", &[&n(3), &n(1), &three_one])
}
fn staged_coprime(a: usize, b: usize) -> String {
    format!(
        "(#theorem input-coprime (#universes) (#parameters) (#statement {}) (#proof {}))\n",
        term("coprime", &[&n(a), &n(b)]),
        coprime(a, b)
    )
}
fn odd_witness(value: usize, half: usize, evidence: &str) -> String {
    let predicate = format!(
        "(#pt-lambda ((candidate-half #pt-nat)) {})",
        nat_eq(
            &n(value),
            &format!(
                "(#pt-succ {})",
                term("multiply", &[&n(2), "candidate-half"])
            )
        )
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {evidence}))",
        n(half)
    )
}
fn odd(value: usize) -> String {
    odd_witness(value, (value - 1) / 2, &refl(value))
}
fn integer(positive: usize, negative: usize) -> String {
    format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(positive),
        n(negative)
    )
}
fn int(value: isize) -> String {
    if value >= 0 {
        term("integer-of-natural", &[&n(value as usize)])
    } else {
        term("integer-negative-natural", &[&n((-value) as usize)])
    }
}
fn ipow(x: &str, exponent: usize) -> String {
    term("integer-power", &[x, &n(exponent)])
}
fn ineg(x: &str) -> String {
    term("integer-negate", &[x])
}
fn ieq(x: &str, y: &str) -> String {
    term("integer-equal", &[x, y])
}
fn int_not_even(value: isize) -> String {
    let x = int(value);
    let magnitude = value.unsigned_abs();
    let divisor = term("integer-divides", &[&int(2), &x]);
    let naturalized = if value < 0 {
        term(
            "integer-divides-negative-target",
            &[&int(2), &x, "alleged-even"],
        )
    } else {
        "alleged-even".to_string()
    };
    let reflected = term(
        "integer-natural-divisibility-reflects",
        &[&n(2), &n(magnitude), &naturalized],
    );
    format!(
        "(#pt-lambda ((alleged-even {divisor})) {})",
        term(
            "odd-even-exclusion",
            &[&n(magnitude), &odd(magnitude), &reflected]
        )
    )
}

#[test]
fn product_powers_include_zero_and_nontrivial_positive_exponents() {
    for (a, b, exponent) in [(0, 0, 0), (0, 2, 1), (2, 3, 2), (2, 1, 5)] {
        let lhs = term("power", &[&term("multiply", &[&n(a), &n(b)]), &n(exponent)]);
        let rhs = term("multiply", &[&power(a, exponent), &power(b, exponent)]);
        fixture(
            "",
            &nat_eq(&lhs, &rhs),
            &term("power-product", &[&n(a), &n(b), &n(exponent)]),
            true,
        );
    }
}

#[test]
fn positive_power_divisibility_requires_a_real_positive_exponent() {
    for exponent in [1, 3] {
        let result = term("divides", &[&n(2), &power(2, exponent)]);
        let proof = term(
            "divides-positive-power",
            &[
                &n(2),
                &n(2),
                &n(exponent),
                &positive(exponent),
                &term("divides-reflexive", &[&n(2)]),
            ],
        );
        fixture("", &result, &proof, true);
    }
    let result = term("divides", &[&n(2), &power(2, 0)]);
    let proof = term(
        "divides-positive-power",
        &[
            &n(2),
            &n(2),
            &n(0),
            &positive(1),
            &term("divides-reflexive", &[&n(2)]),
        ],
    );
    fixture("", &result, &proof, false);
}

#[test]
fn common_nonzero_factor_cancellation_preserves_the_power_equation() {
    let proof = term(
        "power-remove-common-factor",
        &[
            &n(1),
            &n(2),
            &n(4),
            &n(6),
            &n(2),
            &n(1),
            &n(2),
            &n(3),
            &nz(2),
            &refl(6),
            &refl(2),
            &refl(4),
            &refl(6),
        ],
    );
    let result = nat_eq(&term("add", &[&power(1, 1), &power(2, 1)]), &power(3, 1));
    fixture("", &result, &proof, true);
}

#[test]
fn zero_factor_cannot_cancel_a_false_reduced_equation() {
    let proof = term(
        "power-remove-common-factor",
        &[
            &n(1),
            &n(0),
            &n(0),
            &n(0),
            &n(0),
            &n(1),
            &n(1),
            &n(3),
            &nz(1),
            &refl(0),
            &refl(0),
            &refl(0),
            &refl(0),
        ],
    );
    let result = nat_eq(&term("add", &[&power(1, 1), &power(1, 1)]), &power(3, 1));
    fixture("", &result, &proof, false);
}

#[test]
fn witnessed_common_prime_produces_a_strictly_smaller_solution() {
    let prelude = staged_solution(1, 2, 4, 6);
    let first = term("divides-reflexive", &[&n(2)]);
    let second="(#pt-construct exists (0) (#pt-nat (#pt-lambda ((factor #pt-nat)) (#pt-eq #pt-nat (#pt-numeral 4) (#pt-app (#pt-use multiply ()) (#pt-numeral 2) factor)))) introduce ((#pt-numeral 2) (#pt-refl #pt-nat (#pt-numeral 4))))";
    let proof = term(
        "power-common-prime-descends",
        &[
            &n(1),
            &n(2),
            &n(4),
            &n(6),
            &positive(1),
            &term("input-solution", &[]),
            &n(2),
            &term("prime-two", &[]),
            &first,
            second,
        ],
    );
    fixture(
        &prelude,
        &term("has-smaller-natural-power-solution", &[&n(1), &n(6)]),
        &proof,
        true,
    );
}

#[test]
fn primitive_solutions_are_constructed_for_distinct_exponents() {
    for (exponent, a, b, c) in [(1, 2, 4, 6), (2, 3, 4, 5)] {
        let prelude = staged_solution(exponent, a, b, c);
        let proof = term(
            "natural-power-has-primitive",
            &[
                &n(exponent),
                &n(a),
                &n(b),
                &n(c),
                &positive(exponent),
                &term("input-solution", &[]),
            ],
        );
        fixture(
            &prelude,
            &term("has-natural-primitive-power-solution", &[&n(exponent)]),
            &proof,
            true,
        );
    }
}

#[test]
fn signed_odd_powers_cover_noncanonical_representatives() {
    for (x, exponent) in [(int(2), 1), (int(2), 5), (integer(3, 2), 3)] {
        let result = ieq(&ipow(&ineg(&x), exponent), &ineg(&ipow(&x, exponent)));
        fixture(
            "",
            &result,
            &term(
                "integer-negative-odd-power",
                &[&x, &n(exponent), &odd(exponent)],
            ),
            true,
        );
    }
}

#[test]
fn even_exponents_cannot_use_a_forged_odd_half_witness() {
    let x = int(1);
    let result = ieq(&ipow(&ineg(&x), 2), &ineg(&ipow(&x, 2)));
    fixture(
        "",
        &result,
        &term(
            "integer-negative-odd-power",
            &[&x, &n(2), &odd_witness(2, 0, &refl(2))],
        ),
        false,
    );
}

#[test]
fn even_second_coordinate_normalization_covers_all_three_choices() {
    for (a, b, c) in [(1, 2, 3), (2, 1, 3), (1, 1, 2)] {
        let prelude = staged_solution(1, a, b, c) + &staged_coprime(a, b);
        let proof = term(
            "natural-primitive-power-has-even-signed-packet",
            &[
                &n(1),
                &n(a),
                &n(b),
                &n(c),
                &positive(1),
                &odd(1),
                &term("input-solution", &[]),
                &term("input-coprime", &[]),
            ],
        );
        fixture(
            &prelude,
            &term("has-integer-even-power-packet", &[&n(1)]),
            &proof,
            true,
        );
    }
}

#[test]
fn normalized_sign_preserves_all_packet_evidence() {
    for (a, b, c) in [(1, 2, 3), (3, 4, 7), (1, 1, 2)] {
        let prelude = staged_solution(1, a, b, c) + &staged_coprime(a, b);
        let proof = term(
            "natural-primitive-power-has-normalized-signed-packet",
            &[
                &n(1),
                &n(a),
                &n(b),
                &n(c),
                &positive(1),
                &odd(1),
                &term("input-solution", &[]),
                &term("input-coprime", &[]),
            ],
        );
        fixture(
            &prelude,
            &term("has-normalized-integer-power-packet", &[&n(1)]),
            &proof,
            true,
        );
    }
}

#[test]
fn residue_sign_choice_checks_positive_and_negative_quotients() {
    for value in [1, 3, -1, -3] {
        let x = int(value);
        let result = term(
            "disjunction",
            &[
                &term("integer-three-mod-four", &[&x]),
                &term("integer-three-mod-four", &[&ineg(&x)]),
            ],
        );
        fixture(
            "",
            &result,
            &term(
                "integer-not-even-mod-four-sign-cases",
                &[&x, &int_not_even(value)],
            ),
            true,
        );
    }
}

#[test]
fn residue_sign_adjustment_rejects_an_incorrect_quotient_equation() {
    let result = term("integer-three-mod-four", &[&ineg(&int(1))]);
    let proof = term(
        "integer-negative-one-mod-four-is-three",
        &[&int(1), &int(1), &refl(1)],
    );
    fixture("", &result, &proof, false);
}

#[test]
fn four_remainder_cases_require_a_strict_upper_bound() {
    for value in 0..4 {
        let equality = |v| nat_eq(&n(value), &n(v));
        let result = term(
            "disjunction",
            &[
                &equality(0),
                &term(
                    "disjunction",
                    &[
                        &equality(1),
                        &term("disjunction", &[&equality(2), &equality(3)]),
                    ],
                ),
            ],
        );
        let pred = format!(
            "(#pt-lambda ((gap #pt-nat)) {})",
            nat_eq(
                &n(4),
                &term("add", &[&format!("(#pt-succ {})", n(value)), "gap"])
            )
        );
        let bound = format!(
            "(#pt-construct exists (0) (#pt-nat {pred}) introduce ({} {}))",
            n(3 - value),
            refl(4)
        );
        fixture(
            "",
            &result,
            &term("less-than-four-cases", &[&n(value), &bound]),
            true,
        );
    }
    let equality = |v| nat_eq(&n(4), &n(v));
    let result = term(
        "disjunction",
        &[
            &equality(0),
            &term(
                "disjunction",
                &[
                    &equality(1),
                    &term("disjunction", &[&equality(2), &equality(3)]),
                ],
            ),
        ],
    );
    fixture(
        "",
        &result,
        &term(
            "less-than-four-cases",
            &[&n(4), &term("less-than-successor", &[&n(4)])],
        ),
        false,
    );
}

#[test]
fn frey_exponent_bound_cannot_be_supplied_by_prime_three() {
    let result = term(
        "conjunction",
        &[&term("less-than", &[&n(0), &n(3)]), &term("odd", &[&n(3)])],
    );
    let proof = term(
        "large-prime-positive-and-odd",
        &[
            &n(3),
            &term("prime-three", &[]),
            &term("less-than-successor", &[&n(4)]),
        ],
    );
    fixture("", &result, &proof, false);
}

#[test]
fn final_reduction_cannot_omit_frey_package_refutation() {
    fixture(
        "",
        &term("fermats-last-theorem-statement", &[]),
        &term("fermat-statement-from-frey-refutation", &[]),
        false,
    );
}

#[test]
fn cubic_theorem_cannot_refute_all_frey_packages() {
    fixture(
        "",
        &term("fermats-last-theorem-statement", &[]),
        &term(
            "fermat-statement-from-frey-refutation",
            &[&term("fermat-for-three", &[])],
        ),
        false,
    );
}
