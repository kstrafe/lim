//! Concrete and adversarial local valuation certificates checked by the native kernel.
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
fn refl(value: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(value))
}
fn eq(left: &str, right: &str) -> String {
    format!("(#pt-eq #pt-nat {left} {right})")
}
fn not(p: &str) -> String {
    format!("(#pt-pi ((denied-proof {p})) #pt-false)")
}
fn both(p: &str, q: &str, hp: &str, hq: &str) -> String {
    term("conjunction-introduce", &[p, q, hp, hq])
}
fn int(value: isize) -> String {
    term(
        if value < 0 {
            "integer-negative-natural"
        } else {
            "integer-of-natural"
        },
        &[&n(value.unsigned_abs())],
    )
}
fn raw(positive: usize, negative: usize) -> String {
    format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(positive),
        n(negative)
    )
}
fn prime(q: usize) -> String {
    term(if q == 3 { "prime-three" } else { "prime-two" }, &[])
}
fn dvd(q: usize, value: &str) -> String {
    term("divides", &[&n(q), value])
}
fn nv(q: usize, value: &str, k: usize) -> String {
    term("natural-prime-order", &[&n(q), value, &n(k)])
}
fn iv(q: usize, value: &str, k: usize) -> String {
    term("integer-prime-order", &[&n(q), &n(k), value])
}
fn nonzero(value: usize) -> String {
    term("successor-not-zero", &[&n(value.saturating_sub(1))])
}
fn nondivisor(q: usize, value: usize) -> String {
    let remainder = value % q;
    let divisor = term("multiply", &[&n(q), &n(value / q)]);
    let predicate = format!(
        "(#pt-lambda ((candidate-factor #pt-nat)) {})",
        eq(&divisor, &term("multiply", &[&n(q), "candidate-factor"]))
    );
    let factor = format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        n(value / q),
        refl(value - remainder)
    );
    let proof = term(
        "divides-add-cancel-left",
        &[&n(q), &divisor, &n(remainder), &factor, "denied-divisor"],
    );
    let exclusion = term(
        if q == 2 {
            "two-not-divides-one"
        } else if remainder == 2 {
            "three-not-divides-two"
        } else {
            "three-not-divides-one"
        },
        &[],
    );
    // A divisible candidate deliberately supplies an invalid remainder exclusion.
    format!(
        "(#pt-lambda ((denied-divisor {})) (#pt-app {exclusion} {proof}))",
        dvd(q, &n(value))
    )
}
fn natural_order(q: usize, value: usize, k: usize, cofactor: usize) -> String {
    let power = term("power", &[&n(q), &n(k)]);
    let pred = format!(
        "(#pt-lambda ((candidate-cofactor #pt-nat)) {})",
        term(
            "conjunction",
            &[
                &eq(
                    &n(value),
                    &term("multiply", &[&power, "candidate-cofactor"])
                ),
                &not(&dvd(q, "candidate-cofactor"))
            ]
        )
    );
    let packet = both(
        &eq(&n(value), &term("multiply", &[&power, &n(cofactor)])),
        &not(&dvd(q, &n(cofactor))),
        &refl(value),
        &nondivisor(q, cofactor),
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {pred}) introduce ({} {packet}))",
        n(cofactor)
    )
}
fn magnitude(value: &str, positive: usize, negative: usize) -> String {
    let m = positive.abs_diff(negative);
    let p = term("integer-equal", &[value, &int(m as isize)]);
    let q = term("integer-equal", &[value, &int(-(m as isize))]);
    term(
        if positive >= negative {
            "disjunction-left"
        } else {
            "disjunction-right"
        },
        &[&p, &q, &refl(positive.max(negative))],
    )
}
fn signed_order(
    q: usize,
    value: &str,
    positive: usize,
    negative: usize,
    k: usize,
    cofactor: usize,
) -> String {
    let m = positive.abs_diff(negative);
    format!(
        "(#pt-construct integer-prime-order () ({} {} {value}) introduce ({} {} {}))",
        n(q),
        n(k),
        n(m),
        natural_order(q, m, k, cofactor),
        magnitude(value, positive, negative)
    )
}
fn has_natural(q: usize, value: usize) -> String {
    format!(
        "(#pt-app (#pt-use exists (0)) #pt-nat (#pt-lambda ((candidate-order #pt-nat)) {}))",
        term(
            "natural-prime-order",
            &[&n(q), &n(value), "candidate-order"]
        )
    )
}
fn has_integer(q: usize, value: &str) -> String {
    format!(
        "(#pt-app (#pt-use exists (0)) #pt-nat (#pt-lambda ((candidate-order #pt-nat)) {}))",
        term("integer-prime-order", &[&n(q), "candidate-order", value])
    )
}

#[test]
fn every_nonzero_natural_has_a_valuation() {
    for (q, value) in [(2, 1), (2, 12), (2, 24), (3, 18)] {
        fixture(
            &has_natural(q, value),
            &term(
                "natural-prime-order-exists",
                &[&n(q), &n(value), &prime(q), &nonzero(value)],
            ),
            true,
        );
    }
}
#[test]
fn zero_and_composite_numbers_cannot_borrow_existence_evidence() {
    for (q, value) in [(2, 0), (4, 12)] {
        fixture(
            &has_natural(q, value),
            &term(
                "natural-prime-order-exists",
                &[&n(q), &n(value), &prime(q), &nonzero(value)],
            ),
            false,
        );
    }
}
#[test]
fn actual_dividing_power_and_excluded_successor_are_checked() {
    let order = natural_order(2, 24, 3, 3);
    fixture(
        &dvd(8, &n(24)),
        &term(
            "natural-prime-order-power-divides",
            &[&n(2), &n(24), &n(3), &order],
        ),
        true,
    );
    fixture(
        &not(&dvd(16, &n(24))),
        &term(
            "natural-prime-order-next-nondivisor",
            &[&n(2), &n(24), &n(3), &prime(2), &order],
        ),
        true,
    );
}
#[test]
fn natural_valuation_uniqueness_rejects_a_forged_index() {
    let order = natural_order(2, 24, 3, 3);
    for other in [3, 4] {
        fixture(
            &eq(&n(3), &n(other)),
            &term(
                "natural-prime-order-unique",
                &[&n(2), &n(24), &n(3), &n(other), &prime(2), &order, &order],
            ),
            other == 3,
        );
    }
}
#[test]
fn factor_equations_and_cofactor_nondivisibility_are_required() {
    fixture(&nv(2, &n(12), 3), &natural_order(2, 12, 3, 3), false);
    fixture(&nv(2, &n(24), 2), &natural_order(2, 24, 2, 6), false);
}
#[test]
fn natural_product_valuations_add() {
    let product = term("multiply", &[&n(12), &n(10)]);
    fixture(
        &nv(2, &product, 3),
        &term(
            "natural-prime-order-multiply",
            &[
                &n(2),
                &n(12),
                &n(10),
                &n(2),
                &n(1),
                &prime(2),
                &natural_order(2, 12, 2, 3),
                &natural_order(2, 10, 1, 5),
            ],
        ),
        true,
    );
}
#[test]
fn natural_power_valuations_include_exponent_zero() {
    for exponent in [0, 1, 3] {
        fixture(
            &nv(3, &term("power", &[&n(6), &n(exponent)]), exponent),
            &term(
                "natural-prime-order-power",
                &[
                    &n(3),
                    &n(6),
                    &n(1),
                    &n(exponent),
                    &prime(3),
                    &natural_order(3, 6, 1, 2),
                ],
            ),
            true,
        );
    }
}
#[test]
fn signed_existence_covers_noncanonical_representatives() {
    for (p, nv) in [(17, 5), (5, 17)] {
        let value = raw(p, nv);
        let m = p.abs_diff(nv);
        let nz = term(
            "integer-nonzero-of-magnitude",
            &[&value, &n(m), &magnitude(&value, p, nv), &nonzero(m)],
        );
        fixture(
            &has_integer(2, &value),
            &term(
                "integer-prime-order-exists",
                &[&n(2), &value, &prime(2), &nz],
            ),
            true,
        );
    }
}
#[test]
fn integer_equivalence_preserves_the_valuation() {
    let value = raw(17, 5);
    fixture(
        &iv(2, &int(12), 2),
        &term(
            "integer-prime-order-congruent",
            &[
                &n(2),
                &value,
                &int(12),
                &n(2),
                &refl(17),
                &signed_order(2, &value, 17, 5, 2, 3),
            ],
        ),
        true,
    );
}
#[test]
fn signed_uniqueness_requires_the_actual_index() {
    let value = raw(5, 17);
    let order = signed_order(2, &value, 5, 17, 2, 3);
    for other in [2, 3] {
        fixture(
            &eq(&n(2), &n(other)),
            &term(
                "integer-prime-order-unique",
                &[&n(2), &value, &n(2), &n(other), &prime(2), &order, &order],
            ),
            other == 2,
        );
    }
}
#[test]
fn signed_product_and_power_valuations_follow_actual_magnitudes() {
    let a = int(-12);
    let b = int(10);
    fixture(
        &iv(2, &term("integer-multiply", &[&a, &b]), 3),
        &term(
            "integer-prime-order-multiply",
            &[
                &n(2),
                &a,
                &b,
                &n(2),
                &n(1),
                &prime(2),
                &signed_order(2, &a, 0, 12, 2, 3),
                &signed_order(2, &b, 10, 0, 1, 5),
            ],
        ),
        true,
    );
    for exponent in [0, 1, 2, 3] {
        fixture(
            &iv(
                3,
                &term("integer-power", &[&int(-6), &n(exponent)]),
                exponent,
            ),
            &term(
                "integer-prime-order-power",
                &[
                    &n(3),
                    &int(-6),
                    &n(1),
                    &n(exponent),
                    &prime(3),
                    &signed_order(3, &int(-6), 0, 6, 1, 2),
                ],
            ),
            true,
        );
    }
}
#[test]
fn signed_cofactor_witnesses_preserve_sign_and_nondivisibility() {
    for (p, m) in [(17, 5), (5, 17)] {
        let value = raw(p, m);
        let pred = format!(
            "(#pt-lambda ((candidate-factor (#pt-use integer ()))) {})",
            term(
                "conjunction",
                &[
                    &term(
                        "integer-equal",
                        &[
                            &value,
                            &term(
                                "integer-multiply",
                                &[
                                    &term("integer-power", &[&int(2), &n(2)]),
                                    "candidate-factor"
                                ]
                            )
                        ]
                    ),
                    &not(&term("integer-divides", &[&int(2), "candidate-factor"]))
                ]
            )
        );
        let statement = format!("(#pt-app (#pt-use exists (0)) (#pt-use integer ()) {pred})");
        fixture(
            &statement,
            &term(
                "integer-prime-order-cofactor",
                &[&n(2), &value, &n(2), &signed_order(2, &value, p, m, 2, 3)],
            ),
            true,
        );
    }
}
#[test]
fn zero_cannot_carry_a_signed_prime_valuation() {
    fixture(
        &iv(2, &int(0), 0),
        &signed_order(2, &int(0), 0, 0, 0, 0),
        false,
    );
}

fn model() -> String {
    term("integer-frey-model", &[&int(4), &int(1)])
}
fn model_certificate() -> String {
    term(
        "integer-frey-quotients-map",
        &[
            &int(-1),
            &int(16),
            &n(1),
            &int(4),
            &int(1),
            &refl(17),
            &refl(16),
        ],
    )
}
fn delta() -> String {
    term("integer-weierstrass-discriminant", &[&model()])
}
fn coordinates() -> String {
    term(
        "integer-multiply",
        &[&term("integer-multiply", &[&int(-1), &int(16)]), &int(15)],
    )
}
fn definition(name: &str, ty: &str, value: &str) -> String {
    format!("(#theorem {name} (#universes) (#parameters) (#statement {ty}) (#proof {value}))\n")
}
fn not_two(q: usize) -> String {
    let once = term("successor-injective", &[&n(q - 1), &n(1), "equal-to-two"]);
    let twice = term("successor-injective", &[&n(q - 2), &n(0), &once]);
    // q=2 deliberately tries to infer False from 0=0; q=3 is genuine.
    format!(
        "(#pt-lambda ((equal-to-two {})) (#pt-app {} {twice}))",
        eq(&n(q), &n(2)),
        term("successor-not-zero", &[&n(0)])
    )
}
fn frey_fixture(q: usize, wrong_result: bool, wrong_index: bool, wrong_equation: bool) {
    frey_fixture_kind(q, wrong_result, wrong_index, wrong_equation, false);
}

fn frey_fixture_kind(
    q: usize,
    wrong_result: bool,
    wrong_index: bool,
    wrong_equation: bool,
    at_two: bool,
) {
    let (kd, kc) = if q == 3 { (2, 1) } else { (0, 4) };
    let mut prelude = String::new();
    for (name, value, cross) in [("b2", 17, 17), ("b4", 2, 2), ("b6", 0, 0), ("b8", -1, 1)] {
        let ty = term(
            "integer-equal",
            &[
                &term(&format!("integer-weierstrass-{name}"), &[&model()]),
                &int(value),
            ],
        );
        prelude.push_str(&definition(&format!("observed-{name}"), &ty, &refl(cross)));
    }
    let polynomial = term(
        "integer-weierstrass-discriminant-value",
        &[&int(17), &int(2), &int(0), &int(-1)],
    );
    prelude.push_str(&definition(
        "observed-polynomial",
        &term("integer-equal", &[&polynomial, &int(225)]),
        &refl(289),
    ));
    let evaluated = term(
        "integer-weierstrass-discriminant-evaluate",
        &[
            &model(),
            &int(17),
            &int(2),
            &int(0),
            &int(-1),
            &term("observed-b2", &[]),
            &term("observed-b4", &[]),
            &term("observed-b6", &[]),
            &term("observed-b8", &[]),
        ],
    );
    let equivalence = term(
        "integer-transitive",
        &[
            &delta(),
            &polynomial,
            &int(225),
            &evaluated,
            &term("observed-polynomial", &[]),
        ],
    );
    prelude.push_str(&definition(
        "observed-delta",
        &term("integer-equal", &[&delta(), &int(225)]),
        &equivalence,
    ));
    prelude.push_str(&definition(
        "observed-delta-natural-order",
        &nv(q, &n(225), kd),
        &natural_order(q, 225, kd, if q == 3 { 25 } else { 225 }),
    ));
    prelude.push_str(&definition(
        "observed-coordinate-natural-order",
        &nv(q, &n(240), kc),
        &natural_order(q, 240, kc, if q == 3 { 80 } else { 15 }),
    ));
    let mag = term(
        "disjunction-left",
        &[
            &term("integer-equal", &[&delta(), &int(225)]),
            &term("integer-equal", &[&delta(), &int(-225)]),
            &term("observed-delta", &[]),
        ],
    );
    let delta_order = format!(
        "(#pt-construct integer-prime-order () ({} {} {}) introduce ({} {} {mag}))",
        n(q),
        n(kd),
        delta(),
        n(225),
        term("observed-delta-natural-order", &[])
    );
    prelude.push_str(&definition(
        "observed-delta-order",
        &iv(q, &delta(), kd),
        &delta_order,
    ));
    let cmag = magnitude(&coordinates(), 0, 240);
    let coordinate_order = format!(
        "(#pt-construct integer-prime-order () ({} {} {}) introduce ({} {} {cmag}))",
        n(q),
        n(kc),
        coordinates(),
        n(240),
        term("observed-coordinate-natural-order", &[])
    );
    prelude.push_str(&definition(
        "observed-coordinate-order",
        &iv(q, &coordinates(), kc),
        &coordinate_order,
    ));
    prelude.push_str(&definition(
        "observed-model-certificate",
        &term(
            "integer-frey-model-certificate",
            &[&int(-1), &int(16), &n(1), &model()],
        ),
        &model_certificate(),
    ));
    let coordinate_equation = term(
        "integer-equal",
        &[
            &term(
                "integer-add",
                &[
                    &term("integer-power", &[&int(-1), &n(1)]),
                    &term("integer-power", &[&int(16), &n(1)]),
                ],
            ),
            &term("integer-power", &[&int(15), &n(1)]),
        ],
    );
    prelude.push_str(&definition(
        "observed-equation",
        &coordinate_equation,
        &refl(if wrong_equation { 15 } else { 16 }),
    ));
    let binders = format!(
        "((delta-index #pt-nat) (coordinate-index #pt-nat) (delta-evidence {}) (coordinate-evidence {}))",
        term("integer-prime-order", &[&n(q), "delta-index", &delta()]),
        term("integer-prime-order", &[&n(q), "coordinate-index", &coordinates()]),
    );
    let rule_left = if at_two {
        term("add", &["delta-index", &n(8)])
    } else {
        "delta-index".to_owned()
    };
    let rule_type = format!(
        "(#pt-pi {binders} {})",
        eq(
            &rule_left,
            &term(
                "multiply",
                &[&term("multiply", &[&n(2), &n(1)]), "coordinate-index"]
            )
        )
    );
    let rule_body = if at_two {
        term(
            "integer-frey-discriminant-valuation-at-two",
            &[
                &int(-1),
                &int(16),
                &int(15),
                &n(1),
                &model(),
                &term("observed-model-certificate", &[]),
                &term("observed-equation", &[]),
                "delta-index",
                "coordinate-index",
                "delta-evidence",
                "coordinate-evidence",
            ],
        )
    } else {
        term(
            "integer-frey-discriminant-valuation-away-two",
            &[
                &n(q),
                &int(-1),
                &int(16),
                &int(15),
                &n(1),
                &model(),
                &term("observed-model-certificate", &[]),
                &prime(q),
                &not_two(q),
                &term("observed-equation", &[]),
                "delta-index",
                "coordinate-index",
                "delta-evidence",
                "coordinate-evidence",
            ],
        )
    };
    prelude.push_str(&definition(
        "observed-rule",
        &rule_type,
        &format!("(#pt-lambda {binders} {rule_body})"),
    ));
    let proof = term(
        "observed-rule",
        &[
            &n(kd + usize::from(wrong_index)),
            &n(kc),
            &term("observed-delta-order", &[]),
            &term("observed-coordinate-order", &[]),
        ],
    );
    let left = if at_two {
        term("add", &[&n(kd), &n(8)])
    } else {
        n(kd)
    };
    fixture_with_prelude(
        &prelude,
        &eq(&left, &n(if wrong_result { 3 } else { 2 * kc })),
        &proof,
        at_two || (q == 3 && !wrong_result && !wrong_index && !wrong_equation),
    );
}
#[test]
fn actual_frey_valuations_are_two_and_one_at_three() {
    frey_fixture(3, false, false, false);
}
#[test]
fn actual_two_valuation_formula_retains_the_denominator_shift() {
    frey_fixture_kind(2, false, false, false, true);
}
#[test]
fn a_false_valuation_formula_or_index_is_rejected() {
    frey_fixture(3, true, false, false);
    frey_fixture(3, false, true, false);
}
#[test]
fn the_prime_two_exception_and_actual_coordinate_equation_are_required() {
    frey_fixture(2, false, false, false);
    frey_fixture(3, false, false, true);
}
