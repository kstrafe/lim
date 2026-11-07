//! Concrete fraction and Frey-coefficient probes, including invalid denominator evidence.
#[path = "support/flt_rational_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};

fn n(v: usize) -> String {
    if v <= 128 {
        format!("(#pt-numeral {v})")
    } else {
        term("add", &["(#pt-numeral 128)", &n(v - 128)])
    }
}
fn refl(v: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(v))
}
fn nz(v: usize) -> String {
    term("successor-not-zero", &[&n(v - 1)])
}
#[derive(Clone, Copy)]
struct Diff {
    positive: usize,
    negative: usize,
}
impl Diff {
    fn new(v: isize) -> Self {
        Self {
            positive: v.max(0) as usize,
            negative: (-v).max(0) as usize,
        }
    }
    fn add(self, b: Self) -> Self {
        Self {
            positive: self.positive + b.positive,
            negative: self.negative + b.negative,
        }
    }
    fn neg(self) -> Self {
        Self {
            positive: self.negative,
            negative: self.positive,
        }
    }
    fn mul(self, b: Self) -> Self {
        Self {
            positive: self.positive * b.positive + self.negative * b.negative,
            negative: self.positive * b.negative + self.negative * b.positive,
        }
    }
    fn source(self) -> String {
        format!(
            "(#pt-construct integer () () difference ({} {}))",
            n(self.positive),
            n(self.negative)
        )
    }
}
#[derive(Clone)]
struct Ratio {
    source: String,
    numerator: Diff,
    denominator: usize,
}
impl Ratio {
    fn raw(numerator: Diff, denominator: usize) -> Self {
        Self {
            source: format!(
                "(#pt-construct rational () () fraction ({} {} {}))",
                numerator.source(),
                n(denominator),
                nz(denominator)
            ),
            numerator,
            denominator,
        }
    }
    fn new(value: isize, denominator: usize) -> Self {
        Self::raw(Diff::new(value), denominator)
    }
    fn add(&self, b: &Self) -> Self {
        Self {
            source: term("rational-add", &[&self.source, &b.source]),
            numerator: self
                .numerator
                .mul(Diff::new(b.denominator as isize))
                .add(b.numerator.mul(Diff::new(self.denominator as isize))),
            denominator: self.denominator * b.denominator,
        }
    }
    fn mul(&self, b: &Self) -> Self {
        Self {
            source: term("rational-multiply", &[&self.source, &b.source]),
            numerator: self.numerator.mul(b.numerator),
            denominator: self.denominator * b.denominator,
        }
    }
    fn neg(&self) -> Self {
        Self {
            source: term("rational-negate", &[&self.source]),
            numerator: self.numerator.neg(),
            denominator: self.denominator,
        }
    }
}
fn eq(a: &Ratio, b: &Ratio) -> String {
    term("rational-equal", &[&a.source, &b.source])
}
// The host writes a candidate reflexivity term. The kernel checks the other
// cross sum too, so incorrect candidate arithmetic cannot establish a theorem.
fn equality(a: &Ratio, b: &Ratio) -> String {
    refl(a.numerator.positive * b.denominator + b.numerator.negative * a.denominator)
}
fn zero() -> String {
    term("rational-zero", &[])
}
fn not(p: &str) -> String {
    format!("(#pt-pi ((denied-proof {p})) #pt-false)")
}
fn int_nonzero(v: isize) -> String {
    let positive = term(
        "integer-natural-embedding-nonzero",
        &[&n(v.unsigned_abs()), &nz(v.unsigned_abs())],
    );
    if v > 0 {
        positive
    } else {
        term(
            "integer-negative-nonzero",
            &[
                &term("integer-of-natural", &[&n(v.unsigned_abs())]),
                &positive,
            ],
        )
    }
}
fn fraction_nonzero(a: &Ratio, v: isize) -> String {
    term("rational-fraction-nonzero", &[&a.source, &int_nonzero(v)])
}

#[test]
fn cross_equality_accepts_equivalent_fraction_representations() {
    for (a, b) in [
        (Ratio::new(1, 2), Ratio::new(2, 4)),
        (Ratio::new(-1, 2), Ratio::new(-3, 6)),
        (
            Ratio::raw(
                Diff {
                    positive: 3,
                    negative: 2,
                },
                2,
            ),
            Ratio::new(1, 2),
        ),
    ] {
        fixture(&eq(&a, &b), &equality(&a, &b), true);
    }
}

#[test]
fn unequal_fractions_reject_a_forged_cross_equality() {
    let a = Ratio::new(1, 2);
    let b = Ratio::new(1, 3);
    fixture(&eq(&a, &b), &equality(&a, &b), false);
}

#[test]
fn cross_equality_does_not_identify_distinct_raw_records() {
    let a = Ratio::new(1, 2);
    let b = Ratio::new(2, 4);
    let statement = format!("(#pt-eq (#pt-use rational ()) {} {})", a.source, b.source);
    let proof = format!("(#pt-refl (#pt-use rational ()) {})", a.source);
    fixture(&statement, &proof, false);
}

#[test]
fn rational_records_require_nonzero_denominators() {
    for value in [0, 1] {
        let bad = format!(
            "(#pt-construct rational () () fraction ({} (#pt-numeral 0) {}))",
            Diff::new(value).source(),
            nz(1)
        );
        fixture(
            &term("rational-equal", &[&bad, &bad]),
            &term("rational-reflexive", &[&bad]),
            false,
        );
    }
}

#[test]
fn equivalent_fractions_compose_through_a_valid_middle_denominator() {
    let a = Ratio::new(1, 2);
    let b = Ratio::new(2, 4);
    let c = Ratio::new(3, 6);
    let proof = term(
        "rational-transitive",
        &[
            &a.source,
            &b.source,
            &c.source,
            &equality(&a, &b),
            &equality(&b, &c),
        ],
    );
    fixture(&eq(&a, &c), &proof, true);
}

#[test]
fn integer_cross_transitivity_cannot_cancel_a_zero_middle_factor() {
    let i = |v| Diff::new(v).source();
    let proof = term(
        "integer-cross-product-transitive",
        &[
            &i(1),
            &i(0),
            &i(2),
            &i(1),
            &i(0),
            &i(1),
            &int_nonzero(1),
            &refl(0),
            &refl(0),
        ],
    );
    let statement = term(
        "integer-equal",
        &[
            &term("integer-multiply", &[&i(1), &i(1)]),
            &term("integer-multiply", &[&i(2), &i(1)]),
        ],
    );
    fixture(&statement, &proof, false);
}

#[test]
fn addition_computes_signed_fractions_with_distinct_denominators() {
    let sum = Ratio::new(1, 2).add(&Ratio::new(-1, 3));
    let expected = Ratio::new(1, 6);
    fixture(&eq(&sum, &expected), &equality(&sum, &expected), true);
}

#[test]
fn multiplication_computes_signed_fractions_with_distinct_denominators() {
    let product = Ratio::new(2, 3).mul(&Ratio::new(-3, 4));
    let expected = Ratio::new(-1, 2);
    fixture(
        &eq(&product, &expected),
        &equality(&product, &expected),
        true,
    );
}

#[test]
fn add_and_multiply_preserve_equivalent_input_representations() {
    let a = Ratio::new(1, 2);
    let b = Ratio::new(-1, 3);
    let x = Ratio::new(2, 4);
    let y = Ratio::new(-2, 6);
    for multiply in [false, true] {
        let (lhs, rhs, name) = if multiply {
            (a.mul(&b), x.mul(&y), "rational-multiply-congruent")
        } else {
            (a.add(&b), x.add(&y), "rational-add-congruent")
        };
        let proof = term(
            name,
            &[
                &a.source,
                &b.source,
                &x.source,
                &y.source,
                &equality(&a, &x),
                &equality(&b, &y),
            ],
        );
        fixture(&eq(&lhs, &rhs), &proof, true);
    }
}

#[test]
fn rational_addition_is_associative_for_actual_mixed_sign_inputs() {
    let a = Ratio::new(1, 2);
    let b = Ratio::new(-1, 3);
    let c = Ratio::new(1, 6);
    fixture(
        &eq(&a.add(&b).add(&c), &a.add(&b.add(&c))),
        &term(
            "rational-add-associative",
            &[&a.source, &b.source, &c.source],
        ),
        true,
    );
}

#[test]
fn rational_distributivity_handles_different_common_denominators() {
    let a = Ratio::new(2, 3);
    let b = Ratio::new(-1, 2);
    let c = Ratio::new(1, 4);
    fixture(
        &eq(&a.mul(&b.add(&c)), &a.mul(&b).add(&a.mul(&c))),
        &term(
            "rational-multiply-distribute-second",
            &[&a.source, &b.source, &c.source],
        ),
        true,
    );
}

#[test]
fn additive_inverses_and_noncanonical_zero_numerators_are_valid() {
    let a = Ratio::raw(
        Diff {
            positive: 3,
            negative: 2,
        },
        2,
    );
    fixture(
        &term("rational-equal", &[&a.add(&a.neg()).source, &zero()]),
        &term("rational-add-inverse", &[&a.source]),
        true,
    );
    let z = Ratio::raw(
        Diff {
            positive: 3,
            negative: 3,
        },
        2,
    );
    fixture(
        &term("rational-equal", &[&z.source, &zero()]),
        &term("rational-zero-numerator", &[&z.source, &refl(3)]),
        true,
    );
}

#[test]
fn actual_nonzero_numerators_prove_nonzero_products_and_powers() {
    let a = Ratio::new(1, 2);
    let b = Ratio::new(-1, 3);
    let proof = term(
        "rational-nonzero-product",
        &[
            &a.source,
            &b.source,
            &fraction_nonzero(&a, 1),
            &fraction_nonzero(&b, -1),
        ],
    );
    fixture(
        &not(&term("rational-equal", &[&a.mul(&b).source, &zero()])),
        &proof,
        true,
    );
    for exponent in [0, 3] {
        let power = term("rational-power", &[&b.source, &n(exponent)]);
        fixture(
            &not(&term("rational-equal", &[&power, &zero()])),
            &term(
                "rational-power-nonzero",
                &[&b.source, &n(exponent), &fraction_nonzero(&b, -1)],
            ),
            true,
        );
    }
}

#[test]
fn multiplying_by_an_actual_denominator_recovers_the_integer() {
    let numerator = Diff::new(-2).source();
    let value = Ratio::new(-2, 3);
    let lhs = term(
        "rational-multiply",
        &[
            &term("rational-of-integer", &[&Diff::new(3).source()]),
            &value.source,
        ],
    );
    let rhs = term("rational-of-integer", &[&numerator]);
    fixture(
        &term("rational-equal", &[&lhs, &rhs]),
        &term(
            "rational-fraction-times-denominator",
            &[&numerator, &n(3), &nz(3)],
        ),
        true,
    );
}

#[test]
fn fraction_scale_cancellation_requires_an_actual_nonzero_factor() {
    let numerator = Diff::new(1).source();
    let value = Ratio::new(1, 6);
    let expected = Ratio::new(1, 2);
    let lhs = term(
        "rational-multiply",
        &[
            &term("rational-of-integer", &[&Diff::new(3).source()]),
            &value.source,
        ],
    );
    let proof = term(
        "rational-fraction-natural-factor-cancel",
        &[&numerator, &n(2), &n(3), &nz(2), &nz(3)],
    );
    fixture(
        &term("rational-equal", &[&lhs, &expected.source]),
        &proof,
        true,
    );
    let proof = term(
        "rational-fraction-natural-factor-cancel",
        &[&numerator, &n(2), &n(0), &nz(2), &nz(1)],
    );
    fixture(
        &term("rational-equal", &[&expected.source, &expected.source]),
        &proof,
        false,
    );
}

fn model() -> String {
    term(
        "frey-rational-model",
        &[&Diff::new(1).source(), &Diff::new(1).source()],
    )
}

#[test]
fn frey_model_has_the_exact_five_pinned_coefficients() {
    for (index, raw, denominator, expected) in [
        (0, Diff::new(1), 1, Ratio::new(1, 1)),
        (
            1,
            Diff {
                positive: 1,
                negative: 2,
            },
            4,
            Ratio::new(-1, 4),
        ),
        (2, Diff::new(0), 1, Ratio::new(0, 1)),
        (3, Diff::new(-1), 16, Ratio::new(-1, 16)),
        (4, Diff::new(0), 1, Ratio::new(0, 1)),
    ] {
        let coefficient = Ratio {
            source: format!(
                "(#pt-project rational-weierstrass-curve {index} {})",
                model()
            ),
            numerator: raw,
            denominator,
        };
        fixture(
            &eq(&coefficient, &expected),
            &equality(&coefficient, &expected),
            true,
        );
    }
}

#[test]
fn frey_b2_b4_b6_have_the_expected_actual_fraction_values() {
    for (name, raw, denominator, expected) in [
        (
            "rational-weierstrass-b2",
            Diff {
                positive: 8,
                negative: 8,
            },
            4,
            Ratio::new(0, 1),
        ),
        (
            "rational-weierstrass-b4",
            Diff::new(-2),
            16,
            Ratio::new(-1, 8),
        ),
        ("rational-weierstrass-b6", Diff::new(0), 1, Ratio::new(0, 1)),
    ] {
        let actual = Ratio {
            source: term(name, &[&model()]),
            numerator: raw,
            denominator,
        };
        fixture(&eq(&actual, &expected), &equality(&actual, &expected), true);
    }
}

#[test]
fn nonzero_original_coordinates_give_a_nonzero_fourth_coefficient() {
    let one = Diff::new(1).source();
    let curve = term("frey-rational-curve", &[&one, &one, &n(5)]);
    let coefficient = format!("(#pt-project rational-weierstrass-curve 3 {curve})");
    fixture(
        &not(&term("rational-equal", &[&coefficient, &zero()])),
        &term(
            "frey-rational-curve-a4-nonzero",
            &[&one, &one, &n(5), &int_nonzero(1), &int_nonzero(1)],
        ),
        true,
    );
}

#[test]
fn zero_coordinate_cannot_use_forged_nonzero_evidence() {
    let z = Diff::new(0).source();
    let one = Diff::new(1).source();
    let curve = term("frey-rational-curve", &[&z, &one, &n(1)]);
    let coefficient = format!("(#pt-project rational-weierstrass-curve 3 {curve})");
    fixture(
        &not(&term("rational-equal", &[&coefficient, &zero()])),
        &term(
            "frey-rational-curve-a4-nonzero",
            &[&z, &one, &n(1), &int_nonzero(1), &int_nonzero(1)],
        ),
        false,
    );
}
