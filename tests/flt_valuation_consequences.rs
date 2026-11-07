//! Concrete valuation-divisibility and exact source-model predicate controls.
#[path = "support/flt_integral_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, fixture_with_prelude, term};

fn n(v: usize) -> String {
    format!("(#pt-numeral {v})")
}
fn refl(v: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(v))
}
fn eq(a: &str, b: &str) -> String {
    format!("(#pt-eq #pt-nat {a} {b})")
}
fn not(p: &str) -> String {
    format!("(#pt-pi ((denied-proof {p})) #pt-false)")
}
fn dvd(d: usize, v: &str) -> String {
    term("divides", &[&n(d), v])
}
fn prime(q: usize) -> String {
    term(if q == 3 { "prime-three" } else { "prime-two" }, &[])
}
fn int(v: usize) -> String {
    term("integer-of-natural", &[&n(v)])
}
fn negative(v: usize) -> String {
    term("integer-negative-natural", &[&n(v)])
}
fn both(p: &str, q: &str, hp: &str, hq: &str) -> String {
    term("conjunction-introduce", &[p, q, hp, hq])
}
fn above_four(v: usize) -> String {
    let pred = format!(
        "(#pt-lambda ((candidate-gap #pt-nat)) {})",
        eq(&n(v), &term("add", &[&n(5), "candidate-gap"]))
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {pred}) introduce ({} {}))",
        n(v.saturating_sub(5)),
        refl(v)
    )
}
fn not_two(v: usize) -> String {
    let one = term("successor-injective", &[&n(v - 1), &n(1), "equal-to-two"]);
    let zero = term("successor-injective", &[&n(v - 2), &n(0), &one]);
    format!(
        "(#pt-lambda ((equal-to-two {})) (#pt-app {} {zero}))",
        eq(&n(v), &n(2)),
        term("successor-not-zero", &[&n(0)])
    )
}
fn natural_div(d: usize, v: usize, factor: usize) -> String {
    let pred = format!(
        "(#pt-lambda ((candidate-factor #pt-nat)) {})",
        eq(&n(v), &term("multiply", &[&n(d), "candidate-factor"]))
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {pred}) introduce ({} {}))",
        n(factor),
        refl(v)
    )
}

#[test]
fn doubled_coordinate_values_have_the_actual_exponent_divisor() {
    for (p, l) in [(0, 0), (1, 3), (2, 0), (5, 3), (9, 2)] {
        let value = term("multiply", &[&term("multiply", &[&n(2), &n(p)]), &n(l)]);
        fixture(
            &dvd(p, &value),
            &term("natural-exponent-divides-doubled-value", &[&n(p), &n(l)]),
            true,
        );
    }
}
#[test]
fn the_above_four_bound_excludes_two() {
    for v in [5, 7, 2, 4] {
        fixture(
            &not(&eq(&n(v), &n(2))),
            &term("natural-above-four-not-two", &[&n(v), &above_four(v)]),
            v > 4,
        );
    }
}
#[test]
fn the_only_prime_dividing_two_is_two() {
    fixture(
        &eq(&n(2), &n(2)),
        &term(
            "natural-prime-divides-two-only-two",
            &[&n(2), &prime(2), &natural_div(2, 2, 1)],
        ),
        true,
    );
    fixture(
        &eq(&n(3), &n(2)),
        &term(
            "natural-prime-divides-two-only-two",
            &[&n(3), &prime(3), &natural_div(3, 2, 0)],
        ),
        false,
    );
}
#[test]
fn the_eight_argument_retains_the_prime_two_exception() {
    fixture(
        &not(&dvd(3, &n(8))),
        &term(
            "natural-prime-away-two-not-divides-eight",
            &[&n(3), &prime(3), &not_two(3)],
        ),
        true,
    );
    fixture(
        &not(&dvd(2, &n(8))),
        &term(
            "natural-prime-away-two-not-divides-eight",
            &[&n(2), &prime(2), &not_two(2)],
        ),
        false,
    );
}
#[test]
fn a_shifted_valuation_equation_gives_actual_nondivisibility() {
    for k in [4, 3] {
        fixture(
            &not(&dvd(3, &n(k))),
            &term(
                "natural-shifted-valuation-nondivisible",
                &[&n(3), &n(k), &n(2), &prime(3), &not_two(3), &refl(12)],
            ),
            k == 4,
        );
    }
}
#[test]
fn the_prime_two_counterexample_requires_the_actual_exponent_bound() {
    // 0+8=2*2*2, but2 divides0. A false4<2 certificate must be rejected.
    fixture(
        &not(&dvd(2, &n(0))),
        &term(
            "natural-shifted-valuation-nondivisible-above-four",
            &[&n(2), &n(0), &n(2), &prime(2), &above_four(2), &refl(8)],
        ),
        false,
    );
}

fn curve(a4: usize, alternate_first: bool) -> String {
    let first = if alternate_first {
        format!(
            "(#pt-construct integer () () difference ({} {}))",
            n(2),
            n(1)
        )
    } else {
        int(1)
    };
    format!(
        "(#pt-construct integer-weierstrass-curve () () coefficients ({first} {} {} {} {}))",
        int(0),
        int(0),
        int(a4),
        int(0)
    )
}
fn zero_curve() -> String {
    format!(
        "(#pt-construct integer-weierstrass-curve () () coefficients ({} {} {} {} {}))",
        int(0),
        int(0),
        int(0),
        int(0),
        int(0)
    )
}
fn ss(w: &str) -> String {
    term("integer-is-semistable-model", &[w])
}
fn good(w: &str, q: usize) -> String {
    term("integer-is-good-prime-for", &[w, &n(q)])
}
fn invariant(name: &str, w: &str) -> String {
    term(&format!("integer-weierstrass-{name}"), &[w])
}
fn base_semistable() -> String {
    term(
        "integer-c4-one-is-semistable-model",
        &[&curve(0, false), &refl(1)],
    )
}
fn zero_divisor(value: &str, equality: &str) -> String {
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use integer ()))) {})",
        term(
            "integer-equal",
            &[
                value,
                &term("integer-multiply", &[&int(2), "candidate-factor"])
            ]
        )
    );
    format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {pred}) introduce ({} {equality}))",
        int(0),
    )
}
fn coeff_equivalence(v: &str, w: &str, a4: usize) -> String {
    let types: Vec<_> = (0..5)
        .map(|i| {
            term(
                "integer-equal",
                &[
                    &format!("(#pt-project integer-weierstrass-curve {i} {v})"),
                    &format!("(#pt-project integer-weierstrass-curve {i} {w})"),
                ],
            )
        })
        .collect();
    let proofs = [refl(2), refl(0), refl(0), refl(a4), refl(0)];
    fn build(types: &[String], proofs: &[String]) -> (String, String) {
        if types.len() == 1 {
            return (types[0].clone(), proofs[0].clone());
        }
        let (t, h) = build(&types[1..], &proofs[1..]);
        (
            term("conjunction", &[&types[0], &t]),
            both(&types[0], &t, &proofs[0], &h),
        )
    }
    build(&types, &proofs).1
}
fn certificate(name: &str, ty: &str, body: &str) -> String {
    format!("(#theorem {name} (#universes) (#parameters) (#statement {ty}) (#proof {body}))\n")
}

#[test]
fn the_exact_source_model_predicate_does_not_assert_ellipticity() {
    let w = curve(0, false);
    let zero = term("integer-equal", &[&invariant("discriminant", &w), &int(0)]);
    fixture(
        &term("conjunction", &[&ss(&w), &zero]),
        &both(&ss(&w), &zero, &base_semistable(), &refl(0)),
        true,
    );
}
#[test]
fn zero_invariants_fail_the_source_model_predicate() {
    let w = zero_curve();
    let delta = invariant("discriminant", "generic-model");
    let c4 = invariant("c4", "generic-model");
    let binders = format!(
        "((generic-model (#pt-use integer-weierstrass-curve ())) (delta-zero {}) (c4-zero {}))",
        term("integer-equal", &[&delta, &int(0)]),
        term("integer-equal", &[&c4, &int(0)])
    );
    let body = format!(
        "(#pt-lambda {binders} (#pt-lambda ((claimed-model {})) (#pt-app claimed-model {} {} {} {})))",
        ss("generic-model"),
        n(2),
        prime(2),
        zero_divisor(&delta, "delta-zero"),
        zero_divisor(&c4, "c4-zero")
    );
    let mut prelude = certificate(
        "observed-zero-model-rule",
        &format!("(#pt-pi {binders} {})", not(&ss("generic-model"))),
        &body,
    );
    prelude.push_str(&certificate(
        "observed-zero-delta",
        &term("integer-equal", &[&invariant("discriminant", &w), &int(0)]),
        &refl(0),
    ));
    prelude.push_str(&certificate(
        "observed-zero-c4",
        &term("integer-equal", &[&invariant("c4", &w), &int(0)]),
        &refl(0),
    ));
    fixture_with_prelude(
        &prelude,
        &not(&ss(&w)),
        &term(
            "observed-zero-model-rule",
            &[
                &w,
                &term("observed-zero-delta", &[]),
                &term("observed-zero-c4", &[]),
            ],
        ),
        true,
    );
}
#[test]
fn a_forged_unit_c4_cannot_certify_a_zero_model() {
    let w = zero_curve();
    fixture(
        &ss(&w),
        &term("integer-c4-one-is-semistable-model", &[&w, &refl(0)]),
        false,
    );
}
#[test]
fn semistable_model_transport_preserves_equivalent_integer_representations() {
    let v = curve(0, false);
    let w = curve(0, true);
    let mut prelude = certificate(
        "observed-coefficients",
        &term("integer-weierstrass-equivalent", &[&v, &w]),
        &coeff_equivalence(&v, &w, 0),
    );
    prelude.push_str(&certificate(
        "observed-base-model",
        &ss(&v),
        &base_semistable(),
    ));
    fixture_with_prelude(
        &prelude,
        &ss(&w),
        &term(
            "integer-semistable-model-equivalent",
            &[
                &v,
                &w,
                &term("observed-coefficients", &[]),
                &term("observed-base-model", &[]),
            ],
        ),
        true,
    );
}
#[test]
fn false_coefficient_equivalence_cannot_certify_a_zero_model() {
    let v = curve(0, false);
    let w = zero_curve();
    fixture(
        &ss(&w),
        &term(
            "integer-semistable-model-equivalent",
            &[&v, &w, &coeff_equivalence(&v, &w, 0), &base_semistable()],
        ),
        false,
    );
}
#[test]
fn good_prime_transport_uses_actual_discriminant_equivalence() {
    let v = curve(1, false);
    let w = curve(1, true);
    let delta = invariant("discriminant", &v);
    let mag = term(
        "disjunction-right",
        &[
            &term("integer-equal", &[&delta, &int(63)]),
            &term("integer-equal", &[&delta, &negative(63)]),
            &refl(64),
        ],
    );
    let mut prelude = certificate(
        "observed-delta-magnitude",
        &term("integer-magnitude", &[&delta, &n(63)]),
        &mag,
    );
    let natural = term(
        "integer-divides-magnitude",
        &[
            &n(2),
            &delta,
            &n(63),
            &term("observed-delta-magnitude", &[]),
            "discriminant-divides",
        ],
    );
    let one = term(
        "divides-add-cancel-left",
        &[&n(2), &n(62), &n(1), &natural_div(2, 62, 31), &natural],
    );
    let idiv = term("integer-divides", &[&int(2), &delta]);
    let body = format!(
        "(#pt-lambda ((discriminant-divides {idiv})) (#pt-app {} {one}))",
        term("two-not-divides-one", &[])
    );
    prelude.push_str(&certificate("observed-good-prime", &good(&v, 2), &body));
    prelude.push_str(&certificate(
        "observed-coefficients",
        &term("integer-weierstrass-equivalent", &[&v, &w]),
        &coeff_equivalence(&v, &w, 1),
    ));
    fixture_with_prelude(
        &prelude,
        &good(&w, 2),
        &term(
            "integer-good-prime-equivalent",
            &[
                &v,
                &w,
                &n(2),
                &term("observed-coefficients", &[]),
                &term("observed-good-prime", &[]),
            ],
        ),
        true,
    );
}

fn bad_frey_call(missing_exception: bool) {
    let i = "(#pt-use integer ())";
    let iw = "(#pt-use integer-weierstrass-curve ())";
    let product = term(
        "integer-multiply",
        &[&term("integer-multiply", &["first", "second"]), "third"],
    );
    let delta = invariant("discriminant", "model");
    let binders=format!("((first {i}) (second {i}) (third {i}) (exponent #pt-nat) (package {}) (model {iw}) (model-certificate {}) (delta-index #pt-nat) (coordinate-index #pt-nat) (delta-evidence {}) (coordinate-evidence {}))",term("frey-package-certificate", &["exponent","first","second","third"]),term("integer-frey-model-certificate", &["first","second","exponent","model"]),term("integer-prime-order", &[&n(2),"delta-index",&delta]),term("integer-prime-order", &[&n(2),"coordinate-index",&product]));
    let base = [
        "first",
        "second",
        "third",
        "exponent",
        "package",
        "model",
        "model-certificate",
    ];
    let proof = if missing_exception {
        let mut args = vec![n(2)];
        args.extend(base.map(str::to_owned));
        args.extend([
            prime(2),
            prime(2),
            "delta-index".into(),
            "coordinate-index".into(),
            "delta-evidence".into(),
            "coordinate-evidence".into(),
        ]);
        let refs: Vec<_> = args.iter().map(String::as_str).collect();
        term("frey-package-exponent-divides-away-two-valuation", &refs)
    } else {
        let mut args = base.map(str::to_owned).to_vec();
        args.extend([
            "(#pt-succ delta-index)".into(),
            "coordinate-index".into(),
            "delta-evidence".into(),
            "coordinate-evidence".into(),
        ]);
        let refs: Vec<_> = args.iter().map(String::as_str).collect();
        term("frey-package-exponent-not-divides-two-valuation", &refs)
    };
    let conclusion = term("divides", &["exponent", "delta-index"]);
    let conclusion = if missing_exception {
        conclusion
    } else {
        not(&conclusion)
    };
    fixture(
        &format!("(#pt-pi {binders} {conclusion})"),
        &format!("(#pt-lambda {binders} {proof})"),
        false,
    );
}
#[test]
fn the_frey_consequence_requires_the_actual_valuation_index() {
    bad_frey_call(false);
}
#[test]
fn the_away_two_frey_consequence_requires_its_explicit_exception_proof() {
    bad_frey_call(true);
}
