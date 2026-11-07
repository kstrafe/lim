//! Adversarial invariant, valuation and actual model-certificate coupling.
#[path = "support/flt_integral_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, fixture_with_prelude, fixture_with_prelude_and_total, term};

fn n(value: usize) -> String {
    if value <= 128 {
        format!("(#pt-numeral {value})")
    } else {
        term(
            "add",
            &[
                &term("multiply", &[&n(128), &n(value / 128)]),
                &n(value % 128),
            ],
        )
    }
}
fn ty(name: &str) -> String {
    term(name, &[])
}
fn int(value: usize) -> String {
    term("integer-of-natural", &[&n(value)])
}
fn q(value: usize) -> String {
    term("rational-of-integer", &[&int(value)])
}
fn eq(a: &str, b: &str) -> String {
    term("rational-equal", &[a, b])
}
fn mul(a: &str, b: &str) -> String {
    term("rational-multiply", &[a, b])
}
fn pow(a: &str, k: usize) -> String {
    term("rational-power", &[a, &n(k)])
}
fn inv(which: &str, curve: &str) -> String {
    term(&format!("rational-weierstrass-{which}"), &[curve])
}
fn project(family: &str, value: &str) -> String {
    format!("(#pt-project {family} 0 {value})")
}

fn indexed_law(binders: &str, proposition: &str, evidence: &str, actual: usize, target: usize) {
    let prelude=format!("(#math-inductive tested-law () ((law-index #pt-nat)) #pt-prop ((checked ((evidence (#pt-pi {binders} {proposition}))))))");
    let actual_binders = binders.replace("law-index", &n(actual));
    let actual_evidence = evidence.replace("law-index", &n(actual));
    let proof=format!("(#pt-construct tested-law () ({}) checked ((#pt-lambda {actual_binders} {actual_evidence})))",n(actual));
    fixture_with_prelude(
        &prelude,
        &term("tested-law", &[&n(target)]),
        &proof,
        actual == target,
    );
}
fn scale_law(which: &str, degree: usize, wrong: usize) {
    let binders = format!(
        "((change {}) (curve {}))",
        ty("rational-variable-change"),
        ty("rational-weierstrass-curve")
    );
    let acted = term("rational-variable-change-act", &["change", "curve"]);
    let v = "(#pt-project rational-variable-change 1 change)";
    let proposition = eq(
        &inv(which, &acted),
        &mul(
            &term("rational-power", &[v, "law-index"]),
            &inv(which, "curve"),
        ),
    );
    let evidence = term(
        &format!("rational-variable-change-{which}"),
        &["change", "curve"],
    );
    for target in [degree, wrong] {
        indexed_law(&binders, &proposition, &evidence, degree, target);
    }
}
#[test]
fn c6_has_the_sixth_inverse_scale_power() {
    scale_law("c6", 6, 4);
}
#[test]
fn discriminant_has_the_twelfth_inverse_scale_power() {
    scale_law("discriminant", 12, 6);
}
#[test]
fn c_relation_keeps_its_actual_1728_coefficient() {
    let binders = format!("((curve {}))", ty("rational-weierstrass-curve"));
    let coefficient = term(
        "rational-of-integer",
        &[&term("integer-of-natural", &["law-index"])],
    );
    let right = term(
        "rational-add",
        &[
            &pow(&inv("c4", "curve"), 3),
            &term("rational-negate", &[&pow(&inv("c6", "curve"), 2)]),
        ],
    );
    let proposition = eq(&mul(&coefficient, &inv("discriminant", "curve")), &right);
    for target in [1728, 1727] {
        indexed_law(
            &binders,
            &proposition,
            &term("rational-weierstrass-c-relation", &["curve"]),
            1728,
            target,
        );
    }
}
#[test]
fn iterated_powers_multiply_their_exponents() {
    let binders = format!("((base {}))", ty("rational"));
    let proposition = eq(
        &pow(&pow("base", 2), 3),
        &term("rational-power", &["base", "law-index"]),
    );
    for target in [6, 5] {
        indexed_law(
            &binders,
            &proposition,
            &term("rational-power-compose", &["base", &n(2), &n(3)]),
            6,
            target,
        );
    }
}
#[test]
fn products_of_same_base_add_the_exponents() {
    let binders = format!("((base {}))", ty("rational"));
    let proposition = eq(
        &term("rational-power", &["base", "law-index"]),
        &mul(&pow("base", 2), &pow("base", 3)),
    );
    for target in [5, 4] {
        indexed_law(
            &binders,
            &proposition,
            &term("rational-power-add", &["base", &n(2), &n(3)]),
            5,
            target,
        );
    }
}
#[test]
fn cancellation_checks_the_actual_inverse() {
    let qt = ty("rational");
    let h = eq(&mul(&q(4), "first"), &mul(&q(4), "second"));
    let binders = format!("((first {qt}) (second {qt}) (scaled-equation {h}))");
    let quarter = format!(
        "(#pt-construct rational () () fraction ({} {} {}))",
        int(1),
        n(4),
        term("successor-not-zero", &[&n(3)])
    );
    for valid in [true, false] {
        let inverse = if valid { quarter.clone() } else { q(0) };
        let inverse_law = format!("(#pt-refl #pt-nat {})", n(if valid { 4 } else { 0 }));
        let proof = term(
            "rational-cancel-unit-left",
            &[
                &q(4),
                &inverse,
                "first",
                "second",
                &inverse_law,
                "scaled-equation",
            ],
        );
        fixture(
            &format!("(#pt-pi {binders} {})", eq("first", "second")),
            &format!("(#pt-lambda {binders} {proof})"),
            valid,
        );
    }
}
#[test]
fn discriminant_cancellation_does_not_cancel_zero() {
    let qt = ty("rational");
    let coefficient = term(
        "rational-of-integer",
        &[&term("integer-of-natural", &["law-index"])],
    );
    let h = eq(&mul(&coefficient, "first"), &mul(&coefficient, "second"));
    let binders = format!("((first {qt}) (second {qt}) (scaled-equation {h}))");
    for target in [1728, 0] {
        indexed_law(
            &binders,
            &eq("first", "second"),
            &term(
                "rational-cancel-1728",
                &["first", "second", "scaled-equation"],
            ),
            1728,
            target,
        );
    }
}

fn order(value: usize, k: usize) -> String {
    let power = term("power", &[&n(2), &n(k)]);
    let equation = format!(
        "(#pt-eq #pt-nat {} {})",
        n(value),
        term("multiply", &[&power, "candidate-cofactor"])
    );
    let nondivisor = format!(
        "(#pt-pi ((denied-proof {})) #pt-false)",
        term("divides", &[&n(2), "candidate-cofactor"])
    );
    let pred = format!(
        "(#pt-lambda ((candidate-cofactor #pt-nat)) {})",
        term("conjunction", &[&equation, &nondivisor])
    );
    let concrete_eq = format!(
        "(#pt-eq #pt-nat {} {})",
        n(value),
        term("multiply", &[&power, &n(1)])
    );
    let concrete_nondivisor = format!(
        "(#pt-pi ((denied-proof {})) #pt-false)",
        term("divides", &[&n(2), &n(1)])
    );
    let packet = term(
        "conjunction-introduce",
        &[
            &concrete_eq,
            &concrete_nondivisor,
            &format!("(#pt-refl #pt-nat {})", n(value)),
            &ty("two-not-divides-one"),
        ],
    );
    let natural = format!(
        "(#pt-construct exists (0) (#pt-nat {pred}) introduce ({} {packet}))",
        n(1)
    );
    format!(
        "(#pt-construct integer-prime-order () ({} {} {}) introduce ({} {natural} {}))",
        n(2),
        n(k),
        int(value),
        n(value),
        term("integer-natural-magnitude", &[&n(value)])
    )
}
#[test]
fn positive_signed_valuation_produces_its_actual_divisor() {
    for predecessor in [2, 3] {
        fixture(
            &term("integer-divides", &[&int(2), &int(8)]),
            &term(
                "integer-prime-order-successor-divides",
                &[&n(2), &int(8), &n(predecessor), &order(8, 3)],
            ),
            predecessor == 2,
        );
    }
}
#[test]
fn exponent_nondivisor_evidence_cannot_turn_order_zero_into_divisibility() {
    for (value, k) in [(2, 1), (1, 0)] {
        fixture(
            &term("integer-divides", &[&int(2), &int(value)]),
            &term(
                "integer-prime-order-exponent-nondivisor-divides",
                &[
                    &n(2),
                    &int(value),
                    &n(k),
                    &n(2),
                    &order(value, k),
                    &ty("two-not-divides-one"),
                ],
            ),
            k == 1,
        );
    }
}

fn model_evidence() -> String {
    format!("(#math-inductive model-evidence () ((owner {}) (curve {})) #pt-prop ((checked ((underlying {})))))",ty("integer-weierstrass-curve"),ty("rational-weierstrass-curve"),term("integer-is-integral-model-of", &["owner","curve"]))
}
fn cross(u: &str, v: &str) -> String {
    term(
        "integer-multiply",
        &[
            &term(
                "integer-power",
                &[&term("integer-weierstrass-c4", &[u]), &n(3)],
            ),
            &term("integer-weierstrass-discriminant", &[v]),
        ],
    )
}
#[test]
fn cross_identity_cannot_mix_model_certificates_from_different_curves() {
    let iw = ty("integer-weierstrass-curve");
    let wq = ty("rational-weierstrass-curve");
    let first = term("model-evidence", &["first", "curve"]);
    let second = term("model-evidence", &["second", "curve"]);
    let result = term(
        "integer-equal",
        &[&cross("first", "second"), &cross("second", "first")],
    );
    let prelude=format!("{} (#theorem checked-cross (#universes) (#parameters (#parameter first {iw}) (#parameter second {iw}) (#parameter curve {wq}) (#parameter first-proof {first}) (#parameter second-proof {second})) (#statement {result}) (#proof {}))",model_evidence(),term("integer-integral-model-cross-invariant", &["first","second","curve",&project("model-evidence","first-proof"),&project("model-evidence","second-proof")]));
    for valid in [true, false] {
        let other = term(
            "model-evidence",
            &["second", if valid { "curve" } else { "other-curve" }],
        );
        let binders=format!("((first {iw}) (second {iw}) (curve {wq}) (other-curve {wq}) (first-proof {first}) (second-proof {other}))");
        fixture_with_prelude(
            &prelude,
            &format!("(#pt-pi {binders} {result})"),
            &format!(
                "(#pt-lambda {binders} {})",
                term(
                    "checked-cross",
                    &["first", "second", "curve", "first-proof", "second-proof"]
                )
            ),
            valid,
        );
    }
}

fn transfer_check(wrong_ss: bool, wrong_bad: bool, wrong_prime: bool) {
    let iw = ty("integer-weierstrass-curve");
    let wq = ty("rational-weierstrass-curve");
    let ss = term("integer-is-semistable-model", &["owner"]);
    let dvd = term(
        "integer-divides",
        &[
            &term("integer-of-natural", &["prime-number"]),
            &term("integer-weierstrass-discriminant", &["owner"]),
        ],
    );
    let ss_decl=format!("(#math-inductive semistable-evidence () ((owner {iw})) #pt-prop ((checked ((underlying {ss})))))");
    let bad_decl=format!("(#math-inductive bad-evidence () ((owner {iw}) (prime-number #pt-nat)) #pt-prop ((checked ((underlying {dvd})))))");
    let m1 = term("model-evidence", &["first", "curve"]);
    let m2 = term("model-evidence", &["second", "curve"]);
    let s1 = term("semistable-evidence", &["first"]);
    let d1 = term("bad-evidence", &["first", "prime-number"]);
    let prime = term("prime", &["prime-number"]);
    let result = term(
        "integer-divides",
        &[
            &term("integer-of-natural", &["prime-number"]),
            &term("integer-weierstrass-discriminant", &["second"]),
        ],
    );
    let api = term(
        "integer-integral-model-bad-prime-transfer",
        &[
            "first",
            "second",
            "curve",
            "prime-number",
            &project("model-evidence", "first-proof"),
            &project("model-evidence", "second-proof"),
            &project("semistable-evidence", "semistable-proof"),
            "prime-proof",
            &project("bad-evidence", "bad-proof"),
        ],
    );
    let prelude=format!("{} {ss_decl} {bad_decl} (#theorem checked-transfer (#universes) (#parameters (#parameter first {iw}) (#parameter second {iw}) (#parameter curve {wq}) (#parameter prime-number #pt-nat) (#parameter first-proof {m1}) (#parameter second-proof {m2}) (#parameter semistable-proof {s1}) (#parameter prime-proof {prime}) (#parameter bad-proof {d1})) (#statement {result}) (#proof {api}))",model_evidence());
    let ss_input = term(
        "semistable-evidence",
        &[if wrong_ss { "second" } else { "first" }],
    );
    let bad_input = term(
        "bad-evidence",
        &[if wrong_bad { "second" } else { "first" }, "prime-number"],
    );
    let binders=format!("((first {iw}) (second {iw}) (curve {wq}) (prime-number #pt-nat) (first-proof {m1}) (second-proof {m2}) (semistable-proof {ss_input}) (prime-proof {prime}) (bad-proof {bad_input}))");
    let prime_arg = if wrong_prime {
        ty("prime-two")
    } else {
        "prime-proof".to_owned()
    };
    let proof = term(
        "checked-transfer",
        &[
            "first",
            "second",
            "curve",
            "prime-number",
            "first-proof",
            "second-proof",
            "semistable-proof",
            &prime_arg,
            "bad-proof",
        ],
    );
    fixture_with_prelude(
        &prelude,
        &format!("(#pt-pi {binders} {result})"),
        &format!("(#pt-lambda {binders} {proof})"),
        !wrong_ss && !wrong_bad && !wrong_prime,
    );
}
#[test]
fn bad_prime_transfer_requires_the_first_models_semistability() {
    transfer_check(false, false, false);
    transfer_check(true, false, false);
}
#[test]
fn bad_prime_transfer_requires_the_first_models_bad_prime() {
    transfer_check(false, true, false);
}
#[test]
fn bad_prime_transfer_requires_the_actual_prime_proof() {
    transfer_check(false, false, true);
}

#[test]
fn frey_model_claim_is_coupled_to_the_actual_package_coordinates() {
    let i = ty("integer");
    let iw = ty("integer-weierstrass-curve");
    let package = term(
        "frey-package-certificate",
        &["exponent", "first", "second", "third"],
    );
    let package_decl=format!("(#math-inductive package-evidence () ((first {i}) (second {i}) (third {i}) (exponent #pt-nat)) #pt-prop ((checked ((underlying {package})))))");
    let pc = term(
        "package-evidence",
        &["first", "second", "third", "exponent"],
    );
    let curve = term("frey-rational-curve", &["first", "second", "exponent"]);
    let mc = term("model-evidence", &["model", &curve]);
    let prime = term("prime", &["prime-number"]);
    let prod = term(
        "integer-multiply",
        &[&term("integer-multiply", &["first", "second"]), "third"],
    );
    let divides = term(
        "integer-divides",
        &[&term("integer-of-natural", &["prime-number"]), &prod],
    );
    let good = term("integer-is-good-prime-for", &["model", "prime-number"]);
    let result = format!("(#pt-pi ((good-prime {good})) #pt-false)");
    let api = term(
        "frey-package-not-good-prime-for-any-integral-model",
        &[
            "prime-number",
            "first",
            "second",
            "third",
            "exponent",
            &project("package-evidence", "package-proof"),
            "model",
            &project("model-evidence", "model-proof"),
            "prime-proof",
            "coordinate-divides",
        ],
    );
    let prelude=format!("{} {package_decl} (#theorem checked-frey (#universes) (#parameters (#parameter prime-number #pt-nat) (#parameter first {i}) (#parameter second {i}) (#parameter third {i}) (#parameter exponent #pt-nat) (#parameter package-proof {pc}) (#parameter model {iw}) (#parameter model-proof {mc}) (#parameter prime-proof {prime}) (#parameter coordinate-divides {divides})) (#statement {result}) (#proof {api}))",model_evidence());
    for valid in [true, false] {
        let pc = term(
            "package-evidence",
            &[
                "first",
                "second",
                if valid { "third" } else { "other-third" },
                "exponent",
            ],
        );
        let binders=format!("((prime-number #pt-nat) (first {i}) (second {i}) (third {i}) (other-third {i}) (exponent #pt-nat) (package-proof {pc}) (model {iw}) (model-proof {mc}) (prime-proof {prime}) (coordinate-divides {divides}))");
        let call = term(
            "checked-frey",
            &[
                "prime-number",
                "first",
                "second",
                "third",
                "exponent",
                "package-proof",
                "model",
                "model-proof",
                "prime-proof",
                "coordinate-divides",
            ],
        );
        fixture_with_prelude_and_total(
            &prelude,
            &format!("(#pt-pi {binders} {result})"),
            &format!("(#pt-lambda {binders} {call})"),
            valid,
            2 * 1024 * 1024 * 1024,
        );
    }
}
