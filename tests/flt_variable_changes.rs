//! Actual unit witnesses and false coordinate/invariant/model certificates.
#[path = "support/flt_integral_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, fixture_with_prelude, term};

fn ty(name: &str) -> String {
    term(name, &[])
}
fn n(value: usize) -> String {
    format!("(#pt-numeral {value})")
}
fn q(value: usize) -> String {
    term(
        "rational-of-integer",
        &[&term("integer-of-natural", &[&n(value)])],
    )
}
fn project(record: &str, index: usize, value: &str) -> String {
    format!("(#pt-project {record} {index} {value})")
}
fn eq(a: &str, b: &str) -> String {
    term("rational-equal", &[a, b])
}
fn mul(a: &str, b: &str) -> String {
    term("rational-multiply", &[a, b])
}
fn add(a: &str, b: &str) -> String {
    term("rational-add", &[a, b])
}
fn pow(a: &str, k: usize) -> String {
    term("rational-power", &[a, &n(k)])
}
fn change(scale: &str, inverse: &str, unit_cross: usize) -> String {
    let law = format!("(#pt-refl #pt-nat {})", n(unit_cross));
    format!(
        "(#pt-construct rational-variable-change () () coordinates ({scale} {inverse} {} {} {} {law} {law}))",
        q(1), q(1), q(1)
    )
}
fn half() -> String {
    format!(
        "(#pt-construct rational () () fraction ({} {} {}))",
        term("integer-of-natural", &[&n(1)]),
        n(2),
        term("successor-not-zero", &[&n(1)])
    )
}
fn record_witness(c: &str, valid: bool) {
    let t = ty("rational-variable-change");
    fixture(
        &format!("(#pt-eq {t} {c} {c})"),
        &format!("(#pt-refl {t} {c})"),
        valid,
    );
}

#[test]
fn an_actual_two_sided_reciprocal_is_admissible() {
    record_witness(&change(&q(2), &half(), 2), true);
}
#[test]
fn zero_cannot_be_forged_into_an_admissible_scale() {
    record_witness(&change(&q(0), &q(0), 0), false);
}
#[test]
fn a_nonzero_but_incorrect_reciprocal_is_rejected() {
    record_witness(&change(&q(2), &q(1), 2), false);
}
#[test]
fn inverse_coordinates_swap_the_actual_scale_data() {
    let c = change(&q(2), &half(), 2);
    let inverse = term("rational-variable-change-inverse", &[&c]);
    let t = ty("rational");
    for (i, expected) in [(0, half()), (1, q(2))] {
        let value = project("rational-variable-change", i, &inverse);
        fixture(
            &format!("(#pt-eq {t} {value} {expected})"),
            &format!("(#pt-refl {t} {expected})"),
            true,
        );
    }
}

fn invariant_law(which: &str, index: usize, valid: bool) {
    let ct = ty("rational-variable-change");
    let wt = ty("rational-weierstrass-curve");
    let v = project("rational-variable-change", 1, "change");
    let r = project("rational-variable-change", 2, "change");
    let acted = term("rational-variable-change-act", &["change", "curve"]);
    let inv = |name: &str, value: &str| term(&format!("rational-weierstrass-{name}"), &[value]);
    let indexed_constant = term(
        "rational-of-integer",
        &[&term("integer-of-natural", &["law-index"])],
    );
    let target = match which {
        "b2" => add(&inv("b2", "curve"), &mul(&indexed_constant, &r)),
        "b4" => add(
            &add(&inv("b4", "curve"), &mul(&r, &inv("b2", "curve"))),
            &mul(&indexed_constant, &pow(&r, 2)),
        ),
        "c4" => inv("c4", "curve"),
        _ => unreachable!(),
    };
    let exponent = if which == "c4" {
        "law-index".to_owned()
    } else {
        n(if which == "b2" { 2 } else { 4 })
    };
    let proposition = eq(
        &inv(which, &acted),
        &mul(&term("rational-power", &[&v, &exponent]), &target),
    );
    let binders = format!("((change {ct}) (curve {wt}))");
    // The index remains linked to the full invariant equation. This
    // avoids expanding that equation just to reject a different index.
    let prelude = format!(
        "(#math-inductive tested-invariant () ((law-index #pt-nat)) #pt-prop ((checked ((evidence (#pt-pi {binders} {proposition}))))))"
    );
    let actual = n(match which {
        "b2" => 12,
        "b4" => 6,
        "c4" => 4,
        _ => unreachable!(),
    });
    let evidence = format!(
        "(#pt-lambda {binders} {})",
        term(
            &format!("rational-variable-change-{which}"),
            &["change", "curve"]
        )
    );
    fixture_with_prelude(
        &prelude,
        &term("tested-invariant", &[&n(index)]),
        &format!("(#pt-construct tested-invariant () ({actual}) checked ({evidence}))"),
        valid,
    );
}
#[test]
fn b2_retains_the_exact_translation_coefficient() {
    invariant_law("b2", 12, true);
    invariant_law("b2", 11, false);
}
#[test]
fn b4_retains_the_exact_translation_coefficient() {
    invariant_law("b4", 6, true);
    invariant_law("b4", 5, false);
}
#[test]
fn c4_retains_the_fourth_power_of_the_inverse_scale() {
    invariant_law("c4", 4, true);
    invariant_law("c4", 6, false);
}
#[test]
fn exact_maps_produce_integral_models_of_the_same_curve() {
    let wt = ty("integer-weierstrass-curve");
    let qt = ty("rational-weierstrass-curve");
    let mapped = term("integer-weierstrass-map-rational", &["model"]);
    let certificate = term("rational-weierstrass-equivalent", &["curve", &mapped]);
    let prelude = format!(
        "(#math-inductive tested-model () ((model {wt}) (curve {qt})) #pt-prop ((checked ((evidence {})))))",
        term("integer-is-integral-model-of", &["model", "curve"])
    );
    for valid in [true, false] {
        let binders = format!(
            "((model {wt}) (curve {qt}) (other-curve {qt}) (map-certificate {certificate}))"
        );
        let result = term(
            "tested-model",
            &["model", if valid { "curve" } else { "other-curve" }],
        );
        let evidence = term(
            "integer-exact-map-is-integral-model",
            &["model", "curve", "map-certificate"],
        );
        fixture_with_prelude(
            &prelude,
            &format!("(#pt-pi {binders} {result})"),
            &format!(
                "(#pt-lambda {binders} (#pt-construct tested-model () (model curve) checked ({evidence})))"
            ),
            valid,
        );
    }
}

fn check_coordinate_fixture(target: &str) {
    use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/flt_variable_changes/coordinates.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    assert_eq!(
        source
            .lines()
            .filter(|line| line.starts_with("(#theorem "))
            .count(),
        122
    );
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
        .unwrap_or_else(|e| panic!("{target}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty());
}
#[test]
fn translation_changes_all_five_actual_coefficients() {
    check_coordinate_fixture("translated-a6");
}
#[test]
fn rational_scaling_uses_the_five_source_weights() {
    check_coordinate_fixture("scaled-a6");
}
#[test]
fn unused_false_theorem_is_rejected() {
    fixture_with_prelude(
        "(#theorem unrelated-false (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero))) (#proof (#pt-refl #pt-nat #pt-zero)))",
        "(#pt-eq #pt-nat #pt-zero #pt-zero)",
        "(#pt-refl #pt-nat #pt-zero)",
        false,
    );
}
