//! Native rational coordinate changes; audit every source declaration.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

fn matrix(module: &str, steps: usize, names: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let declared: Vec<_> = source
        .lines()
        .filter_map(|line| line.strip_prefix("(#theorem ")?.split_whitespace().next())
        .collect();
    let mut expected: Vec<_> = (0..steps)
        .map(|n| format!("variable-change-step-{n:03}"))
        .collect();
    expected.extend(names.iter().map(|name| (*name).to_owned()));
    assert_eq!(declared, expected, "unaccounted native proof declaration");
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    // Source checking checks every declaration, including unused helpers.
    // The unused_false_theorem_is_rejected regression guards this contract.
    let target = names.last().unwrap();
    let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
        .unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty(), "{:?}", report.foundations);
}

#[test]
fn rational_polynomial_laws() {
    matrix(
        "rational-polynomial-laws",
        0,
        &[
            "rational-multiply-distribute-first",
            "rational-add-swap-inner",
            "rational-negative-as-product",
        ],
    );
}
#[test]
fn identity_polynomials() {
    matrix(
        "rational-variable-change-identity-polynomials",
        63,
        &[
            "rational-variable-change-identity-coefficient-0",
            "rational-variable-change-identity-coefficient-1",
            "rational-variable-change-identity-coefficient-2",
            "rational-variable-change-identity-coefficient-3",
            "rational-variable-change-identity-coefficient-4",
        ],
    );
}
#[test]
fn b2_polynomial() {
    matrix(
        "rational-variable-change-b2-polynomial",
        134,
        &["rational-variable-change-b2-polynomial"],
    );
}
#[test]
fn b4_translation() {
    matrix(
        "rational-variable-change-b4-translation",
        232,
        &["rational-variable-change-b4-translation-polynomial"],
    );
}
#[test]
fn b4_scaling() {
    matrix(
        "rational-variable-change-b4-scale",
        44,
        &["rational-variable-change-b4-scale-polynomial"],
    );
}
#[test]
fn c4_polynomial() {
    matrix(
        "rational-variable-change-c4-polynomial",
        165,
        &["rational-variable-change-c4-polynomial"],
    );
}
#[test]
fn admissible_changes_identity_and_b2() {
    matrix(
        "rational-variable-change",
        0,
        &[
            "rational-variable-change-scale-unit",
            "rational-variable-change-inverse-scale-unit",
            "rational-variable-change-scale-nonzero",
            "rational-variable-change-inverse-scale-nonzero",
            "rational-variable-change-identity-conversion-0",
            "rational-variable-change-identity-projection-0",
            "rational-variable-change-identity-conversion-1",
            "rational-variable-change-identity-projection-1",
            "rational-variable-change-identity-conversion-2",
            "rational-variable-change-identity-projection-2",
            "rational-variable-change-identity-conversion-3",
            "rational-variable-change-identity-projection-3",
            "rational-variable-change-identity-conversion-4",
            "rational-variable-change-identity-projection-4",
            "rational-variable-change-identity-acts",
            "rational-variable-change-b2",
        ],
    );
}
#[test]
fn b4_and_c4_of_actual_coordinate_change() {
    matrix(
        "rational-variable-change-invariants",
        0,
        &["rational-variable-change-b4", "rational-variable-change-c4"],
    );
}
#[test]
fn actual_integral_model_relation() {
    matrix(
        "integer-integral-model",
        0,
        &[
            "integer-exact-map-is-integral-model",
            "integer-model-is-integral-model-of-map",
            "frey-exact-model-is-integral-model",
        ],
    );
}
