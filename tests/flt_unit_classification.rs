//! Foundation-free checks for the FLT Eisenstein unit classification.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EISENSTEIN_UNIT_COORDINATE_CASES: &[&str] = &[
    "eisenstein-unit-norm-value-impossible",
    "eisenstein-unit-zero-real-cases",
    "eisenstein-unit-positive-real-cases",
    "eisenstein-unit-negative-real-cases",
];

const EISENSTEIN_UNIT_CLASSIFICATION: &[&str] = &[
    "eisenstein-unit-classification",
    "eisenstein-unit-from-norm-one-equivalence",
    "eisenstein-standard-unit-is-unit",
];

fn unit_classification_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

fn check_matrix(module: &str, targets: &[&str]) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("theorems/flt").join(module);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let config = unit_classification_config();

    for &target in targets {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|error| {
                panic!(
                    "failed to check {target} in {}: {}",
                    path.display(),
                    error.message
                )
            });
        assert!(
            report.name == target || report.name.ends_with(&format!("::{target}")),
            "unexpected canonical target for {}: {}",
            path.display(),
            report.name
        );
        assert!(
            report.foundations.is_empty(),
            "foundations for {target} in {}: {:?}",
            path.display(),
            report.foundations
        );
    }
}

#[test]
fn eisenstein_unit_coordinate_case_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-unit-coordinate-cases.lim",
        EISENSTEIN_UNIT_COORDINATE_CASES,
    );
}

#[test]
fn eisenstein_unit_classification_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-unit-classification.lim",
        EISENSTEIN_UNIT_CLASSIFICATION,
    );
}

#[path = "support/flt_unit_fixtures.rs"]
mod unit_fixtures;
use unit_fixtures::{fixture, term};

#[test]
fn all_six_standard_representatives_are_certified_units() {
    let one = term("eisenstein-one", &[]);
    let omega = term("eisenstein-omega", &[]);
    let square = term("eisenstein-power", &[&omega, "(#pt-numeral 2)"]);
    let roots = [
        one.clone(),
        term("eisenstein-negate", &[&one]),
        omega.clone(),
        term("eisenstein-negate", &[&omega]),
        square.clone(),
        term("eisenstein-negate", &[&square]),
    ];
    for (index, root) in roots.iter().enumerate() {
        let norm_one = format!(
            "(#pt-refl #pt-nat (#pt-numeral {}))",
            if index < 4 { 1 } else { 2 }
        );
        let unit = term("eisenstein-unit-of-natural-norm-one", &[root, &norm_one]);
        fixture(
            &term("eisenstein-standard-unit", &[root]),
            &term("eisenstein-unit-classification", &[root, &unit]),
            true,
            &unit_classification_config(),
        );
    }
}

#[test]
fn zero_cannot_receive_a_forged_unit_certificate() {
    let zero = term("eisenstein-zero", &[]);
    let unit = term(
        "eisenstein-unit-of-natural-norm-one",
        &[&zero, "(#pt-refl #pt-nat #pt-zero)"],
    );
    fixture(
        &term("eisenstein-standard-unit", &[&zero]),
        &term("eisenstein-unit-classification", &[&zero, &unit]),
        false,
        &unit_classification_config(),
    );
}
