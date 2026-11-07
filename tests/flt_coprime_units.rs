//! Foundation-free checks for Eisenstein unit and coprime theorems.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EISENSTEIN_UNIT_DIVISIBILITY: &[&str] = &[
    "eisenstein-unit-of-divides-one",
    "eisenstein-unit-divides-one",
    "eisenstein-divisor-of-unit-is-unit",
    "eisenstein-unit-divides-anything",
    "eisenstein-unit-congruent",
];
const EISENSTEIN_COPRIME_FACTORS: &[&str] = &[
    "eisenstein-coprime-common-divisor-unit",
    "eisenstein-coprime-of-unit-bezout-gcd",
    "eisenstein-coprime-of-common-divisors-unit",
    "eisenstein-coprime-symmetric",
    "eisenstein-coprime-divides-product",
];

fn coprime_units_config() -> CompileConfig {
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
    let config = coprime_units_config();

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
fn eisenstein_unit_divisibility_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-unit-divisibility.lim",
        EISENSTEIN_UNIT_DIVISIBILITY,
    );
}

#[test]
fn eisenstein_coprime_factors_theorems_are_foundation_free() {
    check_matrix("eisenstein-coprime-factors.lim", EISENSTEIN_COPRIME_FACTORS);
}
