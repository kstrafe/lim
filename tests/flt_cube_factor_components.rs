//! Foundation-free checks for coprime Eisenstein power-factor extraction.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EISENSTEIN_COPRIME_POWER_FACTORS: &[&str] = &[
    "eisenstein-coprime-extract-factor",
    "eisenstein-coprime-extract-power",
];
const EISENSTEIN_CUBE_FACTOR_ALGEBRA: &[&str] = &[
    "eisenstein-unit-cube-factor-rearrange",
    "eisenstein-cube-associate-rebuild",
];
const EISENSTEIN_CUBE_FACTOR_REMOVAL: &[&str] = &["eisenstein-prime-cube-factor-removal"];
const EISENSTEIN_ASSOCIATED_CUBE: &[&str] = &[
    "eisenstein-zero-associated-cube",
    "eisenstein-unit-associated-cube",
    "eisenstein-associated-cube-congruent",
];
const EISENSTEIN_CUBE_EXTRACTION_NORM: &[&str] = &[
    "eisenstein-prime-cube-quotient-norm-decreases",
    "eisenstein-associated-cube-of-cube-factor",
];
const EISENSTEIN_COPRIME_CUBE_INDUCTION: &[&str] = &[
    "eisenstein-coprime-cube-quotient-step",
    "eisenstein-coprime-cube-prime-step",
    "eisenstein-coprime-cube-nonunit-step",
    "eisenstein-coprime-cube-induction-step",
    "eisenstein-coprime-cube-with-norm",
];
const EISENSTEIN_COPRIME_CUBE: &[&str] = &[
    "eisenstein-coprime-product-associated-cube",
    "eisenstein-coprime-product-associated-cubes",
];
const EISENSTEIN_COPRIME_CUBE_TRIPLE: &[&str] = &[
    "eisenstein-coprime-product-right",
    "eisenstein-coprime-triple-associated-cubes",
];
const EISENSTEIN_CUBIC_PACKET_CUBES: &[&str] =
    &["eisenstein-cubic-packet-residuals-associated-cubes"];

fn cube_factor_config() -> CompileConfig {
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
    let config = cube_factor_config();

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
fn eisenstein_coprime_power_factor_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-coprime-power-factor.lim",
        EISENSTEIN_COPRIME_POWER_FACTORS,
    );
}

#[test]
fn eisenstein_cube_factor_algebra_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cube-factor-algebra.lim",
        EISENSTEIN_CUBE_FACTOR_ALGEBRA,
    );
}

#[test]
fn eisenstein_cube_factor_removal_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cube-factor-removal.lim",
        EISENSTEIN_CUBE_FACTOR_REMOVAL,
    );
}

#[test]
fn eisenstein_associated_cube_theorems_are_foundation_free() {
    check_matrix("eisenstein-associated-cube.lim", EISENSTEIN_ASSOCIATED_CUBE);
}

#[test]
fn eisenstein_cube_extraction_norm_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cube-extraction-norm.lim",
        EISENSTEIN_CUBE_EXTRACTION_NORM,
    );
}

#[test]
fn eisenstein_coprime_cube_induction_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-coprime-cube-induction.lim",
        EISENSTEIN_COPRIME_CUBE_INDUCTION,
    );
}

#[test]
fn eisenstein_coprime_cube_theorems_are_foundation_free() {
    check_matrix("eisenstein-coprime-cube.lim", EISENSTEIN_COPRIME_CUBE);
}

#[test]
fn eisenstein_cube_triple_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-coprime-cube-triple.lim",
        EISENSTEIN_COPRIME_CUBE_TRIPLE,
    );
}

#[test]
fn eisenstein_cube_triple_packet_theorem_is_foundation_free() {
    check_matrix(
        "eisenstein-cubic-packet-cubes.lim",
        EISENSTEIN_CUBIC_PACKET_CUBES,
    );
}
