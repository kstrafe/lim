//! Foundation-free checks for Bezout gcd component theorems.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EISENSTEIN_BEZOUT_GCD_DEFS: &[&str] = &[
    "eisenstein-bezout-gcd-zero-right",
    "eisenstein-bezout-gcd-common-divisor",
];
const EISENSTEIN_BEZOUT_GCD_ALGEBRA: &[&str] = &["eisenstein-bezout-quotient-row"];
const EISENSTEIN_BEZOUT_GCD_EUCLIDEAN: &[&str] = &[
    "eisenstein-bezout-gcd-euclidean-step",
    "eisenstein-bezout-gcd-euclidean-backward",
];

fn bezout_gcd_components_config() -> CompileConfig {
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
    let config = bezout_gcd_components_config();

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
fn eisenstein_bezout_gcd_defs_theorems_are_foundation_free() {
    check_matrix("eisenstein-bezout-gcd-defs.lim", EISENSTEIN_BEZOUT_GCD_DEFS);
}
#[test]
fn eisenstein_bezout_gcd_algebra_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-bezout-gcd-algebra.lim",
        EISENSTEIN_BEZOUT_GCD_ALGEBRA,
    );
}
#[test]
fn eisenstein_bezout_gcd_euclidean_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-bezout-gcd-euclidean.lim",
        EISENSTEIN_BEZOUT_GCD_EUCLIDEAN,
    );
}
