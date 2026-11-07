//! Foundation-free checks for the FLT Eisenstein cubic-factorization modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const CUBIC_FACTOR_EXPANSION: &[&str] = &[
    "eisenstein-cubic-factor-expansion",
    "eisenstein-cubic-product-expansion",
];

const CUBIC_FACTORIZATION: &[&str] = &[
    "eisenstein-power-two-as-square",
    "eisenstein-omega-mixed-polynomial",
    "eisenstein-cubic-root-expansion-reduces",
    "eisenstein-sum-cubes-factor",
    "eisenstein-cube-product",
    "eisenstein-omega-square-unit",
    "eisenstein-omega-product-cube",
    "eisenstein-omega-square-product-cube",
];

fn cubic_factorization_config() -> CompileConfig {
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
    let config = cubic_factorization_config();

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
fn cubic_factor_expansion_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-factor-expansion.lim",
        CUBIC_FACTOR_EXPANSION,
    );
}

#[test]
fn cubic_factorization_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-factorization.lim", CUBIC_FACTORIZATION);
}
