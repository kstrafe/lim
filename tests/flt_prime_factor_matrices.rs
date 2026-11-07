//! Foundation-free checks for the finite search and prime-factor matrices.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const PROPOSITION_MINIMUM: &[&str] = &[
    "proposition-prefix-cases",
    "proposition-bounded-minimum",
    "minimum-exists-from-proposition-cases",
    "proposition-conjunction-cases",
    "proposition-disjunction-cases",
];
const EISENSTEIN_FINITE_NORM_SEARCH: &[&str] = &[
    "eisenstein-norm-property-cases",
    "eisenstein-signed-property-cases",
    "eisenstein-coordinate-search-cases",
    "eisenstein-representative-property-choices",
    "eisenstein-box-property-search",
    "eisenstein-norm-existence-to-search",
    "eisenstein-search-to-norm-existence",
    "eisenstein-norm-existence-cases",
];
const EISENSTEIN_NONUNIT_DIVISORS: &[&str] = &[
    "eisenstein-divisibility-cases-nonzero-number",
    "eisenstein-nonunit-divisor-congruent",
    "eisenstein-nonunit-divisor-cases",
];
const EISENSTEIN_LEAST_NONUNIT_DIVISOR: &[&str] = &[
    "eisenstein-nonunit-divisor-norm-cases",
    "eisenstein-minimum-nonunit-divisor-norm",
];
const EISENSTEIN_NONUNIT_FACTOR_NORM: &[&str] = &[
    "eisenstein-nonunit-natural-norm-large",
    "eisenstein-nonunit-factor-norm-decreases",
];
const EISENSTEIN_PRIME_DIVISOR: &[&str] = &[
    "eisenstein-minimal-nonunit-divisor-irreducible",
    "eisenstein-prime-divisor-exists",
];

fn prime_factor_matrix_config() -> CompileConfig {
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
    let config = prime_factor_matrix_config();

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
fn proposition_minimum_theorems_are_foundation_free() {
    check_matrix("proposition-minimum.lim", PROPOSITION_MINIMUM);
}

#[test]
fn eisenstein_finite_norm_search_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-finite-norm-search.lim",
        EISENSTEIN_FINITE_NORM_SEARCH,
    );
}

#[test]
fn eisenstein_nonunit_divisor_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-nonunit-divisors.lim",
        EISENSTEIN_NONUNIT_DIVISORS,
    );
}

#[test]
fn eisenstein_least_nonunit_divisor_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-least-nonunit-divisor.lim",
        EISENSTEIN_LEAST_NONUNIT_DIVISOR,
    );
}

#[test]
fn eisenstein_nonunit_factor_norm_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-nonunit-factor-norm.lim",
        EISENSTEIN_NONUNIT_FACTOR_NORM,
    );
}

#[test]
fn eisenstein_prime_divisor_theorems_are_foundation_free() {
    check_matrix("eisenstein-prime-divisor.lim", EISENSTEIN_PRIME_DIVISOR);
}
