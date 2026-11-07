//! Foundation-free checks for coordinate-search bounds and finite coordinates.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL_COORDINATE_SEARCH: &[&str] = &[
    "natural-three-summands-with-tail",
    "natural-three-square-budget-magnitude-bound",
];
const INTEGER_COORDINATE_SEARCH: &[&str] = &[
    "integer-three-square-natural-budget",
    "integer-three-square-magnitude-bound",
];
const EISENSTEIN_COORDINATE_SEARCH: &[&str] = &[
    "eisenstein-natural-norm-real-square-budget",
    "eisenstein-real-coordinate-magnitude-bound",
    "eisenstein-natural-norm-omega-square-budget",
    "eisenstein-omega-coordinate-magnitude-bound",
];
const EISENSTEIN_FINITE_COORDINATES: &[&str] = &[
    "eisenstein-coordinate-sign-cases",
    "eisenstein-finite-coordinates-exist",
];

fn coordinate_search_config() -> CompileConfig {
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
    let config = coordinate_search_config();

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
fn natural_coordinate_search_theorems_are_foundation_free() {
    check_matrix(
        "natural-coordinate-search-bound.lim",
        NATURAL_COORDINATE_SEARCH,
    );
}

#[test]
fn integer_coordinate_search_theorems_are_foundation_free() {
    check_matrix(
        "integer-coordinate-search-bound.lim",
        INTEGER_COORDINATE_SEARCH,
    );
}

#[test]
fn eisenstein_coordinate_search_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-coordinate-search-bound.lim",
        EISENSTEIN_COORDINATE_SEARCH,
    );
}

#[test]
fn eisenstein_finite_coordinate_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-finite-coordinates.lim",
        EISENSTEIN_FINITE_COORDINATES,
    );
}
