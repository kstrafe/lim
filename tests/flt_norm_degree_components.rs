//! Inventory every native coordinate norm degree and domain theorem.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;
fn matrix(module: &str, expected: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let declared: Vec<_> = source
        .lines()
        .filter_map(|line| line.strip_prefix("(#theorem ")?.split_whitespace().next())
        .collect();
    assert_eq!(
        declared, expected,
        "every native theorem must be inventoried"
    );
    let target = expected.last().unwrap();
    let mut config = CompileConfig::default();
    let budget = ProofBudget::default();
    let total = if module.contains("rational") {
        2 * 1024 * 1024 * 1024
    } else {
        1024 * 1024 * 1024
    };
    config.set_proof_budget(ProofBudget::new(budget.work(), budget.phase_bytes(), total).unwrap());
    let directory = std::env::temp_dir().join(format!(
        "lim-norm-degree-matrix-{}-{module}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.lim");
    let driver = format!(
        "(#alias checked-module-theorem = {}::{target})",
        path.display()
    );
    std::fs::write(&entry, &driver).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &driver,
        &entry,
        &config,
        "checked-module-theorem",
    );
    std::fs::remove_dir_all(directory).unwrap();
    let report = result.unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty());
}

#[test]
fn coordinate_norm_degree_certified_formula() {
    matrix(
        "coordinate-norm-degree-certified-formula",
        &["coordinate-norm-degree-from-inputs-valid"],
    );
}

#[test]
fn coordinate_norm_degree_computed_formula() {
    matrix(
        "coordinate-norm-degree-computed-formula",
        &["coordinate-norm-degree-computed-formula"],
    );
}

#[test]
fn coordinate_norm_degree_contradictions() {
    matrix(
        "coordinate-norm-degree-contradictions",
        &[
            "coordinate-norm-degree-contradict-zero",
            "coordinate-norm-degree-contradict-leading",
        ],
    );
}

#[test]
fn coordinate_norm_degree_coordinate_domain() {
    matrix(
        "coordinate-norm-degree-coordinate-domain",
        &["coordinate-norm-degree-coordinate-domain-product"],
    );
}

#[test]
fn coordinate_norm_degree_cubic_at_least_three_identity() {
    matrix(
        "coordinate-norm-degree-cubic-at-least-three-identity",
        &["coordinate-norm-degree-cubic-at-least-three-identity"],
    );
}

#[test]
fn coordinate_norm_degree_cubic_successor_identity() {
    matrix(
        "coordinate-norm-degree-cubic-successor-identity",
        &["coordinate-norm-degree-cubic-successor-identity"],
    );
}

#[test]
fn coordinate_norm_degree_data_uniqueness() {
    matrix(
        "coordinate-norm-degree-data-uniqueness",
        &[
            "coordinate-norm-degree-data-index-unique",
            "coordinate-norm-degree-data-tag-unique",
        ],
    );
}

#[test]
fn coordinate_norm_degree_dichotomy() {
    matrix(
        "coordinate-norm-degree-dichotomy",
        &["coordinate-norm-degree-gap-dichotomy"],
    );
}

#[test]
fn coordinate_norm_degree_double_successor_identity() {
    matrix(
        "coordinate-norm-degree-double-successor-identity",
        &["coordinate-norm-degree-double-successor-identity"],
    );
}

#[test]
fn coordinate_norm_degree_exclusion() {
    matrix(
        "coordinate-norm-degree-exclusion",
        &[
            "coordinate-norm-degree-zero-constant-not-one",
            "coordinate-norm-degree-not-one",
        ],
    );
}

#[test]
fn coordinate_norm_degree_exhaustive() {
    matrix(
        "coordinate-norm-degree-exhaustive",
        &["coordinate-norm-degree-exhaustive-elimination"],
    );
}

#[test]
fn coordinate_norm_degree_formula() {
    matrix(
        "coordinate-norm-degree-formula",
        &[
            "coordinate-norm-degree-formula",
            "coordinate-norm-degree-transfer",
            "coordinate-norm-degree-form-congruent",
            "coordinate-norm-degree-congruent",
        ],
    );
}

#[test]
fn coordinate_norm_degree_high_branch() {
    matrix(
        "coordinate-norm-degree-high-branch",
        &["coordinate-norm-degree-square-dominant"],
    );
}

#[test]
fn coordinate_norm_degree_high_cross_identity() {
    matrix(
        "coordinate-norm-degree-high-cross-identity",
        &["coordinate-norm-degree-high-cross-identity"],
    );
}

#[test]
fn coordinate_norm_degree_high_cubic_identity() {
    matrix(
        "coordinate-norm-degree-high-cubic-identity",
        &["coordinate-norm-degree-high-cubic-identity"],
    );
}

#[test]
fn coordinate_norm_degree_index_gaps() {
    matrix(
        "coordinate-norm-degree-index-gaps",
        &[
            "coordinate-norm-degree-low-square-gap",
            "coordinate-norm-degree-low-cross-gap",
            "coordinate-norm-degree-high-cross-gap",
            "coordinate-norm-degree-high-cubic-gap",
        ],
    );
}

#[test]
fn coordinate_norm_degree_integer_exclusion() {
    matrix(
        "coordinate-norm-degree-integer-exclusion",
        &[
            "coordinate-norm-degree-double-not-one",
            "coordinate-norm-degree-cubic-not-one",
        ],
    );
}

#[test]
fn coordinate_norm_degree_low_branch() {
    matrix(
        "coordinate-norm-degree-low-branch",
        &["coordinate-norm-degree-cubic-dominant"],
    );
}

#[test]
fn coordinate_norm_degree_low_cross_finish_identity() {
    matrix(
        "coordinate-norm-degree-low-cross-finish-identity",
        &["coordinate-norm-degree-low-cross-finish-identity"],
    );
}

#[test]
fn coordinate_norm_degree_low_cross_reorder_identity() {
    matrix(
        "coordinate-norm-degree-low-cross-reorder-identity",
        &["coordinate-norm-degree-low-cross-reorder-identity"],
    );
}

#[test]
fn coordinate_norm_degree_low_square_identity() {
    matrix(
        "coordinate-norm-degree-low-square-identity",
        &["coordinate-norm-degree-low-square-identity"],
    );
}

#[test]
fn coordinate_norm_degree_maximum() {
    matrix(
        "coordinate-norm-degree-maximum",
        &[
            "coordinate-norm-degree-maximum-zero-right",
            "coordinate-norm-degree-maximum-gap-right",
            "coordinate-norm-degree-maximum-gap-left",
        ],
    );
}

#[test]
fn coordinate_norm_degree_maximum_formula() {
    matrix(
        "coordinate-norm-degree-maximum-formula",
        &["coordinate-norm-degree-maximum-formula"],
    );
}

#[test]
fn coordinate_norm_degree_maximum_order() {
    matrix(
        "coordinate-norm-degree-maximum-order",
        &[
            "coordinate-norm-degree-maximum-strict-right",
            "coordinate-norm-degree-maximum-strict-left",
        ],
    );
}

#[test]
fn coordinate_norm_degree_nilpotent_counterexample() {
    matrix(
        "coordinate-norm-degree-nilpotent-counterexample",
        &[
            "coordinate-norm-degree-square-zero-constant",
            "coordinate-norm-degree-nilpotent-norm-form",
            "coordinate-norm-degree-nilpotent-counterexample",
        ],
    );
}

#[test]
fn coordinate_norm_degree_nonzero_exclusion() {
    matrix(
        "coordinate-norm-degree-nonzero-exclusion",
        &["coordinate-norm-degree-nonzero-inputs-not-one"],
    );
}

#[test]
fn coordinate_norm_degree_nonzero_norm() {
    matrix(
        "coordinate-norm-degree-nonzero-norm",
        &[
            "coordinate-norm-degree-pair-nonzero-norm",
            "coordinate-norm-degree-element-nonzero-norm",
        ],
    );
}

#[test]
fn coordinate_norm_degree_polynomial_domain() {
    matrix(
        "coordinate-norm-degree-polynomial-domain",
        &["coordinate-norm-degree-polynomial-domain-product"],
    );
}

#[test]
fn coordinate_norm_degree_regroup() {
    matrix(
        "coordinate-norm-degree-regroup",
        &["coordinate-norm-degree-regroup"],
    );
}

#[test]
fn coordinate_norm_degree_source_obstruction() {
    matrix(
        "coordinate-norm-degree-source-obstruction",
        &[
            "coordinate-norm-degree-natural-not-one",
            "coordinate-norm-degree-element-not-one",
            "coordinate-norm-degree-element-natural-not-one",
        ],
    );
}

#[test]
fn coordinate_norm_degree_support_gaps() {
    matrix(
        "coordinate-norm-degree-support-gaps",
        &["coordinate-norm-degree-weaken-support"],
    );
}

#[test]
fn coordinate_norm_degree_term_bounds() {
    matrix(
        "coordinate-norm-degree-term-bounds",
        &[
            "coordinate-norm-degree-square",
            "coordinate-norm-degree-cubic-term",
            "coordinate-norm-degree-cross-bound",
        ],
    );
}

#[test]
fn coordinate_norm_degree_zero_cases() {
    matrix(
        "coordinate-norm-degree-zero-cases",
        &[
            "coordinate-norm-degree-zero-constant",
            "coordinate-norm-degree-zero-linear",
        ],
    );
}

#[test]
fn coordinate_norm_degree_zero_equations() {
    matrix(
        "coordinate-norm-degree-zero-equations",
        &[
            "coordinate-norm-degree-zero-constant-form",
            "coordinate-norm-degree-zero-linear-form",
            "coordinate-norm-degree-zero-constant-equation",
            "coordinate-norm-degree-zero-linear-equation",
            "coordinate-norm-degree-both-zero",
        ],
    );
}

#[test]
fn coordinate_norm_degree_zero_kernel() {
    matrix(
        "coordinate-norm-degree-zero-kernel",
        &[
            "coordinate-norm-degree-zero-kernel",
            "coordinate-norm-degree-element-norm-zero",
            "coordinate-norm-degree-element-zero-norm",
        ],
    );
}
