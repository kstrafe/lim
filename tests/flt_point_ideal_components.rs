//! Inventory every native point-ideal matrix and nonprincipality theorem.
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
    let total = 1024 * 1024 * 1024;
    config.set_proof_budget(ProofBudget::new(budget.work(), budget.phase_bytes(), total).unwrap());
    let directory = std::env::temp_dir().join(format!(
        "lim-point-ideal-matrix-{}-{module}",
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
fn point_ideal_basis_constant_factor() {
    matrix(
        "point-ideal-basis-constant-factor",
        &["point-ideal-basis-constant-factor"],
    );
}

#[test]
fn point_ideal_basis_constant_multiply() {
    matrix(
        "point-ideal-basis-constant-multiply",
        &["point-ideal-basis-constant-multiply"],
    );
}

#[test]
fn point_ideal_basis_data() {
    matrix("point-ideal-basis-data", &["point-ideal-basis-determinant"]);
}

#[test]
fn point_ideal_basis_linear_quadratic_principal() {
    matrix(
        "point-ideal-basis-linear-quadratic-principal",
        &["point-ideal-basis-linear-quadratic-principal"],
    );
}

#[test]
fn point_ideal_basis_reconstruction() {
    matrix(
        "point-ideal-basis-reconstruction",
        &["point-ideal-basis-reconstruct"],
    );
}

#[test]
fn point_ideal_basis_zero_linear_y_square() {
    matrix(
        "point-ideal-basis-zero-linear-Y-square",
        &["point-ideal-basis-zero-linear-Y-square"],
    );
}

#[test]
fn point_ideal_degree_factor_nonvanishing() {
    matrix(
        "point-ideal-degree-factor-nonvanishing",
        &[
            "point-ideal-degree-middle-nonzero",
            "point-ideal-degree-first-factor-nonzero",
            "point-ideal-degree-second-factor-nonzero",
        ],
    );
}

#[test]
fn point_ideal_degree_linear_mutual_factors() {
    matrix(
        "point-ideal-degree-linear-mutual-factors",
        &["point-ideal-degree-linear-mutual-factors"],
    );
}

#[test]
fn point_ideal_degree_root_linear() {
    matrix(
        "point-ideal-degree-root-linear",
        &["point-ideal-degree-root-linear"],
    );
}

#[test]
fn point_ideal_degree_small_indices() {
    matrix(
        "point-ideal-degree-small-indices",
        &[
            "point-ideal-degree-zero-sum-left",
            "point-ideal-degree-one-sum-collapse",
        ],
    );
}

#[test]
fn point_ideal_matrix_y_column() {
    matrix(
        "point-ideal-matrix-Y-column",
        &["point-ideal-matrix-Y-column"],
    );
}

#[test]
fn point_ideal_matrix_column_factorization() {
    matrix(
        "point-ideal-matrix-column-factorization",
        &["point-ideal-matrix-column-factorization"],
    );
}

#[test]
fn point_ideal_matrix_columns() {
    matrix(
        "point-ideal-matrix-columns",
        &["point-ideal-matrix-columns-action"],
    );
}

#[test]
fn point_ideal_matrix_equivalence() {
    matrix(
        "point-ideal-matrix-equivalence",
        &[
            "point-ideal-matrix-symmetric",
            "point-ideal-matrix-transitive",
        ],
    );
}

#[test]
fn point_ideal_matrix_left_action() {
    matrix(
        "point-ideal-matrix-left-action",
        &["point-ideal-matrix-left-action"],
    );
}

#[test]
fn point_ideal_matrix_multiplication_columns() {
    matrix(
        "point-ideal-matrix-multiplication-columns",
        &["point-ideal-matrix-multiplication-columns"],
    );
}

#[test]
fn point_ideal_principal_forward_matrix() {
    matrix(
        "point-ideal-principal-forward-matrix",
        &["point-ideal-principal-forward-factorization"],
    );
}

#[test]
fn point_ideal_principal_norm_forward_factor() {
    matrix(
        "point-ideal-principal-norm-forward-factor",
        &["point-ideal-principal-norm-forward-factor"],
    );
}

#[test]
fn point_ideal_principal_norm_reverse_factor() {
    matrix(
        "point-ideal-principal-norm-reverse-factor",
        &["point-ideal-principal-norm-reverse-factor"],
    );
}

#[test]
fn point_ideal_principal_reverse_matrix() {
    matrix(
        "point-ideal-principal-reverse-matrix",
        &["point-ideal-principal-reverse-factorization"],
    );
}

#[test]
fn point_ideal_principal_weierstrass_impossible() {
    matrix(
        "point-ideal-principal-weierstrass-impossible",
        &["point-ideal-principal-weierstrass-impossible"],
    );
}
