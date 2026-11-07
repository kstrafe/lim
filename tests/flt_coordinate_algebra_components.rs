//! Inventory every native ring/polynomial/quadratic normal-form theorem.
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
    let total = if module == "rational-ring-structure" {
        2 * 1024 * 1024 * 1024
    } else {
        1024 * 1024 * 1024
    };
    config.set_proof_budget(ProofBudget::new(budget.work(), budget.phase_bytes(), total).unwrap());
    let directory = std::env::temp_dir().join(format!(
        "lim-coordinate-matrix-{}-{module}",
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
fn commutative_ring_cancellation() {
    matrix(
        "commutative-ring-cancellation",
        &[
            "ring-add-cancel-left",
            "ring-add-cancel-right",
            "ring-negate-unique",
            "ring-negate-zero",
            "ring-negate-involution",
        ],
    );
}

#[test]
fn commutative_ring_data() {
    matrix(
        "commutative-ring-data",
        &[
            "ring-reflexive",
            "ring-symmetric",
            "ring-transitive",
            "ring-add-congruent",
            "ring-multiply-congruent",
            "ring-negate-congruent",
            "ring-add-zero",
            "ring-add-associative",
            "ring-add-commutative",
            "ring-add-inverse",
            "ring-multiply-one",
            "ring-multiply-associative",
            "ring-multiply-commutative",
            "ring-distributive",
            "ring-multiply-zero",
        ],
    );
}

#[test]
fn commutative_ring_elementary_laws() {
    matrix(
        "commutative-ring-elementary-laws",
        &[
            "ring-zero-add",
            "ring-one-multiply",
            "ring-zero-multiply",
            "ring-add-inverse-left",
            "ring-add-left-commutative",
            "ring-multiply-left-commutative",
        ],
    );
}

#[test]
fn commutative_ring_sign_laws() {
    matrix(
        "commutative-ring-sign-laws",
        &[
            "ring-add-shuffle-four",
            "ring-negate-add",
            "ring-distribute-first",
            "ring-multiply-negate-first",
            "ring-multiply-negate-second",
            "ring-multiply-two-negatives",
        ],
    );
}

#[test]
fn finite_residue_ring_structure() {
    matrix(
        "finite-residue-ring-structure",
        &["finite-residue-ring-equality"],
    );
}

#[test]
fn quadratic_algebra_additive_laws() {
    matrix(
        "quadratic-algebra-additive-laws",
        &[
            "quadratic-symmetric",
            "quadratic-transitive",
            "quadratic-add-congruent",
            "quadratic-negate-congruent",
            "quadratic-add-zero",
            "quadratic-add-commutative",
            "quadratic-add-associative",
            "quadratic-add-inverse",
        ],
    );
}

#[test]
fn quadratic_algebra_basis_conjugation() {
    matrix(
        "quadratic-algebra-basis-conjugation",
        &[
            "quadratic-basis-combination",
            "quadratic-basis-reconstruct",
            "quadratic-basis-independent",
            "quadratic-basis-spans",
            "quadratic-Y-relation",
            "quadratic-conjugate-involution",
            "quadratic-conjugate-product",
        ],
    );
}

#[test]
fn quadratic_algebra_data() {
    matrix("quadratic-algebra-data", &["quadratic-reflexive"]);
}

#[test]
fn quadratic_algebra_left_matrix() {
    matrix(
        "quadratic-algebra-left-matrix",
        &[
            "quadratic-left-matrix-multiply",
            "quadratic-norm-determinant",
        ],
    );
}

#[test]
fn quadratic_algebra_multiplication_laws() {
    matrix(
        "quadratic-algebra-multiplication-laws",
        &[
            "quadratic-multiply-congruent",
            "quadratic-multiply-commutative",
            "quadratic-multiply-associative",
            "quadratic-distributive",
            "quadratic-multiply-one",
            "quadratic-multiply-zero",
        ],
    );
}

#[test]
fn quadratic_algebra_norm_laws() {
    matrix(
        "quadratic-algebra-norm-laws",
        &["quadratic-norm-multiply", "quadratic-norm-source-form"],
    );
}

#[test]
fn quadratic_algebra_ring_structure() {
    matrix(
        "quadratic-algebra-ring-structure",
        &["quadratic-ring-equality"],
    );
}

#[test]
fn quadratic_associative_constant_identity() {
    matrix(
        "quadratic-associative-constant-identity",
        &["quadratic-associative-constant-identity"],
    );
}

#[test]
fn quadratic_associative_linear_identity() {
    matrix(
        "quadratic-associative-linear-identity",
        &["quadratic-associative-linear-identity"],
    );
}

#[test]
fn quadratic_basic_scalar_identities() {
    matrix(
        "quadratic-basic-scalar-identities",
        &[
            "quadratic-multiply-one-constant-identity",
            "quadratic-multiply-zero-constant-identity",
            "quadratic-Y-squared-constant-identity",
            "quadratic-multiply-one-linear-identity",
            "quadratic-multiply-zero-linear-identity",
            "quadratic-Y-squared-linear-identity",
            "quadratic-conjugate-involution-constant-identity",
            "quadratic-conjugate-product-constant-identity",
            "quadratic-conjugate-involution-linear-identity",
            "quadratic-conjugate-product-linear-identity",
        ],
    );
}

#[test]
fn quadratic_commutative_constant_identity() {
    matrix(
        "quadratic-commutative-constant-identity",
        &["quadratic-commutative-constant-identity"],
    );
}

#[test]
fn quadratic_commutative_linear_identity() {
    matrix(
        "quadratic-commutative-linear-identity",
        &["quadratic-commutative-linear-identity"],
    );
}

#[test]
fn quadratic_distributive_constant_identity() {
    matrix(
        "quadratic-distributive-constant-identity",
        &["quadratic-distributive-constant-identity"],
    );
}

#[test]
fn quadratic_distributive_linear_identity() {
    matrix(
        "quadratic-distributive-linear-identity",
        &["quadratic-distributive-linear-identity"],
    );
}

#[test]
fn quadratic_left_matrix_0_identity() {
    matrix(
        "quadratic-left-matrix-0-identity",
        &["quadratic-left-matrix-0-identity"],
    );
}

#[test]
fn quadratic_left_matrix_1_identity() {
    matrix(
        "quadratic-left-matrix-1-identity",
        &["quadratic-left-matrix-1-identity"],
    );
}

#[test]
fn quadratic_left_matrix_2_identity() {
    matrix(
        "quadratic-left-matrix-2-identity",
        &["quadratic-left-matrix-2-identity"],
    );
}

#[test]
fn quadratic_left_matrix_3_identity() {
    matrix(
        "quadratic-left-matrix-3-identity",
        &["quadratic-left-matrix-3-identity"],
    );
}

#[test]
fn quadratic_norm_determinant_identity() {
    matrix(
        "quadratic-norm-determinant-identity",
        &["quadratic-norm-determinant-identity"],
    );
}

#[test]
fn rational_ring_structure() {
    matrix("rational-ring-structure", &["rational-ring-equality"]);
}

#[test]
fn ring_matrix2_data() {
    matrix("ring-matrix2-data", &["ring-matrix2-reflexive"]);
}

#[test]
fn ring_matrix2_determinant_laws() {
    matrix(
        "ring-matrix2-determinant-laws",
        &[
            "ring-matrix2-determinant-congruent",
            "ring-matrix2-determinant-multiply",
        ],
    );
}

#[test]
fn ring_matrix2_determinant_product_identity() {
    matrix(
        "ring-matrix2-determinant-product-identity",
        &["ring-matrix2-determinant-product-identity"],
    );
}

#[test]
fn ring_polynomial_additive_laws() {
    matrix(
        "ring-polynomial-additive-laws",
        &[
            "ring-polynomial-add-zero",
            "ring-polynomial-add-commutative",
            "ring-polynomial-add-associative",
            "ring-polynomial-add-inverse",
            "ring-polynomial-zero-add",
            "ring-polynomial-add-shuffle-four",
        ],
    );
}

#[test]
fn ring_polynomial_coefficient_laws() {
    matrix(
        "ring-polynomial-coefficient-laws",
        &[
            "ring-polynomial-add-coefficient",
            "ring-polynomial-negate-coefficient",
            "ring-polynomial-scale-coefficient",
            "ring-polynomial-shift-zero-coefficient",
            "ring-polynomial-shift-successor-coefficient",
        ],
    );
}

#[test]
fn ring_polynomial_congruence() {
    matrix(
        "ring-polynomial-congruence",
        &[
            "ring-polynomial-add-congruent",
            "ring-polynomial-negate-congruent",
            "ring-polynomial-scale-congruent",
            "ring-polynomial-shift-congruent",
        ],
    );
}

#[test]
fn ring_polynomial_data() {
    matrix(
        "ring-polynomial-data",
        &[
            "ring-polynomial-coefficient-nil",
            "ring-polynomial-coefficient-head",
            "ring-polynomial-coefficient-tail",
        ],
    );
}

#[test]
fn ring_polynomial_equivalence() {
    matrix(
        "ring-polynomial-equivalence",
        &[
            "ring-polynomial-reflexive",
            "ring-polynomial-symmetric",
            "ring-polynomial-transitive",
        ],
    );
}

#[test]
fn ring_polynomial_finite_support() {
    matrix(
        "ring-polynomial-finite-support",
        &["ring-polynomial-finite-support"],
    );
}

#[test]
fn ring_polynomial_horner_distributivity() {
    matrix(
        "ring-polynomial-horner-distributivity",
        &[
            "ring-polynomial-multiply-scale",
            "ring-polynomial-multiply-shift",
            "ring-polynomial-distributive",
        ],
    );
}

#[test]
fn ring_polynomial_horner_second_argument() {
    matrix(
        "ring-polynomial-horner-second-argument",
        &[
            "ring-polynomial-multiply-right-congruent",
            "ring-polynomial-multiply-constant",
            "ring-polynomial-cons-decomposition",
            "ring-polynomial-multiply-cons",
        ],
    );
}

#[test]
fn ring_polynomial_multiplication_laws() {
    matrix(
        "ring-polynomial-multiplication-laws",
        &[
            "ring-polynomial-multiply-commutative",
            "ring-polynomial-multiply-congruent",
            "ring-polynomial-distribute-first",
            "ring-polynomial-scale-multiply",
            "ring-polynomial-multiply-associative",
        ],
    );
}

#[test]
fn ring_polynomial_multiplicative_identities() {
    matrix(
        "ring-polynomial-multiplicative-identities",
        &[
            "ring-polynomial-multiply-zero",
            "ring-polynomial-multiply-one",
            "ring-polynomial-one-multiply",
            "ring-polynomial-shift-multiply",
        ],
    );
}

#[test]
fn ring_polynomial_scalar_laws() {
    matrix(
        "ring-polynomial-scalar-laws",
        &[
            "ring-polynomial-scale-add",
            "ring-polynomial-scale-sum",
            "ring-polynomial-scale-associative",
            "ring-polynomial-scale-one",
            "ring-polynomial-scale-zero",
            "ring-polynomial-scale-nil",
        ],
    );
}

#[test]
fn ring_polynomial_shift_laws() {
    matrix(
        "ring-polynomial-shift-laws",
        &[
            "ring-polynomial-cons-congruent",
            "ring-polynomial-shift-nil",
            "ring-polynomial-shift-add",
            "ring-polynomial-shift-scale",
        ],
    );
}

#[test]
fn ring_polynomial_structure() {
    matrix(
        "ring-polynomial-structure",
        &["ring-polynomial-structure-equality"],
    );
}

#[test]
fn weierstrass_coordinate_norm_formula() {
    matrix(
        "weierstrass-coordinate-norm-formula",
        &[
            "weierstrass-coordinate-norm-formula",
            "weierstrass-coordinate-norm-multiply",
        ],
    );
}

#[test]
fn weierstrass_coordinate_normal_form() {
    matrix(
        "weierstrass-coordinate-normal-form",
        &["weierstrass-coordinate-ring-equality"],
    );
}
