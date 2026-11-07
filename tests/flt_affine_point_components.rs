//! Inventory and check each native finite affine-point operation theorem.
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
    config.set_proof_budget(
        ProofBudget::new(budget.work(), budget.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
        .unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty());
}

#[test]
fn affine_integer_cubic_divided_difference() {
    matrix(
        "affine-integer-cubic-divided-difference",
        &["affine-cubic-divided-difference-integer-identity"],
    );
}

#[test]
fn affine_integer_derivative_y_difference() {
    matrix(
        "affine-integer-derivative-y-difference",
        &["affine-derivative-y-difference-integer-identity"],
    );
}

#[test]
fn affine_integer_equal_x_factor() {
    matrix(
        "affine-integer-equal-x-factor",
        &["affine-equal-x-factor-integer-identity"],
    );
}

#[test]
fn affine_integer_line_cubic_derivative() {
    matrix(
        "affine-integer-line-cubic-derivative",
        &["affine-line-cubic-derivative-integer-identity"],
    );
}

#[test]
fn affine_integer_line_cubic_evaluation() {
    matrix(
        "affine-integer-line-cubic-evaluation",
        &["affine-line-cubic-evaluation-integer-identity"],
    );
}

#[test]
fn affine_integer_line_intercept() {
    matrix(
        "affine-integer-line-intercept",
        &["affine-line-intercept-integer-identity"],
    );
}

#[test]
fn affine_integer_neg_derivative_x() {
    matrix(
        "affine-integer-neg-derivative-x",
        &["affine-neg-derivative-x-integer-identity"],
    );
}

#[test]
fn affine_integer_neg_derivative_y() {
    matrix(
        "affine-integer-neg-derivative-y",
        &["affine-neg-derivative-y-integer-identity"],
    );
}

#[test]
fn affine_integer_neg_equation() {
    matrix(
        "affine-integer-neg-equation",
        &["affine-neg-equation-integer-identity"],
    );
}

#[test]
fn affine_integer_neg_y_involution() {
    matrix(
        "affine-integer-neg-y-involution",
        &["affine-neg-y-involution-integer-identity"],
    );
}

#[test]
fn affine_integer_secant_cubic_derivative() {
    matrix(
        "affine-integer-secant-cubic-derivative",
        &["affine-secant-cubic-derivative-integer-identity"],
    );
}

#[test]
fn affine_integer_secant_cubic_interpolation() {
    matrix(
        "affine-integer-secant-cubic-interpolation",
        &["affine-secant-cubic-interpolation-integer-identity"],
    );
}

#[test]
fn affine_integer_tangent_cubic_derivative() {
    matrix(
        "affine-integer-tangent-cubic-derivative",
        &["affine-tangent-cubic-derivative-integer-identity"],
    );
}

#[test]
fn affine_integer_tangent_cubic_expansion() {
    matrix(
        "affine-integer-tangent-cubic-expansion",
        &["affine-tangent-cubic-expansion-integer-identity"],
    );
}

#[test]
fn finite_affine_coordinate_congruence() {
    matrix(
        "finite-affine-coordinate-congruence",
        &["finite-affine-coordinate-congruent"],
    );
}

#[test]
fn finite_affine_cubic_divided_difference_polynomial() {
    matrix(
        "finite-affine-cubic-divided-difference-polynomial",
        &["finite-affine-cubic-divided-difference-polynomial"],
    );
}

#[test]
fn finite_affine_derivative_y_difference_polynomial() {
    matrix(
        "finite-affine-derivative-y-difference-polynomial",
        &["finite-affine-derivative-y-difference-polynomial"],
    );
}

#[test]
fn finite_affine_equal_x_factor_polynomial() {
    matrix(
        "finite-affine-equal-x-factor-polynomial",
        &["finite-affine-equal-x-factor-polynomial"],
    );
}

#[test]
fn finite_affine_line_cubic_derivative_polynomial() {
    matrix(
        "finite-affine-line-cubic-derivative-polynomial",
        &["finite-affine-line-cubic-derivative-polynomial"],
    );
}

#[test]
fn finite_affine_line_cubic_evaluation_polynomial() {
    matrix(
        "finite-affine-line-cubic-evaluation-polynomial",
        &["finite-affine-line-cubic-evaluation-polynomial"],
    );
}

#[test]
fn finite_affine_line_intercept_polynomial() {
    matrix(
        "finite-affine-line-intercept-polynomial",
        &["finite-affine-line-intercept-polynomial"],
    );
}

#[test]
fn finite_affine_neg_derivative_x_polynomial() {
    matrix(
        "finite-affine-neg-derivative-x-polynomial",
        &["finite-affine-neg-derivative-x-polynomial"],
    );
}

#[test]
fn finite_affine_neg_derivative_y_polynomial() {
    matrix(
        "finite-affine-neg-derivative-y-polynomial",
        &["finite-affine-neg-derivative-y-polynomial"],
    );
}

#[test]
fn finite_affine_neg_equation_polynomial() {
    matrix(
        "finite-affine-neg-equation-polynomial",
        &["finite-affine-neg-equation-polynomial"],
    );
}

#[test]
fn finite_affine_neg_y_involution_polynomial() {
    matrix(
        "finite-affine-neg-y-involution-polynomial",
        &["finite-affine-neg-y-involution-polynomial"],
    );
}

#[test]
fn finite_affine_point_equal_x() {
    matrix(
        "finite-affine-point-equal-x",
        &[
            "finite-affine-point-equal-x-cases",
            "finite-affine-point-equal-x-cases-back",
        ],
    );
}

#[test]
fn finite_affine_point_negation() {
    matrix(
        "finite-affine-point-negation",
        &[
            "finite-affine-point-negate-infinity",
            "finite-affine-point-negate-coordinate",
            "finite-affine-coordinate-y-congruent",
            "finite-affine-point-negate-involutive",
            "finite-affine-point-negate-injective",
            "finite-affine-point-negate-tag",
            "finite-affine-point-negate-x-or-zero",
        ],
    );
}

#[test]
fn finite_affine_secant_cubic_derivative_polynomial() {
    matrix(
        "finite-affine-secant-cubic-derivative-polynomial",
        &["finite-affine-secant-cubic-derivative-polynomial"],
    );
}

#[test]
fn finite_affine_secant_cubic_interpolation_polynomial() {
    matrix(
        "finite-affine-secant-cubic-interpolation-polynomial",
        &["finite-affine-secant-cubic-interpolation-polynomial"],
    );
}

#[test]
fn finite_affine_tangent_cubic_derivative_polynomial() {
    matrix(
        "finite-affine-tangent-cubic-derivative-polynomial",
        &["finite-affine-tangent-cubic-derivative-polynomial"],
    );
}

#[test]
fn finite_affine_tangent_cubic_expansion_polynomial() {
    matrix(
        "finite-affine-tangent-cubic-expansion-polynomial",
        &["finite-affine-tangent-cubic-expansion-polynomial"],
    );
}

#[test]
fn finite_residue_decision_choice() {
    matrix(
        "finite-residue-decision-choice",
        &["finite-residue-choice-yes", "finite-residue-choice-no"],
    );
}

#[test]
fn finite_residue_geometric_differences() {
    matrix(
        "finite-residue-geometric-differences",
        &[
            "finite-residue-difference-zero-implies-equal",
            "finite-residue-difference-of-unequal-nonzero",
            "finite-prime-zero-product-cases",
        ],
    );
}

#[test]
fn finite_residue_geometric_division() {
    matrix(
        "finite-residue-geometric-division",
        &[
            "finite-residue-divide-zero",
            "finite-prime-divide-multiply",
            "finite-residue-value-nonzero",
        ],
    );
}

#[test]
fn finite_weierstrass_add_coordinates() {
    matrix(
        "finite-weierstrass-add-coordinates",
        &[
            "finite-weierstrass-add-y-inverse",
            "finite-weierstrass-add-x-symmetric",
        ],
    );
}

#[test]
fn finite_weierstrass_equal_x_cases() {
    matrix(
        "finite-weierstrass-equal-x-cases",
        &[
            "finite-weierstrass-equal-x-y-cases",
            "finite-weierstrass-equal-x-not-neg-equal-y",
        ],
    );
}

#[test]
fn finite_weierstrass_equal_x_factor() {
    matrix(
        "finite-weierstrass-equal-x-factor",
        &["finite-weierstrass-equal-x-factor"],
    );
}

#[test]
fn finite_weierstrass_line_evaluation() {
    matrix(
        "finite-weierstrass-line-evaluation",
        &[
            "finite-weierstrass-line-at-origin",
            "finite-weierstrass-secant-line-at-other",
        ],
    );
}

#[test]
fn finite_weierstrass_neg_y() {
    matrix(
        "finite-weierstrass-neg-y",
        &["finite-weierstrass-neg-y-definition"],
    );
}

#[test]
fn finite_weierstrass_negation_formulas() {
    matrix(
        "finite-weierstrass-negation-formulas",
        &[
            "finite-weierstrass-neg-y-involution",
            "finite-weierstrass-neg-equation",
            "finite-weierstrass-neg-derivative-x",
            "finite-weierstrass-neg-derivative-y",
            "finite-weierstrass-derivative-y-difference",
            "finite-weierstrass-equation-negate",
            "finite-weierstrass-neg-y-congruent",
        ],
    );
}

#[test]
fn finite_weierstrass_negation_nonsingular() {
    matrix(
        "finite-weierstrass-negation-nonsingular",
        &[
            "finite-weierstrass-neg-y-derivative-nonzero",
            "finite-weierstrass-neg-x-derivative-nonzero",
            "finite-weierstrass-nonsingular-negate",
            "finite-weierstrass-nonsingular-negate-back",
        ],
    );
}

#[test]
fn finite_weierstrass_slope_certificates() {
    matrix(
        "finite-weierstrass-slope-certificates",
        &[
            "finite-weierstrass-tangent-denominator-nonzero",
            "finite-weierstrass-tangent-derivative-zero",
            "finite-weierstrass-secant-product",
        ],
    );
}

#[test]
fn finite_weierstrass_slopes() {
    matrix(
        "finite-weierstrass-slopes",
        &[
            "finite-weierstrass-slope-secant",
            "finite-weierstrass-slope-vertical",
            "finite-weierstrass-slope-tangent",
        ],
    );
}
