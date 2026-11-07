//! Inventory every native point-addition theorem and its full source obligations.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;
fn matrix(module: &str, expected: &[&str], combined: bool) {
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
    let total = if combined {
        2 * 1024 * 1024 * 1024
    } else {
        1024 * 1024 * 1024
    };
    config.set_proof_budget(ProofBudget::new(budget.work(), budget.phase_bytes(), total).unwrap());
    let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
        .unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty());
}

#[test]
fn finite_affine_addition_transports() {
    matrix(
        "finite-affine-addition-transports",
        &[
            "finite-residue-zero-sum-first",
            "finite-residue-apply-congruent",
            "finite-residue-product-first-zero",
            "finite-residue-product-second-zero",
            "finite-residue-sum-both-zero",
        ],
        false,
    );
}

#[test]
fn finite_affine_cubic_data() {
    matrix(
        "finite-affine-cubic-data",
        &["finite-cubic-value-definition"],
        false,
    );
}

#[test]
fn finite_affine_cubic_identities() {
    matrix(
        "finite-affine-cubic-identities",
        &[
            "finite-cubic-difference",
            "finite-cubic-interpolation",
            "finite-cubic-derivative-factorization",
        ],
        false,
    );
}

#[test]
fn finite_affine_cubic_root_certificates() {
    matrix(
        "finite-affine-cubic-root-certificates",
        &[
            "finite-cubic-secant-quotient-zero",
            "finite-cubic-root-factorization",
            "finite-cubic-root-derivative-factorization",
            "finite-cubic-quotient-diagonal",
            "finite-cubic-stationary-factorization",
        ],
        false,
    );
}

#[test]
fn finite_affine_point_addition() {
    matrix(
        "finite-affine-point-addition",
        &[
            "finite-affine-point-zero-add",
            "finite-affine-point-add-zero",
        ],
        true,
    );
}

#[test]
fn finite_weierstrass_addition_equations() {
    matrix(
        "finite-weierstrass-addition-equations",
        &[
            "finite-weierstrass-slope-polynomial-factorization",
            "finite-weierstrass-slope-derivative-factorization",
            "finite-weierstrass-third-root",
            "finite-weierstrass-equation-neg-add",
            "finite-weierstrass-equation-add",
        ],
        true,
    );
}

#[test]
fn finite_weierstrass_addition_nonsingular() {
    matrix(
        "finite-weierstrass-addition-nonsingular",
        &[
            "finite-weierstrass-nonsingular-neg-add",
            "finite-weierstrass-nonsingular-add",
        ],
        true,
    );
}

#[test]
fn finite_weierstrass_line_cubic() {
    matrix(
        "finite-weierstrass-line-cubic",
        &[
            "finite-weierstrass-line-intercept-equation",
            "finite-weierstrass-line-substitution",
            "finite-weierstrass-line-cubic-evaluation",
            "finite-weierstrass-line-equation",
            "finite-weierstrass-line-derivative-substitution",
            "finite-weierstrass-line-cubic-derivative",
            "finite-weierstrass-line-derivative-equation",
        ],
        false,
    );
}

#[test]
fn finite_weierstrass_line_root_certificates() {
    matrix(
        "finite-weierstrass-line-root-certificates",
        &[
            "finite-weierstrass-line-first-root",
            "finite-weierstrass-line-second-root",
            "finite-weierstrass-line-stationary-root",
        ],
        false,
    );
}

#[test]
fn finite_weierstrass_nonsingular_transports() {
    matrix(
        "finite-weierstrass-nonsingular-transports",
        &[
            "finite-weierstrass-nonsingular-coordinate-transport",
            "finite-weierstrass-nonsingular-of-line-gradient",
        ],
        false,
    );
}

#[test]
fn finite_weierstrass_slope_cubic_certificates() {
    matrix(
        "finite-weierstrass-slope-cubic-certificates",
        &[
            "finite-weierstrass-secant-quotient-zero",
            "finite-weierstrass-tangent-quotient-zero",
            "finite-weierstrass-slope-quotient-zero",
        ],
        true,
    );
}

#[test]
fn finite_weierstrass_third_root_nonsingular() {
    matrix(
        "finite-weierstrass-third-root-nonsingular",
        &[
            "finite-weierstrass-third-root-derivative",
            "finite-weierstrass-third-root-gradient",
            "finite-weierstrass-third-root-gradient-nonzero",
            "finite-weierstrass-nonsingular-third-distant",
        ],
        true,
    );
}
