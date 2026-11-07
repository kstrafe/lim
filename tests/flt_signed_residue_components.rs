//! Audit every signed reduction and finite point declaration with the native kernel.
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
fn decidable_negation() {
    matrix("decidable-negation", &["decision-negation-has-evidence"]);
}

#[test]
fn finite_residue_additive_rearrangement() {
    matrix(
        "finite-residue-additive-rearrangement",
        &[
            "finite-residue-add-swap-inner",
            "finite-residue-add-shuffle-four",
            "finite-residue-negate-add",
        ],
    );
}

#[test]
fn finite_residue_cancellation() {
    matrix(
        "finite-residue-cancellation",
        &[
            "finite-residue-add-cancel-left",
            "finite-residue-add-cancel-right",
            "finite-residue-negate-unique",
            "finite-residue-negate-zero",
            "finite-residue-negate-involution",
        ],
    );
}

#[test]
fn finite_residue_congruence_laws() {
    matrix(
        "finite-residue-congruence-laws",
        &[
            "finite-residue-add-congruent",
            "finite-residue-multiply-congruent",
            "finite-residue-negate-congruent",
            "finite-residue-zero-value",
            "finite-residue-add-inverse-zero",
            "finite-residue-add-inverse-left-zero",
            "finite-residue-add-zero-left",
        ],
    );
}

#[test]
fn finite_residue_difference_congruence() {
    matrix(
        "finite-residue-difference-congruence",
        &[
            "finite-residue-difference-cross-congruent",
            "finite-residue-difference-product-expand",
            "finite-residue-difference-product",
        ],
    );
}

#[test]
fn finite_residue_differences() {
    matrix(
        "finite-residue-differences",
        &[
            "finite-residue-difference-congruent",
            "finite-residue-difference-self",
            "finite-residue-difference-zero-right",
            "finite-residue-difference-zero-left",
            "finite-residue-difference-add-denominator",
            "finite-residue-difference-add-two",
            "finite-residue-difference-sum",
            "finite-residue-difference-negate",
        ],
    );
}

#[test]
fn finite_residue_extensional() {
    matrix(
        "finite-residue-extensional",
        &[
            "finite-residue-extensional",
            "finite-residue-value-congruence",
        ],
    );
}

#[test]
fn finite_residue_integer_cast() {
    matrix(
        "finite-residue-integer-cast",
        &[
            "finite-residue-integer-natural",
            "finite-residue-integer-negative-natural",
            "finite-residue-integer-negate",
            "finite-residue-integer-congruent",
            "finite-residue-integer-zero",
            "finite-residue-integer-one",
        ],
    );
}

#[test]
fn finite_residue_integer_operations() {
    matrix(
        "finite-residue-integer-operations",
        &[
            "finite-reduction-sum-products",
            "finite-residue-integer-add",
            "finite-residue-integer-multiply",
            "finite-residue-integer-difference",
        ],
    );
}

#[test]
fn finite_residue_multiplicative_signs() {
    matrix(
        "finite-residue-multiplicative-signs",
        &[
            "finite-residue-multiply-zero-right",
            "finite-residue-multiply-zero-left",
            "finite-residue-distribute-first",
            "finite-residue-multiply-negate-first",
            "finite-residue-multiply-negate-second",
            "finite-residue-multiply-negate-both",
        ],
    );
}

#[test]
fn finite_residue_powers() {
    matrix(
        "finite-residue-powers",
        &[
            "finite-residue-power-zero",
            "finite-residue-power-successor",
            "finite-residue-power-congruent",
            "finite-residue-integer-power",
        ],
    );
}

#[test]
fn finite_weierstrass_equivalence() {
    matrix(
        "finite-weierstrass-equivalence",
        &[
            "finite-weierstrass-reflexive",
            "finite-weierstrass-symmetric",
            "finite-weierstrass-transitive",
        ],
    );
}

#[test]
fn finite_weierstrass_integer_evaluation() {
    matrix(
        "finite-weierstrass-integer-evaluation",
        &[
            "finite-weierstrass-integer-polynomial-map",
            "finite-weierstrass-integer-derivative-x-map",
            "finite-weierstrass-integer-derivative-y-map",
            "finite-weierstrass-integer-equation-map",
        ],
    );
}

#[test]
fn finite_weierstrass_point_congruence() {
    matrix(
        "finite-weierstrass-point-congruence",
        &[
            "finite-weierstrass-polynomial-congruent",
            "finite-weierstrass-derivative-x-congruent",
            "finite-weierstrass-derivative-y-congruent",
            "finite-weierstrass-equation-congruent",
            "finite-weierstrass-nonsingular-congruent",
        ],
    );
}

#[test]
fn finite_weierstrass_point_decisions() {
    matrix(
        "finite-weierstrass-point-decisions",
        &["finite-weierstrass-nonsingular-decided"],
    );
}

#[test]
fn finite_weierstrass_points() {
    matrix(
        "finite-weierstrass-points",
        &[
            "finite-weierstrass-equation-of-nonsingular",
            "finite-weierstrass-derivative-of-nonsingular",
        ],
    );
}

#[test]
fn finite_weierstrass_reduction() {
    matrix(
        "finite-weierstrass-reduction",
        &[
            "finite-weierstrass-reduction-congruent",
            "finite-weierstrass-reduction-a1",
            "finite-weierstrass-reduction-a2",
            "finite-weierstrass-reduction-a3",
            "finite-weierstrass-reduction-a4",
            "finite-weierstrass-reduction-a6",
        ],
    );
}
