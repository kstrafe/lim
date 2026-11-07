//! Inventory every native quadratic division, evaluation and quotient theorem.
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
        "lim-quadratic-matrix-{}-{module}",
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
fn quadratic_division_data() {
    matrix(
        "quadratic-division-data",
        &["quadratic-division-divisor-coefficient-two"],
    );
}

#[test]
fn quadratic_division_equation() {
    matrix(
        "quadratic-division-equation",
        &["quadratic-division-equation"],
    );
}

#[test]
fn quadratic_division_local_equation() {
    matrix(
        "quadratic-division-local-equation",
        &["quadratic-division-local-equation"],
    );
}

#[test]
fn quadratic_division_scalar_laws() {
    matrix(
        "quadratic-division-scalar-laws",
        &[
            "quadratic-division-constant-cancellation",
            "quadratic-division-linear-cancellation",
        ],
    );
}

#[test]
fn quadratic_division_step_equation() {
    matrix(
        "quadratic-division-step-equation",
        &["quadratic-division-step-equation"],
    );
}

#[test]
fn quadratic_quotient_coefficient_add_constant_identity() {
    matrix(
        "quadratic-quotient-coefficient-add-constant-identity",
        &["quadratic-quotient-coefficient-add-constant-identity"],
    );
}

#[test]
fn quadratic_quotient_coefficient_add_linear_identity() {
    matrix(
        "quadratic-quotient-coefficient-add-linear-identity",
        &["quadratic-quotient-coefficient-add-linear-identity"],
    );
}

#[test]
fn quadratic_quotient_coefficient_map() {
    matrix(
        "quadratic-quotient-coefficient-map",
        &["quadratic-quotient-coefficient-map-value"],
    );
}

#[test]
fn quadratic_quotient_coefficient_multiply_constant_identity() {
    matrix(
        "quadratic-quotient-coefficient-multiply-constant-identity",
        &["quadratic-quotient-coefficient-multiply-constant-identity"],
    );
}

#[test]
fn quadratic_quotient_coefficient_multiply_linear_identity() {
    matrix(
        "quadratic-quotient-coefficient-multiply-linear-identity",
        &["quadratic-quotient-coefficient-multiply-linear-identity"],
    );
}

#[test]
fn quadratic_quotient_congruence() {
    matrix(
        "quadratic-quotient-congruence",
        &[
            "quadratic-quotient-coefficients-equal",
            "quadratic-quotient-add-congruent",
            "quadratic-quotient-multiply-congruent",
            "quadratic-quotient-negate-congruent",
        ],
    );
}

#[test]
fn quadratic_quotient_correspondence() {
    matrix(
        "quadratic-quotient-correspondence",
        &[
            "quadratic-quotient-equal-evaluations",
            "quadratic-quotient-evaluations-equal",
            "quadratic-quotient-equal-iff",
        ],
    );
}

#[test]
fn quadratic_quotient_divisibility() {
    matrix(
        "quadratic-quotient-divisibility",
        &[
            "quadratic-quotient-multiple-zero",
            "quadratic-quotient-divides-zero",
        ],
    );
}

#[test]
fn quadratic_quotient_divisor_zero_constant_identity() {
    matrix(
        "quadratic-quotient-divisor-zero-constant-identity",
        &["quadratic-quotient-divisor-zero-constant-identity"],
    );
}

#[test]
fn quadratic_quotient_divisor_zero_linear_identity() {
    matrix(
        "quadratic-quotient-divisor-zero-linear-identity",
        &["quadratic-quotient-divisor-zero-linear-identity"],
    );
}

#[test]
fn quadratic_quotient_equivalence() {
    matrix(
        "quadratic-quotient-equivalence",
        &[
            "quadratic-quotient-reflexive",
            "quadratic-quotient-symmetric",
            "quadratic-quotient-transitive",
        ],
    );
}

#[test]
fn quadratic_quotient_evaluation() {
    matrix(
        "quadratic-quotient-evaluation",
        &[
            "quadratic-quotient-linear-evaluates",
            "quadratic-quotient-divisor-evaluates-zero",
        ],
    );
}

#[test]
fn quadratic_quotient_isomorphism() {
    matrix(
        "quadratic-quotient-isomorphism",
        &[
            "quadratic-quotient-forward-inverse",
            "quadratic-quotient-inverse-forward",
        ],
    );
}

#[test]
fn quadratic_quotient_kernel() {
    matrix(
        "quadratic-quotient-kernel",
        &[
            "quadratic-quotient-zero-divides",
            "quadratic-quotient-kernel",
        ],
    );
}

#[test]
fn quadratic_quotient_linear_evaluation_constant_identity() {
    matrix(
        "quadratic-quotient-linear-evaluation-constant-identity",
        &["quadratic-quotient-linear-evaluation-constant-identity"],
    );
}

#[test]
fn quadratic_quotient_linear_evaluation_linear_identity() {
    matrix(
        "quadratic-quotient-linear-evaluation-linear-identity",
        &["quadratic-quotient-linear-evaluation-linear-identity"],
    );
}

#[test]
fn quadratic_quotient_linear_operations() {
    matrix(
        "quadratic-quotient-linear-operations",
        &[
            "quadratic-quotient-linear-add",
            "quadratic-quotient-linear-multiply",
            "quadratic-quotient-linear-negate",
            "quadratic-quotient-linear-normal-form",
        ],
    );
}

#[test]
fn quadratic_quotient_relation() {
    matrix(
        "quadratic-quotient-relation",
        &["quadratic-quotient-difference-evaluation"],
    );
}

#[test]
fn quadratic_quotient_remainder_correspondence() {
    matrix(
        "quadratic-quotient-remainder-correspondence",
        &[
            "quadratic-quotient-equal-remainders",
            "quadratic-quotient-remainders-equal",
            "quadratic-quotient-remainder-iff",
        ],
    );
}

#[test]
fn quadratic_quotient_remainder_evaluation() {
    matrix(
        "quadratic-quotient-remainder-evaluation",
        &["quadratic-quotient-remainder-evaluation"],
    );
}

#[test]
fn quadratic_quotient_ring_structure() {
    matrix(
        "quadratic-quotient-ring-structure",
        &["quadratic-quotient-ring-equality"],
    );
}

#[test]
fn quadratic_quotient_zero_remainder() {
    matrix(
        "quadratic-quotient-zero-remainder",
        &["quadratic-quotient-zero-remainder"],
    );
}

#[test]
fn ring_evaluation_addition() {
    matrix("ring-evaluation-addition", &["ring-evaluation-add"]);
}

#[test]
fn ring_evaluation_congruence() {
    matrix("ring-evaluation-congruence", &["ring-evaluation-congruent"]);
}

#[test]
fn ring_evaluation_data() {
    matrix(
        "ring-evaluation-data",
        &[
            "ring-evaluation-zero",
            "ring-evaluation-constant",
            "ring-evaluation-shift",
            "ring-evaluation-one",
        ],
    );
}

#[test]
fn ring_evaluation_morphism() {
    matrix(
        "ring-evaluation-morphism",
        &[
            "ring-evaluation-map-congruent",
            "ring-evaluation-map-zero",
            "ring-evaluation-map-one",
            "ring-evaluation-map-add",
            "ring-evaluation-map-multiply",
        ],
    );
}

#[test]
fn ring_evaluation_multiplication() {
    matrix(
        "ring-evaluation-multiplication",
        &["ring-evaluation-multiply"],
    );
}

#[test]
fn ring_evaluation_negation() {
    matrix("ring-evaluation-negation", &["ring-evaluation-negate"]);
}

#[test]
fn ring_evaluation_scaling() {
    matrix("ring-evaluation-scaling", &["ring-evaluation-scale"]);
}

#[test]
fn ring_evaluation_zero_coefficients() {
    matrix(
        "ring-evaluation-zero-coefficients",
        &["ring-evaluation-zero-coefficients"],
    );
}

#[test]
fn weierstrass_coordinate_quotient() {
    matrix(
        "weierstrass-coordinate-quotient",
        &[
            "weierstrass-coordinate-quotient-correspondence",
            "weierstrass-coordinate-quotient-forward-inverse",
            "weierstrass-coordinate-quotient-inverse-forward",
        ],
    );
}
