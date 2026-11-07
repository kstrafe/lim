//! Audit every new discriminant, model-comparison and prime declaration.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

fn matrix(module: &str, prefix: &str, first: usize, count: usize, public: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let declared: Vec<_> = source
        .lines()
        .filter_map(|line| line.strip_prefix("(#theorem ")?.split_whitespace().next())
        .collect();
    let width = if prefix == "discriminant-step-" { 4 } else { 3 };
    let mut expected: Vec<_> = (first..first + count)
        .map(|n| format!("{prefix}{n:0width$}"))
        .collect();
    expected.extend(public.iter().map(|s| (*s).to_owned()));
    assert_eq!(
        declared, expected,
        "every native helper must be inventoried"
    );
    let target = expected.last().unwrap();
    let total = if module.starts_with("frey-package-") {
        2
    } else {
        1
    };
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    config.set_proof_budget(
        ProofBudget::new(
            default.work(),
            default.phase_bytes(),
            total * 1024 * 1024 * 1024,
        )
        .unwrap(),
    );
    let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
        .unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty(), "{:?}", report.foundations);
}
#[test]
fn frey_package_all_primes() {
    matrix(
        "frey-package-all-primes",
        "",
        0,
        0,
        &[
            "frey-package-two-divides-discriminant",
            "frey-package-coordinate-prime-divides-discriminant",
            "frey-package-prime-divisors-equivalent",
        ],
    );
}

#[test]
fn frey_package_general_model_bad_primes() {
    matrix(
        "frey-package-general-model-bad-primes",
        "",
        0,
        0,
        &[
            "frey-package-model-bad-prime-transfer",
            "frey-package-not-good-prime-for-any-integral-model",
        ],
    );
}

#[test]
fn integer_integral_model_bad_primes() {
    matrix(
        "integer-integral-model-bad-primes",
        "",
        0,
        0,
        &["integer-integral-model-bad-prime-transfer"],
    );
}

#[test]
fn integer_integral_model_comparison() {
    matrix(
        "integer-integral-model-comparison",
        "",
        0,
        0,
        &["integer-integral-model-cross-invariant"],
    );
}

#[test]
fn integer_model_cross_reflection() {
    matrix(
        "integer-model-cross-reflection",
        "",
        0,
        0,
        &[
            "integer-cross-invariants-map",
            "integer-cross-invariants-reflect",
        ],
    );
}

#[test]
fn integer_prime_order_divides() {
    matrix(
        "integer-prime-order-divides",
        "",
        0,
        0,
        &[
            "integer-prime-order-successor-divides",
            "integer-prime-order-exponent-nondivisor-divides",
        ],
    );
}

#[test]
fn rational_c_invariants_weight_part_00() {
    matrix(
        "rational-c-invariants-weight-part-00",
        "discriminant-step-",
        0,
        128,
        &[],
    );
}

#[test]
fn rational_c_invariants_weight_part_01() {
    matrix(
        "rational-c-invariants-weight-part-01",
        "discriminant-step-",
        128,
        62,
        &[],
    );
}

#[test]
fn rational_c_invariants_weight() {
    matrix(
        "rational-c-invariants-weight",
        "",
        0,
        0,
        &["rational-c-invariants-weight-polynomial"],
    );
}

#[test]
fn rational_c_relation_polynomial_part_00() {
    matrix(
        "rational-c-relation-polynomial-part-00",
        "discriminant-step-",
        0,
        128,
        &[],
    );
}

#[test]
fn rational_c_relation_polynomial_part_01() {
    matrix(
        "rational-c-relation-polynomial-part-01",
        "discriminant-step-",
        128,
        128,
        &[],
    );
}

#[test]
fn rational_c_relation_polynomial_part_02() {
    matrix(
        "rational-c-relation-polynomial-part-02",
        "discriminant-step-",
        256,
        101,
        &[],
    );
}

#[test]
fn rational_c_relation_polynomial() {
    matrix(
        "rational-c-relation-polynomial",
        "",
        0,
        0,
        &["rational-c-relation-polynomial"],
    );
}

#[test]
fn rational_c6_scaling_part_00() {
    matrix(
        "rational-c6-scaling-part-00",
        "discriminant-step-",
        0,
        128,
        &[],
    );
}

#[test]
fn rational_c6_scaling_part_01() {
    matrix(
        "rational-c6-scaling-part-01",
        "discriminant-step-",
        128,
        7,
        &[],
    );
}

#[test]
fn rational_c6_scaling() {
    matrix(
        "rational-c6-scaling",
        "",
        0,
        0,
        &["rational-c6-scaling-polynomial"],
    );
}

#[test]
fn rational_c6_translation_part_00() {
    matrix(
        "rational-c6-translation-part-00",
        "discriminant-step-",
        0,
        128,
        &[],
    );
}

#[test]
fn rational_c6_translation_part_01() {
    matrix(
        "rational-c6-translation-part-01",
        "discriminant-step-",
        128,
        128,
        &[],
    );
}

#[test]
fn rational_c6_translation_part_02() {
    matrix(
        "rational-c6-translation-part-02",
        "discriminant-step-",
        256,
        7,
        &[],
    );
}

#[test]
fn rational_c6_translation() {
    matrix(
        "rational-c6-translation",
        "",
        0,
        0,
        &["rational-c6-translation-polynomial"],
    );
}

#[test]
fn rational_composite_powers() {
    matrix(
        "rational-composite-powers",
        "",
        0,
        0,
        &[
            "rational-power-add",
            "rational-power-iterate",
            "rational-power-compose",
            "rational-scaled-c4-cube",
        ],
    );
}

#[test]
fn rational_discriminant_cancellation() {
    matrix(
        "rational-discriminant-cancellation",
        "",
        0,
        0,
        &["rational-cancel-1728"],
    );
}

#[test]
fn rational_four_discriminant_polynomial() {
    matrix(
        "rational-four-discriminant-polynomial",
        "variable-change-step-",
        0,
        96,
        &["rational-four-discriminant-polynomial"],
    );
}

#[test]
fn rational_model_cross_invariant() {
    matrix(
        "rational-model-cross-invariant",
        "",
        0,
        0,
        &[
            "rational-two-scaled-invariants-cross",
            "rational-variable-changes-cross-invariant",
            "rational-integral-model-cross-invariant",
        ],
    );
}

#[test]
fn rational_unit_cancellation() {
    matrix(
        "rational-unit-cancellation",
        "",
        0,
        0,
        &["rational-cancel-unit-left", "rational-cancel-four"],
    );
}

#[test]
fn rational_variable_change_b6_scale() {
    matrix(
        "rational-variable-change-b6-scale",
        "variable-change-step-",
        0,
        68,
        &["rational-variable-change-b6-scale-polynomial"],
    );
}

#[test]
fn rational_variable_change_b6_translation() {
    matrix(
        "rational-variable-change-b6-translation",
        "variable-change-step-",
        0,
        275,
        &["rational-variable-change-b6-translation-polynomial"],
    );
}

#[test]
fn rational_variable_change_b6() {
    matrix(
        "rational-variable-change-b6",
        "",
        0,
        0,
        &["rational-variable-change-b6"],
    );
}

#[test]
fn rational_variable_change_c6() {
    matrix(
        "rational-variable-change-c6",
        "",
        0,
        0,
        &["rational-c6-value-congruent", "rational-variable-change-c6"],
    );
}

#[test]
fn rational_variable_change_discriminant() {
    matrix(
        "rational-variable-change-discriminant",
        "",
        0,
        0,
        &[
            "rational-c-numerator-congruent",
            "rational-variable-change-c-numerator",
            "rational-variable-change-discriminant-scaled",
            "rational-variable-change-discriminant",
        ],
    );
}

#[test]
fn rational_weierstrass_c_relation() {
    matrix(
        "rational-weierstrass-c-relation",
        "",
        0,
        0,
        &["rational-weierstrass-c-relation"],
    );
}

#[test]
fn rational_weierstrass_four_b8_polynomial() {
    matrix(
        "rational-weierstrass-four-b8-polynomial",
        "variable-change-step-",
        0,
        147,
        &["rational-weierstrass-four-b8-polynomial"],
    );
}

#[test]
fn rational_weierstrass_four_discriminant() {
    matrix(
        "rational-weierstrass-four-discriminant",
        "",
        0,
        0,
        &[
            "rational-weierstrass-four-b8",
            "rational-four-discriminant-substitute",
            "rational-weierstrass-four-discriminant",
        ],
    );
}
