//! Bounded theorem matrix for the newly added FLT norm and integer proofs.
use lim::{check_theorem_details_from_path_with_config, CompileConfig};
use std::path::Path;

const INTEGER_AND_SCALAR_TARGETS: &[(&str, &str)] = &[
    (
        "eisenstein-norm-scalar-conjugate-add-omega.lim",
        "eisenstein-norm-scalar-conjugate-add-omega",
    ),
    (
        "eisenstein-norm-scalar-conjugate-add-real.lim",
        "eisenstein-norm-scalar-conjugate-add-real",
    ),
    (
        "eisenstein-norm-scalar-conjugate-involution-omega.lim",
        "eisenstein-norm-scalar-conjugate-involution-omega",
    ),
    (
        "eisenstein-norm-scalar-conjugate-involution-real.lim",
        "eisenstein-norm-scalar-conjugate-involution-real",
    ),
    (
        "eisenstein-norm-scalar-conjugate-product-omega.lim",
        "eisenstein-norm-scalar-conjugate-product-omega",
    ),
    (
        "eisenstein-norm-scalar-conjugate-product-real.lim",
        "eisenstein-norm-scalar-conjugate-product-real",
    ),
    (
        "eisenstein-norm-scalar-norm-conjugate.lim",
        "eisenstein-norm-scalar-norm-conjugate",
    ),
    (
        "eisenstein-norm-scalar-norm-difference-square.lim",
        "eisenstein-norm-scalar-norm-difference-square",
    ),
    (
        "eisenstein-norm-scalar-norm-four-square-omega.lim",
        "eisenstein-norm-scalar-norm-four-square-omega",
    ),
    (
        "eisenstein-norm-scalar-norm-four-square-real.lim",
        "eisenstein-norm-scalar-norm-four-square-real",
    ),
    (
        "eisenstein-norm-scalar-norm-negative.lim",
        "eisenstein-norm-scalar-norm-negative",
    ),
    (
        "eisenstein-norm-scalar-norm-scalar.lim",
        "eisenstein-norm-scalar-norm-scalar",
    ),
    (
        "eisenstein-norm-scalar-product-conjugate-omega.lim",
        "eisenstein-norm-scalar-product-conjugate-omega",
    ),
    (
        "eisenstein-norm-scalar-product-conjugate-real.lim",
        "eisenstein-norm-scalar-product-conjugate-real",
    ),
    ("integer-domain.lim", "integer-equality-decided"),
    ("integer-domain.lim", "integer-natural-embedding-nonzero"),
    ("integer-domain.lim", "integer-nonzero-product"),
    ("integer-domain.lim", "integer-product-zero-cancel-first"),
    ("integer-domain.lim", "integer-square-zero"),
    ("integer-domain.lim", "integer-multiply-cancel-first"),
    ("integer-nonnegative.lim", "integer-natural-nonnegative"),
    ("integer-nonnegative.lim", "integer-nonnegative-congruent"),
    ("integer-nonnegative.lim", "integer-nonnegative-add"),
    ("integer-nonnegative.lim", "integer-nonnegative-multiply"),
    (
        "integer-nonnegative.lim",
        "integer-square-magnitude-positive",
    ),
    ("integer-nonnegative.lim", "integer-square-nonnegative"),
    (
        "integer-nonnegative.lim",
        "integer-nonnegative-zero-sum-first",
    ),
    (
        "integer-nonnegative.lim",
        "integer-nonnegative-zero-sum-second",
    ),
    (
        "integer-nonnegative.lim",
        "integer-negative-natural-nonnegative-zero",
    ),
    (
        "integer-nonnegative.lim",
        "integer-nonnegative-scale-reflect",
    ),
];

const MULTIPLICITY_TARGETS: &[(&str, &str)] = &[
    ("natural-power-growth.lim", "successor-below-triple"),
    ("natural-power-growth.lim", "exponent-below-three-power"),
    (
        "eisenstein-norm-divisibility.lim",
        "eisenstein-natural-norm-divides",
    ),
    (
        "eisenstein-lambda-multiplicity.lim",
        "eisenstein-lambda-power-norm-divides",
    ),
    (
        "eisenstein-lambda-multiplicity.lim",
        "eisenstein-lambda-power-norm-bound",
    ),
    (
        "eisenstein-lambda-multiplicity.lim",
        "eisenstein-lambda-finite-multiplicity",
    ),
];

const REMAINING_TARGETS: &[(&str, &str)] = &[
    ("eisenstein-conjugate.lim", "eisenstein-conjugate-congruent"),
    (
        "eisenstein-conjugate.lim",
        "eisenstein-conjugate-involution",
    ),
    ("eisenstein-conjugate.lim", "eisenstein-conjugate-add"),
    ("eisenstein-conjugate.lim", "eisenstein-conjugate-product"),
    ("eisenstein-conjugate.lim", "eisenstein-product-conjugate"),
    ("eisenstein-domain.lim", "eisenstein-equality-decided"),
    ("eisenstein-domain.lim", "eisenstein-nonzero-product"),
    (
        "eisenstein-domain.lim",
        "eisenstein-product-zero-cancel-first",
    ),
    ("eisenstein-domain.lim", "eisenstein-zero-difference"),
    ("eisenstein-domain.lim", "eisenstein-multiply-cancel-first"),
    ("eisenstein-domain.lim", "eisenstein-multiply-cancel-second"),
    ("eisenstein-domain.lim", "eisenstein-product-zero-cases"),
    (
        "eisenstein-natural-norm-multiply.lim",
        "eisenstein-natural-norm-multiply",
    ),
    (
        "eisenstein-natural-norm-properties.lim",
        "eisenstein-natural-norm-nonzero",
    ),
    (
        "eisenstein-natural-norm-properties.lim",
        "eisenstein-natural-norm-one",
    ),
    (
        "eisenstein-natural-norm-properties.lim",
        "eisenstein-natural-norm-lambda",
    ),
    (
        "eisenstein-natural-norm-properties.lim",
        "eisenstein-natural-norm-power",
    ),
    ("eisenstein-norm-basic.lim", "eisenstein-norm-congruent"),
    ("eisenstein-norm-basic.lim", "eisenstein-norm-zero"),
    ("eisenstein-norm-basic.lim", "eisenstein-norm-one"),
    ("eisenstein-norm-basic.lim", "eisenstein-norm-lambda"),
    (
        "eisenstein-norm-multiply.lim",
        "eisenstein-multiply-left-commutative",
    ),
    (
        "eisenstein-norm-multiply.lim",
        "eisenstein-multiply-four-interchange",
    ),
    ("eisenstein-norm-multiply.lim", "eisenstein-norm-multiply"),
    (
        "eisenstein-norm-nondegenerate.lim",
        "eisenstein-norm-zero-omega",
    ),
    (
        "eisenstein-norm-nondegenerate.lim",
        "eisenstein-norm-zero-real",
    ),
    (
        "eisenstein-norm-nondegenerate.lim",
        "eisenstein-norm-zero-implies-zero",
    ),
    (
        "eisenstein-norm-nondegenerate.lim",
        "eisenstein-zero-implies-norm-zero",
    ),
    (
        "eisenstein-norm-nondegenerate.lim",
        "eisenstein-nonzero-norm",
    ),
    (
        "eisenstein-norm-nonnegative.lim",
        "eisenstein-norm-nonnegative",
    ),
    (
        "eisenstein-norm-nonnegative.lim",
        "eisenstein-natural-norm-exists",
    ),
    (
        "eisenstein-norm-nonnegative.lim",
        "eisenstein-natural-norm-unique",
    ),
    (
        "eisenstein-norm-nonnegative.lim",
        "eisenstein-natural-norm-congruent",
    ),
    (
        "eisenstein-norm-squares.lim",
        "eisenstein-norm-four-squares",
    ),
    ("eisenstein-norm-squares.lim", "eisenstein-norm-of-integer"),
    (
        "eisenstein-norm-symmetries.lim",
        "eisenstein-norm-conjugate",
    ),
    ("eisenstein-norm-symmetries.lim", "eisenstein-norm-negative"),
    (
        "eisenstein-norm-symmetries.lim",
        "eisenstein-norm-four-square-real",
    ),
    (
        "eisenstein-norm-symmetries.lim",
        "eisenstein-norm-difference-square",
    ),
    (
        "eisenstein-norm-unit.lim",
        "eisenstein-unit-natural-norm-one",
    ),
    (
        "eisenstein-norm-unit.lim",
        "eisenstein-unit-of-natural-norm-one",
    ),
];

fn check_matrix(targets: &[(&str, &str)]) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let config = CompileConfig::default();
    for &(module, target) in targets {
        let path = root.join("theorems/flt").join(module);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
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
fn integer_domain_nonnegative_and_scalar_norm_theorems_are_foundation_free() {
    check_matrix(INTEGER_AND_SCALAR_TARGETS);
}

#[test]
fn remaining_new_norm_theorems_are_foundation_free() {
    check_matrix(REMAINING_TARGETS);
}

#[test]
fn lambda_finite_multiplicity_theorems_are_foundation_free() {
    check_matrix(MULTIPLICITY_TARGETS);
}
