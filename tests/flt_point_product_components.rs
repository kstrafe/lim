//! Inventory every native field and opposite point-ideal product theorem.
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
        "lim-point-product-matrix-{}-{module}",
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
fn point_ideal_product_curve_residual_identity() {
    matrix(
        "point-ideal-product-curve-residual-identity",
        &["point-ideal-product-curve-residual-identity"],
    );
}

#[test]
fn point_ideal_product_origin_partials() {
    matrix(
        "point-ideal-product-origin-partials",
        &[
            "point-ideal-product-origin-x-scalar",
            "point-ideal-product-origin-x",
            "point-ideal-product-origin-y-scalar",
            "point-ideal-product-origin-y",
            "point-ideal-product-origin-negative-y-scalar",
            "point-ideal-product-origin-negative-y",
        ],
    );
}

#[test]
fn point_ideal_product_field_data() {
    matrix(
        "point-ideal-product-field-data",
        &[
            "point-ideal-product-field-one-nonzero",
            "point-ideal-product-field-inverse",
        ],
    );
}

#[test]
fn point_ideal_product_field_domain() {
    matrix(
        "point-ideal-product-field-domain",
        &["point-ideal-product-field-product-nonzero"],
    );
}

#[test]
fn point_ideal_product_field_nonprincipal() {
    matrix(
        "point-ideal-product-field-nonprincipal",
        &["point-ideal-product-field-nonprincipal"],
    );
}

#[test]
fn point_ideal_product_four_generator_factor() {
    matrix(
        "point-ideal-product-four-generator-factor",
        &["point-ideal-product-four-generator-factor"],
    );
}

#[test]
fn point_ideal_product_generators_nonzero() {
    matrix(
        "point-ideal-product-generators-nonzero",
        &[
            "point-ideal-product-X-nonzero",
            "point-ideal-product-Y-nonzero",
        ],
    );
}

#[test]
fn point_ideal_product_image_unit_top() {
    matrix(
        "point-ideal-product-image-unit-top",
        &["point-ideal-product-image-unit-top"],
    );
}

#[test]
fn point_ideal_product_intrinsic_equality() {
    matrix(
        "point-ideal-product-intrinsic-equality",
        &["point-ideal-product-from-identity"],
    );
}

#[test]
fn point_ideal_product_mixed_factor() {
    matrix(
        "point-ideal-product-mixed-factor",
        &["point-ideal-product-mixed-factor"],
    );
}

#[test]
fn point_ideal_product_model_kernel_inclusion() {
    matrix(
        "point-ideal-product-model-kernel-inclusion",
        &["point-ideal-product-model-kernel-inclusion"],
    );
}

#[test]
fn point_ideal_product_model_nonsingular_top() {
    matrix(
        "point-ideal-product-model-nonsingular-top",
        &["point-ideal-product-model-nonsingular-top"],
    );
}

#[test]
fn point_ideal_product_model_opposite_ideal() {
    matrix(
        "point-ideal-product-model-opposite-ideal",
        &["point-ideal-product-model-opposite-ideal"],
    );
}

#[test]
fn point_ideal_product_model_opposite_product() {
    matrix(
        "point-ideal-product-model-opposite-product",
        &["point-ideal-product-model-opposite-product"],
    );
}

#[test]
fn point_ideal_product_model_partials() {
    matrix(
        "point-ideal-product-model-partials",
        &["point-ideal-product-model-opposite-image"],
    );
}

#[test]
fn point_ideal_product_model_quotient_image() {
    matrix(
        "point-ideal-product-model-quotient-image",
        &["point-ideal-product-model-quotient-image"],
    );
}

#[test]
fn point_ideal_product_model_unit_top() {
    matrix(
        "point-ideal-product-model-unit-top",
        &[
            "point-ideal-product-model-Y-unit-top",
            "point-ideal-product-model-X-unit-top",
        ],
    );
}

#[test]
fn point_ideal_product_nonsingular_data() {
    matrix(
        "point-ideal-product-nonsingular-data",
        &[
            "point-ideal-product-nonsingular-equation",
            "point-ideal-product-nonsingular-jacobian",
        ],
    );
}

#[test]
fn point_ideal_product_nonsingular_opposite() {
    matrix(
        "point-ideal-product-nonsingular-opposite",
        &["point-ideal-product-nonsingular-opposite"],
    );
}

#[test]
fn point_ideal_product_opposite_constant_identity() {
    matrix(
        "point-ideal-product-opposite-constant-identity",
        &["point-ideal-product-opposite-constant-identity"],
    );
}

#[test]
fn point_ideal_product_opposite_factorization() {
    matrix(
        "point-ideal-product-opposite-factorization",
        &["point-ideal-product-opposite-factorization"],
    );
}

#[test]
fn point_ideal_product_opposite_linear_factors() {
    matrix(
        "point-ideal-product-opposite-linear-factors",
        &["point-ideal-product-opposite-linear-factors"],
    );
}

#[test]
fn point_ideal_product_opposite_linear_identity() {
    matrix(
        "point-ideal-product-opposite-linear-identity",
        &["point-ideal-product-opposite-linear-identity"],
    );
}

#[test]
fn point_ideal_product_pair_congruence() {
    matrix(
        "point-ideal-product-pair-congruence",
        &["point-ideal-product-pair-congruent"],
    );
}

#[test]
fn point_ideal_product_prime_field() {
    matrix(
        "point-ideal-product-prime-field",
        &["point-ideal-product-prime-field-inverse"],
    );
}

#[test]
fn point_ideal_product_rational_field() {
    matrix(
        "point-ideal-product-rational-field",
        &["point-ideal-product-rational-field-inverse"],
    );
}

#[test]
fn point_ideal_product_residual_data() {
    matrix(
        "point-ideal-product-residual-data",
        &["point-ideal-product-polynomial-opposite-factors"],
    );
}

#[test]
fn point_ideal_product_residual_root() {
    matrix(
        "point-ideal-product-residual-root",
        &["point-ideal-product-residual-root"],
    );
}

#[test]
fn point_ideal_product_same_value_generator() {
    matrix(
        "point-ideal-product-same-value-generator",
        &["point-ideal-product-same-value-generator"],
    );
}

#[test]
fn point_ideal_product_same_value_ideals() {
    matrix(
        "point-ideal-product-same-value-ideals",
        &["point-ideal-product-same-value-ideals"],
    );
}

#[test]
fn point_ideal_product_value_difference() {
    matrix(
        "point-ideal-product-value-difference",
        &["point-ideal-product-value-difference-root"],
    );
}

#[test]
fn point_ideal_product_weierstrass_negative_value() {
    matrix(
        "point-ideal-product-weierstrass-negative-value",
        &[
            "point-ideal-product-weierstrass-negative-value-scalar",
            "point-ideal-product-weierstrass-negative-value-native",
            "point-ideal-product-weierstrass-negative-value",
        ],
    );
}

#[test]
fn point_ideal_product_weierstrass_opposite() {
    matrix(
        "point-ideal-product-weierstrass-opposite",
        &["point-ideal-product-weierstrass-opposite"],
    );
}

#[test]
fn point_ideal_product_weierstrass_opposite_value() {
    matrix(
        "point-ideal-product-weierstrass-opposite-value",
        &[
            "point-ideal-product-weierstrass-opposite-value-scalar",
            "point-ideal-product-weierstrass-opposite-value-native",
            "point-ideal-product-weierstrass-opposite-value",
        ],
    );
}

#[test]
fn point_ideal_product_weierstrass_quotient_jacobian() {
    matrix(
        "point-ideal-product-weierstrass-quotient-jacobian",
        &[
            "point-ideal-product-weierstrass-quotient-jacobian-scalar",
            "point-ideal-product-weierstrass-quotient-jacobian-residual-list",
            "point-ideal-product-weierstrass-quotient-jacobian-quotient-list",
            "point-ideal-product-weierstrass-quotient-jacobian-evaluate-list",
            "point-ideal-product-weierstrass-quotient-jacobian-quotient-bridge",
            "point-ideal-product-weierstrass-quotient-jacobian-native",
            "point-ideal-product-weierstrass-quotient-jacobian",
        ],
    );
}
