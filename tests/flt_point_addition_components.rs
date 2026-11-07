//! Inventory native point-ideal addition prerequisites and conditional identities.
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
        "lim-point-addition-matrix-{}-{module}",
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
fn point_ideal_addition_x_image_scalar() {
    matrix(
        "point-ideal-addition-X-image-scalar",
        &["point-ideal-addition-X-image-scalar"],
    );
}

#[test]
fn point_ideal_addition_x_image() {
    matrix(
        "point-ideal-addition-X-image",
        &["point-ideal-addition-X-image"],
    );
}

#[test]
fn point_ideal_addition_colon_members() {
    matrix(
        "point-ideal-addition-colon-members",
        &[
            "point-ideal-addition-colon-first",
            "point-ideal-addition-colon-second",
            "point-ideal-addition-colon-line",
            "point-ideal-addition-colon-opposite",
        ],
    );
}

#[test]
fn point_ideal_addition_common_colon() {
    matrix(
        "point-ideal-addition-common-colon",
        &["point-ideal-addition-common-colon"],
    );
}

#[test]
fn point_ideal_addition_common_members() {
    matrix(
        "point-ideal-addition-common-members",
        &[
            "point-ideal-addition-common-contains-point",
            "point-ideal-addition-common-contains-second",
            "point-ideal-addition-common-contains-opposite",
        ],
    );
}

#[test]
fn point_ideal_addition_coordinate_field_unit() {
    matrix(
        "point-ideal-addition-coordinate-field-unit",
        &["point-ideal-addition-coordinate-field-unit"],
    );
}

#[test]
fn point_ideal_addition_coordinate_kernel() {
    matrix(
        "point-ideal-addition-coordinate-kernel",
        &["point-ideal-addition-coordinate-kernel"],
    );
}

#[test]
fn point_ideal_addition_coordinate_product() {
    matrix(
        "point-ideal-addition-coordinate-product",
        &["point-ideal-addition-coordinate-product"],
    );
}

#[test]
fn point_ideal_addition_coordinate_units() {
    matrix(
        "point-ideal-addition-coordinate-units",
        &[
            "point-ideal-addition-secant-unit",
            "point-ideal-addition-tangent-unit",
        ],
    );
}

#[test]
fn point_ideal_addition_evaluation_root_congruent() {
    matrix(
        "point-ideal-addition-evaluation-root-congruent",
        &["point-ideal-addition-evaluation-root-congruent"],
    );
}

#[test]
fn point_ideal_addition_forward_inclusion() {
    matrix(
        "point-ideal-addition-forward-inclusion",
        &["point-ideal-addition-forward-inclusion"],
    );
}

#[test]
fn point_ideal_addition_identity() {
    matrix(
        "point-ideal-addition-identity",
        &["point-ideal-addition-identity"],
    );
}

#[test]
fn point_ideal_addition_line_first() {
    matrix(
        "point-ideal-addition-line-first",
        &[
            "point-ideal-addition-line-first-scalar",
            "point-ideal-addition-line-first",
        ],
    );
}

#[test]
fn point_ideal_addition_line_generator_changes() {
    matrix(
        "point-ideal-addition-line-generator-changes",
        &[
            "point-ideal-addition-first-generator-change",
            "point-ideal-addition-second-generator-change",
        ],
    );
}

#[test]
fn point_ideal_addition_line_member() {
    matrix(
        "point-ideal-addition-line-member",
        &["point-ideal-addition-line-member"],
    );
}

#[test]
fn point_ideal_addition_line_polynomial() {
    matrix(
        "point-ideal-addition-line-polynomial",
        &[
            "point-ideal-addition-line-value-scalar",
            "point-ideal-addition-line-value",
        ],
    );
}

#[test]
fn point_ideal_addition_line_second() {
    matrix(
        "point-ideal-addition-line-second",
        &[
            "point-ideal-addition-line-second-scalar",
            "point-ideal-addition-line-second",
        ],
    );
}

#[test]
fn point_ideal_addition_norm_member() {
    matrix(
        "point-ideal-addition-norm-member",
        &["point-ideal-addition-norm-member"],
    );
}

#[test]
fn point_ideal_addition_opposite_image() {
    matrix(
        "point-ideal-addition-opposite-image",
        &["point-ideal-addition-opposite-image"],
    );
}

#[test]
fn point_ideal_addition_permutation_first() {
    matrix(
        "point-ideal-addition-permutation-first",
        &["point-ideal-addition-permutation-first"],
    );
}

#[test]
fn point_ideal_addition_permutation_line() {
    matrix(
        "point-ideal-addition-permutation-line",
        &["point-ideal-addition-permutation-line"],
    );
}

#[test]
fn point_ideal_addition_permutation_opposite() {
    matrix(
        "point-ideal-addition-permutation-opposite",
        &["point-ideal-addition-permutation-opposite"],
    );
}

#[test]
fn point_ideal_addition_permutation_second() {
    matrix(
        "point-ideal-addition-permutation-second",
        &["point-ideal-addition-permutation-second"],
    );
}

#[test]
fn point_ideal_addition_product_generators() {
    matrix(
        "point-ideal-addition-product-generators",
        &[
            "point-ideal-addition-generator-XX",
            "point-ideal-addition-generator-XL",
            "point-ideal-addition-generator-LX",
            "point-ideal-addition-generator-LL",
        ],
    );
}

#[test]
fn point_ideal_addition_reverse_inclusion() {
    matrix(
        "point-ideal-addition-reverse-inclusion",
        &["point-ideal-addition-reverse-inclusion"],
    );
}

#[test]
fn point_ideal_addition_scaled_pair_product() {
    matrix(
        "point-ideal-addition-scaled-pair-product",
        &["point-ideal-addition-scaled-pair-product"],
    );
}

#[test]
fn point_ideal_addition_source_left_product() {
    matrix(
        "point-ideal-addition-source-left-product",
        &["point-ideal-addition-source-left-product"],
    );
}

#[test]
fn point_ideal_addition_source_line_curve() {
    matrix(
        "point-ideal-addition-source-line-curve",
        &["point-ideal-addition-source-line-curve"],
    );
}

#[test]
fn point_ideal_addition_source_product() {
    matrix(
        "point-ideal-addition-source-product",
        &["point-ideal-addition-source-product"],
    );
}

#[test]
fn point_ideal_addition_source_right_product() {
    matrix(
        "point-ideal-addition-source-right-product",
        &["point-ideal-addition-source-right-product"],
    );
}

#[test]
fn point_ideal_addition_sum_generator_change() {
    matrix(
        "point-ideal-addition-sum-generator-change",
        &["point-ideal-addition-sum-generator-change"],
    );
}

#[test]
fn point_ideal_addition_target_members() {
    matrix(
        "point-ideal-addition-target-members",
        &[
            "point-ideal-addition-target-XX",
            "point-ideal-addition-target-XL",
            "point-ideal-addition-target-LX",
            "point-ideal-addition-target-LL",
        ],
    );
}
