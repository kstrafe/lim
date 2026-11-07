//! Inventory every native ideal and coordinate point-ideal theorem.
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
    let directory =
        std::env::temp_dir().join(format!("lim-ideal-matrix-{}-{module}", std::process::id()));
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
fn coordinate_point_ideal_data() {
    matrix(
        "coordinate-point-ideal-data",
        &[
            "coordinate-point-ideal-X-constant",
            "coordinate-point-ideal-X-linear",
            "coordinate-point-ideal-Y-constant",
            "coordinate-point-ideal-Y-linear",
        ],
    );
}

#[test]
fn coordinate_point_ideal_membership() {
    matrix(
        "coordinate-point-ideal-membership",
        &[
            "coordinate-point-ideal-contains-X",
            "coordinate-point-ideal-contains-Y",
            "coordinate-point-ideal-least",
        ],
    );
}

#[test]
fn coordinate_point_ideal_product_expansion() {
    matrix(
        "coordinate-point-ideal-product-expansion",
        &["coordinate-point-ideal-product-expansion"],
    );
}

#[test]
fn ring_ideal_colon_element() {
    matrix(
        "ring-ideal-colon-element",
        &["ring-ideal-colon-element-member"],
    );
}

#[test]
fn ring_ideal_colon_factorization() {
    matrix(
        "ring-ideal-colon-factorization",
        &[
            "ring-ideal-product-to-colon",
            "ring-ideal-product-from-colon",
        ],
    );
}

#[test]
fn ring_ideal_data() {
    matrix(
        "ring-ideal-data",
        &[
            "ring-ideal-member-congruent",
            "ring-ideal-zero",
            "ring-ideal-add",
            "ring-ideal-negate",
            "ring-ideal-multiply-left",
            "ring-ideal-multiply-right",
        ],
    );
}

#[test]
fn ring_ideal_equivalence() {
    matrix(
        "ring-ideal-equivalence",
        &[
            "ring-ideal-subset-reflexive",
            "ring-ideal-subset-transitive",
            "ring-ideal-equal-reflexive",
            "ring-ideal-equal-symmetric",
            "ring-ideal-equal-transitive",
        ],
    );
}

#[test]
fn ring_ideal_expression() {
    matrix(
        "ring-ideal-expression",
        &["ring-ideal-expression-zero-value"],
    );
}

#[test]
fn ring_ideal_operation_congruence() {
    matrix(
        "ring-ideal-operation-congruence",
        &[
            "ring-ideal-product-congruent",
            "ring-ideal-sum-monotone",
            "ring-ideal-sum-congruent",
        ],
    );
}

#[test]
fn ring_ideal_pair() {
    matrix(
        "ring-ideal-pair",
        &[
            "ring-ideal-pair-first",
            "ring-ideal-pair-second",
            "ring-ideal-pair-least",
            "ring-ideal-pair-introduce",
            "ring-ideal-pair-coefficients",
        ],
    );
}

#[test]
fn ring_ideal_pair_bezout_top() {
    matrix(
        "ring-ideal-pair-bezout-top",
        &["ring-ideal-pair-bezout-top"],
    );
}

#[test]
fn ring_ideal_pair_generator_change() {
    matrix(
        "ring-ideal-pair-generator-change",
        &["ring-ideal-pair-add-multiple"],
    );
}

#[test]
fn ring_ideal_pair_product() {
    matrix("ring-ideal-pair-product", &["ring-ideal-pair-product"]);
}

#[test]
fn ring_ideal_pair_span() {
    matrix(
        "ring-ideal-pair-span",
        &["ring-ideal-pair-span", "ring-ideal-pair-commutative"],
    );
}

#[test]
fn ring_ideal_principal() {
    matrix(
        "ring-ideal-principal",
        &[
            "ring-ideal-principal-introduce",
            "ring-ideal-principal-generator",
        ],
    );
}

#[test]
fn ring_ideal_principal_pair_product() {
    matrix(
        "ring-ideal-principal-pair-product",
        &["ring-ideal-principal-pair-product"],
    );
}

#[test]
fn ring_ideal_principal_product() {
    matrix(
        "ring-ideal-principal-product",
        &["ring-ideal-principal-product"],
    );
}

#[test]
fn ring_ideal_principal_product_inclusion() {
    matrix(
        "ring-ideal-principal-product-inclusion",
        &["ring-ideal-principal-product-inclusion"],
    );
}

#[test]
fn ring_ideal_principal_product_reorder() {
    matrix(
        "ring-ideal-principal-product-reorder",
        &["ring-ideal-principal-product-reorder"],
    );
}

#[test]
fn ring_ideal_principal_universal() {
    matrix(
        "ring-ideal-principal-universal",
        &[
            "ring-ideal-principal-least",
            "ring-ideal-principal-span",
            "ring-ideal-principal-congruent",
        ],
    );
}

#[test]
fn ring_ideal_product() {
    matrix(
        "ring-ideal-product",
        &["ring-ideal-product-introduce", "ring-ideal-product-least"],
    );
}

#[test]
fn ring_ideal_product_associative() {
    matrix(
        "ring-ideal-product-associative",
        &["ring-ideal-product-associative"],
    );
}

#[test]
fn ring_ideal_product_associative_inclusion() {
    matrix(
        "ring-ideal-product-associative-inclusion",
        &["ring-ideal-product-associative-inclusion"],
    );
}

#[test]
fn ring_ideal_product_basic_laws() {
    matrix(
        "ring-ideal-product-basic-laws",
        &[
            "ring-ideal-product-commutative",
            "ring-ideal-product-left-contained",
            "ring-ideal-product-right-contained",
            "ring-ideal-product-monotone",
        ],
    );
}

#[test]
fn ring_ideal_product_distribute_first() {
    matrix(
        "ring-ideal-product-distribute-first",
        &["ring-ideal-product-distribute-first"],
    );
}

#[test]
fn ring_ideal_product_distribute_first_inclusion() {
    matrix(
        "ring-ideal-product-distribute-first-inclusion",
        &["ring-ideal-product-distribute-first-inclusion"],
    );
}

#[test]
fn ring_ideal_product_distributive() {
    matrix(
        "ring-ideal-product-distributive",
        &["ring-ideal-product-distributive"],
    );
}

#[test]
fn ring_ideal_product_sum_colon() {
    matrix(
        "ring-ideal-product-sum-colon",
        &[
            "ring-ideal-product-sum-colon-left",
            "ring-ideal-product-sum-colon-right",
        ],
    );
}

#[test]
fn ring_ideal_product_zero_unit() {
    matrix(
        "ring-ideal-product-zero-unit",
        &[
            "ring-ideal-product-top",
            "ring-ideal-product-bottom",
            "ring-ideal-containing-one",
            "ring-ideal-principal-one",
            "ring-ideal-principal-zero",
        ],
    );
}

#[test]
fn ring_ideal_span_construction() {
    matrix(
        "ring-ideal-span-construction",
        &["ring-ideal-span-generator"],
    );
}

#[test]
fn ring_ideal_span_universal() {
    matrix(
        "ring-ideal-span-universal",
        &[
            "ring-ideal-span-expression-contained",
            "ring-ideal-span-least",
            "ring-ideal-span-monotone",
            "ring-ideal-span-ideal",
        ],
    );
}

#[test]
fn ring_ideal_sum() {
    matrix("ring-ideal-sum", &["ring-ideal-sum-introduce"]);
}

#[test]
fn ring_ideal_sum_universal() {
    matrix(
        "ring-ideal-sum-universal",
        &[
            "ring-ideal-sum-left",
            "ring-ideal-sum-right",
            "ring-ideal-sum-least",
            "ring-ideal-sum-commutative",
        ],
    );
}

#[test]
fn ring_ideal_zero_unit() {
    matrix(
        "ring-ideal-zero-unit",
        &[
            "ring-ideal-bottom-least",
            "ring-ideal-top-greatest",
            "ring-ideal-top-member",
        ],
    );
}
