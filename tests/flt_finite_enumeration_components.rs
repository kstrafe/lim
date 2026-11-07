//! Audit every native finite enumeration, cardinality and signed trace theorem.
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
fn finite_affine_point_identities() {
    matrix(
        "finite-affine-point-identities",
        &[
            "finite-affine-coordinate-injective",
            "finite-affine-infinity-not-coordinate",
        ],
    );
}

#[test]
fn finite_affine_selected_map() {
    matrix(
        "finite-affine-selected-map",
        &[
            "finite-affine-point-of-selected-injective",
            "finite-affine-point-of-selected-not-infinity",
        ],
    );
}

#[test]
fn finite_coordinate_space() {
    matrix(
        "finite-coordinate-space",
        &[
            "finite-coordinate-space-covers",
            "finite-coordinate-space-no-duplicates",
        ],
    );
}

#[test]
fn finite_enumeration_cardinality() {
    matrix(
        "finite-enumeration-cardinality",
        &["finite-enumeration-size-independent"],
    );
}

#[test]
fn finite_enumeration_defs() {
    matrix(
        "finite-enumeration-defs",
        &[
            "finite-enumeration-covers",
            "finite-enumeration-no-duplicates",
        ],
    );
}

#[test]
fn finite_list_append_distinct() {
    matrix(
        "finite-list-append-distinct",
        &["finite-list-append-no-duplicates"],
    );
}

#[test]
fn finite_list_append_membership() {
    matrix(
        "finite-list-append-membership",
        &[
            "finite-list-append-member-left",
            "finite-list-append-member-right",
            "finite-list-append-member-cases",
        ],
    );
}

#[test]
fn finite_list_cardinality() {
    matrix(
        "finite-list-cardinality",
        &["finite-list-cardinality-equal"],
    );
}

#[test]
fn finite_list_defs() {
    matrix(
        "finite-list-defs",
        &[
            "finite-list-member-head",
            "finite-list-member-tail",
            "finite-list-nil-no-duplicates",
            "finite-list-cons-no-duplicates",
        ],
    );
}

#[test]
fn finite_list_erasure_defs() {
    matrix(
        "finite-list-erasure-defs",
        &["finite-list-member-has-erasure"],
    );
}

#[test]
fn finite_list_erasure_distinct() {
    matrix(
        "finite-list-erasure-distinct",
        &[
            "finite-list-erasure-no-duplicates",
            "finite-list-erasure-excludes-value",
        ],
    );
}

#[test]
fn finite_list_erasure_membership() {
    matrix(
        "finite-list-erasure-membership",
        &[
            "finite-list-erasure-included",
            "finite-list-erasure-keeps-other-members",
        ],
    );
}

#[test]
fn finite_list_erasure_size() {
    matrix(
        "finite-list-erasure-size",
        &["finite-list-erasure-length", "finite-list-erasure-member"],
    );
}

#[test]
fn finite_list_inclusion() {
    matrix(
        "finite-list-inclusion",
        &["finite-list-included-nil-length"],
    );
}

#[test]
fn finite_list_map_laws() {
    matrix(
        "finite-list-map-laws",
        &[
            "finite-list-map-no-duplicates",
            "finite-list-map-length",
            "finite-list-append-length",
        ],
    );
}

#[test]
fn finite_list_membership() {
    matrix(
        "finite-list-membership",
        &[
            "finite-list-member-congruent",
            "finite-list-map-member",
            "finite-list-map-preimage",
        ],
    );
}

#[test]
fn finite_list_product_distinct() {
    matrix(
        "finite-list-product-distinct",
        &["finite-list-product-no-duplicates"],
    );
}

#[test]
fn finite_list_product() {
    matrix(
        "finite-list-product",
        &["finite-list-product-member", "finite-list-product-preimage"],
    );
}

#[test]
fn finite_list_select_laws() {
    matrix(
        "finite-list-select-laws",
        &[
            "finite-list-select-cover",
            "finite-list-select-no-duplicates",
        ],
    );
}

#[test]
fn finite_list_select() {
    matrix("finite-list-select", &["finite-list-select-preimage"]);
}

#[test]
fn finite_list_tabulate_distinct() {
    matrix(
        "finite-list-tabulate-distinct",
        &["finite-list-tabulate-no-duplicates"],
    );
}

#[test]
fn finite_list_tabulate() {
    matrix(
        "finite-list-tabulate",
        &[
            "finite-list-tabulate-member",
            "finite-list-tabulate-index",
            "finite-list-tabulate-length",
        ],
    );
}

#[test]
fn finite_pair_defs() {
    matrix(
        "finite-pair-defs",
        &[
            "finite-pair-extensional",
            "finite-pair-first-congruent",
            "finite-pair-second-congruent",
        ],
    );
}

#[test]
fn finite_prime_ap() {
    matrix(
        "finite-prime-ap",
        &[
            "finite-prime-positive",
            "finite-prime-ap-of-model-congruent",
        ],
    );
}

#[test]
fn finite_residue_enumeration() {
    matrix(
        "finite-residue-enumeration",
        &["finite-residue-enumeration-size"],
    );
}

#[test]
fn finite_residue_values() {
    matrix(
        "finite-residue-values",
        &[
            "finite-residue-values-cover",
            "finite-residue-values-no-duplicates",
            "finite-residue-values-length",
        ],
    );
}

#[test]
fn finite_subtype_defs() {
    matrix(
        "finite-subtype-defs",
        &[
            "finite-subtype-extensional",
            "finite-subtype-value-congruent",
        ],
    );
}

#[test]
fn finite_weierstrass_ap() {
    matrix(
        "finite-weierstrass-ap",
        &["finite-weierstrass-ap-of-model-congruent"],
    );
}

#[test]
fn finite_weierstrass_cardinality() {
    matrix(
        "finite-weierstrass-cardinality",
        &[
            "finite-weierstrass-card-enumeration-independent",
            "finite-weierstrass-card-congruent",
        ],
    );
}

#[test]
fn finite_weierstrass_extensional() {
    matrix(
        "finite-weierstrass-extensional",
        &["finite-weierstrass-extensional"],
    );
}

#[test]
fn finite_weierstrass_point_enumeration() {
    matrix(
        "finite-weierstrass-point-enumeration",
        &["finite-weierstrass-point-enumeration-size-is-length"],
    );
}

#[test]
fn finite_weierstrass_point_values() {
    matrix(
        "finite-weierstrass-point-values",
        &[
            "finite-weierstrass-point-values-cover",
            "finite-weierstrass-point-values-no-duplicates",
        ],
    );
}

#[test]
fn finite_weierstrass_satisfying_coordinates() {
    matrix(
        "finite-weierstrass-satisfying-coordinates",
        &[
            "finite-weierstrass-satisfying-coordinates-cover",
            "finite-weierstrass-satisfying-coordinates-no-duplicates",
        ],
    );
}

#[test]
fn finite_weierstrass_trace() {
    matrix(
        "finite-weierstrass-trace",
        &[
            "finite-weierstrass-trace-enumeration-independent",
            "finite-weierstrass-trace-congruent",
        ],
    );
}

#[test]
fn natural_prefix_bounds() {
    matrix(
        "natural-prefix-bounds",
        &[
            "natural-prefix-successor-cases",
            "natural-prefix-weaken-successor",
        ],
    );
}
