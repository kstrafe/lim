//! Inventory every native point-evaluation and quotient theorem.
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
    let directory = std::env::temp_dir().join(format!(
        "lim-point-evaluation-matrix-{}-{module}",
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
fn point_evaluation_composition() {
    matrix(
        "point-evaluation-composition",
        &["point-evaluation-compose-mapping"],
    );
}

#[test]
fn point_evaluation_constant_linear_product() {
    matrix(
        "point-evaluation-constant-linear-product",
        &["point-evaluation-constant-linear-product"],
    );
}

#[test]
fn point_evaluation_coordinate_constant_contained() {
    matrix(
        "point-evaluation-coordinate-constant-contained",
        &["point-evaluation-coordinate-constant-contained"],
    );
}

#[test]
fn point_evaluation_coordinate_constant_root() {
    matrix(
        "point-evaluation-coordinate-constant-root",
        &["point-evaluation-coordinate-constant-root"],
    );
}

#[test]
fn point_evaluation_coordinate_formula() {
    matrix(
        "point-evaluation-coordinate-formula",
        &["point-evaluation-coordinate-formula"],
    );
}

#[test]
fn point_evaluation_coordinate_generators() {
    matrix(
        "point-evaluation-coordinate-generators",
        &[
            "point-evaluation-coordinate-X-zero",
            "point-evaluation-coordinate-Y-zero",
        ],
    );
}

#[test]
fn point_evaluation_coordinate_ideal_contained() {
    matrix(
        "point-evaluation-coordinate-ideal-contained",
        &["point-evaluation-coordinate-ideal-contained"],
    );
}

#[test]
fn point_evaluation_coordinate_kernel_contained() {
    matrix(
        "point-evaluation-coordinate-kernel-contained",
        &["point-evaluation-coordinate-kernel-contained"],
    );
}

#[test]
fn point_evaluation_coordinate_kernel_is_point_ideal() {
    matrix(
        "point-evaluation-coordinate-kernel-is-point-ideal",
        &["point-evaluation-coordinate-kernel-is-point-ideal"],
    );
}

#[test]
fn point_evaluation_coordinate_morphism() {
    matrix(
        "point-evaluation-coordinate-morphism",
        &["point-evaluation-coordinate-mapping"],
    );
}

#[test]
fn point_evaluation_coordinate_quotient_isomorphism() {
    matrix(
        "point-evaluation-coordinate-quotient-isomorphism",
        &[
            "point-evaluation-coordinate-quotient-right-inverse",
            "point-evaluation-coordinate-quotient-left-inverse",
        ],
    );
}

#[test]
fn point_evaluation_coordinate_quotient_relation() {
    matrix(
        "point-evaluation-coordinate-quotient-relation",
        &["point-evaluation-coordinate-quotient-relation"],
    );
}

#[test]
fn point_evaluation_coordinate_section() {
    matrix(
        "point-evaluation-coordinate-section",
        &["point-evaluation-coordinate-section-inverse"],
    );
}

#[test]
fn point_evaluation_coordinate_source_equation() {
    matrix(
        "point-evaluation-coordinate-source-equation",
        &["point-evaluation-coordinate-source-equation"],
    );
}

#[test]
fn point_evaluation_embedded_multiple() {
    matrix(
        "point-evaluation-embedded-multiple",
        &["point-evaluation-embedded-multiple"],
    );
}

#[test]
fn point_evaluation_image_map_laws() {
    matrix(
        "point-evaluation-image-map-laws",
        &[
            "point-evaluation-image-map-congruent",
            "point-evaluation-image-map-zero",
            "point-evaluation-image-map-one",
            "point-evaluation-image-map-add",
            "point-evaluation-image-map-multiply",
        ],
    );
}

#[test]
fn point_evaluation_image_morphism() {
    matrix(
        "point-evaluation-image-morphism",
        &["point-evaluation-image-mapping"],
    );
}

#[test]
fn point_evaluation_image_ring() {
    matrix(
        "point-evaluation-image-ring",
        &["point-evaluation-image-relation"],
    );
}

#[test]
fn point_evaluation_kernel() {
    matrix(
        "point-evaluation-kernel",
        &[
            "point-evaluation-kernel-introduce",
            "point-evaluation-kernel-eliminate",
        ],
    );
}

#[test]
fn point_evaluation_kernel_difference() {
    matrix(
        "point-evaluation-kernel-difference",
        &[
            "point-evaluation-kernel-difference-equal",
            "point-evaluation-equal-kernel-difference",
        ],
    );
}

#[test]
fn point_evaluation_linear_decomposition() {
    matrix(
        "point-evaluation-linear-decomposition",
        &["point-evaluation-linear-decomposition"],
    );
}

#[test]
fn point_evaluation_map_negate() {
    matrix(
        "point-evaluation-map-negate",
        &["point-evaluation-map-negate"],
    );
}

#[test]
fn point_evaluation_naturality() {
    matrix(
        "point-evaluation-naturality",
        &["point-evaluation-naturality"],
    );
}

#[test]
fn point_evaluation_quadratic_formula() {
    matrix(
        "point-evaluation-quadratic-formula",
        &["point-evaluation-quadratic-formula"],
    );
}

#[test]
fn point_evaluation_quadratic_morphism() {
    matrix(
        "point-evaluation-quadratic-morphism",
        &["point-evaluation-quadratic-mapping"],
    );
}

#[test]
fn point_evaluation_quotient_congruence() {
    matrix(
        "point-evaluation-quotient-congruence",
        &["point-evaluation-quotient-congruent"],
    );
}

#[test]
fn point_evaluation_quotient_divides_zero() {
    matrix(
        "point-evaluation-quotient-divides-zero",
        &["point-evaluation-quotient-divides-zero"],
    );
}

#[test]
fn point_evaluation_quotient_morphism() {
    matrix(
        "point-evaluation-quotient-morphism",
        &["point-evaluation-quotient-mapping"],
    );
}

#[test]
fn point_evaluation_section_laws() {
    matrix(
        "point-evaluation-section-laws",
        &[
            "point-evaluation-section-congruent",
            "point-evaluation-section-zero",
            "point-evaluation-section-one",
            "point-evaluation-section-add",
            "point-evaluation-section-multiply",
        ],
    );
}

#[test]
fn point_evaluation_section_morphism() {
    matrix(
        "point-evaluation-section-morphism",
        &[
            "point-evaluation-section-right-inverse",
            "point-evaluation-section-left-inverse",
        ],
    );
}

#[test]
fn polynomial_root_division_data() {
    matrix(
        "polynomial-root-division-data",
        &["polynomial-root-divisor-linear-coefficient"],
    );
}

#[test]
fn polynomial_root_division_equation() {
    matrix(
        "polynomial-root-division-equation",
        &["polynomial-root-division-equation"],
    );
}

#[test]
fn polynomial_root_division_evaluation() {
    matrix(
        "polynomial-root-division-evaluation",
        &["polynomial-root-division-evaluation"],
    );
}

#[test]
fn polynomial_root_evaluation_bridge() {
    matrix(
        "polynomial-root-evaluation-bridge",
        &["polynomial-root-evaluation-bridge"],
    );
}

#[test]
fn polynomial_root_evaluation_generators() {
    matrix(
        "polynomial-root-evaluation-generators",
        &[
            "polynomial-root-evaluate-constant",
            "polynomial-root-evaluate-shift",
            "polynomial-root-evaluate-divisor",
        ],
    );
}

#[test]
fn polynomial_root_evaluation_laws() {
    matrix(
        "polynomial-root-evaluation-laws",
        &[
            "polynomial-root-evaluate-congruent",
            "polynomial-root-evaluate-add",
            "polynomial-root-evaluate-multiply",
        ],
    );
}

#[test]
fn polynomial_root_evaluation_morphism() {
    matrix(
        "polynomial-root-evaluation-morphism",
        &["polynomial-root-evaluation-mapping"],
    );
}

#[test]
fn polynomial_root_evaluation_negation() {
    matrix(
        "polynomial-root-evaluation-negation",
        &["polynomial-root-evaluate-negate"],
    );
}

#[test]
fn polynomial_root_factor() {
    matrix("polynomial-root-factor", &["polynomial-root-factor"]);
}

#[test]
fn polynomial_root_identity_morphism() {
    matrix(
        "polynomial-root-identity-morphism",
        &["polynomial-root-identity-mapping"],
    );
}

#[test]
fn polynomial_root_kernel_is_principal() {
    matrix(
        "polynomial-root-kernel-is-principal",
        &["polynomial-root-kernel-is-principal"],
    );
}

#[test]
fn polynomial_root_local_equation() {
    matrix(
        "polynomial-root-local-equation",
        &["polynomial-root-local-equation"],
    );
}

#[test]
fn polynomial_root_principal_member() {
    matrix(
        "polynomial-root-principal-member",
        &["polynomial-root-principal-member"],
    );
}

#[test]
fn polynomial_root_remainder_evaluation() {
    matrix(
        "polynomial-root-remainder-evaluation",
        &["polynomial-root-remainder-evaluation"],
    );
}

#[test]
fn polynomial_root_step_equation() {
    matrix(
        "polynomial-root-step-equation",
        &["polynomial-root-step-equation"],
    );
}

#[test]
fn polynomial_root_vanishes_if_principal() {
    matrix(
        "polynomial-root-vanishes-if-principal",
        &["polynomial-root-vanishes-if-principal"],
    );
}
