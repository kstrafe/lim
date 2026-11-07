//! Inventory and check every native finite-residue theorem, including helpers.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

fn matrix(module: &str, helpers: usize, names: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let declared: Vec<_> = source
        .lines()
        .filter_map(|line| line.strip_prefix("(#theorem ")?.split_whitespace().next())
        .collect();
    let mut expected: Vec<_> = (0..helpers)
        .map(|n| format!("residue-step-{n:03}"))
        .collect();
    expected.extend(names.iter().map(|s| (*s).to_owned()));
    assert_eq!(
        declared, expected,
        "every native theorem must be inventoried"
    );
    let target = expected.last().unwrap();
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
        .unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty());
}
macro_rules! matrix {
    ($test:ident, $module:literal, $helpers:literal, [$($name:literal),+ $(,)?]) => {
        #[test] fn $test() { matrix($module, $helpers, &[$($name),+]); }
    };
}
matrix!(
    natural_division_data,
    "natural-division-data",
    0,
    ["compute-natural-division-correct"]
);
matrix!(
    finite_residue_defs,
    "finite-residue-defs",
    0,
    [
        "finite-residue-value-in-range",
        "finite-reduction-certificate",
        "finite-reduction-from-division",
        "finite-reduction-small",
        "finite-reduction-multiple",
        "finite-reduction-period",
    ]
);
matrix!(
    finite_residue_operations,
    "finite-residue-operations",
    0,
    [
        "finite-residue-add-in-range",
        "finite-residue-add-certificate",
        "finite-residue-multiply-in-range",
        "finite-residue-multiply-certificate",
    ]
);
matrix!(
    finite_residue_congruence,
    "finite-residue-congruence",
    0,
    [
        "finite-reduction-congruent",
        "finite-reduction-period-multiple",
        "finite-reduction-equation",
        "finite-reduction-idempotent",
    ]
);
matrix!(
    finite_residue_polynomials,
    "finite-residue-polynomials",
    9,
    [
        "finite-division-sum-polynomial",
        "finite-division-product-polynomial",
    ]
);
matrix!(
    finite_residue_arithmetic_laws,
    "finite-residue-arithmetic-laws",
    0,
    ["finite-reduction-sum", "finite-reduction-product"]
);
matrix!(
    finite_residue_nested_reduction,
    "finite-residue-nested-reduction",
    0,
    [
        "finite-reduction-sum-left",
        "finite-reduction-sum-right",
        "finite-reduction-product-left",
        "finite-reduction-product-right",
    ]
);
matrix!(
    finite_residue_semiring,
    "finite-residue-semiring",
    0,
    [
        "finite-residue-add-associative",
        "finite-residue-add-commutative",
        "finite-residue-add-identity",
        "finite-residue-multiply-associative",
        "finite-residue-multiply-commutative",
        "finite-residue-multiply-identity",
        "finite-residue-distributive",
    ]
);
matrix!(
    finite_residue_negation,
    "finite-residue-negation",
    0,
    [
        "finite-positive-modulus-successor",
        "finite-residue-add-inverse",
        "finite-residue-negate-in-range",
    ]
);
