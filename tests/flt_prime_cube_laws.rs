//! Foundation-free checks for the Eisenstein prime cube laws.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const PRIME_CUBE_LAWS: &[&str] = &[
    "eisenstein-prime-nonzero",
    "eisenstein-prime-nonunit",
    "eisenstein-prime-divides-product",
    "eisenstein-prime-divides-power",
    "eisenstein-coprime-divisor-left",
    "eisenstein-prime-divisor-excludes-coprime-factor",
    "eisenstein-prime-divides-unit-cube-root",
];

fn prime_cube_laws_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

#[test]
fn eisenstein_prime_cube_laws_are_foundation_free() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("theorems/flt/eisenstein-prime-cube-laws.lim");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let config = prime_cube_laws_config();

    for &target in PRIME_CUBE_LAWS {
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
