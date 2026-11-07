//! Check the small-prime split without admitting the remaining large-prime case.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::{
    fs,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
};

const TARGETS: &[&str] = &[
    "fermat-for-odd-prime-from-large-primes",
    "fermat-statement-from-primes-at-least-five",
];

fn config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}
fn term(name: &str, args: &[&str]) -> String {
    if args.is_empty() {
        format!("(#pt-use {name} ())")
    } else {
        format!("(#pt-app (#pt-use {name} ()) {})", args.join(" "))
    }
}

#[test]
fn small_prime_reduction_declarations_have_no_global_foundations() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt/large-prime-reduction.lim");
    let source = fs::read_to_string(&path).unwrap();
    for &target in TARGETS {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config(), target)
            .unwrap_or_else(|error| panic!("{target}: {}", error.message));
        assert!(report.name == target || report.name.ends_with(&format!("::{target}")));
        assert!(
            report.foundations.is_empty(),
            "{target}: {:?}",
            report.foundations
        );
    }
}

fn fixture(parameters: &str, statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-large-prime-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{parameters} {statement} {proof}");
    let referenced: std::collections::HashSet<&str> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for (module, names) in [
        (
            "large-prime-reduction",
            &[
                "large-prime-fermat-cases",
                "fermat-for-odd-prime-from-large-primes",
                "fermat-statement-from-primes-at-least-five",
            ][..],
        ),
        (
            "../fermat_statement",
            &["fermats-last-theorem-statement", "multiply"][..],
        ),
        ("fermat-for", &["fermat-for"][..]),
        ("fermat-three", &["fermat-for-three"][..]),
        ("natural-prime-three", &["prime-three"][..]),
        ("logic-exists", &["exists"][..]),
    ] {
        for name in names {
            if referenced.contains(name) {
                source.push_str(&format!(
                    "(#alias {name} = {}::{name})\n",
                    root.join(format!("{module}.lim")).display()
                ));
            }
        }
    }
    source.push_str(&format!("(#theorem observed-small-prime (#universes) (#parameters {parameters}) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config(),
        "observed-small-prime",
    );
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}

#[test]
fn the_small_prime_branch_accepts_the_actual_prime_three_certificate() {
    let half_predicate = format!(
        "(#pt-lambda ((candidate-half #pt-nat)) (#pt-eq #pt-nat (#pt-numeral 3) (#pt-succ {})))",
        term("multiply", &["(#pt-numeral 2)", "candidate-half"])
    );
    let odd_three = format!("(#pt-construct exists (0) (#pt-nat {half_predicate}) introduce ((#pt-numeral 1) (#pt-refl #pt-nat (#pt-numeral 3))))");
    let proof = term(
        "fermat-for-odd-prime-from-large-primes",
        &[
            "(#pt-numeral 3)",
            &term("prime-three", &[]),
            &odd_three,
            "large-prime-cases",
        ],
    );
    fixture(
        "(#parameter large-prime-cases (#pt-use large-prime-fermat-cases ()))",
        &term("fermat-for", &["(#pt-numeral 3)"]),
        &proof,
        true,
    );
}

#[test]
fn the_final_reduction_cannot_omit_its_large_prime_evidence() {
    fixture(
        "",
        &term("fermats-last-theorem-statement", &[]),
        &term("fermat-statement-from-primes-at-least-five", &[]),
        false,
    );
}

#[test]
fn one_closed_exponent_cannot_supply_every_large_prime_case() {
    let proof = term(
        "fermat-statement-from-primes-at-least-five",
        &[&term("fermat-for-three", &[])],
    );
    fixture(
        "",
        &term("fermats-last-theorem-statement", &[]),
        &proof,
        false,
    );
}
