//! Integral-model candidate certificates; all mathematical checks use the native kernel.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::{
    collections::HashSet,
    fs,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
};

pub fn term(name: &str, args: &[&str]) -> String {
    if args.is_empty() {
        format!("(#pt-use {name} ())")
    } else {
        format!("(#pt-app (#pt-use {name} ()) {})", args.join(" "))
    }
}

pub fn fixture(statement: &str, proof: &str, valid: bool) {
    fixture_with_prelude("", statement, proof, valid)
}

pub fn fixture_with_prelude(prelude: &str, statement: &str, proof: &str, valid: bool) {
    fixture_with_prelude_and_total(prelude, statement, proof, valid, 1024 * 1024 * 1024)
}

pub fn fixture_with_prelude_and_total(
    prelude: &str,
    statement: &str,
    proof: &str,
    valid: bool,
    total: usize,
) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-integral-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{prelude} {statement} {proof}");
    let referenced: HashSet<_> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for module in [
        "../fermat_statement",
        "logic-exists",
        "logical-connectives",
        "natural-order",
        "natural-parity",
        "natural-nonzero",
        "natural-successor",
        "natural-prime",
        "natural-prime-two",
        "natural-prime-three",
        "natural-divisibility",
        "natural-divisibility-defs",
        "natural-divisibility-addition",
        "integer-defs",
        "integer-equality",
        "integer-domain",
        "integer-divisibility-decision",
        "integer-divisibility",
        "integer-gcd",
        "integer-magnitude",
        "integer-mod-four-normalization",
        "rational-defs",
        "rational-equality",
        "rational-weierstrass-defs",
        "frey-rational-curve",
        "integer-power-difference-step-cross",
        "integer-frey-a2-rearrange-cross",
        "integer-integral-identities",
        "integer-power-divisibility",
        "integer-power-differences",
        "frey-coefficient-divisibility",
        "frey-package-coefficients",
        "frey-package",
        "integer-weierstrass-defs",
        "weierstrass-model-equivalence",
        "weierstrass-invariant-congruence",
        "integer-weierstrass-map",
        "integer-weierstrass-evaluation",
        "integer-frey-model",
        "integer-frey-invariants",
        "frey-package-integral-model",
        "frey-c4-alternate-cross",
        "frey-c4-alternate",
        "integer-prime-coprimality",
        "frey-c4-prime-divisibility",
        "integer-frey-c4-primes",
        "frey-package-c4-primes",
        "integer-prime-away-two",
        "integer-frey-away-two",
        "natural-prime-order-defs",
        "natural-prime-order-existence",
        "natural-prime-order-bounds",
        "natural-prime-order-uniqueness",
        "natural-prime-order-arithmetic",
        "integer-prime-order-defs",
        "integer-prime-order-existence",
        "integer-prime-order-uniqueness",
        "integer-prime-order-arithmetic",
        "integer-prime-order-cofactors",
        "integer-prime-order-scaling",
        "frey-local-valuations",
        "frey-local-valuations-two",
        "natural-valuation-divisibility",
        "frey-valuation-divisibility",
        "integer-model-prime-defs",
        "integer-model-primes",
        "frey-semistable-model",
        "rational-variable-change-defs",
        "rational-variable-change",
        "rational-variable-change-invariants",
        "integer-integral-model-defs",
        "integer-integral-model",
        "rational-composite-powers",
        "rational-unit-cancellation",
        "rational-discriminant-cancellation",
        "rational-weierstrass-four-discriminant",
        "rational-weierstrass-c-relation",
        "rational-variable-change-b6",
        "rational-variable-change-c6",
        "rational-variable-change-discriminant",
        "rational-model-cross-invariant",
        "integer-model-cross-reflection",
        "integer-integral-model-comparison",
        "integer-integral-model-bad-primes",
        "integer-prime-order-divides",
        "frey-package-all-primes",
        "frey-package-general-model-bad-primes",
    ] {
        let module_path = root.join(format!("{module}.lim"));
        let module_source = fs::read_to_string(&module_path).unwrap();
        for line in module_source.lines() {
            for prefix in ["(#theorem ", "(#math-definition ", "(#math-inductive "] {
                if let Some(tail) = line.strip_prefix(prefix) {
                    let name = tail.split_whitespace().next().unwrap();
                    if referenced.contains(name) {
                        source.push_str(&format!(
                            "(#alias {name} = {}::{name})\n",
                            module_path.display()
                        ));
                    }
                }
            }
        }
    }
    source.push_str(prelude);
    source.push_str(&format!("(#theorem observed-integral (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let expected = format!(
        "{}::observed-integral",
        path.canonicalize().unwrap().display()
    );
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    config
        .set_proof_budget(ProofBudget::new(default.work(), default.phase_bytes(), total).unwrap());
    let result =
        check_theorem_details_from_path_with_config(&source, &path, &config, "observed-integral");
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        let report = result.unwrap_or_else(|e| panic!("{}", e.message));
        assert_eq!(report.name, expected);
        assert!(report.foundations.is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
