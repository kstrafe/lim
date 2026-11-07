//! Candidate certificates for discriminant tests; the native kernel decides validity.
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
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-discriminant-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{statement} {proof}");
    let referenced: HashSet<_> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    // Read declaration names only, then alias just those explicitly referenced
    // by this fixture. This does not supply any mathematical evidence.
    for module in [
        "../fermat_statement",
        "natural-nonzero",
        "integer-defs",
        "integer-domain",
        "integer-equality",
        "integer-divisibility-decision",
        "logical-connectives",
        "logic-exists",
        "rational-defs",
        "rational-equality",
        "rational-ring",
        "rational-weierstrass-defs",
        "frey-rational-curve",
        "rational-sign-laws",
        "rational-power-laws",
        "rational-discriminant-algebra",
        "weierstrass-zero-b6",
        "frey-discriminant-factor",
        "frey-discriminant-square-cross",
        "frey-discriminant-square-integer",
        "frey-discriminant-square",
        "rational-fraction-products",
        "integer-power-sums",
        "frey-discriminant-fraction",
        "frey-discriminant",
        "frey-package-discriminant",
        "rational-units",
        "frey-elliptic",
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
    source.push_str(&format!("(#theorem observed-discriminant (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let expected_name = format!(
        "{}::observed-discriminant",
        path.canonicalize().unwrap().display()
    );
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-discriminant",
    );
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        let report = result.unwrap_or_else(|e| panic!("{}", e.message));
        assert_eq!(report.name, expected_name);
        assert!(report.foundations.is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
