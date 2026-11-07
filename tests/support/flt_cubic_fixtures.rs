//! Small, isolated native proof probes used by the cubic descent regressions.
use lim::{check_theorem_details_from_path_with_config, CompileConfig};
use std::{
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
pub fn product(x: &str, y: &str) -> String {
    term("eisenstein-multiply", &[x, y])
}
pub fn power(x: &str, n: usize) -> String {
    term("eisenstein-power", &[x, &format!("(#pt-numeral {n})")])
}

pub fn fixture(statement: &str, proof: &str, valid: bool, config: &CompileConfig) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-cubic-factor-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{statement} {proof}");
    let referenced: std::collections::HashSet<&str> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for (module, names) in [
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-one",
                "eisenstein-zero",
                "eisenstein-lambda",
                "eisenstein-omega",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-multiply",
                "eisenstein-negate",
                "eisenstein-power",
                "eisenstein-divides",
            ][..],
        ),
        ("../fermat_statement", &["add", "multiply"][..]),
        (
            "eisenstein-equality",
            &[
                "eisenstein-reflexive",
                "eisenstein-symmetric",
                "eisenstein-transitive",
                "eisenstein-add-congruent",
                "eisenstein-multiply-congruent",
            ][..],
        ),
        (
            "eisenstein-ring",
            &[
                "eisenstein-multiply-one",
                "eisenstein-one-multiply",
                "eisenstein-multiply-zero",
                "eisenstein-add-zero",
                "eisenstein-add-commutative",
                "eisenstein-add-inverse",
            ][..],
        ),
        (
            "eisenstein-divisibility",
            &[
                "eisenstein-divides-zero",
                "eisenstein-divides-reflexive",
                "eisenstein-divides-congruent-target",
            ][..],
        ),
        (
            "eisenstein-additive-divisibility",
            &["eisenstein-add-after-subtract"][..],
        ),
        (
            "eisenstein-lambda-decision-core",
            &["eisenstein-lambda-not-divides-one"][..],
        ),
        ("eisenstein-lambda-order", &["eisenstein-lambda-order"][..]),
        (
            "eisenstein-cubic-shifts",
            &["eisenstein-omega-plus-one-unit"][..],
        ),
        (
            "eisenstein-cubic-rotated-orders",
            &[
                "eisenstein-cubic-omega-factor-order-one",
                "eisenstein-cubic-omega-square-factor-order-one",
            ][..],
        ),
        (
            "eisenstein-cubic-power-factors",
            &[
                "natural-three-times-as-sum",
                "eisenstein-lambda-power-cube",
                "eisenstein-cube-lambda-powered-factor",
            ][..],
        ),
        (
            "eisenstein-cubic-residual-equation",
            &["eisenstein-cubic-residual-equation"][..],
        ),
    ] {
        for name in names {
            if referenced.contains(name) {
                // one-multiply is defined in the original cubic bridge.
                let module = if *name == "eisenstein-one-multiply" {
                    "eisenstein-cubic-bridge"
                } else {
                    module
                };
                source.push_str(&format!(
                    "(#alias {name} = {}::{name})\n",
                    root.join(format!("{module}.lim")).display()
                ));
            }
        }
    }
    source.push_str(&format!("(#theorem observed-factor (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-factor");
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
