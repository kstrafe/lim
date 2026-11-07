//! Isolated native proof probes for signed coordinate division.
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

pub fn fixture(statement: &str, proof: &str, valid: bool, config: &CompileConfig) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-division-{}-{}",
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
            "integer-defs",
            &[
                "integer",
                "integer-of-natural",
                "integer-negative-natural",
                "integer-equal",
                "integer-add",
                "integer-multiply",
            ][..],
        ),
        ("eisenstein-defs", &["eisenstein"][..]),
        ("eisenstein-norm-defs", &["eisenstein-natural-norm"][..]),
        (
            "eisenstein-coordinate-norm-bound",
            &["eisenstein-natural-coordinate-norm-bound"][..],
        ),
        (
            "natural-rectangle-norm-bound",
            &["natural-rectangle-square-budget-bound"][..],
        ),
        (
            "integer-division-defs",
            &[
                "integer-division-spec",
                "integer-has-division",
                "integer-division-congruent-dividend",
                "integer-natural-division-equation",
                "integer-negative-exact-division-equation",
                "integer-negative-complement-division-equation",
            ][..],
        ),
        (
            "integer-division-existence",
            &["integer-division-exists"][..],
        ),
        (
            "eisenstein-coordinate-division",
            &[
                "eisenstein-coordinate-division-spec",
                "eisenstein-coordinate-division-exists",
                "eisenstein-coordinate-division-from-components",
            ][..],
        ),
        ("../fermat_statement", &["add"][..]),
        ("natural-order", &["less-than"][..]),
        ("logical-connectives", &["conjunction-introduce"][..]),
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
    source.push_str(&format!("(#theorem observed-division (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-division");
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        // A resource limit is not evidence that an invalid proof was rejected.
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
