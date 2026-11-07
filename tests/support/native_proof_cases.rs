//! Native proof fixtures with exact global-reference imports and bounded checking.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicUsize, Ordering},
        OnceLock,
    },
};

fn catalog() -> &'static BTreeMap<String, Vec<PathBuf>> {
    static CATALOG: OnceLock<BTreeMap<String, Vec<PathBuf>>> = OnceLock::new();
    CATALOG.get_or_init(|| {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
        let mut files = fs::read_dir(&root)
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|e| e == "lim"))
            .collect::<Vec<_>>();
        files.push(root.join("../fermat_statement.lim"));
        files.sort();
        let mut result: BTreeMap<String, Vec<PathBuf>> = BTreeMap::new();
        for path in files {
            for line in fs::read_to_string(&path).unwrap().lines() {
                for prefix in ["(#theorem ", "(#math-definition ", "(#math-inductive "] {
                    if let Some(tail) = line.strip_prefix(prefix) {
                        let name = tail.split_whitespace().next().unwrap();
                        result
                            .entry(name.to_owned())
                            .or_default()
                            .push(path.clone());
                    }
                }
            }
        }
        result
    })
}

pub fn check(prelude: &str, statement: &str, proof: &str, good: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-opposite-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&dir).unwrap();
    let path = dir.join("fixture.lim");
    let terms = format!("{prelude} {statement} {proof}");
    let tokens = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();
    let mut references = BTreeSet::new();
    let mut declared = BTreeSet::new();
    for pair in tokens.windows(2) {
        if matches!(
            pair[0],
            "#pt-use" | "#pt-construct" | "#pt-project" | "#pt-induct"
        ) {
            references.insert(pair[1]);
        }
        if matches!(pair[0], "#theorem" | "#math-definition" | "#math-inductive") {
            declared.insert(pair[1]);
        }
    }
    let mut source = String::new();
    for name in &references {
        if declared.contains(name) {
            continue;
        }
        let owners = catalog()
            .get(*name)
            .unwrap_or_else(|| panic!("fixture references undeclared native symbol {name}"));
        assert_eq!(owners.len(), 1, "ambiguous native fixture symbol {name}");
        source.push_str(&format!(
            "(#alias {name} = {}::{name})\n",
            owners[0].display()
        ));
    }
    source.push_str(prelude);
    source.push_str(&format!("(#theorem observed-point-product (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let budget = ProofBudget::default();
    let total = if references.contains("rational") {
        2 * 1024 * 1024 * 1024
    } else {
        1024 * 1024 * 1024
    };
    config.set_proof_budget(ProofBudget::new(budget.work(), budget.phase_bytes(), total).unwrap());
    let expected = format!(
        "{}::observed-point-product",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-point-product",
    );
    fs::remove_dir_all(dir).unwrap();
    if good {
        let report = result.unwrap_or_else(|e| {
            panic!(
                "{}: {}",
                statement.chars().take(260).collect::<String>(),
                e.message
            )
        });
        assert_eq!(report.name, expected);
        assert!(report.foundations.is_empty());
    } else {
        let e = result.expect_err("invalid mathematical evidence unexpectedly checked");
        assert_eq!(e.code, DiagnosticCode::Proof);
        assert!(
            e.message.contains("mismatch"),
            "{}: {}",
            statement.chars().take(260).collect::<String>(),
            e.message
        );
    }
}
