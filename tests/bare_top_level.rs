use lim::{CompileConfig, DiagnosticCode, Expr, TargetDescription};
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

fn scratch() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "lim-bare-roots-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    path
}

fn trees(source: &str) -> Vec<Expr> {
    lim::parse_source_unit(source)
        .unwrap()
        .into_iter()
        .map(|n| n.expr)
        .collect()
}

#[test]
fn logical_roots_share_streaming_boundaries_and_keep_authored_spans() {
    for source in [
        "#fn main { #params = {}; #returns = #u64; #body: #return 42; }",
        "#fn main () #u64\n  (#return 42u64)\n",
        "// before\r\n#type Answer #u64; #fn main () Answer (#return 42u64) // after\r\n",
        "#struct Pair () { left = #u64; right = #u64; }\n#fn main () #u64\n  (#let pair Pair (#struct-literal Pair { left = 20u64; right = 22u64; }))\n  (#return (#u64::add-wrap (#get pair left) (#get pair right)))\n",
        "#fn main {\n #params = {};\n #returns = #u64;\n #body:\n  #let value #u64 42;\n  #return value;\n}\n// boundary\n#type Number #u64\n",
    ] {
        let nodes = lim::parse_source_unit(source).unwrap();
        for node in &nodes {
            assert!(source[node.span.start..node.span.end].starts_with('#'));
            assert_eq!(node.children[0].span.start, node.span.start);
        }
        let formatted = lim::format_source(source).unwrap();
        assert_eq!(trees(source), trees(&formatted), "{formatted}");
        assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
        lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    }
}

#[test]
fn explicit_root_wrappers_reject_but_nested_and_quoted_trees_are_data() {
    for source in [
        "(#fn main () #u64 (#return 42u64))",
        "(#fn main { #params = {}; #returns = #u64; #body: #return 42; })",
        "((#fn main () #u64 (#return 42u64)))",
        ": #fn main () #u64 (#return 42u64)",
        "'(#fn main () #u64 (#return 42u64))",
    ] {
        assert!(lim::parse_source_unit(source)
            .unwrap_err()
            .contains("bare root"));
        assert!(lim::parse_program(source).is_err());
        assert!(lim::format_source(source).is_err());
    }
    // A syntax-tree API is not an alternate compilation-unit grammar.
    assert!(lim::parse("'((#fn main () #u64 (#return 42u64)))").is_ok());
    let source = "#cfg-if (#cfg-is #platform linux)\n  (#fn main () #u64 (#return 42u64))\n";
    assert!(lim::parse_source_unit(source).is_ok());
    assert!(lim::parse_source_unit(
        "#fn main { #params = {}; #returns = (); #body: #return (); } #type X #u64"
    )
    .is_err());
}

#[test]
fn source_errors_keep_delimiters_and_unicode_positions() {
    let source = "// λ\n(#fn main () #u64 (#return 42u64))";
    let dir = scratch();
    let error = lim::compile_source_to_assembly(
        source,
        &dir.join("case.lim"),
        &CompileConfig::default(),
        &dir.join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Parse);
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "(");
    assert_eq!((span.line, span.column), (2, 1));
    for source in [
        "#fn main {",
        "#type X (#tuple #u64]",
        "#fn main () #u64 (#return 42u64))",
    ] {
        assert!(lim::parse_source_unit(source).is_err(), "{source}");
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn generated_documents_use_bare_roots_with_stable_cold_warm_artifacts() {
    let dir = scratch();
    let source = "#gn emit ()\n  `((#fn answer () #u64 (#return 42u64)))\n#generate emit\n#fn main () #u64 (#return (#call answer ()))\n";
    let compile = || {
        lim::compile_source_with_generated_sources(
            source,
            &dir.join("main.lim"),
            &CompileConfig::default(),
            &dir.join("cache"),
            TargetDescription::X86_64_SYSTEM_V,
            None,
            &dir.join("generated"),
        )
    };
    let cold = compile().unwrap();
    let artifacts = fs::read_dir(dir.join("generated"))
        .unwrap()
        .map(|entry| {
            let path = entry.unwrap().path();
            let text = fs::read_to_string(&path).unwrap();
            assert!(lim::parse_source_unit(&text).is_ok(), "{text}");
            assert!(!text.lines().any(|line| line.starts_with("(#")), "{text}");
            assert!(text.contains("#generated-context"));
            (path, text)
        })
        .collect::<Vec<_>>();
    assert!(!artifacts.is_empty());
    assert_eq!(compile().unwrap(), cold);
    for (path, text) in artifacts {
        assert_eq!(fs::read_to_string(path).unwrap(), text);
    }
    fs::remove_dir_all(dir).unwrap();
}
