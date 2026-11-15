mod support;

use lim::{CompileConfig, Expr};
use std::fs;

fn trees(source: &str) -> Vec<Expr> {
    lim::parse_source_unit(source)
        .unwrap()
        .into_iter()
        .map(|node| node.expr)
        .collect()
}

#[test]
fn function_records_keep_the_existing_internal_signatures() {
    for (source, canonical) in [
        (
            "#fn answer { #params = {}; #returns = #u64; #body: #return 42; }",
            "(#fn answer () #u64 (#return 42))",
        ),
        (
            "#unsafe-fn identity { #params = { value = #u64; }; #returns = #u64; #body: #return value; }",
            "(#unsafe-fn identity ((value #u64)) #u64 (#return value))",
        ),
        (
            "#extern-fn foreign { #abi = #abi-c; #params = { value = #u64; }; #returns = (); }",
            "(#extern-fn #abi-c foreign ((value #u64)) ())",
        ),
    ] {
        let expected = lim::parse(canonical).unwrap().remove(0).expr;
        assert_eq!(trees(source), vec![expected]);
        let formatted = lim::format_source(source).unwrap();
        assert_eq!(trees(&formatted), trees(source));
        assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
    }
}

#[test]
fn source_rejects_positional_and_section_signatures_without_banning_raw_trees() {
    for declaration in [
        "#fn answer () #u64 (#return 42u64)",
        "#unsafe-fn answer () #u64 (#return 42u64)",
        "#extern-fn #abi-c foreign ((value #u64)) ()",
        "#fn answer (#params {}) (#returns #u64) (#body (#return 42u64))",
    ] {
        assert!(lim::parse_source_unit(declaration)
            .unwrap_err()
            .contains("require a named record"));
        assert!(lim::format_source(declaration).is_err());
        assert!(lim::parse(&format!("({declaration})")).is_ok());
        assert!(lim::parse(&format!("'({declaration})")).is_ok());
    }
    assert!(lim::parse_source_unit("#gn data () '(#fn literal () #u64 (#return 42u64))").is_ok());
}

#[test]
fn cfg_declaration_branches_are_checked_even_when_inactive_but_templates_are_data() {
    let modern = "#fn answer { #params = {}; #returns = #u64; #body: #return 42; }";
    for source in [
        format!("#cfg-if (#cfg-is #feature enabled) ({modern})"),
        format!("#cfg-if (#cfg-is #feature enabled) (#type Word #u64) (#cfg-else ({modern}))"),
        "#cfg-if (#cfg-is #feature enabled) (#gn data () '(#fn literal () #u64 (#return 42u64)))"
            .into(),
    ] {
        assert!(lim::parse_source_unit(&source).is_ok(), "{source}");
    }
    for source in [
        "#cfg-if (#cfg-is #feature disabled) (#fn old () #u64 (#return 42u64))",
        "#cfg-if (#cfg-is #feature enabled) (#type Word #u64) (#cfg-else (#unsafe-fn old () #u64 (#return 42u64)))",
        "#cfg-if (#cfg-is #feature enabled) (#cfg-if (#cfg-is #mode fast) (#extern-fn #abi-c old () ()))",
    ] {
        assert!(lim::parse_source_unit(source)
            .unwrap_err()
            .contains("require a named record"));
    }
}

#[test]
fn extern_records_require_the_abi_and_retain_the_unsafe_boundary() {
    for fields in [
        "#params = {}; #returns = ();",
        "#abi = #abi-other; #params = {}; #returns = ();",
        "#abi = #abi-c; #params = {}; #returns = (); #body: #return ();",
        "#abi = #abi-c; #abi = #abi-c; #params = {}; #returns = ();",
    ] {
        assert!(lim::parse_source_unit(&format!("#extern-fn foreign {{ {fields} }}")).is_err());
    }
    let binding =
        "#extern-fn foreign { #abi = #abi-c; #params = { value = #u64; }; #returns = (); }";
    let safe = format!("{binding}\n#fn main {{ #params = {{}}; #returns = (); #body = (foreign {{ value = 1; }}; #return ();); }}");
    let error = lim::parse_program(&safe)
        .and_then(|program| lim::check_types(&program))
        .unwrap_err();
    assert!(error.contains("unsafe"), "{error}");
    let unsafe_call = format!("{binding}\n#fn main {{ #params = {{}}; #returns = (); #body = (#unsafe : #unsafe-call foreign {{ value = 1; }}; #return ();); }}");
    lim::check_types(&lim::parse_program(&unsafe_call).unwrap()).unwrap();
}

#[test]
fn generated_canonical_function_data_publishes_modern_source_with_contracts() {
    let scratch = support::Scratch::new("record-function-artifacts");
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    let output = scratch.path().join("generated");
    let source = "#gn emit () `((#fn answer ((n #u64)) #u64 (#requires (#u64::lt n 100u64)) (#requires (#u64::gt n 0u64)) (#return n)) (#unsafe-fn alter ((#mut value #u64)) #u64 (#set value 42u64) (#return value)) (#extern-fn #abi-c foreign ((value #u64)) ()) (#cfg-if (#cfg-is #feature records) (#fn selected () #u64 (#return 42u64))))\n#generate emit\n#fn main { #params = {}; #returns = #u64; #body: #return 42; }";
    let mut config = CompileConfig::default();
    config.set("feature", "records");
    for _ in 0..2 {
        let program =
            lim::parse_program_from_path_with_config_and_cache(source, &path, &config, &cache)
                .unwrap();
        lim::check_types(&program).unwrap();
        assert!(program.items.iter().any(|item| matches!(item,
            lim::Item::Function(function) if function.name.ends_with("alter") && function.parameters[0].mutable)));
        assert!(program.items.iter().any(|item| matches!(item,
            lim::Item::Function(function) if function.name.ends_with("selected"))));
        lim::write_generated_sources_from_path_with_config_and_cache(
            source, &path, &output, &config, &cache,
        )
        .unwrap();
    }
    let artifacts = fs::read_dir(output)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .collect::<Vec<_>>();
    let artifact = artifacts
        .iter()
        .find(|source| source.contains("#fn answer {"))
        .unwrap();
    assert!(artifact.contains("#params = { n = #u64; };"));
    assert_eq!(artifact.matches("#requires =").count(), 1);
    assert!(artifact.contains("#body:"));
    assert!(artifacts
        .iter()
        .any(|source| source.contains("#unsafe-fn alter {")));
    assert!(artifacts
        .iter()
        .any(|source| source.contains("#extern-fn foreign {")));
    let nodes = trees(artifact);
    assert!(nodes.iter().any(|node| matches!(node, Expr::List(parts)
        if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "#fn"))));
}
