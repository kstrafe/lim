mod support;

fn expand(expression: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("generator-syntax-values");
    let source = format!(
        "(#gn alias (options) `((#type ,{expression} u64)))
         (@alias (: name Word : suffix \"-alias\"))
         (#fn main () u64 (#return 42u64))"
    );
    lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn named_syntax_lookup_and_identifier_composition_are_literal_operations() {
    for expression in [
        "(#gn-get options name)",
        "(#gn-get options absent Fallback)",
        "(#gn-get options name (#gn-error \"unused fallback must not run\"))",
        "(#gn-symbol-append (#gn-get options name) (#gn-get options suffix))",
        "(#gn-symbol-append Word -alias)",
    ] {
        expand(expression).unwrap();
    }
}

#[test]
fn syntax_lookup_and_symbol_composition_fail_with_invocation_spans() {
    for (expression, expected) in [
        ("(#gn-get options absent)", "missing key"),
        ("(#gn-get (: name Word : name Other) name)", "repeats key"),
        ("(#gn-get ((name Word) (malformed)) name)", "pairs"),
        ("(#gn-get (name Word) name)", "pairs"),
        ("(#gn-get options 1)", "symbol key"),
        ("(#gn-get options)", "requires"),
        (
            "(#gn-symbol-append Word \" extra\")",
            "one ordinary identifier",
        ),
        ("(#gn-symbol-append Word \"()\")", "one ordinary identifier"),
        ("(#gn-symbol-append 1 \"-alias\")", "symbol base"),
        ("(#gn-symbol-append Word 1)", "suffix"),
        ("(#gn-symbol-append Word)", "requires"),
    ] {
        let error = expand(expression).unwrap_err();
        assert!(error.message.contains(expected), "{expression}: {error:?}");
        let span = error
            .span
            .expect("generator error must have an invocation span");
        assert_eq!(span.source_id, 0);
        assert_eq!(span.line, 2);
        assert!(span.end > span.start);
    }
}
