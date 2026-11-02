use lim::{lex, parse, TokenKind};

#[test]
fn splice_marker_span_includes_comma_at_unicode_column() {
    let source = "alpha\n  λ ,@items";
    let tokens = lex(source).unwrap();
    let marker = tokens
        .iter()
        .find(|token| token.kind == TokenKind::UnquoteSplicing)
        .unwrap();
    assert_eq!(&source[marker.span.start..marker.span.end], ",@");
    assert_eq!((marker.span.line, marker.span.column), (2, 5));

    let forms = parse(source).unwrap();
    let splice = &forms[2];
    assert_eq!(&source[splice.span.start..splice.span.end], ",@items");
    assert_eq!((splice.span.line, splice.span.column), (2, 5));
    let child = &splice.children[0];
    assert_eq!(&source[child.span.start..child.span.end], "items");
}

#[test]
fn missing_splice_operand_underlines_both_marker_characters() {
    let source = "\n ,@";
    let directory = std::env::temp_dir();
    let error = lim::compile_source_to_assembly(
        source,
        &directory.join("lim-reader-span.lim"),
        &lim::CompileConfig::default(),
        &directory.join("lim-reader-span-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    let span = error.span.expect("missing operand has a source span");
    assert_eq!(&source[span.start..span.end], ",@");
    assert_eq!((span.line, span.column), (2, 2));
}
