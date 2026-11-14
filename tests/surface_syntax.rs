#[test]
fn slash_comments_do_not_consume_literals_and_keep_source_positions() {
    let source = "first// adjacent comment\n\"https://example.test\" #\\/ last";
    let forms = lim::parse(source).unwrap();
    assert_eq!(forms.len(), 4);
    assert_eq!(forms[0].expr, lim::Expr::Symbol("first".into()));
    assert_eq!(
        forms[1].expr,
        lim::Expr::String("https://example.test".into())
    );
    assert_eq!(forms[2].expr, lim::Expr::Char('/'));
    assert_eq!(forms[3].span.start, source.rfind("last").unwrap());
    let formatted = lim::format_source(source).unwrap();
    assert!(formatted.contains("// adjacent comment"));
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
}
