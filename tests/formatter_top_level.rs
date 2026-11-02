fn assert_formatted(source: &str, expected: &str) {
    let formatted = lim::format_source(source).unwrap();
    assert_eq!(formatted, expected);
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
}

#[test]
fn top_level_comments_stay_with_their_expression_boundary() {
    assert_formatted(
        "alpha ; same line\n; between\nbeta\n; after",
        "alpha ; same line\n; between\nbeta\n; after\n",
    );
    assert_formatted("; before\nalpha\n; after\n", "; before\nalpha\n; after\n");
}

#[test]
fn adjacent_declarations_and_values_keep_declaration_spacing() {
    assert_formatted(
        "(#fn first () #u64 (#return 1u64)) value (#fn second () #u64 (#return 2u64))",
        "(#fn first () #u64\n  (#return 1u64))\n\nvalue\n\n(#fn second () #u64\n  (#return 2u64))\n",
    );
    assert_formatted(
        "(#fn first () #u64 (#return 1u64))\n\nvalue",
        "(#fn first () #u64\n  (#return 1u64))\n\nvalue\n",
    );
}

#[test]
fn quoted_and_reader_forms_are_preserved_across_top_level_boundaries() {
    assert_formatted(
        "'alpha `(#reader ,beta) ,@items",
        "'alpha\n`(#reader ,beta)\n,@items\n",
    );
}

#[test]
fn empty_and_comment_only_sources_have_a_final_newline() {
    assert_formatted("", "\n");
    assert_formatted(" ; only comment\n", "; only comment\n");
}

#[test]
fn malformed_trailing_expression_returns_error() {
    assert!(lim::format_source("valid (unterminated").is_err());
}

#[test]
fn lexical_parse_and_nesting_errors_match_the_ordinary_parser() {
    let too_deep = format!("valid {}value{}", "(".repeat(257), ")".repeat(257));
    for source in [
        "valid )",
        "valid (unterminated",
        "valid '",
        "valid `",
        "valid ,@",
        "valid (: name :)",
        ") \"unterminated",
        &too_deep,
    ] {
        assert_eq!(
            lim::format_source(source).unwrap_err(),
            lim::parse(source).unwrap_err(),
            "{source}"
        );
    }
}
