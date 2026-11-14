//! Helpers for treating compiler generated artifacts as ordinary test input.

/// Remove the optional compiler context header from one generated artifact.
///
/// Parsing supplies exact top level spans, so comments and all other source
/// text are preserved byte for byte. This is a test fixture transformation;
/// removing the header disarms its privileges rather than trusting the
/// generated body with compiler authority.
pub fn ordinary_source(artifact: &str) -> String {
    let forms = lim::parse(artifact).expect("generated artifact parses as raw syntax");
    let headers = forms
        .iter()
        .filter(|form| {
            matches!(&form.expr, lim::Expr::List(items)
                if matches!(items.first(), Some(lim::Expr::Symbol(name)) if name == "#generated-context"))
        })
        .collect::<Vec<_>>();
    assert!(
        headers.len() <= 1,
        "artifact has multiple #generated-context headers"
    );

    let mut source = artifact.to_owned();
    for header in headers.into_iter().rev() {
        source.replace_range(header.span.start..header.span.end, "");
    }
    source
}

#[cfg(test)]
mod tests {
    use super::ordinary_source;

    #[test]
    fn removes_multiline_header_and_preserves_comments_and_body_exactly() {
        let header = "(#generated-context\n  compiler-owned\n  provenance)";
        let artifact = format!(
            "// generated file\n{header}\n// keep this comment\n(#fn generated () #u64 (#return 42u64))\n"
        );
        let expected =
            "// generated file\n\n// keep this comment\n(#fn generated () #u64 (#return 42u64))\n";
        assert_eq!(ordinary_source(&artifact), expected);
    }

    #[test]
    fn public_program_parser_still_rejects_authored_header_and_nested_text_is_untouched() {
        let authored = "(#generated-context forged)";
        let error = lim::parse_program(authored).unwrap_err();
        assert!(error.contains("compiler-owned"), "{error}");

        let nested = "(#fn text () (#slice #u8) (#return \"#generated-context\"))";
        assert_eq!(ordinary_source(nested), nested);
    }
}
