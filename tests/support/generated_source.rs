//! Helpers for treating compiler generated artifacts as ordinary test input.

/// Remove the optional compiler context header from one generated artifact.
///
/// Parsing supplies exact top level spans, so comments and all other source
/// text are preserved byte for byte. This is a test fixture transformation;
/// removing the header disarms its privileges rather than trusting the
/// generated body with compiler authority.
pub fn ordinary_source(artifact: &str) -> String {
    let forms = lim::parse_source_unit(artifact).expect("generated artifact parses as a source unit");
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

/// Restore local spellings when moving an inspected file's declarations back
/// into that same authored file. Foreign references and string data stay exact.
#[allow(dead_code)]
pub fn ordinary_source_in_file(artifact: &str, path: &std::path::Path) -> String {
    let mut source = ordinary_source(artifact);
    let prefix = format!("{}::", path.display());
    for token in lim::lex(&source).unwrap().into_iter().rev() {
        if let lim::TokenKind::Symbol(name) = token.kind {
            if let Some(local) = name.strip_prefix(&prefix) {
                source.replace_range(token.span.start..token.span.end, local);
            }
        }
    }
    source
}

#[cfg(test)]
mod tests {
    use super::ordinary_source;

    #[test]
    fn restoring_local_names_preserves_foreign_references_and_string_data() {
        let source =
            "#fn /entry.lim::work () #u64 (#return /other.lim::value)\n \"/entry.lim::data\"";
        assert_eq!(
            super::ordinary_source_in_file(source, std::path::Path::new("/entry.lim")),
            "#fn work () #u64 (#return /other.lim::value)\n \"/entry.lim::data\""
        );
    }

    #[test]
    fn removes_multiline_header_and_preserves_comments_and_body_exactly() {
        let header = "#generated-context\n    compiler-owned\n    provenance\n";
        let artifact = format!(
            "// generated file\n{header}\n// keep this comment\n(#fn generated () #u64 (#return 42u64))\n"
        );
        let expected =
            "// generated file\n\n// keep this comment\n#fn generated () #u64 (#return 42u64)\n";
        assert_eq!(ordinary_source(&artifact), expected);
    }

    #[test]
    fn public_program_parser_still_rejects_authored_header_and_nested_text_is_untouched() {
        let authored = "#generated-context forged\n";
        let error = lim::parse_program(authored).unwrap_err();
        assert!(error.contains("compiler-owned"), "{error}");

        let nested = "#fn text () (#slice #u8) (#return \"#generated-context\")\n";
        assert_eq!(ordinary_source(nested), nested);
    }
}

/// Inspect declarations rather than relying on formatter whitespace or file prefixes.
#[allow(dead_code)]
pub fn contains_function(source: &str, expected: &str) -> bool {
    contains_declaration(source, "#fn", expected)
}

pub fn contains_declaration(source: &str, keyword: &str, expected: &str) -> bool {
    lim::parse_source_unit(source).unwrap().iter().any(|form| {
        matches!(form.children.first().map(|node| &node.expr), Some(lim::Expr::Symbol(head)) if head == keyword)
            && matches!(form.children.get(1).map(|node| &node.expr), Some(lim::Expr::Symbol(name)) if name == expected || name.ends_with(&format!("::{expected}")))
    })
}
