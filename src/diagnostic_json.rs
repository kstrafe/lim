use crate::{Diagnostic, DiagnosticCode, Span};
use std::fmt::Write;

pub(crate) fn quoted(value: &str) -> String {
    let mut output = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            ch if ch <= '\u{1f}' => {
                write!(output, "\\u{:04x}", ch as u32).unwrap();
            }
            ch => output.push(ch),
        }
    }
    output.push('"');
    output
}

fn location(path: &str, span: Span) -> String {
    format!("{{\"path\":{},\"source_id\":{},\"byte_start\":{},\"byte_end\":{},\"line\":{},\"column\":{}}}",
        quoted(path), span.source_id, span.start, span.end, span.line, span.column)
}

/// One newline-free JSON object; offsets are zero-based UTF-8 byte ranges,
/// while line/column are one-based Unicode scalar positions, not screen cells.
pub fn render_diagnostic_json(diagnostic: &Diagnostic, default_path: &str) -> String {
    let path = diagnostic.source_name.as_deref().unwrap_or(default_path);
    let phase = match diagnostic.code {
        DiagnosticCode::Lex => "lex",
        DiagnosticCode::Parse => "parse",
        DiagnosticCode::Generator => "generator",
        DiagnosticCode::Type => "type",
        DiagnosticCode::Borrow => "borrow",
        DiagnosticCode::Linear => "linear",
        DiagnosticCode::Unsafe => "unsafe",
        DiagnosticCode::Proof => "proof",
        DiagnosticCode::Codegen => "codegen",
        DiagnosticCode::Link => "link",
        DiagnosticCode::Cli => "cli",
        DiagnosticCode::UnusedType => "unused_type",
    };
    let mut labels = Vec::new();
    if let Some(span) = diagnostic.span {
        labels.push(format!(
            "{{\"primary\":true,\"message\":{},\"location\":{}}}",
            quoted(&diagnostic.message),
            location(path, span)
        ));
    }
    labels.extend(diagnostic.labels.iter().map(|label| {
        format!(
            "{{\"primary\":false,\"message\":{},\"location\":{}}}",
            quoted(&label.message),
            location(label.source_name.as_deref().unwrap_or(path), label.span)
        )
    }));
    let expansion = diagnostic
        .expansion_provenance
        .iter()
        .map(|label| location(label.source_name.as_deref().unwrap_or(path), label.span))
        .collect::<Vec<_>>()
        .join(",");
    format!("{{\"schema_version\":1,\"severity\":{},\"code\":{},\"category\":{},\"message\":{},\"path\":{},\"location\":{},\"labels\":[{}],\"expansion_provenance\":[{}],\"notes\":[{}]}}",
        quoted(diagnostic.severity.as_str()), quoted(&diagnostic.code_string()), quoted(phase), quoted(&diagnostic.message), quoted(path),
        diagnostic.span.map(|span| location(path, span)).unwrap_or_else(|| "null".into()),
        labels.join(","), expansion, diagnostic.notes.iter().map(|note| quoted(note)).collect::<Vec<_>>().join(","))
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;
    #[test]
    fn escapes_controls_quotes_backslashes_and_preserves_unicode() {
        assert_eq!(
            quoted("é\"\\\n\r\t\0\u{8}\u{1f}"),
            "\"é\\\"\\\\\\n\\r\\t\\u0000\\u0008\\u001f\""
        );
        let error = Diagnostic::new(DiagnosticCode::Type, "bad\nvalue");
        let json = render_diagnostic_json(&error, "a:\"é.lim");
        assert!(!json.contains('\n'));
        assert!(json.contains("\"location\":null"));
        assert!(json.contains("\"schema_version\":1"));
    }
}
