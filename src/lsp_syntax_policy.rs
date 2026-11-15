//! Navigation review inventory. Adding a language form must also update its
//! source roles, positive/negative navigation tests, and docs/lsp-design.md.
//!
//! Generator record policy: declaration keys are public labels; value patterns
//! alone bind generator names. Puns share one authored span. Capability names
//! refer only to capability declarations, never same-spelled lexical bindings.
//! #generate values remain syntax data (apart from @ and nested #fn roles);
//! #gn-call values are evaluated in generator scope, and labels target helper
//! keys. An invocation pun retains both destinations when its label and value
//! are semantic references; repeated source spans are deduplicated. Calls
//! require the correct #gn/#gn-fn declaration kind. Quoted labels
//! and bare record values never acquire local roles through token spelling.
//! Bundled #std/...lim::symbol callees use file-target navigation, including
//! when the leading # would otherwise resemble an ordinary reserved keyword.
//!
//! Conditional records retain lexical roles in #condition and separate scopes
//! in #then/#else. '=' values remain expressions; colon branches are #block
//! statements. The reserved field markers and delimiters have no targets.

#[cfg(test)]
mod tests {
    // Deliberately independent of is_builtin_form: deriving this list from the
    // parser would let new syntax silently bypass navigation review.
    const REVIEWED: &[&str] = &[
        "abi", // Function-record metadata key; ABI keywords have no definition.
        "abi-c",
        "addr-of",
        "addr-of-mut",
        "alias",
        "align-of",
        "arch",
        "arg", // Bare value binds to the explicit single positional parameter.
        "array", // Also #generate #array: literal inputs and generated definitions.
        "array-of",
        "array-repeat",
        "as",
        "asm",
        "assert",
        "assume",
        "requires",
        "ensures",
        "preserves",
        "if-valid",
        "where",
        "old",
        "result",
        "atomic",
        "atomic-compare-exchange",
        "atomic-compare-exchange-weak",
        "atomic-exchange",
        "atomic-fetch-add",
        "atomic-init",
        "atomic-load",
        "atomic-store",
        "await",
        "block",
        "body", // Generic inline/indented ':' is punctuation, excluded from key/reference spans.
        "bool",
        "borrow",
        "borrow-mut",
        "borrow-slice",
        "borrow-slice-mut",
        "break",
        "break-to",
        "call", // Marker-free record/colon-argument calls; labels target parameters.
        "call-graph",
        "capability",
        "case",
        "case-pin",
        "case-pin-mut",
        "case-ref",
        "case-ref-mut",
        "cfg-and",
        "cfg-else",
        "cfg-if",
        "cfg-is",
        "cfg-not",
        "cfg-or",
        "char",
        "clone",
        "const",
        "condition", // Conditional record metadata; never a value reference.
        "continue",
        "continue-to",
        "debug-assert",
        "deref",
        "deref-set",
        "dispatch-case", // Keyword opens artifact; operands resolve dispatcher/variant/handler.
        "dispatch-fn", // Explicit signature; selected parameter is a local use.
        "dispatch-on", // Contextual metadata; value targets a declared parameter.
        "distributed-enum",
        "drop",
        "effects", // Explicit permissions: function/global targets, never keyword definitions.
        "effects-of",
        "global-access",
        "io",
        "io-input",
        "io-input-byte",
        "io-output",
        "io-output-byte",
        "read-global",
        "write-global",
        "else",
        "enum",
        "enum-contribute",
        "enum-literal",
        "export",
        "extern-fn",
        "f32",
        "f64",
        "fn",
        "for",
        "for-range", // Layout headers retain binder/body scopes; ':' has no target.
        "forget",
        "get",
        "generate", // Named literal arguments; keys target #gn record declarations.
        "generated-context",
        "get-payload",
        "gn", // Record keys are distinct from body bindings; puns share a span.
        "gn-call", // #gn-fn keys + evaluated generator-scope values.
        "gn-equal",
        "gn-error",
        "gn-first",
        "gn-fn", // Capabilities annotate binding values, not argument keys.
        "gn-for-each",
        "gn-gensym",
        "gn-get",
        "gn-if",
        "gn-length",
        "gn-list",
        "gn-list?",
        "gn-rest",
        "gn-symbol",
        "gn-symbol-append",
        "gn-symbol?",
        "gn-variant",
        "i128",
        "i16",
        "i32",
        "i64",
        "i8",
        "if",
        "if-let",
        "index",
        "index-proven",
        "isize",
        "label",
        "let",
        "let-else",
        "let-mut",
        "linear",
        "linux-syscall",
        "literal",
        "loop",
        "match",
        "memory-acq-rel",
        "memory-acquire",
        "memory-relaxed",
        "memory-release",
        "memory-seq-cst",
        "mut",
        "offset-of",
        "opaque",
        "or",
        "os",
        "panic",
        "params",
        "pin",
        "pin-borrow",
        "pin-borrow-mut",
        "pin-get-payload-unchecked",
        "pin-get-payload-unchecked-mut",
        "pin-own",
        "pin-own-borrow",
        "pin-own-borrow-mut",
        "pin-own-of",
        "pin-ptr-borrow",
        "pin-ptr-borrow-mut",
        "pin-read",
        "pin-ref",
        "pin-ref-mut",
        "pin-release",
        "pin-set-field",
        "pin-share",
        "pin-share-clone",
        "pin-shared",
        "pin-shared-borrow",
        "pin-shared-borrow-mut",
        "pin-shared-own",
        "pin-shared-release",
        "pin-write",
        "platform",
        "println",
        "ptr",
        "ptr-address",
        "ptr-borrow",
        "ptr-borrow-mut",
        "ptr-is-null",
        "ptr-mut",
        "ptr-null",
        "ptr-offset",
        "ptr-read",
        "ptr-write",
        "range",
        "ref",
        "ref-mut",
        "ref-ptr",
        "repr-c",
        "require-generated",
        "return",
        "returns",
        "saturate",
        "send",
        "set",
        "set-field",
        "set-index",
        "set-payload",
        "size-of",
        "slice",
        "slice-idx",
        "slice-len",
        "slice-mut",
        "slice-mut-idx",
        "slice-mut-len",
        "slice-mut-of",
        "slice-mut-range",
        "slice-mut-split",
        "slice-of",
        "slice-range",
        "static",
        "std",
        "struct",
        "struct-literal",
        "sync",
        "syntax",
        "syntax-splice",
        "target",
        "then", // Conditional record metadata; branch scopes remain separate.
        "thread-task",
        "thread-task-join",
        "thread-task-spawn",
        "tuple",
        "type",
        "u128",
        "u16",
        "u32",
        "u64",
        "u8",
        "unreachable",
        "unsafe",
        "unsafe-call",
        "value",
        "wrap",
        "unstable",
        "unsafe-fn",
        "unsafe-impl",
        "usize",
        "variant-is",
        "when",
        "while",
        "while-let",
        "word-forget",
        "word-read",
        "word-take",
        "word-view",
        "word-write",
    ];

    #[test]
    fn contract_keywords_have_navigation_review() {
        for name in [
            "requires",
            "ensures",
            "preserves",
            "assume",
            "if-valid",
            "where",
            "old",
            "result",
        ] {
            assert!(
                REVIEWED.contains(&name),
                "contract form #{name} needs navigation review"
            );
        }
    }

    #[test]
    fn every_parser_keyword_requires_a_navigation_review() {
        let source = include_str!("lib.rs");
        let forms = source
            .split("fn is_builtin_form(name:")
            .nth(1)
            .unwrap()
            .split("fn is_operator_symbol")
            .next()
            .unwrap();
        for name in forms.split('"').skip(1).step_by(2) {
            assert!(REVIEWED.contains(&name), "new syntax #{name} needs navigation roles, positive/negative LSP tests, and a design/checklist update");
        }
        let reference = include_str!("../docs/language.md")
            .split("### Complete `#` builtin reference (alphabetical)")
            .nth(1)
            .unwrap()
            .split("#### Typed operator families")
            .next()
            .unwrap();
        for line in reference.lines() {
            let Some(name) = line
                .split('|')
                .nth(1)
                .map(str::trim)
                .and_then(|cell| cell.strip_prefix("`#"))
                .and_then(|cell| cell.strip_suffix('`'))
            else {
                continue;
            };
            assert!(REVIEWED.contains(&name), "documented builtin #{name} needs navigation review too, including specialized parser forms and non-reference metadata");
        }
        let design = include_str!("../docs/lsp-design.md");
        assert!(design.contains("New syntax acceptance checklist"));
        assert!(design.contains("lsp_syntax_policy.rs"));
    }
}
