mod support;

use lim::lsp::{
    self,
    json::{self, Json},
};
use std::{collections::BTreeMap, fs, io::Cursor, path::Path};

fn object<const N: usize>(fields: [(&str, Json); N]) -> Json {
    Json::Object(
        fields
            .into_iter()
            .map(|(key, value)| (key.into(), value))
            .collect::<BTreeMap<_, _>>(),
    )
}
fn string(value: impl Into<String>) -> Json {
    Json::String(value.into())
}
fn number(value: usize) -> Json {
    Json::Number(value.to_string())
}
fn position(source: &str, byte: usize) -> Json {
    let prefix = &source[..byte];
    object([
        (
            "line",
            number(prefix.bytes().filter(|byte| *byte == b'\n').count()),
        ),
        (
            "character",
            number(prefix.rsplit('\n').next().unwrap().encode_utf16().count()),
        ),
    ])
}
fn information(documents: &[(&Path, &str)], queries: &[(usize, usize, &str, usize)]) -> Vec<Json> {
    let mut messages = vec![
        object([
            ("jsonrpc", string("2.0")),
            ("id", number(1)),
            ("method", string("initialize")),
            ("params", object([])),
        ]),
        object([
            ("jsonrpc", string("2.0")),
            ("method", string("initialized")),
            ("params", object([])),
        ]),
    ];
    for &(path, source) in documents {
        let uri = lsp::path_to_uri(path).unwrap();
        messages.push(object([
            ("jsonrpc", string("2.0")),
            ("method", string("textDocument/didOpen")),
            (
                "params",
                object([(
                    "textDocument",
                    object([
                        ("uri", string(&uri)),
                        ("languageId", string("lim")),
                        ("version", number(1)),
                        ("text", string(source)),
                    ]),
                )]),
            ),
        ]));
    }
    for &(id, document, method, byte) in queries {
        let (path, source) = documents[document];
        let uri = lsp::path_to_uri(path).unwrap();
        messages.push(object([
            ("jsonrpc", string("2.0")),
            ("id", number(id)),
            ("method", string(method)),
            (
                "params",
                object([
                    ("textDocument", object([("uri", string(&uri))])),
                    ("position", position(source, byte)),
                ]),
            ),
        ]));
    }
    messages.push(object([
        ("jsonrpc", string("2.0")),
        ("id", number(99)),
        ("method", string("shutdown")),
        ("params", Json::Null),
    ]));
    messages.push(object([
        ("jsonrpc", string("2.0")),
        ("method", string("exit")),
        ("params", Json::Null),
    ]));
    let mut input = Vec::new();
    for message in messages {
        json::write_frame(&mut input, &message.render()).unwrap();
    }
    let mut output = Vec::new();
    assert_eq!(
        lsp::serve(
            Cursor::new(input),
            &mut output,
            &lim::CompileConfig::default()
        )
        .unwrap(),
        0
    );
    let mut output = Cursor::new(output);
    let mut messages = Vec::new();
    while let Some(message) = json::read_frame(&mut output).unwrap() {
        messages.push(json::parse(&message).unwrap());
    }
    messages
}
fn result(messages: &[Json], id: usize) -> &Json {
    messages
        .iter()
        .find(|message| message.get("id").and_then(Json::integer) == Some(id as i64))
        .unwrap()
        .get("result")
        .unwrap()
}
fn location(value: &Json) -> &Json {
    match value {
        Json::Array(values) => {
            assert_eq!(values.len(), 1, "{value:?}");
            &values[0]
        }
        Json::Null => panic!("missing definition"),
        value => value,
    }
}
fn assert_definition(value: &Json, path: &Path, source: &str, start: usize, token: &str) {
    let value = location(value);
    assert_eq!(
        value.get("uri").and_then(Json::string),
        Some(lsp::path_to_uri(path).unwrap().as_str())
    );
    let range = value.get("range").unwrap();
    assert_eq!(
        range.get("start"),
        Some(&position(source, start)),
        "{value:?}"
    );
    assert_eq!(
        range.get("end"),
        Some(&position(source, start + token.len())),
        "{value:?}"
    );
}

const TYPES: &str = "#distributed-enum Choice ()\n#enum-contribute Choice (Choice.Full #u64)\n#enum-contribute Choice (Choice.Empty)\n";
const HANDLERS: &str = "#fn full { #params = { extra = #u64; value = #u64; }; #returns = #u64; #body: #return (#u64::add-wrap value extra); }\n";
const SOURCE: &str = r#"// 😀 origins stay attached to their own source files.
#alias Choice = ./types.lim::Choice
#alias remote = ./handlers.lim::full
#alias same = ./facade.lim::handler
#dispatch-fn evaluate {
  #params = { value = Choice; extra = #u64; };
  #returns = #u64;
  #dispatch-on = value;
}
#dispatch-case evaluate Choice.Full remote
#dispatch-case evaluate Choice.Full same
#dispatch-case evaluate Choice.Empty empty
#fn full { #params = {}; #returns = #u64; #body: #return 99u64; }
#fn empty { #params = { extra = #u64; }; #returns = #u64; #body: #return extra; }
#fn main { #params = {}; #returns = #u64;
  #body: #return (evaluate { value = (Choice.Full 40u64); extra = 2u64; }); }
"#;

fn fixture(root: &Path) -> std::path::PathBuf {
    fs::write(root.join("types.lim"), TYPES).unwrap();
    fs::write(root.join("handlers.lim"), HANDLERS).unwrap();
    fs::write(
        root.join("facade.lim"),
        "#alias handler = ./handlers.lim::full\n",
    )
    .unwrap();
    fs::write(
        root.join("lim.lsp"),
        "schema-version = 2\n[[context]]\nentry = \"main.lim\"\ntarget = \"x86_64-sysv\"\n",
    )
    .unwrap();
    let path = root.join("main.lim");
    fs::write(&path, SOURCE).unwrap();
    path
}
fn node<'a>(forms: &'a [lim::SpannedExpr], head: &str) -> &'a lim::SpannedExpr {
    fn find<'a>(forms: &'a [lim::SpannedExpr], head: &str) -> Option<&'a lim::SpannedExpr> {
        for form in forms {
            if matches!(form.children.first().map(|node| &node.expr), Some(lim::Expr::Symbol(name)) if name == head)
            {
                return Some(form);
            }
            if let Some(found) = find(&form.children, head) {
                return Some(found);
            }
        }
        None
    }
    find(forms, head).unwrap_or_else(|| panic!("missing {head}"))
}
fn diagnostics(messages: &[Json]) -> impl Iterator<Item = &Json> {
    messages
        .iter()
        .filter(|message| {
            message.get("method").and_then(Json::string) == Some("textDocument/publishDiagnostics")
        })
        .flat_map(|message| {
            message
                .get("params")
                .unwrap()
                .get("diagnostics")
                .unwrap()
                .array()
                .unwrap()
        })
}
fn related<'a>(diagnostic: &'a Json, message: &str) -> &'a Json {
    diagnostic
        .get("relatedInformation")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .find(|label| {
            label
                .get("message")
                .unwrap()
                .string()
                .unwrap()
                .contains(message)
        })
        .unwrap_or_else(|| panic!("missing {message}: {diagnostic:?}"))
        .get("location")
        .unwrap()
}
fn assert_range(value: &Json, source: &str, span: lim::Span) {
    assert_eq!(
        value.get("start"),
        Some(&position(source, span.start)),
        "{value:?}"
    );
    assert_eq!(
        value.get("end"),
        Some(&position(source, span.end)),
        "{value:?}"
    );
}

#[test]
fn source_dispatch_roles_publish_and_navigate_exact_alias_and_file_targets() {
    let scratch = support::Scratch::new("lsp-dispatch-source");
    let path = fixture(scratch.path());
    let call = SOURCE.rfind("evaluate {").unwrap();
    let registration = SOURCE.find("#dispatch-case").unwrap();
    let mut artifact = None;
    for _ in 0..2 {
        let messages = information(
            &[(&path, SOURCE)],
            &[
                (
                    2,
                    0,
                    "textDocument/definition",
                    SOURCE.find("#dispatch-fn").unwrap(),
                ),
                (3, 0, "textDocument/definition", call),
                (
                    4,
                    0,
                    "textDocument/definition",
                    SOURCE.find("evaluate {").unwrap(),
                ),
                (5, 0, "textDocument/definition", registration),
                (
                    6,
                    0,
                    "textDocument/definition",
                    registration + "#dispatch-case evaluate ".len(),
                ),
                (
                    7,
                    0,
                    "textDocument/definition",
                    registration + "#dispatch-case evaluate Choice.Full ".len(),
                ),
                (
                    8,
                    0,
                    "textDocument/definition",
                    SOURCE.find("Choice.Full same").unwrap() + "Choice.Full ".len(),
                ),
                (
                    9,
                    0,
                    "textDocument/definition",
                    SOURCE.find("#dispatch-on = value").unwrap() + "#dispatch-on = ".len(),
                ),
                (
                    10,
                    0,
                    "textDocument/definition",
                    SOURCE.find("#dispatch-on").unwrap(),
                ),
                (
                    11,
                    0,
                    "textDocument/definition",
                    SOURCE.find("#params").unwrap(),
                ),
                (
                    12,
                    0,
                    "textDocument/definition",
                    SOURCE.find("#returns = #u64").unwrap() + "#returns = ".len(),
                ),
                (
                    13,
                    0,
                    "textDocument/definition",
                    SOURCE.find("value = Choice").unwrap() + "value = ".len(),
                ),
                (
                    14,
                    0,
                    "textDocument/definition",
                    registration + "#dispatch-case ".len(),
                ),
            ],
        );
        assert!(
            !diagnostics(&messages)
                .any(|diagnostic| diagnostic.get("severity").and_then(Json::integer) == Some(1)),
            "{messages:?}"
        );
        let generated = lsp::uri_to_path(
            location(result(&messages, 2))
                .get("uri")
                .unwrap()
                .string()
                .unwrap(),
        )
        .unwrap();
        assert!(fs::read_to_string(&generated).unwrap().contains("#match"));
        if let Some(previous) = &artifact {
            assert_eq!(previous, &generated);
        }
        artifact = Some(generated.clone());
        assert_eq!(result(&messages, 2), result(&messages, 5));
        let snapshot = lsp::uri_to_path(
            location(result(&messages, 3))
                .get("uri")
                .unwrap()
                .string()
                .unwrap(),
        )
        .unwrap();
        let emitted = fs::read_to_string(&snapshot).unwrap();
        let forms = lim::parse_source_unit(&emitted).unwrap();
        let function = node(&forms, "#fn");
        let name = &function.children[1];
        let token = &emitted[name.span.start..name.span.end];
        assert_definition(
            result(&messages, 3),
            &snapshot,
            &emitted,
            name.span.start,
            token,
        );
        assert_definition(
            result(&messages, 4),
            &snapshot,
            &emitted,
            name.span.start,
            token,
        );
        assert_definition(
            result(&messages, 6),
            &scratch.path().join("types.lim"),
            TYPES,
            TYPES.find("Choice.Full").unwrap(),
            "Choice.Full",
        );
        for id in [7, 8] {
            assert_definition(
                result(&messages, id),
                &scratch.path().join("handlers.lim"),
                HANDLERS,
                HANDLERS.find("full").unwrap(),
                "full",
            );
        }
        assert_definition(
            result(&messages, 9),
            &path,
            SOURCE,
            SOURCE.find("value = Choice").unwrap(),
            "value",
        );
        assert_definition(
            result(&messages, 13),
            &scratch.path().join("types.lim"),
            TYPES,
            TYPES.find("Choice").unwrap(),
            "Choice",
        );
        assert_definition(
            result(&messages, 14),
            &snapshot,
            &emitted,
            name.span.start,
            token,
        );
        for id in [10, 11, 12] {
            assert_eq!(result(&messages, id), &Json::Null);
        }
    }
}

#[test]
fn generated_function_case_variant_and_handler_keep_current_origins_on_cached_runs() {
    let scratch = support::Scratch::new("lsp-dispatch-generated");
    let path = fixture(scratch.path());
    let messages = information(
        &[(&path, SOURCE)],
        &[
            (
                2,
                0,
                "textDocument/definition",
                SOURCE.rfind("evaluate {").unwrap(),
            ),
            (
                3,
                0,
                "textDocument/definition",
                SOURCE.find("#dispatch-fn").unwrap(),
            ),
        ],
    );
    let snapshot = lsp::uri_to_path(
        location(result(&messages, 2))
            .get("uri")
            .unwrap()
            .string()
            .unwrap(),
    )
    .unwrap();
    let emitted = fs::read_to_string(&snapshot).unwrap();
    let forms = lim::parse_source_unit(&emitted).unwrap();
    let function = node(&forms, "#fn");
    let case = node(&forms, "#case");
    // Collection emits variants in canonical order; choose the payload arm.
    fn payload_case(forms: &[lim::SpannedExpr]) -> Option<&lim::SpannedExpr> {
        for form in forms {
            if matches!(form.children.first().map(|node| &node.expr), Some(lim::Expr::Symbol(head)) if head == "#case")
                && form
                    .children
                    .get(1)
                    .is_some_and(|pattern| matches!(pattern.expr, lim::Expr::List(_)))
            {
                return Some(form);
            }
            if let Some(found) = payload_case(&form.children) {
                return Some(found);
            }
        }
        None
    }
    let case = payload_case(&forms).unwrap_or(case);
    let variant = &case.children[1].children[0];
    let handler = &node(&case.children, "#call").children[1];
    for _ in 0..2 {
        let messages = information(
            &[(&path, SOURCE), (&snapshot, &emitted)],
            &[
                (
                    2,
                    1,
                    "textDocument/definition",
                    function.children[1].span.start,
                ),
                (3, 1, "textDocument/definition", case.children[0].span.start),
                (4, 1, "textDocument/definition", variant.span.start),
                (5, 1, "textDocument/definition", handler.span.start),
            ],
        );
        assert_definition(
            result(&messages, 2),
            &path,
            SOURCE,
            SOURCE.find("evaluate {").unwrap(),
            "evaluate",
        );
        let targets = result(&messages, 3)
            .array()
            .expect("case has registration and handler origins");
        assert_eq!(targets.len(), 3, "{targets:?}");
        for target in targets {
            if target.get("uri").unwrap().string().unwrap() == lsp::path_to_uri(&path).unwrap() {
                let start = target.get("range").unwrap().get("start").unwrap();
                let matches = SOURCE
                    .match_indices("#dispatch-case evaluate Choice.Full")
                    .any(|(byte, _)| *start == position(SOURCE, byte));
                assert!(matches, "{target:?}");
            } else {
                assert_definition(
                    target,
                    &scratch.path().join("handlers.lim"),
                    HANDLERS,
                    HANDLERS.find("full").unwrap(),
                    "full",
                );
            }
        }
        assert_definition(
            result(&messages, 4),
            &scratch.path().join("types.lim"),
            TYPES,
            TYPES.find("Choice.Full").unwrap(),
            "Choice.Full",
        );
        assert_definition(
            result(&messages, 5),
            &scratch.path().join("handlers.lim"),
            HANDLERS,
            HANDLERS.find("full").unwrap(),
            "full",
        );
    }
}

#[test]
fn missing_coverage_diagnostic_uses_dispatcher_and_variant_exact_ranges() {
    let scratch = support::Scratch::new("lsp-dispatch-missing");
    let path = fixture(scratch.path());
    let source = SOURCE.replace("#dispatch-case evaluate Choice.Empty empty", "");
    let messages = information(
        &[(&path, &source)],
        &[(
            2,
            0,
            "textDocument/definition",
            source.find("#dispatch-fn").unwrap(),
        )],
    );
    let diagnostic = diagnostics(&messages)
        .find(|diagnostic| {
            diagnostic
                .get("message")
                .unwrap()
                .string()
                .unwrap()
                .contains("missing a handler")
        })
        .unwrap();
    let start = source.find("evaluate {").unwrap();
    let range = diagnostic.get("range").unwrap();
    assert_eq!(range.get("start"), Some(&position(&source, start)));
    assert_eq!(
        range.get("end"),
        Some(&position(&source, start + "evaluate".len()))
    );
    let target = diagnostic
        .get("relatedInformation")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .map(|label| label.get("location").unwrap())
        .find(|location| {
            location.get("uri").unwrap().string().unwrap()
                == lsp::path_to_uri(&scratch.path().join("types.lim")).unwrap()
        })
        .unwrap();
    let variant = lim::parse_source_unit(TYPES)
        .unwrap()
        .into_iter()
        .find(|form| {
            form.children.iter().any(|child| {
                child
                    .children
                    .first()
                    .is_some_and(|node| node.expr == lim::Expr::Symbol("Choice.Empty".into()))
            })
        })
        .unwrap();
    assert_range(
        target.get("range").unwrap(),
        TYPES,
        variant.children[2].span,
    );
    assert_eq!(result(&messages, 2), &Json::Null);
}

#[test]
fn conflicting_registration_diagnostic_retains_both_exact_source_ranges() {
    let scratch = support::Scratch::new("lsp-dispatch-conflict");
    let path = fixture(scratch.path());
    let source = format!("{SOURCE}\n#fn other {{ #params = {{ value = #u64; extra = #u64; }}; #returns = #u64; #body: #return value; }}\n#dispatch-case evaluate Choice.Full other\n");
    let messages = information(&[(&path, &source)], &[]);
    let diagnostic = diagnostics(&messages)
        .find(|diagnostic| {
            diagnostic
                .get("message")
                .unwrap()
                .string()
                .unwrap()
                .contains("conflicting handlers")
        })
        .unwrap();
    let start = source.rfind("other").unwrap();
    let range = diagnostic.get("range").unwrap();
    assert_eq!(range.get("start"), Some(&position(&source, start)));
    assert_eq!(
        range.get("end"),
        Some(&position(&source, start + "other".len()))
    );
    let forms = lim::parse_source_unit(&source).unwrap();
    let first = node(&forms, "#dispatch-case");
    let earlier = diagnostic
        .get("relatedInformation")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .find(|label| {
            label
                .get("location")
                .unwrap()
                .get("range")
                .unwrap()
                .get("start")
                == Some(&position(&source, first.span.start))
        })
        .unwrap();
    assert_range(
        earlier.get("location").unwrap().get("range").unwrap(),
        &source,
        first.span,
    );
}

#[test]
fn emitted_call_errors_include_registration_and_handler_related_locations() {
    let scratch = support::Scratch::new("lsp-dispatch-effects-origins");
    let path = fixture(scratch.path());
    let handler = HANDLERS.replace("#body:", "#effects = (#io-output); #body:");
    fs::write(scratch.path().join("handlers.lim"), &handler).unwrap();
    let messages = information(
        &[(&path, SOURCE)],
        &[(
            2,
            0,
            "textDocument/definition",
            SOURCE.find("#dispatch-fn").unwrap(),
        )],
    );
    let diagnostic = diagnostics(&messages)
        .find(|diagnostic| {
            diagnostic
                .get("message")
                .unwrap()
                .string()
                .unwrap()
                .contains("explicit effect qualification")
        })
        .unwrap();
    let registration = node(&lim::parse_source_unit(SOURCE).unwrap(), "#dispatch-case").span;
    let location = related(diagnostic, "dispatch case registered here");
    assert_eq!(
        location.get("uri").unwrap().string().unwrap(),
        lsp::path_to_uri(&path).unwrap()
    );
    assert_range(location.get("range").unwrap(), SOURCE, registration);
    assert_definition(
        related(diagnostic, "dispatch handler defined here"),
        &scratch.path().join("handlers.lim"),
        &handler,
        handler.find("full").unwrap(),
        "full",
    );
    assert_eq!(
        result(&messages, 2),
        &Json::Null,
        "invalid emitted function must not publish an artifact"
    );
}

#[test]
fn unsaved_registration_changes_replace_cached_origins_instead_of_reusing_spans() {
    let scratch = support::Scratch::new("lsp-dispatch-overlay");
    let path = fixture(scratch.path());
    // Publish the original implementation before editing the registration set.
    information(
        &[(&path, SOURCE)],
        &[(
            2,
            0,
            "textDocument/definition",
            SOURCE.find("#dispatch-fn").unwrap(),
        )],
    );
    let edited = SOURCE.replace(
        "#dispatch-case evaluate Choice.Full same",
        "// duplicate removed in unsaved buffer",
    );
    let messages = information(
        &[(&path, &edited)],
        &[(
            2,
            0,
            "textDocument/definition",
            edited.rfind("evaluate {").unwrap(),
        )],
    );
    let snapshot = lsp::uri_to_path(
        location(result(&messages, 2))
            .get("uri")
            .unwrap()
            .string()
            .unwrap(),
    )
    .unwrap();
    let emitted = fs::read_to_string(&snapshot).unwrap();
    let forms = lim::parse_source_unit(&emitted).unwrap();
    fn payload_keyword(forms: &[lim::SpannedExpr]) -> Option<usize> {
        for form in forms {
            if matches!(form.children.first().map(|node| &node.expr), Some(lim::Expr::Symbol(head)) if head == "#case")
                && form
                    .children
                    .get(1)
                    .is_some_and(|pattern| matches!(pattern.expr, lim::Expr::List(_)))
            {
                return Some(form.children[0].span.start);
            }
            if let Some(found) = payload_keyword(&form.children) {
                return Some(found);
            }
        }
        None
    }
    let messages = information(
        &[(&path, &edited), (&snapshot, &emitted)],
        &[(
            2,
            1,
            "textDocument/definition",
            payload_keyword(&forms).unwrap(),
        )],
    );
    assert_eq!(
        result(&messages, 2).array().unwrap().len(),
        2,
        "{messages:?}"
    );
    assert_eq!(
        fs::read_to_string(&path).unwrap(),
        SOURCE,
        "checking must not save the buffer"
    );
}

#[test]
fn quoted_dispatch_forms_stay_literal() {
    let scratch = support::Scratch::new("lsp-dispatch-quoted");
    let path = fixture(scratch.path());
    let source =
        format!("{SOURCE}\n#gn quoted {{}} `((#dispatch-case evaluate Choice.Full remote))\n");
    let quoted = source.rfind("#dispatch-case").unwrap();
    let messages = information(
        &[(&path, &source)],
        &[
            (2, 0, "textDocument/definition", quoted),
            (
                3,
                0,
                "textDocument/definition",
                quoted + "#dispatch-case ".len(),
            ),
            (
                4,
                0,
                "textDocument/definition",
                quoted + "#dispatch-case evaluate ".len(),
            ),
            (
                5,
                0,
                "textDocument/definition",
                quoted + "#dispatch-case evaluate Choice.Full ".len(),
            ),
        ],
    );
    for id in 2..=5 {
        assert_eq!(result(&messages, id), &Json::Null);
    }
}

#[test]
fn dispatch_contracts_and_effect_clauses_keep_local_and_declaration_roles() {
    let scratch = support::Scratch::new("lsp-dispatch-contract-roles");
    let path = fixture(scratch.path());
    let source = SOURCE.replace("#dispatch-on = value;", "#dispatch-on = value;\n  #requires = ((#u64::lt extra 100u64));\n  #effects = ((#effects-of remote));")
        .replace("#body: #return (evaluate", "#body: (#assume (#u64::lt 2u64 100u64)) #return (evaluate");
    let messages = information(
        &[(&path, &source)],
        &[
            (
                2,
                0,
                "textDocument/definition",
                source.find("#u64::lt extra").unwrap() + "#u64::lt ".len(),
            ),
            (
                3,
                0,
                "textDocument/definition",
                source.find("#effects-of remote").unwrap() + "#effects-of ".len(),
            ),
            (
                4,
                0,
                "textDocument/definition",
                source.find("#requires").unwrap(),
            ),
            (
                5,
                0,
                "textDocument/definition",
                source.find("#effects-of").unwrap(),
            ),
        ],
    );
    assert_definition(
        result(&messages, 2),
        &path,
        &source,
        source.find("extra = #u64").unwrap(),
        "extra",
    );
    assert_definition(
        result(&messages, 3),
        &scratch.path().join("handlers.lim"),
        HANDLERS,
        HANDLERS.find("full").unwrap(),
        "full",
    );
    for id in [4, 5] {
        assert_eq!(result(&messages, id), &Json::Null);
    }
}
