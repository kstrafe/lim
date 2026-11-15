mod support;

use lim::{lsp::{self, json::{self, Json}}, CompileConfig, Diagnostic, DiagnosticCode};
use std::{collections::BTreeMap, fs, io::Cursor};

fn object<const N: usize>(fields: [(&str, Json); N]) -> Json {
    Json::Object(fields.into_iter().map(|(key, value)| (key.into(), value)).collect::<BTreeMap<_, _>>())
}
fn string(value: impl Into<String>) -> Json { Json::String(value.into()) }
fn number(value: usize) -> Json { Json::Number(value.to_string()) }
fn position(source: &str, byte: usize) -> Json {
    let prefix = &source[..byte];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count();
    let character = prefix.rsplit('\n').next().unwrap().encode_utf16().count();
    object([("line", number(line)), ("character", number(character))])
}
fn range(source: &str, start: usize, end: usize) -> Json {
    object([("start", position(source, start)), ("end", position(source, end))])
}

fn session(source: &str, queries: &[(usize, &str, usize)]) -> (String, Vec<Json>) {
    let scratch = support::Scratch::new("lsp-conditional-records");
    let path = scratch.path().join("main.lim");
    // Public requests must use the unsaved document, including its UTF-16 ranges.
    fs::write(&path, "#fn main { #params = {}; #returns = (); #body: #return (); }").unwrap();
    let uri = lsp::path_to_uri(&path).unwrap();
    let mut messages = vec![
        object([("jsonrpc", string("2.0")), ("id", number(1)), ("method", string("initialize")), ("params", object([]))]),
        object([("jsonrpc", string("2.0")), ("method", string("initialized")), ("params", object([]))]),
        object([("jsonrpc", string("2.0")), ("method", string("textDocument/didOpen")), ("params", object([
            ("textDocument", object([
                ("uri", string(&uri)), ("languageId", string("lim")),
                ("version", number(1)), ("text", string(source)),
            ])),
        ]))]),
    ];
    for &(id, method, byte) in queries {
        messages.push(object([
            ("jsonrpc", string("2.0")), ("id", number(id)), ("method", string(method)),
            ("params", object([
                ("textDocument", object([("uri", string(&uri))])),
                ("position", position(source, byte)),
            ])),
        ]));
    }
    messages.push(object([("jsonrpc", string("2.0")), ("id", number(999)), ("method", string("shutdown")), ("params", Json::Null)]));
    messages.push(object([("jsonrpc", string("2.0")), ("method", string("exit")), ("params", Json::Null)]));
    let mut input = Vec::new();
    for message in messages { json::write_frame(&mut input, &message.render()).unwrap(); }
    let mut output = Vec::new();
    assert_eq!(lsp::serve(Cursor::new(input), &mut output, &CompileConfig::default()).unwrap(), 0);
    let mut output = Cursor::new(output);
    let mut messages = Vec::new();
    while let Some(message) = json::read_frame(&mut output).unwrap() {
        messages.push(json::parse(&message).unwrap());
    }
    (uri, messages)
}
fn result(messages: &[Json], id: usize) -> &Json {
    messages.iter().find(|message| message.get("id").and_then(Json::integer) == Some(id as i64))
        .unwrap().get("result").unwrap()
}
fn diagnostics<'a>(messages: &'a [Json], uri: &str) -> &'a [Json] {
    messages.iter().rev().find_map(|message| {
        if message.get("method").and_then(Json::string) != Some("textDocument/publishDiagnostics") {
            return None;
        }
        let params = message.get("params")?;
        (params.get("uri").and_then(Json::string) == Some(uri))
            .then(|| params.get("diagnostics").unwrap().array().unwrap())
    }).expect("document diagnostics")
}
fn marked(source: &str) -> (String, usize, usize) {
    let start = source.find("[[").unwrap();
    let closing = source[start + 2..].find("]]").unwrap() + start + 2;
    let token = &source[start + 2..closing];
    (format!("{}{}{}", &source[..start], token, &source[closing + 2..]), start, start + token.len())
}
fn semantic_error(source: &str) -> Diagnostic {
    let scratch = support::Scratch::new("conditional-semantic-span");
    lim::check_source_with_generated_sources(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        &scratch.path().join("generated"),
    ).unwrap_err()
}

#[test]
fn compiler_and_public_lsp_pinpoint_conditional_values_and_statement_keywords() {
    for head in ["#if", "#if-valid"] {
        for fields in [
            "#condition = [[42u64]]; #then = 42u64; #else = 0u64;",
            "#condition = flag; #then = (#block (#let noise #bool false) 42u64); #else = [[false]];",
            "#condition = flag; #then = 0u64; #else = (#if { #condition = true; #then = (#block (#let noise #bool false) 42u64); #else = [[false]]; });",
            "#condition = flag;\n      #then:\n        #let noise #bool false;\n        42u64;\n      #else:\n        #let noise #u64 42u64;\n        [[false]];\n",
            "#condition = flag; #then = [[missing-value]]; #else = 0u64;",
            "#condition = flag; #then = ([[#return]] 42u64); #else = 0u64;",
            "#condition = flag;\n      #then:\n        #let value #u64 [[false]];\n        value;\n      #else = 0u64;",
        ] {
            let (source, start, end) = marked(&format!(
                "#fn choose {{ #params = {{ flag = #bool; }}; #returns = #u64; #body:\n    #let text (#array #char 1) \"🙂\"; #return ({head} {{ {fields} }});\n}}"
            ));
            let error = semantic_error(&source);
            assert_eq!(error.code, DiagnosticCode::Type, "{}\n{source}", error.message);
            let span = error.span.unwrap();
            assert_eq!((span.start, span.end), (start, end), "{}\n{source}", error.message);
            let (uri, messages) = session(&source, &[]);
            let published = diagnostics(&messages, &uri);
            assert_eq!(published.len(), 1, "{published:?}\n{source}");
            let code = error.code_string();
            assert_eq!(published[0].get("code").and_then(Json::string), Some(code.as_str()));
            assert_eq!(published[0].get("range"), Some(&range(&source, start, end)), "{published:?}\n{source}");
        }
    }
}

#[test]
fn public_information_uses_branch_scopes_and_leaves_all_markers_without_targets() {
    let source = r#"
#fn identity { #params = { value = #u64; }; #returns = #u64; #body: #return value; }
#fn condition { #params = {}; #returns = (); #body: #return (); }
#fn then { #params = {}; #returns = (); #body: #return (); }
#fn else { #params = {}; #returns = (); #body: #return (); }
#fn choose {
  #params = { flag = #bool; input = #u64; };
  #returns = #u64;
  #body:
    #return (#if {
      #condition = flag;
      #then:
        #let branch #u64 input;
        #let text (#array #char 1) "🙂"; identity { value = branch; };
      #else = (#block (#let branch #u64 7u64) branch);
    });
}
"#;
    let use_start = source.find("value = branch").unwrap() + "value = ".len();
    let label = source.find("value = branch").unwrap();
    let local = source.find("#let branch").unwrap() + "#let ".len();
    let mut queries = vec![
        (2, "textDocument/hover", use_start),
        (3, "textDocument/definition", use_start),
        (4, "textDocument/signatureHelp", label),
    ];
    let mut marker_ids = Vec::new();
    for marker in ["#if {", "#condition", "#then", "#else"] {
        let byte = source.find(marker).unwrap();
        let length = marker.trim_end_matches(" {").len();
        for offset in 0..length {
            for method in ["textDocument/definition", "textDocument/hover", "textDocument/signatureHelp"] {
                let id = queries.len() + 2;
                queries.push((id, method, byte + offset));
                marker_ids.push(id);
            }
        }
    }
    let (uri, messages) = session(source, &queries);
    assert!(diagnostics(&messages, &uri).is_empty());
    let hover = result(&messages, 2);
    let text = hover.get("contents").unwrap().get("value").unwrap().string().unwrap();
    assert!(text.contains("branch") && text.contains("#u64"), "{hover:?}");
    assert_eq!(hover.get("range"), Some(&range(source, use_start, use_start + "branch".len())));
    let definition = match result(&messages, 3) {
        Json::Array(locations) => { assert_eq!(locations.len(), 1); &locations[0] }
        location => location,
    };
    assert_eq!(definition.get("uri").and_then(Json::string), Some(uri.as_str()));
    assert_eq!(definition.get("range"), Some(&range(source, local, local + "branch".len())));
    let help = result(&messages, 4);
    assert_eq!(help.get("activeParameter").and_then(Json::integer), Some(0));
    assert!(help.get("signatures").unwrap().array().unwrap()[0]
        .get("label").unwrap().string().unwrap().contains("identity"));
    for id in marker_ids {
        assert_eq!(result(&messages, id), &Json::Null, "marker query {id}");
    }
}

#[test]
fn public_diagnostics_keep_parse_ranges_and_evidence_failures_distinct() {
    for (fields, marker) in [
        ("#condition = true; #then = 42u64; [[#else]] = 0u64; #else = 1u64;", "duplicate"),
        ("#condition = true; #then = 42u64; #else = 0u64; [[#otherwise]] = ();", "unknown"),
    ] {
        // Mark the second duplicate, which is the actual offending key.
        let fields = if marker == "duplicate" {
            fields.replace("[[#else]]", "#else").replace("#else = 1", "[[#else]] = 1")
        } else { fields.to_owned() };
        let (source, start, end) = marked(&format!(
            "#fn main {{ #params = {{}}; #returns = #u64; #body: #return (#if {{ {fields} }}); }}"
        ));
        let error = semantic_error(&source);
        assert_eq!(error.code, DiagnosticCode::Parse);
        assert!(error.message.contains(marker), "{}", error.message);
        assert_eq!(error.span.map(|span| (span.start, span.end)), Some((start, end)));
        let (uri, messages) = session(&source, &[]);
        let published = diagnostics(&messages, &uri);
        assert_eq!(published.len(), 1);
        assert_eq!(published[0].get("range"), Some(&range(&source, start, end)));
    }
    let (source, start, end) = marked(
        "#fn main { #params = {}; #returns = #u64; #body: #return (#if [[{ #condition = true; #then = 42u64; }]]); }"
    );
    let error = semantic_error(&source);
    assert_eq!(error.code, DiagnosticCode::Parse);
    assert!(error.message.contains("requires '#else'"));
    assert_eq!(error.span.map(|span| (span.start, span.end)), Some((start, end)));
    let (uri, messages) = session(&source, &[]);
    let published = diagnostics(&messages, &uri);
    assert_eq!(published.len(), 1);
    assert_eq!(published[0].get("range"), Some(&range(&source, start, end)));
    let source = r#"
#fn positive { #params = { value = #u64; }; #returns = #bool; #body: #return [#u64; value > 0u64]; }
#fn accept { #params = { value = #u64; }; #returns = #u64; #requires: positive { value = value; }; #body: #return value; }
#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let-mut value #u64 42u64;
    #return (#if-valid {
      #condition = (positive { value; });
      #then:
        #set value 0u64;
        accept { value; };
      #else = 0u64;
    });
}
"#;
    let error = semantic_error(source);
    assert_eq!(error.code, DiagnosticCode::Contract);
    assert!(error.message.contains("missing evidence"), "{}", error.message);
    let span = error.span.unwrap();
    assert!(source[span.start..span.end].contains("accept"), "{span:?}");
    let (uri, messages) = session(source, &[]);
    let published = diagnostics(&messages, &uri);
    assert_eq!(published.len(), 1);
    let code = error.code_string();
    assert_eq!(published[0].get("code").and_then(Json::string), Some(code.as_str()));
    assert_eq!(published[0].get("range"), Some(&range(source, span.start, span.end)));
}
