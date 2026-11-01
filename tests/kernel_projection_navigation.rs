mod support;

use lim::lsp::{
    self,
    json::{self, Json},
};
use std::{collections::HashMap, io::Cursor};

fn quoted(s: &str) -> String {
    Json::String(s.into()).render()
}

#[test]
fn projection_navigates_family_and_scoped_subject_but_not_index_metadata() {
    run(
        r#"
      (#math-inductive [[family|Box]] () (([[parameter|A]] (#pt-type 0)))
        (#pt-type 0) ((pack ((value A)))))
      (#math-definition index-global () #pt-nat #pt-zero)
      (#math-definition [[subject-global|subject-global]] () #pt-nat #pt-zero)
      (#math-definition use () #pt-nat
        (#pt-lambda (([[binder|Box]] #pt-nat))
          (#pt-project [[family-use|Box]] [[ordinal|0]] [[subject-local|Box]])))
      (#math-definition global-use () #pt-nat
        (#pt-project Box 42 (#pt-use [[subject-global-use|subject-global]] ())))
      (#math-definition absolute-use () #pt-nat
        (#pt-project [[absolute-family|@Box]] 0 #pt-zero))
      (#math-definition outside-scope () #pt-nat
        (#pt-project Box 0 [[leak|Box]]))
    "#,
        &[
            ("family-use", &["family"]),
            ("binder", &["binder"]),
            ("subject-local", &["binder"]),
            ("ordinal", &[]),
            ("absolute-family", &["family"]),
            ("subject-global-use", &["subject-global"]),
            ("leak", &[]),
        ],
    );
}

#[test]
fn projection_family_alias_and_import_resolve_to_original_declaration() {
    run_files(
        r#"
      (#alias ImportedBox = ./families.lim::Box)
      (#math-definition use () #pt-nat
        (#pt-project [[family-use|ImportedBox]] 3 #pt-zero))
    "#,
        &[(
            "families.lim",
            "(#math-inductive [[family|Box]] () () (#pt-type 0) ((pack ())))",
        )],
        &[("family-use", &["family"])],
    );
}

#[test]
fn projection_family_direct_path_resolves_to_imported_declaration() {
    run_files(
        r#"
      (#math-definition use () #pt-nat
        (#pt-project [[family-use|./families.lim::Box]] 0 #pt-zero))
    "#,
        &[(
            "families.lim",
            "(#math-inductive [[family|Box]] () () (#pt-type 0) ((pack ())))",
        )],
        &[("family-use", &["family"])],
    );
}

#[test]
fn generated_projection_family_resolves_to_emitted_declaration() {
    run(
        r#"
      (#gn emit () `((#math-inductive generated-box () () (#pt-type 0)
        ((pack ((field #pt-nat)))))))
      (#generate emit)
      (#math-definition use ()
        (#pt-eq #pt-nat
          (#pt-project [[family-use|generated-box]] 0
            (#pt-construct generated-box () () pack (#pt-zero)))
          #pt-zero)
        (#pt-refl #pt-nat #pt-zero))
    "#,
        &[("family-use", &["generated:generated-box"])],
    );
}

#[test]
fn malformed_projection_forms_have_no_navigation_fallback() {
    for term in [
        "(#pt-project [[family|Box]] 0)",
        "(#pt-project [[family|Box]] -1 #pt-zero)",
        "(#pt-project [[family|Box]] [[index|index-global]] #pt-zero)",
        "(#pt-project [[family|Box]] 0 #pt-zero extra)",
        "(#pt-project [[family|Unknown]] 0 #pt-zero)",
    ] {
        let source = format!(
            "(#math-inductive Box () () (#pt-type 0) ((pack ()))) (#math-definition index-global () #pt-nat #pt-zero) (#math-definition use () #pt-nat {term})"
        );
        let mut expected = vec![("family", &[][..])];
        if term.contains("[[index|") {
            expected.push(("index", &[][..]));
        }
        run(&source, &expected);
    }
}

fn annotated(input: &str) -> (String, HashMap<String, (usize, usize)>) {
    let mut source = String::new();
    let mut marks = HashMap::new();
    let mut rest = input;
    while let Some(start) = rest.find("[[") {
        source.push_str(&rest[..start]);
        rest = &rest[start + 2..];
        let end = rest.find("]]").unwrap();
        let (label, token) = rest[..end].split_once('|').unwrap();
        let start = source.len();
        source.push_str(token);
        assert!(marks
            .insert(label.to_owned(), (start, source.len()))
            .is_none());
        rest = &rest[end + 2..];
    }
    source.push_str(rest);
    (source, marks)
}
fn run(input: &str, expected: &[(&str, &[&str])]) {
    run_files(input, &[], expected);
}
fn run_files(input: &str, files: &[(&str, &str)], expected: &[(&str, &[&str])]) {
    let scratch = support::Scratch::new("kernel-navigation");
    let uri = lsp::path_to_uri(&scratch.path().join("main.lim")).unwrap();
    let (source, marks) = annotated(input);
    lim::parse(&source).unwrap();
    let mut locations = HashMap::new();
    for (name, &(start, end)) in &marks {
        locations.insert(name.clone(), (uri.clone(), source.clone(), start, end));
    }
    for (path, input) in files {
        let (text, marks) = annotated(input);
        let path = scratch.path().join(path);
        std::fs::write(&path, &text).unwrap();
        let uri = lsp::path_to_uri(&path).unwrap();
        for (name, (start, end)) in marks {
            assert!(locations
                .insert(name, (uri.clone(), text.clone(), start, end))
                .is_none());
        }
    }
    let mut input = Vec::new();
    for body in [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_owned(),
        format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":1,\"languageId\":\"lim\",\"text\":{}}}}}}}", quoted(&uri), quoted(&source)),
    ] { json::write_frame(&mut input, &body).unwrap(); }
    for (index, (query, _)) in expected.iter().enumerate() {
        let (line, character) = lsp::byte_position(&source, marks[*query].0);
        json::write_frame(&mut input, &format!("{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":\"textDocument/definition\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}}}", index + 2, quoted(&uri))).unwrap();
    }
    json::write_frame(
        &mut input,
        r#"{"jsonrpc":"2.0","id":999,"method":"shutdown","params":null}"#,
    )
    .unwrap();
    json::write_frame(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    )
    .unwrap();
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
    let mut responses = HashMap::new();
    let mut diagnostics = Vec::new();
    while let Some(frame) = json::read_frame(&mut output).unwrap() {
        let value = json::parse(&frame).unwrap();
        if let Some(id) = value.get("id").and_then(Json::integer) {
            responses.insert(id, value);
        } else if value.get("method").and_then(Json::string)
            == Some("textDocument/publishDiagnostics")
        {
            diagnostics.push(value);
        }
    }
    for (index, (query, targets)) in expected.iter().enumerate() {
        let reply = &responses[&(index as i64 + 2)];
        let result = reply
            .get("result")
            .unwrap_or_else(|| panic!("{query}: {reply:?}"));
        let actual = match result {
            Json::Null => vec![],
            Json::Array(items) => items.iter().collect(),
            item => vec![item],
        };
        assert_eq!(
            actual.len(),
            targets.len(),
            "{query}: {result:?}\n{source}\nDiagnostics: {diagnostics:?}"
        );
        for target in *targets {
            let generated;
            let (target_uri, text, start, end) =
                if let Some(token) = target.strip_prefix("generated:") {
                    let item = actual[0];
                    let uri = item.get("uri").and_then(Json::string).unwrap().to_owned();
                    let path = lsp::uri_to_path(&uri).unwrap();
                    assert!(path
                        .file_name()
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .starts_with("editor-"));
                    let text = std::fs::read_to_string(path).unwrap();
                    let start = ["math-definition", "math-inductive", "theorem"]
                        .iter()
                        .find_map(|head| {
                            let prefix = format!("(#{head} ");
                            text.find(&format!("{prefix}{token} "))
                                .map(|start| start + prefix.len())
                        })
                        .or_else(|| text.find(&format!("({token} ")).map(|start| start + 1))
                        .unwrap();
                    generated = (uri, text, start, start + token.len());
                    &generated
                } else {
                    &locations[*target]
                };
            let (line, character) = lsp::byte_position(text, *start);
            let (end_line, end_character) = lsp::byte_position(text, *end);
            assert!(
                actual.iter().any(|item| {
                    let range = item.get("range").unwrap();
                    item.get("uri").and_then(Json::string) == Some(target_uri.as_str())
                        && range
                            .get("start")
                            .unwrap()
                            .get("line")
                            .and_then(Json::integer)
                            == Some(line as i64)
                        && range
                            .get("start")
                            .unwrap()
                            .get("character")
                            .and_then(Json::integer)
                            == Some(character as i64)
                        && range
                            .get("end")
                            .unwrap()
                            .get("line")
                            .and_then(Json::integer)
                            == Some(end_line as i64)
                        && range
                            .get("end")
                            .unwrap()
                            .get("character")
                            .and_then(Json::integer)
                            == Some(end_character as i64)
                }),
                "{query} must resolve to {target}: {result:?}"
            );
        }
    }
}
