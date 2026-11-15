mod support;

use lim::lsp::{self, json::{self, Json}};
use std::{collections::BTreeMap, fs, io::Cursor, path::Path};

fn object<const N: usize>(fields: [(&str, Json); N]) -> Json {
    Json::Object(fields.into_iter().map(|(key, value)| (key.into(), value)).collect::<BTreeMap<_, _>>())
}
fn string(value: impl Into<String>) -> Json { Json::String(value.into()) }
fn number(value: usize) -> Json { Json::Number(value.to_string()) }
fn position(source: &str, byte: usize) -> Json {
    let prefix = &source[..byte];
    object([
        ("line", number(prefix.bytes().filter(|byte| *byte == b'\n').count())),
        ("character", number(prefix.rsplit('\n').next().unwrap().encode_utf16().count())),
    ])
}
fn information(path: &Path, source: &str, queries: &[(usize, &str, usize)]) -> Vec<Json> {
    let uri = lsp::path_to_uri(path).unwrap();
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
    messages.push(object([("jsonrpc", string("2.0")), ("id", number(99)), ("method", string("shutdown")), ("params", Json::Null)]));
    messages.push(object([("jsonrpc", string("2.0")), ("method", string("exit")), ("params", Json::Null)]));
    let mut input = Vec::new();
    for message in messages { json::write_frame(&mut input, &message.render()).unwrap(); }
    let mut output = Vec::new();
    assert_eq!(lsp::serve(Cursor::new(input), &mut output, &lim::CompileConfig::default()).unwrap(), 0);
    let mut output = Cursor::new(output);
    let mut messages = Vec::new();
    while let Some(message) = json::read_frame(&mut output).unwrap() {
        messages.push(json::parse(&message).unwrap());
    }
    messages
}
fn result(messages: &[Json], id: usize) -> &Json {
    messages.iter().find(|message| message.get("id").and_then(Json::integer) == Some(id as i64))
        .unwrap().get("result").unwrap()
}
fn hover(messages: &[Json], id: usize) -> &str {
    result(messages, id).get("contents").unwrap().get("value").unwrap().string().unwrap()
}

fn location(value: &Json) -> &Json {
    match value {
        Json::Array(values) => { assert_eq!(values.len(), 1, "{value:?}"); &values[0] }
        Json::Null => panic!("missing definition"),
        value => value,
    }
}
fn assert_definition(value: &Json, path: &Path, source: &str, start: usize, token: &str) {
    let value = location(value);
    assert_eq!(value.get("uri").and_then(Json::string), Some(lsp::path_to_uri(path).unwrap().as_str()));
    let range = value.get("range").unwrap();
    assert_eq!(range.get("start"), Some(&position(source, start)), "{value:?}");
    assert_eq!(range.get("end"), Some(&position(source, start + token.len())), "{value:?}");
}

#[test]
fn generator_record_labels_and_hover_follow_aliases_and_file_targets() {
    let scratch = support::Scratch::new("generator-record-information");
    fs::create_dir(scratch.path().join("library")).unwrap();
    let module = "#export emit helper\n#gn emit { public = bound; } `()\n#gn-fn helper { payload = local; } local\n";
    let imported = scratch.path().join("library/lib.lim");
    fs::write(&imported, module).unwrap();
    fs::write(scratch.path().join("facade.lim"), "#alias make = ./library/lib.lim::emit\n#alias invoke = ./library/lib.lim::helper\n").unwrap();
    let source = r#"#alias renamed = ./facade.lim::make
#alias helper-alias = ./facade.lim::invoke
#fn emit { #params = (); #returns = #u64; #body = ((#return 42u64)); }
#gn outer { input = value; }
  (#gn-call helper-alias { payload = value; })
#gn outer-direct { input = value; }
  (#gn-call ./library/lib.lim::helper { payload = value; })
#generate renamed { public = (); }
#generate outer { input = (); }
#generate outer-direct { input = (); }
#generate ./library/lib.lim::emit { public = (); }
"#;
    let path = scratch.path().join("main.lim");
    fs::write(&path, source).unwrap();
    lim::parse_program_from_path(source, &path).unwrap();
    let helper_value = source.find("payload = value").unwrap() + "payload = ".len();
    let messages = information(&path, source, &[
        (2, "textDocument/definition", source.find("renamed {").unwrap()),
        (3, "textDocument/definition", source.find("public =").unwrap()),
        (4, "textDocument/definition", source.find("helper-alias {").unwrap()),
        (5, "textDocument/definition", source.find("payload =").unwrap()),
        (6, "textDocument/definition", helper_value),
        (7, "textDocument/hover", source.find("public =").unwrap()),
        (8, "textDocument/hover", helper_value),
        (9, "textDocument/definition", source.rfind("public =").unwrap()),
        (10, "textDocument/definition", source.find("./library/lib.lim::emit {").unwrap()),
        (11, "textDocument/definition", source.find("./library/lib.lim::helper {").unwrap()),
        (12, "textDocument/definition", source.rfind("payload =").unwrap()),
    ]);
    assert_definition(result(&messages, 2), &imported, module, module.find("emit {").unwrap(), "emit");
    assert_definition(result(&messages, 3), &imported, module, module.find("public =").unwrap(), "public");
    assert_definition(result(&messages, 4), &imported, module, module.find("helper {").unwrap(), "helper");
    assert_definition(result(&messages, 5), &imported, module, module.find("payload =").unwrap(), "payload");
    assert_definition(result(&messages, 6), &path, source, source.find("input = value").unwrap() + "input = ".len(), "value");
    assert_definition(result(&messages, 9), &imported, module, module.find("public =").unwrap(), "public");
    assert_definition(result(&messages, 10), &imported, module, module.find("emit {").unwrap(), "emit");
    assert_definition(result(&messages, 11), &imported, module, module.find("helper {").unwrap(), "helper");
    assert_definition(result(&messages, 12), &imported, module, module.find("payload =").unwrap(), "payload");
    assert!(hover(&messages, 7).contains("generator argument label public"), "{}", hover(&messages, 7));
    assert!(hover(&messages, 7).contains("public = bound"));
    assert!(hover(&messages, 8).contains("generator binding value"), "{}", hover(&messages, 8));
    assert!(!hover(&messages, 7).contains(".lim::"));
}

#[test]
fn bundled_standard_generator_paths_have_callee_and_label_roles() {
    // This fixture is accepted with the parent's reserved #std/ path loader
    // and bundled generator-record migration; it grants no filesystem alias.
    let scratch = support::Scratch::new("generator-record-std-path");
    let source = "#generate #std/cell.lim::cell { value-type = #u64; name = Counter; create = create-counter; get = get-counter; set = set-counter; }\n";
    let path = scratch.path().join("main.lim");
    let messages = information(&path, source, &[
        (2, "textDocument/definition", source.find("#std/cell.lim::cell").unwrap()),
        (3, "textDocument/definition", source.find("name =").unwrap()),
        (4, "textDocument/hover", source.find("name =").unwrap()),
    ]);
    for id in [2, 3] {
        let target = location(result(&messages, id));
        assert!(target.get("uri").unwrap().string().unwrap().ends_with("/cell.lim"), "{target:?}");
    }
    let library = include_str!("../library/cell.lim");
    let declaration = library.find("#gn cell").unwrap() + "#gn ".len();
    assert_eq!(location(result(&messages, 2)).get("range").unwrap().get("start"), Some(&position(library, declaration)));
    assert!(hover(&messages, 4).contains("generator label and binding name"), "{}", hover(&messages, 4));
}

#[test]
fn capability_hover_describes_the_interface_across_its_implementations() {
    let scratch = support::Scratch::new("generator-record-capability-information");
    let source = "#capability Copy #u64 ()\n#capability Copy #u32 ()\n#gn emit { type = (ty Copy); } `()\n";
    let path = scratch.path().join("main.lim");
    let messages = information(&path, source, &[
        (2, "textDocument/hover", source.rfind("Copy").unwrap()),
    ]);
    let value = hover(&messages, 2);
    for part in ["#capability Copy #u64", "#capability Copy #u32"] {
        assert!(value.contains(part), "missing {part}: {value}");
    }
}
