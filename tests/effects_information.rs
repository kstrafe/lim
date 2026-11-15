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
fn signature(messages: &[Json], id: usize) -> &Json {
    &result(messages, id).get("signatures").unwrap().array().unwrap()[0]
}

#[test]
fn declared_effects_have_their_own_hover_and_signature_section() {
    let scratch = support::Scratch::new("effects-information");
    let source = r#"#static counter (#atomic #u64) (#atomic-init #u64 0u64)
#fn valid { #params = ((value #u64)); #returns = #bool;
  #body = ( (#return true) ); }
#fn emit { #params = (); #returns = (); #effects = (#io-output);
  #body = ( (#return ()) ); }
#fn inspect {
  #params = ((value #u64)); #returns = #u64;
  #effects = (#io-input (#read-global counter) (#effects-of @emit));
  #requires = ((#call valid ((value value))));
  #ensures = ((#call valid ((value (#result)))));
  #body = ( (#return value) );
}
#fn caller {
  #params = ((input #u64)); #returns = #u64;
  #effects = ((#effects-of @inspect));
  #requires = ((#call valid ((value input))));
  #body = ( (#return (#call inspect ((value input)))) );
}
"#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let path = scratch.path().join("main.lim");
    fs::write(&path, source).unwrap();
    let call = source.find("inspect ((value input))").unwrap();
    let messages = information(&path, source, &[
        (2, "textDocument/hover", source.find("inspect {").unwrap()),
        (3, "textDocument/hover", call),
        (4, "textDocument/signatureHelp", call + "inspect ((value ".len()),
    ]);
    let documentation = signature(&messages, 4).get("documentation").unwrap().get("value").unwrap().string().unwrap();
    for value in [hover(&messages, 2), hover(&messages, 3), documentation] {
        let (contracts, effects) = value.split_once("// Declared effects").unwrap();
        // Predicate metadata may be appended by the parent integration. Check
        // this declared section independently of any following section.
        let effects = effects.split("\n// ").next().unwrap();
        for contract in ["#requires", "#ensures", "#call valid"] {
            assert!(contracts.contains(contract), "{value}");
            assert!(!effects.contains(contract), "{value}");
        }
        for permission in ["#effects", "#io-input", "(#read-global counter)", "(#effects-of @emit)"] {
            assert!(effects.contains(permission), "{value}");
        }
        assert!(!effects.contains("#io-output"), "declared inclusions must remain authored: {value}");
        assert!(!effects.contains("predicate"), "{value}");
    }
    assert!(signature(&messages, 4).get("label").unwrap().string().unwrap().contains("inspect"));
}

#[test]
fn aliased_effect_information_preserves_private_authored_targets() {
    let scratch = support::Scratch::new("effects-information-alias");
    let module = r#"#export inspect
#static hidden-counter (#atomic #u64) (#atomic-init #u64 0u64)
#fn inspect {
  #params = (); #returns = #u64;
  #effects = ((#read-global hidden-counter));
  #body = ( (#return 42u64) );
}
"#;
    fs::create_dir(scratch.path().join("library")).unwrap();
    fs::write(scratch.path().join("library/lib.lim"), module).unwrap();
    fs::write(scratch.path().join("facade.lim"), "#alias operation = ./library/lib.lim::inspect\n").unwrap();
    let source = r#"#alias renamed = ./facade.lim::operation
#fn inspect { #params = (); #returns = #u64; #body = ( (#return 7u64) ); }
#fn caller { #params = (); #returns = #u64;
  #effects = ((#effects-of @renamed));
  #body = ( (#return (#call renamed ())) ); }
#fn local { #params = (); #returns = #u64;
  #body = ( (#return (#call inspect ())) ); }
"#;
    let path = scratch.path().join("main.lim");
    fs::write(&path, source).unwrap();
    lim::check_types(&lim::parse_program_from_path(source, &path).unwrap()).unwrap();
    let messages = information(&path, source, &[
        (2, "textDocument/hover", source.find("renamed ()").unwrap()),
        (3, "textDocument/signatureHelp", source.find("renamed ()").unwrap() + "renamed (".len()),
        (4, "textDocument/hover", source.find("inspect ()").unwrap()),
    ]);
    let documentation = signature(&messages, 3).get("documentation").unwrap().get("value").unwrap().string().unwrap();
    for value in [hover(&messages, 2), documentation] {
        assert!(value.contains("// Declared effects"), "{value}");
        assert!(value.contains("(#read-global hidden-counter)"), "{value}");
        assert!(!value.contains(".lim::"), "{value}");
        assert!(!value.contains("#global-access"), "{value}");
    }
    let local = hover(&messages, 4);
    assert!(local.contains("inspect"), "{local}");
    assert!(!local.contains("Declared effects"), "{local}");
    assert!(!local.contains("hidden-counter"), "{local}");
}

#[test]
fn explicit_empty_effects_remain_distinct_from_omitted_declarations() {
    let scratch = support::Scratch::new("effects-information-empty");
    let source = "#fn empty { #params = (); #returns = (); #effects = (); #body = ( (#return ()) ); }\n#fn omitted { #params = (); #returns = (); #body = ( (#return ()) ); }\n";
    let path = scratch.path().join("main.lim");
    let messages = information(&path, source, &[
        (2, "textDocument/hover", source.find("empty {").unwrap()),
        (3, "textDocument/hover", source.find("omitted {").unwrap()),
    ]);
    let empty = hover(&messages, 2);
    assert!(empty.contains("// Declared effects"), "{empty}");
    assert!(empty.contains("#effects = ()"), "{empty}");
    assert!(!hover(&messages, 3).contains("Declared effects"));
}
