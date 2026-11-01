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
fn kernel_universes_and_dependent_binders_have_sequential_lexical_scopes() {
    run(
        r#"
      (#proof [[name|identity]] (#[[declaration|proof-definition]] ([[universe|u]])
        (#[[pi|pt-pi]] (([[type-binder|A]] (#pt-type [[signature-level|u]]))
                      ([[argument|x]] [[argument-type|A]])) [[codomain|A]])
        (#[[lambda|pt-lambda]] (([[value-type|A]] (#pt-type [[value-level|u]]))
                              ([[value-binder|x]] [[value-argument-type|A]])) [[body|x]])))
      (#proof separate (#proof-definition () #pt-nat [[no-leak|x]]))
    "#,
        &[
            ("name", &["name"]),
            ("declaration", &[]),
            ("pi", &[]),
            ("lambda", &[]),
            ("universe", &["universe"]),
            ("signature-level", &["universe"]),
            ("value-level", &["universe"]),
            ("type-binder", &["type-binder"]),
            ("argument", &["argument"]),
            ("argument-type", &["type-binder"]),
            ("codomain", &["type-binder"]),
            ("value-argument-type", &["value-type"]),
            ("body", &["value-binder"]),
            ("no-leak", &[]),
        ],
    );
}

#[test]
fn kernel_binder_types_precede_their_binding_and_nested_binders_shadow() {
    run(
        r#"
      (#proof scopes (#proof-definition () #pt-nat
        (#pt-lambda (([[outer|x]] #pt-nat))
          (#pt-app (#pt-lambda (([[inner|x]] [[own-type|x]])) [[inner-use|x]]) [[outer-use|x]]))))
      (#proof bad-scope (#proof-definition () #pt-nat
        (#pt-pi ((first [[later-type|later]]) (later #pt-nat)) [[first-use|first]])))
    "#,
        &[
            ("own-type", &["outer"]),
            ("inner-use", &["inner"]),
            ("outer-use", &["outer"]),
            ("later-type", &[]),
        ],
    );
}

#[test]
fn universe_levels_have_a_separate_namespace_and_never_resolve_globals() {
    run(
        r#"
      (#fn missing () #u64 (#return 0u64))
      (#proof levels (#proof-definition ([[universe|u]] [[other|v]])
        (#pt-type (#[[max|pt-level-max]] [[level|u]] (#[[succ|pt-level-succ]] [[successor|v]]) [[number|0]]))
        (#pt-lambda (([[local|u]] #pt-nat))
          (#pt-pair (#pt-type [[level-under-local|u]]) [[local-use|u]] [[universe-as-term|v]]))))
      (#proof missing-level (#proof-definition () (#pt-type [[unknown|missing]]) #pt-zero))
    "#,
        &[
            ("level", &["universe"]),
            ("successor", &["other"]),
            ("max", &[]),
            ("succ", &[]),
            ("number", &[]),
            ("level-under-local", &["universe"]),
            ("local-use", &["local"]),
            ("universe-as-term", &[]),
            ("unknown", &[]),
        ],
    );
}

#[test]
fn explicit_kernel_references_use_proof_declarations_instead_of_local_values() {
    run(
        r#"
      (#proof [[target|NatAlias]] (#proof-definition ([[target-level|u]]) (#pt-type 0) #pt-nat))
      (#proof [[procedural|runtime-proof]] (#proof-eq 0u64 0u64))
      (#fn function () #u64 (#return 0u64))
      (#proof refs (#proof-definition ([[universe|v]]) #pt-nat
        (#pt-lambda ((NatAlias #pt-nat) (runtime-proof #pt-nat))
          (#pt-app (#[[use-keyword|pt-use]] [[reference|NatAlias]] ([[explicit-level|v]]))
            (#[[program-keyword|pt-program]] [[program|runtime-proof]])
            (#[[certificate-keyword|pt-certificate]] [[certificate|runtime-proof]])
            (#pt-use [[wrong-kind|function]] ())
            (#pt-program [[wrong-program|NatAlias]])
            (#pt-use [[wrong-use|runtime-proof]] ())))))
    "#,
        &[
            ("reference", &["target"]),
            ("explicit-level", &["universe"]),
            ("program", &["procedural"]),
            ("certificate", &["procedural"]),
            ("use-keyword", &[]),
            ("program-keyword", &[]),
            ("certificate-keyword", &[]),
            ("wrong-kind", &[]),
            ("wrong-program", &[]),
            ("wrong-use", &[]),
        ],
    );
}

#[test]
fn sigma_and_term_operands_reuse_kernel_scopes_without_runtime_lookup() {
    for expression in [
        "(#pt-app vALUE vALUE vALUE)",
        "(#pt-eq vALUE vALUE vALUE)",
        "(#pt-refl vALUE vALUE)",
        "(#pt-eq-elim vALUE vALUE vALUE vALUE vALUE vALUE)",
        "(#pt-pair vALUE vALUE vALUE)",
        "(#pt-first vALUE)",
        "(#pt-second vALUE)",
        "(#pt-succ vALUE)",
        "(#pt-nat-induct vALUE vALUE vALUE vALUE)",
    ] {
        let mut counter = 0;
        let mut expression = expression.to_owned();
        while let Some(start) = expression.find("vALUE") {
            expression.replace_range(start..start + 5, &format!("[[use-{counter}|value]]"));
            counter += 1;
        }
        let source = format!("(#proof operands (#proof-definition () #pt-nat (#pt-lambda (([[binder|value]] #pt-nat)) {expression})))");
        let queries = (0..counter)
            .map(|index| format!("use-{index}"))
            .collect::<Vec<_>>();
        let expected = queries
            .iter()
            .map(|name| (name.as_str(), &["binder"][..]))
            .collect::<Vec<_>>();
        run(&source, &expected);
    }
    run(
        r#"
      (#proof dependent-pair (#proof-definition ()
        (#[[sigma-keyword|pt-sigma]] (([[binder|first]] #pt-nat)) (#pt-eq #pt-nat [[left|first]] [[right|first]]))
        [[outside|first]]))
    "#,
        &[
            ("sigma-keyword", &[]),
            ("left", &["binder"]),
            ("right", &["binder"]),
            ("outside", &[]),
        ],
    );
}

#[test]
fn inductive_constructor_labels_and_dependent_fields_are_scoped_to_the_datatype() {
    run(
        r#"
      (#proof [[datatype|Box]] (#proof-inductive ([[level|u]])
        (([[parameter|A]] (#pt-type [[parameter-level|u]]))) (#pt-type [[sort-level|u]])
        (([[constructor|pack]] (([[field|value]] [[field-type|A]])
                               ([[evidence|same]] (#pt-eq [[equality-type|A]] [[field-left|value]] [[field-right|value]]))))
         (other (([[isolated|value]] [[other-type|A]]) (leak [[field-leak|same]]))))))
      (#proof Another (#proof-inductive () () (#pt-type 0) ((pack ()))))
      (#proof make (#proof-definition ([[use-level|v]]) #pt-nat
        (#pt-lambda (([[element|T]] (#pt-type v)) ([[argument|x]] T))
          (#pt-construct [[datatype-use|Box]] ([[level-use|v]]) ([[parameter-use|T]]) [[constructor-use|pack]] ([[field-use|x]] x)))))
      (#proof eliminate (#proof-definition () #pt-nat
        (#pt-lambda (([[term|x]] #pt-nat))
          (#pt-induct [[induct-type|Box]] (0) ([[induct-param|x]]) [[motive|x]] ([[branch-one|x]] [[branch-two|x]]) [[subject|x]]))))
    "#,
        &[
            ("datatype", &["datatype"]),
            ("parameter-level", &["level"]),
            ("sort-level", &["level"]),
            ("field-type", &["parameter"]),
            ("equality-type", &["parameter"]),
            ("field-left", &["field"]),
            ("field-right", &["field"]),
            ("other-type", &["parameter"]),
            ("field-leak", &[]),
            ("constructor", &["constructor"]),
            ("datatype-use", &["datatype"]),
            ("level-use", &["use-level"]),
            ("parameter-use", &["element"]),
            ("constructor-use", &["constructor"]),
            ("field-use", &["argument"]),
            ("induct-type", &["datatype"]),
            ("induct-param", &["term"]),
            ("motive", &["term"]),
            ("branch-one", &["term"]),
            ("branch-two", &["term"]),
            ("subject", &["term"]),
        ],
    );
}
#[test]
fn kernel_keywords_are_metadata_including_theorem_declarations() {
    for keyword in [
        "pt-type",
        "pt-pi",
        "pt-lambda",
        "pt-sigma",
        "pt-use",
        "pt-app",
        "pt-level-succ",
        "pt-level-max",
        "pt-eq",
        "pt-refl",
        "pt-eq-elim",
        "pt-pair",
        "pt-first",
        "pt-second",
        "pt-succ",
        "pt-numeral",
        "pt-nat-induct",
        "pt-construct",
        "pt-induct",
        "pt-program",
        "pt-certificate",
    ] {
        run(
            &format!("(#fn {keyword} () #u64 (#return 0u64)) (#proof test (#proof-definition () #pt-nat (#[[keyword|{keyword}]])))"),
            &[("keyword", &[])],
        );
    }
    run(
        r#"
      (#proof [[theorem|reflexive]] (#[[keyword|proof-theorem]] ()
        (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero)))
    "#,
        &[("theorem", &["theorem"]), ("keyword", &[])],
    );
}

#[test]
fn kernel_metadata_and_bare_names_never_fall_back_to_global_spellings() {
    for expression in [
        "#[[query|pt-prop]]",
        "#[[query|pt-nat]]",
        "#[[query|pt-zero]]",
        "#[[query|pt-false]]",
        "#[[query|pt-self]]",
        "(#pt-numeral [[query|3]])",
        "(#pt-type [[query|value]])",
        "[[query|value]]",
        "[[query|@value]]",
        "(#pt-custom [[query|value]])",
        "(#get value [[query|value]])",
    ] {
        let source = format!("(#proof value (#proof-definition () #pt-nat #pt-zero)) (#proof test (#proof-definition () #pt-nat {expression}))");
        run(&source, &[("query", &[])]);
    }
}

#[test]
fn constructor_lookup_fails_closed_for_missing_ambiguous_or_noninductive_targets() {
    run(
        r#"
      (#fn label () #u64 (#return 0u64))
      (#proof Duplicate (#proof-inductive () () (#pt-type 0) ((same ()) (same ()))))
      (#proof Ordinary (#proof-definition () (#pt-type 0) #pt-nat))
      (#proof Empty (#proof-inductive () () (#pt-type 0) ()))
      (#proof duplicate-use (#proof-definition () #pt-nat
        (#pt-construct Duplicate () () [[ambiguous|same]] ())))
      (#proof missing-use (#proof-definition () #pt-nat
        (#pt-construct Empty () () [[missing|label]] ())))
      (#proof wrong-use (#proof-definition () #pt-nat
        (#pt-construct [[noninductive|Ordinary]] () () [[wrong-label|label]] ())))
    "#,
        &[
            ("ambiguous", &[]),
            ("missing", &[]),
            ("noninductive", &[]),
            ("wrong-label", &[]),
        ],
    );
}

#[test]
fn imported_proofs_aliases_levels_and_constructor_labels_keep_source_identity() {
    run_files(
        r#"
      (#alias Imported = ./facade.lim::Forward)
      (#alias ImportedBox = ./library.lim::Box)
      (#proof NatAlias (#proof-definition () (#pt-type 0) #pt-nat))
      (#proof refs (#proof-definition ([[level|v]]) (#pt-type 0)
        (#pt-app (#pt-use [[alias|Imported]] ([[level-use|v]]))
                 (#pt-use [[path|./library.lim::NatAlias]] ()))))
      (#proof constructed (#proof-definition () #pt-nat
        (#pt-construct [[datatype|ImportedBox]] () () [[constructor|pack]] ())))
      (#alias certificate = ./library.lim::checked)
      (#proof bridge (#proof-theorem () #pt-prop (#pt-certificate [[procedural|certificate]])))
    "#,
        &[
            (
                "library.lim",
                r#"
              (#proof [[original|NatAlias]] (#proof-definition (u) (#pt-type 0) #pt-nat))
              (#proof [[box|Box]] (#proof-inductive () () (#pt-type 0) (([[pack|pack]] ()))))
              (#proof [[checked|checked]] (#proof-eq 0u64 0u64))
            "#,
            ),
            ("facade.lim", "(#alias Forward = ./library.lim::NatAlias)"),
        ],
        &[
            ("alias", &["original"]),
            ("path", &["original"]),
            ("level-use", &["level"]),
            ("datatype", &["box"]),
            ("constructor", &["pack"]),
            ("procedural", &["checked"]),
        ],
    );
}

#[test]
fn generated_kernel_proofs_resolve_to_their_emitted_declarations() {
    run(
        r#"
      (#gn emit () `((#proof nat-alias (#proof-definition () (#pt-type 0) #pt-nat))
                    (#proof zero (#proof-definition () (#pt-use nat-alias ()) #pt-zero))))
      (#generate emit)
      (#proof use-generated (#proof-definition () (#pt-type 0) (#pt-use [[use|nat-alias]] ())))
    "#,
        &[("use", &["generated:nat-alias"])],
    );
}

#[test]
fn imported_generators_expose_kernel_names_through_the_final_file_scope() {
    run_files(
        r#"
      (#alias emit = ./generator.lim::emit)
      (#generate emit)
      (#proof use-generated (#proof-definition () (#pt-type 0) (#pt-use [[use|generated-nat]] ())))
    "#,
        &[(
            "generator.lim",
            "(#gn emit () `((#proof generated-nat (#proof-definition () (#pt-type 0) #pt-nat))))",
        )],
        &[("use", &["generated:generated-nat"])],
    );
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
                    let declaration = format!("(#proof {token} ");
                    let start = text.find(&declaration).unwrap() + "(#proof ".len();
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
