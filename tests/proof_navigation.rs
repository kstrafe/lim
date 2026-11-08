mod support;

use lim::lsp::{
    self,
    json::{self, Json},
};
use std::{collections::HashMap, io::Cursor};

fn quoted(s: &str) -> String {
    Json::String(s.into()).render()
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
    let scratch = support::Scratch::new("lsp-navigation");
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
    while let Some(frame) = json::read_frame(&mut output).unwrap() {
        let value = json::parse(&frame).unwrap();
        if let Some(id) = value.get("id").and_then(Json::integer) {
            responses.insert(id, value);
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
        assert_eq!(actual.len(), targets.len(), "{query}: {result:?}\n{source}");
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
                    let declaration = format!("(#fn {token} ");
                    let start = text.find(&declaration).unwrap() + "(#fn ".len();
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

#[test]
fn validation_descriptors_resolve_function_and_parameter_roles() {
    run_files(
        r#"
      (#alias check-user = ./validation.lim::validate)
      (#alias action = ./validation.lim::perform)
      (#const [[global|missing]] #u64 0u64)
      (#fn [[entry|entry]] ((object (#ref #u64))) () (#return ()))
      (#theorem safe
        (#[[keyword|proof-requires-validation]] [[entry-use|entry]]
          (#[[validator-marker|parameter-of]] [[validator-use|check-user]] [[validator-parameter|user]])
          (#[[action-marker|parameter-of]] [[action-use|action]] [[action-parameter|input]])))
      (#theorem editing
        (#proof-requires-validation entry (#parameter-of check-user [[missing-parameter|missing]])
          (#parameter-of action [[wrong-function-parameter|user]])))
      (#theorem bad-function
        (#proof-requires-validation entry (#parameter-of [[not-a-function|missing]] input) (#parameter-of action input)))
      (#theorem malformed
        (#proof-requires-validation entry (#parameter-of [[malformed-function|check-user]] [[malformed-parameter|user]] extra) (#parameter-of action input)))
      (#theorem legacy
        (#proof-requires-validation entry ([[legacy-function|check-user]] [[legacy-parameter|user]]) (#parameter-of action input)))
      (#theorem missing-marker
        (#proof-requires-validation entry ([[bare-marker|parameter-of]] [[bare-function|check-user]] [[bare-parameter|user]]) (#parameter-of action input)))
      "#,
        &[(
            "validation.lim",
            r#"
      (#fn [[validator|validate]] (([[validated|user]] (#ref #u64))) #bool (#return true))
      (#fn [[action|perform]] (([[acted|input]] (#ref #u64))) () (#return ()))
      "#,
        )],
        &[
            ("keyword", &[]),
            ("validator-marker", &[]),
            ("action-marker", &[]),
            ("entry-use", &["entry"]),
            ("validator-use", &["validator"]),
            ("validator-parameter", &["validated"]),
            ("action-use", &["action"]),
            ("action-parameter", &["acted"]),
            ("missing-parameter", &[]),
            ("wrong-function-parameter", &[]),
            ("not-a-function", &[]),
            ("malformed-function", &[]),
            ("malformed-parameter", &[]),
            ("legacy-function", &[]),
            ("legacy-parameter", &[]),
            ("bare-marker", &[]),
            ("bare-function", &[]),
            ("bare-parameter", &[]),
        ],
    );
}

#[test]
fn proof_using_navigates_contract_theorem_references_and_keeps_body_scope() {
    run_files(
        r#"
      (#alias imported-law = ./contracts.lim::remote-law)
      (#theorem [[local-declaration|local-law]] (#proof-eq true true))
      (#theorem dependent
        (#proof-using ([[imported-use|imported-law]] [[local-use|local-law]])
          (#proof-for-all (: [[body-binder|x]] #u8)
            (#proof-eq [[body-use|x]] [[body-again|x]]))))
      (#theorem empty-dependencies
        (#proof-using () (#proof-eq [[empty-body|unknown-empty-body]] true)))
    "#,
        &[(
            "contracts.lim",
            "(#theorem [[remote-declaration|remote-law]] (#proof-eq true true))",
        )],
        &[
            ("imported-use", &["remote-declaration"]),
            ("local-use", &["local-declaration"]),
            ("body-binder", &["body-binder"]),
            ("body-use", &["body-binder"]),
            ("body-again", &["body-binder"]),
            ("empty-body", &[]),
        ],
    );
}

#[test]
fn validation_selector_markers_are_contextual_and_do_not_bind_parameters() {
    run(
        r#"
      (#fn [[named-function|parameter-of]] (([[named-parameter|parameter-of]] (#ref #u64))) #bool (#return true))
      (#const not-function #u64 0u64)
      (#fn [[action|perform]] (([[action-parameter|user]] (#ref #u64))) () (#return ()))
      (#fn [[entry|entry]] ((input (#ref #u64))) () (#return ()))
      (#fn ordinary (([[ordinary-parameter|parameter-of]] (#ref #u64))) #bool
        (#return (#call [[ordinary-function|parameter-of]] (: [[ordinary-label|parameter-of]] [[ordinary-value|parameter-of]]))))
      (#theorem selected
        (#proof-and
          (#proof-requires-validation [[entry-use|entry]]
            (#[[marker|parameter-of]] [[function-use|parameter-of]] [[parameter-use|parameter-of]])
            (#parameter-of [[action-use|perform]] [[action-parameter-use|user]]))
          (#proof-eq [[no-binding|user]] 0u64)))
      (#theorem qualified
        (#proof-requires-validation entry
          (#parameter-of [[qualified-function|@parameter-of]] parameter-of)
          (#parameter-of perform user)))
      (#theorem legacy
        (#proof-requires-validation entry
          ([[legacy-function|@parameter-of]] [[legacy-parameter|parameter-of]])
          (#parameter-of perform user)))
      (#theorem short
        (#proof-requires-validation entry
          (#[[short-marker|parameter-of]] [[short-function|@parameter-of]])
          (#parameter-of perform user)))
      (#theorem bare
        (#proof-requires-validation entry
          ([[bare-marker|parameter-of]] [[bare-function|@parameter-of]] [[bare-parameter|parameter-of]])
          (#parameter-of perform user)))
      (#theorem wrong-kind
        (#proof-requires-validation entry
          (#parameter-of [[qualified-nonfunction|@not-function]] user)
          (#parameter-of perform user)))
      (#theorem wrong-parameter
        (#proof-requires-validation entry
          (#parameter-of parameter-of [[qualified-parameter|@parameter-of]])
          (#parameter-of perform user)))
      (#theorem long
        (#proof-requires-validation entry
          (#parameter-of [[long-function|@parameter-of]] [[long-parameter|parameter-of]] extra)
          (#parameter-of perform user)))
    "#,
        &[
            ("ordinary-function", &["named-function"]),
            ("ordinary-label", &["named-parameter"]),
            ("ordinary-value", &["ordinary-parameter"]),
            ("entry-use", &["entry"]),
            ("marker", &[]),
            ("function-use", &["named-function"]),
            ("parameter-use", &["named-parameter"]),
            ("action-use", &["action"]),
            ("action-parameter-use", &["action-parameter"]),
            ("no-binding", &[]),
            ("qualified-function", &["named-function"]),
            ("legacy-function", &[]),
            ("legacy-parameter", &[]),
            ("short-marker", &[]),
            ("short-function", &[]),
            ("bare-marker", &[]),
            ("bare-function", &[]),
            ("bare-parameter", &[]),
            ("qualified-nonfunction", &[]),
            ("qualified-parameter", &[]),
            ("long-function", &[]),
            ("long-parameter", &[]),
        ],
    );
}

#[test]
fn proof_names_and_function_operands_have_distinct_declaration_roles() {
    run(
        r#"
      (#fn [[f|first]] () #u64 (#return 0u64))
      (#fn [[g|second]] () #u64 (#return 0u64))
      (#fn [[h|third]] () #u64 (#return 0u64))
      (#[[keyword|theorem]] [[theorem|order]]
        (#proof-and
          (#proof-calls-directly [[direct-f|first]] [[direct-g|second]])
          (#proof-calls-transitively [[trans-f|first]] [[trans-g|third]])
          (#proof-calls-before [[before-f|first]] [[before-g|second]] [[before-h|third]])
          (#proof-calls-when [[when-f|first]] [[when-g|second]] [[boolean|false]] [[when-h|third]])
          (#proof-no-effects [[effects|first]] (#proof-allocation #proof-io #proof-global-write #proof-unsafe #proof-external #proof-asm #proof-mutation))
          (#proof-only-unsafe [[unsafe-f|first]] (#[[operation|ptr-read]]))
          (#proof-stack-at-most [[stack-f|first]] [[abi|"x86_64-sysv"]] [[limit|32]])
          (#proof-not (#proof-or (#proof-eq 0u64 0u64) (#proof-implies (#proof-eq 0u64 0u64) (#proof-eq 0u64 0u64))))))
    "#,
        &[
            ("theorem", &["theorem"]),
            ("keyword", &[]),
            ("direct-f", &["f"]),
            ("direct-g", &["g"]),
            ("trans-f", &["f"]),
            ("trans-g", &["h"]),
            ("before-f", &["f"]),
            ("before-g", &["g"]),
            ("before-h", &["h"]),
            ("when-f", &["f"]),
            ("when-g", &["g"]),
            ("when-h", &["h"]),
            ("effects", &["f"]),
            ("unsafe-f", &["f"]),
            ("stack-f", &["f"]),
            ("boolean", &[]),
            ("operation", &[]),
            ("abi", &[]),
            ("limit", &[]),
        ],
    );
}

#[test]
fn quantifiers_bind_types_and_values_without_leaking_between_propositions() {
    run(
        r#"
      (#type [[number|Number]] #u64)
      (#fn [[comparator|compare]] (: a #u64 : b #u64) #bool (#return true))
      (#theorem quantified
        (#proof-and
          (#proof-for-all (: [[binder|x]] [[type|Number]] : [[other|y]] #u64)
            (#proof-and
              (#proof-eq [[x-use|x]] [[y-use|y]])
              (#proof-no-overflow #[[operator|u64::add-wrap]] [[add-x|x]] [[add-y|y]])
              (#proof-eq (#proof-old [[old|x]]) (#proof-result [[result|y]]))
              (#proof-loop-limit [[bound|8]] (#proof-eq [[bounded|x]] y))
              (#proof-for-all (: [[inner|z]] #u64) (#proof-eq [[inner-use|z]] [[outer-use|x]]))))
          (#proof-eq [[leaked|x]] [[nested-leak|z]])))
      (#theorem arrays (#proof-for-all (: [[array|items]] (#array #u64 2))
        (#proof-and (#proof-sorted [[sorted|items]] [[compare-use|compare]])
          (#proof-permutation [[left|items]] [[right|items]])
          (#proof-unique [[unique|items]]))))
    "#,
        &[
            ("type", &["number"]),
            ("binder", &["binder"]),
            ("x-use", &["binder"]),
            ("y-use", &["other"]),
            ("add-x", &["binder"]),
            ("add-y", &["other"]),
            ("old", &["binder"]),
            ("result", &["other"]),
            ("bounded", &["binder"]),
            ("inner-use", &["inner"]),
            ("outer-use", &["binder"]),
            ("leaked", &[]),
            ("nested-leak", &[]),
            ("operator", &[]),
            ("bound", &[]),
            ("sorted", &["array"]),
            ("unique", &["array"]),
            ("compare-use", &["comparator"]),
            ("left", &["array"]),
            ("right", &["array"]),
        ],
    );
}

#[test]
fn contract_predicates_reuse_runtime_fields_and_named_argument_roles() {
    run(
        r#"
      (#struct [[row|Row]] () (: [[field|value]] #u64))
      (#fn [[f|subject]] (: [[param|input]] Row) #u64 (#return (#get input value)))
      (#fn [[helper|helper]] (: [[arg|value]] #u64) #u64 (#return value))
      (#fn value () #u64 (#return 0u64))
      (#fn missing () #u64 (#return 0u64))
      (#theorem contract
        (#proof-contract [[function|subject]]
          (#proof-eq (#get [[receiver|input]] [[member|value]])
            (#call [[callee|helper]] (: [[named|value]] (#get input [[missing-field|missing]]))))
          (#proof-eq (#proof-result) (#proof-old (#get [[post-param|input]] value)))))
      (#theorem outside (#proof-eq [[leak|input]] 0u64))
    "#,
        &[
            ("function", &["f"]),
            ("receiver", &["param"]),
            ("member", &["field"]),
            ("callee", &["helper"]),
            ("named", &["arg"]),
            ("missing-field", &[]),
            ("post-param", &["param"]),
            ("leak", &[]),
        ],
    );
}

#[test]
fn invariants_use_only_the_selected_functions_scope_at_its_label() {
    run(
        r#"
      (#fn [[function|work]] (: [[param|input]] #u64) #u64
        (#block (#let [[hidden|hidden]] #u64 0u64))
        (#let [[local|count]] #u64 input)
        (#label [[label|again]] (#loop (#break ())))
        (#let [[later|later]] #u64 0u64)
        (#return input))
      (#fn other (: input #u64) #u64
        (#let count #u64 input) (#label again (#loop (#break ()))) (#return input))
      (#fn ghost () #u64 (#return 0u64))
      (#theorem invariant
        (#proof-with-invariants
          (([[selected|work]] [[loop-use|again]]
            (#proof-eq [[invariant-param|input]] [[invariant-local|count]])
            (#u64::sub-wrap [[rank|count]] 0u64)))
          (#proof-eq [[local-leak|count]] [[param-leak|input]])))
      (#theorem hidden-check (#proof-with-invariants
        ((work again (#proof-eq [[hidden-use|hidden]] [[later-use|later]]) 0u64))
        (#proof-eq 0u64 0u64)))
      (#theorem label-check (#proof-with-invariants
        ((work [[unknown-label|ghost]] (#proof-eq 0u64 0u64) 0u64))
        (#proof-eq 0u64 0u64)))
    "#,
        &[
            ("selected", &["function"]),
            ("loop-use", &["label"]),
            ("invariant-param", &["param"]),
            ("invariant-local", &["local"]),
            ("rank", &["local"]),
            ("local-leak", &[]),
            ("param-leak", &[]),
            ("hidden-use", &[]),
            ("later-use", &[]),
            ("unknown-label", &[]),
        ],
    );
}

#[test]
fn trace_claims_inside_invariants_keep_function_parameter_and_loop_roles() {
    run(
        r#"
      (#fn [[validator|validate]] (: [[subject|user]] (#ref #u8)) #bool (#return true))
      (#fn [[action|perform]] (: [[argument|input]] (#ref #u8)) () (#return ()))
      (#fn [[entry|process]] (: [[count|count]] #u8 : user (#ref #u8)) ()
        (#let-mut [[remaining|remaining]] #u8 count)
        (#label [[label|again]] (#while (#u8::gt remaining 0u8)
          (#if (#call validate (: user user)) (#call perform (: input user)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim (#proof-loop-limit 1
        (#proof-with-invariants
          (([[loop-function|process]] [[loop-label|again]]
            (#u8::le [[predicate|remaining]] [[bound|count]]) [[rank|remaining]]))
          (#proof-requires-validation [[trace-entry|process]]
            (#parameter-of [[trace-validator|validate]] [[trace-subject|user]])
            (#parameter-of [[trace-action|perform]] [[trace-argument|input]])))))
    "#,
        &[
            ("loop-function", &["entry"]),
            ("loop-label", &["label"]),
            ("predicate", &["remaining"]),
            ("bound", &["count"]),
            ("rank", &["remaining"]),
            ("trace-entry", &["entry"]),
            ("trace-validator", &["validator"]),
            ("trace-subject", &["subject"]),
            ("trace-action", &["action"]),
            ("trace-argument", &["argument"]),
        ],
    );
}

#[test]
fn collection_invariants_resolve_views_bounds_and_comparator_metadata() {
    run(
        r#"
      (#fn [[comparator|less]] (: left #u8 : right #u8) #bool (#return (#u8::lt left right)))
      (#fn [[entry|work]] (: [[source|values]] (#ref-mut (#array #u8 3)) : [[bound|end]] #usize) ()
        (#let [[original|original]] (#array #u8 3) (#deref values))
        (#let [[collision|less]] #u8 0u8)
        (#let-mut [[remaining|remaining]] #usize end)
        (#label [[label|again]] (#while (#usize::gt remaining 0usize)
          (#set remaining (#usize::sub-wrap remaining 1usize))))
        (#return ()))
      (#theorem claim (#proof-with-invariants
        (([[function-use|work]] [[label-use|again]]
          (#proof-and
            (#proof-unique (#borrow-slice (#deref [[unique-source|values]]) 0usize [[range-end|end]]))
            (#proof-permutation (#deref [[left-source|values]]) [[right-source|original]])
            (#proof-sorted (#deref [[sorted-source|values]]) [[comparator-use|less]]))
          [[rank|remaining]]))
        (#proof-eq [[leaked|remaining]] 0usize)))
    "#,
        &[
            ("function-use", &["entry"]),
            ("label-use", &["label"]),
            ("unique-source", &["source"]),
            ("range-end", &["bound"]),
            ("left-source", &["source"]),
            ("right-source", &["original"]),
            ("sorted-source", &["source"]),
            ("comparator-use", &["comparator"]),
            ("rank", &["remaining"]),
            ("leaked", &[]),
        ],
    );
}

#[test]
fn proof_validated_resolves_descriptor_and_invariant_scope_without_leaks() {
    run(
        r#"
      (#fn [[validator|validate]] (: [[subject|user]] (#ref #u8)) #bool (#return true))
      (#fn [[action|perform]] (: input (#ref #u8)) () (#return ()))
      (#fn [[unrelated|absent]] () () (#return ()))
      (#fn [[entry|process]] (: [[argument|user]] (#ref #u8) : count #u8) ()
        (#let checked #bool false)
        (#let-mut remaining #u8 count)
        (#label [[label|again]] (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim (#proof-with-invariants
        ((process again (#proof-implies checked
          (#proof-validated (#parameter-of [[descriptor-function|validate]] [[descriptor-parameter|user]]) [[object|user]])) remaining))
        (#proof-requires-validation process
          (#parameter-of validate user)
          (#parameter-of perform input))))
      (#theorem invalid (#proof-with-invariants
        ((process again (#proof-validated ([[bad-marker|parameter-of]] validate user) [[malformed-object|user]]) remaining))
        (#proof-requires-validation process
          (#parameter-of missing user) (#parameter-of perform input))))
      (#theorem unknown (#proof-with-invariants
        ((process again (#proof-validated (#parameter-of validate [[unknown-parameter|absent]]) [[unknown-object|user]]) remaining))
        (#proof-requires-validation process
          (#parameter-of validate user) (#parameter-of perform input))))
      (#theorem no-leak (#proof-eq [[leaked-object|user]] 0u8))
      (#theorem qualified (#proof-with-invariants
        ((process again (#proof-validated (#parameter-of [[qualified-function|@validate]] [[qualified-parameter|user]]) user) remaining))
        (#proof-requires-validation process (#parameter-of validate user) (#parameter-of perform input))))
      (#theorem bad-qualified (#proof-with-invariants
        ((process again (#proof-validated (#parameter-of validate [[qualified-bad-parameter|@absent]]) user) remaining))
        (#proof-requires-validation process (#parameter-of validate user) (#parameter-of perform input))))
    "#,
        &[
            ("descriptor-function", &["validator"]),
            ("descriptor-parameter", &["subject"]),
            ("object", &["argument"]),
            ("bad-marker", &[]),
            ("malformed-object", &["argument"]),
            ("unknown-parameter", &[]),
            ("unknown-object", &["argument"]),
            ("leaked-object", &[]),
            ("qualified-function", &["validator"]),
            ("qualified-parameter", &["subject"]),
            ("qualified-bad-parameter", &[]),
        ],
    );
}

#[test]
fn proof_metadata_never_becomes_a_global_reference() {
    let forms = [
        "proof-and",
        "proof-or",
        "proof-not",
        "proof-implies",
        "proof-calls-directly",
        "proof-calls-transitively",
        "proof-calls-before",
        "proof-calls-when",
        "proof-no-effects",
        "proof-only-unsafe",
        "proof-stack-at-most",
        "proof-for-all",
        "proof-eq",
        "proof-contract",
        "proof-result",
        "proof-old",
        "proof-no-overflow",
        "proof-with-invariants",
        "proof-loop-limit",
        "proof-sorted",
        "proof-permutation",
        "proof-unique",
        "proof-allocation",
        "proof-io",
        "proof-global-write",
        "proof-unsafe",
        "proof-external",
        "proof-asm",
        "proof-mutation",
    ];
    for form in forms {
        run(
            &format!("(#fn {form} () #u64 (#return 0u64)) (#theorem test (#[[keyword|{form}]]))"),
            &[("keyword", &[])],
        );
    }
    run(
        r#"
      (#fn [[operation-function|ptr-read]] () #u64 (#return 0u64))
      (#fn [[f|work]] () #u64 (#return 0u64))
      (#theorem metadata (#proof-only-unsafe work ([[unprefixed|ptr-read]] #[[builtin|ptr-read]])))
      (#theorem invalid-function (#proof-calls-directly [[wrong|metadata]] [[right|work]]))
    "#,
        &[
            ("unprefixed", &["operation-function"]),
            ("builtin", &[]),
            ("wrong", &[]),
            ("right", &["f"]),
        ],
    );
}

#[test]
fn unsafe_allowlist_function_entries_ignore_lexical_values_and_nonfunctions() {
    run(
        r#"
      (#fn [[function|trusted]] () #u64 (#return 0u64))
      (#fn work () #u64 (#return 0u64))
      (#struct Record () (: value #u64))
      (#theorem editing (#proof-for-all (: trusted #u64 : only-local #u64)
        (#proof-only-unsafe work
          ([[boundary|trusted]] [[local|only-local]] [[record|Record]]
           [[unknown|missing]] #[[builtin|ptr-read]]))))
    "#,
        &[
            ("boundary", &["function"]),
            ("local", &[]),
            ("record", &[]),
            ("unknown", &[]),
            ("builtin", &[]),
        ],
    );
}

#[test]
fn unsafe_allowlist_aliases_and_file_references_reach_original_functions() {
    run_files(
        r#"
      (#alias boundary = ./facade.lim::forward)
      (#fn trusted () #u64 (#return 0u64))
      (#fn work () #u64 (#return 0u64))
      (#theorem allowed (#proof-only-unsafe work
        ([[alias|boundary]] [[path|./library.lim::trusted]] #[[builtin|ptr-read]])))
    "#,
        &[
            (
                "library.lim",
                "(#fn [[original|trusted]] () #u64 (#return 0u64))",
            ),
            ("facade.lim", "(#alias forward = ./library.lim::trusted)"),
        ],
        &[
            ("alias", &["original"]),
            ("path", &["original"]),
            ("builtin", &[]),
        ],
    );
}

#[test]
fn proof_function_aliases_and_contract_parameters_reach_the_original_file() {
    run_files(
        r#"
      (#alias facade = ./facade.lim::forward)
      (#fn subject (: input #u64) #u64 (#return input))
      (#theorem direct (#proof-calls-directly [[alias-use|facade]] [[path-use|./library.lim::subject]]))
      (#theorem contract (#proof-contract [[contract-function|facade]]
        (#proof-eq [[pre|input]] input) (#proof-eq (#proof-result) [[post|input]])))
    "#,
        &[
            (
                "library.lim",
                "(#fn [[original|subject]] (: [[original-param|input]] #u64) #u64 (#return input))",
            ),
            ("facade.lim", "(#alias forward = ./library.lim::subject)"),
        ],
        &[
            ("alias-use", &["original"]),
            ("path-use", &["original"]),
            ("contract-function", &["original"]),
            ("pre", &["original-param"]),
            ("post", &["original-param"]),
        ],
    );
}

#[test]
fn generated_function_operands_reach_the_emitted_declaration() {
    run(
        r#"
      (#gn emit () `((#fn leaf () #u64 (#return 0u64))
                    (#fn emitted () #u64 (#return (#call leaf ())))
                    (#theorem generated (#proof-calls-directly emitted leaf))))
      (#generate emit)
      (#theorem source (#proof-calls-transitively [[generated-use|emitted]] leaf))
      (#theorem boundary (#proof-only-unsafe emitted ([[generated-allowed|leaf]])))
    "#,
        &[
            ("generated-use", &["generated:emitted"]),
            ("generated-allowed", &["generated:leaf"]),
        ],
    );
}

#[test]
fn generated_fresh_names_use_the_final_file_scope() {
    run_files(r#"
      (#alias emit = ./generator.lim::emit)
      (#generate emit)
      (#theorem imported (#proof-calls-directly [[use|provided]] provided-leaf))
    "#, &[("generator.lim", "(#gn emit () `((#fn provided-leaf () #u64 (#return 0u64)) (#fn provided () #u64 (#return (#call provided-leaf ()))) (#theorem generated (#proof-calls-directly provided provided-leaf))))")],
    &[("use", &["generated:provided"])]);
}

#[test]
fn contract_result_and_old_wrappers_preserve_member_types() {
    run(
        r#"
      (#struct Row () (: [[field|value]] #u64))
      (#fn [[function|identity]] (: [[param|input]] Row) Row (#return input))
      (#theorem preserves (#proof-contract [[subject|identity]]
        (#proof-eq (#get (#proof-old [[old-input|input]]) [[old-field|value]]) 0u64)
        (#proof-eq (#get (#proof-result) [[result-field|value]]) (#get input value))))
    "#,
        &[
            ("subject", &["function"]),
            ("old-input", &["param"]),
            ("old-field", &["field"]),
            ("result-field", &["field"]),
        ],
    );
}

#[test]
fn enum_patterns_in_loop_invariants_keep_variant_and_payload_binding_scopes() {
    run(
        r#"
      (#enum Maybe () (: [[none|Maybe.None]] : [[some|Maybe.Some]] (#ref #u8)))
      (#fn populate (: [[target|target]] (#ref-mut Maybe) : alternate (#ref #u8) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#deref-set target (#enum-literal Maybe.Some alternate))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim (#proof-with-invariants
        ((populate again
          (#match (#deref [[receiver|target]])
            (#case ([[variant|Maybe.Some]] [[binding|value]]) (#u8::eq (#deref [[use|value]]) (#deref value)))
            (#case [[other|Maybe.None]] true)) remaining))
        (#proof-contract populate true true)))
    "#,
        &[
            ("receiver", &["target"]),
            ("variant", &["some"]),
            ("other", &["none"]),
            ("use", &["binding"]),
        ],
    );
}

#[test]
fn invariants_preserve_loop_body_and_branch_binding_lifetimes() {
    run(
        r#"
      (#fn work (: [[param|input]] #u64) #u64
        (#while true
          (#let [[local|counter]] #u64 input)
          (#label [[label|inside]] (#loop (#break ()))))
        (#label [[outer|outside]] (#loop (#break ())))
        (#return input))
      (#theorem inner (#proof-with-invariants
        ((work [[inside-use|inside]] (#proof-eq [[counter-use|counter]] [[input-use|input]]) 0u64))
        (#proof-eq 0u64 0u64)))
      (#theorem outer (#proof-with-invariants
        ((work [[outside-use|outside]] (#proof-eq [[counter-leak|counter]] input) 0u64))
        (#proof-eq 0u64 0u64)))
    "#,
        &[
            ("inside-use", &["label"]),
            ("counter-use", &["local"]),
            ("input-use", &["param"]),
            ("outside-use", &["outer"]),
            ("counter-leak", &[]),
        ],
    );
}

#[test]
fn imported_invariant_bindings_reach_actual_function_locals() {
    run_files(
        r#"
      (#alias selected = ./library.lim::work)
      (#fn work (: input #u64) #u64 (#return input))
      (#theorem imported (#proof-with-invariants
        (([[function-use|selected]] [[label-use|again]]
          (#proof-eq [[param-use|input]] [[local-use|remaining]]) [[rank-use|remaining]]))
        (#proof-eq 0u64 0u64)))
    "#,
        &[(
            "library.lim",
            r#"
      (#fn [[function|work]] (: [[param|input]] #u64) #u64
        (#let [[local|remaining]] #u64 input)
        (#label [[label|again]] (#loop (#break ())))
        (#return input))
    "#,
        )],
        &[
            ("function-use", &["function"]),
            ("label-use", &["label"]),
            ("param-use", &["param"]),
            ("local-use", &["local"]),
            ("rank-use", &["local"]),
        ],
    );
}

#[test]
fn ambiguous_invariant_labels_and_unknown_argument_labels_fail_closed() {
    run(
        r#"
      (#fn work (: input #u64) #u64
        (#block (#label duplicate (#loop (#break ()))))
        (#block (#label duplicate (#loop (#break ()))))
        (#return input))
      (#fn ghost () #u64 (#return 0u64))
      (#theorem ambiguous (#proof-with-invariants
        ((work [[ambiguous|duplicate]] (#proof-eq [[unresolved|input]] 0u64) 0u64))
        (#proof-eq 0u64 0u64)))
      (#theorem arguments (#proof-eq (#call work (: [[missing|ghost]] 0u64)) 0u64))
    "#,
        &[("ambiguous", &[]), ("unresolved", &[]), ("missing", &[])],
    );
}
