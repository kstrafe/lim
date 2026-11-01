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
          (#proof-permutation [[left|items]] [[right|items]]))))
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
