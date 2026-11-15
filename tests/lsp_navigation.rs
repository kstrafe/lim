mod support;

#[test]
fn conditional_records_keep_value_roles_and_distinct_branch_scopes() {
    let source = r#"
#fn [[identity|identity]] {
  #params = { [[parameter|value]] = #u64; };
  #returns = #u64;
  #body: #return value;
}
#fn choose {
  #params = { [[flag|flag]] = #bool; [[input|input]] = #u64; };
  #returns = #u64;
  #body:
    #let result #u64 (#[[if|if]] {
      [[else-marker|#else]] = (#block
        (#let [[else-local|branch]] #u64 [[else-input|input]])
        ([[else-callee|identity]] { [[else-label|value]] = [[else-use|branch]]; }));
      [[condition-marker|#condition]] [[equal|=]] [[condition-use|flag]];
      [[then-marker|#then]][[colon|:]]
        #let [[then-local|branch]] #u64 [[then-input|input]];
        [[then-callee|identity]] { [[then-label|value]] = [[then-use|branch]]; };
    });
    #return [[after|input]];
}
"#;
    for source in [source.to_owned(), source.replace("#[[if|if]]", "#[[if|if-valid]]")] {
        run(&source, &[
            ("if", &[]), ("condition-marker", &[]), ("then-marker", &[]),
            ("else-marker", &[]), ("equal", &[]), ("colon", &[]),
            ("condition-use", &["flag"]),
            ("then-input", &["input"]), ("else-input", &["input"]),
            ("then-use", &["then-local"]), ("else-use", &["else-local"]),
            ("then-callee", &["identity"]), ("else-callee", &["identity"]),
            ("then-label", &["parameter"]), ("else-label", &["parameter"]),
            ("after", &["input"]),
        ]);
    }
}

#[test]
fn conditional_branches_do_not_expose_initializers_sibling_or_following_locals() {
    run(r#"
#fn choose {
  #params = { [[flag|flag]] = #bool; };
  #returns = #u64;
  #body:
    #let result #u64 (#if {
      #condition = [[condition|flag]];
      #then:
        #let [[local|branch]] #u64 [[initializer|branch]];
        [[then-use|branch]];
      #else = [[sibling|branch]];
    });
    #return [[after|branch]];
}
"#, &[
        ("condition", &["flag"]), ("initializer", &[]),
        ("then-use", &["local"]), ("sibling", &[]), ("after", &[]),
    ]);
}

#[test]
fn conditional_data_is_inert_and_async_function_input_retains_lexical_roles() {
    run(r#"
#fn [[runtime|input]] { #params = {}; #returns = #u64; #body: #return 42u64; }
#gn emit { payload; } `()
#generate emit { payload = (#if {
  [[marker|#condition]] = [[condition-data|input]];
  #then = [[then-data|input]];
  #else = [[else-data|input]];
}); }
#generate #async-fn {
  protocol = WorkAwait;
  waker = #u64;
  function = (#fn work (([[flag|flag]] #bool) ([[parameter|value]] #u64)) #u64
    (#return (#if {
      [[async-marker|#condition]] = [[condition-use|flag]];
      #then: [[then-use|value]];
      #else = [[else-use|value]];
    })));
}
"#, &[
        ("marker", &[]), ("condition-data", &[]),
        ("then-data", &[]), ("else-data", &[]), ("async-marker", &[]),
        ("condition-use", &["flag"]),
        ("then-use", &["parameter"]), ("else-use", &["parameter"]),
    ]);
}

#[test]
fn positional_calls_and_arg_resolve_to_their_explicit_signature() {
    run(
        "#type [[type|Number]] #u64\n#fn [[function|increment]] {\n  #params = [[parameter|Number]];\n  #returns = Number;\n  #body: #return [#u64 #wrap; [[arg-use|#arg]] + 1u64];\n}\n#fn view {\n #params = (#[[ref-key|ref]] [[ref-type|Number]]);\n #returns = Number;\n #body: #return (#deref #arg);\n}\n#fn main {\n #params = {}; #returns = #u64;\n #body:\n   #let [[local|input]] #u64 41u64;\n   #return ([[callee|increment]] [[operand|input]]);\n}",
        &[("arg-use", &["parameter"]), ("parameter", &["type"]),
          ("ref-key", &[]), ("ref-type", &["type"]),
          ("callee", &["function"]), ("operand", &["local"])],
    );
}

#[test]
fn generic_colon_groups_keep_callees_labels_and_values_navigable() {
    run(
        "#fn [[function|identity]] {
          #params = { [[parameter|value]] = #u64; };
          #returns = #u64;
          #body: #return [[parameter-use|value]];
        }
#fn main {
          #params = {}; #returns = #u64;
          #body:
            #let [[binding|input]] #u64 42;
            #return [[outer-colon|:]] [[callee|identity]] [[args-colon|:]] [[pair-colon|:]] [[label|value]] [[argument|input]];
        }",
        &[
            ("parameter-use", &["parameter"]),
            ("outer-colon", &[]), ("args-colon", &[]), ("pair-colon", &[]),
            ("callee", &["function"]), ("label", &["parameter"]),
            ("argument", &["binding"]),
        ],
    );
}

#[test]
fn indented_statement_headers_keep_loop_scopes_and_call_labels() {
    run(
        "#fn [[function|identity]] {
          #params = { [[parameter|value]] = #u64; };
          #returns = #u64;
          #body:
            #return value;
        }
#fn main {
          #params = {}; #returns = #u64;
          #body:
            #let-mut [[total|total]] #u64 0;
            #[[loop|for-range]] ([[index|index]] #u64) 1 11[[colon|:]]
              #set [[set-use|total]] [#u64 #wrap; [[total-use|total]] +
                ([[call|identity]] (([[label|value]] [[argument|index]])))];
            #return [[after-loop|total]];
        }",
        &[
            ("loop", &[]),
            ("colon", &[]),
            ("set-use", &["total"]),
            ("total-use", &["total"]),
            ("call", &["function"]),
            ("label", &["parameter"]),
            ("argument", &["index"]),
            ("after-loop", &["total"]),
        ],
    );
}

#[test]
fn function_records_layout_calls_and_infix_keep_exact_source_roles() {
    run(
        "#fn [[function|identity]] {
          #[[params-key|params]] = { [[binding|value]] = #u64; };
          #[[returns-key|returns]] = #u64;
          #[[requires-key|requires]][[requires-colon|:]]
            [#u64; [[require-use|value]] [[operator|<]] 100];
          #[[body-key|body]][[body-colon|:]]
            #return [[body-use|value]];
        }
#fn main {
          #params = {}; #returns = #u64;
          #body = (
            #let [[input|input]] #u64 42;
            #assume [#u64; [[assume-use|input]] < 100];
            #return [[call|identity]] { [[label|value]] = [[argument|input]]; };
          );
        }",
        &[
            ("params-key", &[]),
            ("returns-key", &[]),
            ("requires-key", &[]),
            ("requires-colon", &[]),
            ("body-key", &[]),
            ("body-colon", &[]),
            ("require-use", &["binding"]),
            ("operator", &[]),
            ("body-use", &["binding"]),
            ("assume-use", &["input"]),
            ("call", &["function"]),
            ("label", &["binding"]),
            ("argument", &["input"]),
        ],
    );
}

#[test]
fn array_generator_inputs_are_literal_data() {
    run(
        "#struct Row () ((value #u64))
#generate #[[generator|array]]
             (([[element-label|element]] [[element|Row]]) ([[length-label|length]] [[length|4]]) ([[name-label|name]] [[name|Rows]]))\n",
        &[("generator", &[]), ("element-label", &[]), ("element", &[]), ("length-label", &[]), ("length", &[]), ("name-label", &[]), ("name", &[])],
    );
}

#[test]
fn callable_intrinsic_operands_navigate_but_builtin_labels_do_not() {
    run(
        "#fn use {
  #params = (([[left|index]] #usize) ([[right|bound]] #usize));
  #returns = #bool;
  #body = (
            (#return (#[[call|call]] #[[intrinsic|usize::lt]]
              (([[label-left|left]] [[left-use|index]]) ([[label-right|right]] [[right-use|bound]]))))\n  );\n}\n",
        &[("call", &[]), ("intrinsic", &[]), ("label-left", &[]), ("label-right", &[]), ("left-use", &["left"]), ("right-use", &["right"])],
    );
}

#[test]
fn proven_index_has_value_operands_and_no_keyword_definition() {
    run(
        "#struct Item () (([[field|value]] #u64))
#fn read {
  #params = (([[array|values]] (#ref (#array Item 4))) ([[index|position]] #usize));
  #returns = #u64;
  #body = (
             (#requires (#usize::lt [[bound-index|position]] 4usize))
             (#return (#get (#[[keyword|index-proven]] [[array-use|values]] [[index-use|position]]) [[field-use|value]]))
  );
}
",
        &[("keyword", &[]), ("bound-index", &["index"]), ("array-use", &["array"]), ("index-use", &["index"]), ("field-use", &["field"])],
    );
}

#[test]
fn call_graph_has_no_user_definition_or_arguments() {
    run(
        "#fn [[entry|main]] {
  #params = ();
  #returns = #u64;
  #body = (
        (#println (#[[trace|call-graph]]))
        (#return 42u64)
  );
}
",
        &[("entry", &["entry"]), ("trace", &[])],
    );
}

#[test]
fn generated_variant_name_operations_navigate_syntax_parameters() {
    run(
        "#gn make { [[binding|name]]; }
        (#[[operation|gn-variant]] [[argument|name]] [[literal|\"Ready\"]])
",
        &[
            ("argument", &["binding"]),
            ("operation", &[]),
            ("literal", &[]),
        ],
    );
}

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
    run_with_files(input, &[], expected);
}

fn run_with_files(
    input: &str,
    files: &[(&str, &str)],
    expected: &[(&str, &[&str])],
) {
    let scratch = support::Scratch::new("lsp-navigation");
    let uri = lsp::path_to_uri(&scratch.path().join("main.lim")).unwrap();
    let (source, marks) = annotated(input);
    let mut imported = HashMap::new();
    for (name, input) in files {
        let path = scratch.path().join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let (text, targets) = annotated(input);
        std::fs::write(&path, &text).unwrap();
        let uri = lsp::path_to_uri(&path).unwrap();
        for (label, span) in targets {
            assert!(!marks.contains_key(&label));
            assert!(imported
                .insert(label, (uri.clone(), text.clone(), span))
                .is_none());
        }
    }
    if !files.is_empty() {
        let path = scratch.path().join("main.lim");
        let program = lim::parse_program_from_path(&source, &path)
            .unwrap();
        lim::check_types(&program).unwrap();
    }
    lim::parse_source_unit(&source).unwrap();
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
            let (target_uri, text, (start, end)) = imported
                .get(*target)
                .map(|(uri, text, span)| {
                    (uri.as_str(), text.as_str(), *span)
                })
                .unwrap_or_else(|| {
                    (uri.as_str(), source.as_str(), marks[*target])
                });
            let (line, character) = lsp::byte_position(text, start);
            let (end_line, end_character) =
                lsp::byte_position(text, end);
            assert!(
                actual.iter().any(|item| {
                    let range = item.get("range").unwrap();
                    item.get("uri").and_then(Json::string)
                        == Some(target_uri)
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
fn all_value_positions_use_lexical_bindings_and_not_global_spelling() {
    run(
        r#"
#enum Choice () ((Choice.Full #u64) Choice.Empty)
#const [[limit|LIMIT]] #u64 42u64
#static [[count|COUNT]] #u64 1u64
#fn first {
  #params = (([[first-x|x]] Choice));
  #returns = #u64;
  #body = (
          (#return (#match [[match-x|x]]
            (#case (Choice.Full [[payload|value]])
              (#let-mut [[local|answer]] #u64 [[payload-use|value]])
              (#set [[set-use|answer]] (#u64::add-wrap [[arithmetic-use|answer]] [[limit-use|LIMIT]]))
              (#let ref (#ref #u64) (#borrow [[borrow-use|answer]]))
              (#forget ref)
              (#return [[return-use|answer]]))
            (#case Choice.Empty (#unsafe [[static-use|COUNT]]))))
  );
}
#fn second {
  #params = (([[second-x|x]] #u64));
  #returns = #u64;
  #body = ( (#return [[second-use|x]])
  );
}
    "#,
        &[
            ("match-x", &["first-x"]),
            ("payload-use", &["payload"]),
            ("set-use", &["local"]),
            ("arithmetic-use", &["local"]),
            ("borrow-use", &["local"]),
            ("return-use", &["local"]),
            ("limit-use", &["limit"]),
            ("static-use", &["count"]),
            ("second-use", &["second-x"]),
        ],
    );
}

#[test]
fn fields_and_argument_labels_resolve_through_their_actual_owner() {
    run(
        r#"
#struct [[left|Left]] () (([[left-value|value]] #u64))
#struct Right () (([[right-value|value]] #u64))
#type Alias (#ref Left)
#fn make {
  #params = (([[param|value]] #u64));
  #returns = Right;
  #body = (
          (#return (#struct-literal Right (([[literal-field|value]] [[param-use|value]]))))
  );
}
#fn other {
  #params = (([[other-param|value]] #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}
#fn main {
  #params = (([[owner|object]] Alias));
  #returns = #u64;
  #body = (
          (#let [[local|value]] #u64 (#get [[receiver|object]] [[left-field|value]]))
          (#let record Right (#call make (([[label|value]] [[argument|value]]))))
          (#set-field record [[set-field|value]] 2u64)
          (#let field #u64 (#get record [[right-field|value]]))
          (#call other (($ [[pun|value]])))
          (#call other (([[other-label|value]] 1u64)))
          (#return (#get (#call make ((value 0u64))) [[call-field|value]]))
  );
}
    "#,
        &[
            ("literal-field", &["right-value"]),
            ("param-use", &["param"]),
            ("receiver", &["owner"]),
            ("left-field", &["left-value"]),
            ("label", &["param"]),
            ("argument", &["local"]),
            ("set-field", &["right-value"]),
            ("right-field", &["right-value"]),
            ("pun", &["local"]),
            ("other-label", &["other-param"]),
            ("call-field", &["right-value"]),
        ],
    );
}

#[test]
fn record_pun_navigation_resolves_the_identifier_as_a_value_use() {
    run(
        r#"
#fn inspect {
  #params = (([[parameter|value]] #u64));
  #returns = #u64;
  #body = (
    #return (#call consume { [[pun|value]]; });
  );
}
#fn consume {
  #params = ((value #u64));
  #returns = #u64;
  #body = (#return value;);
}
    "#,
        &[("pun", &["parameter"])],
    );
}

#[test]
fn pattern_forms_bind_values_in_their_own_scopes_and_navigate_variants() {
    run(
        r#"
#struct Record () (([[field|value]] #u64))
#enum [[choice|Choice]] () (([[full|Choice.Full]] Record) [[empty|Choice.Empty]])
#fn inspect {
  #params = ((input Choice));
  #returns = #u64;
  #body = (
          (#let-else ([[let-variant|Choice.Full]] [[success|record]]) [[let-type|Choice]] input
            (#else [[else-variant|Choice.Empty]] (#return 0u64)))
          (#let n #u64 (#get [[success-use|record]] [[success-field|value]]))
          (#if-let ([[if-variant|Choice.Full]] [[if-bind|inside]]) Choice (Choice.Full record)
            (#block (#forget [[if-use|inside]]) ())
            (#block (#forget [[not-in-else|inside]]) ()))
          (#while-let ([[while-variant|Choice.Full]] [[while-bind|item]]) (Choice.Full record)
            (#forget [[while-use|item]]) (#break))
          (#forget [[not-after-loop|item]])
          (#return n)
  );
}
    "#,
        &[
            ("let-variant", &["full"]),
            ("let-type", &["choice"]),
            ("else-variant", &["empty"]),
            ("success-use", &["success"]),
            ("success-field", &["field"]),
            ("if-variant", &["full"]),
            ("if-use", &["if-bind"]),
            ("not-in-else", &[]),
            ("while-variant", &["full"]),
            ("while-use", &["while-bind"]),
            ("not-after-loop", &[]),
        ],
    );
}

#[test]
fn destructuring_loop_and_label_scopes_do_not_leak_or_allow_forward_uses() {
    run(
        r#"
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#forget [[forward|later]])
          (#let [[later|later]] #u64 1u64)
          (#let (#tuple [[first|a]] [[second|b]]) (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) 1u64 2u64))
          (#forget [[tuple-use|b]])
          (#block (#let [[block|inner]] #u64 1u64) (#forget [[block-use|inner]]))
          (#forget [[block-leak|inner]])
          (#label [[label|outer]]
            (#for (#let-mut [[index|i]] #usize 0usize) (#usize::lt [[condition|i]] 3usize)
              (#set [[step|i]] (#usize::add-wrap i 1usize))
              (#continue-to [[continue|outer]]) (#break-to [[break|outer]])))
          (#forget [[loop-leak|i]])
          (#for-range ([[range|j]] #usize) 0usize 3usize (#forget [[range-use|j]]))
          (#forget [[range-leak|j]])
          (#if true (#let [[yes|branch]] #u64 0u64) (#forget [[else-leak|branch]]))
          (#return [[first-use|a]])
  );
}
    "#,
        &[
            ("forward", &[]),
            ("tuple-use", &["second"]),
            ("block-use", &["block"]),
            ("block-leak", &[]),
            ("condition", &["index"]),
            ("step", &["index"]),
            ("continue", &["label"]),
            ("break", &["label"]),
            ("loop-leak", &[]),
            ("range-use", &["range"]),
            ("range-leak", &[]),
            ("else-leak", &[]),
            ("first-use", &["first"]),
        ],
    );
}

#[test]
fn explicit_type_positions_and_variant_operations_navigate() {
    run(
        r#"
#struct [[record|Record]] () (([[field|value]] #u64))
#type [[alias|Number]] #u64
#enum Choice () (([[full|Choice.Full]] Record) Choice.Empty)
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let r Record (#struct-literal [[literal|Record]] ((value 42u64))))
          (#let size #usize (#size-of [[size|Record]]))
          (#let align #usize (#align-of [[align|Record]]))
          (#let offset #usize (#offset-of [[offset-type|Record]] [[offset-field|value]]))
          (#let n Number (#as 42u64 [[cast|Number]]))
          (#let array (#array Record 1) (#array-of (#array [[array|Record]] 1) r))
          (#let pointer (#ptr Record) (#ptr-null (#ptr [[pointer|Record]])))
          (#let choice Choice ([[constructor|Choice.Full]] (#struct-literal Record ((value 42u64)))))
          (#assert (#variant-is choice [[is|Choice.Full]]))
          (#let extracted Record (#get-payload choice [[payload|Choice.Full]] 0))
          (#forget array) (#forget pointer) (#forget extracted)
          (#return n)
  );
}
    "#,
        &[
            ("literal", &["record"]),
            ("size", &["record"]),
            ("align", &["record"]),
            ("offset-type", &["record"]),
            ("offset-field", &["field"]),
            ("cast", &["alias"]),
            ("array", &["record"]),
            ("pointer", &["record"]),
            ("constructor", &["full"]),
            ("is", &["full"]),
            ("payload", &["full"]),
        ],
    );
}

#[test]
fn generators_resolve_evaluated_bindings_but_not_literal_template_symbols() {
    run(
        r#"
#gn-fn [[helper|identity]] { [[param|value]]; } [[param-use|value]]
#gn emit { [[items|items]]; }
          (#gn-for-each [[item|item]] [[items-use|items]]
            (#gn-call [[call|identity]] { value =
              `(([[literal|item]] ,[[unquoted|item]] ',[[quoted|item]])); }))
#syntax [[bundle|Protocol]] (#u64)
#fn ordinary {
  #params = (([[runtime|x]] #u64));
  #returns = #u64;
  #body = ( (#return x)
  );
}
#generate emit { items = [[argument-literal|ordinary]]; }
    "#,
        &[
            ("param-use", &["param"]),
            ("items-use", &["items"]),
            ("call", &["helper"]),
            ("literal", &[]),
            ("unquoted", &["item"]),
            ("quoted", &[]),
            ("argument-literal", &[]),
        ],
    );
}

#[test]
fn function_syntax_inside_generator_inputs_and_utf16_names_keep_local_roles() {
    run(
        r#"
#generate unknown { function =
          (#fn work { #params = (([[param|名字]] #u64)); #returns = #u64;
            #body = ((#let [[local|résultat]] #u64 [[param-use|名字]])
                     (#return [[local-use|résultat]])); }); }
    "#,
        &[("param-use", &["param"]), ("local-use", &["local"])],
    );
}

#[test]
fn or_patterns_share_one_binding_but_invalid_duplicate_lets_are_ambiguous() {
    run(
        r#"
#enum Choice () ((Choice.A #u64) (Choice.B #u64))
#fn choose {
  #params = ((input Choice));
  #returns = #u64;
  #body = (
          (#return (#match input
            (#case (#or (Choice.A [[a|value]]) (Choice.B [[b|value]])) [[use|value]])))
  );
}
#fn broken {
  #params = ();
  #returns = #u64;
  #body = (
          (#let repeated #u64 0u64)
          (#let repeated #u64 1u64)
          (#return [[duplicate|repeated]])
  );
}
    "#,
        &[("use", &["a", "b"]), ("duplicate", &[])],
    );
}

#[test]
fn syntax_bundles_and_nested_splices_have_explicit_reference_roles() {
    run(
        r#"
#syntax [[base|Base]] (#u64)
#syntax [[combined|Combined]] ((#syntax-splice [[nested|Base]]))
#fn expanded {
  #params = ();
  #returns = (#syntax-splice [[signature|Base]]);
  #body = ( (#return 42u64)
  );
}
#generate unknown { function = (#fn work {
  #params = (); #returns = #u64;
  #body = ((#let result #u64 (#await [[protocol|Combined]] child))
           (#return result));
}); }
    "#,
        &[
            ("nested", &["base"]),
            ("signature", &["base"]),
            ("protocol", &["combined"]),
        ],
    );
}

#[test]
fn raw_builtin_operands_are_values_but_register_and_cfg_names_are_metadata() {
    run(
        r#"
#enum RegisterCollision () (RegisterCollision.Rax)
#fn main {
  #params = (([[param|value]] #usize));
  #returns = #u64;
  #body = (
          (#let array (#array #usize 2) (#array-repeat [[repeat|value]]))
          (#let kernel #i64 (#unsafe (#linux-syscall #i64 [[number|value]]
            ([[first|value]] [[second|value]]))))
          (#let result #usize (#unsafe (#asm #usize (([[register|rax]] [[operand|value]])) "nop")))
          (#forget array) (#return (#as result #u64))
  );
}
    "#,
        &[
            ("repeat", &["param"]),
            ("number", &["param"]),
            ("first", &["param"]),
            ("second", &["param"]),
            ("operand", &["param"]),
            ("register", &[]),
        ],
    );
}

#[test]
fn unrecognized_generator_lists_are_literal_data_even_when_they_contain_binding_names() {
    run(
        r#"
#gn-fn identity { [[param|item]]; } (literal [[data|item]])
#gn-fn evaluate { [[value|item]]; } (#gn-list [[evaluated|item]])
#gn nested { [[nested-param|item]]; }
          `(([[literal|item]] `(,[[inactive|item]] ,,[[active|item]])))
    "#,
        &[
            ("data", &[]),
            ("evaluated", &["value"]),
            ("literal", &[]),
            ("inactive", &[]),
            ("active", &["nested-param"]),
        ],
    );
}

#[test]
fn inline_control_flow_receiver_types_use_checked_metadata_when_needed() {
    let input = r#"
#struct Row () (([[field|value]] #u64))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let one #u64 (#get (#if true (#struct-literal Row ((value 1u64)))
                                        (#struct-literal Row ((value 2u64)))) [[if-field|value]]))
          (#let two #u64 (#get (#block (#let record Row (#struct-literal Row ((value 3u64)))) record) [[block-field|value]]))
          (#let three #u64 (#get (#match true
            (#case true (#struct-literal Row ((value 4u64))))
            (#case false (#struct-literal Row ((value 5u64))))) [[match-field|value]]))
          (#let four #u64 (#get (#loop (#break (#struct-literal Row ((value 6u64))))) [[loop-field|value]]))
          (#let five #u64 (#get (#label done (#loop (#break-to done (#struct-literal Row ((value 7u64)))))) [[label-field|value]]))
          (#return one)
  );
}
    "#;
    lim::check_types(&lim::parse_program(&annotated(input).0).unwrap()).unwrap();
    run(
        input,
        &[
            ("if-field", &["field"]),
            ("block-field", &["field"]),
            ("match-field", &["field"]),
            ("loop-field", &["field"]),
            ("label-field", &["field"]),
        ],
    );
}

#[test]
fn borrowed_and_pinned_payload_members_keep_their_declared_type() {
    for (case, kind) in [
        ("#case", "Choice"),
        ("#case-ref", "(#ref Choice)"),
        ("#case-ref-mut", "(#ref-mut Choice)"),
        ("#case-pin", "(#pin-ref Choice)"),
        ("#case-pin-mut", "(#pin-ref-mut Choice)"),
    ] {
        let source = format!(
            r#"
#struct Row () (([[field|value]] #u64))
#enum Choice () ((Choice.Full Row) Choice.Empty)
#fn read {{
  #params = ((input {kind}));
  #returns = #u64;
  #body = ( (#return (#match input
              ({case} (Choice.Full [[payload|row]])
                (#let answer #u64 (#get [[receiver|row]] [[member|value]]))
                (#forget row) answer)
              ({case} Choice.Empty 0u64)))
  );
}}
        "#
        );
        run(
            &source,
            &[("receiver", &["payload"]), ("member", &["field"])],
        );
    }
}

#[test]
fn internal_thread_signatures_and_worker_symbols_have_declaration_roles() {
    run(
        r#"
#fn [[worker|worker]] {
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}
#thread-task Task [[worker-use|worker]]
          (#thread-task-spawn [[spawn|spawn-task]] (([[param|value]] #u64)) Task)
          (#thread-task-join join-task ((task Task)) #u64)
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let task Task (#call [[spawn-use|spawn-task]] (([[label|value]] 42u64))))
          (#return (#call join-task ((task task))))
  );
}
    "#,
        &[
            ("worker-use", &["worker"]),
            ("spawn-use", &["spawn"]),
            ("label", &["param"]),
        ],
    );
}

#[test]
fn ordinary_operand_families_keep_value_roles_in_every_position() {
    for expression in [
        "(#deref vALUE)",
        "(#deref-set vALUE vALUE)",
        "(#clone vALUE)",
        "(#println vALUE)",
        "(#assert vALUE)",
        "(#debug-assert vALUE)",
        "(#set-index vALUE vALUE vALUE)",
        "(#pin-write vALUE vALUE)",
        "(#ptr-offset vALUE vALUE)",
        "(#ptr-write vALUE vALUE)",
        "(#slice-range vALUE vALUE vALUE)",
        "(#slice-mut-range vALUE vALUE vALUE)",
        "(#slice-mut-split vALUE vALUE)",
        "(#index vALUE vALUE)",
        "(#atomic-load vALUE #memory-relaxed)",
        "(#atomic-store vALUE vALUE #memory-release)",
        "(#atomic-compare-exchange vALUE vALUE vALUE #memory-acq-rel #memory-acquire)",
        "(#word-write Number vALUE vALUE)",
        "(#word-forget Number vALUE)",
        "(#u64::add-wrap vALUE vALUE)",
    ] {
        let mut counter = 0;
        let mut expression = expression.to_owned();
        while let Some(start) = expression.find("vALUE") {
            expression.replace_range(start..start + 5, &format!("[[use-{counter}|value]]"));
            counter += 1;
        }
        let source = format!("#type Number #u64\n#fn main {{\n  #params = (([[parameter|value]] #u64));\n  #returns = ();\n  #body = ( {expression} (#return ())\n  );\n}}\n");
        let queries = (0..counter)
            .map(|index| format!("use-{index}"))
            .collect::<Vec<_>>();
        let expected = queries
            .iter()
            .map(|name| (name.as_str(), &["parameter"][..]))
            .collect::<Vec<_>>();
        run(&source, &expected);
    }
}

#[test]
fn optional_reference_projections_resolve_payload_members_and_branch_scopes() {
    for kind in ["ref", "ref-mut", "pin-ref", "pin-ref-mut"] {
        let source = format!(
            r#"
#struct Row () (([[field|value]] #u64))
#enum [[enum|Projection]] () (([[full|Projection::Some]] (#{kind} Row)) Projection.None)
#fn main {{
  #params = (([[input|input]] [[type|Projection]]));
  #returns = #u64;
  #body = (
              (#let-else ([[variant|Projection::Some]] [[payload|payload]]) [[operand|input]]
                (#else
                  (#forget [[success-in-failure|payload]])
                  (#let [[failure|failure]] #u64 0u64)
                  (#return [[failure-use|failure]])))
              (#forget [[failure-leak|failure]])
              (#return (#get [[payload-use|payload]] [[member|value]]))
  );
}}
        "#
        );
        run(
            &source,
            &[
                ("variant", &["full"]),
                ("type", &["enum"]),
                ("operand", &["input"]),
                ("failure-use", &["failure"]),
                ("success-in-failure", &[]),
                ("failure-leak", &[]),
                ("payload-use", &["payload"]),
                ("member", &["field"]),
            ],
        );
    }
}

#[test]
fn inconsistent_or_bindings_fail_closed_in_the_arm_body() {
    run(
        r#"
#enum Choice () ((Choice.A #u64) (Choice.B #u64))
#fn main {
  #params = ((input Choice));
  #returns = #u64;
  #body = ( (#return (#match input
          (#case (#or (Choice.A x) (Choice.B y)) [[missing|x]])))
  );
}
    "#,
        &[("missing", &[])],
    );
}

#[test]
fn compact_let_else_navigates_the_initializer_and_isolates_failure_scope() {
    run(
        r#"
#struct Row () (([[field|value]] #u64))
#enum Choice () (([[full|Choice.Full]] Row) Choice.Empty)
#fn main {
  #params = (([[input|input]] Choice) ([[fallback|fallback]] #u64));
  #returns = #u64;
  #body = (
          (#let-else ([[variant|Choice.Full]] [[payload|payload]]) [[operand|input]]
            (#else
              (#forget [[missing|payload]])
              (#let [[failure-local|failure-local]] #u64 [[fallback-use|fallback]])
              (#return [[failure-use|failure-local]])))
          (#forget [[failure-leak|failure-local]])
          (#return (#get [[payload-use|payload]] [[member|value]]))
  );
}
    "#,
        &[
            ("variant", &["full"]),
            ("operand", &["input"]),
            ("missing", &[]),
            ("fallback-use", &["fallback"]),
            ("failure-use", &["failure-local"]),
            ("failure-leak", &[]),
            ("payload-use", &["payload"]),
            ("member", &["field"]),
        ],
    );
}

#[test]
fn enum_literals_navigate_only_variants_and_runtime_payloads() {
    run(
        r#"
#struct Row () (([[field|value]] #u64))
#enum Choice () (([[full|Choice.Full]] Row) [[empty|Choice.Empty]])
#fn main {
  #params = (([[input|input]] Row));
  #returns = #u64;
  #body = (
          (#let choice Choice (#enum-literal [[variant|Choice.Full]] [[payload|input]]))
          (#let missing Choice (#enum-literal [[wrong-target|input]] input))
          (#let none Choice (#enum-literal [[fieldless|Choice.Empty]]))
          (#let-else ([[pattern|Choice.Full]] [[binding|row]]) choice (#else (#return 0u64)))
          (#return (#get [[use|row]] [[member|value]]))
  );
}
    "#,
        &[
            ("variant", &["full"]),
            ("payload", &["input"]),
            ("wrong-target", &[]),
            ("fieldless", &["empty"]),
            ("pattern", &["full"]),
            ("use", &["binding"]),
            ("member", &["field"]),
        ],
    );
}

#[test]
fn contracts_resolve_predicates_subjects_and_no_keyword_definitions() {
    run(
        "#fn [[predicate|valid]] {
  #params = ((value #u64));
  #returns = #bool;
  #body = ( (#return true)
  );
}
#fn example {
  #params = (([[parameter|input]] #u64));
  #returns = ();
  #body = (
          (#[[requires|requires]] (#call [[use-predicate|valid]] ((value [[subject|input]]))))
          (#[[ensures|ensures]] (#call valid ((value (#[[old|old]] [[old-subject|input]])))))
          (#[[preserves|preserves]] (#call valid ((value [[preserved-subject|input]]))))
          (#[[assume|assume]] (#call valid ((value [[assumed-subject|input]]))))
          (#[[branch|if-valid]] (#call valid ((value [[validated-subject|input]]))) ())
          (#return ())
  );
}
",
        &[
            ("use-predicate", &["predicate"]),
            ("subject", &["parameter"]),
            ("old-subject", &["parameter"]),
            ("preserved-subject", &["parameter"]),
            ("assumed-subject", &["parameter"]),
            ("validated-subject", &["parameter"]),
            ("requires", &[]),
            ("ensures", &[]),
            ("preserves", &[]),
            ("assume", &[]),
            ("branch", &[]),
            ("old", &[]),
        ],
    );
}
#[test]
fn refinement_binder_scope_is_local_to_the_type() {
    run("#fn [[predicate|valid]] {
  #params = ((value #u64));
  #returns = #bool;
  #body = ( (#return true)
  );
}
#const [[global|value]] #u64 1u64
#type Small (#[[where|where]] ([[binder|value]] #u64) (#call [[use|valid]] ((value [[bound|value]]))))
#fn example {
  #params = ();
  #returns = #u64;
  #body = ( (#return [[outside|value]])
  );
}
", &[
      ("where", &[]), ("use", &["predicate"]), ("bound", &["binder"]), ("outside", &["global"]),
    ]);
}
#[test]
fn postcondition_result_has_return_type_for_member_navigation() {
    run(
        "#struct Packet () (([[field|count]] #u64))
#fn valid {
  #params = ((value #u64));
  #returns = #bool;
  #body = ( (#return true)
  );
}
#fn make {
  #params = ();
  #returns = Packet;
  #body = (
          (#ensures (#call valid ((value (#get (#[[result|result]]) [[projection|count]])))))
          (#return (#struct-literal Packet ((count 1u64))))
  );
}
",
        &[("result", &[]), ("projection", &["field"])],
    );
}

#[test]
fn effects_metadata_has_declaration_targets_and_no_keyword_targets() {
    run(
        r#"#static [[state|state]] #u64 0u64
#fn [[leaf|leaf]] {
  #params = (); #returns = (); #effects = (#io-output);
  #body = ((#return ()));
}
#fn wrapper {
  #params = (); #returns = ();
  #[[effects-key|effects]] = (
    #[[io|io]] #[[input|io-input]] #[[output|io-output]]
    #[[global|global-access]]
    (#[[of|effects-of]] [[bare-function|leaf]])
    (#effects-of (([[qualified-function|@leaf]] ())
                  ([[grouped-function|leaf]])))
    (#[[read|read-global]] [[read-state|state]])
    (#[[write|write-global]] [[write-state|@state]])
  );
  #body = ((#return ()));
}
"#,
        &[
            ("effects-key", &[]), ("io", &[]), ("input", &[]),
            ("output", &[]), ("global", &[]), ("of", &[]),
            ("read", &[]), ("write", &[]),
            ("bare-function", &["leaf"]),
            ("qualified-function", &["leaf"]),
            ("grouped-function", &["leaf"]),
            ("read-state", &["state"]),
            ("write-state", &["state"]),
        ],
    );
}

#[test]
fn effects_metadata_does_not_navigate_wrong_declaration_kinds() {
    run(
        r#"#static state #u64 0u64
#const answer #u64 42u64
#fn leaf {
  #params = (); #returns = (); #body = ((#return ()));
}
#fn wrapper {
  #params = ((local #u64)); #returns = ();
  #effects = (
    (#effects-of [[static-as-function|@state]])
    (#effects-of [[constant-as-function|answer]])
    (#effects-of [[local-as-function|local]])
    (#read-global [[function-as-static|leaf]])
    (#write-global [[qualified-function-as-static|@leaf]])
    (#read-global [[constant-as-static|answer]])
    (#read-global [[missing-static|missing]])
    (#effects-of '[[quoted-function|@leaf]])
  );
  #body = ((#return ()));
}
"#,
        &[
            ("static-as-function", &[]),
            ("constant-as-function", &[]),
            ("local-as-function", &[]),
            ("function-as-static", &[]),
            ("qualified-function-as-static", &[]),
            ("constant-as-static", &[]),
            ("missing-static", &[]),
            ("quoted-function", &[]),
        ],
    );
}

#[test]
fn byte_io_builtin_heads_have_no_targets_but_operands_do() {
    run(
        r#"#fn read {
  #params = (([[input-fd|descriptor]] #i64));
  #returns = (#tuple #i64 #u8); #effects = (#io-input);
  #body = ((#return
    (#[[input-builtin|io-input-byte]] [[input-use|descriptor]])));
}
#fn write {
  #params = (([[output-fd|descriptor]] #i64)
             ([[byte|byte]] #u8));
  #returns = #i64; #effects = (#io-output);
  #body = ((#return (#[[output-builtin|io-output-byte]]
    [[output-use|descriptor]] [[byte-use|byte]])));
}
"#,
        &[
            ("input-builtin", &[]), ("output-builtin", &[]),
            ("input-use", &["input-fd"]),
            ("output-use", &["output-fd"]),
            ("byte-use", &["byte"]),
        ],
    );
}

#[test]
fn effect_targets_follow_library_reexports_to_canonical_declarations() {
    run_with_files(
        r#"#alias count = ./library/lib.lim::counter
#alias action = ./library/lib.lim::invoke
#fn main {
  #params = (); #returns = ();
  #effects = (
    (#read-global [[read-alias|count]])
    (#write-global [[write-alias|@count]])
    (#effects-of ([[qualified-alias|@action]]
                  ([[bare-alias|action]])))
  );
  #body = ((#return ()));
}
"#,
        &[
            (
                "library/lib.lim",
                "#alias counter = ./storage.lim::state\n\
                 #alias invoke = ./storage.lim::callback\n\
                 #export counter invoke\n",
            ),
            (
                "library/storage.lim",
                r#"#static [[canonical-state|state]] #u64 0u64
#fn [[canonical-function|callback]] {
  #params = (); #returns = (); #effects = (#io-output);
  #body = ((#return ()));
}
"#,
            ),
        ],
        &[
            ("read-alias", &["canonical-state"]),
            ("write-alias", &["canonical-state"]),
            ("qualified-alias", &["canonical-function"]),
            ("bare-alias", &["canonical-function"]),
        ],
    );
}

#[test]
fn generator_effect_shaped_data_keeps_existing_qualification_roles() {
    let input = r#"#fn [[leaf|leaf]] {
  #params = (); #returns = (); #body = ((#return ()));
}
#gn ignore { value; } (#gn-list)
#generate ignore { value = (#effects ((#effects-of (
  [[literal|leaf]] [[qualified|@leaf]])))); }
"#;
    lim::parse_program(&annotated(input).0).unwrap();
    run(input, &[("literal", &[]), ("qualified", &["leaf"])]);
}

#[test]
fn delimited_let_bindings_keep_local_type_and_initializer_navigation() {
    for keyword in ["#let", "#let-mut"] {
        let source = r#"#type [[number|Number]] #u64
#fn [[identity|identity]] {
  #params = { [[parameter|value]] = Number; };
  #returns = Number;
  #body: #return value;
}
#fn main {
  #params = {}; #returns = Number;
  #body = (
    #let [[input|input]] : Number = 42u64;
    #let-kind [[binding|count]] [[colon|:]] [[type-use|Number]] [[equals|=]] [[callee|identity]] { [[label|value]] = [[argument|input]]; };
    #return [[later-use|count]];
  );
}
"#
        .replace("#let-kind", keyword);
        run(
            &source,
            &[
                ("binding", &["binding"]),
                ("type-use", &["number"]),
                ("colon", &[]),
                ("equals", &[]),
                ("callee", &["identity"]),
                ("label", &["parameter"]),
                ("argument", &["input"]),
                ("later-use", &["binding"]),
            ],
        );
    }
}

#[test]
fn delimited_let_compound_types_keep_exact_user_type_targets() {
    run(
        r#"#struct [[row-type|Row]] () (([[field|value]] #u64))
#fn main {
  #params = {}; #returns = #u64;
  #body = (
    #let [[row|row]] : [[named-type|Row]] = (#struct-literal [[constructor-type|Row]] ((value 42u64)));
    #let [[view|view]] [[ref-colon|:]] (#ref [[referent-type|Row]]) [[ref-equals|=]] (#borrow [[owner-use|row]]);
    #let-mut [[pair|pair]] [[tuple-colon|:]] (#tuple [[left-type|Row]] [[right-type|Row]]) [[tuple-equals|=]] (#tuple [[left-value|row]] [[right-value|row]]);
    #forget [[pair-use|pair]];
    #return (#get [[view-use|view]] [[field-use|value]]);
  );
}
"#,
        &[
            ("named-type", &["row-type"]),
            ("constructor-type", &["row-type"]),
            ("referent-type", &["row-type"]),
            ("left-type", &["row-type"]),
            ("right-type", &["row-type"]),
            ("ref-colon", &[]),
            ("ref-equals", &[]),
            ("tuple-colon", &[]),
            ("tuple-equals", &[]),
            ("owner-use", &["row"]),
            ("left-value", &["row"]),
            ("right-value", &["row"]),
            ("pair", &["pair"]),
            ("pair-use", &["pair"]),
            ("view-use", &["view"]),
            ("field-use", &["field"]),
        ],
    );
}

#[test]
fn delimited_let_multiline_initializers_keep_callees_and_named_arguments() {
    for keyword in ["#let", "#let-mut"] {
        let source = r#"#fn [[choose|choose]] {
  #params = { [[first|first]] = #u64; [[second|second]] = #u64; };
  #returns = #u64;
  #body: #return (#u64::add-wrap first second);
}
#fn main {
  #params = {}; #returns = #u64;
  #body = (
    #let [[input|input]] : #u64 = 21u64;
    #let-kind [[binding|answer]] [[colon|:]] #u64 [[equals|=]] (#call [[callee|choose]] (
        ([[second-label|second]] [[second-argument|input]])
        ([[first-label|first]] [[first-argument|input]])
      ));
    #return [[later-use|answer]];
  );
}
"#
        .replace("#let-kind", keyword);
        run(
            &source,
            &[
                ("binding", &["binding"]),
                ("colon", &[]),
                ("equals", &[]),
                ("callee", &["choose"]),
                ("second-label", &["second"]),
                ("second-argument", &["input"]),
                ("first-label", &["first"]),
                ("first-argument", &["input"]),
                ("later-use", &["binding"]),
            ],
        );
    }
}

#[test]
fn generator_records_separate_argument_keys_bindings_and_capabilities() {
    run(r#"
#capability [[capability|Copy]] #u64 ()
#gn-fn [[helper|echo]] { [[helper-key|item]] = [[helper-binding|local]]; }
  [[helper-use|local]]
#gn [[generator|emit]] {
  [[key|input]] = [[binding|value]];
  [[pun|items]];
  [[cap-key|type]] = ([[cap-binding|ty]] [[cap-use|Copy]]);
}
  (#gn-list [[binding-use|value]] [[pun-use|items]] [[type-use|ty]]
            [[label-leak|input]]
            (#gn-call [[helper-call|echo]] {
              [[helper-label|item]] = [[helper-value|value]];
            }))
#generate [[generator-call|emit]] {
  [[invocation-label|input]] = [[literal-value|value]];
  [[pun-label|items]] = ([[literal-item|items]]);
  [[type-label|type]] = #u64;
}
#gn outside {} [[binding-leak|value]]
"#, &[
        ("key", &["key"]), ("binding", &["binding"]),
        ("binding-use", &["binding"]), ("pun-use", &["pun"]),
        ("type-use", &["cap-binding"]), ("cap-use", &["capability"]),
        ("label-leak", &[]), ("binding-leak", &[]),
        ("helper-call", &["helper"]), ("helper-use", &["helper-binding"]),
        ("helper-label", &["helper-key"]), ("helper-value", &["binding"]),
        ("generator-call", &["generator"]), ("invocation-label", &["key"]),
        ("pun-label", &["pun"]), ("type-label", &["cap-key"]),
        ("literal-value", &[]), ("literal-item", &[]),
    ]);
}

#[test]
fn generator_call_puns_keep_both_roles_and_loop_bindings_stay_local() {
    run(r#"
#gn-fn echo { [[helper-key|item]] = local; } local
#gn emit { [[binding|item]]; [[items|items]]; }
  (#gn-list
    (#gn-call echo { [[call-pun|item]]; })
    (#gn-for-each [[loop-binding|entry]] [[loop-input|items]]
      (#gn-call echo { [[call-key|item]] = [[loop-use|entry]]; }))
    [[loop-leak|entry]])
#generate emit { [[literal-pun|item]]; items = (); }
"#, &[
        ("call-pun", &["helper-key", "binding"]),
        ("loop-input", &["items"]), ("loop-use", &["loop-binding"]),
        ("call-key", &["helper-key"]), ("loop-leak", &[]),
        ("literal-pun", &["binding"]),
    ]);
}

#[test]
fn generator_literal_arguments_keep_only_explicit_qualification_and_function_roles() {
    run(r#"
#fn [[runtime|ordinary]] { #params = (); #returns = #u64; #body = ((#return 42u64)); }
#gn emit { [[key|input]]; } `()
#generate emit { [[label|input]] =
  (([[literal|ordinary]]) [[qualified|@ordinary]]
   (#gn-call [[literal-helper|ordinary]] { input = [[literal-expression|ordinary]]; })
   (#fn nested { #params = (([[parameter|value]] #u64)); #returns = #u64;
     #body = ((#return [[parameter-use|value]])); }));
}
"#, &[
        ("label", &["key"]), ("literal", &[]), ("qualified", &["runtime"]),
        ("literal-helper", &[]), ("literal-expression", &[]),
        ("parameter-use", &["parameter"]),
    ]);
}

#[test]
fn generator_record_targets_reject_wrong_kinds_and_old_positional_binding_roles() {
    run(r#"
#fn [[runtime|ordinary]] { #params = (); #returns = #u64; #body = ((#return 42u64)); }
#struct Fake () ()
#gn-fn helper { [[helper-key|item]] = local; } local
#gn emit { [[binding|item]]; }
  (#gn-list
    (#gn-call [[wrong-helper|ordinary]] { [[wrong-label|item]] = [[value-use|item]]; })
    (#gn-call [[wrong-qualified-helper|@ordinary]] { item = item; })
    (#gn-call [[generator-as-helper|emit]] { [[generator-as-helper-label|item]] = item; })
    (#gn-call helper { [[unknown-label|missing]] = item; }))
#generate [[wrong-generator|ordinary]] { [[wrong-generator-label|item]] = item; }
#generate [[helper-as-generator|helper]] { [[helper-as-generator-label|item]] = item; }
#gn wrong-capability { type = (bound [[wrong-capability|Fake]]); } bound
#gn old ([[old-binding|legacy]]) [[old-use|legacy]]
"#, &[
        ("wrong-helper", &[]), ("wrong-label", &[]), ("value-use", &["binding"]),
        ("wrong-qualified-helper", &[]), ("unknown-label", &[]),
        ("generator-as-helper", &[]), ("generator-as-helper-label", &[]),
        ("wrong-generator", &[]), ("wrong-generator-label", &[]),
        ("helper-as-generator", &[]), ("helper-as-generator-label", &[]),
        ("wrong-capability", &[]), ("old-binding", &[]), ("old-use", &[]),
    ]);
}

#[test]
fn capability_annotations_resolve_all_implementations_without_using_type_roles() {
    run(r#"
#capability [[first|Copy]] #u64 ()
#capability [[second|Copy]] #u32 ()
#gn emit { type = (ty [[reference|Copy]]); } `()
"#, &[("reference", &["first", "second"])]);
}
