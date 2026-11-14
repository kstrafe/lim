mod support;

#[test]
fn array_generator_inputs_are_literal_data() {
    run(
        "(#struct Row () (: value #u64))
         (#generate #[[generator|array]]
           (: [[element-label|element]] [[element|Row]] : [[length-label|length]] [[length|4]] : [[name-label|name]] [[name|Rows]]))",
        &[("generator", &[]), ("element-label", &[]), ("element", &[]), ("length-label", &[]), ("length", &[]), ("name-label", &[]), ("name", &[])],
    );
}

#[test]
fn callable_intrinsic_operands_navigate_but_builtin_labels_do_not() {
    run(
        "(#fn use (([[left|index]] #usize) ([[right|bound]] #usize)) #bool
          (#return (#[[call|call]] #[[intrinsic|usize::lt]]
            (: [[label-left|left]] [[left-use|index]] : [[label-right|right]] [[right-use|bound]]))))",
        &[("call", &[]), ("intrinsic", &[]), ("label-left", &[]), ("label-right", &[]), ("left-use", &["left"]), ("right-use", &["right"])],
    );
}

#[test]
fn proven_index_has_value_operands_and_no_keyword_definition() {
    run(
        "(#struct Item () (([[field|value]] #u64)))
         (#fn read (([[array|values]] (#ref (#array Item 4))) ([[index|position]] #usize)) #u64
           (#requires (#usize::lt [[bound-index|position]] 4usize))
           (#return (#get (#[[keyword|index-proven]] [[array-use|values]] [[index-use|position]]) [[field-use|value]])))",
        &[("keyword", &[]), ("bound-index", &["index"]), ("array-use", &["array"]), ("index-use", &["index"]), ("field-use", &["field"])],
    );
}

#[test]
fn call_graph_has_no_user_definition_or_arguments() {
    run(
        "(#fn [[entry|main]] () #u64
      (#println (#[[trace|call-graph]]))
      (#return 42u64))",
        &[("entry", &["entry"]), ("trace", &[])],
    );
}

#[test]
fn generated_variant_name_operations_navigate_syntax_parameters() {
    run(
        "(#gn make ([[binding|name]])
      (#[[operation|gn-variant]] [[argument|name]] [[literal|\"Ready\"]]))",
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
    let scratch = support::Scratch::new("lsp-navigation");
    let uri = lsp::path_to_uri(&scratch.path().join("main.lim")).unwrap();
    let (source, marks) = annotated(input);
    lim::parse(&source).unwrap();
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
            let (start, end) = marks[*target];
            let (line, character) = lsp::byte_position(&source, start);
            let (end_line, end_character) = lsp::byte_position(&source, end);
            assert!(
                actual.iter().any(|item| {
                    let range = item.get("range").unwrap();
                    item.get("uri").and_then(Json::string) == Some(uri.as_str())
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
      (#enum Choice () ((Choice.Full #u64) Choice.Empty))
      (#const [[limit|LIMIT]] #u64 42u64)
      (#static [[count|COUNT]] #u64 1u64)
      (#fn first (: [[first-x|x]] Choice) #u64
        (#return (#match [[match-x|x]]
          (#case (Choice.Full [[payload|value]])
            (#let-mut [[local|answer]] #u64 [[payload-use|value]])
            (#set [[set-use|answer]] (#u64::add-wrap [[arithmetic-use|answer]] [[limit-use|LIMIT]]))
            (#let ref (#ref #u64) (#borrow [[borrow-use|answer]]))
            (#forget ref)
            (#return [[return-use|answer]]))
          (#case Choice.Empty (#unsafe [[static-use|COUNT]])))))
      (#fn second (: [[second-x|x]] #u64) #u64 (#return [[second-use|x]]))
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
      (#struct [[left|Left]] () (: [[left-value|value]] #u64))
      (#struct Right () (: [[right-value|value]] #u64))
      (#type Alias (#ref Left))
      (#fn make (: [[param|value]] #u64) Right
        (#return (#struct-literal Right (: [[literal-field|value]] [[param-use|value]]))))
      (#fn other (: [[other-param|value]] #u64) #u64 (#return value))
      (#fn main (: [[owner|object]] Alias) #u64
        (#let [[local|value]] #u64 (#get [[receiver|object]] [[left-field|value]]))
        (#let record Right (#call make (: [[label|value]] [[argument|value]])))
        (#set-field record [[set-field|value]] 2u64)
        (#let field #u64 (#get record [[right-field|value]]))
        (#call other (($ [[pun|value]])))
        (#call other (: [[other-label|value]] 1u64))
        (#return (#get (#call make (: value 0u64)) [[call-field|value]])))
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
fn pattern_forms_bind_values_in_their_own_scopes_and_navigate_variants() {
    run(
        r#"
      (#struct Record () (: [[field|value]] #u64))
      (#enum [[choice|Choice]] () (([[full|Choice.Full]] Record) [[empty|Choice.Empty]]))
      (#fn inspect (: input Choice) #u64
        (#let-else ([[let-variant|Choice.Full]] [[success|record]]) [[let-type|Choice]] input
          (#else [[else-variant|Choice.Empty]] (#return 0u64)))
        (#let n #u64 (#get [[success-use|record]] [[success-field|value]]))
        (#if-let ([[if-variant|Choice.Full]] [[if-bind|inside]]) Choice (Choice.Full record)
          (#block (#forget [[if-use|inside]]) ())
          (#block (#forget [[not-in-else|inside]]) ()))
        (#while-let ([[while-variant|Choice.Full]] [[while-bind|item]]) (Choice.Full record)
          (#forget [[while-use|item]]) (#break))
        (#forget [[not-after-loop|item]])
        (#return n))
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
      (#fn main () #u64
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
        (#return [[first-use|a]]))
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
      (#struct [[record|Record]] () (: [[field|value]] #u64))
      (#type [[alias|Number]] #u64)
      (#enum Choice () (([[full|Choice.Full]] Record) Choice.Empty))
      (#fn main () #u64
        (#let r Record (#struct-literal [[literal|Record]] (: value 42u64)))
        (#let size #usize (#size-of [[size|Record]]))
        (#let align #usize (#align-of [[align|Record]]))
        (#let offset #usize (#offset-of [[offset-type|Record]] [[offset-field|value]]))
        (#let n Number (#as 42u64 [[cast|Number]]))
        (#let array (#array Record 1) (#array-of (#array [[array|Record]] 1) r))
        (#let pointer (#ptr Record) (#ptr-null (#ptr [[pointer|Record]])))
        (#let choice Choice ([[constructor|Choice.Full]] (#struct-literal Record (: value 42u64))))
        (#assert (#variant-is choice [[is|Choice.Full]]))
        (#let extracted Record (#get-payload choice [[payload|Choice.Full]] 0))
        (#forget array) (#forget pointer) (#forget extracted)
        (#return n))
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
      (#gn-fn [[helper|identity]] ([[param|value]]) [[param-use|value]])
      (#gn emit ([[items|items]])
        (#gn-for-each [[item|item]] [[items-use|items]]
          (#gn-call [[call|identity]]
            `(([[literal|item]] ,[[unquoted|item]] ',[[quoted|item]])))))
      (#syntax [[bundle|Protocol]] (#u64))
      (#fn ordinary (: [[runtime|x]] #u64) #u64 (#return x))
      (#generate emit [[argument-literal|ordinary]])
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
      (#generate unknown (: function
        (#fn work (: [[param|名字]] #u64) #u64
          (#let [[local|résultat]] #u64 [[param-use|名字]])
          (#return [[local-use|résultat]]))))
    "#,
        &[("param-use", &["param"]), ("local-use", &["local"])],
    );
}

#[test]
fn or_patterns_share_one_binding_but_invalid_duplicate_lets_are_ambiguous() {
    run(
        r#"
      (#enum Choice () ((Choice.A #u64) (Choice.B #u64)))
      (#fn choose (: input Choice) #u64
        (#return (#match input
          (#case (#or (Choice.A [[a|value]]) (Choice.B [[b|value]])) [[use|value]]))))
      (#fn broken () #u64
        (#let repeated #u64 0u64)
        (#let repeated #u64 1u64)
        (#return [[duplicate|repeated]]))
    "#,
        &[("use", &["a", "b"]), ("duplicate", &[])],
    );
}

#[test]
fn syntax_bundles_and_nested_splices_have_explicit_reference_roles() {
    run(
        r#"
      (#syntax [[base|Base]] (#u64))
      (#syntax [[combined|Combined]] ((#syntax-splice [[nested|Base]])))
      (#fn expanded () (#syntax-splice [[signature|Base]]) (#return 42u64))
      (#generate unknown (: function (#fn work () #u64
        (#let result #u64 (#await [[protocol|Combined]] child))
        (#return result))))
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
      (#enum RegisterCollision () (RegisterCollision.Rax))
      (#fn main (: [[param|value]] #usize) #u64
        (#let array (#array #usize 2) (#array-repeat [[repeat|value]]))
        (#let kernel #i64 (#unsafe (#linux-syscall #i64 [[number|value]]
          ([[first|value]] [[second|value]]))))
        (#let result #usize (#unsafe (#asm #usize (([[register|rax]] [[operand|value]])) "nop")))
        (#forget array) (#return (#as result #u64)))
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
      (#gn-fn identity ([[param|item]]) (literal [[data|item]]))
      (#gn-fn evaluate ([[value|item]]) (#gn-list [[evaluated|item]]))
      (#gn nested ([[nested-param|item]])
        `(([[literal|item]] `(,[[inactive|item]] ,,[[active|item]]))))
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
      (#struct Row () (: [[field|value]] #u64))
      (#fn main () #u64
        (#let one #u64 (#get (#if true (#struct-literal Row (: value 1u64))
                                      (#struct-literal Row (: value 2u64))) [[if-field|value]]))
        (#let two #u64 (#get (#block (#let record Row (#struct-literal Row (: value 3u64))) record) [[block-field|value]]))
        (#let three #u64 (#get (#match true
          (#case true (#struct-literal Row (: value 4u64)))
          (#case false (#struct-literal Row (: value 5u64)))) [[match-field|value]]))
        (#let four #u64 (#get (#loop (#break (#struct-literal Row (: value 6u64)))) [[loop-field|value]]))
        (#let five #u64 (#get (#label done (#loop (#break-to done (#struct-literal Row (: value 7u64))))) [[label-field|value]]))
        (#return one))
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
          (#struct Row () (: [[field|value]] #u64))
          (#enum Choice () ((Choice.Full Row) Choice.Empty))
          (#fn read (: input {kind}) #u64 (#return (#match input
            ({case} (Choice.Full [[payload|row]])
              (#let answer #u64 (#get [[receiver|row]] [[member|value]]))
              (#forget row) answer)
            ({case} Choice.Empty 0u64))))
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
      (#fn [[worker|worker]] (: value #u64) #u64 (#return value))
      (#thread-task Task [[worker-use|worker]]
        (#thread-task-spawn [[spawn|spawn-task]] (: [[param|value]] #u64) Task)
        (#thread-task-join join-task (: task Task) #u64))
      (#fn main () #u64
        (#let task Task (#call [[spawn-use|spawn-task]] (: [[label|value]] 42u64)))
        (#return (#call join-task (: task task))))
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
        let source = format!("(#type Number #u64) (#fn main (: [[parameter|value]] #u64) () {expression} (#return ()))");
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
          (#struct Row () (: [[field|value]] #u64))
          (#enum [[enum|Projection]] () (([[full|Projection::Some]] (#{kind} Row)) Projection.None))
          (#fn main (: [[input|input]] [[type|Projection]]) #u64
            (#let-else ([[variant|Projection::Some]] [[payload|payload]]) [[operand|input]]
              (#else
                (#forget [[success-in-failure|payload]])
                (#let [[failure|failure]] #u64 0u64)
                (#return [[failure-use|failure]])))
            (#forget [[failure-leak|failure]])
            (#return (#get [[payload-use|payload]] [[member|value]])))
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
      (#enum Choice () ((Choice.A #u64) (Choice.B #u64)))
      (#fn main (: input Choice) #u64 (#return (#match input
        (#case (#or (Choice.A x) (Choice.B y)) [[missing|x]]))))
    "#,
        &[("missing", &[])],
    );
}

#[test]
fn compact_let_else_navigates_the_initializer_and_isolates_failure_scope() {
    run(
        r#"
      (#struct Row () (: [[field|value]] #u64))
      (#enum Choice () (([[full|Choice.Full]] Row) Choice.Empty))
      (#fn main (: [[input|input]] Choice : [[fallback|fallback]] #u64) #u64
        (#let-else ([[variant|Choice.Full]] [[payload|payload]]) [[operand|input]]
          (#else
            (#forget [[missing|payload]])
            (#let [[failure-local|failure-local]] #u64 [[fallback-use|fallback]])
            (#return [[failure-use|failure-local]])))
        (#forget [[failure-leak|failure-local]])
        (#return (#get [[payload-use|payload]] [[member|value]])))
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
      (#struct Row () (: [[field|value]] #u64))
      (#enum Choice () (([[full|Choice.Full]] Row) [[empty|Choice.Empty]]))
      (#fn main (: [[input|input]] Row) #u64
        (#let choice Choice (#enum-literal [[variant|Choice.Full]] [[payload|input]]))
        (#let missing Choice (#enum-literal [[wrong-target|input]] input))
        (#let none Choice (#enum-literal [[fieldless|Choice.Empty]]))
        (#let-else ([[pattern|Choice.Full]] [[binding|row]]) choice (#else (#return 0u64)))
        (#return (#get [[use|row]] [[member|value]])))
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
        "(#fn [[predicate|valid]] ((value #u64)) #bool (#return true))
      (#fn example (([[parameter|input]] #u64)) ()
        (#[[requires|requires]] (#call [[use-predicate|valid]] (: value [[subject|input]])))
        (#[[ensures|ensures]] (#call valid (: value (#[[old|old]] [[old-subject|input]]))))
        (#[[preserves|preserves]] (#call valid (: value [[preserved-subject|input]])))
        (#[[assume|assume]] (#call valid (: value [[assumed-subject|input]])))
        (#[[branch|if-valid]] (#call valid (: value [[validated-subject|input]])) ())
        (#return ()))",
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
    run("(#fn [[predicate|valid]] ((value #u64)) #bool (#return true))
      (#const [[global|value]] #u64 1u64)
      (#type Small (#[[where|where]] ([[binder|value]] #u64) (#call [[use|valid]] (: value [[bound|value]]))))
      (#fn example () #u64 (#return [[outside|value]]))", &[
      ("where", &[]), ("use", &["predicate"]), ("bound", &["binder"]), ("outside", &["global"]),
    ]);
}
#[test]
fn postcondition_result_has_return_type_for_member_navigation() {
    run(
        "(#struct Packet () (([[field|count]] #u64)))
      (#fn valid ((value #u64)) #bool (#return true))
      (#fn make () Packet
        (#ensures (#call valid (: value (#get (#[[result|result]]) [[projection|count]]))))
        (#return (#struct-literal Packet ((count 1u64)))))",
        &[("result", &[]), ("projection", &["field"])],
    );
}
