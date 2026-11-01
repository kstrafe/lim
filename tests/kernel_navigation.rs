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
fn sort_and_imax_operands_navigate_only_their_universe_binders() {
    run(
        r#"
      (#math-definition u () #pt-nat #pt-zero)
      (#math-definition missing () #pt-nat #pt-zero)
      (#math-definition levels ([[universe|u]] [[other|v]])
        (#[[sort-keyword|pt-sort]]
          (#[[imax-keyword|pt-level-imax]] [[left|u]] (#pt-level-succ [[right|v]])))
        (#pt-lambda (([[term|u]] #pt-nat))
          (#pt-pair (#pt-sort (#pt-level-imax [[level-under-term|u]] [[zero|0]]))
            [[term-use|u]] (#pt-sort (#pt-level-max v (#pt-level-imax [[nested-left|u]] [[nested-right|v]]))))))
      (#math-definition unknown () (#pt-sort (#pt-level-imax [[unknown|missing]] 0)) #pt-zero)
    "#,
        &[
            ("sort-keyword", &[]),
            ("imax-keyword", &[]),
            ("left", &["universe"]),
            ("right", &["other"]),
            ("level-under-term", &["universe"]),
            ("zero", &[]),
            ("term-use", &["term"]),
            ("nested-left", &["universe"]),
            ("nested-right", &["other"]),
            ("unknown", &[]),
        ],
    );
}

#[test]
fn theorem_sort_parameters_use_the_shared_universe_scope() {
    run(
        r#"
      (#theorem reflexive (#universes [[universe|u]] [[other|v]])
        (#parameters
          (#parameter [[type-parameter|A]]
            (#[[sort-keyword|pt-sort]] (#[[imax-keyword|pt-level-imax]] [[left|u]] [[right|v]])))
          (#parameter [[value-parameter|x]] [[parameter-type|A]]))
        (#statement (#pt-eq [[statement-type|A]] [[statement-value|x]] x))
        (#proof (#pt-refl [[evidence-type|A]] [[evidence-value|x]])))
    "#,
        &[
            ("sort-keyword", &[]),
            ("imax-keyword", &[]),
            ("left", &["universe"]),
            ("right", &["other"]),
            ("parameter-type", &["type-parameter"]),
            ("statement-type", &["type-parameter"]),
            ("statement-value", &["value-parameter"]),
            ("evidence-type", &["type-parameter"]),
            ("evidence-value", &["value-parameter"]),
        ],
    );
}

#[test]
fn sort_and_imax_malformed_operands_and_keyword_clicks_have_no_fallback() {
    for expression in [
        "(#[[query|pt-sort]] 0)",
        "(#pt-sort (#[[query|pt-level-imax]] u v))",
        "(#pt-sort (#pt-level-imax [[query|u]]))",
        "(#pt-sort (#pt-level-imax [[query|u]] v 0))",
        "(#pt-sort [[query|u]] v)",
        "(#pt-sort [[query|@u]])",
        "(#pt-sort (#pt-level-imax v [[query|@u]]))",
        "(#pt-type (#pt-level-imax v [[query|@u]]))",
        "(#pt-use u ([[query|@u]]))",
        "(#pt-level-imax [[query|u]] v)",
    ] {
        run(
            &format!("(#math-definition u () #pt-nat #pt-zero) (#math-definition editing (u v) (#pt-sort 1) {expression})"),
            &[("query", &[])],
        );
    }
}

#[test]
fn imported_sort_definitions_keep_colliding_level_aliases_out_of_universe_metadata() {
    run_files(
        r#"
      (#alias u = ./levels.lim::global-u)
      (#alias v = ./levels.lim::global-v)
      (#alias sort-value = ./levels.lim::sort-value)
      (#math-definition instantiate ([[universe|u]] [[other|v]])
        (#pt-sort (#pt-level-succ (#pt-level-imax [[left|u]] [[right|v]])))
        (#pt-use [[reference|sort-value]] ([[argument-left|u]] [[argument-right|v]])))
      (#math-definition nested ([[nested-u|u]] [[nested-v|v]])
        (#pt-sort (#pt-level-succ (#pt-level-imax (#pt-level-imax u v) v)))
        (#pt-use sort-value ((#pt-level-imax [[nested-argument-left|u]] [[nested-argument-right|v]]) v)))
    "#,
        &[(
            "levels.lim",
            r#"
          (#math-definition global-u () #pt-nat #pt-zero)
          (#math-definition global-v () #pt-nat #pt-zero)
          (#math-definition [[original|sort-value]] (a b)
            (#pt-sort (#pt-level-succ (#pt-level-imax a b)))
            (#pt-sort (#pt-level-imax a b)))
        "#,
        )],
        &[
            ("left", &["universe"]),
            ("right", &["other"]),
            ("reference", &["original"]),
            ("argument-left", &["universe"]),
            ("argument-right", &["other"]),
            ("nested-argument-left", &["nested-u"]),
            ("nested-argument-right", &["nested-v"]),
        ],
    );
}

#[test]
fn generated_sort_definitions_keep_universes_distinct_from_definition_context_names() {
    run_files(
        r#"
      (#alias emit = ./generator.lim::emit)
      (#generate emit)
      (#math-definition instantiate ([[universe|u]] [[other|v]])
        (#pt-sort (#pt-level-succ (#pt-level-imax [[left|u]] [[right|v]])))
        (#pt-use [[reference|sort-value]] ([[argument-left|u]] [[argument-right|v]])))
    "#,
        &[(
            "generator.lim",
            r#"
          (#math-definition u () #pt-nat #pt-zero)
          (#gn emit () `((#math-definition sort-value (u v)
            (#pt-sort (#pt-level-succ (#pt-level-imax u v)))
            (#pt-sort (#pt-level-imax u v)))))
        "#,
        )],
        &[
            ("left", &["universe"]),
            ("right", &["other"]),
            ("reference", &["generated:sort-value"]),
            ("argument-left", &["universe"]),
            ("argument-right", &["other"]),
        ],
    );
}

#[test]
fn theorem_parameters_share_their_source_binders_across_statement_and_evidence() {
    run(
        r#"
      (#[[declaration|theorem]] [[name|reflexive]]
        (#[[universes-keyword|universes]] [[universe|u]])
        (#[[parameters-keyword|parameters]]
          (#[[parameter-keyword|parameter]] [[type-parameter|A]] (#pt-type [[parameter-level|u]]))
          (#parameter [[value-parameter|x]] [[parameter-type|A]]))
        (#[[statement-keyword|statement]]
          (#pt-eq [[statement-type|A]] [[statement-left|x]] [[statement-right|x]]))
        (#[[proof-keyword|proof]] (#pt-refl [[evidence-type|A]] [[evidence-value|x]])))
      (#math-definition outside () #pt-nat [[leak|x]])
    "#,
        &[
            ("declaration", &[]),
            ("name", &["name"]),
            ("universes-keyword", &[]),
            ("parameters-keyword", &[]),
            ("parameter-keyword", &[]),
            ("statement-keyword", &[]),
            ("proof-keyword", &[]),
            ("universe", &["universe"]),
            ("parameter-level", &["universe"]),
            ("type-parameter", &["type-parameter"]),
            ("value-parameter", &["value-parameter"]),
            ("parameter-type", &["type-parameter"]),
            ("statement-type", &["type-parameter"]),
            ("statement-left", &["value-parameter"]),
            ("statement-right", &["value-parameter"]),
            ("evidence-type", &["type-parameter"]),
            ("evidence-value", &["value-parameter"]),
            ("leak", &[]),
        ],
    );
}

#[test]
fn theorem_parameter_types_are_sequential_and_use_the_kernel_namespaces() {
    run(
        r#"
      (#type Runtime #u64)
      (#theorem editing
        (#universes [[universe|u]])
        (#parameters
          (#parameter [[type-parameter|A]] (#pt-type [[level|u]]))
          (#parameter [[value-parameter|x]] [[value-type|A]])
          (#parameter [[path-parameter|p]] (#pt-eq [[path-type|A]] [[path-left|x]] x))
          (#parameter future [[future-type|later]])
          (#parameter later [[runtime-type|Runtime]]))
        (#statement (#pt-eq A [[statement|x]] x))
        (#proof (#pt-lambda (([[inner|x]] [[inner-type|A]])) [[inner-use|x]])))
    "#,
        &[
            ("level", &["universe"]),
            ("value-type", &["type-parameter"]),
            ("path-type", &["type-parameter"]),
            ("path-left", &["value-parameter"]),
            ("future-type", &[]),
            ("runtime-type", &[]),
            ("statement", &["value-parameter"]),
            ("inner-type", &["type-parameter"]),
            ("inner-use", &["inner"]),
        ],
    );
}

#[test]
fn math_theorems_and_direct_definitions_have_global_proof_reference_roles() {
    run_files(
        r#"
      (#alias imported = ./library.lim::reflexive)
      (#theorem [[procedural|procedural]] (#proof-eq 0u64 0u64))
      (#math-definition refs () #pt-nat
        (#pt-app (#pt-use [[theorem-use|imported]] ())
          (#pt-program [[procedural-use|procedural]])
          (#pt-certificate [[wrong-certificate|imported]])))
    "#,
        &[(
            "library.lim",
            r#"
          (#theorem [[original|reflexive]]
            (#universes) (#parameters (#parameter A (#pt-type 0)) (#parameter x A))
            (#statement (#pt-eq A x x)) (#proof (#pt-refl A x)))
        "#,
        )],
        &[
            ("theorem-use", &["original"]),
            ("procedural-use", &["procedural"]),
            ("wrong-certificate", &[]),
        ],
    );
}

#[test]
fn generated_shared_parameter_theorems_keep_the_authored_declaration_target() {
    run(
        r#"
      (#gn emit () `((#theorem reflexive
        (#universes) (#parameters (#parameter n #pt-nat))
        (#statement (#pt-eq #pt-nat n n)) (#proof (#pt-refl #pt-nat n)))))
      (#generate emit)
      (#theorem instance (#universes) (#parameters (#parameter m #pt-nat))
        (#statement (#pt-eq #pt-nat m m))
        (#proof (#pt-app (#pt-use [[reference|reflexive]] ()) m)))
    "#,
        &[("reference", &["generated:reflexive"])],
    );
}

#[test]
fn kernel_universes_and_dependent_binders_have_sequential_lexical_scopes() {
    run(
        r#"
      (#[[declaration|math-definition]] [[name|identity]] ([[universe|u]]) (#[[pi|pt-pi]] (([[type-binder|A]] (#pt-type [[signature-level|u]]))
                      ([[argument|x]] [[argument-type|A]])) [[codomain|A]]) (#[[lambda|pt-lambda]] (([[value-type|A]] (#pt-type [[value-level|u]]))
                              ([[value-binder|x]] [[value-argument-type|A]])) [[body|x]]))
      (#math-definition separate () #pt-nat [[no-leak|x]])
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
      (#math-definition scopes () #pt-nat (#pt-lambda (([[outer|x]] #pt-nat))
          (#pt-app (#pt-lambda (([[inner|x]] [[own-type|x]])) [[inner-use|x]]) [[outer-use|x]])))
      (#math-definition bad-scope () #pt-nat (#pt-pi ((first [[later-type|later]]) (later #pt-nat)) [[first-use|first]]))
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
      (#math-definition levels ([[universe|u]] [[other|v]]) (#pt-type (#[[max|pt-level-max]] [[level|u]] (#[[succ|pt-level-succ]] [[successor|v]]) [[number|0]])) (#pt-lambda (([[local|u]] #pt-nat))
          (#pt-pair (#pt-type [[level-under-local|u]]) [[local-use|u]] [[universe-as-term|v]])))
      (#math-definition missing-level () (#pt-type [[unknown|missing]]) #pt-zero)
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
      (#math-definition [[target|NatAlias]] ([[target-level|u]]) (#pt-type 0) #pt-nat)
      (#theorem [[procedural|runtime-proof]] (#proof-eq 0u64 0u64))
      (#fn function () #u64 (#return 0u64))
      (#math-definition refs ([[universe|v]]) #pt-nat (#pt-lambda ((NatAlias #pt-nat) (runtime-proof #pt-nat))
          (#pt-app (#[[use-keyword|pt-use]] [[reference|NatAlias]] ([[explicit-level|v]]))
            (#[[program-keyword|pt-program]] [[program|runtime-proof]])
            (#[[certificate-keyword|pt-certificate]] [[certificate|runtime-proof]])
            (#pt-use [[wrong-kind|function]] ())
            (#pt-program [[wrong-program|NatAlias]])
            (#pt-use [[wrong-use|runtime-proof]] ()))))
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
        let source = format!("(#math-definition operands () #pt-nat (#pt-lambda (([[binder|value]] #pt-nat)) {expression}))");
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
      (#math-definition dependent-pair () (#[[sigma-keyword|pt-sigma]] (([[binder|first]] #pt-nat)) (#pt-eq #pt-nat [[left|first]] [[right|first]])) [[outside|first]])
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
      (#math-inductive [[datatype|Box]] ([[level|u]]) (([[parameter|A]] (#pt-type [[parameter-level|u]]))) (#pt-type [[sort-level|u]]) (([[constructor|pack]] (([[field|value]] [[field-type|A]])
                               ([[evidence|same]] (#pt-eq [[equality-type|A]] [[field-left|value]] [[field-right|value]]))))
         (other (([[isolated|value]] [[other-type|A]]) (leak [[field-leak|same]])))))
      (#math-inductive Another () () (#pt-type 0) ((pack ())))
      (#math-definition make ([[use-level|v]]) #pt-nat (#pt-lambda (([[element|T]] (#pt-type v)) ([[argument|x]] T))
          (#pt-construct [[datatype-use|Box]] ([[level-use|v]]) ([[parameter-use|T]]) [[constructor-use|pack]] ([[field-use|x]] x))))
      (#math-definition eliminate () #pt-nat (#pt-lambda (([[term|x]] #pt-nat))
          (#pt-induct [[induct-type|Box]] (0) ([[induct-param|x]]) [[motive|x]] ([[branch-one|x]] [[branch-two|x]]) [[subject|x]])))
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
        "pt-sort",
        "pt-pi",
        "pt-lambda",
        "pt-sigma",
        "pt-use",
        "pt-app",
        "pt-level-succ",
        "pt-level-max",
        "pt-level-imax",
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
            &format!("(#fn {keyword} () #u64 (#return 0u64)) (#math-definition test () #pt-nat (#[[keyword|{keyword}]]))"),
            &[("keyword", &[])],
        );
    }
    run(
        r#"
      (#[[keyword|theorem]] [[theorem|reflexive]] (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))
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
        let source = format!("(#math-definition value () #pt-nat #pt-zero) (#math-definition test () #pt-nat {expression})");
        run(&source, &[("query", &[])]);
    }
}

#[test]
fn constructor_lookup_fails_closed_for_missing_ambiguous_or_noninductive_targets() {
    run(
        r#"
      (#fn label () #u64 (#return 0u64))
      (#math-inductive Duplicate () () (#pt-type 0) ((same ()) (same ())))
      (#math-definition Ordinary () (#pt-type 0) #pt-nat)
      (#math-inductive Empty () () (#pt-type 0) ())
      (#math-definition duplicate-use () #pt-nat (#pt-construct Duplicate () () [[ambiguous|same]] ()))
      (#math-definition missing-use () #pt-nat (#pt-construct Empty () () [[missing|label]] ()))
      (#math-definition wrong-use () #pt-nat (#pt-construct [[noninductive|Ordinary]] () () [[wrong-label|label]] ()))
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
      (#math-definition NatAlias () (#pt-type 0) #pt-nat)
      (#math-definition refs ([[level|v]]) (#pt-type 0) (#pt-app (#pt-use [[alias|Imported]] ([[level-use|v]]))
                 (#pt-use [[path|./library.lim::NatAlias]] ())))
      (#math-definition constructed () #pt-nat (#pt-construct [[datatype|ImportedBox]] () () [[constructor|pack]] ()))
      (#alias certificate = ./library.lim::checked)
      (#theorem bridge (#universes) (#parameters) (#statement #pt-prop) (#proof (#pt-certificate [[procedural|certificate]])))
    "#,
        &[
            (
                "library.lim",
                r#"
              (#math-definition [[original|NatAlias]] (u) (#pt-type 0) #pt-nat)
              (#math-inductive [[box|Box]] () () (#pt-type 0) (([[pack|pack]] ())))
              (#theorem [[checked|checked]] (#proof-eq 0u64 0u64))
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
      (#gn emit () `((#math-definition nat-alias () (#pt-type 0) #pt-nat)
                    (#math-definition zero () (#pt-use nat-alias ()) #pt-zero)))
      (#generate emit)
      (#math-definition use-generated () (#pt-type 0) (#pt-use [[use|nat-alias]] ()))
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
      (#math-definition use-generated () (#pt-type 0) (#pt-use [[use|generated-nat]] ()))
    "#,
        &[(
            "generator.lim",
            "(#gn emit () `((#math-definition generated-nat () (#pt-type 0) #pt-nat)))",
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
                    let start = ["math-definition", "math-inductive", "theorem"]
                        .iter()
                        .find_map(|head| {
                            let prefix = format!("(#{head} ");
                            text.find(&format!("{prefix}{token} "))
                                .map(|start| start + prefix.len())
                        })
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
