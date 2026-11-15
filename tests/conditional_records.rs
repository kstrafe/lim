mod support;

use lim::{CompileConfig, Expr, TargetDescription};
use std::{process::Command, time::Duration};

fn trees(source: &str) -> Vec<Expr> {
    lim::parse_source_unit(source)
        .unwrap()
        .into_iter()
        .map(|node| node.expr)
        .collect()
}

fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}

fn function(body: &str) -> String {
    format!("#fn choose {{ #params = {{ flag = #bool; value = #u64; }}; #returns = #u64; #body = ({body}); }}")
}

fn run(source: &str, expected: i32, audited: bool) {
    let scratch = support::Scratch::new("conditional-records");
    let mut config = CompileConfig::default();
    if audited {
        config.set("contracts", "check");
    }
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &config,
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{}\n{source}", error.message));
    let output = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &output,
        &[],
        &[],
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(output), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(expected), "{source}\n{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn named_operands_lower_in_semantic_order_and_nested_call_arguments_are_visited() {
    for head in ["#if", "#if-valid"] {
        let source = function(&format!(
            "#return ({head} {{ #else = 0u64; #then = value; #condition = flag; }});"
        ));
        let canonical = lim::parse(&format!(
            "(#fn choose ((flag #bool) (value #u64)) #u64 (#return ({head} flag value 0u64)))"
        ))
        .unwrap()
        .remove(0)
        .expr;
        assert_eq!(trees(&source), vec![canonical]);
        check(&source).unwrap();
    }
    let source = r#"
#fn add {
  #params = { left = #u64; right = #u64; };
  #returns = #u64;
  #body: #return [#u64 #wrap; left + right];
}
#fn main {
  #params = {};
  #returns = #u64;
  #body: #return add {
    left = (#if { #condition = true; #then = 40u64; #else = 0u64; });
    right = (#if { #condition = false; #then = 0u64; #else = 2u64; });
  };
}
"#;
    run(source, 42, false);
}

#[test]
fn colon_branches_lower_to_existing_blocks_with_statements_and_values() {
    let source = r#"
#fn choose {
  #params = { flag = #bool; value = #u64; };
  #returns = #u64;
  #body:
    #return (#if {
      #condition = flag;
      #then:
        #let answer #u64 [#u64 #wrap; value + 2u64];
        #return answer;
      #else: #return 7u64;
    });
}
"#;
    let canonical = lim::parse(
        "(#fn choose ((flag #bool) (value #u64)) #u64 (#return (#if flag (#block (#let answer #u64 (#u64::add-wrap value 2u64)) (#return answer)) (#block (#return 7u64)))))",
    )
    .unwrap()
    .remove(0)
    .expr;
    assert_eq!(trees(source), vec![canonical]);
    check(source).unwrap();

    let scalar = function(
        "#return (#if { #condition = flag; #then: value; #else: 7u64; });",
    );
    let canonical = lim::parse(
        "(#fn choose ((flag #bool) (value #u64)) #u64 (#return (#if flag (#block value) (#block 7u64))))",
    )
    .unwrap()
    .remove(0)
    .expr;
    assert_eq!(trees(&scalar), vec![canonical]);
    check(&scalar).unwrap();
}

#[test]
fn malformed_records_report_the_reserved_field_and_its_source_location() {
    for head in ["#if", "#if-valid"] {
        for (fields, expected, location) in [
            ("", "record requires '#condition'", "{"),
            ("#condition = true;", "record requires '#then'", "{"),
            (
                "#condition = true; #then = 1u64;",
                "record requires '#else'",
                "{",
            ),
            (
                "#condition = true; #then = 1u64; #else = 0u64; #other = ();",
                "field '#other'",
                "#other",
            ),
            (
                "#condition = true; #then = 1u64; #else = 0u64; #then = 2u64;",
                "duplicate",
                "#then",
            ),
            (
                "condition = true; #then = 1u64; #else = 0u64;",
                "field 'condition'",
                "condition",
            ),
        ] {
            let expression = format!("{head} {{ {fields} }}");
            let source = function(&format!("#return ({expression});"));
            let error = lim::parse_source_unit(&source).unwrap_err();
            assert!(error.contains(expected), "{source}\n{error}");
            let offset = if location == "{" {
                source.find(&expression).unwrap() + head.len() + 1
            } else if expected == "duplicate" {
                source.rfind(location).unwrap()
            } else if location == "condition" {
                source.find("condition = true").unwrap()
            } else {
                source.find(location).unwrap()
            };
            assert!(error.starts_with(&format!("1:{}:", offset + 1)), "{error}");
        }
        let mixed = function(&format!(
            "#return ({head} {{ #condition = true; #then = 1u64; #else = 0u64; }} 2u64);"
        ));
        assert!(lim::parse_source_unit(&mixed)
            .unwrap_err()
            .contains("record must be its only operand"));
        let malformed = function(&format!(
            "#return ({head} ((#condition true) (#then 1u64 2u64) (#else 0u64)));"
        ));
        assert!(lim::parse_source_unit(&malformed)
            .unwrap_err()
            .contains("record requires key/value pairs"));
    }
}

#[test]
fn explicit_unit_else_and_statement_only_returns_keep_existing_rules() {
    let unit = r#"
#fn main {
  #params = {};
  #returns = ();
  #body:
    #if { #condition = true; #then = (); #else = (); };
    #return ();
}
"#;
    check(unit).unwrap();
    assert!(lim::parse_source_unit(&unit.replace("#else = ();", ""))
        .unwrap_err()
        .contains("requires '#else'"));
    for statement in ["(#return 42u64)", "(#break 42u64)"] {
        let source = function(&format!(
            "#return (#if {{ #condition = flag; #then = {statement}; #else = 0u64; }});"
        ));
        assert!(check(&source).unwrap_err().contains("only valid as a statement"));
    }
}

const PREDICATES: &str = r#"
#fn positive {
  #params = { value = #u64; };
  #returns = #bool;
  #body: #return [#u64; value > 0u64];
}
#fn under-100 {
  #params = { value = #u64; };
  #returns = #bool;
  #body: #return [#u64; value < 100u64];
}
#fn accept {
  #params = { value = #u64; };
  #returns = #u64;
  #requires:
    positive { value = value; };
    under-100 { value = value; };
  #body: #return value;
}
"#;

#[test]
fn only_the_valid_then_branch_receives_conjunction_evidence() {
    let source = format!(
        "{PREDICATES}\n{}",
        function("#return (#if-valid { #condition = (#bool::and (positive { value = value; }) (under-100 { value = value; })); #then = (accept { value = value; }); #else = 0u64; });")
    );
    check(&source).unwrap();
    for invalid in [
        source.replace("#if-valid", "#if"),
        source.replace("#bool::and", "#bool::or"),
        source.replace(
            "#then = (accept { value = value; }); #else = 0u64;",
            "#then = 0u64; #else = (accept { value = value; });",
        ),
        source.replace(
            "#then = (accept { value = value; }); #else = 0u64;",
            "#then = (accept { value = 42u64; }); #else = 0u64;",
        ),
    ] {
        assert_ne!(source, invalid);
        assert!(check(&invalid).unwrap_err().contains("missing evidence"));
    }
    let joined = format!(
        "{PREDICATES}\n{}",
        function("#if-valid { #condition = (#bool::and (positive { value = value; }) (under-100 { value = value; })); #then = (); #else = (); }; #return accept { value = value; };")
    );
    assert!(check(&joined).unwrap_err().contains("missing evidence"));
}

#[test]
fn branch_mutation_revokes_evidence_before_a_later_call() {
    let source = format!(
        r#"{PREDICATES}
#fn main {{
  #params = {{}};
  #returns = #u64;
  #body:
    #let-mut value #u64 42u64;
    #return (#if-valid {{
      #condition = (#bool::and (positive {{ value = value; }}) (under-100 {{ value = value; }}));
      #then:
        #set value 0u64;
        accept {{ value = value; }};
      #else = 0u64;
    }});
}}
"#
    );
    assert!(check(&source).unwrap_err().contains("missing evidence"));
    let unchanged = source.replace("#set value 0u64;", "#let unrelated #u64 0u64;");
    check(&unchanged).unwrap();
}

#[test]
fn conjunction_does_not_restore_evidence_invalidated_by_its_second_operand() {
    let source = format!(
        r#"{PREDICATES}
#fn accept-positive {{
  #params = {{ value = #u64; }};
  #returns = #u64;
  #requires: positive {{ value = value; }};
  #body: #return value;
}}
#fn overwrite {{
  #params = {{ value = (#ref-mut #u64); }};
  #returns = #bool;
  #body:
    #deref-set value 0u64;
    #return true;
}}
#fn main {{
  #params = {{}};
  #returns = #u64;
  #body:
    #let-mut value #u64 42u64;
    #return (#if-valid {{
      #condition = (#bool::and (positive {{ value = value; }}) (overwrite {{ value = (#borrow-mut value); }}));
      #then = (accept-positive {{ value = value; }});
      #else = 0u64;
    }});
}}
"#
    );
    assert!(check(&source).unwrap_err().contains("missing evidence"));
    let unchanged = source.replace("#deref-set value 0u64;", "#forget value;");
    check(&unchanged).unwrap();
}

#[test]
fn branch_scopes_and_exclusive_moves_follow_canonical_ownership() {
    let source = r#"
#struct Token (#linear) { number = #u64; }
#fn consume {
  #params = { token = Token; };
  #returns = #u64;
  #body:
    #let result #u64 (#get token number);
    #forget token;
    #return result;
}
#fn choose {
  #params = { flag = #bool; token = Token; };
  #returns = #u64;
  #body:
    #let result #u64 (#if {
      #condition = flag;
      #then = (consume { token = token; });
      #else = (consume { token = token; });
    });
    #return result;
}
"#;
    check(source).unwrap();
    let moved = source.replace(
        "    });\n    #return result;",
        "    });\n    #forget token;\n    #return result;",
    );
    assert_ne!(source, moved);
    assert!(check(&moved).is_err());
    let scope = function(
        "#if { #condition = flag; #then = (#block (#let hidden #u64 value) ()); #else = (); }; #return hidden;",
    );
    assert!(check(&scope).is_err());
    let borrow = r#"
#fn choose {
  #params = { flag = #bool; };
  #returns = #u64;
  #body:
    #let-mut value #u64 40u64;
    #if {
      #condition = flag;
      #then:
        #let view (#ref-mut #u64) (#borrow-mut value);
        #deref-set view 42u64;
        #forget view;
        ();
      #else = ();
    };
    #return value;
}
"#;
    check(borrow).unwrap();
    let overlapping = borrow.replace(
        "#let view (#ref-mut #u64) (#borrow-mut value);",
        "#let view (#ref-mut #u64) (#borrow-mut value); #let other (#ref-mut #u64) (#borrow-mut value); #deref-set other 0u64; #forget other;",
    );
    assert_ne!(borrow, overlapping);
    assert!(check(&overlapping).is_err());
}

#[test]
fn runtime_branches_preserve_returns_breaks_continue_divergence_and_evaluation_order() {
    let source = r#"
#fn tick {
  #params = { counter = (#ref-mut #u64); };
  #returns = #bool;
  #body:
    #deref-set counter [#u64 #wrap; (#deref counter) + 1u64];
    #return true;
}
#fn early {
  #params = {};
  #returns = #u64;
  #body:
    #if { #condition = true; #then: #return 7u64; #else = (); };
    #return 0u64;
}
#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let-mut count #u64 0u64;
    #let branch #u64 (#if {
      #else = (#panic);
      #then = 35u64;
      #condition = (tick { counter = (#borrow-mut count); });
    });
    #assert [#u64; count == 1u64];
    #let-mut iteration #u64 0u64;
    #let result #u64 (#loop
      (#set iteration [#u64 #wrap; iteration + 1u64])
      (#if {
        #condition = [#u64; iteration < 3u64];
        #then: #continue;
        #else: #break branch;
      }));
    #assert [#u64; iteration == 3u64];
    #return [#u64 #wrap; result + (early {})];
}
"#;
    for audited in [false, true] {
        run(source, 42, audited);
    }
}

#[test]
fn opaque_generator_data_stays_literal_but_function_templates_are_normalized() {
    assert!(lim::parse("'(#if { #opaque = (); })").is_ok());
    assert!(lim::parse_source_unit(&function(
        "#return '(#if { #opaque = (); });"
    ))
    .is_ok());
    let opaque = "#gn data {} '(#if { #opaque = (); })";
    let parsed = trees(opaque);
    let Expr::List(generator) = &parsed[0] else { panic!() };
    let Expr::Quote(data) = generator.last().unwrap() else { panic!() };
    assert!(matches!(data.as_ref(), Expr::List(parts) if parts.len() == 2));

    let source = r#"
#gn emit {} `((#fn answer () #u64
  (#return (#if { #condition = true; #then = 42u64; #else = 0u64; }))))
#generate emit {}
#fn main {
  #params = {};
  #returns = #u64;
  #body: #return answer {};
}
"#;
    let tree = trees(source);
    let Expr::List(generator) = &tree[0] else { panic!() };
    let Expr::QuasiQuote(forms) = generator.last().unwrap() else { panic!() };
    let Expr::List(forms) = forms.as_ref() else { panic!() };
    let Expr::List(function) = &forms[0] else { panic!() };
    let Expr::List(returned) = &function[4] else { panic!() };
    assert!(matches!(&returned[1], Expr::List(parts) if parts.len() == 4));
    run(source, 42, false);
}

#[test]
fn builtin_async_input_uses_the_same_function_normalization() {
    let source = r#"
#generate #async-fn {
  protocol = WorkAwait;
  waker = #u64;
  function = (#fn work ((choose #bool)) #u64
    (#if { #condition = choose; #then: #return 42u64; #else = (); })
    (#return 7u64));
}
"#;
    check(source).unwrap();
}

#[test]
fn formatting_preserves_layout_and_the_example_runs_with_contract_audits() {
    let source = include_str!("../examples/conditional_records.lim");
    let formatted = lim::format_source(source).unwrap();
    assert_eq!(trees(source), trees(&formatted));
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
    for audited in [false, true] {
        run(source, 42, audited);
    }
    let rejected_input = source.replace("#let seed #u64 21u64;", "#let seed #u64 0u64;");
    assert_ne!(source, rejected_input);
    run(&rejected_input, 0, true);
}
