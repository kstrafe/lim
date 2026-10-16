mod support;
use std::{fs, process::Command};

#[test]
fn enum_match_destinations_preserve_checked_nested_expressions() {
    for (ty, subject, yes, no) in [
        ("#bool", "true", "true", "false"),
        (
            "(#tuple #bool #u64)",
            "(#tuple true 1u64)",
            "(#tuple true _)",
            "_",
        ),
        (
            "(#array #bool 2)",
            "(#array-of true false)",
            "(#array true _)",
            "_",
        ),
        (
            "(#array #bool 10)",
            "(#array-repeat true)",
            "(#array true _ _ _ _ _ _ _ _ _)",
            "_",
        ),
    ] {
        let source = format!(
            "(#enum E () ((Value #u64) (Padding (#array #u64 10))))
          (#fn answer ((value #u64)) #u64 (#return value))
          (#fn make ((choose {ty})) E
            (#return (#match (#clone choose)
              (#case {yes} (Value (#match (#u64.== 1u64 1u64)
                (#case true (#call answer (: value 42u64))) (#case false 0u64))))
              (#case {no} (Value 0u64)))))
          (#fn main () #u64
            (#let subject {ty} {subject})
            (#let-mut value E (Value 0u64))
            (#set value (#match (#clone subject)
              (#case {yes} (#call make (: choose (#clone subject))))
              (#case {no} (Value 0u64))))
            (#return (#get-payload value Value 0)))"
        );
        assert_eq!(run(&source).code(), Some(42), "{source}");
    }
}

fn run(source: &str) -> std::process::ExitStatus {
    let scratch = support::Scratch::new("owned-enum-payloads");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Command::new(binary).status().unwrap()
}

#[test]
fn owned_and_computed_payloads_preserve_values_and_register_classes() {
    for (ty, value, result) in [
        ("#u64", "42u64", "(#get-payload SOURCE Value 0)"),
        (
            "#u128",
            "42u128",
            "(#as (#get-payload SOURCE Value 0) #u64)",
        ),
        (
            "#f32",
            "(#literal #f32 42.0)",
            "(#if (#f32.== (#get-payload SOURCE Value 0) (#literal #f32 42.0)) 42u64 0u64)",
        ),
        (
            "#f64",
            "(#literal #f64 42.0)",
            "(#if (#f64.== (#get-payload SOURCE Value 0) (#literal #f64 42.0)) 42u64 0u64)",
        ),
        (
            "(#tuple #u64 #u64)",
            "(#tuple 42u64 1u64)",
            "(#get (#get-payload SOURCE Value 0) 0)",
        ),
    ] {
        for source in ["owner", "(#call make ())"] {
            let result = result.replace("SOURCE", source);
            let program = format!(
                "(#enum E () ((Value {ty}) Other))
                 (#fn make () E (#return (Value {value})))
                 (#fn main () #u64
                   (#let owner E (Value {value}))
                   (#return {result}))"
            );
            assert_eq!(run(&program).code(), Some(42), "{program}");
        }
    }
}

#[test]
fn owned_payload_checks_discriminant_and_evaluates_unit_receivers() {
    let inactive = "(#enum E () ((Value #u64) Other))
      (#fn main () #u64
        (#let owner E Other)
        (#return (#get-payload owner Value 0)))";
    assert!(!run(inactive).success());
    for words in [1, 8] {
        let fields = "#u64 ".repeat(words);
        let value_source = format!(
            "(#enum E () ((Value #u64) (Other {fields})))
             (#fn make () E (#return (Value 42u64)))
             (#fn main () #u64
               (#return (#get-payload (#call make ()) Value 0)))"
        );
        assert_eq!(run(&value_source).code(), Some(42));
        let source = format!(
            "(#enum E () ((Value ()) (Other {fields})))
             (#fn make () E (#assert false) (#return (Value ())))
             (#fn main () #u64
               (#forget (#get-payload (#call make ()) Value 0))
               (#return 42u64))"
        );
        assert!(!run(&source).success());
    }
}
