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
            "#enum E () ((E.Value #u64) (E.Padding (#array #u64 10)))
#fn answer {{
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}}
#fn make {{
  #params = ((choose {ty}));
  #returns = E;
  #body = (
              (#return (#match (#clone choose)
                (#case {yes} (E.Value (#match (#u64::eq 1u64 1u64)
                  (#case true (#call answer ((value 42u64)))) (#case false 0u64))))
                (#case {no} (E.Value 0u64))))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let subject {ty} {subject})
              (#let-mut value E (E.Value 0u64))
              (#set value (#match (#clone subject)
                (#case {yes} (#call make ((choose (#clone subject)))))
                (#case {no} (E.Value 0u64))))
              (#return (#get-payload value E.Value 0))\n  );\n}}\n"
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
        ("#u64", "42u64", "(#get-payload SOURCE E.Value 0)"),
        (
            "#u128",
            "42u128",
            "(#as (#get-payload SOURCE E.Value 0) #u64)",
        ),
        (
            "#f32",
            "(#literal #f32 42.0)",
            "(#if (#f32::eq (#get-payload SOURCE E.Value 0) (#literal #f32 42.0)) 42u64 0u64)",
        ),
        (
            "#f64",
            "(#literal #f64 42.0)",
            "(#if (#f64::eq (#get-payload SOURCE E.Value 0) (#literal #f64 42.0)) 42u64 0u64)",
        ),
        (
            "(#tuple #u64 #u64)",
            "(#tuple 42u64 1u64)",
            "(#get (#get-payload SOURCE E.Value 0) 0)",
        ),
    ] {
        for source in ["owner", "(#call make ())"] {
            let result = result.replace("SOURCE", source);
            let program = format!(
                "#enum E () ((E.Value {ty}) E.Other)
#fn make {{
  #params = ();
  #returns = E;
  #body = ( (#return (E.Value {value}))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                     (#let owner E (E.Value {value}))
                     (#return {result})\n  );\n}}\n"
            );
            assert_eq!(run(&program).code(), Some(42), "{program}");
        }
    }
}

#[test]
fn owned_payload_checks_discriminant_and_evaluates_unit_receivers() {
    let inactive = "#enum E () ((E.Value #u64) E.Other)
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let owner E E.Other)
          (#return (#get-payload owner E.Value 0))\n  );\n}\n";
    assert!(!run(inactive).success());
    for words in [1, 8] {
        let fields = format!("(#tuple {})", "#u64 ".repeat(words));
        let value_source = format!(
            "#enum E () ((E.Value #u64) (E.Other {fields}))
#fn make {{
  #params = ();
  #returns = E;
  #body = ( (#return (E.Value 42u64))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                 (#return (#get-payload (#call make ()) E.Value 0))\n  );\n}}\n"
        );
        assert_eq!(run(&value_source).code(), Some(42));
        let source = format!(
            "#enum E () ((E.Value ()) (E.Other {fields}))
#fn make {{
  #params = ();
  #returns = E;
  #body = ( (#assert false) (#return (E.Value ()))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                 (#forget (#get-payload (#call make ()) E.Value 0))
                 (#return 42u64)\n  );\n}}\n"
        );
        assert!(!run(&source).success());
    }
}

#[test]
fn enum_variants_reject_multiple_payload_types() {
    let source = "#enum E () ((E.Pair #u64 #u64))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 0u64)\n  );\n}\n";
    assert!(lim::parse_program(source)
        .unwrap_err()
        .to_string()
        .contains("at most one payload type"));
}
