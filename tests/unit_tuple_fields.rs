mod support;
use std::{fs, process::Command};

fn run(source: &str) -> std::process::ExitStatus {
    let scratch = support::Scratch::new("unit-tuple-fields");
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
fn unit_tuple_fields_need_no_slot_or_register() {
    let source = r#"
      (#let GLOBAL (#tuple #u64 ()) (#tuple (#tuple #u64 ()) 42u64 ()))
      (#fn main () #u64
        (#let local (#tuple () #u64 ()) (#tuple (#tuple () #u64 ()) () 42u64 ()))
        (#get local 0)
        (#get local 2)
        (#get GLOBAL 1)
        (#return (#get local 1)))
    "#;
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn zero_word_aggregate_locals_can_be_enum_payloads() {
    for (declarations, ty, value) in [
        ("", "(#tuple () ())", "(#tuple (#tuple () ()) () ())"),
        ("", "(#array () 2)", "(#array-of (#array () 2) () ())"),
        ("(#struct Empty ())", "Empty", "(#struct-literal Empty (:))"),
    ] {
        let source = format!(
            "{declarations}
          (#enum Outcome ((Done {ty})))
          (#fn make () Outcome
            (#let empty {ty} {value}) (#return (Done empty)))
          (#fn main () #u64
            (#return (#match (#call make (:))
              (#case (Done value) (#block value 42u64)))))"
        );
        assert_eq!(run(&source).code(), Some(42), "{source}");
    }
}

#[test]
fn unit_tuple_projection_evaluates_small_and_indirect_receivers() {
    for words in [1, 8] {
        let fields = "#u64 ".repeat(words);
        let values = "42u64 ".repeat(words);
        let source = format!(
            r#"
          (#fn make () (#tuple {fields} ())
            (#assert false)
            (#return (#tuple (#tuple {fields} ()) {values} ())))
          (#fn main () #u64
            (#get (#call make ()) {words})
            (#return 42u64))
        "#
        );
        let status = run(&source);
        assert!(!status.success());
        assert_ne!(status.code(), Some(42));
    }
}
