mod support;
use std::{fs, process::Command};

fn run(source: &str) -> std::process::ExitStatus {
    let scratch = support::Scratch::new("reference-write-values");
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
fn one_word_aggregate_reference_writes_use_the_target_type() {
    for rhs in [
        "(#struct-literal Value ((number 42u64)))",
        "replacement",
        "(#call make ())",
        "(#block (#struct-literal Value ((number 42u64))))",
    ] {
        let source = format!(
            "(#struct Value ((number #u64)))
             (#fn make () Value (#return (#struct-literal Value ((number 42u64)))))
             (#fn write ((target (#ref-mut Value)) (replacement Value)) ()
               (#deref-set target {rhs}) (#return ()))
             (#fn main () #u64
               (#let-mut owner Value (#struct-literal Value ((number 1u64))))
               (#call write (: target (#borrow-mut owner)
                 : replacement (#struct-literal Value ((number 42u64)))))
               (#return (#get owner number)))"
        );
        assert_eq!(run(&source).code(), Some(42), "{source}");
    }
}

#[test]
fn zero_sized_reference_writes_preserve_adjacent_storage() {
    let source = "(#struct Empty ())
      (#struct Value ((empty Empty) (number #u64)))
      (#fn main () #u64
        (#let-mut owner Value (#struct-literal Value
          ((empty (#struct-literal Empty ())) (number 42u64))))
        (#let view (#ref-mut Value) (#borrow-mut owner))
        (#deref-set (#borrow-mut (#get view empty)) (#struct-literal Empty ()))
        (#return (#get view number)))";
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn zero_sized_reference_writes_evaluate_the_rhs() {
    let source = "(#struct Empty ())
      (#struct Value ((empty Empty) (number #u64)))
      (#fn fail () Empty (#assert false) (#return (#struct-literal Empty ())))
      (#fn main () #u64
        (#let-mut owner Value (#struct-literal Value
          ((empty (#struct-literal Empty ())) (number 42u64))))
        (#let view (#ref-mut Value) (#borrow-mut owner))
        (#deref-set (#borrow-mut (#get view empty)) (#call fail ()))
        (#return 42u64))";
    assert!(!run(source).success());
}
