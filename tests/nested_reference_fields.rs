mod support;
use std::{fs, process::Command};

fn run(source: &str) -> std::process::ExitStatus {
    let scratch = support::Scratch::new("nested-reference-fields");
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
fn computed_nested_one_word_aggregates_use_the_value_register() {
    let source = "#struct Inner () ((value #u64))
#struct Outer () ((prefix ()) (inner Inner))
#fn main () #u64
          (#let outer Outer (#struct-literal Outer
            ((prefix ()) (inner (#struct-literal Inner ((value 42u64)))))))
          (#let result #u64 (#get (#get (#block (#clone outer)) inner) value))
          (#forget outer) (#return result)\n";
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn computed_nested_mutable_reference_fields_support_writes() {
    let source = "#struct Owner () ((value #u64))
#struct View () ((item (#ref-mut #u64)))
#struct Wrapper () ((view View))
#fn main () #u64
          (#let-mut owner Owner (#struct-literal Owner ((value 1u64))))
          (#let parent (#ref-mut Owner) (#borrow-mut owner))
          (#let view View (#struct-literal View ((item (#borrow-mut (#get parent value))))))
          (#let wrapper Wrapper (#struct-literal Wrapper ((view view))))
          (#deref-set (#get (#get wrapper view) item) 42u64)
          (#let result #u64 (#deref (#get (#get wrapper view) item)))
          (#forget wrapper) (#drop parent) (#forget owner) (#return result)\n";
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn zero_sized_computed_fields_still_evaluate_the_container() {
    for trap in [false, true] {
        let effect = if trap { "(#assert false)" } else { "" };
        let source = format!(
            "#struct Empty () ()
#struct Outer () ((empty Empty))
#fn main () #u64
                 (#let empty Empty (#get
                   (#block {effect} (#struct-literal Outer ((empty (#struct-literal Empty ())))))
                   empty))
                 (#forget empty) (#return 42u64)\n"
        );
        let status = run(&source);
        if trap {
            assert!(!status.success());
        } else {
            assert_eq!(status.code(), Some(42));
        }
    }
}
