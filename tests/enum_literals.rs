mod support;

use lim::{check_types, parse_program};
use std::{fs, process::Command, time::Duration};

fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}

fn run(source: &str, expected: i32) {
    check(source).unwrap();
    let scratch = support::Scratch::new("enum-literal");
    let input = scratch.path().join("main.lim");
    let output = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(input)
            .arg("-o")
            .arg(&output),
        Duration::from_secs(30),
        65536,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) =
        support::run(&mut Command::new(output), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(expected), "{source}: {stderr:?}");
}

#[test]
fn explicit_payload_and_fieldless_values_keep_patterns_unchanged() {
    for (value, expected) in [
        ("(#enum-literal Answer.Value 42u64)", 42),
        ("(#enum-literal Answer.Empty)", 7),
    ] {
        run(&format!("#enum Answer () ((Answer.Value 18446744073709551615 #u64) (Answer.Empty 7))
#type Result Answer
#fn make () Result (#return {value})
#fn main () #u64 (#let answer Result (#call make ()))
              (#return (#match answer (#case (Answer.Value number) number) (#case Answer.Empty 7u64)))\n"), expected);
    }
}

#[test]
fn payload_computation_is_evaluated_once_and_nested_literals_work() {
    run(
        "#enum Inner () ((Inner.Number #u64))
#struct Row () ((item Inner))
#enum Outer () ((Outer.Wrapped Row))
#fn main () #u64 (#let-mut count #u64 0u64)
          (#let value Outer (#enum-literal Outer.Wrapped
            (#struct-literal Row ((item (#enum-literal Inner.Number
              (#block (#set count (#u64::add-wrap count 1u64)) 41u64)))))))
          (#let-else (Outer.Wrapped row) value (#else (#return 0u64)))
          (#return (#match (#get row item) (#case (Inner.Number number) (#u64::add-wrap count number))))\n",
        42,
    );
}

#[test]
fn malformed_and_mismatched_constructions_are_rejected() {
    for value in [
        "(#enum-literal)",
        "(#enum-literal (Maybe.Some))",
        "(#enum-literal missing)",
        "(#enum-literal Maybe.Some)",
        "(#enum-literal Maybe.None 1u64)",
        "(#enum-literal Maybe.Some 1u64 2u64)",
        "(#enum-literal Maybe.Some false)",
        "(#enum-literal Maybe)",
        "(#enum-literal maker)",
    ] {
        let source = format!(
            "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#fn maker () Maybe (#return (#enum-literal Maybe.None))
#fn main () #u64 (#let value Maybe {value}) (#forget value) (#return 0u64)\n"
        );
        assert!(check(&source).is_err(), "{value}");
    }
    assert!(check(
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#fn main () #u64 (#return (#match (#enum-literal Maybe.None)
          (#case (#enum-literal Maybe.Some value) value) (#case _ 0u64)))\n"
    )
    .is_err());
}

#[test]
fn reference_payloads_keep_their_origin_and_exclusivity() {
    let source = "#enum Holder () ((Holder.Held (#ref-mut #u64)))
#fn main () #u64 (#let-mut owner #u64 42u64)
          (#let holder Holder (#enum-literal Holder.Held (#borrow-mut owner)))
          (#let-else (Holder.Held reference) holder (#else (#return 0u64)))
          (#set owner 0u64) (#return (#deref reference))\n";
    assert!(check(source).unwrap_err().contains("borrow"));
    let escaping = "#enum Holder () ((Holder.Held (#ref #u64)))
#fn escape () Holder (#let local #u64 42u64)
          (#return (#enum-literal Holder.Held (#borrow local)))\n";
    assert!(check(escaping).is_err());
}

#[test]
fn explicit_literals_work_inside_async_generator_functions() {
    run(
        "#enum Answer () ((Answer.Number #u64) Answer.Empty)
#generate #async-fn-pinned ((protocol Work::Await) (waker #u64)
          (function (#fn work () Answer (#return (#enum-literal Answer.Number 42u64)))))
#fn main () #u64 (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ()))
          (#let-else (Work::Poll.Ready value)
            (#call Work::poll ((task (#pin-borrow-mut task)) (waker (#borrow waker))))
            (#else (#forget task) (#return 0u64)))
          (#forget task)
          (#return (#match value (#case (Answer.Number number) number) (#case Answer.Empty 0u64)))\n",
        42,
    );
}

#[test]
fn globals_unit_payloads_and_same_spelled_user_functions_are_distinct() {
    run(
        "#enum Answer () ((Answer.Number #u64) (Answer.Marker ()))
#let gLOBAL Answer (#enum-literal Answer.Number 41u64)
#fn enum-literal ((value #u64)) #u64 (#return value)
#fn main () #u64
          (#let marker Answer (#enum-literal Answer.Marker ()))
          (#forget marker)
          (#return (#match gLOBAL (#case (Answer.Number value)
            (#u64::add-wrap value (#call enum-literal ((value 1u64)))))
            (#case (Answer.Marker unit) (#block (#forget unit) 0u64))))\n",
        42,
    );
}

#[test]
fn imported_and_user_generated_enum_literals_keep_concrete_variant_identity() {
    let scratch = support::Scratch::new("enum-literal-import");
    fs::write(
        scratch.path().join("module.lim"),
        "#enum Answer () ((Answer.Value #u64) Answer.Empty)
#fn make () Answer (#return (#enum-literal Answer.Value 42u64))\n",
    )
    .unwrap();
    let source =
        "#alias Ext@make = ./module.lim::make
#alias Ext@Answer = ./module.lim::Answer
#fn main () #u64 (#return (#match (#call Ext@make ())
          (#case (Ext@Answer.Value value) value) (#case Ext@Answer.Empty 0u64)))\n";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    check_types(&program).unwrap();
    lim::generate_assembly(&program).unwrap();
    run(
        "#enum Answer () ((Answer.Value #u64) Answer.Empty)
#gn emit (name) `((#fn ,name () Answer (#return (#enum-literal Answer.Value 42u64))))
#generate emit make
#fn main () #u64 (#return (#match (#call make ())
          (#case (Answer.Value value) value) (#case Answer.Empty 0u64)))\n",
        42,
    );
}
