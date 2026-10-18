mod support;

use lim::{check_types, parse_program, DiagnosticCode};
use std::{fs, process::Command, time::Duration};

fn check(source: &str) -> Result<(), String> {
    let program = parse_program(source).map_err(|error| error.to_string())?;
    check_types(&program).map_err(|error| error.to_string())
}

fn run(source: &str) -> std::process::ExitStatus {
    let scratch = support::Scratch::new("variant-is");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        64 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    support::run(&mut Command::new(binary), Duration::from_secs(5), 1024)
        .unwrap()
        .0
}

#[test]
fn variant_tests_borrow_linear_values_without_consuming_them() {
    let source = "(#enum Choice (#linear) ((Number 7 #u64) (Other 19 #u64)))

      (#type ChoiceAlias Choice)
      (#fn main () #u64
        (#let-mut value ChoiceAlias (Number 42u64))
        (#let shared (#ref Choice) (#borrow value))
        (#let first #bool (#variant-is shared Number))
        (#let again #bool (#variant-is shared Other))
        (#drop shared)
        (#let exclusive (#ref-mut Choice) (#borrow-mut value))
        (#let selected #bool (#variant-is exclusive Number))
        (#drop exclusive)
        (#let payload #u64 (#get-payload value Number 0))
        (#forget value)
        (#return (#if (#bool.&& first (#bool.&& (#bool.! again) selected))
          payload 0u64)))";
    check(source).unwrap();
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn pinned_shared_and_exclusive_references_and_explicit_discriminants_work() {
    let source = "(#enum Choice () ((Number 7 #u64) (Other 19 #u64)))
      (#fn main () #u64
        (#let-mut value Choice (Other 42u64))
        (#let shared (#pin-ref Choice) (#pin-borrow value))
        (#let wrong #bool (#variant-is shared Number))
        (#let right #bool (#variant-is shared Other))
        (#drop shared)
        (#let exclusive (#pin-ref-mut Choice) (#pin-borrow-mut value))
        (#let still-right #bool (#variant-is exclusive Other))
        (#drop exclusive)
        (#return (#if (#bool.&& (#bool.! wrong) (#bool.&& right still-right))
          (#get-payload value Other 0) 0u64)))";
    check(source).unwrap();
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn computed_receiver_is_evaluated_once() {
    let source = "(#enum Choice () ((Yes #u64) No))
      (#fn counted ((counter (#ref-mut #u64)) (value (#ref Choice))) (#ref Choice)
        (#deref-set counter (#u64.+.wrap (#deref counter) 1u64))
        (#return value))
      (#fn main () #u64
        (#let-mut counter #u64 0u64)
        (#let value Choice (Yes 42u64))
        (#let result #bool (#variant-is
          (#call counted (: counter (#borrow-mut counter) : value (#borrow value))) Yes))
        (#return (#if (#bool.&& result (#u64.== counter 1u64)) 42u64 0u64)))";
    check(source).unwrap();
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn builtin_sigils_do_not_reserve_the_unprefixed_function_name() {
    let source = "(#enum Choice () (Ready Stop))
      (#fn variant-is ((number #u64)) #u64 (#return number))
      (#fn main () #u64
        (#let value Choice Ready)
        (#assert (#variant-is (#borrow value) Ready))
        (#return (#call variant-is (: number 42u64))))";
    check(source).unwrap();
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn variant_test_rejects_invalid_operands_and_reports_the_expression_line() {
    let cases = [
        ("(#variant-is true Yes)", "true"),
        ("(#variant-is (#borrow record) Yes)", "(#borrow record)"),
        ("(#variant-is (#borrow value) Missing)", "Missing"),
        ("(#variant-is (#borrow value) Right)", "Right"),
        ("(#variant-is (#borrow value))", "#variant-is"),
    ];
    let scratch = support::Scratch::new("variant-is-diagnostics");
    for (expression, offending) in cases {
        let source = format!(
            "(#enum Choice () (Yes No))\n\
             (#enum Other () (Right))\n\
             (#struct Record () ())\n\
             (#fn main () #bool\n  \
               (#let value Choice Yes)\n  \
               (#let record Record (#struct-literal Record ()))\n  \
               {expression}\n  \
               (#return true))"
        );
        let input = scratch.path().join("bad.lim");
        fs::write(&input, &source).unwrap();
        let error = lim::compile_source_to_assembly(
            &source,
            &input,
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Type, "{error:?}");
        let span = error
            .span
            .expect("type diagnostic should have a source span");
        assert_eq!(&source[span.start..span.end], offending, "{error:?}");
    }
}

#[test]
fn exclusive_handles_in_fields_and_computed_blocks_remain_usable() {
    let source = "(#enum Choice (#linear) ((Number #u64) Empty))
      (#struct Holder () ((view (#ref-mut Choice))))
      (#type Alias Choice)
      (#fn main () #u64
        (#let-mut value Choice (Number 42u64))
        (#let holder Holder (#struct-literal Holder (: view (#borrow-mut value))))
        (#assert (#variant-is (#get holder view) Number))
        (#assert (#variant-is (#get holder view) Number))
        (#forget holder)
        (#let view (#ref-mut Alias) (#borrow-mut value))
        (#assert (#variant-is (#block view) Number))
        (#assert (#variant-is view Number))
        (#drop view)
        (#let result #u64 (#get-payload value Number 0))
        (#forget value) (#return result))";
    check(source).unwrap();
    assert_eq!(run(source).code(), Some(42));
}

#[test]
fn tag_tests_do_not_bypass_live_mutable_child_loans() {
    for receiver in ["parent", "(#block parent)"] {
        let expression = format!("(#variant-is {receiver} Number)");
        let source = format!(
            "(#enum Choice () ((Number #u64) Empty))
          (#fn main () #u64
            (#let-mut value Choice (Number 42u64))
            (#let parent (#pin-ref-mut Choice) (#pin-borrow-mut value))
            (#let child (#pin-ref-mut #u64) (#unsafe (#pin-get-payload-unchecked-mut parent Number)))
            {expression}
            (#let result #u64 (#deref child))
            (#drop child) (#drop parent) (#forget value) (#return result))"
        );
        let scratch = support::Scratch::new("variant-is-loan");
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("bad.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "#variant-is", "{error:?}");
    }
}
