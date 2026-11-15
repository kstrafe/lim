mod support;

use std::{process::Command, time::Duration};

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("pinned-cases");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("pinned-cases-native");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = compile(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(
        status.code(),
        Some(expected),
        "status={status:?} stderr={stderr:?}\n{source}"
    );
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

fn reject(source: &str, expected: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|error| {
        panic!("fixture must parse before semantic rejection: {error}\n{source}")
    });
    let error = lim::check_types(&program).expect_err("fixture should fail semantic checking");
    assert!(
        error.contains(expected),
        "expected {expected:?}, got {error}\n{source}"
    );
}

fn reject_any(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|error| {
        panic!("fixture must parse before semantic rejection: {error}\n{source}")
    });
    let error = lim::check_types(&program).err().unwrap_or_else(|| {
        panic!("fixture should be rejected during semantic checking:\n{source}")
    });
    assert!(
        !error.is_empty(),
        "semantic rejection needs a diagnostic\n{source}"
    );
}

fn reject_program(source: &str, expected: &str) {
    lim::parse_source_unit(source).unwrap_or_else(|error| panic!("fixture must parse: {error}\n{source}"));
    let error = lim::parse_program(source).expect_err("program should fail semantic validation");
    assert!(
        error.contains(expected),
        "expected {expected:?}, got {error}\n{source}"
    );
}

#[test]
fn shared_and_exclusive_payload_projection_runs_on_stack_and_heap() {
    let source = include_str!("../examples/pinned_cases.lim");
    run(source, 83);

    let heap = source
        .replace(
            "(#let-mut choice Choice (Choice.Full (#struct-literal Payload ((value 41u64)))))",
            "(#let allocation (#ptr-mut Choice) (#unsafe (#linux-syscall (#ptr-mut Choice) 9usize\n            (0usize (#size-of Choice) 3usize 34usize -1i64 0usize))))\n  (#let-mut choice (#pin-own Choice) (#unsafe (#pin-own-of allocation\n    (Choice.Full (#struct-literal Payload ((value 41u64)))))))",
        )
        .replace("(#pin choice)", "(#pin-own-borrow-mut choice)")
        .replace(
            "(#forget choice)",
            "(#let released (#ptr-mut Choice) (#unsafe (#pin-release choice)))\n  (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (released (#size-of Choice)))) 0i64))",
        );
    run(&heap, 83);
}

#[test]
fn pinned_match_evaluates_input_once_and_supports_guards_and_nested_projection() {
    run(
        "#struct Payload () ((value #u64))
#enum Inner () ((Inner.Empty) (Inner.Full Payload))
#enum Outer () ((Outer.Nested Inner) (Outer.Other))
#fn select {
  #params = ((choice (#pin-ref-mut Outer)) (count (#ref-mut #u64)));
  #returns = #u64;
  #body = (
             (#return (#match (#block (#deref-set count (#u64::add-wrap (#deref count) 1u64)) choice)
               (#case-pin-mut (Outer.Nested inner)
                 (#match inner
                   (#case-pin-mut (Inner.Full guarded) (#when (#u64::eq (#get guarded value) 0u64)) 0u64)
                   (#case-pin-mut (Inner.Full payload) (#get payload value))
                   (#case-pin-mut Inner.Empty 0u64)))
               (#case-pin-mut Outer.Other 0u64)))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let-mut count #u64 0u64)
             (#let-mut value Outer (Outer.Nested (Inner.Full (#struct-literal Payload ((value 42u64))))))
             (#let pin (#pin-ref-mut Outer) (#pin value))
             (#let answer #u64 (#call select ((choice (#pin-borrow-mut (#deref pin))) (count (#borrow-mut count)))))
             (#assert (#u64::eq count 1u64)) (#forget pin) (#forget value) (#return answer)\n  );\n}\n",
        42,
    );
}

#[test]
fn exclusive_pinned_match_requires_exclusive_input_and_local_escape_is_rejected() {
    reject(
        "#enum Choice () ((Choice.Full #u64))
#fn bad {
  #params = ((choice (#pin-ref Choice)));
  #returns = #u64;
  #body = (
             (#return (#match choice (#case-pin-mut (Choice.Full payload) (#deref payload))))\n  );\n}\n",
        "mutable",
    );
    let local_escape = "#enum Choice () ((Choice.Full #u64))
#fn bad {
  #params = ();
  #returns = (#pin-ref #u64);
  #body = (
             (#let-mut choice Choice (Choice.Full 42u64))
             (#let pin (#pin-ref-mut Choice) (#pin choice))
             (#return (#match pin (#case-pin (Choice.Full payload) payload)))\n  );\n}\n";
    reject(local_escape, "local");
    reject(
        &local_escape.replace("(#match pin", "(#match (#block pin)"),
        "local",
    );
}

#[test]
fn pinned_match_keeps_standard_exhaustiveness_and_pattern_restrictions() {
    let prefix = "#struct Pair () ((left #u64) (right #u64))\n#enum Choice () ((Choice.Full Pair) Choice.Empty)\n#fn bad {\n  #params = ((choice (#pin-ref Choice)));\n  #returns = #u64;\n  #body = (";
    reject_any(&format!(
        "{prefix}(#return (#match choice (#case-pin (Choice.Full (Pair left right)) left) (#case-pin Choice.Empty 0u64)))\n  );\n}}"
    ));
    reject_any(&format!(
        "{prefix}(#return (#match choice (#case-pin (Choice.Full payload) 1u64) (#case-pin (Choice.Full again) 2u64) (#case-pin Choice.Empty 0u64)))\n  );\n}}"
    ));
    reject_any(&format!(
        "{prefix}(#return (#match choice (#case-pin (Choice.Full payload) (#get payload left))))\n  );\n}}"
    ));
    reject_any(&format!(
        "{prefix}(#return (#match choice (#case (Choice.Full payload) (#get payload left)) (#case _ 0u64)))\n  );\n}}"
    ));
    reject_program(
        "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#fn bad {
  #params = ((choice (#pin-ref Choice)));
  #returns = #u64;
  #body = (
             (#return (#match choice
               (#case-pin (Choice.Full choice) (#deref choice))
               (#case-pin Choice.Empty 0u64)))\n  );\n}\n",
        "shadows",
    );
    reject_any(
        "#struct Payload () ((value #u64))
#enum Choice () ((Choice.Full Payload) Choice.Empty)
#fn bad {
  #params = ((choice (#pin-ref Choice)));
  #returns = #u64;
  #body = (
             (#return (#match choice
               (#case-pin (Choice.Full payload)
                 (#block (#pin-set-field payload value 0u64) (#get payload value)))
               (#case-pin Choice.Empty 0u64)))\n  );\n}\n",
    );
}

#[test]
fn returned_payload_reference_keeps_the_callers_lifetime() {
    let source = "#enum Choice () ((Choice.Full #u64))
#fn payload {
  #params = ((choice (#pin-ref Choice)));
  #returns = (#pin-ref #u64);
  #body = (
             (#return (#match choice
               (#case-pin (Choice.Full value) value)
               (#case _ (#unreachable))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let value Choice (Choice.Full 42u64))
             (#let pin (#pin-ref Choice) (#pin-borrow value))
             (#let result (#pin-ref #u64) (#call payload ((choice pin))))
             (#let answer #u64 (#deref result)) (#forget result) (#forget pin) (#forget value)
             (#return answer)\n  );\n}\n";
    run(source, 42);
    run(
        &source.replace("(#match choice", "(#match (#block choice)"),
        42,
    );
    let computed = format!(
        "#fn identity {{\n  #params = ((input (#pin-ref Choice)));\n  #returns = (#pin-ref Choice);\n  #body = ( (#return input)\n  );\n}}\n{}",
        source.replace(
            "(#match choice",
            "(#match (#call identity ((input choice)))"
        )
    );
    run(&computed, 42);
}

#[test]
fn pinned_payload_match_handles_large_discriminants_and_early_return() {
    run(
        "#enum Wide () ((Wide.Empty 4294967295) (Wide.Full 4294967296 #u64))
#fn result {
  #params = ((value (#pin-ref Wide)));
  #returns = #u64;
  #body = (
             (#return (#match value
               (#case-pin (Wide.Full payload) (#block (#return (#deref payload)) (#unreachable)))
               (#case-pin Wide.Empty 0u64)))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let value Wide (Wide.Full 42u64))
             (#let pin (#pin-ref Wide) (#pin-borrow value))
             (#let answer #u64 (#call result ((value pin))))
             (#forget pin) (#forget value) (#return answer)\n  );\n}\n",
        42,
    );
}

#[test]
fn mutable_payload_reborrow_conflicts_with_parent_reborrow() {
    let source = "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#fn touch {
  #params = ((choice (#pin-ref-mut Choice)));
  #returns = #u64;
  #body = (
             (#return (#match choice
               (#case-pin-mut (Choice.Full value) (#deref value))
               (#case-pin-mut Choice.Empty 0u64)))
  );
}
#fn bad {
  #params = ((choice (#pin-ref-mut Choice)));
  #returns = #u64;
  #body = (
             (#return (#match choice
               (#case-pin-mut (Choice.Full payload)
                 (#block (#call touch ((choice choice))) (#deref payload)))
               (#case-pin-mut Choice.Empty 0u64)))\n  );\n}\n";
    reject_any(source);
    reject_any(&source.replace("(#match choice", "(#match (#block choice)"));
    let computed =
        format!(
        "#fn identity {{\n  #params = ((input (#pin-ref-mut Choice)));\n  #returns = (#pin-ref-mut Choice);\n  #body = ( (#return input)\n  );\n}}\n{}",
        source.replace("(#match choice", "(#match (#call identity ((input choice)))")
    );
    reject_any(&computed);
}

#[test]
fn async_generator_body_can_match_a_pinned_enum_payload() {
    let source = "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#enum Child (#linear) ((Child.Start #u64) (Child.Resume #u64))
#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
             (#return (#match task
               (#case (Child.Start value) (ChildPoll.Pending (Child.Resume value)))
               (#case (Child.Resume value) (ChildPoll.Ready value))))
  );
}
#syntax StepAwait (#u64 Child ChildPoll.Pending ChildPoll.Ready child-poll)
#generate #async-fn ((protocol WorkAwait) (waker #u64)
             (function (#fn work ((choice (#pin-ref-mut Choice)) (seed #u64)) #u64
               (#let selected #u64 (#match choice
                 (#case-pin-mut (Choice.Full payload) (#when (#u64::eq (#deref payload) 42u64)) (#deref payload))
                 (#case _ 0u64)))
               (#forget choice)
               (#return (#await StepAwait (Child.Start selected))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let-mut choice Choice (Choice.Full 42u64))
             (#let pin (#pin-ref-mut Choice) (#pin choice))
             (#let waker #u64 0u64)
             (#let first Work::Poll (#call Work::poll
               ((task (#call work ((choice (#pin-borrow-mut (#deref pin))) (seed 42u64)))) (waker (#borrow waker)))))
             (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
             (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
               (#case (Work::Poll.Ready value) value)
               (#case (Work::Poll.Pending child) (#block (#forget child) (#unreachable)))))
             (#forget pin) (#forget choice)
             (#return answer)\n  );\n}\n";
    run(source, 42);
    run(
        &source.replace("(Choice.Full 42u64)", "(Choice.Full 41u64)"),
        0,
    );
    run(&source.replace("(Choice.Full 42u64)", "Choice.Empty"), 0);
    let shared = source
        .replace("#pin-ref-mut Choice", "#pin-ref Choice")
        .replace("#case-pin-mut", "#case-pin")
        .replace("(#pin choice)", "(#pin-shared choice)")
        .replace(
            "(#pin-borrow-mut (#deref pin))",
            "(#pin-borrow (#deref pin))",
        );
    run(&shared, 42);
}

#[test]
fn byte_payload_write_and_aggregate_match_result_run_on_stack_and_heap() {
    let source = "#struct Payload () ((wide #u64) (narrow #u8))
#struct Summary () ((narrow #u8) (wide #u64))
#enum Choice () ((Choice.Byte #u8) (Choice.Wide Payload) Choice.Empty)
#fn summarize {
  #params = ((choice (#pin-ref-mut Choice)));
  #returns = Summary;
  #body = (
             (#return (#match choice
               (#case-pin-mut (Choice.Byte byte)
                 (#block
                   (#unsafe (#pin-write byte 201u8))
                   (#struct-literal Summary ((narrow (#deref byte)) (wide 42u64)))))
               (#case-pin-mut (Choice.Wide payload)
                 (#struct-literal Summary ((narrow (#get payload narrow)) (wide (#get payload wide)))))
               (#case-pin-mut Choice.Empty
                 (#struct-literal Summary ((narrow 0u8) (wide 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let-mut choice Choice (Choice.Byte 17u8))
             (#let pin (#pin-ref-mut Choice) (#pin choice))
             (#let result Summary (#call summarize ((choice (#pin-borrow-mut (#deref pin))))))
             (#assert (#u8::eq (#get result narrow) 201u8))
             (#assert (#u64::eq (#get result wide) 42u64))
             (#forget pin) (#forget choice) (#return 42u64)\n  );\n}\n";
    run(source, 42);

    let heap = source
        .replace(
            "(#let-mut choice Choice (Choice.Byte 17u8))",
            "(#let allocation (#ptr-mut Choice) (#unsafe (#linux-syscall (#ptr-mut Choice) 9usize\n            (0usize (#size-of Choice) 3usize 34usize -1i64 0usize))))\n  (#let-mut choice (#pin-own Choice) (#unsafe (#pin-own-of allocation (Choice.Byte 17u8))))",
        )
        .replace("(#pin choice)", "(#pin-own-borrow-mut choice)")
        .replace(
            "(#forget choice)",
            "(#let released (#ptr-mut Choice) (#unsafe (#pin-release choice)))\n  (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (released (#size-of Choice)))) 0i64))",
        );
    run(&heap, 42);
}
