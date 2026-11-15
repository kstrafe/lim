mod support;

use std::{process::Command, time::Duration};

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("borrowed-cases");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("borrowed-cases-native");
    let assembly = compile(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
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
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("fixture must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("fixture should fail semantic checking");
    assert!(
        error.contains(expected),
        "expected {expected:?}, got {error}\n{source}"
    );
}

fn reject_any(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("fixture must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("fixture should fail semantic checking");
    assert!(
        !error.is_empty(),
        "semantic rejection needs a diagnostic\n{source}"
    );
}

#[test]
fn borrowed_payload_matches_and_updates_in_place() {
    let source = include_str!("../examples/borrowed_cases.lim");
    run(source, 82);
    run(
        &source
            .replace(
                "inspect ((choice (#ref Choice)))",
                "inspect ((choice (#ref-mut Choice)))",
            )
            .replace(
                "inspect (($ (#borrow choice)))",
                "inspect (($ (#borrow-mut choice)))",
            ),
        82,
    );
    let heap = source
        .replace(
            "(#let-mut choice Choice (Choice.Full (#struct-literal Payload ((value 41u64) (narrow 7u8)))))",
            "(#let pointer (#ptr-mut Choice) (#unsafe (#linux-syscall (#ptr-mut Choice) 9usize (0usize 4096usize 3usize 34usize -1i64 0usize))))\n  (#let-mut anchor #u64 0u64)\n  (#let choice (#ref-mut Choice) (#unsafe (#ptr-borrow-mut (#borrow-mut anchor) pointer)))\n  (#deref-set choice (Choice.Full (#struct-literal Payload ((value 41u64) (narrow 7u8)))))",
        )
        .replace("(#borrow choice)", "choice")
        .replace("(#borrow-mut choice)", "choice")
        .replace("(#call inspect (($ choice)))", "(#call inspect ((choice (#borrow (#deref choice)))))")
        .replace(
            "(#return (#u64::add-wrap observed changed))",
            "(#forget choice)\n  (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))\n  (#return (#u64::add-wrap observed changed))",
        );
    run(&heap, 82);
}

#[test]
fn borrowed_match_evaluates_receiver_once() {
    run(
        "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#fn main () #u64
             (#let value Choice (Choice.Full 42u64))
             (#let-mut calls #u64 0u64)
             (#let answer #u64 (#match (#block
               (#deref-set (#borrow-mut calls) (#u64::add-wrap calls 1u64))
               (#borrow value))
               (#case-ref (Choice.Full payload) (#when false) 0u64)
               (#case-ref (Choice.Full payload) (#when true) (#deref payload))
               (#case-ref Choice.Empty 0u64)
               (#case _ 0u64)))
             (#assert (#u64::eq calls 1u64))
             (#return answer)\n",
        42,
    );
}

#[test]
fn borrowed_payload_reference_retains_owner_lifetime() {
    run(
        "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#fn payload ((choice (#ref Choice))) (#ref #u64)
          (#return (#match choice (#case-ref (Choice.Full value) value) (#case-ref Choice.Empty (#unreachable))))
#fn main () #u64 (#let value Choice (Choice.Full 42u64))
          (#let result (#ref #u64) (#call payload ((choice (#borrow value)))))
          (#let answer #u64 (#deref result)) (#return answer)\n",
        42,
    );
}

#[test]
fn borrowed_aggregate_payload_preserves_reference_origins() {
    let source = "#struct View () ((target (#ref #u64)))
#enum E () ((E.A View) E.Empty)
#fn projected ((value (#ref E))) (#ref #u64)
          (#return (#match value (#case-ref (E.A view) (#get view target)) (#case-ref E.Empty (#unreachable))))
#fn identity ((value (#ref E))) (#ref E) (#return value)
#fn main () #u64
          (#let target #u64 42u64)
          (#let value E (E.A (#struct-literal View ((target (#borrow target))))))
          (#let result (#ref #u64) (#call projected ((value (#borrow value)))))
          (#return (#deref result))\n";
    run(source, 42);
    run(
        &source.replace("(#match value", "(#match (#block value)"),
        42,
    );
    run(
        &source.replace("(#match value", "(#match (#call identity ((value value)))"),
        42,
    );

    let mutation = source
        .replace(
            "(#return (#deref result))",
            "(#set target 43u64)\n        (#return (#deref result))",
        )
        .replace("(#let target #u64", "(#let-mut target #u64");
    reject_any(&mutation);
    reject_any(&mutation.replace("(#match value", "(#match (#block value)"));
    reject_any(&mutation.replace("(#match value", "(#match (#call identity ((value value)))"));
}

fn async_match_source() -> &'static str {
    "#enum Choice () ((Choice.Full #u64) Choice.Empty)
#enum Child (#linear) ((Child.Start #u64) (Child.Resume #u64))
#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready #u64))
#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
          (#return (#match task (#case (Child.Start value) (ChildPoll.Pending (Child.Resume value))) (#case (Child.Resume value) (ChildPoll.Ready value))))
#syntax StepAwait (#u64 Child ChildPoll.Pending ChildPoll.Ready child-poll)
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((choice (#ref-mut Choice)) (seed #u64)) #u64
            (#let selected #u64 (#match choice
              (#case-ref-mut (Choice.Full payload) (#when (#u64::eq (#deref payload) 42u64)) (#deref payload))
              (#case _ 0u64)))
            (#return (#await StepAwait (Child.Start selected))))))
#fn main () #u64
          (#let-mut choice Choice (Choice.Full 42u64))
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((choice (#borrow-mut choice)) (seed 42u64)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#return (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value) (#case (Work::Poll.Pending child) (#block (#forget child) (#unreachable)))))\n"
}

#[test]
fn async_generator_matches_borrowed_case_before_await() {
    let source = async_match_source();
    run(source, 42);
    run(
        &source.replace("(#match choice", "(#match (#block choice)"),
        42,
    );
    run(
        &source.replace("(Choice.Full 42u64)", "(Choice.Full 41u64)"),
        0,
    );
    run(&source.replace("(Choice.Full 42u64)", "Choice.Empty"), 0);
    run(
        &source
            .replace("#case-ref-mut", "#case-ref")
            .replace("#ref-mut Choice", "#ref Choice")
            .replace("(#borrow-mut choice)", "(#borrow choice)"),
        42,
    );
}

#[test]
#[ignore = "async reference-returning calls retain a conflicting parent handle in the generated frame"]
fn async_generator_matches_reference_returned_by_call() {
    let computed = format!(
        "#fn identity ((input (#ref-mut Choice))) (#ref-mut Choice) (#return input)\n{}",
        async_match_source().replace(
            "(#match choice",
            "(#match (#call identity ((input choice)))"
        )
    );
    run(&computed, 42);
}

#[test]
fn borrowed_case_rejections_cover_mode_and_aliasing_rules() {
    reject("#enum E () ((E.A #u64) E.B)\n#fn f ((e (#ref E))) #u64 (#return (#match e (#case-ref-mut (E.A x) (#deref x)) (#case-ref E.B 0u64)))\n", "mutable");
    let prefix = "#struct Pair () ((left #u64) (right #u64))\n#enum E () ((E.A Pair) E.B)\n#fn f ((e (#ref E))) #u64";
    reject_any(&format!(
        "{prefix}(#return (#match e (#case-ref (E.A (Pair x y)) x) (#case-ref E.B 0u64)))"
    ));
    reject_any(&format!("{prefix}(#return (#match e (#case-ref (E.A value) 1u64) (#case-ref (E.A again) 2u64) (#case-ref E.B 0u64)))"));
    reject_any(&format!(
        "{prefix}(#return (#match e (#case-ref (E.A value) 1u64)))"
    ));
    reject_any(&format!(
        "{prefix}(#return (#match e (#case-ref (E.A value) 1u64) (#case-pin E.B 0u64)))"
    ));
    let shadowing = "#enum E () ((E.A #u64))\n#fn f ((e (#ref E))) #u64 (#return (#match e (#case-ref (E.A e) (#deref e))))\n";
    lim::parse_source_unit(shadowing).unwrap();
    assert!(lim::parse_program(shadowing)
        .unwrap_err()
        .to_lowercase()
        .contains("shadow"));
    reject_any("#enum E () ((E.A #u64))\n#fn bad () (#ref #u64) (#let value E (E.A 42u64)) (#return (#match (#borrow value) (#case-ref (E.A payload) payload)))\n");
    let conflict = "#enum E () ((E.A #u64) E.B)\n#fn touch ((e (#ref-mut E))) () (#return ())\n#fn bad ((e (#ref-mut E))) #u64 (#return (#match e (#case-ref-mut (E.A value) (#block (#call touch ((e e))) (#deref value))) (#case-ref-mut E.B 0u64)))\n";
    reject_any(conflict);
    reject_any(&conflict.replace("(#match e", "(#match (#block e)"));
}
