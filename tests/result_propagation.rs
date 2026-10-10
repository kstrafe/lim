mod support;

use std::{process::Command, time::Duration};

fn checked(source: &str) -> lim::Program {
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
    lim::generate_assembly(&program).unwrap();
    program
}

fn rejected(source: &str, expected: &str) {
    let error = match lim::parse_program(source) {
        Ok(program) => lim::check_types(&program).unwrap_err(),
        Err(error) => error,
    };
    assert!(
        error.contains(expected),
        "expected {expected:?}, got {error}"
    );
}

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("result-propagation");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            target,
        )
        .unwrap()
    };
    let assembly = compile();
    assert_eq!(
        assembly,
        compile(),
        "warm cache must preserve failure bindings"
    );
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(expected), "{stderr:?}\n{source}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

const RESULTS: &str = "(@result (: ok #u64 : error #u32 : name Input))
    (@result (: ok #bool : error #u32 : name Output))
    (#fn convert (: value Input) Output
      (#let-else (Input-ok-value number) Input value
        (#else (Input-err-value error)
          (#return (#call Output-err (: error error)))))
      (#return (#call Output-ok (: value (#u64.== number 42u64)))))";

#[test]
fn documented_example_runs_natively() {
    run(include_str!("../examples/result_propagation.lim"), 42);
}

#[test]
fn propagates_across_concrete_success_types_native_and_cached() {
    for (constructor, expected) in [
        ("(#call Input-ok (: value 42u64))", 42),
        ("(#call Input-err (: error 7u32))", 7),
    ] {
        let source = format!(
            "{RESULTS}
          (#fn main () #u64
            (#return (#match (#call convert (: value {constructor}))
              (#case (Output-ok-value yes) (#if yes 42u64 0u64))
              (#case (Output-err-value error) (#as error #u64)))))"
        );
        run(&source, expected);
    }
}

#[test]
fn evaluates_source_once_on_both_edges() {
    for choice in ["(Some 40u64)", "(Error 40u64)"] {
        run(
            &format!(
                "(#enum Choice (: Some #u64 : Error #u64))
          (#fn source (: count (#ref-mut #u64)) Choice
            (#deref-set count (#u64.+.wrap (#deref count) 1u64))
            (#return {choice}))
          (#fn test (: count (#ref-mut #u64)) #u64
            (#let-else (Some number) Choice (#call source (: count count))
              (#else (Error error) (#return error)))
            (#return number))
          (#fn main () #u64 (#let-mut count #u64 1u64)
            (#let value #u64 (#call test (: count (#borrow-mut count))))
            (#return (#u64.+.wrap value count)))"
            ),
            42,
        );
    }
}

#[test]
fn validates_failure_patterns_and_divergence() {
    let template = "(#enum Choice (: Some #u64 : Error #u64 : Empty))
      (#fn test (: value Choice) #u64
        (#let-else (Some number) Choice value FALLBACK) (#return number))";
    for (fallback, error) in [
        (
            "(#else (Error error) (#return error))",
            "does not cover all success mismatches",
        ),
        ("(#else (Missing error) (#return error))", "not a variant"),
        (
            "(#else (Error first second) (#return first))",
            "expects 1 payload patterns",
        ),
        ("(#else _ (#let answer #u64 0u64))", "body must diverge"),
        (
            "(#else (Error value) (#return value))",
            "shadowing is not allowed",
        ),
        (
            "(#else (Error error) (#return number))",
            "does not cover all success mismatches",
        ),
    ] {
        rejected(&template.replace("FALLBACK", fallback), error);
    }
    checked(&template.replace("FALLBACK", "(#else _ (#return 0u64))"));
}

#[test]
fn coverage_includes_refutable_success_payloads() {
    rejected(
        "(#enum Choice (: Some #u64 : Error #u64))
      (#fn test (: value Choice) #u64
        (#let-else (Some 42u64) Choice value
          (#else (Error error) (#return error))) (#return 42u64))",
        "does not cover all success mismatches",
    );
    checked(
        "(#enum Choice (: Flag #bool))
      (#fn test (: value Choice) #u64
        (#let-else (Flag true) Choice value
          (#else (Flag false) (#return 0u64))) (#return 42u64))",
    );
}

#[test]
fn lowers_scalar_aggregate_fieldless_and_large_failures() {
    run(
        "(#fn main () #u64
      (#let-else 0u64 #u64 42u64 (#else error (#return error))) (#return 0u64))",
        42,
    );
    run(
        "(#fn main () #u64
      (#let-else (#tuple number true) (#tuple #u64 #bool) (#tuple 42u64 false)
        (#else (#tuple error false) (#return error))) (#return number))",
        42,
    );
    run(
        "(#enum Choice (Some Error Empty)) (#fn main () #u64
      (#let-else Some Choice Error (#else _ (#return 42u64))) (#return 0u64))",
        42,
    );
    run(
        "(#enum Choice (: Some #u64 : Error (#tuple #u64 #u64 #u64 #u64 #u64 #u64 #u64)))
      (#fn main () #u64
        (#let-else (Some number) Choice (Error (#tuple 1u64 2u64 3u64 4u64 5u64 6u64 21u64))
          (#else (Error (#tuple first second third fourth fifth sixth last))
            (#return (#u64.+.wrap (#u64.+.wrap (#u64.+.wrap first second)
              (#u64.+.wrap third fourth)) (#u64.+.wrap (#u64.+.wrap fifth sixth) last)))))
        (#return number))",
        42,
    );
}

#[test]
fn failure_cleanup_is_checked_only_for_success_mismatches() {
    for (value, expected) in [
        ("(Missing)", 0),
        ("(Owned (#struct-literal Token (: value 42u64)))", 42),
    ] {
        run(
            &format!(
                "(#struct Token (: value #u64)) (#linear Token)
          (#enum Choice (: Owned Token : Missing))
          (#fn main () #u64
            (#let-else (Owned token) Choice {value} (#else _ (#return 0u64)))
            (#let number #u64 (#get token value)) (#forget token) (#return number))"
            ),
            expected,
        );
    }
}

#[test]
fn cannot_discard_an_indivisible_linear_error_enum() {
    let source = "(#enum Error (Broken)) (#linear Error)
      (#enum Input (: Some #u64 : Failure Error))
      (#fn test (: value Input) #u64
        (#let-else (Some number) Input value
          (#else (Failure _) (#return 0u64))) (#return number))";
    rejected(source, "would discard a linear payload");
    checked(
        &source
            .replace("(Failure _)", "(Failure error)")
            .replace("(#return 0u64)", "(#forget error) (#return 0u64)"),
    );
}

#[test]
fn linear_error_is_consumed_once() {
    let source = "(#struct Token (: value #u64)) (#linear Token)
      (#enum Input (: Input-ok-value #u64 : Input-err-value Token))
      (#enum Output (: Output-ok-value #bool : Output-err-value Token))
      (#fn Output-err (: error Token) Output (#return (Output-err-value error)))
      (#fn Output-ok (: value #bool) Output (#return (Output-ok-value value)))
      (#fn Input-err (: error Token) Input (#return (Input-err-value error)))
      (#fn convert (: value Input) Output
        (#let-else (Input-ok-value number) Input value
          (#else (Input-err-value error)
            (#return (#call Output-err (: error error)))))
        (#forget number) (#return (#call Output-ok (: value true))))
      (#fn main () #u64
        (#let value Output (#call convert (: value
          (#call Input-err (: error (#struct-literal Token (: value 42u64)))))))
        (#return (#match value
          (#case (Output-ok-value _) 0u64)
          (#case (Output-err-value token) (#block
            (#let answer #u64 (#get token value)) (#forget token) answer)))))";
    run(source, 42);
    rejected(
        &source.replace(
            "(#return (#call Output-err (: error error)))",
            "(#forget error) (#return (#call Output-err (: error error)))",
        ),
        "used more than once",
    );
    rejected(
        &source.replace(
            "(#return (#call Output-err (: error error)))",
            "(#return (#call Output-ok (: value false)))",
        ),
        "linear",
    );
    rejected(
        &source.replace(
            "(#else (Input-err-value error)",
            "(#else (Input-err-value _)",
        ),
        "unknown variable or enum variant 'error'",
    );
    rejected(
        &source
            .replace("(#else (Input-err-value error)", "(#else _")
            .replace(
                "(#return (#call Output-err (: error error)))",
                "(#return (#call Output-ok (: value false)))",
            ),
        "linear",
    );
}

#[test]
fn legacy_fallbacks_and_multiple_failure_statements() {
    for fallback in [
        "(#return 42u64)",
        "(#block (#return 42u64))",
        "(#else (Error error) (#let answer #u64 error) (#return answer))",
    ] {
        run(
            &format!(
                "(#enum Choice (: Some #u64 : Error #u64))
          (#fn main () #u64 (#let value Choice (Error 42u64))
            (#let-else (Some number) Choice value {fallback}) (#return number))"
            ),
            42,
        );
    }
}

#[test]
fn failure_bindings_are_scoped_and_success_bindings_unavailable() {
    rejected(
        "(#enum Choice (: Some #u64 : Error #u64))
      (#fn test (: value Choice) #u64
        (#let-else (Some number) Choice value
          (#else (Error error) (#return number))) (#return number))",
        "unknown variable or enum variant 'number'",
    );
    rejected(
        "(#enum Choice (: Some #u64 : Error #u64))
      (#fn test (: value Choice) #u64
        (#let-else (Some number) Choice value
          (#else (Error error) (#return error))) (#return error))",
        "unknown variable or enum variant 'error'",
    );
}

#[test]
fn failure_diagnostics_point_inside_else() {
    let scratch = support::Scratch::new("failure-diagnostics");
    let source = "(#enum Choice (: Some #u64 : Error #u64))
      (#fn test (: value Choice) #u64
        (#let-else (Some number) Choice value
          (#else (Missing error) (#return error))) (#return number))";
    let diagnostic = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        diagnostic.message.contains("not a variant"),
        "{diagnostic:?}"
    );
    assert_eq!(
        diagnostic.span.unwrap().start,
        source.find("Missing").unwrap()
    );
    let source = source
        .replace("Missing", "Error")
        .replace("(#return error)", "(#return unknown)");
    let diagnostic = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(
        diagnostic.span.unwrap().start,
        source.find("unknown").unwrap(),
        "{diagnostic:?}"
    );
    let source = source
        .replace("(Error error)", "(Error value)")
        .replace("(#return unknown)", "(#return value)");
    let diagnostic = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(
        diagnostic.span.unwrap().start,
        source.find("Error value").unwrap() + 6,
        "{diagnostic:?}"
    );
}

#[test]
fn reference_error_retains_provenance() {
    let source = "(#struct Error (: view (#ref #u64)))
      (@result (: ok #u64 : error Error : name Input))
      (@result (: ok #bool : error Error : name Output))
      (#fn convert (: value Input) Output
        (#let-else (Input-ok-value number) Input value
          (#else (Input-err-value error)
            (#return (#call Output-err (: error error)))))
        (#forget number) (#return (#call Output-ok (: value true))))
      (#fn main () #u64 (#let-mut owner #u64 42u64)
        (#let result Output (#call convert (: value (#call Input-err
          (: error (#struct-literal Error (: view (#borrow owner))))))))
        (#return (#match result (#case (Output-ok-value _) 0u64)
          (#case (Output-err-value error) (#deref (#get error view))))))";
    run(source, 42);
    rejected(
        &source.replace(
            "(#return (#match result",
            "(#set owner 0u64) (#return (#match result",
        ),
        "borrow",
    );
    let exclusive = source
        .replace("(#ref #u64)", "(#ref-mut #u64)")
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    run(&exclusive, 42);
    rejected(
        &exclusive.replace(
            "(#return (#match result",
            "(#set owner 0u64) (#return (#match result",
        ),
        "borrow",
    );
}

#[test]
fn preserves_failure_pattern_after_async_suspension() {
    for constructor in [
        "(#call Input-ok (: value 42u64))",
        "(#call Input-err (: error 42u32))",
    ] {
        run(
            &format!(
                "(#enum Input (: Input-ok-value #u64 : Input-err-value #u32))
          (#enum Output (: Output-ok-value #bool : Output-err-value #u32))
          (#fn Input-ok (: value #u64) Input (#return (Input-ok-value value)))
          (#fn Input-err (: error #u32) Input (#return (Input-err-value error)))
          (#fn Output-ok (: value #bool) Output (#return (Output-ok-value value)))
          (#fn Output-err (: error #u32) Output (#return (Output-err-value error)))
          (#enum Step (: Waiting #u64)) (#linear Step)
          (#enum StepPoll (: StepPending Step : StepReady #u64))
          (#fn step-poll (: task Step : waker (#ref #u64)) StepPoll
            (#return (#match task (#case (Waiting remaining)
              (#if (#u64.== remaining 0u64) (StepReady 0u64) (StepPending (Waiting 0u64)))))))
          (@async-fn (: names (Frame Poll Pending Ready poll) : waker #u64 : function
            (#fn convert (: value Input) Output
              (#let waited #u64 (#await Step StepPending StepReady step-poll (Waiting 1u64)))
              (#forget waited)
              (#let-else (Input-ok-value number) Input value
                (#else (Input-err-value error)
                  (#return (#call Output-err (: error error)))))
              (#return (#call Output-ok (: value (#u64.== number 42u64)))))))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let first Poll (#call poll (: task (#call convert (: value {constructor}))
              : waker (#borrow waker))))
            (#let-else (Pending waiting) Poll first (#unreachable))
            (#let second Poll (#call poll (: task waiting : waker (#borrow waker))))
            (#return (#match second
              (#case (Pending task) (#block (#forget task) 0u64))
              (#case (Ready result) (#match result
                (#case (Output-ok-value yes) (#if yes 42u64 0u64))
                (#case (Output-err-value error) (#as error #u64)))))))"
            ),
            42,
        );
    }
}
