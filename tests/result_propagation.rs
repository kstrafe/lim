#[path = "support/generated_source.rs"]
mod generated_source;
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

const RESULTS: &str = "(#generate #result ((ok #u64) (error #u32) (name Input)))
    (#generate #result ((ok #bool) (error #u32) (name Output)))
    (#fn convert ((value Input)) Output
      (#let-else (Input.Ok number) Input value
        (#else (Input.Err error)
          (#return (#call Output::err ((error error))))))
      (#return (#call Output::ok ((value (#u64::eq number 42u64))))))";

#[test]
fn documented_example_runs_natively() {
    run(include_str!("../examples/result_propagation.lim"), 42);
}

#[test]
fn propagates_across_concrete_success_types_native_and_cached() {
    for (constructor, expected) in [
        ("(#call Input::ok ((value 42u64)))", 42),
        ("(#call Input::err ((error 7u32)))", 7),
    ] {
        let source = format!(
            "{RESULTS}
          (#fn main () #u64
            (#return (#match (#call convert ((value {constructor})))
              (#case (Output.Ok yes) (#if yes 42u64 0u64))
              (#case (Output.Err error) (#as error #u64)))))"
        );
        run(&source, expected);
    }
}

#[test]
fn evaluates_source_once_on_both_edges() {
    for choice in ["(Choice.Some 40u64)", "(Choice.Error 40u64)"] {
        run(
            &format!(
                "(#enum Choice () ((Choice.Some #u64) (Choice.Error #u64)))
          (#fn source ((count (#ref-mut #u64))) Choice
            (#deref-set count (#u64::add-wrap (#deref count) 1u64))
            (#return {choice}))
          (#fn test ((count (#ref-mut #u64))) #u64
            (#let-else (Choice.Some number) Choice (#call source ((count count)))
              (#else (Choice.Error error) (#return error)))
            (#return number))
          (#fn main () #u64 (#let-mut count #u64 1u64)
            (#let value #u64 (#call test ((count (#borrow-mut count)))))
            (#return (#u64::add-wrap value count)))"
            ),
            42,
        );
    }
}

#[test]
fn validates_failure_patterns_and_divergence() {
    let template = "(#enum Choice () ((Choice.Some #u64) (Choice.Error #u64) (Choice.Empty)))
      (#fn test ((value Choice)) #u64
        (#let-else (Choice.Some number) Choice value FALLBACK) (#return number))";
    for (fallback, error) in [
        (
            "(#else (Choice.Error error) (#return error))",
            "does not cover all success mismatches",
        ),
        (
            "(#else (Choice.Missing error) (#return error))",
            "not a variant",
        ),
        (
            "(#else (Choice.Error first second) (#return first))",
            "expects 1 payload patterns",
        ),
        ("(#else _ (#let answer #u64 0u64))", "body must diverge"),
        (
            "(#else (Choice.Error value) (#return value))",
            "shadowing is not allowed",
        ),
        (
            "(#else (Choice.Error error) (#return number))",
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
        "(#enum Choice () ((Choice.Some #u64) (Choice.Error #u64)))
      (#fn test ((value Choice)) #u64
        (#let-else (Choice.Some 42u64) Choice value
          (#else (Choice.Error error) (#return error))) (#return 42u64))",
        "does not cover all success mismatches",
    );
    checked(
        "(#enum Choice () ((Choice.Flag #bool)))
      (#fn test ((value Choice)) #u64
        (#let-else (Choice.Flag true) Choice value
          (#else (Choice.Flag false) (#return 0u64))) (#return 42u64))",
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
        "(#enum Choice () (Choice.Some Choice.Error Choice.Empty)) (#fn main () #u64
      (#let-else Choice.Some Choice Choice.Error (#else _ (#return 42u64))) (#return 0u64))",
        42,
    );
    run(
        "(#enum Choice () ((Choice.Some #u64) (Choice.Error (#tuple #u64 #u64 #u64 #u64 #u64 #u64 #u64))))
      (#fn main () #u64
        (#let-else (Choice.Some number) Choice (Choice.Error (#tuple 1u64 2u64 3u64 4u64 5u64 6u64 21u64))
          (#else (Choice.Error (#tuple first second third fourth fifth sixth last))
            (#return (#u64::add-wrap (#u64::add-wrap (#u64::add-wrap first second)
              (#u64::add-wrap third fourth)) (#u64::add-wrap (#u64::add-wrap fifth sixth) last)))))
        (#return number))",
        42,
    );
}

#[test]
fn failure_cleanup_is_checked_only_for_success_mismatches() {
    for (value, expected) in [
        ("(Choice.Missing)", 0),
        ("(Choice.Owned (#struct-literal Token ((value 42u64))))", 42),
    ] {
        run(
            &format!(
                "(#struct Token (#linear) ((value #u64)))
          (#enum Choice () ((Choice.Owned Token) (Choice.Missing)))
          (#fn main () #u64
            (#let-else (Choice.Owned token) Choice {value} (#else _ (#return 0u64)))
            (#let number #u64 (#get token value)) (#forget token) (#return number))"
            ),
            expected,
        );
    }
}

#[test]
fn cannot_discard_an_indivisible_linear_error_enum() {
    let source = "(#enum Error (#linear) (Error.Broken))
      (#enum Input () ((Input.Some #u64) (Input.Failure Error)))
      (#fn test ((value Input)) #u64
        (#let-else (Input.Some number) Input value
          (#else (Input.Failure _) (#return 0u64))) (#return number))";
    rejected(source, "would discard a linear payload");
    checked(
        &source
            .replace("(Input.Failure _)", "(Input.Failure error)")
            .replace("(#return 0u64)", "(#forget error) (#return 0u64)"),
    );
}

#[test]
fn linear_error_is_consumed_once() {
    let source = "(#struct Token (#linear) ((value #u64)))
      (#generate #result ((ok #u64) (error Token) (name Input)))
      (#generate #result ((ok #bool) (error Token) (name Output)))
      (#fn convert ((value Input)) Output
        (#let-else (Input.Ok number) Input value
          (#else (Input.Err error)
            (#return (#call Output::err ((error error))))))
        (#forget number) (#return (#call Output::ok ((value true)))))
      (#fn main () #u64
        (#let value Output (#call convert ((value
          (#call Input::err ((error (#struct-literal Token ((value 42u64))))))))))
        (#return (#match value
          (#case (Output.Ok _) 0u64)
          (#case (Output.Err token) (#block
            (#let answer #u64 (#get token value)) (#forget token) answer)))))";
    run(source, 42);
    rejected(
        &source.replace(
            "(#return (#call Output::err ((error error))))",
            "(#forget error) (#return (#call Output::err ((error error))))",
        ),
        "used more than once",
    );
    rejected(
        &source.replace(
            "(#return (#call Output::err ((error error))))",
            "(#return (#call Output::ok ((value false))))",
        ),
        "linear",
    );
    rejected(
        &source.replace("(#else (Input.Err error)", "(#else (Input.Err _)"),
        "unknown variable or enum variant 'error'",
    );
    rejected(
        &source
            .replace("(#else (Input.Err error)", "(#else _")
            .replace(
                "(#return (#call Output::err ((error error))))",
                "(#return (#call Output::ok ((value false))))",
            ),
        "linear",
    );
}

#[test]
fn generated_linear_error_enum_propagates_on_both_edges() {
    let declarations = "(#enum Error (#linear) (Error.Broken))
      (#generate #result ((ok #u64) (error Error) (name Input)))
      (#generate #result ((ok #bool) (error Error) (name Output)))
      (#fn convert ((value Input)) Output
        (#let-else (Input.Ok number) Input value
          (#else (Input.Err error)
            (#return (#call Output::err ((error error))))))
        (#return (#call Output::ok ((value (#u64::eq number 42u64))))))";
    for constructor in [
        "(#call Input::ok ((value 42u64)))",
        "(#call Input::err ((error Error.Broken)))",
    ] {
        run(
            &format!(
                "{declarations}
          (#fn main () #u64
            (#return (#match (#call convert ((value {constructor})))
              (#case (Output.Ok yes) (#if yes 42u64 0u64))
              (#case (Output.Err error) (#block (#forget error) 42u64)))))"
            ),
            42,
        );
    }
    rejected(
        &format!(
            "{declarations}
      (#fn main () #bool
        (#return (#call Input::is-ok ((value (#call Input::err ((error Error.Broken))))))))"
        ),
        "Input::is-ok",
    );
    run(
        "(#struct Token (#linear) ((value #u64)))
      (#generate #optional ((type Token) (name Maybe)))
      (#fn main () #u64
        (#let value Maybe (#call Maybe::construct ((value (#struct-literal Token ((value 42u64)))))))
        (#return (#match value
          (#case (Maybe.Some token) (#block
            (#let answer #u64 (#get token value)) (#forget token) answer))
          (#case Maybe.None 0u64))))",
        42,
    );
}

#[test]
fn builtin_helper_policy_matches_materialization_and_cache_context() {
    let scratch = support::Scratch::new("result-helper-context");
    let source = "(#enum Error () (Error.Broken))
      (#generate #result ((ok #u64) (error Error) (name Result)))
      (#generate #optional ((type Error) (name Maybe)))";
    let generated = || {
        std::fs::read_dir(scratch.path().join("generated"))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "lim"))
            .map(|path| std::fs::read_to_string(path).unwrap())
            .collect::<Vec<_>>()
    };
    for linear in [false, true] {
        let source = if linear {
            source.replace("(#enum Error ()", "(#enum Error (#linear)")
        } else {
            source.to_owned()
        };
        let before = if linear { generated() } else { Vec::new() };
        lim::write_generated_sources(&source, scratch.path()).unwrap();
        let after = generated();
        let new_sources = after
            .iter()
            .filter(|source| !before.contains(source))
            .collect::<Vec<_>>();
        assert_eq!(
            new_sources.len(),
            2,
            "Copy context must invalidate both builtin caches"
        );
        let program = lim::parse_program(&source).unwrap();
        lim::check_types(&program).unwrap();
        for (name, constructor, helper) in
            [("Result", "ok", "is-ok"), ("Maybe", "construct", "is-some")]
        {
            let materialized = new_sources
                .iter()
                .find(|source| source.contains(&format!("#enum {name} ")))
                .unwrap();
            let ast_names = program
                .items
                .iter()
                .filter_map(|item| match item {
                    lim::Item::Function(function)
                        if function.name.starts_with(&format!("{name}::")) =>
                    {
                        Some(function.name.clone())
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let materialized_program = lim::parse_program(&format!(
                "{}\n{}",
                source.split("(#generate").next().unwrap(),
                generated_source::ordinary_source(materialized)
            ))
            .unwrap();
            let materialized_names = materialized_program
                .items
                .iter()
                .filter_map(|item| match item {
                    lim::Item::Function(function) => Some(function.name.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(ast_names, materialized_names);
            assert!(ast_names.contains(&format!("{name}::{constructor}")));
            assert_eq!(ast_names.contains(&format!("{name}::{helper}")), !linear);
            assert_eq!(materialized.contains("unwrap-or"), !linear);
            assert!(!materialized.contains("#forget"));
        }
        lim::write_generated_sources(&source, scratch.path()).unwrap();
        assert_eq!(
            generated().len(),
            after.len(),
            "warm materialization must reuse its context"
        );
    }
}

#[test]
fn builtin_copy_policy_handles_aliases_exclusive_refs_and_explicit_linearity() {
    for (declarations, payload, helpers) in [
        ("", "#u64", true),
        ("(#type Payload #u64)", "Payload", true),
        (
            "(#enum Error (#linear) (Error.Broken))  (#type Payload Error)",
            "Payload",
            false,
        ),
        ("", "(#ref-mut #u64)", false),
        ("(#type Payload (#ref-mut #u64))", "Payload", false),
        (
            "(#struct Payload () ((view (#ref-mut #u64))))",
            "Payload",
            false,
        ),
        ("", "(#tuple #u64 (#ref-mut #u64))", false),
        ("", "(#array (#ref-mut #u64) 2)", false),
        ("", "(#ref #u64)", true),
    ] {
        let source = format!(
            "{declarations}
          (#generate #result ((ok #bool) (error {payload}) (name Result)))
          (#generate #optional ((type {payload}) (name Maybe)))"
        );
        let program = lim::parse_program(&source).unwrap();
        lim::check_types(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
        let scratch = support::Scratch::new("result-copy-policy");
        lim::write_generated_sources(&source, scratch.path()).unwrap();
        for entry in std::fs::read_dir(scratch.path().join("generated")).unwrap() {
            let path = entry.unwrap().path();
            if !path.extension().is_some_and(|extension| extension == "lim") {
                continue;
            }
            let generated = std::fs::read_to_string(path).unwrap();
            let name = if generated.contains("#enum Result ") {
                "Result"
            } else {
                "Maybe"
            };
            let ast_names = program
                .items
                .iter()
                .filter_map(|item| match item {
                    lim::Item::Function(function)
                        if function.name.starts_with(&format!("{name}::")) =>
                    {
                        Some(function.name.clone())
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let materialized = lim::parse_program(&format!(
                "{declarations}\n{}",
                generated_source::ordinary_source(&generated)
            ))
            .unwrap();
            let generated_names = materialized
                .items
                .iter()
                .filter_map(|item| match item {
                    lim::Item::Function(function) => Some(function.name.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(ast_names, generated_names, "{source}");
            assert_eq!(generated.contains("unwrap-or"), helpers, "{source}");
            assert_eq!(
                generated.contains("is-ok") || generated.contains("is-some"),
                helpers,
                "{source}"
            );
            assert!(!generated.contains("#forget"));
        }
    }
    run(
        "(#generate #optional ((type (#ref-mut #u64)) (name Maybe)))
      (#fn main () #u64
        (#let-mut number #u64 42u64)
        (#let value Maybe (#call Maybe::construct ((value (#borrow-mut number)))))
        (#let-else (Maybe.Some view) Maybe value (#else Maybe.None (#return 0u64)))
        (#return (#deref view)))",
        42,
    );
}

#[test]
fn user_generator_emitted_builtins_keep_copy_dependent_helpers() {
    let generator = "(#gn emit (payload)
      `((#generate #optional ((type ,payload) (name Maybe)))
        (#generate #result ((ok #bool) (error ,payload) (name Result)))))";
    run(
        &format!(
            "{generator} (#type Payload #u64) (#generate emit Payload)
      (#fn main () #u64
        (#let maybe Maybe (#call Maybe::construct ((value 42u64))))
        (#let result Result (#call Result::err ((error 42u64))))
        (#return (#if (#call Result::is-ok ((value (#clone result)))) 0u64
          (#u64::add-wrap
            (#call Maybe::unwrap-or ((value maybe) (fallback 0u64)))
            (#call Result::unwrap-err-or ((value result) (fallback 0u64)))))))"
        ),
        84,
    );
    let source = format!(
        "{generator}
      (#enum Error (#linear) (Error.Broken))  (#type Payload Error) (#generate emit Payload)
      (#fn main () #u64
        (#let result Result (#call Result::err ((error Error.Broken))))
        (#let-else (Result.Ok yes) Result result
          (#else (Result.Err error) (#forget error) (#return 42u64)))
        (#return (#if yes 1u64 0u64)))"
    );
    run(&source, 42);
    let program = lim::parse_program(&source).unwrap();
    assert!(!program.items.iter().any(|item| matches!(item,
        lim::Item::Function(function) if function.name.contains("unwrap-or")
            || function.name == "Result::is-ok" || function.name == "Maybe::is-some")));
}

#[test]
fn legacy_fallbacks_and_multiple_failure_statements() {
    for fallback in [
        "(#return 42u64)",
        "(#block (#return 42u64))",
        "(#else (Choice.Error error) (#let answer #u64 error) (#return answer))",
    ] {
        run(
            &format!(
                "(#enum Choice () ((Choice.Some #u64) (Choice.Error #u64)))
          (#fn main () #u64 (#let value Choice (Choice.Error 42u64))
            (#let-else (Choice.Some number) Choice value {fallback}) (#return number))"
            ),
            42,
        );
    }
}

#[test]
fn failure_bindings_are_scoped_and_success_bindings_unavailable() {
    rejected(
        "(#enum Choice () ((Choice.Some #u64) (Choice.Error #u64)))
      (#fn test ((value Choice)) #u64
        (#let-else (Choice.Some number) Choice value
          (#else (Choice.Error error) (#return number))) (#return number))",
        "unknown variable or enum variant 'number'",
    );
    rejected(
        "(#enum Choice () ((Choice.Some #u64) (Choice.Error #u64)))
      (#fn test ((value Choice)) #u64
        (#let-else (Choice.Some number) Choice value
          (#else (Choice.Error error) (#return error))) (#return error))",
        "unknown variable or enum variant 'error'",
    );
}

#[test]
fn failure_diagnostics_point_inside_else() {
    let scratch = support::Scratch::new("failure-diagnostics");
    let source = "(#enum Choice () ((Choice.Some #u64) (Choice.Error #u64)))
      (#fn test ((value Choice)) #u64
        (#let-else (Choice.Some number) Choice value
          (#else (Choice.Missing error) (#return error))) (#return number))";
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
        source.find("Choice.Missing").unwrap()
    );
    let source = source
        .replace("Choice.Missing", "Choice.Error")
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
        .replace("(Choice.Error error)", "(Choice.Error value)")
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
        source.find("Choice.Error value").unwrap() + "Choice.Error ".len(),
        "{diagnostic:?}"
    );
}

#[test]
fn reference_error_retains_provenance() {
    let source = "(#struct Error () ((view (#ref #u64))))
      (#generate #result ((ok #u64) (error Error) (name Input)))
      (#generate #result ((ok #bool) (error Error) (name Output)))
      (#fn convert ((value Input)) Output
        (#let-else (Input.Ok number) Input value
          (#else (Input.Err error)
            (#return (#call Output::err ((error error))))))
        (#forget number) (#return (#call Output::ok ((value true)))))
      (#fn main () #u64 (#let-mut owner #u64 42u64)
        (#let result Output (#call convert ((value (#call Input::err
          ((error (#struct-literal Error ((view (#borrow owner)))))))))))
        (#return (#match result (#case (Output.Ok _) 0u64)
          (#case (Output.Err error) (#deref (#get error view))))))";
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
        "(#call Input::ok ((value 42u64)))",
        "(#call Input::err ((error 42u32)))",
    ] {
        run(
            &format!(
                "(#enum Input () ((Input.Ok #u64) (Input.Err #u32)))
          (#enum Output () ((Output.Ok #bool) (Output.Err #u32)))
          (#fn Input::ok ((value #u64)) Input (#return (Input.Ok value)))
          (#fn Input::err ((error #u32)) Input (#return (Input.Err error)))
          (#fn Output::ok ((value #bool)) Output (#return (Output.Ok value)))
          (#fn Output::err ((error #u32)) Output (#return (Output.Err error)))
          (#enum Step (#linear) ((Step.Waiting #u64)))
          (#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64)))
          (#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
            (#return (#match task (#case (Step.Waiting remaining)
              (#if (#u64::eq remaining 0u64) (StepPoll.StepReady 0u64) (StepPoll.StepPending (Step.Waiting 0u64)))))))
          (#generate #async-fn ((protocol convert-await) (waker #u64) (function
            (#fn convert ((value Input)) Output
              (#let waited #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 1u64)))
              (#forget waited)
              (#let-else (Input.Ok number) Input value
                (#else (Input.Err error)
                  (#return (#call Output::err ((error error))))))
              (#return (#call Output::ok ((value (#u64::eq number 42u64)))))))))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let first Convert::Poll (#call Convert::poll ((task (#call convert ((value {constructor}))))
              (waker (#borrow waker)))))
            (#let-else (Convert::Poll.Pending waiting) Convert::Poll first (#unreachable))
            (#let second Convert::Poll (#call Convert::poll ((task waiting) (waker (#borrow waker)))))
            (#return (#match second
              (#case (Convert::Poll.Pending task) (#block (#forget task) 0u64))
              (#case (Convert::Poll.Ready result) (#match result
                (#case (Output.Ok yes) (#if yes 42u64 0u64))
                (#case (Output.Err error) (#as error #u64)))))))"
            ),
            42,
        );
    }
}
