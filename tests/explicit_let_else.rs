mod support;

use lim::{check_types, generate_assembly, parse_program};
use std::{fs, process::Command, time::Duration};

const ENUM: &str = "(#enum Outcome () ((Outcome.Success #u64) Outcome.Failure))";

fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}

fn run(source: &str, expected: i32) {
    check(source).unwrap();
    let scratch = support::Scratch::new("explicit-let-else");
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
    assert_eq!(status.code(), Some(expected), "{source}\n{stderr:?}");
}

#[test]
fn return_fallback_and_success_bindings_execute_on_distinct_paths() {
    for (value, expected) in [("(Outcome.Success 42u64)", 42), ("Outcome.Failure", 7)] {
        run(
            &format!(
                "{ENUM}
          (#fn main () #u64
            (#let outcome Outcome {value})
            (#let-else (Outcome.Success answer) outcome
              (#else (#let fallback #u64 7u64) (#return fallback)))
            (#return answer))"
            ),
            expected,
        );
    }
}

#[test]
fn break_and_continue_skip_all_success_code_in_loop_while_and_for() {
    for transfer in ["#break", "#continue"] {
        for (header, tail) in [
            (
                "#loop",
                "(#if (#u64::eq (#clone count) 2u64) (#block (#break)) ())",
            ),
            ("#while (#u64::lt (#clone count) 2u64)", ""),
            ("#for () (#u64::lt (#clone count) 2u64) ()", ""),
        ] {
            // First iteration fails; the second succeeds only with continue.
            // Reaching the success code after Failure would either read an
            // uninitialized payload or add 100, making the result incorrect.
            let expected = if transfer == "#break" { 1 } else { 42 };
            run(
                &format!(
                    "{ENUM}
              (#fn main () #u64
                (#let-mut count #u64 0u64)
                (#let-mut total #u64 0u64)
                ({header}
                  (#set count (#u64::add-wrap (#clone count) 1u64))
                  (#let outcome Outcome (#if (#u64::eq (#clone count) 1u64) Outcome.Failure (Outcome.Success 40u64)))
                  (#let-else (Outcome.Success answer) outcome
                    (#else (#set total (#u64::add-wrap (#clone total) 1u64)) ({transfer})))
                  (#set total (#u64::add-wrap (#clone total) (#u64::add-wrap answer 1u64)))
                  {tail})
                (#return total))"
                ),
                expected,
            );
        }
    }
}

#[test]
fn all_fallback_paths_must_exit_and_success_binding_is_not_in_else_scope() {
    for fallback in [
        "()",
        "(#let fallback #u64 1u64)",
        "(#if true (#block (#return 1u64)) ())",
        "(#loop (#break))",
        "(#for () false () (#break))",
        "(#label inner (#loop (#break-to inner)))",
    ] {
        let source = format!(
            "{ENUM} (#fn main () #u64
          (#let-else (Outcome.Success answer) Outcome.Failure (#else {fallback})) (#return answer))"
        );
        let error = check(&source).unwrap_err();
        assert!(error.contains("diverge"), "{fallback}: {error}");
    }
    let source = format!(
        "{ENUM} (#fn main () #u64
      (#let-else (Outcome.Success answer) Outcome.Failure (#else (#return answer))) (#return answer))"
    );
    assert!(check(&source).unwrap_err().contains("answer"));
    let source = format!(
        "{ENUM} (#fn main () #u64
      (#let-else (Outcome.Success answer) Outcome.Failure (#else (#break))) (#return answer))"
    );
    assert!(check(&source).unwrap_err().contains("outside a loop"));
}

#[test]
fn named_outer_transfers_and_all_path_returns_are_accepted() {
    for transfer in ["(#break-to outer)", "(#continue-to outer)"] {
        let source = format!(
            "{ENUM} (#fn main () #u64
          (#label outer (#loop
            (#let-else (Outcome.Success answer) Outcome.Failure (#else {transfer}))
            (#return answer))) (#return 0u64))"
        );
        let program = parse_program(&source).unwrap();
        check_types(&program).unwrap();
        generate_assembly(&program).unwrap();
    }
    for fallback in [
        "(#if true (#block (#return 1u64)) (#block (#return 2u64)))",
        "(#match true (#case true (#block (#return 1u64))) (#case false (#block (#return 2u64))))",
        "(#unreachable)",
    ] {
        check(&format!(
            "{ENUM} (#fn main () #u64
          (#let-else (Outcome.Success answer) Outcome.Failure (#else {fallback})) (#return answer))"
        ))
        .unwrap();
    }
}

#[test]
fn enum_owner_is_resolved_from_the_variant_not_the_value() {
    check(&format!(
        "{ENUM} (#fn main () #u64
      (#let-else (Outcome.Success answer) 42u64 (#else (#return 0u64))) (#return answer))"
    ))
    .unwrap_err();
    let error = check(
        "(#fn main () #u64
      (#let-else (missing answer) 42u64 (#else (#return 0u64))) (#return answer))",
    )
    .unwrap_err();
    assert!(error.contains("unknown enum variant 'missing'"), "{error}");
    check(&format!(
        "{ENUM} (#fn main () #u64
      (#let-else Outcome.Failure Outcome.Failure (#else (#return 0u64))) (#return 42u64))"
    ))
    .unwrap();
}

#[test]
fn initializer_block_is_evaluated_once_and_fallback_locals_do_not_escape() {
    run(
        &format!(
            "{ENUM} (#fn main () #u64
      (#let-mut calls #u64 0u64)
      (#let-else (Outcome.Success answer)
        (#block (#set calls (#u64::add-wrap (#clone calls) 1u64)) (Outcome.Success 41u64))
        (#else (#return 0u64)))
      (#return (#u64::add-wrap calls answer)))"
        ),
        42,
    );
    let error = check(&format!(
        "{ENUM} (#fn main () #u64
      (#let-else (Outcome.Success answer) Outcome.Failure
        (#else (#let fallback #u64 0u64) (#return fallback)))
      (#return (#u64::add-wrap answer fallback)))"
    ))
    .unwrap_err();
    assert!(error.contains("fallback"), "{error}");
}

fn projection_source(value: &str) -> String {
    format!(
        "(#std)
      (#enum Task () ((Task.Work #u64) Task.Idle))
      (#generate #enum-project ((enum Task) (variant Task.Work) (payload #u64) (mode #pin-ref-mut) (name WorkProjection)))
      (#fn main () #u64
        (#let-mut task Task {value})
        (#let-else (WorkProjection.Some frame)
          (#call WorkProjection::project ((source (#pin-borrow-mut task))))
          (#else (#forget task) (#return 7u64)))
        (#let answer #u64 (#unsafe (#pin-read frame)))
        (#forget frame)
        (#forget task)
        (#return answer))"
    )
}

#[test]
fn generated_optional_projection_preserves_loans_and_can_release_mismatched_owner() {
    run(&projection_source("(Task.Work 42u64)"), 42);
    run(&projection_source("Task.Idle"), 7);
    for mutation in ["(#forget task)", "(#set task Task.Idle)"] {
        let invalid = projection_source("(Task.Work 42u64)").replace(
            "(#let answer #u64",
            &format!("{mutation}\n (#let answer #u64"),
        );
        let error = check(&invalid).unwrap_err();
        assert!(
            error.contains("borrow") || error.contains("pinned"),
            "{error}"
        );
    }
    let mismatch = projection_source("Task.Idle").replace("(payload #u64)", "(payload #u32)");
    assert!(check(&mismatch).is_err());
    let unknown = projection_source("Task.Idle").replace("(payload #u64)", "(typo #u64)");
    assert!(check(&unknown)
        .unwrap_err()
        .contains("missing key 'payload'"));
    let extra =
        projection_source("Task.Idle").replace("(payload #u64)", "(payload #u64) (typo #u64)");
    assert!(check(&extra).unwrap_err().contains("requires exactly"));
    let duplicate = projection_source("Task.Idle").replace("(payload #u64)", "(enum #u64)");
    assert!(check(&duplicate)
        .unwrap_err()
        .contains("repeats key 'enum'"));
}

#[test]
fn compact_formatting_is_idempotent_and_keeps_else_statements_in_the_body() {
    let source =
        "(#let-else (Outcome.Success answer) outcome (#else (#forget owner) (#return 0u64)))";
    let formatted = lim::format_source(source).unwrap();
    assert!(formatted.contains("(#else\n"), "{formatted}");
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
}

#[test]
fn imported_and_generator_defined_variants_resolve_without_rhs_inference() {
    let scratch = support::Scratch::new("compact-let-else-import");
    let module = scratch.path().join("module.lim");
    fs::write(
        &module,
        format!(
            "{ENUM}
      (#fn read ((value Outcome)) #u64
        (#let-else (Outcome.Success number) value (#else (#return 0u64)))
        (#return number))"
        ),
    )
    .unwrap();
    let source = "(#alias Ext::read = ./module.lim::read)\n(#alias Ext@Success = ./module.lim::Outcome.Success)
      (#fn main () #u64 (#return (#call Ext::read ((value (Ext@Success 42u64))))))";
    let program = lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
    check_types(&program).unwrap();
    generate_assembly(&program).unwrap();
    check(
        "(#generate #optional ((type #u64) (name Number)))
      (#fn main () #u64
        (#let-else (Number.Some number) (Number.Some 42u64)
          (#else (#return 0u64)))
        (#return number))",
    )
    .unwrap();
}

#[test]
fn compact_patterns_work_in_async_source_and_generated_poll_consumers() {
    let source = format!(
        "{ENUM}
      (#generate #async-fn-pinned ((protocol Work::Await) (waker #u64)
        (function (#fn work () #u64
          (#let-else (Outcome.Success answer) (Outcome.Success 42u64)
            (#else (#return 0u64)))
          (#return answer)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work ()))
        (#let-else (Work::Poll.Ready answer)
          (#call Work::poll ((task (#pin-borrow-mut task)) (waker (#borrow waker))))
          (#else (#forget task) (#return 0u64)))
        (#forget task)
        (#return answer))"
    );
    run(&source, 42);
}
