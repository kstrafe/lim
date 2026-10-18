mod support;

use std::{process::Command, time::Duration};

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("local-pin");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            target,
        )
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"))
    };
    let assembly = compile();
    assert_eq!(assembly, compile(), "warm cache must preserve local pins");
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(expected), "{stderr:?}\n{source}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

fn reject(source: &str, expected: &str) {
    let error = match lim::parse_program(source) {
        Ok(program) => lim::check_types(&program).unwrap_err(),
        Err(error) => error,
    };
    assert!(
        error.contains(expected),
        "expected {expected:?}, got {error}\n{source}"
    );
}

const JOB: &str = "(#struct Job (#linear) (: state #u64)) ";
const POLL: &str = "(#fn poll (: target (#pin-ref-mut Job)) #u64
  (#let answer #u64 (#get target state))
  (#pin-set-field target state (#u64::add-wrap answer 1u64))
  (#forget target) (#return answer))";

#[test]
fn two_local_pins_branch_poll_and_cleanup_natively() {
    for choice in ["true", "false"] {
        run(
            &format!(
                "{JOB} {POLL}
          (#fn main () #u64
            (#let-mut left Job (#struct-literal Job (: state 42u64)))
            (#let-mut right Job (#struct-literal Job (: state 42u64)))
            (#let left-pin (#pin-ref-mut Job) (#pin left))
            (#let right-pin (#pin-ref-mut Job) (#pin right))
            (#let answer #u64 (#if {choice}
              (#block (#forget right-pin) (#call poll (: target left-pin)))
              (#block (#forget left-pin) (#call poll (: target right-pin)))))
            (#forget left) (#forget right) (#return answer))"
            ),
            42,
        );
    }
}

#[test]
fn generated_pinned_futures_accept_local_pins_not_ordinary_references() {
    let source = include_str!("../examples/async_two_pinned.lim");
    run(source, 42);
    let ordinary = source.replacen("(#pin reader)", "(#borrow-mut reader)", 1);
    assert_ne!(
        ordinary, source,
        "the example must exercise a local reader pin"
    );
    reject(&ordinary, "PinnedReference");
}

#[test]
fn invalid_pin_argument_preserves_structured_diagnostic_span_and_cache() {
    let source = "(#fn main () #u64
  (#let view (#pin-ref-mut #u64) (#pin 42u64))
  (#forget view)
  (#return 0u64))";
    let scratch = support::Scratch::new("local-pin-diagnostic");
    let path = scratch.path().join("invalid pin.lim");
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &path,
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    let diagnostic = compile();
    assert_eq!(
        diagnostic,
        compile(),
        "warm diagnostics must retain pin argument spans"
    );
    assert_eq!(diagnostic.code, lim::DiagnosticCode::Type);
    assert!(diagnostic
        .message
        .contains("requires an initialized local variable"));
    assert_eq!(diagnostic.source_name.as_deref(), path.to_str());
    assert_eq!(diagnostic.source_text.as_deref(), Some(source));
    let span = diagnostic.span.unwrap();
    assert_eq!(&source[span.start..span.end], "42u64");
    assert_eq!(span.start, source.find("42u64").unwrap());
    assert_eq!(span.line, 2);
}

#[test]
fn documented_local_pin_cleanup_runs_natively() {
    let source = include_str!("../docs/language.md")
        .split_once("(#struct LocalJob () (: state #u64))")
        .unwrap()
        .1
        .split_once("```")
        .unwrap()
        .0;
    run(&format!("(#struct LocalJob () (: state #u64)){source}"), 42);
}

#[test]
fn shared_pin_and_projection_reborrows_work_natively() {
    run(
        "(#fn main () #u64
      (#let number #u64 42u64)
      (#let view (#pin-ref #u64) (#pin-shared number))
      (#let answer #u64 (#deref view))
      (#forget view) (#forget number) (#return answer))",
        42,
    );
    run(
        &format!(
            "{JOB}
      (#fn main () #u64
        (#let-mut job Job (#struct-literal Job (: state 42u64)))
        (#let parent (#pin-ref-mut Job) (#pin job))
        (#let child (#pin-ref-mut #u64) (#pin-borrow-mut (#get parent state)))
        (#let answer #u64 (#deref child))
        (#forget child) (#forget parent) (#forget job) (#return answer))"
        ),
        42,
    );
}

#[test]
fn owned_parameter_cannot_move_after_local_pin_ends() {
    reject(
        &format!(
            "{JOB} (#fn bad (: #mut job Job) Job
              (#let view (#pin-ref-mut Job) (#pin job))
              (#forget view) (#return job))"
        ),
        "stationary",
    );
}

#[test]
fn each_loop_iteration_initializes_fresh_pinned_storage() {
    run(
        &format!(
            "{JOB} {POLL} (#fn main () #u64
              (#let-mut total #u64 0u64)
              (#for (#let-mut index #u64 0u64)
                (#u64::lt index 2u64)
                (#set index (#u64::add-wrap index 1u64))
                (#let-mut job Job (#struct-literal Job (: state 21u64)))
                (#let view (#pin-ref-mut Job) (#pin job))
                (#let value #u64 (#call poll (: target view)))
                (#set total (#u64::add-wrap total value))
                (#forget job))
              (#return total))"
        ),
        42,
    );
}

#[test]
fn frozen_copy_storage_remains_readable_after_pin_loan_ends() {
    for (operator, ty) in [("#pin", "#pin-ref-mut"), ("#pin-shared", "#pin-ref")] {
        run(
            &format!(
                "(#fn main () #u64
                  (#let-mut number #u64 21u64)
                  (#let view ({ty} #u64) ({operator} number))
                  (#forget view)
                  (#let copied #u64 number)
                  (#let cloned #u64 (#clone number))
                  (#forget number)
                  (#return (#u64::add-wrap copied cloned)))"
            ),
            42,
        );
    }
}

#[test]
fn forgetting_pin_does_not_allow_linear_move() {
    for (operator, ty) in [("#pin", "#pin-ref-mut"), ("#pin-shared", "#pin-ref")] {
        reject(
            &format!(
                "{JOB} (#fn main () #u64
          (#let-mut job Job (#struct-literal Job (: state 42u64)))
          (#let view ({ty} Job) ({operator} job)) (#forget view)
          (#let moved Job job) (#forget moved) (#return 0u64))"
            ),
            "pin",
        );
    }
}

#[test]
fn forgetting_pin_does_not_allow_copy_assignment() {
    for (operator, ty) in [("#pin", "#pin-ref-mut"), ("#pin-shared", "#pin-ref")] {
        reject(
            &format!(
                "(#fn main () #u64
          (#let-mut number #u64 42u64)
          (#let view ({ty} #u64) ({operator} number)) (#forget view)
          (#set number 0u64) (#return number))"
            ),
            "pin",
        );
    }
}

#[test]
fn may_pin_branch_join_prevents_move() {
    reject(
        &format!(
            "{JOB} (#fn test (: choice #bool) #u64
      (#let-mut job Job (#struct-literal Job (: state 42u64)))
      (#if choice (#block
        (#let view (#pin-ref-mut Job) (#pin job)) (#forget view) ()) ())
      (#let moved Job job) (#forget moved) (#return 0u64))"
        ),
        "pin",
    );
}

#[test]
fn pinned_local_reference_cannot_escape() {
    reject(
        "(#fn escape () (#pin-ref #u64)
      (#let number #u64 42u64)
      (#let view (#pin-ref #u64) (#pin-shared number)) (#return view))",
        "local",
    );
    reject(
        "(#fn escape () (#pin-ref-mut #u64)
      (#let-mut number #u64 42u64)
      (#let view (#pin-ref-mut #u64) (#pin number)) (#return view))",
        "local",
    );
}

#[test]
fn ordinary_reference_cannot_satisfy_pinned_parameter() {
    reject(
        &format!(
            "{JOB} {POLL} (#fn main () #u64
      (#let-mut job Job (#struct-literal Job (: state 42u64)))
      (#let answer #u64 (#call poll (: target (#borrow-mut job))))
      (#forget job) (#return answer))"
        ),
        "expected PinnedReference",
    );
}

#[test]
fn pin_requires_mutable_initialized_local_not_temporary_projection_or_reference() {
    reject(
        "(#fn main () #u64 (#let number #u64 42u64)
      (#let view (#pin-ref-mut #u64) (#pin number)) (#forget view) (#return 0u64))",
        "mutable",
    );
    for (operator, ty) in [("#pin", "#pin-ref-mut"), ("#pin-shared", "#pin-ref")] {
        for expression in ["42u64", "(#get job state)"] {
            reject(
                &format!(
                    "{JOB} (#fn main () #u64
              (#let-mut job Job (#struct-literal Job (: state 42u64)))
              (#let view ({ty} #u64) ({operator} {expression}))
              (#forget view) (#forget job) (#return 0u64))"
                ),
                "initialized local",
            );
        }
        reject(
            &format!(
                "(#fn main () #u64 (#let-mut number #u64 42u64)
          (#let reference (#ref-mut #u64) (#borrow-mut number))
          (#let view ({ty} (#ref-mut #u64)) ({operator} reference))
          (#forget view) (#forget reference) (#return 0u64))"
            ),
            "reference variable",
        );
    }
}

#[test]
fn local_pin_operations_reject_globals_and_statics() {
    for declaration in ["#const", "#static"] {
        for (operator, ty) in [("#pin", "#pin-ref-mut"), ("#pin-shared", "#pin-ref")] {
            reject(
                &format!(
                    "({declaration} GLOBAL #u64 42u64)
                    (#fn main () #u64
                      (#let view ({ty} #u64) ({operator} GLOBAL))
                      (#forget view) (#return 0u64))"
                ),
                "requires an initialized local variable",
            );
        }
    }
}

#[test]
fn exclusive_pins_cannot_overlap_or_shadow() {
    reject(
        &format!(
            "{JOB} (#fn main () #u64
      (#let-mut job Job (#struct-literal Job (: state 42u64)))
      (#let first (#pin-ref-mut Job) (#pin job))
      (#let second (#pin-ref-mut Job) (#pin job))
      (#forget first) (#forget second) (#forget job) (#return 0u64))"
        ),
        "borrow",
    );
    reject(
        "(#fn main () #u64 (#let-mut number #u64 42u64)
      (#let view (#pin-ref-mut #u64) (#pin number))
      (#let view #u64 0u64) (#return view))",
        "shadow",
    );
}

#[test]
fn forgetting_reference_does_not_implicitly_consume_linear_owner() {
    reject(
        &format!(
            "{JOB} (#fn main () #u64
      (#let-mut job Job (#struct-literal Job (: state 42u64)))
      (#let view (#pin-ref-mut Job) (#pin job))
      (#forget view) (#return 0u64))"
        ),
        "must be consumed",
    );
}

#[test]
fn owner_cannot_end_while_pin_is_retained() {
    reject(
        &format!(
            "{JOB} (#fn main () #u64
      (#let-mut job Job (#struct-literal Job (: state 42u64)))
      (#let view (#pin-ref-mut Job) (#pin job))
      (#forget job) (#forget view) (#return 0u64))"
        ),
        "borrow",
    );
}
