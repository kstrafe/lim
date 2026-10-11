mod support;

use lim::{Diagnostic, DiagnosticCode};
use std::{process::Command, time::Duration};

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

const CHILD: &str = "(#enum Child ((Waiting #u64))) (#linear Child)
  (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
  (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
    (#return (#match task
      (#case (Waiting count)
        (#if (#u64.< count 2u64)
          (ChildPending (Waiting (#u64.+.wrap count 1u64)))
          (ChildReady count))))))
  (#fn cancel-child (: child Child) () (#forget child) (#return ()))
  (#fn cancel-u64 (: value #u64) () (#forget value) (#return ()))";

const CANCEL: &str = ": cancel (work-cancel ((await-0 cancel-child)))";

fn compile_error(source: &str, label: &str) -> Diagnostic {
    let scratch = support::Scratch::new(label);
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

fn assert_borrow_error(source: &str, label: &str, conflict: &str, occurrence: usize) {
    let error = compile_error(source, label);
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    let span = error
        .span
        .expect("borrow diagnostic should identify conflict");
    let expected = source
        .match_indices(conflict)
        .nth(occurrence)
        .expect("conflict text in source")
        .0;
    assert_eq!(span.start, expected, "{error:?}");
    assert_eq!(&source[span.start..span.end], conflict, "{error:?}");
}

fn rejected(body: &str, label: &str, conflict: &str, occurrence: usize) {
    let source = format!(
        "{CHILD}\n(@#async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64 {body})))"
    );
    assert_borrow_error(&source, label, conflict, occurrence);
}

#[test]
fn rejects_shared_then_mutable_alias_while_local_loan_is_live_across_await() {
    rejected(
        "(#let-mut owner #u64 40u64)
      (#let view (#ref #u64) (#borrow owner))
      (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
      (#forget ignored)
      (#let alias (#ref-mut #u64) (#borrow-mut owner))
      (#drop alias) (#drop view) (#forget owner)
      (#return 0u64)",
        "async-shared-then-mut",
        "#borrow-mut",
        0,
    );
}

#[test]
fn rejects_mutable_alias_created_while_local_loan_is_live_across_await() {
    rejected(
        "(#let-mut owner #u64 40u64)
      (#let-mut view (#ref-mut #u64) (#borrow-mut owner))
      (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
      (#forget ignored)
      (#let alias (#ref #u64) (#borrow owner))
      (#drop alias) (#drop view) (#forget owner)
      (#return 0u64)",
        "async-mut-then-shared",
        "#borrow",
        1,
    );
}

#[test]
fn rejects_moving_owner_while_borrow_is_live_across_await() {
    let source = format!(
        "{CHILD}\n(#struct Owner (: value #u64)) (#linear Owner)
        (#fn destroy-owner (: value Owner) () (#forget value) (#return ()))
        (@#async-fn-pinned (: protocol WorkAwait : waker #u64
          : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child)))
          : function (#fn work () #u64
            (#let owner Owner (#struct-literal Owner (: value 40u64)))
            (#let view (#ref Owner) (#borrow owner))
            (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#let moved Owner owner)
            (#drop view) (#forget moved) (#forget ignored) (#return 0u64))))"
    );
    let error = compile_error(&source, "async-owner-move");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.expect("owner move conflict span");
    let moved = source.find("(#let moved Owner owner)").unwrap();
    let owner = moved + "(#let moved Owner ".len();
    assert_eq!(span.start, owner, "{error:?}");
    assert_eq!(&source[span.start..span.end], "owner", "{error:?}");
}

#[test]
fn rejects_scalar_owner_mutation_while_shared_borrow_is_live() {
    rejected(
        "(#let-mut owner #u64 40u64)
      (#let view (#ref #u64) (#borrow owner))
      (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
      (#set owner 41u64)
      (#let value #u64 (#deref view))
      (#drop view) (#forget owner) (#forget ignored) (#return value)",
        "async-owner-mutation",
        "#set",
        0,
    );
}

#[test]
fn rejects_returning_reference_to_async_local() {
    let source = format!(
        "{CHILD}\n(@#async-fn-pinned (: protocol WorkAwait : waker #u64
          : function (#fn work () (#ref #u64)
            (#let owner #u64 40u64)
            (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#forget ignored)
            (#return (#borrow owner)))))"
    );
    let error = compile_error(&source, "async-return-local-ref");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.expect("escaping local reference span");
    let returned = source.find("(#return (#borrow owner))").unwrap();
    assert_eq!(span.start, returned, "{error:?}");
    assert!(
        error
            .labels
            .iter()
            .any(|label| label.span.start == source.find("(#borrow owner)").unwrap()),
        "expected a label at the originating borrow: {error:?}"
    );
}

#[test]
fn movable_async_function_cannot_borrow_its_own_local_across_await() {
    let source = format!(
        "{CHILD}\n(@#async-fn (: protocol WorkAwait : waker #u64
          : function (#fn work () #u64
            (#let owner #u64 40u64)
            (#let view (#ref #u64) (#borrow owner))
            (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#let value #u64 (#deref view))
            (#drop view) (#forget owner) (#forget ignored) (#return value))))"
    );
    let error = compile_error(&source, "async-movable-self-borrow");
    assert!(
        matches!(
            error.code,
            DiagnosticCode::Generator | DiagnosticCode::Borrow | DiagnosticCode::Type
        ),
        "{error:?}"
    );
}

#[test]
fn pinned_local_shared_borrow_survives_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (@#async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64
            (#let owner #u64 40u64)
            (#let view (#ref #u64) (#borrow owner))
            (#let result #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#let answer #u64 (#u64.+.wrap (#deref view) result))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work ()))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
          (#let-else (work-pending pending-again) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (work-ready value) value)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64.== answer 42u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrows", 42);
}

#[test]
fn pinned_local_shared_shared_aliases_are_valid_across_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (@#async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64
            (#let owner #u64 40u64)
            (#let view (#ref #u64) (#borrow owner))
            (#let alias (#ref #u64) (#borrow owner))
            (#let result #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#let answer #u64 (#u64.+.wrap (#u64.+.wrap (#deref view) (#deref alias)) result))
            (#drop alias) (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work ()))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
          (#let-else (work-pending pending-again) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (work-ready value) value)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64.== answer 82u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrow-shared-alias", 42);
}

#[test]
fn pinned_local_mutable_borrow_survives_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (@#async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64
            (#let-mut owner #u64 40u64)
            (#let-mut view (#ref-mut #u64) (#borrow-mut owner))
            (#let result #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#deref-set view 41u64)
            (#let answer #u64 (#u64.+.wrap (#deref view) result))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work ()))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
          (#let-else (work-pending pending-again) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (work-ready value) value)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64.== answer 43u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrow-mutable", 42);
}

#[test]
fn pinned_local_nested_mutable_projection_survives_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (#struct Owner (: amount #i8)) (#linear Owner)
        (#fn destroy-owner (: value Owner) () (#forget value) (#return ()))
        (@#async-fn-pinned (: protocol WorkAwait : waker #u64
          : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child)))
          : function (#fn work () #u64
            (#let-mut owner Owner (#struct-literal Owner (: amount -1i8)))
            (#let-mut view (#ref-mut #i8) (#borrow-mut (#get owner amount)))
            (#let result #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#deref-set view 40i8)
            (#let amount #i8 (#deref view))
            (#let answer #u64 (#if (#i8.== amount 40i8) (#u64.+.wrap result 40u64) 0u64))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work ()))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
          (#let-else (work-pending pending-again) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (work-ready value) value)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64.== answer 42u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrow-nested-mutable", 42);
}

#[test]
fn pinned_shared_owner_reference_reads_second_field_after_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (#struct Owner (: first #u64 : second #i8)) (#linear Owner)
        (#fn destroy-owner (: value Owner) () (#forget value) (#return ()))
        (@#async-fn-pinned (: protocol WorkAwait : waker #u64
          : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child)))
          : function (#fn work () #u64
            (#let owner Owner (#struct-literal Owner (: first 7u64 : second -1i8)))
            (#let view (#ref Owner) (#borrow owner))
            (#let result #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
            (#let second #i8 (#get view second))
            (#let answer #u64 (#if (#i8.== second -1i8) (#u64.+.wrap result 40u64) 0u64))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work-frame (#call work ()))
          (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
          (#let-else (work-pending pending-again) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (work-ready value) value)
            (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64.== answer 42u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrow-multifield-shared", 42);
}

fn run_native(source: &str, label: &str, expected: i32) {
    let scratch = support::Scratch::new(label);
    let input = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let compile = || {
        lim::compile_source_to_assembly(
            &source,
            &input,
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
    };
    let cold = compile().unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let warm = compile().unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(cold, warm, "cold and warm compilation differ");
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &warm,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(expected), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn forgetting_a_pending_handle_does_not_make_the_self_referential_frame_movable() {
    let source = format!(
        "{CHILD}
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work () #u64
          (#let owner #u64 40u64)
          (#let view (#ref #u64) (#borrow owner))
          (#let result #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#let answer #u64 (#u64.+.wrap (#deref view) result))
          (#drop view) (#forget owner) (#return answer))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work-frame (#call work ()))
        (#let first Work-poll-result (#call work-poll
          (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#forget first)
        (#let moved Work-frame task)
        (#forget moved) (#return 0u64))"
    );
    let error = compile_error(&source, "async-forgotten-pin-still-stationary");
    assert!(error.message.contains("stationary"), "{}", error.message);
    let span = error.span.expect("pinned move must be source-spanned");
    assert!(source[span.start..span.end].contains("task"));
}
