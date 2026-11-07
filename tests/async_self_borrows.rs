#[path = "support/generated_source.rs"]
mod generated_source;
mod support;

use lim::{Diagnostic, DiagnosticCode};
use std::{process::Command, time::Duration};

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

const CHILD: &str = "(#enum Child (#linear) ((Child.Waiting #u64)))
  (#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64)))
  (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
    (#return (#match task
      (#case (Child.Waiting count)
        (#if (#u64::lt count 2u64)
          (ChildPoll.ChildPending (Child.Waiting (#u64::add-wrap count 1u64)))
          (ChildPoll.ChildReady count))))))
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
        "{CHILD}\n(#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64 {body})))"
    );
    assert_borrow_error(&source, label, conflict, occurrence);
}

#[test]
fn pinned_nested_enum_payload_borrows_survive_cold_and_cached_suspension() {
    let source = include_str!("../examples/async_fn_enum_self_reference.lim");
    run_native(source, "async-word-enum-payload-shared", 42);
    let mutable = source
        .replace(
            "((owner Owner)) #u64",
            "((input Owner)) #u64\n    (#let-mut owner Owner input)",
        )
        .replace(
            "(: owner (#struct-literal Owner",
            "(: input (#struct-literal Owner",
        )
        .replace("(#pin-ref #u64)", "(#pin-ref-mut #u64)")
        .replace("(#pin-borrow ", "(#pin-borrow-mut ")
        .replace("(#pin-borrow\n", "(#pin-borrow-mut\n")
        .replace(": mode #pin-ref ", ": mode #pin-ref-mut ")
        .replace(
            "(#return (#u64::add-wrap (#deref view) result))",
            "(#unsafe (#pin-write view 40u64)) (#return (#u64::add-wrap (#deref view) result))",
        );
    run_native(&mutable, "async-word-enum-payload-exclusive", 42);
    let mutable_parameter = mutable
        .replace(
            "((input Owner)) #u64\n    (#let-mut owner Owner input)",
            "((#mut owner Owner)) #u64",
        )
        .replace(
            "(: input (#struct-literal Owner",
            "(: owner (#struct-literal Owner",
        );
    run_native(
        &mutable_parameter,
        "async-word-enum-payload-mutable-parameter",
        42,
    );
    let immutable_parameter = mutable_parameter.replace("((#mut owner Owner))", "((owner Owner))");
    let error = compile_error(
        &immutable_parameter,
        "async-word-enum-payload-immutable-parameter",
    );
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    let overlapping = mutable.replacen(
        "(#let result #u64",
        "(#let conflict (#pin-ref-mut Owner) (#pin-borrow-mut owner))\n    (#let result #u64",
        1,
    );
    let error = compile_error(&overlapping, "async-word-enum-payload-overlap");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
}

#[test]
fn scope_exit_retires_implicit_shared_handles_before_their_local_owner() {
    run_native(
        include_str!("../examples/async_fn_local_self_reference.lim"),
        "async-scope-exit-local-reference",
        42,
    );
}

#[test]
fn rejects_shared_then_mutable_alias_while_local_loan_is_live_across_await() {
    rejected(
        "(#let-mut owner #u64 40u64)
      (#let view (#ref #u64) (#borrow owner))
      (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
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
      (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
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
        "{CHILD}\n(#struct Owner (#linear) (: value #u64))
        (#fn destroy-owner (: value Owner) () (#forget value) (#return ()))
        (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
          : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child)))
          : function (#fn work () #u64
            (#let owner Owner (#struct-literal Owner (: value 40u64)))
            (#let view (#ref Owner) (#borrow owner))
            (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
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
      (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
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
        "{CHILD}\n(#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
          : function (#fn work () (#ref #u64)
            (#let owner #u64 40u64)
            (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
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
        "{CHILD}\n(#generate #async-fn (: protocol WorkAwait : waker #u64
          : function (#fn work () #u64
            (#let owner #u64 40u64)
            (#let view (#ref #u64) (#borrow owner))
            (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
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
        (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64
            (#let owner #u64 40u64)
            (#let view (#ref #u64) (#borrow owner))
            (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#let answer #u64 (#u64::add-wrap (#deref view) result))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending-again) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64::eq answer 42u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrows", 42);
}

#[test]
fn pinned_local_shared_shared_aliases_are_valid_across_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64
            (#let owner #u64 40u64)
            (#let view (#ref #u64) (#borrow owner))
            (#let alias (#ref #u64) (#borrow owner))
            (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#let answer #u64 (#u64::add-wrap (#u64::add-wrap (#deref view) (#deref alias)) result))
            (#drop alias) (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending-again) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64::eq answer 82u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrow-shared-alias", 42);
}

#[test]
fn pinned_local_mutable_borrow_survives_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
          : function (#fn work () #u64
            (#let-mut owner #u64 40u64)
            (#let-mut view (#ref-mut #u64) (#borrow-mut owner))
            (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#deref-set view 41u64)
            (#let answer #u64 (#u64::add-wrap (#deref view) result))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending-again) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64::eq answer 43u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrow-mutable", 42);
}

#[test]
fn pinned_local_nested_mutable_projection_survives_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (#struct Owner (#linear) (: amount #i8))
        (#fn destroy-owner (: value Owner) () (#forget value) (#return ()))
        (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
          : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child)))
          : function (#fn work () #u64
            (#let-mut owner Owner (#struct-literal Owner (: amount -1i8)))
            (#let-mut view (#ref-mut #i8) (#borrow-mut (#get owner amount)))
            (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#deref-set view 40i8)
            (#let amount #i8 (#deref view))
            (#let answer #u64 (#if (#i8::eq amount 40i8) (#u64::add-wrap result 40u64) 0u64))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending-again) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64::eq answer 42u64) 42u64 0u64)))"
    );
    run_native(&source, "async-self-borrow-nested-mutable", 42);
}

#[test]
fn pinned_shared_owner_reference_reads_second_field_after_repeated_pending_polls() {
    let source = format!(
        "{CHILD}
        (#struct Owner (#linear) (: first #u64 : second #i8))
        (#fn destroy-owner (: value Owner) () (#forget value) (#return ()))
        (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
          : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child)))
          : function (#fn work () #u64
            (#let owner Owner (#struct-literal Owner (: first 7u64 : second -1i8)))
            (#let view (#ref Owner) (#borrow owner))
            (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#let second #i8 (#get view second))
            (#let answer #u64 (#if (#i8::eq second -1i8) (#u64::add-wrap result 40u64) 0u64))
            (#drop view) (#forget owner) (#return answer))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
          (#let-else (Work::Poll.Pending pending-again) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll (: task pending-again : waker (#borrow waker))))
          (#let answer #u64 (#match third
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget task) (#return (#if (#u64::eq answer 42u64) 42u64 0u64)))"
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

fn selected_array_elements_source(mutable: bool) -> String {
    let suffix = if mutable { "-mut" } else { "" };
    let write = if mutable {
        "(#deref-set view 42u64)"
    } else {
        ""
    };
    let (left_result, right_result, external_value) =
        if mutable { (44, 44, 42) } else { (42, 52, 50) };
    format!("{CHILD}
          (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
            : function (#fn work (: choose #bool : external (#ref{suffix} (#array #u64 4))) #u64
              (#let-mut owner (#array #u64 3) (#array-of (#array #u64 3) 1u64 40u64 3u64))
              (#let view (#ref{suffix} #u64) (#if choose
                (#borrow{suffix} (#index owner 1usize))
                (#borrow{suffix} (#index external 2usize))))
              (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
              {write}
              (#let answer #u64 (#u64::add-wrap (#deref view) ignored))
              (#drop view) (#assert (#u64::eq (#index owner 0usize) 1u64))
              (#assert (#u64::eq (#index owner 2usize) 3u64))
              (#forget owner) (#return answer))))
          (#fn run (: choose #bool : cancel #bool) #u64
            (#let-mut external (#array #u64 4)
              (#array-of (#array #u64 4) 4u64 5u64 50u64 7u64))
            (#let waker #u64 0u64)
            (#let-mut task Work::Frame (#call work (: choose choose : external (#borrow{suffix} external))))
            (#let first Work::Poll
              (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
            (#drop next)
            (#if cancel (#block
              (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
              (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
              (#set-index external 2usize 42u64) (#forget task) (#return 42u64)) ())
            (#let answer #u64 (#loop
              (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
                (#case (Work::Poll.Pending later) (#block (#drop later) (#continue)))
                (#case (Work::Poll.Ready value) (#block (#break value))))))
            (#forget task)
            (#assert (#u64::eq (#index external 0usize) 4u64))
            (#assert (#u64::eq (#index external 3usize) 7u64))
            (#assert (#u64::eq (#index external 2usize) (#if choose 50u64 {external_value}u64)))
            (#return answer))
          (#fn main () #u64
            (#assert (#u64::eq (#call run (: choose true : cancel false)) {left_result}u64))
            (#assert (#u64::eq (#call run (: choose false : cancel false)) {right_result}u64))
            (#assert (#u64::eq (#call run (: choose true : cancel true)) 42u64))
            (#return (#call run (: choose false : cancel true))))")
}

#[test]
fn runtime_selected_array_indices_are_not_reread_after_suspension() {
    for mutable in [false, true] {
        let suffix = if mutable { "-mut" } else { "" };
        let source = selected_array_elements_source(mutable)
            .replace(
                "(#let view (#ref",
                "(#let-mut selected #usize 1usize)\n(#let view (#ref",
            )
            .replace("(#index owner 1usize)", "(#index owner selected)")
            .replace(
                &format!("(#borrow{suffix} (#index external 2usize))"),
                &format!("(#borrow{suffix} (#index external (#usize::add-wrap selected 1usize)))"),
            )
            .replace(
                "(#let ignored #u64 (#await",
                "(#set selected 0usize)\n(#let ignored #u64 (#await",
            );
        assert!(source.contains("(#index owner selected)"));
        assert_independent_generated_source(&source);
        run_native(&source, "async-runtime-array-selection", 42);
        let conflicting = source.replace(
            "(#drop next)",
            "(#drop next)\n(#set-index external 2usize 99u64)",
        );
        assert_borrow_error(
            &conflicting,
            "async-runtime-array-caller-conflict",
            "#set-index",
            0,
        );
    }
}

#[test]
fn selected_array_elements_preserve_offsets_and_external_loans() {
    for mutable in [false, true] {
        let source = selected_array_elements_source(mutable);
        assert_independent_generated_source(&source);
        run_native(&source, "async-selected-array-elements", 42);
    }
}

fn assert_independent_generated_source(source: &str) {
    let scratch = support::Scratch::new("async-array-independent-source");
    let input = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let output = scratch.path().join("generated");
    lim::write_generated_sources_from_path_with_config_and_cache(
        source,
        &input,
        &output,
        &config(),
        &cache,
    )
    .unwrap();
    let mut standalone = source.to_owned();
    for invocation in lim::parse(source).unwrap().into_iter().rev() {
        if source[invocation.span.start..invocation.span.end].starts_with("(#generate ") {
            standalone.replace_range(invocation.span.start..invocation.span.end, "");
        }
    }
    for entry in std::fs::read_dir(output).unwrap() {
        standalone.push('\n');
        let artifact = std::fs::read_to_string(entry.unwrap().path()).unwrap();
        standalone.push_str(&generated_source::ordinary_source(&artifact));
    }
    let program = lim::parse_program(&standalone).unwrap();
    lim::check_types(&program).unwrap_or_else(|error| panic!("{error}\n{standalone}"));
    lim::generate_assembly(&program).unwrap();
}

#[test]
fn selected_array_future_keeps_the_callers_array_borrowed() {
    for mutable in [false, true] {
        let source = selected_array_elements_source(mutable).replace(
            "(#drop next)",
            "(#drop next)\n(#set-index external 2usize 99u64)",
        );
        assert_borrow_error(
            &source,
            "async-selected-array-caller-conflict",
            "#set-index",
            0,
        );
    }
}

#[test]
fn dormant_out_of_bounds_array_anchor_is_not_probed() {
    let source = format!(
        "{CHILD}
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
        : function (#fn work (: choose #bool) #u64
          (#let left (#array #u64 3) (#array-of (#array #u64 3) 1u64 2u64 3u64))
          (#let right (#array #u64 4) (#array-of (#array #u64 4) 4u64 5u64 50u64 7u64))
          (#let view (#ref #u64) (#if choose
            (#borrow (#index left 8usize)) (#borrow (#index right 2usize))))
          (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
          (#return (#u64::add-wrap (#deref view) result)))))
      (#fn main () #u64 (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (: choose false)))
        (#let answer #u64 (#loop
          (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
            (#case (Work::Poll.Pending next) (#block (#drop next) (#continue)))
            (#case (Work::Poll.Ready value) (#block (#break value))))))
        (#forget task) (#return answer))"
    );
    run_native(&source, "async-dormant-array-anchor", 52);
}

#[test]
fn selected_internal_reference_keeps_its_owner_across_repeated_pending() {
    for mutable in [false, true] {
        let suffix = if mutable { "-mut" } else { "" };
        let write = if mutable {
            "(#deref-set view 42u64)"
        } else {
            ""
        };
        let owner_check = if mutable {
            "(#assert (#if choose (#bool::and (#u64::eq left 42u64) (#u64::eq right 50u64))
              (#bool::and (#u64::eq left 40u64) (#u64::eq right 42u64))))"
        } else {
            ""
        };
        let (left_result, right_result) = if mutable { (44, 44) } else { (42, 52) };
        let source = format!("{CHILD}
          (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
            : function (#fn work (: choose #bool) #u64
              (#let-mut left #u64 40u64)
              (#let-mut right #u64 50u64)
              (#let view (#ref{suffix} #u64)
                (#if choose (#borrow{suffix} left) (#borrow{suffix} right)))
              (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
              {write}
              (#let answer #u64 (#u64::add-wrap (#deref view) ignored))
              (#drop view) {owner_check} (#forget left) (#forget right) (#return answer))))
          (#fn run (: choose #bool) #u64
            (#let waker #u64 0u64)
            (#let-mut task Work::Frame (#call work (($ choose))))
            (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
            (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
            (#let second Work::Poll (#call Work::poll (: task next : waker (#borrow waker))))
            (#let-else (Work::Poll.Pending last) Work::Poll second (#unreachable))
            (#let answer #u64 (#match (#call Work::poll (: task last : waker (#borrow waker)))
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
            (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
            (#forget task) (#return answer))
          (#fn main () #u64
            (#assert (#u64::eq (#call run (: choose true)) {left_result}u64))
            (#assert (#u64::eq (#call run (: choose false)) {right_result}u64))
            (#return 42u64))");
        run_native(&source, "async-selected-internal-reference", 42);
    }
}

#[test]
fn mixed_internal_external_reference_retains_caller_storage() {
    for mutable in [false, true] {
        let suffix = if mutable { "-mut" } else { "" };
        let write = if mutable {
            "(#deref-set view 42u64)"
        } else {
            ""
        };
        let release_parameter = if mutable { "" } else { "(#drop external)" };
        let (inside, outside) = if mutable { (44, 44) } else { (42, 52) };
        let external_value = if mutable {
            "(#if choose 50u64 42u64)"
        } else {
            "50u64"
        };
        let source = format!("{CHILD}
          (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
            : function (#fn work (: external (#ref{suffix} #u64) : choose #bool) #u64
              (#let-mut owner #u64 40u64)
              (#let view (#ref{suffix} #u64) (#if choose (#borrow{suffix} owner) external))
              {release_parameter}
              (#let extra #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
              {write}
              (#let answer #u64 (#u64::add-wrap (#deref view) extra))
              (#drop view) (#forget owner) (#return answer))))
          (#fn run (: choose #bool) #u64
            (#let-mut external #u64 50u64) (#let waker #u64 0u64)
            (#let-mut task Work::Frame (#call work (: external (#borrow{suffix} external) : choose choose)))
            (#let answer #u64 (#loop
              (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
                (#case (Work::Poll.Pending next) (#block (#drop next) (#continue)))
                (#case (Work::Poll.Ready value) (#block (#break value))))))
            (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
            (#forget task) (#assert (#u64::eq external {external_value})) (#return answer))
          (#fn main () #u64
            (#assert (#u64::eq (#call run (: choose true)) {inside}u64))
            (#assert (#u64::eq (#call run (: choose false)) {outside}u64)) (#return 42u64))");
        run_native(&source, "async-mixed-reference", 42);
    }
}

#[test]
fn mixed_external_projection_preserves_native_layout_and_releases_on_cancel() {
    let source = format!("{CHILD}
      (#struct Outside () (: other #u64 : selected #u64))
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
        : function (#fn work (: external (#ref-mut Outside) : choose #bool) #u64
          (#let-mut owner (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) 80u64 40u64))
          (#let view (#ref-mut #u64) (#if choose
            (#borrow-mut (#get owner 1)) (#borrow-mut (#get external selected))))
          (#let extra #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
          (#deref-set view 42u64)
          (#let answer #u64 (#u64::add-wrap (#deref view) extra))
          (#drop view) (#forget owner) (#return answer))))
      (#fn run (: choose #bool : cancel #bool) #u64
        (#let-mut external Outside (#struct-literal Outside (: other 90u64 : selected 50u64)))
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (: external (#borrow-mut external) : choose choose)))
        (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
        (#drop next)
        (#if cancel (#block
          (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
          (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
          (#forget task)
          (#assert (#u64::eq (#get external selected) 50u64))
          (#return 42u64)) ())
        (#let answer #u64 (#loop
          (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
            (#case (Work::Poll.Pending later) (#block (#drop later) (#continue)))
            (#case (Work::Poll.Ready value) (#block (#break value))))))
        (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
        (#forget task)
        (#assert (#u64::eq (#get external other) 90u64))
        (#assert (#u64::eq (#get external selected) (#if choose 50u64 42u64)))
        (#return answer))
      (#fn main () #u64
        (#assert (#u64::eq (#call run (: choose true : cancel false)) 44u64))
        (#assert (#u64::eq (#call run (: choose false : cancel false)) 44u64))
        (#assert (#u64::eq (#call run (: choose true : cancel true)) 42u64))
        (#assert (#u64::eq (#call run (: choose false : cancel true)) 42u64)) (#return 42u64))");
    run_native(&source, "async-mixed-external-projection", 42);
}

#[test]
fn mixed_selected_future_cannot_erase_a_callers_borrow_or_escape_its_local() {
    let work = format!(
        "{CHILD}
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
        : function (#fn work (: external (#ref #u64) : choose #bool) #u64
          (#let owner #u64 40u64)
          (#let view (#ref #u64) (#if choose (#borrow owner) external))
          (#let extra #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
          (#let answer #u64 (#u64::add-wrap (#deref view) extra))
          (#drop view) (#return answer))))"
    );
    let conflict = "(#set external 99u64)";
    let source = format!("{work}
      (#fn main () #u64
        (#let-mut external #u64 50u64) (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (: external (#borrow external) : choose true)))
        (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#forget first) {conflict} (#forget task) (#return 0u64))");
    assert_borrow_error(&source, "async-mixed-caller-mutation", "#set", 0);
    let escaping = format!(
        "{work}
      (#fn escape () Work::Frame
        (#let local #u64 50u64)
        (#return (#call work (: external (#borrow local) : choose false))))"
    );
    let error = compile_error(&escaping, "async-mixed-caller-escape");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some());
}

#[test]
fn mixed_aggregate_reference_preserves_stack_and_frame_layouts() {
    let source = format!(
        "{CHILD}
      (#struct Values () (: first #u64 : second #u64 : third #u64 : fourth #u64
        : fifth #u64 : sixth #u64 : seventh #u64 : last #u64))
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
        : function (#fn work (: external (#ref-mut Values) : choose #bool) #u64
          (#let-mut owner Values (#struct-literal Values (: first 1u64 : second 2u64
            : third 3u64 : fourth 4u64 : fifth 5u64 : sixth 6u64 : seventh 7u64 : last 40u64)))
          (#let-mut view (#ref-mut Values) (#if choose (#borrow-mut owner) external))
          (#let extra #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
          (#deref-set (#borrow-mut (#get view last)) 42u64)
          (#assert (#u64::eq (#get view first) (#if choose 1u64 10u64)))
          (#let answer #u64 (#u64::add-wrap (#get view last) extra))
          (#drop view) (#forget owner) (#return answer))))
      (#fn run (: choose #bool) #u64
        (#let-mut external Values (#struct-literal Values (: first 10u64 : second 20u64
          : third 30u64 : fourth 40u64 : fifth 50u64 : sixth 60u64 : seventh 70u64 : last 80u64)))
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (: external (#borrow-mut external) : choose choose)))
        (#let answer #u64 (#loop
          (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
            (#case (Work::Poll.Pending next) (#block (#drop next) (#continue)))
            (#case (Work::Poll.Ready value) (#block (#break value))))))
        (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
        (#forget task) (#assert (#u64::eq (#get external first) 10u64))
        (#assert (#u64::eq (#get external last) (#if choose 80u64 42u64))) (#return answer))
      (#fn main () #u64
        (#assert (#u64::eq (#call run (: choose true)) 44u64))
        (#assert (#u64::eq (#call run (: choose false)) 44u64)) (#return 42u64))"
    );
    run_native(&source, "async-mixed-aggregate-layout", 42);
}

#[test]
fn selected_internal_projections_preserve_offsets_and_mutable_writes() {
    let source = format!(
        "{CHILD}
      (#struct Left (#linear) (: selected #u64 : other #u64))
      (#struct Right (#linear) (: other #u64 : selected #u64))

      (#fn destroy-left (: value Left) ()
        (#assert (#u64::eq (#get value selected) 10u64)) (#forget value) (#return ()))
      (#fn destroy-right (: value Right) ()
        (#assert (#u64::eq (#get value selected) 20u64)) (#forget value) (#return ()))
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (work-cancel ((left destroy-left) (right destroy-right) (await-0 cancel-child)))
        : function (#fn work (: choose #bool) #u64
          (#let-mut left Left (#struct-literal Left (: selected 10u64 : other 80u64)))
          (#let-mut right Right (#struct-literal Right (: other 90u64 : selected 20u64)))
          (#let view (#ref-mut #u64) (#if choose
            (#borrow-mut (#get left selected)) (#borrow-mut (#get right selected))))
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
          (#deref-set view 42u64) (#drop view) (#forget ignored)
          (#assert (#u64::eq (#get left other) 80u64))
          (#assert (#u64::eq (#get right other) 90u64))
          (#let answer #u64 (#if choose (#get left selected) (#get right selected)))
          (#assert (#u64::eq (#if choose (#get right selected) (#get left selected))
            (#if choose 20u64 10u64)))
          (#forget left) (#forget right) (#return answer))))
      (#fn run (: choose #bool) #u64
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (($ choose))))
        (#let answer #u64 (#loop
          (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
            (#case (Work::Poll.Pending next) (#block (#drop next) (#continue)))
            (#case (Work::Poll.Ready value) (#block (#break value))))))
        (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
        (#forget task) (#return answer))
      (#fn cancel-run (: choose #bool) ()
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (($ choose))))
        (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
        (#call work-cancel (: task (#call Work::Poll::cleanup (: task next))))
        (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
        (#forget task) (#return ()))
      (#fn main () #u64
        (#call cancel-run (: choose true)) (#call cancel-run (: choose false))
        (#assert (#u64::eq (#call run (: choose true)) 42u64))
        (#return (#call run (: choose false))))"
    );
    run_native(&source, "async-selected-internal-projections", 42);
}

#[test]
fn selected_internal_reference_can_switch_owners_on_loop_backedges() {
    let source = format!(
        "{CHILD}
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 {CANCEL}
        : function (#fn work () #u64
          (#let left #u64 40u64) (#let right #u64 50u64)
          (#let-mut iteration #u64 0u64) (#let-mut total #u64 0u64)
          (#while (#u64::lt iteration 2u64)
            (#let view (#ref #u64) (#if (#u64::eq iteration 0u64) (#borrow left) (#borrow right)))
            (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#forget ignored) (#set total (#u64::add-wrap total (#deref view))) (#drop view)
            (#set iteration (#u64::add-wrap iteration 1u64)))
          (#forget left) (#forget right) (#return total))))
      (#fn main () #u64
        (#let waker #u64 0u64) (#let-mut task Work::Frame (#call work ()))
        (#let answer #u64 (#loop
          (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
            (#case (Work::Poll.Pending next) (#block (#drop next) (#continue)))
            (#case (Work::Poll.Ready value) (#block (#break value))))))
        (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
        (#forget task) (#assert (#u64::eq answer 90u64)) (#return 42u64))"
    );
    run_native(&source, "async-selected-internal-loop", 42);
}

#[test]
fn selected_internal_references_do_not_invent_branch_correlated_consumption() {
    let source = format!(
        "{CHILD}
      (#struct Owner (#linear) (: value #u64))
      (#fn destroy-owner (: value Owner) () (#forget value) (#return ()))
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (work-cancel ((left destroy-owner) (right destroy-owner) (await-0 cancel-child)))
        : function (#fn work (: choose #bool) #u64
          (#let left Owner (#struct-literal Owner (: value 40u64)))
          (#let right Owner (#struct-literal Owner (: value 50u64)))
          (#let view (#ref #u64) (#if choose
            (#block (#forget right) (#borrow (#get left value)))
            (#block (#forget left) (#borrow (#get right value)))))
          (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
          (#let answer #u64 (#u64::add-wrap (#deref view) ignored))
          (#drop view) (#if choose (#forget left) (#forget right)) (#return answer))))
      (#fn run (: choose #bool) #u64
        (#let waker #u64 0u64) (#let-mut task Work::Frame (#call work (($ choose))))
        (#let answer #u64 (#loop
          (#match (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker)))
            (#case (Work::Poll.Pending next) (#block (#drop next) (#continue)))
            (#case (Work::Poll.Ready value) (#block (#break value))))))
        (#call work-cancel (: task (#call Work::Poll::cleanup (: task (#pin-borrow-mut task)))))
        (#forget task) (#return answer))
      (#fn main () #u64
        (#assert (#u64::eq (#call run (: choose true)) 42u64))
        (#assert (#u64::eq (#call run (: choose false)) 52u64)) (#return 42u64))"
    );
    let error = compile_error(&source, "async-selected-correlated-consumption");
    assert_eq!(error.code, DiagnosticCode::Linear, "{error:?}");
    assert!(error.message.contains("already consumed"), "{error:?}");
    let span = error.span.expect("conflicting consumption span");
    assert_eq!(&source[span.start..span.end], "left");
}

#[test]
fn forgetting_a_pending_handle_does_not_make_the_self_referential_frame_movable() {
    let source = format!(
        "{CHILD}
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work () #u64
          (#let owner #u64 40u64)
          (#let view (#ref #u64) (#borrow owner))
          (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
          (#let answer #u64 (#u64::add-wrap (#deref view) result))
          (#drop view) (#forget owner) (#return answer))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work ()))
        (#let first Work::Poll (#call Work::poll
          (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#forget first)
        (#let moved Work::Frame task)
        (#forget moved) (#return 0u64))"
    );
    let error = compile_error(&source, "async-forgotten-pin-still-stationary");
    assert!(error.message.contains("stationary"), "{}", error.message);
    let span = error.span.expect("pinned move must be source-spanned");
    assert!(source[span.start..span.end].contains("task"));
}
