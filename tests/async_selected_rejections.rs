mod support;

use lim::{Diagnostic, DiagnosticCode};

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

const CONTEXT: &str = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
      (#return (#match task
        (#case (Child.Waiting count)
          (#if (#u64::eq count 0u64)
            (ChildPoll.ChildPending (Child.Waiting 1u64))
            (ChildPoll.ChildReady count)))))
#fn cancel-child ((child Child)) () (#forget child) (#return ())
#struct Owner (#linear) ((value #u64))
#fn destroy-owner ((owner Owner)) () (#forget owner) (#return ())\n";

fn checked_source(body: &str, pinned: bool, return_type: &str) -> String {
    let annotation = if pinned {
        "#async-fn-pinned"
    } else {
        "#async-fn"
    };
    let cancel = "(cancel (work-cancel ((left destroy-owner) (right destroy-owner) (await-0 cancel-child))))";
    let main = if pinned {
        "#fn main () #u64
            (#let waker #u64 0u64)
            (#let-mut frame Work::Frame (#call work ((choose true))))
            (#let result Work::Poll
              (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
            (#forget result) (#forget frame) (#forget waker) (#return 0u64)\n"
    } else {
        "#fn main () #u64 (#let task Work::Task (#call work ((choose true))))
            (#forget task) (#return 0u64)\n"
    };
    format!(
        "{CONTEXT}
#generate {annotation} ((protocol WorkAwait) (waker #u64) {cancel}
            (function (#fn work ((choose #bool)) {return_type} {body})))
{main}"
    )
}

fn compile_error(source: &str, label: &str) -> (support::Scratch, Diagnostic) {
    let scratch = support::Scratch::new(label);
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("adversarial selected borrow must be rejected");
    (scratch, error)
}

fn assert_source_span(source: &str, error: &Diagnostic, anchor: &str, needle: &str) {
    let base = source.find(anchor).expect("diagnostic anchor is in source");
    let start = base
        + source[base..]
            .find(needle)
            .expect("span needle follows anchor");
    let span = error.span.expect("diagnostic should carry a source span");
    assert_eq!(span.start, start, "{error:?}");
    assert_eq!(&source[span.start..span.end], needle, "{error:?}");
}

fn assert_unpublished(scratch: &support::Scratch) {
    assert!(
        !scratch.path().join("cache").exists(),
        "invalid source published compiler cache entries"
    );
}

fn selected_view(mutable: bool) -> &'static str {
    if mutable {
        "(#let-mut left Owner (#struct-literal Owner ((value 40u64))))
         (#let-mut right Owner (#struct-literal Owner ((value 50u64))))
         (#let-mut view (#ref-mut Owner)
           (#if choose (#borrow-mut left) (#borrow-mut right)))"
    } else {
        "(#let-mut left Owner (#struct-literal Owner ((value 40u64))))
         (#let-mut right Owner (#struct-literal Owner ((value 50u64))))
         (#let view (#ref Owner) (#if choose (#borrow left) (#borrow right)))"
    }
}

#[test]
fn selected_shared_reference_rejects_mutating_either_owner_across_await() {
    for owner in ["left", "right"] {
        let body = format!(
            "{}\n(#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
             (#set-field {owner} value 99u64)
             (#let observed #u64 (#get view value))
             (#drop view) (#forget left) (#forget right) (#forget ignored)
             (#return observed)",
            selected_view(false)
        );
        let source = checked_source(&body, true, "#u64");
        let (scratch, error) = compile_error(&source, "selected-mutate-owner");
        assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
        assert_source_span(&source, &error, "(#set-field", "#set-field");
        assert_unpublished(&scratch);
    }
}

#[test]
fn selected_shared_reference_rejects_moving_either_owner_across_await() {
    for owner in ["left", "right"] {
        let body = format!(
            "{}\n(#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
             (#let moved Owner {owner})
             (#drop view) (#forget moved) {forget_other}
             (#forget ignored) (#return 0u64)",
            selected_view(false),
            forget_other = if owner == "left" {
                "(#forget right)"
            } else {
                "(#forget left)"
            }
        );
        let source = checked_source(&body, true, "#u64");
        let (scratch, error) = compile_error(&source, "selected-move-owner");
        assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
        assert_source_span(
            &source,
            &error,
            &format!("(#let moved Owner {owner})"),
            owner,
        );
        assert_unpublished(&scratch);
    }
}

#[test]
fn selected_borrow_rejects_shared_mutable_alias_conflicts_for_both_owners() {
    for (selected_mutable, alias_mutable) in [(false, true), (true, false)] {
        for owner in ["left", "right"] {
            let alias_ty = if alias_mutable {
                "(#ref-mut Owner)"
            } else {
                "(#ref Owner)"
            };
            let alias_borrow = if alias_mutable {
                "borrow-mut"
            } else {
                "borrow"
            };
            let body = format!(
                "{}\n(#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
                 (#let alias {alias_ty} (#{alias_borrow} {owner}))
                 (#let observed #u64 (#get view value))
                 (#drop alias) (#drop view) (#forget left) (#forget right)
                 (#forget ignored) (#return observed)",
                selected_view(selected_mutable)
            );
            let source = checked_source(&body, true, "#u64");
            let (scratch, error) = compile_error(&source, "selected-alias-conflict");
            assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
            assert_source_span(&source, &error, "(#let alias", &format!("#{alias_borrow}"));
            assert_unpublished(&scratch);
        }
    }
}

#[test]
fn returning_selected_reference_to_local_owners_is_rejected() {
    let body = "(#let left #u64 40u64) (#let right #u64 50u64)
      (#let view (#ref #u64) (#if choose (#borrow left) (#borrow right)))
      (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
      (#forget ignored) (#return view)";
    let source = checked_source(body, true, "(#ref #u64)").replace(
        "((left destroy-owner) (right destroy-owner) (await-0 cancel-child))",
        "((await-0 cancel-child))",
    );
    let (scratch, error) = compile_error(&source, "selected-return-local");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    assert_source_span(&source, &error, "(#return view)", "(#return view)");
    assert_unpublished(&scratch);
}

#[test]
fn movable_async_frame_cannot_hold_a_selected_local_reference_across_await() {
    let body = format!(
        "{}\n(#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
         (#let observed #u64 (#get view value))
         (#drop view) (#forget left) (#forget right) (#forget ignored) (#return observed)",
        selected_view(false)
    );
    let source = checked_source(&body, false, "#u64");
    let (scratch, error) = compile_error(&source, "selected-movable-frame");
    assert!(
        matches!(
            error.code,
            DiagnosticCode::Generator | DiagnosticCode::Borrow | DiagnosticCode::Type
        ),
        "{error:?}"
    );
    assert!(error.span.is_some(), "expected a source span: {error:?}");
    assert_unpublished(&scratch);
}
