#[path = "../support/mod.rs"]
mod support;

use std::{process::Command, time::Duration};

fn run(body: &str, label: &str) {
    run_storage(body, label, true);
}

fn run_storage(body: &str, label: &str, pinned: bool) {
    let source = format!(
        r#"
        (#enum Child (#linear) ((Child.Start #u64) (Child.Resume #u64)))
        (#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64)))
        (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
          (#return (#match task
            (#case (Child.Start value) (ChildPoll.ChildPending (Child.Resume value)))
            (#case (Child.Resume value) (ChildPoll.ChildReady value)))))
        (#struct Owner () ((values (#array #u64 2))))
        (#type WideRow (#array #u128 2))
        (#generate #async-fn-pinned ((protocol work-await) (waker #u64)
          (function (#fn work ((seed #u64)) #u64 {body}))))
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ((seed 42u64))))
          (#let first Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending) (#block (#forget pending) (#unreachable)))))
          (#forget task) (#return answer))
        "#
    );
    let source = if pinned {
        source
    } else {
        source
            .replace("#generate #async-fn-pinned", "#generate #async-fn")
            .replace("(#let-mut task Work::Frame", "(#let task Work::Task")
            .replace("(#pin-borrow-mut task)", "task")
            .replace("(#forget task) (#return answer)", "(#return answer)")
    };
    let scratch = support::Scratch::new(label);
    let syntax = crate::prepare_program_syntax(
        &source,
        scratch.path(),
        None,
        &crate::CompileConfig::default(),
        None,
    )
    .unwrap();
    let planning = crate::generator::async_prepare::prepare(&syntax).unwrap();
    let generated = crate::generator::async_emit::generate(&planning).unwrap();
    let program = crate::generator::async_emit::program(&planning, &generated).unwrap();
    let checked = crate::CheckedProgram::validate_with_span(&program)
        .unwrap_or_else(|error| panic!("{error:?}\n{}", generated[0].source));
    let assembly = crate::codegen::generate_checked_executable_assembly(
        &checked,
        crate::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let binary = scratch.path().join("program");
    crate::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        crate::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn nested_struct_array_read_survives_pending() {
    run(
        "(#let owner Owner (#struct-literal Owner ((values (#array-of (#array #u64 2) 0u64 seed)))))
          (#let amount #u64 (#index (#get owner values) 1usize))
          (#let child #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)))
          (#forget owner) (#return (#u64::add-wrap amount child))",
        "selected-nested-struct-array",
    );
}

#[test]
fn mutable_selected_array_view_survives_pending() {
    run(
        "(#let-mut owner (#array #u64 2) (#array-of (#array #u64 2) 0u64 seed))
          (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#index owner 1usize)))
          (#let child #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)))
          (#let answer #u64 (#deref view)) (#drop view) (#forget owner)
          (#return (#u64::add-wrap answer child))",
        "selected-mutable-array-view",
    );
}

#[test]
fn movable_static_array_store_preserves_aliased_wide_layout_across_pending() {
    run_storage(
        "(#let-mut values WideRow (#array-of WideRow 0u128 3u128))
          (#set-index values 1usize
            (#as (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)) #u128))
          (#return (#as (#index values 1usize) #u64))",
        "movable-static-wide-array-store",
        false,
    );
}

#[test]
fn movable_static_struct_array_read_uses_the_resumed_frame() {
    run_storage(
        "(#let owner Owner (#struct-literal Owner ((values (#array-of (#array #u64 2) 0u64 seed)))))
          (#let child #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)))
          (#let answer #u64 (#index (#get owner values) 1usize))
          (#forget owner) (#return (#u64::add-wrap answer child))",
        "movable-static-struct-array-read", false,
    );
}

#[test]
fn movable_static_tuple_array_read_uses_the_resumed_frame() {
    run_storage(
        "(#let values (#tuple (#array #u64 2))
            (#tuple (#tuple (#array #u64 2)) (#array-of (#array #u64 2) 0u64 seed)))
          (#let child #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)))
          (#let answer #u64 (#index (#get values 0) 1usize))
          (#forget values) (#return (#u64::add-wrap answer child))",
        "movable-static-tuple-array-read",
        false,
    );
}

#[test]
fn movable_dynamic_array_store_freezes_index_before_rhs_mutation_and_pending() {
    run_storage(
        "(#let-mut index #usize 1usize)
          (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 0u64 3u64))
          (#set-index values index (#block (#set index 0usize)
            (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed))))
          (#assert (#u64::eq (#index values 0usize) 0u64))
          (#return (#index values 1usize))",
        "movable-dynamic-array-store",
        false,
    );
}

#[test]
fn movable_nested_selection_keeps_parent_index_while_child_index_suspends() {
    run_storage(
        "(#let-mut row #usize 1usize)
          (#let values (#array (#array #u64 2) 2)
            (#array-of (#array (#array #u64 2) 2)
              (#array-of (#array #u64 2) 0u64 0u64)
              (#array-of (#array #u64 2) 0u64 seed)))
          (#return (#index (#index values row)
            (#block (#set row 0usize)
              (#as (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 1u64)) #usize))))",
        "movable-nested-dynamic-selection",
        false,
    );
}
