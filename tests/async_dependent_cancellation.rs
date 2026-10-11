mod support;

use std::{process::Command, time::Duration};

fn source() -> &'static str {
    "(#struct Owner (: amount #u64)) (#linear Owner)
      (#enum Child ((Holding (#ref Owner) #u64))) (#linear Child)
      (#enum ChildPoll ((Pending Child) (Ready #u64)))
      (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
        (#return (#match task (#case (Holding view count)
          (#if (#u64.== count 0u64) (Pending (Holding view 1u64))
            (Ready (#u64.+.wrap (#get view amount) 2u64)))))))
      (#fn cancel-child (: value Child) ()
        (#match value (#case (Holding view count)
          (#block (#assert (#u64.== (#get view amount) 40u64))
            (#drop view) (#forget count) ())))
        (#return ()))
      (#fn destroy-owner (: value Owner) ()
        (#assert (#u64.== (#get value amount) 40u64))
        (#forget value) (#return ()))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child)))
        : function (#fn work () #u64
          (#let owner Owner (#struct-literal Owner (: amount 40u64)))
          (#let answer #u64 (#await Child Pending Ready child-poll
            (Holding (#borrow owner) 0u64)))
          (#forget owner) (#return answer))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work-frame (#call work ()))
        (#let first Work-poll-result (#call work-poll
          (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task pending)))
        (#assert (#variant-is (#borrow (#get cleanup await-0)) Work-frame-cleanup-await-0-empty))
        (#call work-cancel (: task cleanup))
        (#call work-poll-destroy (: task (#pin-borrow-mut task)))
        (#forget task) (#return 42u64))"
}

#[test]
fn dependent_child_is_destroyed_before_exporting_its_owner() {
    run(source(), "async-dependent-cancellation");
}

#[test]
fn runtime_array_child_is_cancelled_before_destroying_its_selected_owner() {
    let program = source()
        .replace("(#fn destroy-owner (: value Owner) ()\n        (#assert (#u64.== (#get value amount) 40u64))",
            "(#fn destroy-owner (: value (#array Owner 2)) ()\n        (#assert (#u64.== (#get (#index value 0usize) amount) 10u64))\n        (#assert (#u64.== (#get (#index value 1usize) amount) 40u64))")
        .replace("(#let owner Owner (#struct-literal Owner (: amount 40u64)))",
            "(#let owner (#array Owner 2) (#array-of (#array Owner 2)\n            (#struct-literal Owner (: amount 10u64)) (#struct-literal Owner (: amount 40u64))))\n          (#let-mut index #usize 1usize)")
        .replace("(Holding (#borrow owner) 0u64)",
            "(#block (#let selected (#ref Owner) (#borrow (#index owner index)))\n              (#set index 0usize) (Holding selected 0u64))");
    assert!(program.contains("(#index owner index)"));
    run(&program, "async-runtime-array-dependent-cancellation");
}

#[test]
fn suspended_for_step_cancels_child_before_its_body_owner() {
    let original = "(#let owner Owner (#struct-literal Owner (: amount 40u64)))
          (#let answer #u64 (#await Child Pending Ready child-poll
            (Holding (#borrow owner) 0u64)))
          (#forget owner) (#return answer)";
    let program = source().replace(
        original,
        "(#let-mut total #u64 0u64)
          (#for (#let-mut iteration #u64 0u64) (#u64.< iteration 1u64)
            (#block
              (#let answer #u64 (#await Child Pending Ready child-poll
                (Holding (#borrow owner) 0u64)))
              (#set total answer) (#forget owner) (#set iteration 1u64))
            (#let owner Owner (#struct-literal Owner (: amount 40u64))))
          (#return total)",
    );
    assert_ne!(program, source());
    run(&program, "async-for-step-dependent-cancellation");
}

#[test]
fn exclusive_dependent_mutates_owner_before_owner_destruction() {
    let program = source()
        .replace("(#let owner Owner", "(#let-mut owner Owner")
        .replace("(#ref Owner)", "(#ref-mut Owner)")
        .replace("(#borrow owner)", "(#borrow-mut owner)")
        .replace("(#drop view) (#forget count)",
            "(#deref-set (#borrow-mut (#get view amount)) 41u64) (#drop view) (#forget count)")
        .replace("(#fn destroy-owner (: value Owner) ()\n        (#assert (#u64.== (#get value amount) 40u64))",
            "(#fn destroy-owner (: value Owner) ()\n        (#assert (#u64.== (#get value amount) 41u64))");
    run(&program, "async-exclusive-dependent-cancellation");
}

#[test]
fn dependent_child_cancellation_preserves_selected_internal_and_external_owners() {
    for choose in ["true", "false"] {
        let program = source()
            .replace("(#fn work () #u64", "(#fn work (: external (#ref Owner) : choose #bool) #u64")
            .replace("(#let answer #u64 (#await Child Pending Ready child-poll\n            (Holding (#borrow owner) 0u64)))",
                "(#let view (#ref Owner) (#if choose (#borrow owner) external))\n          (#let answer #u64 (#await Child Pending Ready child-poll (Holding view 0u64)))\n          (#drop view)")
            .replace("(#let waker #u64 0u64)", "(#let outside Owner (#struct-literal Owner (: amount 40u64)))\n        (#let waker #u64 0u64)")
            .replace("(#call work ())", &format!("(#call work (: external (#borrow outside) : choose {choose}))"))
            .replace("(#forget task) (#return 42u64)", "(#forget task) (#forget outside) (#return 42u64)");
        assert!(program.contains("(#let view (#ref Owner)"));
        run(&program, "async-mixed-dependent-cancellation");
    }
}

#[test]
fn pinned_child_cancellation_preserves_selected_internal_and_external_owners() {
    for choose in ["true", "false"] {
        let program = pinned_source()
            .replace("(#fn parent () #u64", "(#fn parent (: external (#ref Owner) : choose #bool) #u64")
            .replace("(#let-mut nested Child-frame (#call child (: view (#borrow owner))))",
                "(#let view (#ref Owner) (#if choose (#borrow owner) external))\n          (#let-mut nested Child-frame (#call child (: view view)))\n          (#drop view)")
            .replace("(#let waker #u64 0u64)", "(#let outside Owner (#struct-literal Owner (: amount 40u64)))\n        (#let waker #u64 0u64)")
            .replace("(#call parent ())", &format!("(#call parent (: external (#borrow outside) : choose {choose}))"))
            .replace("(#forget task) (#return 42u64)", "(#forget task) (#forget outside) (#return 42u64)");
        assert!(program.contains("(#let view (#ref Owner)"));
        run(&program, "async-mixed-pinned-dependent-cancellation");
    }
}

#[test]
fn cancellation_before_first_poll_and_after_ready_is_idempotent() {
    let prefix = source().split("(#fn main").next().unwrap();
    let program = format!(
        "{prefix}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut unstarted Work-frame (#call work ()))
        (#call work-poll-destroy (: task (#pin-borrow-mut unstarted)))
        (#call work-poll-destroy (: task (#pin-borrow-mut unstarted)))
        (#forget unstarted)
        (#let-mut task Work-frame (#call work ()))
        (#let first Work-poll-result (#call work-poll
          (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let-else (work-ready answer) Work-poll-result second (#unreachable))
        (#call work-poll-destroy (: task (#pin-borrow-mut task)))
        (#call work-poll-destroy (: task (#pin-borrow-mut task)))
        (#forget task) (#return answer))"
    );
    run(&program, "async-dependent-terminal-cancellation");
}

fn pinned_source() -> &'static str {
    "(#struct Owner (: amount #u64)) (#linear Owner)
      (#enum Step ((Start #u64))) (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll (: task Step : waker (#ref #u64)) StepPoll
        (#return (#match task (#case (Start count)
          (#if (#u64.== count 0u64) (StepPending (Start 1u64)) (StepReady count))))))
      (#fn cancel-step (: value Step) () (#forget value) (#return ()))
      (#fn destroy-owner (: value Owner) ()
        (#assert (#u64.== (#get value amount) 40u64)) (#forget value) (#return ()))
      (@#async-fn-pinned (: protocol ChildAwait : waker #u64
        : cancel (child-cancel ((await-0 cancel-step)))
        : function (#fn child (: view (#ref Owner)) #u64
          (#let result #u64 (#await Step StepPending StepReady step-poll (Start 0u64)))
          (#return (#u64.+.wrap (#get view amount) result)))))
      (@#async-fn-pinned (: protocol ParentAwait : waker #u64
        : cancel (parent-cancel ((owner destroy-owner) (nested child-poll-destroy)))
        : function (#fn parent () #u64
          (#let owner Owner (#struct-literal Owner (: amount 40u64)))
          (#let-mut nested Child-frame (#call child (: view (#borrow owner))))
          (#let answer #u64 (#await ChildAwait (#pin-borrow-mut nested)))
          (#forget nested) (#forget owner) (#return answer))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Parent-frame (#call parent ()))
        (#let first Parent-poll-result (#call parent-poll
          (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (parent-pending pending) Parent-poll-result first (#unreachable))
        (#call parent-poll-destroy (: task pending))
        (#call parent-poll-destroy (: task (#pin-borrow-mut task)))
        (#forget task) (#return 42u64))"
}

#[test]
fn pinned_generated_child_is_cancelled_without_moving_its_frame() {
    run(pinned_source(), "async-dependent-pinned-child");
}

#[test]
fn pinned_child_rejects_a_by_value_cancellation_handler() {
    let program = pinned_source().replace("(nested child-poll-destroy)", "(nested forget-child)")
        + "\n(#fn forget-child (: value Child-frame) () (#forget value) (#return ()))";
    let scratch = support::Scratch::new("async-dependent-pinned-handler-error");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let error = lim::compile_source_to_assembly(
        &program,
        &scratch.path().join("main.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("pinned mutable reference"),
        "{}",
        error.message
    );
    assert!(error.span.is_some());
    assert!(!scratch.path().join("generated").exists());
}

#[test]
fn private_cancellation_cannot_export_a_live_dependent() {
    let program = source().replace(
        "(#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task pending)))\n        (#assert (#variant-is (#borrow (#get cleanup await-0)) Work-frame-cleanup-await-0-empty))\n        (#call work-cancel (: task cleanup))",
        "(#let cleanup Work-frame-state (#call work-poll-cancel (: task pending)))\n        (#forget cleanup)",
    );
    assert_ne!(program, source());
    run(&program, "async-dependent-private-cancellation");
}

fn run(source: &str, label: &str) {
    let scratch = support::Scratch::new(label);
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("input.lim"),
            &config,
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{}", lim::render_diagnostic(&error, source, "input.lim")))
    };
    let cold = compile();
    let warm = compile();
    assert_eq!(cold, warm);
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
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}
