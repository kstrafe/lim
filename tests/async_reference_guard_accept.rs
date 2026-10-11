mod support;

use std::{process::Command, time::Duration};

const CONTEXT: &str = "
  (#enum Child ((Start #u64) (Resume #u64))) (#linear Child)
  (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
  (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
    (#return (#match task
      (#case (Start value) (ChildPending (Resume value)))
      (#case (Resume value) (ChildReady value)))))";

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

fn run_guard(guard_accepts: bool) {
    let awaited = if guard_accepts { "0u64" } else { "1u64" };
    let comparison = "(#u64.-.wrap (#deref view) 42u64)";
    let expected_marker = if guard_accepts { "0u64" } else { "1u64" };
    let completion_polls = if guard_accepts {
        "(#let answer #u64 (#match
          (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready result) result)
          (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))"
    } else {
        "(#let second Work-poll-result
          (#call work-poll (: task next : waker (#borrow waker))))
        (#let-else (work-pending last) Work-poll-result second (#unreachable))
        (#let answer #u64 (#match
          (#call work-poll (: task last : waker (#borrow waker)))
          (#case (work-ready result) result)
          (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))"
    };
    let source = format!(
        "{CONTEXT}
      (#enum Holder ((Holding (#ref #u64)))) (#linear Holder)
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work (: source (#ref #u64)) #u64
          (#let-mut marker #u64 0u64)
          (#let holder Holder (Holding source))
          (#let result #u64 (#match holder
            (#case (Holding view)
              (#when (#u64.==
                (#await Child ChildPending ChildReady child-poll (Start {awaited}))
                {comparison}))
              (#deref view))
            (#case (Holding view)
              (#block
                (#set marker 1u64)
                (#await Child ChildPending ChildReady child-poll (Start (#deref view)))))))
          (#assert (#u64.== marker {expected_marker}))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64) (#let owner #u64 42u64)
        (#let-mut frame Work-frame
          (#call work (: source (#borrow owner))))
        (#let first Work-poll-result
          (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        {completion_polls}
        (#forget frame) (#return answer))"
    );
    let scratch = support::Scratch::new(if guard_accepts {
        "async-reference-guard-accepted"
    } else {
        "async-reference-guard-rejected"
    });
    let input = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let mut assemblies = Vec::new();
    for _ in 0..2 {
        assemblies.push(
            lim::compile_source_to_assembly(
                &source,
                &input,
                &config(),
                &cache,
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap_or_else(|error| panic!("{}\n{source}", error.message)),
        );
    }
    assert_eq!(
        assemblies[0], assemblies[1],
        "cold and warm assembly differ"
    );
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assemblies[1],
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

#[test]
fn shared_reference_guard_acceptance_skips_fallback_and_rejection_runs_it() {
    run_guard(true);
    run_guard(false);
}
