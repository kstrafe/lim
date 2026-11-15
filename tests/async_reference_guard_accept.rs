mod support;

use std::{process::Command, time::Duration};

const CONTEXT: &str = "
#enum Child (#linear) ((Child.Start #u64) (Child.Resume #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
      (#return (#match task
        (#case (Child.Start value) (ChildPoll.ChildPending (Child.Resume value)))
        (#case (Child.Resume value) (ChildPoll.ChildReady value))))\n  );\n}\n";

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

fn run_guard(guard_accepts: bool) {
    let awaited = if guard_accepts { "0u64" } else { "1u64" };
    let comparison = "(#u64::sub-wrap (#deref view) 42u64)";
    let expected_marker = if guard_accepts { "0u64" } else { "1u64" };
    let completion_polls = if guard_accepts {
        "(#let answer #u64 (#match
            (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))"
    } else {
        "(#let second Work::Poll
          (#call Work::poll ((task next) (waker (#borrow waker)))))
        (#let-else (Work::Poll.Pending last) Work::Poll second (#unreachable))
        (#let answer #u64 (#match
          (#call Work::poll ((task last) (waker (#borrow waker))))
          (#case (Work::Poll.Ready result) result)
          (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))"
    };
    let source = format!(
        "{CONTEXT}
#enum Holder (#linear) ((Holder.Holding (#ref #u64)))
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((source (#ref #u64))) #u64
            (#let-mut marker #u64 0u64)
            (#let holder Holder (Holder.Holding source))
            (#let result #u64 (#match holder
              (#case (Holder.Holding view)
                (#when (#u64::eq
                  (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start {awaited}))
                  {comparison}))
                (#deref view))
              (#case (Holder.Holding view)
                (#block
                  (#set marker 1u64)
                  (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start (#deref view)))))))
            (#assert (#u64::eq marker {expected_marker}))
            (#return result))))
#fn main {{
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of Work::poll)); #body = (
          (#let waker #u64 0u64) (#let owner #u64 42u64)
          (#let-mut frame Work::Frame
            (#call work ((source (#borrow owner)))))
          (#let first Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          {completion_polls}
          (#forget frame) (#return answer)\n  );\n}}\n"
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
