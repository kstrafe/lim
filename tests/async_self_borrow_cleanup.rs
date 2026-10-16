mod support;

use std::{fs, process::Command, time::Duration};

#[test]
fn child_retaining_a_parent_borrow_cannot_be_exported_by_cleanup() {
    let source = "(#enum Child (#linear) ((Holding (#ref #u64) #u64)))
      (#enum ChildPoll () ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
        (#return (#match task (#case (Holding view count)
          (#if (#u64.== count 0u64) (ChildPending (Holding view 1u64))
            (ChildReady (#deref view)))))))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work () #u64
          (#let owner #u64 40u64)
          (#let answer #u64 (#await Child ChildPending ChildReady child-poll (Holding (#borrow owner) 0u64)))
          (#forget owner) (#return answer))))";
    let scratch = support::Scratch::new("async-retained-child-borrow");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("a live dependent child cannot accompany an extracted owner");
    assert!(
        error.message.contains("in-place cancellation"),
        "{}",
        error.message
    );
    let span = error
        .span
        .expect("retained-child diagnostic must locate the source");
    assert!(source[span.start..span.end].contains("Holding"));
    assert!(!scratch.path().join("generated").exists());
}

#[test]
fn cancellation_clears_internal_handles_before_exporting_stationary_owners() {
    let source = "(#struct Owner (#linear) (: amount #u64))
      (#enum Child () ((Start #u64)))
      (#enum ChildPoll () ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
        (#return (#match task (#case (Start count)
          (#if (#u64.== count 0u64) (ChildPending (Start 2u64)) (ChildReady count))))))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work () #u64
          (#let owner Owner (#struct-literal Owner (: amount 40u64)))
          (#let view (#ref Owner) (#borrow owner))
          (#let result #u64 (#await Child ChildPending ChildReady child-poll (Start 0u64)))
          (#let answer #u64 (#u64.+.wrap (#get view amount) result))
          (#drop view) (#forget owner) (#return answer))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work ()))
        (#let first Work::Poll (#call Work::poll
          (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (Work::Pending pending) Work::Poll first (#unreachable))
        (#let cleanup Work::Frame::Cleanup (#call Work::poll::cleanup (: task pending)))
        (#let amount #u64 (#match (#get cleanup owner)
          (#case Work::Frame::Cleanup::owner::Empty (#unreachable))
          (#case (Work::Frame::Cleanup::owner::Full extracted)
            (#block (#let answer #u64 (#get extracted amount)) (#forget extracted) answer))))
        (#forget cleanup)
        (#let again Work::Frame::Cleanup (#call Work::poll::cleanup (: task (#pin-borrow-mut task))))
        (#assert (#variant-is (#borrow (#get again owner)) Work::Frame::Cleanup::owner::Empty))
        (#forget again) (#forget task) (#return (#u64.+.wrap amount 2u64)))";
    let scratch = support::Scratch::new("async-self-borrow-cleanup");
    let cache = scratch.path().join("cache");
    let input = scratch.path().join("input.lim");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &input,
            &config,
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{:?}: {}", error.code, error.message))
    };
    let cold = compile();
    let warm = compile();
    assert_eq!(cold, warm);
    let artifacts = fs::read_dir(scratch.path().join("generated"))
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(artifacts.len(), 1);
    assert!(artifacts[0].contains("(#ptr Owner)"));
    assert!(artifacts[0].contains("#ref-ptr"));
    assert!(artifacts[0].contains("#ptr-borrow"));
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
