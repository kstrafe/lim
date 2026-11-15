mod support;

use std::{fs, process::Command, time::Duration};

#[test]
fn child_retaining_a_parent_borrow_cannot_be_exported_by_cleanup() {
    let source = "#enum Child (#linear) ((Child.Holding (#tuple (#ref #u64) #u64)))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Holding (#tuple view count))
            (#if (#u64::eq count 0u64) (ChildPoll.ChildPending (Child.Holding (#tuple view 1u64)))
              (ChildPoll.ChildReady (#deref view))))))
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (function (#fn work () #u64
            (#let owner #u64 40u64)
            (#let answer #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Holding (#tuple (#borrow owner) 0u64))))
            (#forget owner) (#return answer))))\n";
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
    assert!(source[span.start..span.end].contains("Child.Holding"));
    assert!(!scratch.path().join("generated").exists());
}

#[test]
fn cancellation_clears_internal_handles_before_exporting_stationary_owners() {
    let source = "#struct Owner (#linear) ((amount #u64))
#enum Child () ((Child.Start #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Start count)
            (#if (#u64::eq count 0u64) (ChildPoll.ChildPending (Child.Start 2u64)) (ChildPoll.ChildReady count)))))
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (function (#fn work () #u64
            (#let owner Owner (#struct-literal Owner ((amount 40u64))))
            (#let view (#ref Owner) (#borrow owner))
            (#let result #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)))
            (#let answer #u64 (#u64::add-wrap (#get view amount) result))
            (#drop view) (#forget owner) (#return answer))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut task Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll
            ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task pending))))
          (#let amount #u64 (#match (#get cleanup owner)
            (#case Work::Frame::Cleanup::Owner.Empty (#unreachable))
            (#case (Work::Frame::Cleanup::Owner.Full extracted)
              (#block (#let answer #u64 (#get extracted amount)) (#forget extracted) answer))))
          (#forget cleanup)
          (#let again Work::Frame::Cleanup (#call Work::Poll::cleanup ((task (#pin-borrow-mut task)))))
          (#assert (#variant-is (#borrow (#get again owner)) Work::Frame::Cleanup::Owner.Empty))
          (#forget again) (#forget task) (#return (#u64::add-wrap amount 2u64))\n  );\n}\n";
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
