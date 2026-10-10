use std::{process::Command, time::Duration};

mod support;

const PREFIX: &str = r#"
  (#struct Holder (: link (#ref #u64)))
  (#fn make (: pointer (#ptr-mut Holder) : source (#ref #u64)) (#pin-own Holder)
    (#return (#unsafe (#pin-own-of pointer (#struct-literal Holder (: link source))))))
  (#fn get (: owner (#ref (#pin-own Holder))) (#ref #u64)
    (#let view (#pin-ref Holder) (#pin-own-borrow owner))
    (#return (#get view link)))
  (#fn destroy (: owner (#pin-own Holder)) ()
    (#let pointer (#ptr-mut Holder) (#unsafe (#pin-release owner)))
    (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))
    (#return ()))
  (#enum Step (: Waiting #u64)) (#linear Step)
  (#enum StepPoll (: StepPending Step : StepReady #u64)) (#linear StepPoll)
  (#fn step-poll (: task Step : waker (#ref #u64)) StepPoll
    (#return (#match task
      (#case (Waiting count)
        (#if (#u64.== count 0u64) (StepReady 0u64)
          (StepPending (Waiting (#u64.-.wrap count 1u64))))))))
  (@#async-fn (: protocol work-await : waker #u64 : function
    (#fn work (: pointer (#ptr-mut Holder) : source (#ref #u64)) #u64
      (#let ignored #u64 (#await Step StepPending StepReady step-poll (Waiting 1u64)))
      (#let owner (#pin-own Holder) (#call make (: pointer pointer : source source)))
      (#let completed #u64 (#await Step StepPending StepReady step-poll (Waiting 1u64)))
      (#let stored (#ref #u64) (#call get (: owner (#borrow owner))))
      (#let answer #u64 (#deref stored))
      (#call destroy (: owner owner))
      (#return answer))))
"#;

fn compile(source: &str, scratch: &support::Scratch) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn heap_reference_owner_created_after_await_survives_next_await() {
    let source = format!(
        r#"{PREFIX}
      (#fn main () #u64
        (#let-mut source #u64 42u64)
        (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let waker #u64 0u64)
        (#let first work-poll-result (#call work-poll (: task (#call work (: pointer pointer : source (#borrow source))) : waker (#borrow waker))))
        (#let-else (work-pending waiting1) work-poll-result first (#unreachable))
        (#let second work-poll-result (#call work-poll (: task waiting1 : waker (#borrow waker))))
        (#let-else (work-pending waiting2) work-poll-result second (#unreachable))
        (#let third work-poll-result (#call work-poll (: task waiting2 : waker (#borrow waker))))
        (#let answer #u64 (#match third
          (#case (work-ready answer) answer)
          (#case (work-pending unfinished) (#block (#forget unfinished) (#unreachable)))))
        (#set source 99u64)
        (#return answer))"#
    );
    let scratch = support::Scratch::new("async-heap-contents");
    let assembly = compile(&source, &scratch).unwrap_or_else(|e| panic!("{}", e.message));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
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
fn async_heap_reference_prevents_source_mutation_across_pending() {
    let source = format!(
        r#"{PREFIX}
      (#fn main () #u64
        (#let-mut source #u64 42u64)
        (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let waker #u64 0u64)
        (#let first work-poll-result (#call work-poll (: task (#call work (: pointer pointer : source (#borrow source))) : waker (#borrow waker))))
        (#let-else (work-pending waiting1) work-poll-result first (#unreachable))
        (#let second work-poll-result (#call work-poll (: task waiting1 : waker (#borrow waker))))
        (#let-else (work-pending waiting2) work-poll-result second (#unreachable))
        (#set source 99u64)
        (#let third work-poll-result (#call work-poll (: task waiting2 : waker (#borrow waker))))
        (#return (#match third (#case (work-ready answer) answer)
          (#case (work-pending unfinished) (#block (#forget unfinished) (#unreachable))))))"#
    );
    let scratch = support::Scratch::new("async-heap-contents-mutation");
    let error = compile(&source, &scratch).expect_err("stored reference must keep source borrowed");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    let span = error
        .span
        .expect("borrow diagnostic should identify its source span");
    assert!(&source[span.start..span.end] == "#set", "{error:?}");
}

#[test]
fn async_heap_owner_is_transferred_to_explicit_cancellation_cleanup() {
    let prefix = PREFIX
        .replace(
            "(#fn make (: pointer (#ptr-mut Holder) : source (#ref #u64)) (#pin-own Holder)\n    (#return",
            "(#fn make (: pointer (#ptr-mut Holder) : source (#ref #u64) : counts (#ptr-mut #u64)) (#pin-own Holder)\n    (#unsafe (#ptr-write counts (#u64.+.wrap (#ptr-read counts) 1u64)))\n    (#return",
        )
        .replace(
            "(#fn destroy (: owner (#pin-own Holder)) ()",
            "(#fn destroy (: owner (#pin-own Holder) : counts (#ptr-mut #u64)) ()",
        )
        .replace(
            "(#fn work (: pointer (#ptr-mut Holder) : source (#ref #u64)) #u64",
            "(#fn work (: pointer (#ptr-mut Holder) : source (#ref #u64) : counts (#ptr-mut #u64)) #u64",
        )
        .replace(
            "(#let owner (#pin-own Holder) (#call make (: pointer pointer : source source)))",
            "(#let owner (#pin-own Holder) (#call make (: pointer pointer : source source : counts counts)))",
        )
        .replace(
            "(#call destroy (: owner owner))",
            "(#call destroy (: owner owner : counts counts))",
        )
        .replace(
            "(#let completed #u64 (#await Step StepPending StepReady step-poll (Waiting 1u64)))",
            "(#let completed #u64 (#await Step StepPending StepReady step-poll (Waiting 2u64)))",
        )
        .replace(
            "(#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))\n    (#return",
            "(#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))\n    (#unsafe (#ptr-write (#ptr-offset counts 1usize) (#u64.+.wrap (#ptr-read (#ptr-offset counts 1usize)) 1u64)))\n    (#return",
        )
        .replace(
            ": waker #u64 : function",
            ": waker #u64 : cancel (work-cancel\n      ((work-task-start cancel-start)\n       (work-task-await-0 cancel-await-before-owner)\n       (work-task-await-1 cancel-await-after-owner)))\n    : function",
        );
    let source = format!(
        r#"{prefix}
      (#fn cancel-start
        ((task (#tuple (#ptr-mut Holder) (#ref #u64) (#ptr-mut #u64)))) ()
        (#let (#tuple pointer source counts)
          (#tuple (#ptr-mut Holder) (#ref #u64) (#ptr-mut #u64)) task)
        (#forget pointer) (#forget source) (#forget counts) (#return ()))
      (#fn cancel-await-before-owner
        ((task (#tuple (#ptr-mut Holder) (#ref #u64) (#ptr-mut #u64) Step))) ()
        (#let (#tuple pointer source counts child)
          (#tuple (#ptr-mut Holder) (#ref #u64) (#ptr-mut #u64) Step) task)
        (#forget pointer) (#forget source) (#forget counts) (#forget child) (#return ()))
      (#fn cancel-await-after-owner
        ((task (#tuple (#ptr-mut #u64) (#pin-own Holder) Step))) ()
        (#let (#tuple counts owner child)
          (#tuple (#ptr-mut #u64) (#pin-own Holder) Step) task)
        (#call destroy (: owner owner : counts counts))
        (#forget child) (#return ()))
      (#fn main () #u64
        (#let-mut source #u64 42u64)
        (#let counts (#ptr-mut #u64) (#unsafe (#linux-syscall (#ptr-mut #u64) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let frame work-task (#call work (: pointer pointer : source (#borrow source) : counts counts)))
        (#let waker #u64 0u64)
        (#let first work-poll-result (#call work-poll (: task frame : waker (#borrow waker))))
        (#let-else (work-pending pending-before-owner) work-poll-result first (#unreachable))
        (#assert (#u64.== (#unsafe (#ptr-read counts)) 0u64))
        (#assert (#u64.== (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
        (#call work-cancel (: task pending-before-owner))

        (#let frame-after-owner work-task
          (#call work (: pointer pointer : source (#borrow source) : counts counts)))
        (#let first-after-owner work-poll-result
          (#call work-poll (: task frame-after-owner : waker (#borrow waker))))
        (#let-else (work-pending pending-step) work-poll-result first-after-owner (#unreachable))
        (#assert (#u64.== (#unsafe (#ptr-read counts)) 0u64))
        (#assert (#u64.== (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
        (#let second-after-owner work-poll-result
          (#call work-poll (: task pending-step : waker (#borrow waker))))
        (#let-else (work-pending pending-owner) work-poll-result second-after-owner (#unreachable))
        (#assert (#u64.== (#unsafe (#ptr-read counts)) 1u64))
        (#assert (#u64.== (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
        (#let repeated work-poll-result
          (#call work-poll (: task pending-owner : waker (#borrow waker))))
        (#let-else (work-pending pending-owner-again) work-poll-result repeated (#unreachable))
        (#assert (#u64.== (#unsafe (#ptr-read counts)) 1u64))
        (#assert (#u64.== (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
        (#call work-cancel (: task pending-owner-again))
        (#assert (#u64.== (#unsafe (#ptr-read counts)) 1u64))
        (#assert (#u64.== (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 1u64))
        (#set source 99u64)
        (#set source 42u64)
        (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (counts 4096usize))) 0i64))
        (#forget waker)
        (#return source))"#
    );
    let scratch = support::Scratch::new("async-heap-owner-cancel");
    let assembly = compile(&source, &scratch).unwrap_or_else(|error| panic!("{}", error.message));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
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

    let pending_mutation = source.replace(
        "        (#call work-cancel (: task pending-owner-again))",
        "        (#set source 99u64)\n        (#call work-cancel (: task pending-owner-again))",
    );
    assert_ne!(
        pending_mutation, source,
        "pending mutation insertion must match"
    );
    let error = compile(&pending_mutation, &scratch)
        .expect_err("the owner must retain the source borrow while pending");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}
