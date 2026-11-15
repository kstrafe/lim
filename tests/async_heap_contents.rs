use std::{process::Command, time::Duration};

mod support;

const PREFIX: &str = r#"
#struct Holder () ((link (#ref #u64)))
#fn make ((pointer (#ptr-mut Holder)) (source (#ref #u64))) (#pin-own Holder)
      (#return (#unsafe (#pin-own-of pointer (#struct-literal Holder ((link source))))))
#fn get ((owner (#ref (#pin-own Holder)))) (#ref #u64)
      (#let view (#pin-ref Holder) (#pin-own-borrow owner))
      (#return (#get view link))
#fn destroy ((owner (#pin-own Holder))) ()
      (#let pointer (#ptr-mut Holder) (#unsafe (#pin-release owner)))
      (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))
      (#return ())
#enum Step (#linear) ((Step.Waiting #u64))
#enum StepPoll (#linear) ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
      (#return (#match task
        (#case (Step.Waiting count)
          (#if (#u64::eq count 0u64) (StepPoll.StepReady 0u64)
            (StepPoll.StepPending (Step.Waiting (#u64::sub-wrap count 1u64)))))))
#generate #async-fn ((protocol work-await) (waker #u64) (function
      (#fn work ((pointer (#ptr-mut Holder)) (source (#ref #u64))) #u64
        (#let ignored #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 1u64)))
        (#let owner (#pin-own Holder) (#call make ((pointer pointer) (source source))))
        (#let completed #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 1u64)))
        (#let stored (#ref #u64) (#call get ((owner (#borrow owner)))))
        (#let answer #u64 (#deref stored))
        (#call destroy ((owner owner)))
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
#fn main () #u64
          (#let-mut source #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((pointer pointer) (source (#borrow source))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending waiting1) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task waiting1) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending waiting2) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task waiting2) (waker (#borrow waker)))))
          (#let answer #u64 (#match third
            (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending unfinished) (#block (#forget unfinished) (#unreachable)))))
          (#set source 99u64)
          (#return answer)
"#
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
#fn main () #u64
          (#let-mut source #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((pointer pointer) (source (#borrow source))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending waiting1) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task waiting1) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending waiting2) Work::Poll second (#unreachable))
          (#set source 99u64)
          (#let third Work::Poll (#call Work::poll ((task waiting2) (waker (#borrow waker)))))
          (#return (#match third (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending unfinished) (#block (#forget unfinished) (#unreachable)))))
"#
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
            "#fn make ((pointer (#ptr-mut Holder)) (source (#ref #u64))) (#pin-own Holder)\n      (#return",
            "#fn make ((pointer (#ptr-mut Holder)) (source (#ref #u64)) (counts (#ptr-mut #u64))) (#pin-own Holder)\n    (#unsafe (#ptr-write counts (#u64::add-wrap (#ptr-read counts) 1u64)))\n    (#return",
        )
        .replace(
            "#fn destroy ((owner (#pin-own Holder))) ()",
            "#fn destroy ((owner (#pin-own Holder)) (counts (#ptr-mut #u64))) ()",
        )
        .replace(
            "(#fn work ((pointer (#ptr-mut Holder)) (source (#ref #u64))) #u64",
            "(#fn work ((pointer (#ptr-mut Holder)) (source (#ref #u64)) (counts (#ptr-mut #u64))) #u64",
        )
        .replace(
            "(#let owner (#pin-own Holder) (#call make ((pointer pointer) (source source))))",
            "(#let owner (#pin-own Holder) (#call make ((pointer pointer) (source source) (counts counts))))",
        )
        .replace(
            "(#call destroy ((owner owner)))",
            "(#call destroy ((owner owner) (counts counts)))",
        )
        .replace(
            "(#let completed #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 1u64)))",
            "(#let completed #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 2u64)))",
        )
        .replace(
            "(#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))\n      (#return",
            "(#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))\n    (#unsafe (#ptr-write (#ptr-offset counts 1usize) (#u64::add-wrap (#ptr-read (#ptr-offset counts 1usize)) 1u64)))\n    (#return",
        )
        .replace(
            "(waker #u64) (function",
            "(waker #u64) (cancel (work-cancel\n      ((owner destroy-counted)\n       (await-0 cancel-step)\n       (await-1 cancel-step))))\n    (function",
        );
    let prefix = prefix
        .replace("(#let owner (#pin-own Holder) (#call make ((pointer pointer) (source source) (counts counts))))",
            "(#let owner CountedOwner (#call make-counted ((pointer pointer) (source source) (counts counts))))")
        .replace("(#call get ((owner (#borrow owner))))", "(#call get-counted ((owner (#borrow owner))))")
        .replace("(#call destroy ((owner owner) (counts counts)))", "(#call destroy-counted ((counted owner)))");
    let source = format!(
        r#"{prefix}
#struct CountedOwner () ((owner (#pin-own Holder)) (counts (#ptr-mut #u64)))
#fn make-counted ((pointer (#ptr-mut Holder)) (source (#ref #u64)) (counts (#ptr-mut #u64))) CountedOwner
          (#return (#struct-literal CountedOwner
            ((owner (#call make ((pointer pointer) (source source) (counts counts)))) (counts counts))))
#fn get-counted ((owner (#ref CountedOwner))) (#ref #u64)
          (#return (#call get ((owner (#borrow (#get owner owner))))))
#fn destroy-counted ((counted CountedOwner)) ()
          (#let (CountedOwner owner counts) CountedOwner counted)
          (#call destroy ((owner owner) (counts counts))) (#return ())
#fn cancel-step ((child Step)) () (#forget child) (#return ())
#fn main () #u64
          (#let-mut source #u64 42u64)
          (#let counts (#ptr-mut #u64) (#unsafe (#linux-syscall (#ptr-mut #u64) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let frame Work::Task (#call work ((pointer pointer) (source (#borrow source)) (counts counts))))
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-before-owner) Work::Poll first (#unreachable))
          (#assert (#u64::eq (#unsafe (#ptr-read counts)) 0u64))
          (#assert (#u64::eq (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
          (#call work-cancel ((task (#call Work::Poll::cleanup ((task pending-before-owner))))))

          (#let frame-after-owner Work::Task
            (#call work ((pointer pointer) (source (#borrow source)) (counts counts))))
          (#let first-after-owner Work::Poll
            (#call Work::poll ((task frame-after-owner) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-step) Work::Poll first-after-owner (#unreachable))
          (#assert (#u64::eq (#unsafe (#ptr-read counts)) 0u64))
          (#assert (#u64::eq (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
          (#let second-after-owner Work::Poll
            (#call Work::poll ((task pending-step) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-owner) Work::Poll second-after-owner (#unreachable))
          (#assert (#u64::eq (#unsafe (#ptr-read counts)) 1u64))
          (#assert (#u64::eq (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
          (#let repeated Work::Poll
            (#call Work::poll ((task pending-owner) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-owner-again) Work::Poll repeated (#unreachable))
          (#assert (#u64::eq (#unsafe (#ptr-read counts)) 1u64))
          (#assert (#u64::eq (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 0u64))
          (#call work-cancel ((task (#call Work::Poll::cleanup ((task pending-owner-again))))))
          (#assert (#u64::eq (#unsafe (#ptr-read counts)) 1u64))
          (#assert (#u64::eq (#unsafe (#ptr-read (#ptr-offset counts 1usize))) 1u64))
          (#set source 99u64)
          (#set source 42u64)
          (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (counts 4096usize))) 0i64))
          (#forget waker)
          (#return source)
"#
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
        "        (#call work-cancel ((task (#call Work::Poll::cleanup ((task pending-owner-again))))))",
        "        (#set source 99u64)\n        (#call work-cancel ((task (#call Work::Poll::cleanup ((task pending-owner-again))))))",
    );
    assert_ne!(
        pending_mutation, source,
        "pending mutation insertion must match"
    );
    let error = compile(&pending_mutation, &scratch)
        .expect_err("the owner must retain the source borrow while pending");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}
