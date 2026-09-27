mod support;

use std::{fs, process::Command, time::Duration};

fn example_source() -> String {
    include_str!("../examples/async_fn.lim")
        .replace(
            "../library/tasks.lim",
            &format!("{}/library/tasks.lim", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "../library/local_waker.lim",
            &format!("{}/library/local_waker.lim", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "../library/cell.lim",
            &format!("{}/library/cell.lim", env!("CARGO_MANIFEST_DIR")),
        )
}

fn example_without_cancel_work() -> String {
    let original = example_source();
    let (prefix, rest) = original.split_once("(#fn cancel-work").unwrap();
    let (_, main) = rest.split_once("(#fn main () u64").unwrap();
    let main = format!("(#fn main () u64{main}").replace(
        "  (#call cancel-work (: task (#call work (: offset 99u64))))\n",
        "",
    );
    format!("{prefix}{main}")
}

fn build_and_run(source: &str, expected: i32) -> String {
    let scratch = support::Scratch::new("async-fn");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let generated = fs::read_dir(scratch.path().join(".lim/cache"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "lim")
        })
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(
        status.code(),
        Some(expected),
        "{status:?}: {}",
        String::from_utf8_lossy(&stderr)
    );
    generated
}

#[test]
fn async_function_suspends_resumes_and_is_inspectable() {
    let generated = build_and_run(&example_source(), 42);
    assert!(generated.contains("(#enum Work ((Work-start u64) (Work-await-0 u64 Step)))"));
    assert!(generated.contains("(#fn work-poll-resume-0"));
    assert!(generated.contains("(#fn work-poll"));
    assert!(!generated.contains("#await"));
}

#[test]
fn async_function_can_complete_without_suspension() {
    let original = example_source();
    let (prefix, _) = original.split_once("(#fn main () u64").unwrap();
    let source = format!(
        "{} (#fn main () u64
           (#let executor Executor
             (#struct-literal Executor ((notifications
               (#call CellU64-create (: value 0u64))))))
           (#let waker LocalWaker
             (#call local-waker-create (: executor (#borrow executor) : metadata (#struct-literal WakeMetadata ((amount 1u64))))))
           (#let result WorkPoll
             (#call work-poll (: task (#call work (: offset 1u64)) : waker (#borrow waker))))
           (#let value u64
             (#match result
               (#case (WorkReady value) value)
               (#case (WorkPending task)
                 (#block (#forget task) (#unreachable)))))
           (#call local-waker-destroy (: waker waker))
           (#forget executor)
           (#return value))",
        prefix.replace(
            "(#let step Step (Waiting 1u64))",
            "(#let step Step (Waiting 0u64))"
        )
    );
    build_and_run(&source, 41);
}

#[test]
fn async_function_requires_explicit_capture() {
    let source = example_source().replace("(#await (offset)", "(#await ()");
    let error = lim::parse_program(&source).unwrap_err();
    assert!(error.contains("absent from its capture list"), "{error}");
    let scratch = support::Scratch::new("async-fn-diagnostic");
    let diagnostic = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    let span = diagnostic.span.expect("#await has a source span");
    assert_eq!(&source[span.start..span.end], "#await");
}

#[test]
fn async_function_rejects_reference_to_pre_suspension_local() {
    let source = "(#struct Waker ((count u64)))
        (#enum Child ((Waiting u64)))
        (#linear Child)
        (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
        (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
          (#return (ChildPending task)))
        (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function (#fn make () u64
            (#let owner u64 1u64)
            (#let view (#ref u64) (#borrow owner))
            (#let child Child (Waiting 1u64))
            (#let value u64
              (#await (view) Child ChildPending ChildReady child-poll child))
            (#return (#deref view)))))
        (#fn main () u64 (#return 0u64))";
    let program = lim::parse_program(source).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("local") || error.contains("outlive") || error.contains("borrow"),
        "{error}"
    );
}

#[test]
fn async_function_accepts_no_arguments_or_captures() {
    let source = "(#struct Waker ((count u64)))
      (#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#forget task)
        (#return (ChildReady 7u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function (#fn work () u64
          (#let value u64
            (#await () Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#return value))))
      (#fn main () u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let outcome Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result u64
          (#match outcome
            (#case (Ready value) value)
            (#case (Pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 7);
}

#[test]
fn async_function_supports_multiple_awaits() {
    let source = example_without_cancel_work()
        .replace(
            "(#return (#u64.+.wrap value offset))",
            "(#if (#u64.== offset 1u64)
           (#block (#set offset (#u64.+.wrap offset 5u64)) ())
           (#block (#set offset (#u64.+.wrap offset 10u64)) ()))
         (#let second u64
           (#await (offset value) Step StepPending StepReady step-poll (Waiting 0u64)))
         (#return (#u64.+.wrap value offset))",
        )
        .replace("((offset u64)) u64", "((#mut offset u64)) u64");
    let generated = build_and_run(&source, 47);
    assert!(generated.contains("Work-await-1"));
    assert!(generated.contains("work-poll-resume-1"));
}

#[test]
fn async_function_awaits_directly_in_explicit_return() {
    let source = "(#struct Waker ((count u64)))
      (#enum Step ((Waiting u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (StepPending (Waiting 1u64))
              (StepReady count))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function
        (#fn work ((initial u64)) u64
          (#return (#await (initial) Step StepPending StepReady step-poll (Waiting initial))))))
      (#fn main () u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Poll
          (#call poll (: task (#call work (: initial 0u64)) : waker (#borrow waker))))
        (#let-else (Pending first-task) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task first-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 1);
    assert!(generated.contains("(#fn poll-resume-0"), "{generated}");
    assert!(
        generated.contains("(#return (Ready lim.async.return-value))"),
        "{generated}"
    );
}

#[test]
fn async_function_carries_mutable_locals_across_pending_resume() {
    let source = "(#struct Waker ((count u64)))
      (#enum Step ((Waiting u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (StepPending (Waiting 1u64))
              (StepReady count))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function
        (#fn work ((#mut initial u64)) u64
          (#let-mut total u64 initial)
          (#let-mut result u64
            (#await (total) Step StepPending StepReady step-poll (Waiting 0u64)))
          (#set result (#u64.+.wrap result 0u64))
          (#set total (#u64.+.wrap total result))
          (#return total))))
      (#fn main () u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Poll
          (#call poll (: task (#call work (: initial 2u64)) : waker (#borrow waker))))
        (#let-else (Pending first-task) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task first-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 3);
    assert!(generated.contains("(#mut initial u64)"), "{generated}");
    assert!(generated.contains("(#mut total u64)"), "{generated}");
    assert!(generated.contains("(#mut result u64)"), "{generated}");
}

#[test]
fn async_function_rejects_assignment_to_immutable_capture() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll (#return (ChildReady 1u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let total u64 2u64)
          (#let result u64
            (#await (total) Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#set total result)
          (#return result))))";
    let error = lim::parse_program(source).unwrap_err();
    assert!(
        error.contains("assignment to 'total' requires a mutable"),
        "{error}"
    );
}

#[test]
fn async_function_can_suspend_at_each_await() {
    let original = example_without_cancel_work();
    let (prefix, _) = original.split_once("(#fn main () u64").unwrap();
    let prefix = prefix.replace(
        "(#return (#u64.+.wrap value offset))",
        "(#let second u64
           (#await (offset value) Step StepPending StepReady step-poll (Waiting 1u64)))
         (#return (#u64.+.wrap value offset))",
    );
    let source = format!(
        "{prefix} (#fn main () u64
           (#let executor Executor
             (#struct-literal Executor ((notifications
               (#call CellU64-create (: value 0u64))))))
           (#let waker LocalWaker
             (#call local-waker-create (: executor (#borrow executor) : metadata (#struct-literal WakeMetadata ((amount 1u64))))))
           (#let first WorkPoll
             (#call work-poll (: task (#call work (: offset 1u64)) : waker (#borrow waker))))
           (#let-else (WorkPending first-task) WorkPoll first (#unreachable))
           (#let second WorkPoll
             (#call work-poll (: task first-task : waker (#borrow waker))))
           (#let-else (WorkPending second-task) WorkPoll second (#unreachable))
           (#let third WorkPoll
             (#call work-poll (: task second-task : waker (#borrow waker))))
           (#let value u64
             (#match third
               (#case (WorkReady result) result)
               (#case (WorkPending task)
                 (#block (#forget task) (#unreachable)))))
           (#call local-waker-destroy (: waker waker))
           (#let executor-ref (#ref Executor) (#borrow executor))
           (#let notifications u64 (#call CellU64-get (: cell (#borrow (#get executor-ref notifications)))))
           (#drop executor-ref)
           (#forget executor)
           (#return (#u64.+.wrap value notifications)))"
    );
    build_and_run(&source, 43);
}

#[test]
fn async_function_pending_state_can_be_cancelled_explicitly() {
    let original = example_source();
    let (prefix, _) = original.split_once("(#fn main () u64").unwrap();
    let source = format!(
        "{prefix} (#fn main () u64
           (#let executor Executor
             (#struct-literal Executor ((notifications
               (#call CellU64-create (: value 0u64))))))
           (#let waker LocalWaker
             (#call local-waker-create (: executor (#borrow executor) : metadata (#struct-literal WakeMetadata ((amount 1u64))))))
           (#let first WorkPoll
             (#call work-poll (: task (#call work (: offset 1u64)) : waker (#borrow waker))))
           (#let-else (WorkPending pending) WorkPoll first (#unreachable))
           (#call cancel-work (: task pending))
           (#call local-waker-destroy (: waker waker))
           (#let executor-ref (#ref Executor) (#borrow executor))
           (#let notifications u64 (#call CellU64-get (: cell (#borrow (#get executor-ref notifications)))))
           (#drop executor-ref)
           (#forget executor)
           (#return notifications))"
    );
    build_and_run(&source, 1);
}
