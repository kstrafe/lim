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
    let generated_sources = fs::read_dir(scratch.path().join(".lim/cache"))
        .into_iter()
        .flatten()
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
    assert!(
        status.success(),
        "{}\ngenerated source:\n{generated_sources}",
        String::from_utf8_lossy(&stderr)
    );
    let generated = generated_sources;
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
fn async_generated_code_does_not_allow_shadowing_in_nested_branches() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (ChildReady 0u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((value u64)) u64
          (#let result u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#if true
            (#block (#let value u64 2u64) ())
            ())
          (#return result))))";
    let scratch = support::Scratch::new("async-shadow");
    let input = scratch.path().join("shadow.lim");
    let diagnostic = lim::compile_source_to_assembly(
        source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        diagnostic
            .message
            .contains("binding 'value' shadows an existing binding"),
        "{diagnostic:?}"
    );
    let span = diagnostic.span.expect("shadowed binding source span");
    assert_eq!(&source[span.start..span.end], "value");
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
fn pinned_async_frames_poll_in_place_and_cancel_explicitly() {
    let source = "(#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (#fn cancel-child ((task Child)) () (#forget task) (#return ()))
      (@async-fn-pinned (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((offset u64)) u64
          (#let value u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64))
          )
          (#return (#u64.+.wrap value offset)))))
      (#fn cancel-frame ((task Frame)) ()
        (#match task
          (#case (Frame-start offset) (#forget offset))
          (#case (Frame-await-0 offset child)
            (#block (#forget offset) (#call cancel-child (: task child))))
          (#case Frame-done ()))
        (#return ()))
      (#fn main () u64
        (#let-mut frame Frame (#call work (: offset 40u64)))
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (Pending pinned-frame) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pinned-frame : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) (#unreachable)))))
        (#forget frame)
        (#let-mut cancelled-frame Frame (#call work (: offset 90u64)))
        (#let first-cancel Poll
          (#call poll (: task (#pin-borrow-mut cancelled-frame) : waker (#borrow waker))))
        (#let-else (Pending cancel-pin) Poll first-cancel (#unreachable))
        (#let state-to-cancel Frame (#call poll-cancel (: task cancel-pin)))
        (#call cancel-frame (: task state-to-cancel))
        (#forget cancelled-frame)
        (#forget waker)
        (#return result))";
    let moved = source.replace(
        "(#let second Poll",
        "(#let moved Frame frame)\n        (#let second Poll",
    );
    let error = lim::check_types(&lim::parse_program(&moved).unwrap()).unwrap_err();
    assert!(
        error.contains("pinned") || error.contains("borrow") || error.contains("consumed"),
        "{error}"
    );

    let escaping = source.replace(
        "(#fn main () u64",
        "(#fn escape-frame () Poll
          (#let-mut frame Frame (#call work (: offset 40u64)))
          (#let waker u64 0u64)
          (#return (#call poll (: task (#pin-borrow-mut frame) : waker (#borrow waker)))))
        (#fn main () u64",
    );
    let error = lim::check_types(&lim::parse_program(&escaping).unwrap()).unwrap_err();
    assert!(
        error.contains("outlive")
            || error.contains("borrow")
            || error.contains("local")
            || error.contains("consumed"),
        "pinned frame handle must not escape its owner: {error}"
    );

    let generated = build_and_run(source, 41);
    assert!(
        generated.contains("(#pin-ref-mut Frame)"),
        "poll must borrow the pinned frame: {generated}"
    );
    assert!(generated.contains("(#pin-read task)"), "{generated}");
    assert!(generated.contains("(#pin-write task"), "{generated}");
    assert!(generated.contains("(#fn poll-cancel"), "{generated}");
}

#[test]
fn pinned_async_frames_reject_stack_pins_captured_across_suspension() {
    let source = "(#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn-pinned (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut value u64 41u64)
          (#let view (#pin-ref u64) (#pin-borrow value))
          (#let result u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#return (#u64.+.wrap (#deref view) result)))))
      (#fn main () u64 (#return 0u64))";
    let program = lim::parse_program(source).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("pinned")
            || error.contains("outlive")
            || error.contains("borrow")
            || error.contains("local"),
        "a stack pin must not be laundered into a pinned async frame: {error}"
    );
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
fn async_function_infers_only_live_across_await_values() {
    let source = "(#struct Box ((value u64)))
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (#block (#forget value) (ChildReady 1u64))))))
      (#fn echo ((value u64)) u64 (#return value))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
      (#fn work ((first u64)) u64
          (#let value u64 5u64)
          (#let box Box (#struct-literal Box ((value 7u64))))
          (#let child Child (Waiting 0u64))
          (#let result u64
            (#await Child ChildPending ChildReady child-poll child))
          (#return (#u64.+.wrap
            (#call echo (: value 8u64))
            (#u64.+.wrap first (#get box value)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let outcome Poll
          (#call poll (: task (#call work (: first 2u64)) : waker (#borrow waker))))
        (#return (#match outcome
          (#case (Ready result) result)
          (#case (Pending task) (#block (#forget task) (#unreachable))))))";
    let generated = build_and_run(source, 17);
    assert!(generated.contains("Frame-await-0"), "{generated}");
    assert!(
        generated.contains("(first u64) (box Box) (result u64)"),
        "captures must preserve declaration order: {generated}"
    );
}

#[test]
fn async_function_requires_unused_linear_values_to_be_consumed_before_await() {
    let source = "(#struct Token ((value u64)))
      (#linear Token)
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (#block (#forget value) (ChildReady 1u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let token Token (#struct-literal Token ((value 1u64))))
          (#let child Child (Waiting 0u64))
          (#let result u64
            (#await Child ChildPending ChildReady child-poll child))
          (#return result))))
      (#fn main () () (#return ()))";
    let program = lim::parse_program(source).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("token") && (error.contains("linear") || error.contains("consum")),
        "{error}"
    );
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
              (#await Child ChildPending ChildReady child-poll child))
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
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
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
         (#match offset
           (#case 6u64 (#block (#set offset (#u64.+.wrap offset 1u64)) ()))
           (#case _ (#block (#set offset 99u64) ())))
         (#let second u64
           (#await Step StepPending StepReady step-poll (Waiting 0u64)))
         (#return (#u64.+.wrap value offset))",
        )
        .replace("((offset u64)) u64", "((#mut offset u64)) u64");
    let generated = build_and_run(&source, 48);
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
          (#return (#await Step StepPending StepReady step-poll (Waiting initial))))))
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
fn async_function_extracts_typed_awaits_from_value_expressions() {
    let source = "(#struct Waker ((count u64)))
      (#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (#fn sum ((a u64) (b u64)) u64 (#return (#u64.+.wrap a b)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function
        (#fn work () u64
          (#let result u64 (#call sum (:
            b (#await u64 Child ChildPending ChildReady child-poll (Waiting 20u64))
            : a (#await u64 Child ChildPending ChildReady child-poll (Waiting 10u64)))))
          (#return result))))
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
    let generated = build_and_run(source, 30);
    assert!(
        generated.contains("lim.async.nested-await-0"),
        "{generated}"
    );
    assert!(
        generated.contains("lim.async.nested-await-1"),
        "{generated}"
    );
}

#[test]
fn async_function_requires_types_for_nested_awaits() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll (#return (ChildReady 1u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#return (#u64.+.wrap
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64))
            1u64)))))";
    let error = lim::parse_program(source).unwrap_err();
    assert!(
        error.contains("nested #await requires an explicit result type"),
        "{error}"
    );
}

#[test]
fn async_function_extracts_awaits_from_keyed_struct_literals() {
    let source = "(#struct Waker ((count u64)))
      (#struct Pair ((left u64) (right u64)))
      (#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function
        (#fn work () Pair
          (#let result Pair (#struct-literal Pair
            ((right (#await u64 Child ChildPending ChildReady child-poll (Waiting 20u64)))
             (left (#await u64 Child ChildPending ChildReady child-poll (Waiting 10u64))))))
          (#return result))))
      (#fn main () u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let outcome Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result u64
          (#match outcome
            (#case (Ready pair)
              (#u64.+.wrap (#get pair left) (#u64.*.wrap 2u64 (#get pair right))))
            (#case (Pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 50);
}

#[test]
fn async_function_awaits_after_conditional_task_selection() {
    let source = "(#struct Waker ((count u64)))
      (#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#enum Choice ((Small) (Large)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (IfFrame IfPoll IfPending IfReady poll-if) : waker Waker : function
        (#fn choose-if ((large bool)) u64
          (#return (#if large
            (#await u64 Child ChildPending ChildReady child-poll (Waiting 20u64))
            (#await u64 Child ChildPending ChildReady child-poll (Waiting 10u64)))))))
      (@async-fn (: names (MatchFrame MatchPoll MatchPending MatchReady poll-match) : waker Waker : function
        (#fn choose-match ((choice Choice)) u64
          (#return (#match choice
            (#case Small (#await u64 Child ChildPending ChildReady child-poll (Waiting 10u64)))
            (#case Large (#await u64 Child ChildPending ChildReady child-poll (Waiting 20u64))))))))
      (#fn main () u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let if-result IfPoll
          (#call poll-if (: task (#call choose-if (: large true)) : waker (#borrow waker))))
        (#let match-result MatchPoll
          (#call poll-match (: task (#call choose-match (: choice Large)) : waker (#borrow waker))))
        (#let total u64
          (#u64.+.wrap
            (#match if-result
              (#case (IfReady value) value)
              (#case (IfPending task) (#block (#forget task) (#unreachable))))
            (#match match-result
              (#case (MatchReady value) value)
              (#case (MatchPending task) (#block (#forget task) (#unreachable))))))
        (#forget waker)
        (#return total))";
    let generated = build_and_run(source, 40);
    assert!(
        generated.contains("lim.async.nested-await-0"),
        "{generated}"
    );
}

#[test]
fn async_conditional_await_joins_with_an_immediate_value() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((choose bool)) u64
          (#let result u64
            (#if choose
              (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
              41u64))
          (#return result))))
      (#enum Choice (Await Immediate))
      (@async-fn (: names (MatchFrame MatchPoll MatchPending MatchReady match-poll) : waker u64 : function
        (#fn work-match ((choice Choice)) u64
          (#let result u64
            (#match choice
              (#case Await
                (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
              (#case Immediate 41u64)))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let awaited Poll
          (#call poll (: task (#call work (: choose true)) : waker (#borrow waker))))
        (#let awaited-value u64
          (#match awaited
            (#case (Ready value) value)
            (#case (Pending awaited-child)
              (#match (#call poll (: task awaited-child : waker (#borrow waker)))
                (#case (Ready awaited-ready) awaited-ready)
                (#case (Pending awaited-again) (#block (#forget awaited-again) (#unreachable)))))))
        (#let immediate Poll
          (#call poll (: task (#call work (: choose false)) : waker (#borrow waker))))
        (#let immediate-value u64
          (#match immediate
            (#case (Ready immediate-ready) immediate-ready)
            (#case (Pending immediate-task) (#block (#forget immediate-task) (#unreachable)))))
        (#let match-awaited MatchPoll
          (#call match-poll (: task (#call work-match (: choice Await)) : waker (#borrow waker))))
        (#let match-awaited-value u64
          (#match match-awaited
            (#case (MatchReady value) value)
            (#case (MatchPending match-child)
              (#match (#call match-poll (: task match-child : waker (#borrow waker)))
                (#case (MatchReady match-ready) match-ready)
                (#case (MatchPending match-again) (#block (#forget match-again) (#unreachable)))))))
        (#let match-immediate MatchPoll
          (#call match-poll (: task (#call work-match (: choice Immediate)) : waker (#borrow waker))))
        (#let match-immediate-value u64
          (#match match-immediate
            (#case (MatchReady match-immediate-ready) match-immediate-ready)
            (#case (MatchPending match-immediate-task)
              (#block (#forget match-immediate-task) (#unreachable)))))
        (#return (#u64.+.wrap
          (#u64.+.wrap awaited-value immediate-value)
          (#u64.+.wrap match-awaited-value match-immediate-value))))";
    let generated = build_and_run(source, 84);
    assert!(generated.contains(".choice-"), "{generated}");
    assert!(generated.contains("-poll-result"), "{generated}");
}

#[test]
fn async_conditional_choice_captures_and_releases_a_borrow_on_cancel() {
    let source = "(#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((choose bool) (view (#ref u64))) u64
          (#let result u64
            (#if choose
              (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
              41u64))
          (#return (#u64.+.wrap result (#deref view))))))
      (#fn main () u64
        (#let-mut owner u64 1u64)
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (: choose true : view (#borrow owner)))
            : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        CHECK_HERE
        (#forget pending)
        (#set owner 42u64)
        (#let immediate Poll
          (#call poll (: task (#call work (: choose false : view (#borrow owner)))
            : waker (#borrow waker))))
        (#let answer u64
          (#match immediate
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return answer))";

    let rejected = source.replace("CHECK_HERE", "(#set owner 40u64)");
    let error = lim::check_types(&lim::parse_program(&rejected).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );

    let accepted = source.replace("CHECK_HERE", "");
    let generated = build_and_run(&accepted, 83);
    assert!(
        generated.contains("(view (#ref u64))"),
        "the frame must retain the live external borrow: {generated}"
    );
}

#[test]
fn async_function_rejects_conditional_awaits_with_different_result_types() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64) (ChildAlternateReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (#fn child-poll-alt ((task Child) (waker (#ref u64))) ChildPoll
        (#return (ChildAlternateReady 2u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#return (#if true
            (#await u64 Child ChildPending ChildReady child-poll (Waiting 1u64))
            (#await u64 Child ChildPending ChildAlternateReady child-poll-alt (Waiting 2u64)))))))";
    let mismatched = source.replace(
        "#await u64 Child ChildPending ChildAlternateReady child-poll-alt",
        "#await u32 Child ChildPending ChildAlternateReady child-poll-alt",
    );
    let error = lim::parse_program(&mismatched).unwrap_err();
    assert!(
        error.contains("conditional #await branches must produce the same result type"),
        "{error}"
    );
}

#[test]
fn async_conditional_awaits_support_distinct_child_poll_protocols() {
    let source = "(#enum LeftChild ((LeftWaiting u64)))
      (#enum LeftPoll ((LeftPending LeftChild) (LeftReady u64)))
      (#fn left-poll ((task LeftChild) (waker (#ref u64))) LeftPoll
        (#return (#match task
          (#case (LeftWaiting value)
            (#if (#u64.== value 0u64)
              (LeftPending (LeftWaiting 1u64))
              (LeftReady value))))))
      (#enum RightChild ((RightWaiting u64)))
      (#enum RightPoll ((RightPending RightChild) (RightReady u64)))
      (#fn right-poll ((task RightChild) (waker (#ref u64))) RightPoll
        (#return (#match task (#case (RightWaiting value) (RightReady (#u64.+.wrap value 1u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((choose-left bool)) u64
          (#return (#if choose-left
            (#await u64 LeftChild LeftPending LeftReady left-poll (LeftWaiting 0u64))
            (#await u64 RightChild RightPending RightReady right-poll (RightWaiting 2u64)))))))
      (#enum Choice (Left Right))
      (@async-fn (: names (MatchFrame MatchPoll MatchPending MatchReady match-poll) : waker u64 : function
        (#fn work-match ((choice Choice)) u64
          (#return (#match choice
            (#case Left
              (#await u64 LeftChild LeftPending LeftReady left-poll (LeftWaiting 0u64)))
            (#case Right
              (#await u64 RightChild RightPending RightReady right-poll (RightWaiting 2u64))))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let left-first Poll
          (#call poll (: task (#call work (: choose-left true)) : waker (#borrow waker))))
        (#let left Poll
          (#match left-first
            (#case (Pending task)
              (#call poll (: task task : waker (#borrow waker))))
            (#case (Ready value) (Ready value))))
        (#let left-value u64
          (#match left
            (#case (Ready value) value)
            (#case (Pending task) (#block (#forget task) (#unreachable)))))
        (#let right Poll
          (#call poll (: task (#call work (: choose-left false)) : waker (#borrow waker))))
        (#let right-value u64
          (#match right
            (#case (Ready value) value)
            (#case (Pending task) (#block (#forget task) (#unreachable)))))
        (#let matched MatchPoll
          (#call match-poll (: task (#call work-match (: choice Right)) : waker (#borrow waker))))
        (#let matched-value u64
          (#match matched
            (#case (MatchReady value) value)
            (#case (MatchPending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return (#u64.+.wrap (#u64.+.wrap left-value right-value) matched-value)))";
    let generated = build_and_run(source, 7);
    assert!(generated.contains("LeftChild"), "{generated}");
    assert!(generated.contains("RightChild"), "{generated}");
    assert!(generated.contains("left-poll"), "{generated}");
    assert!(generated.contains("right-poll"), "{generated}");
}

#[test]
fn async_function_retains_external_borrows_across_pending() {
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
        (#fn read-after-await ((view (#ref u64))) u64
          (#let result u64
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
          (#return (#u64.+.wrap (#deref view) result)))))
      (#fn main () u64
        (#let-mut owner u64 37u64)
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Poll
          (#call poll (: task (#call read-after-await (: view (#borrow owner)))
            : waker (#borrow waker))))
        (#let-else (Pending task) Poll first (#unreachable))
        MUTATE_WHILE_PENDING
        (#let second Poll
          (#call poll (: task task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending extra-task) (#block (#forget extra-task) (#unreachable)))))
        (#set owner 39u64)
        (#forget waker)
        (#return (#u64.+.wrap owner result)))";
    let accepted = source.replace("MUTATE_WHILE_PENDING", "");
    build_and_run(&accepted, 77);

    let rejected = source.replace(
        "MUTATE_WHILE_PENDING",
        "(#set owner (#u64.+.wrap owner 1u64))",
    );
    let error = lim::check_types(&lim::parse_program(&rejected).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("mutate") || error.contains("loan"),
        "{error}"
    );

    let escaping = accepted.replace(
        "(#fn main () u64",
        "(#fn escape () Frame\n          (#let owner u64 3u64)\n          (#return (#call read-after-await (: view (#borrow owner)))))\n      (#fn main () u64",
    );
    let error = lim::check_types(&lim::parse_program(&escaping).unwrap()).unwrap_err();
    assert!(
        error.contains("local") || error.contains("outlive") || error.contains("borrow"),
        "{error}"
    );
}

#[test]
fn async_function_retains_mutable_external_borrows_across_pending() {
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
        (#fn write-after-await ((view (#ref-mut u64))) u64
          (#let result u64
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
          (#deref-set view (#u64.+.wrap (#deref view) result))
          (#return (#deref view)))))
      (#fn main () u64
        (#let-mut owner u64 37u64)
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Poll
          (#call poll (: task (#call write-after-await (: view (#borrow-mut owner)))
            : waker (#borrow waker))))
        (#let-else (Pending task) Poll first (#unreachable))
        READ_WHILE_PENDING
        (#let second Poll
          (#call poll (: task task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending extra-task) (#block (#forget extra-task) (#unreachable)))))
        (#set owner 39u64)
        (#return (#u64.+.wrap result owner)))";
    let accepted = source.replace("READ_WHILE_PENDING", "");
    build_and_run(&accepted, 77);

    let rejected = source.replace("READ_WHILE_PENDING", "(#let snapshot u64 owner)");
    let error = lim::check_types(&lim::parse_program(&rejected).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn cancelling_a_pending_async_frame_releases_its_external_mutable_borrow() {
    let source = "(#struct Waker ((count u64)))
      (#enum Step ((Waiting u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count) (StepPending (Waiting count))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function
        (#fn work ((view (#ref-mut u64))) u64
          (#let result u64
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
          (#return (#deref view)))))
      (#fn main () u64
        (#let-mut owner u64 37u64)
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Poll
          (#call poll (: task (#call work (: view (#borrow-mut owner)))
            : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        WHILE_PENDING
        (#forget pending)
        (#set owner 42u64)
        (#return owner))";
    let accepted = source.replace("WHILE_PENDING", "");
    lim::check_types(&lim::parse_program(&accepted).unwrap()).unwrap();

    let rejected = source.replace("WHILE_PENDING", "(#set owner 40u64)");
    let error = lim::check_types(&lim::parse_program(&rejected).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );

    let shared = source
        .replace("#ref-mut", "#ref")
        .replace("#borrow-mut owner", "#borrow owner");
    let accepted = shared.replace("WHILE_PENDING", "");
    lim::check_types(&lim::parse_program(&accepted).unwrap()).unwrap();
    let rejected = shared.replace("WHILE_PENDING", "(#set owner 40u64)");
    let error = lim::check_types(&lim::parse_program(&rejected).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
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
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
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
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#set total result)
          (#return result))))";
    let error = lim::parse_program(source).unwrap_err();
    assert!(
        error.contains("assignment to 'total' requires a mutable"),
        "{error}"
    );
}

#[test]
fn async_function_lowers_await_in_terminal_binding_block() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#return (#if true
            (#block
              (#let task-input u64 17u64)
              (#let result u64
                (#await Child ChildPending ChildReady child-poll (Waiting task-input)))
              result)
            0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let outcome Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value u64
          (#match outcome
            (#case (Ready ready) ready)
            (#case (Pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run(source, 17);
    assert!(generated.contains(".choice-"), "{generated}");
    let frame_declaration = generated
        .lines()
        .find(|line| line.contains("(#enum Frame "))
        .expect("generated async frame");
    assert!(
        !frame_declaration.contains("task-input"),
        "branch-local setup must not become a suspended-frame capture: {frame_declaration}"
    );
}

#[test]
fn async_function_resumes_a_child_await_inside_a_while_loop() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#while (#u64.< iteration 2u64)
            (#let child-input u64 iteration)
            (#let result u64
              (#await Child ChildPending ChildReady child-poll (Waiting child-input)))
            (#set iteration (#u64.+.wrap iteration 1u64)))
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 2);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_resumes_a_child_await_in_a_while_condition() {
    let source = include_str!("../examples/async_fn_while_condition.lim");
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_returns_linear_state_after_a_loop() {
    let source = "(#struct State ((value u64)))
      (#linear State)
      (#struct Token ((limit u64)))
      (#linear Token)
      (#enum ChildPoll ((ChildPending u64) (ChildReady u64)))
      (#fn child-poll ((task u64) (waker (#ref u64))) ChildPoll
        (#return (#if (#u64.== task 0u64)
          (ChildPending 1u64)
          (ChildReady task))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut state State (#struct-literal State ((value 0u64))))
          (#let token Token (#struct-literal Token ((limit 3u64))))
          (#while (#u64.< (#get state value) (#get token limit))
            (#let result u64
              (#await u64 ChildPending ChildReady child-poll (#get state value)))
            (#let next-value u64 (#u64.+.wrap result 1u64))
            (#forget state)
            (#set state (#struct-literal State
              ((value next-value)))))
          (#return (#block
            (#let value u64 (#get state value))
            (#forget state)
            (#forget token)
            value)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let cancel-frame Frame (#call work (:)))
        (#let cancel-first Poll (#call poll (: task cancel-frame : waker (#borrow waker))))
        (#let-else (Pending cancelled-task) Poll cancel-first (#unreachable))
        (#forget cancelled-task)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 3);
    assert!(generated.contains("-outputs"), "{generated}");
    assert!(
        generated.contains("(state State) (token Token)"),
        "{generated}"
    );
}

#[test]
fn async_function_resumes_child_await_inside_a_for_range_loop() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for-range (iteration u64) 0u64 2u64
            (#let result u64
              (#await Child ChildPending ChildReady child-poll (Waiting iteration))))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_resumes_child_await_inside_for_with_existing_counter() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for (#set iteration 0u64)
                (#u64.< iteration 2u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#let result u64
              (#await Child ChildPending ChildReady child-poll (Waiting iteration))))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_resumes_child_await_inside_for_with_local_initializer() {
    let source = "(#struct Child ((iteration u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-value ((iteration u64)) u64 (#return iteration))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#let value u64 (#get task iteration))
        (#return (#if (#u64.== value 0u64)
          (ChildPending (#struct-literal Child ((iteration 1u64))))
          (ChildReady value))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for (#let-mut iteration u64 0u64)
                (#u64.< iteration 2u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#let result u64
              (#await Child ChildPending ChildReady child-poll
                (#struct-literal Child ((iteration
                  (#call child-value (: iteration iteration))))))))
          (#let iteration u64 42u64)
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_rejects_for_initializer_shadowing() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (ChildReady 1u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 5u64)
          (#for (#let-mut iteration u64 0u64)
                (#u64.< iteration 2u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#let result u64
              (#await Child ChildPending ChildReady child-poll (Waiting iteration))))
          (#return 42u64))))";
    let scratch = support::Scratch::new("async-for-init-binding");
    let input = scratch.path().join("loop.lim");
    let diagnostic = lim::compile_source_to_assembly(
        source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        diagnostic.message.contains("shadowing is not allowed"),
        "{diagnostic:?}"
    );
}

#[test]
fn async_function_resumes_child_await_inside_loop_until_terminal_break() {
    let source = "(#enum ChildPoll ((ChildPending u64) (ChildReady u64)))
      (#fn child-poll ((task u64) (waker (#ref u64))) ChildPoll
        (#return (#if (#u64.== task 0u64)
          (ChildPending 1u64)
          (ChildReady task))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#loop
            (#let result u64
              (#await u64 ChildPending ChildReady child-poll iteration))
            (#set iteration result)
            (#set iteration (#u64.+.wrap iteration 1u64))
            (#if (#u64.== iteration 2u64) (#break) (#continue)))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_does_not_hoist_awaits_out_of_loop_forms() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (ChildReady 1u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#loop
            (#let result u64
              (#await Child ChildPending ChildReady child-poll (Waiting 0u64))))
          (#return 42u64))))";
    let scratch = support::Scratch::new("async-loop-await");
    let input = scratch.path().join("loop.lim");
    let diagnostic = lim::compile_source_to_assembly(
        source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        diagnostic
            .message
            .contains("requires a terminal #break or #continue"),
        "{diagnostic:?}"
    );
    let span = diagnostic.span.expect("await source span");
    assert_eq!(&source[span.start..span.end], "#await");
}

#[test]
fn async_function_rejects_loop_locals_used_after_suspension() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (ChildReady 1u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#while (#u64.< iteration 1u64)
            (#let-mut child-input u64 iteration)
            (#let result u64
              (#await Child ChildPending ChildReady child-poll (Waiting child-input)))
            (#set child-input result)
            (#set iteration (#u64.+.wrap iteration 1u64)))
          (#return 42u64))))";
    let scratch = support::Scratch::new("async-loop-local-after-await");
    let input = scratch.path().join("loop.lim");
    let diagnostic = lim::compile_source_to_assembly(
        source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        diagnostic
            .message
            .contains("is not available after suspension"),
        "{diagnostic:?}"
    );
}

#[test]
fn async_function_can_suspend_at_each_await() {
    let original = example_without_cancel_work();
    let (prefix, _) = original.split_once("(#fn main () u64").unwrap();
    let prefix = prefix.replace(
        "(#return (#u64.+.wrap value offset))",
        "(#let second u64
           (#await Step StepPending StepReady step-poll (Waiting 1u64)))
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
