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
        "{status:?}: {}\ngenerated source:\n{generated}",
        String::from_utf8_lossy(&stderr),
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
fn async_function_early_returns_from_synchronous_loops_produce_ready() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((finish-early bool) (range-early bool) (for-early bool)) u64
          (#while finish-early
            (#return 41u64))
          (#for-range (iteration u32) 0u32
            (#if range-early 1u32 0u32)
            (#return 40u64))
          (#for (#let-mut iteration u32 0u32)
                (#u32.< iteration (#if for-early 1u32 0u32))
                (#set iteration (#u32.+.wrap iteration 1u32))
            (#return 39u64))
          (#let value u64
            (#await Child ChildPending ChildReady child-poll (Waiting 42u64)))
          (#return value))))
      (#fn poll-work ((finish-early bool) (range-early bool) (for-early bool) (waker (#ref u64))) u64
        (#let task Frame
          (#call work (: finish-early finish-early : range-early range-early : for-early for-early)))
        (#let result Poll (#call poll (: task task : waker waker)))
        (#return (#match result
          (#case (Ready value) value)
          (#case (Pending pending) (#block (#forget pending) 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let early u64
          (#call poll-work (: finish-early true : range-early false : for-early false : waker (#borrow waker))))
        (#let range u64
          (#call poll-work (: finish-early false : range-early true : for-early false : waker (#borrow waker))))
        (#let for u64
          (#call poll-work (: finish-early false : range-early false : for-early true : waker (#borrow waker))))
        (#let resumed u64
          (#call poll-work (: finish-early false : range-early false : for-early false : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap early (#u64.+.wrap range (#u64.+.wrap for resumed)))))";
    build_and_run(source, 162);
}

#[test]
fn async_function_early_return_from_synchronous_loop_produces_ready() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#loop (#return 41u64))
          (#let value u64
            (#await Child ChildPending ChildReady child-poll (Waiting 42u64)))
          (#return value))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value u64
          (#match result
            (#case (Ready ready) ready)
            (#case (Pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    build_and_run(source, 41);
}

#[test]
fn async_lowering_errors_highlight_the_later_nested_await() {
    let source = "(#enum Step ((Waiting u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady u64)))
      (#fn step-poll ((task Step) (waker (#ref u64))) StepPoll
        (#return (#match task (#case (Waiting value) (StepReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let first u64
            (#await Step StepPending StepReady step-poll (Waiting 1u64)))
          (#let second u64
            (#await Step StepPending StepReady step-poll
              (Waiting (#await Step StepPending StepReady step-poll (Waiting 2u64)))))
          (#return second))))";
    let scratch = support::Scratch::new("async-await-span");
    let input = scratch.path().join("source.lim");
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
            .contains("nested #await requires an explicit result type"),
        "{diagnostic:?}"
    );
    let span = diagnostic
        .span
        .expect("nested await error has a source span");
    let await_tokens = source.match_indices("#await").collect::<Vec<_>>();
    assert_eq!(await_tokens.len(), 3);
    assert_eq!(span.start, await_tokens[2].0);
    assert_eq!(&source[span.start..span.end], "#await");
}

#[test]
fn async_function_suspends_resumes_and_is_inspectable() {
    let generated = build_and_run(&example_source(), 42);
    assert!(generated.contains("(#enum Work ((Work-start u64) (Work-await-0 u64 u64 Step)))"));
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
      (#fn cancel-frame ((task Frame-state)) ()
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
        (#let state-to-cancel Frame-state (#call poll-cancel (: task cancel-pin)))
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
    assert!(
        generated.contains("(#struct Frame ((state Frame-state)))"),
        "{generated}"
    );
    assert!(
        generated.contains("(#pin-borrow-mut (#get task state))"),
        "poll must project the state field from the pinned shell: {generated}"
    );
    assert!(!generated.contains("(#pin-read task)"), "{generated}");
    assert!(!generated.contains("(#pin-write task"), "{generated}");
    assert!(
        generated.contains("(#pin-read lim.async.pin-state)"),
        "{generated}"
    );
    assert!(
        generated.contains("(#pin-write lim.async.pending-state"),
        "{generated}"
    );
    assert!(
        generated.contains("(#fn poll-cancel ((task (#pin-ref-mut Frame))) Frame-state"),
        "{generated}"
    );
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
fn pinned_async_frame_self_reference_survives_pending_and_is_cleared_on_cancel() {
    let source = include_str!("../examples/async_fn_self_reference.lim");
    let generated = build_and_run(source, 58);
    assert!(
        generated.contains("(#struct SelfRefFrame ((state SelfRefFrame-state) (owner Owner)))"),
        "{generated}"
    );
    assert!(
        generated.contains("(#pin-borrow (#get (#get (#get task owner) payload) left))"),
        "the self-reference must be formed from the pinned frame field: {generated}"
    );
    assert!(
        generated.contains("(SelfRefFrame-await-0 (#pin-ref u64) (#pin-ref u64) Child)"),
        "both disjoint internal references must be retained in the suspended state: {generated}"
    );

    let pending_mutation = source.replace(
        "  (#let second SelfRefPoll",
        "  (#set-field frame owner (#struct-literal Owner ((payload (#struct-literal Payload ((left 99u64) (right 5u64)))))))\n  (#let second SelfRefPoll",
    );
    let error = lim::check_types(&lim::parse_program(&pending_mutation).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the owner must stay borrowed while the frame is Pending: {error}"
    );

    let conflicting_projection = source.replace(
        "  (#let second SelfRefPoll",
        "  (#let left-pin (#pin-ref-mut u64)\n    (#pin-borrow-mut (#get (#get (#get pending-frame owner) payload) left)))\n  (#let second SelfRefPoll",
    );
    let error =
        lim::check_types(&lim::parse_program(&conflicting_projection).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the live internal reference must exclude an overlapping mutable projection: {error}"
    );

    let conflicting_second_projection = source.replace(
        "  (#let second SelfRefPoll",
        "  (#let right-pin (#pin-ref-mut u64)\n    (#pin-borrow-mut (#get (#get (#get pending-frame owner) payload) right)))\n  (#let second SelfRefPoll",
    );
    let error =
        lim::check_types(&lim::parse_program(&conflicting_second_projection).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the second internal reference must also exclude its overlapping mutable projection: {error}"
    );

    let mutation = source.replace(
        "  (#call cancel-self-ref-state (: task state))",
        "  (#set-field cancelled owner (#struct-literal Owner ((payload (#struct-literal Payload ((left 11u64) (right 7u64)))))))\n  (#call cancel-self-ref-state (: task state))",
    );
    let error = lim::check_types(&lim::parse_program(&mutation).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the owner must stay borrowed until the suspended reference is consumed: {error}"
    );

    let direct_owner_use = source.replace(
        "(#u64.+.wrap (#u64.+.wrap (#deref view) (#deref right-view)) result)",
        "(#u64.+.wrap (#u64.+.wrap (#u64.+.wrap (#deref view) (#deref right-view)) result) (#get (#get owner payload) left))",
    );
    let error = lim::parse_program(&direct_owner_use)
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("owner") && error.contains("only be used to initialize"),
        "owner access must not bypass the retained reference loan: {error}"
    );
}

#[test]
fn pinned_async_frame_retains_enum_payload_reference_across_pending() {
    let source = include_str!("../examples/async_fn_enum_self_reference.lim");
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains(
            "(#pin-borrow (#get (#pin-get-payload (#pin-borrow (#get (#get task owner) choice)) Number 0) value))"
        ),
        "the frame should reborrow a struct field nested in the selected enum payload: {generated}"
    );
    assert!(
        generated.contains("(EnumFrame-await-0 (#pin-ref u64) Child)"),
        "the enum-payload reference should be carried in the pending state: {generated}"
    );

    let pending_mutation = source.replace(
        "  (#let second EnumPoll",
        "  (#let choice-pin (#pin-ref-mut Choice)\n    (#pin-borrow-mut (#get (#get pending-frame owner) choice)))\n  (#let second EnumPoll",
    );
    let error = lim::check_types(&lim::parse_program(&pending_mutation).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the enum owner must remain borrowed while its payload reference is pending: {error}"
    );
}

#[test]
fn pinned_async_frame_promotes_a_local_owner_before_self_borrowing_it() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim");
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains(
            "(#fn local-self-ref ((seed u64)) LocalSelfRefFrame\n(#let owner LocalOwner",
        ),
        "the owner must be initialized before the frame is returned: {generated}"
    );
    assert!(
        generated.contains("(#pin-borrow (#get (#get (#get task owner) payload) left))"),
        "the local reference must be formed from the pinned frame's owner: {generated}"
    );

    let late_owner = source.replace(
        "    (#let owner LocalOwner",
        "    (#let before-owner u64 1u64)\n    (#let owner LocalOwner",
    );
    let error = lim::parse_program(&late_owner).unwrap_err();
    assert!(
        error.contains("must be the first function statement"),
        "local owners after other statements are not hoisted implicitly: {error}"
    );
}

#[test]
fn pinned_async_frame_retains_mutable_self_reference_across_pending() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim")
        .replace("(#pin-ref u64)", "(#pin-ref-mut u64)")
        .replace(
            "(#pin-borrow (#get (#get owner payload) left))",
            "(#pin-borrow-mut (#get (#get owner payload) left))",
        )
        .replace(
            "    (#return (#u64.+.wrap (#deref view) result))",
            "    (#unsafe (#pin-write view 41u64))\n    (#return (#u64.+.wrap (#deref view) result))",
        );
    lim::check_types(&lim::parse_program(&source).unwrap()).unwrap();
    let generated = build_and_run(&source, 43);
    assert!(
        generated.contains("(#pin-ref-mut u64)"),
        "the exclusive reference must remain typed in the suspended state: {generated}"
    );

    let overlapping_owner_read = source.replace(
        "    (#unsafe (#pin-write view 41u64))",
        "    (#let overlapping u64 (#get (#get owner payload) left))\n    (#unsafe (#pin-write view 41u64))",
    );
    let error = match lim::parse_program(&overlapping_owner_read) {
        Err(error) => error,
        Ok(program) => lim::check_types(&program).unwrap_err(),
    };
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "reading through the owner must conflict with the retained exclusive projection: {error}"
    );

    let duplicate_exclusive_borrow = source.replace(
        "    (#let result u64",
        "    (#let second-view (#pin-ref-mut u64)\n      (#pin-borrow-mut (#get (#get owner payload) left)))\n    (#let result u64",
    );
    let error = match lim::parse_program(&duplicate_exclusive_borrow) {
        Err(error) => error,
        Ok(program) => lim::check_types(&program).unwrap_err(),
    };
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the same pinned projection must not be borrowed exclusively twice: {error}"
    );

    let (prefix, after_second_poll) = source
        .split_once("  (#let second LocalSelfRefPoll")
        .unwrap();
    let (_, suffix) = after_second_poll.split_once("  (#forget frame)").unwrap();
    let cancelled = format!(
        "{prefix}\
          (#let cancelled-state LocalSelfRefFrame-state\n\
            (#call local-self-ref-poll-cancel (: task pending-frame)))\n\
          (#forget cancelled-state)\n\
          (#set-field frame owner\n\
            (#struct-literal LocalOwner ((payload\n\
              (#struct-literal LocalPayload ((left 41u64) (right 5u64)))))))\n\
          (#let result u64 (#get (#get (#get frame owner) payload) left))\n\
          (#forget frame){suffix}"
    );
    let generated = build_and_run(&cancelled, 41);
    assert!(
        generated.contains("(#fn local-self-ref-poll-cancel"),
        "the generated cancel path should be exercised: {generated}"
    );
}

#[test]
fn pinned_async_result_reference_keeps_its_frame_borrow_live() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim")
        .replace(
            "(#fn local-self-ref ((seed u64)) u64",
            "(#fn local-self-ref ((seed u64)) (#pin-ref u64)",
        )
        .replace(
            "(#return (#u64.+.wrap (#deref view) result))",
            "(#return view)",
        )
        .replace(
            "(#let result u64\n    (#match second",
            "(#let result (#pin-ref u64)\n    (#match second",
        )
        .replace("(#return result))", "(#return (#deref result)))");
    let error = lim::check_types(&lim::parse_program(&source).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("pinned") || error.contains("destroy"),
        "the async result reference must keep its pinned frame borrowed: {error}"
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
fn async_function_without_await_runs_its_body_on_first_poll() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work ((cell (#ref CellU64))) u64
             (#call CellU64-set (: cell cell : value 1u64))
             (#return (#u64.+.wrap (#call CellU64-get (: cell cell)) 41u64)))))
         (#fn main () u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let task Frame (#call work (: cell (#borrow cell))))
           (#let before u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let waker u64 0u64)
           (#let outcome Poll (#call poll (: task task : waker (#borrow waker))))
           (#let result u64
             (#match outcome
               (#case (Ready value) value)
               (#case (Pending pending) (#block (#forget pending) 0u64))))
           (#let after u64 (#call CellU64-get (: cell (#borrow cell))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#bool.&& (#u64.== result 42u64)
                                            (#u64.== after 1u64)))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run(&source, 42);
    assert!(generated.contains("poll-start"), "{generated}");
    assert!(generated.contains("(#return (Ready"), "{generated}");
}

#[test]
fn pinned_async_function_without_await_runs_on_first_poll() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (@async-fn-pinned (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work ((cell (#ref CellU64))) u64
             (#call CellU64-set (: cell cell : value 1u64))
             (#return (#u64.+.wrap (#call CellU64-get (: cell cell)) 41u64)))))
         (#fn main () u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let-mut frame Frame (#call work (: cell (#borrow cell))))
           (#let before u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let waker u64 0u64)
           (#let outcome Poll
             (#call poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
           (#let result u64
             (#match outcome
               (#case (Ready value) value)
               (#case (Pending pending) (#block (#forget pending) 0u64))))
           (#let after u64 (#call CellU64-get (: cell (#borrow cell))))
           (#forget frame)
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#bool.&& (#u64.== result 42u64)
                                            (#u64.== after 1u64)))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run(&source, 42);
    assert!(generated.contains("(#pin-ref-mut Frame)"), "{generated}");
    assert!(generated.contains("(#fn poll-cancel"), "{generated}");
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
            "(#return (#u64.+.wrap total offset))",
            "(#if (#u64.== offset 1u64)
           (#block (#set offset (#u64.+.wrap offset 5u64)) ())
           (#block (#set offset (#u64.+.wrap offset 10u64)) ()))
         (#match offset
           (#case 6u64 (#block (#set offset (#u64.+.wrap offset 1u64)) ()))
           (#case _ (#block (#set offset 99u64) ())))
         (#let second u64
           (#await Step StepPending StepReady step-poll (Waiting 0u64)))
         (#return (#u64.+.wrap total offset))",
        )
        .replace("((offset u64)) u64", "((#mut offset u64)) u64");
    let generated = build_and_run(&source, 48);
    assert!(generated.contains("Work-await-1"));
    assert!(generated.contains("work-poll-resume-1"));
}

#[test]
fn async_function_has_no_fixed_suspension_count_limit() {
    let mut body = String::new();
    for index in 0..33 {
        body.push_str(&format!(
            "(#let result-{index} u64 (#await Step StepPending StepReady step-poll (Waiting {index}u64)))\n"
        ));
    }
    body.push_str("(#return result-32)");
    let source = format!(
        "(#enum Step ((Waiting u64)))
         (#linear Step)
         (#enum StepPoll ((StepPending Step) (StepReady u64)))
         (#fn step-poll ((task Step) (waker (#ref u64))) StepPoll
           (#return (#match task (#case (Waiting value) (StepReady value)))))
         (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work () u64 {body})))
         (#fn main () u64
           (#let waker u64 0u64)
           (#let outcome Poll
             (#call poll (: task (#call work (:)) : waker (#borrow waker))))
           (#let result u64
             (#match outcome
               (#case (Ready value) value)
               (#case (Pending task) (#block (#forget task) 0u64))))
           (#forget waker)
           (#return result))"
    );
    let generated = build_and_run(&source, 32);
    assert!(generated.contains("Frame-await-32"), "{generated}");
}

#[test]
fn async_function_awaits_a_task_produced_by_an_earlier_await() {
    let source = "(#enum OuterTask ((Waiting u64) (Resuming u64)))
      (#linear OuterTask)
      (#enum OuterPoll ((OuterPending OuterTask) (OuterReady u64)))
      (#fn outer-poll ((task OuterTask) (waker (#ref u64))) OuterPoll
        (#return (#match task
          (#case (Waiting value) (OuterPending (Resuming value)))
          (#case (Resuming value) (OuterReady value)))))
      (#enum InnerTask (MakeOuter))
      (#enum InnerPoll ((InnerPending InnerTask) (InnerReady OuterTask)))
      (#fn inner-poll ((task InnerTask) (waker (#ref u64))) InnerPoll
        (#return (#match task
          (#case MakeOuter (InnerReady (Waiting 42u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#await OuterTask OuterPending OuterReady outer-poll
              (#await OuterTask InnerTask InnerPending InnerReady inner-poll MakeOuter)))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll-resume-1"), "{generated}");
    assert!(!generated.contains("(#await"), "{generated}");
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
fn async_function_suspends_in_a_value_block_with_conditional_await() {
    let source = "(#enum StepTask ((Waiting u64) (Resuming u64)))
      (#enum StepPoll ((StepPending StepTask) (StepReady u64)))
      (#linear StepTask)
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case (Waiting value) (StepPending (Resuming value)))
          (#case (Resuming value) (StepReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((choose bool)) u64
          (#let value u64
            (#block
              (#let base u64 13u64)
              (#if choose
                (#await u64 StepTask StepPending StepReady step-poll (Waiting base))
                0u64)))
          (#return (#u64.+.wrap value 13u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (: choose true)))
        (#let first Poll (#call poll (: task task : waker (#borrow waker))))
        (#let result u64
          (#match first
            (#case (PollReady first-value) first-value)
            (#case (PollPending pending)
              (#match (#call poll (: task pending : waker (#borrow waker)))
                (#case (PollReady second-value) second-value)
                (#case (PollPending unexpected)
                  (#block (#forget unexpected) 0u64))))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 26);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_function_suspends_inside_mutable_assignment_rhs() {
    let source = "(#struct Waker ((count u64)))
      (#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker Waker : function
        (#fn work () u64
          (#let-mut total u64 10u64)
          (#set total
            (#await u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
          (#return total))))
      (#fn main () u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(#set total lim.async.nested-await-0)"),
        "{generated}"
    );
    assert!(
        generated.contains("(#fn poll-resume-0 ((#mut total u64)"),
        "{generated}"
    );
}

#[test]
fn async_loop_expression_can_be_suspended_as_a_nested_value() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let ignored ()
            (#loop
              (#let result u64
                (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
              (#break)))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (:)))
        (#let first Poll (#call poll (: task task : waker (#borrow waker))))
        (#let-else (PollPending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let-else (PollReady result) Poll second (#unreachable))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_while_expression_can_be_suspended_as_a_nested_value() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let ignored ()
            (#block
              (#let-mut iteration u64 0u64)
              (#while (#u64.< iteration 1u64)
                (#let result u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#set iteration 1u64))))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (:)))
        (#let first Poll (#call poll (: task task : waker (#borrow waker))))
        (#let-else (PollPending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let-else (PollReady result) Poll second (#unreachable))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_loop_expression_can_be_suspended_in_a_selected_branch() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((choose bool)) u64
          (#let ignored ()
            (#if choose
              (#loop
                (#let value u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break))
              ()))
          (#return 42u64))))
      (#fn run ((choose bool) (waker (#ref u64))) u64
        (#let task Frame (#call work (: choose choose)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let awaited u64 (#call run (: choose true : waker (#borrow waker))))
        (#let immediate u64 (#call run (: choose false : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap awaited immediate)))";
    let generated = build_and_run(source, 84);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_suspension_inside_nested_value_block_preserves_block_scope() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn identity ((value u64)) u64 (#return value))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call identity (: value
              (#block
                (#let value u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                value))))
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 41);
    assert!(generated.contains("#call identity"), "{generated}");
}

#[test]
fn async_value_loop_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn identity ((value u64)) u64 (#return value))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call identity (: value
              (#loop
                (#let awaited u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break awaited)))))
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 41);
    assert!(generated.contains("loop-result-state"), "{generated}");
}

#[test]
fn async_value_loop_break_moves_linear_payload_across_pending() {
    let source = "(#struct Token ((value u64)))
      (#linear Token)
      (#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Token)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value)
            (ChildReady (#struct-literal Token ((value value))))))))
      (#fn consume-token ((token Token)) u64
        (#let value u64 (#get token value))
        (#forget token)
        (#return value))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call consume-token (: token
              (#loop
                (#let token Token
                  (#await Token ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break token)))))
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 41);
}

#[test]
fn async_unit_loop_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) u64 (#return 42u64))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call consume-unit (: value
              (#loop
                (#let awaited u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break)))))
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_unit_while_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) u64 (#return 43u64))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call consume-unit (: value
              (#while true
                (#let awaited u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break)))))
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 43);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_for_range_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) u64 (#return 44u64))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call consume-unit (: value
              (#for-range (iteration u64) 0u64 1u64
                (#let awaited u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll
                    (Waiting iteration)))))))
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 44);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_for_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) u64 (#return 45u64))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call consume-unit (: value
              (#for (#let-mut iteration u64 0u64)
                    (#u64.< iteration 1u64)
                    (#set iteration (#u64.+.wrap iteration 1u64))
                (#let awaited u64
                  (#await u64 ChildTask ChildPending ChildReady child-poll
                    (Waiting iteration)))))))
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 45);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_while_let_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Maybe)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady None)))))
      (#fn consume-unit ((value ())) u64 (#return 46u64))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#call consume-unit (: value
              (#while-let (Some payload)
                (#await Maybe ChildTask ChildPending ChildReady child-poll (Waiting 0u64))
                ()))) )
          (#return result))))
      (#fn run ((waker (#ref u64))) u64
        (#let task Frame (#call work ()))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 46);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_function_suspends_inside_projected_assignment_rhs() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut values (#array u64 1) (#array-of (#array u64 1) 0u64))
          (#set-index values 0usize
            (#await u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
          (#return (#index values 0usize)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(#set-index values (#literal usize 0) lim.async.nested-await-0)"),
        "{generated}"
    );
    assert!(generated.contains("(#fn poll-resume-0"), "{generated}");
}

#[test]
fn async_function_awaits_before_selecting_an_if_branch() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady true)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#if (#await bool Child ChildPending ChildReady child-poll (Waiting 1u64))
              42u64
              0u64))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("lim.async.nested-await-0"),
        "{generated}"
    );
    assert!(
        generated.contains("(#if lim.async.nested-await-0"),
        "{generated}"
    );
}

#[test]
fn async_function_awaits_before_selecting_a_match_arm() {
    let source = "(#enum Decision ((Continue u64) Stop))
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady Decision)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady (Continue 42u64))
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#return (#match (#await Decision Child ChildPending ChildReady child-poll (Waiting 1u64))
            (#case (Continue value) value)
            (#case Stop 0u64))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("lim.async.nested-await-0"),
        "{generated}"
    );
    assert!(
        generated.contains("(#match lim.async.nested-await-0"),
        "{generated}"
    );
}

#[test]
fn async_function_resumes_inside_a_value_producing_block() {
    let source = "(#struct DecisionResult ((condition bool) (value u64)))
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady true)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let result DecisionResult
            (#block
              (#let offset u64 40u64)
              (#let choose bool true)
              (#let condition bool
                (#if choose
                  (#await bool Child ChildPending ChildReady child-poll
                    (Waiting (#u64.-.wrap offset 39u64)))
                  false))
              (#struct-literal DecisionResult
                ((condition condition)
                 (value (#if condition (#u64.+.wrap offset 2u64) 0u64))))))
          (#return (#get result value)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(condition lim.async.nested-await-"),
        "{generated}"
    );
    assert!(
        generated.contains("(#fn poll-resume-0 ((lim.async.nested-await-1 u64)"),
        "the block-local value must be carried across Pending: {generated}"
    );
    assert!(
        generated.contains("(#u64.-.wrap lim.async.nested-await-1 (#literal u64 39))"),
        "block-local setup must also initialize the child task: {generated}"
    );
}

#[test]
fn async_function_assigns_conditional_await_result_inside_a_block() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady 42u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((choose bool)) u64
          (#return (#block
            (#let-mut result u64 0u64)
            (#set result
              (#if choose
                (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
                7u64))
            result)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (: choose true)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 42);
}

#[test]
fn async_function_resumes_multiple_awaits_inside_one_block() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady true)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#block
              (#let first bool
                (#await bool Child ChildPending ChildReady child-poll (Waiting 1u64)))
              (#let second bool
                (#await bool Child ChildPending ChildReady child-poll (Waiting 2u64)))
              (#if (#bool.&& first second) 42u64 0u64)))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending after-first) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task after-first : waker (#borrow waker))))
        (#let-else (Pending after-second) Poll second (#unreachable))
        (#let third Poll (#call poll (: task after-second : waker (#borrow waker))))
        (#let-else (Pending after-third) Poll third (#unreachable))
        (#let fourth Poll (#call poll (: task after-third : waker (#borrow waker))))
        (#let result u64
          (#match fourth
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll-resume-1"), "{generated}");
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
fn async_function_assigns_a_block_local_after_await_resumes() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut total (#array u64 1)
            (#array-of (#array u64 1) 1u64))
          (#let result u64
            (#block
              (#set-index total 0usize
                (#await u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
              (#index total 0usize)))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(#set-index total (#literal usize 0) lim.async.nested-await-0)"),
        "{generated}"
    );
    assert!(
        generated.contains("(#fn poll-resume-0 ((#mut total (#array u64 1))"),
        "the mutable assignment target must survive Pending: {generated}"
    );
}

#[test]
fn async_function_preserves_mutability_of_block_await_bindings() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 41u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#block
              (#let-mut value u64
                (#await u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
              (#set value (#u64.+.wrap value 1u64))
              value))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(#mut lim.async.nested-await-0 u64)"),
        "the resumed helper must receive a mutable binding: {generated}"
    );
}

#[test]
fn async_function_runs_block_prefix_side_effect_once_before_await() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady 42u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut count u64 0u64)
          (#let result u64
            (#block
              (#set count (#u64.+.wrap count 1u64))
              (#let value u64
                (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
              (#u64.+.wrap value count)))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending running-task) Poll first (#unreachable))
        (#let second Poll (#call poll (: task running-task : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 43);
}

#[test]
fn async_function_suspends_on_a_discarded_copy_await_in_a_block() {
    let source = "(#enum ChildTask (Start Resume))
      (#linear ChildTask)
      (#enum ChildPoll ((Pending ChildTask) (Ready ())))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case Start (Pending Resume))
          (#case Resume (Ready ())))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#block
              (#let base u64 40u64)
              (#await () ChildTask Pending Ready child-poll Start)
              (#u64.+.wrap base 2u64)))
          (#return result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (:)))
        (#let first Poll (#call poll (: task task : waker (#borrow waker))))
        (#let-else (PollPending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (PollReady value) value)
            (#case (PollPending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll-child"), "{generated}");
}

#[test]
fn async_function_rejects_discarding_a_linear_await_result_in_a_block() {
    let source = "(#struct Resource ((value u64)))
      (#linear Resource)
      (#enum ChildTask (Start Resume))
      (#linear ChildTask)
      (#enum ChildPoll ((Pending ChildTask) (Ready Resource)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case Start (Pending Resume))
          (#case Resume (Ready (#struct-literal Resource ((value 1u64))))))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work () u64
          (#let result u64
            (#block
              (#await Resource ChildTask Pending Ready child-poll Start)
              42u64))
          (#return result))))";
    let error = lim::parse_program(source).unwrap_err();
    assert!(
        error.contains("cannot discard a non-Copy #await result"),
        "{error}"
    );

    let direct_source = source.replace(
        "          (#let result u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
        "          (#await Resource ChildTask Pending Ready child-poll Start)\n          (#return 42u64)",
    );
    assert_ne!(direct_source, source);
    let direct_error = lim::parse_program(&direct_source).unwrap_err();
    assert!(
        direct_error.contains("cannot discard a non-Copy #await result"),
        "{direct_error}"
    );

    let untyped_source = direct_source.replace(
        "#await Resource ChildTask Pending",
        "#await ChildTask Pending",
    );
    assert_ne!(untyped_source, direct_source);
    let untyped_error = lim::parse_program(&untyped_source).unwrap_err();
    assert!(
        untyped_error.contains("discarded #await result requires an explicit type"),
        "{untyped_error}"
    );

    let terminal_block_source = source.replace(
        "          (#let result u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
        "          (#block\n            (#await Resource ChildTask Pending Ready child-poll Start))\n          (#return 42u64)",
    );
    assert_ne!(terminal_block_source, source);
    let type_error = lim::parse_program(&terminal_block_source).unwrap_err();
    assert!(
        type_error.contains("cannot discard a non-Copy #await result"),
        "{type_error}"
    );

    let conditional_source = source.replace(
        "          (#let result u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
        "          (#if true\n            (#await Resource ChildTask Pending Ready child-poll Start)\n            (#await Resource ChildTask Pending Ready child-poll Resume))\n          (#return 42u64)",
    );
    assert_ne!(conditional_source, source);
    let conditional_error = match lim::parse_program(&conditional_source) {
        Err(error) => error,
        Ok(program) => lim::check_types(&program)
            .expect_err("discarding an awaited linear if result must be rejected"),
    };
    assert!(
        conditional_error.contains("cannot discard a non-Copy #await result")
            || conditional_error.contains("linear value")
            || conditional_error.contains("must be consumed"),
        "{conditional_error}"
    );

    let match_source = source.replace(
        "          (#let result u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
        "          (#match true\n            (#case true (#await Resource ChildTask Pending Ready child-poll Start))\n            (#case false (#await Resource ChildTask Pending Ready child-poll Resume)))\n          (#return 42u64)",
    );
    assert_ne!(match_source, source);
    let match_error = lim::parse_program(&match_source).unwrap_err();
    assert!(
        match_error.contains("cannot discard a non-Copy #await result"),
        "{match_error}"
    );
}

#[test]
fn async_function_let_else_returns_ready_before_and_after_suspension() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe) (after Maybe)) u64
          (#let-else (Some payload) Maybe input (#return 7u64))
          (#let value u64
            (#await Child ChildPending ChildReady child-poll (Waiting 42u64)))
          (#let-else (Some ignored) Maybe after (#return 9u64))
          (#return value))))
      (#fn poll-work ((input Maybe) (after Maybe) (waker (#ref u64))) u64
        (#let task Frame (#call work (: input input : after after)))
        (#let result Poll (#call poll (: task task : waker waker)))
        (#return (#match result
          (#case (Ready value) value)
          (#case (Pending pending) (#block (#forget pending) 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let early u64
          (#call poll-work (: input None : after (Some 1u64) : waker (#borrow waker))))
        (#let post-await u64
          (#call poll-work (: input (Some 1u64) : after None : waker (#borrow waker))))
        (#let awaited u64
          (#call poll-work (: input (Some 1u64) : after (Some 1u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap (#u64.+.wrap early post-await) awaited)))";
    let generated = build_and_run(source, 58);
    assert!(generated.contains("#return (Ready"), "{generated}");
}

#[test]
fn async_function_can_await_let_else_scrutinee() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum Child ((Waiting Maybe)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady Maybe)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let-else (Some value) Maybe
            (#await Child ChildPending ChildReady child-poll (Waiting input))
            (#return 7u64))
          (#return value))))
      (#fn poll-work ((input Maybe) (waker (#ref u64))) u64
        (#let task Frame (#call work (: input input)))
        (#let result Poll (#call poll (: task task : waker waker)))
        (#return (#match result
          (#case (Ready value) value)
          (#case (Pending pending) (#block (#forget pending) 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let unmatched u64
          (#call poll-work (: input None : waker (#borrow waker))))
        (#let matched u64
          (#call poll-work (: input (Some 42u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap unmatched matched)))";
    build_and_run(source, 49);
}

#[test]
fn async_function_awaits_inside_let_else_return_expression() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 7u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let-else (Some value) Maybe input
            (#return (#u64.+.wrap 1u64
              (#await u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))))
          (#return value))))";
    let source = format!(
        "{source}
         (#fn poll-work ((input Maybe) (waker (#ref u64))) u64
           (#let task Frame (#call work (: input input)))
           (#let first Poll (#call poll (: task task : waker waker)))
           (#let result u64
             (#match first
               (#case (Ready value) value)
               (#case (Pending pending) (#block
                 (#let second Poll (#call poll (: task pending : waker waker)))
                 (#match second
                   (#case (Ready value) value)
                   (#case (Pending unexpected) (#block (#forget unexpected) 0u64)))))))
           (#return result))
         (#fn main () u64
           (#let waker u64 0u64)
           (#let mismatch u64 (#call poll-work (: input None : waker (#borrow waker))))
           (#let matched u64 (#call poll-work (: input (Some 41u64) : waker (#borrow waker))))
           (#forget waker)
           (#return (#u64.+.wrap mismatch matched)))"
    );
    build_and_run(&source, 49);
}

#[test]
fn async_let_else_can_await_before_an_unreachable_failure() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let-else (Some payload) Maybe input
            (#block
              (#let ignored u64
                (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))
              (#unreachable)))
          (#return payload))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (: input (Some 42u64))))
        (#let outcome Poll (#call poll (: task task : waker (#borrow waker))))
        (#let value u64
          (#match outcome
            (#case (Ready ready) ready)
            (#case (Pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll-child"), "{generated}");
}

#[test]
fn async_let_else_awaits_inside_an_assertion_before_unreachable() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ChildTask (Waiting))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildReady 42u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let-else (Some value) Maybe input
            (#block
              (#assert (#u64.==
                (#await u64 ChildTask ChildPending ChildReady child-poll Waiting)
                42u64))
              (#unreachable)))
          (#return value))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (: input (Some 42u64))))
        (#let outcome Poll (#call poll (: task task : waker (#borrow waker))))
        (#let result u64
          (#match outcome
            (#case (Ready value) value)
            (#case (Pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll-child"), "{generated}");
}

#[test]
fn async_let_else_accepts_conditional_awaited_return_arms() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((input Maybe) (choose bool)) u64
          (#let-else (Some payload) Maybe input
            (#block
              (#let base u64 13u64)
              (#if choose
                (#return (#await u64 ChildTask ChildPending ChildReady
                  child-poll (Waiting base)))
                (#return (#u64.+.wrap base 4u64)))))
          (#return payload))))
      (#fn drive ((input Maybe) (choose bool) (waker (#ref u64))) u64
        (#let task Frame (#call work (: input input : choose choose)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady first-value) first-value)
          (#case (PollPending pending)
            (#match (#call poll (: task pending : waker waker))
              (#case (PollReady second-value) second-value)
              (#case (PollPending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let awaited u64
          (#call drive (: input None : choose true : waker (#borrow waker))))
        (#let immediate u64
          (#call drive (: input None : choose false : waker (#borrow waker))))
        (#let matched u64
          (#call drive (: input (Some 9u64) : choose true : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap (#u64.+.wrap awaited immediate) matched)))";
    build_and_run(source, 39);
}

#[test]
fn async_let_else_diverging_branch_can_return_after_multiple_awaits() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let-else (Some matched) Maybe input
            (#block
              (#let first u64
                (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 20u64)))
              (#let second u64
                (#await u64 ChildTask ChildPending ChildReady child-poll
                  (Waiting (#u64.+.wrap first 7u64))))
              (#return (#u64.+.wrap first second))))
          (#return matched))))
      (#fn run ((input Maybe) (waker (#ref u64))) u64
        (#let task Frame (#call work (: input input)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (PollReady result) result)
          (#case (PollPending after-first)
            (#match (#call poll (: task after-first : waker waker))
              (#case (PollReady result) result)
              (#case (PollPending after-second)
                (#match (#call poll (: task after-second : waker waker))
                  (#case (PollReady result) result)
                  (#case (PollPending unexpected)
                    (#block (#forget unexpected) 0u64)))))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let missing u64 (#call run (: input None : waker (#borrow waker))))
        (#let present u64 (#call run (: input (Some 9u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap missing present)))";
    build_and_run(source, 56);
}

#[test]
fn async_function_requires_explicit_type_for_nested_let_else_await() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let-else (Some value) Maybe input
            (#return (#u64.+.wrap 1u64
              (#await Child ChildPending ChildReady child-poll (Waiting 7u64)))))
          (#return value))))";
    let error = lim::parse_program(source).unwrap_err();
    assert!(
        error.contains("nested #await requires an explicit result type"),
        "{error}"
    );
}

#[test]
fn async_function_only_polls_awaited_let_else_mismatch_arm() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 7u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let-else (Some value) Maybe input
            (#block
              (#let retry-count u64 1u64)
              (#let first u64
                (#await u64 Child ChildPending ChildReady child-poll
                  (Waiting retry-count)))
              (#let second u64
                (#await u64 Child ChildPending ChildReady child-poll
                  (Waiting 0u64)))
              (#return (#u64.+.wrap first second))))
          (#let adjusted u64 (#u64.+.wrap value 1u64))
          (#return adjusted))))
      (#fn poll-work ((input Maybe) (waker (#ref u64))) u64
        (#let task Frame (#call work (: input input)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (Ready value) value)
          (#case (Pending running-task)
            (#block
              (#let second Poll (#call poll (: task running-task : waker waker)))
              (#match second
                (#case (Ready value) value)
                (#case (Pending pending) (#block (#forget pending) 0u64))))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let mismatch u64
          (#call poll-work (: input None : waker (#borrow waker))))
        (#let matched u64
          (#call poll-work (: input (Some 42u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap mismatch matched)))";
    build_and_run(source, 57);
}

#[test]
fn async_function_resumes_suspension_after_awaited_let_else_success() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum Child ((Waiting u64) (SuccessWaiting u64 u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 7u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64)))))
          (#case (SuccessWaiting remaining value)
            (#if (#u64.== remaining 0u64)
              (ChildReady value)
              (ChildPending
                (SuccessWaiting (#u64.-.wrap remaining 1u64) value)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#let base u64 1u64)
          (#let-else (Some value) Maybe input
          (#return (#await u64 Child ChildPending ChildReady child-poll
              (Waiting 1u64))))
          (#let result u64
            (#await Child ChildPending ChildReady child-poll
              (SuccessWaiting 1u64 (#u64.+.wrap value base))))
          (#return result))))
      (#fn poll-work ((input Maybe) (waker (#ref u64))) u64
        (#let task Frame (#call work (: input input)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (Ready value) value)
          (#case (Pending running-task)
            (#block
              (#let second Poll (#call poll (: task running-task : waker waker)))
              (#match second
                (#case (Ready value) value)
                (#case (Pending pending) (#block (#forget pending) 0u64))))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let mismatch u64
          (#call poll-work (: input None : waker (#borrow waker))))
        (#let matched u64
          (#call poll-work (: input (Some 42u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap mismatch matched)))";
    build_and_run(source, 50);
}

#[test]
fn async_function_releases_let_else_success_borrow_after_ready() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum Child ((Waiting u64) (WriteAfterResume (#ref-mut u64) u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value))
          (#case (WriteAfterResume owner remaining)
            (#if (#u64.== remaining 0u64)
              (#block (#deref-set owner 42u64) (ChildReady 42u64))
              (ChildPending
                (WriteAfterResume owner (#u64.-.wrap remaining 1u64))))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe) (owner (#ref-mut u64))) u64
          (#let-else (Some value) Maybe input
            (#return (#await u64 Child ChildPending ChildReady child-poll
              (Waiting 7u64))))
          (#let result u64
            (#await Child ChildPending ChildReady child-poll
              (WriteAfterResume owner 1u64)))
          (#return result))))
      (#fn main () u64
        (#let-mut owner u64 1u64)
        (#let waker u64 0u64)
        (#let task Frame (#call work
          (: input (Some 10u64) : owner (#borrow-mut owner))))
        (#let first Poll (#call poll (: task task : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        MUTATE_WHILE_PENDING
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64 (#match second
          (#case (Ready value) value)
          (#case (Pending unfinished) (#block (#forget unfinished) 0u64))))
        (#set owner 3u64)
        (#forget waker)
        (#return (#u64.+.wrap result owner)))";
    let accepted = source.replace("MUTATE_WHILE_PENDING", "");
    build_and_run(&accepted, 45);

    let rejected = source.replace("MUTATE_WHILE_PENDING", "(#set owner 4u64)");
    let error = lim::check_types(&lim::parse_program(&rejected).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("loan"),
        "the success child must retain its exclusive borrow while Pending: {error}"
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
      (#struct Increment ((value u64)))
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
              (#block
                (#let increment Increment
                  (#struct-literal Increment ((value 1u64))))
                (#let-mut awaited-value u64
                  (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
                (#let second-value u64
                  (#await u64 Child ChildPending ChildReady child-poll (Waiting awaited-value)))
                (#u64.+.wrap second-value (#get increment value)))
              41u64))
          (#return result))))
      (#enum Choice (Await Immediate))
      (@async-fn (: names (MatchFrame MatchPoll MatchPending MatchReady match-poll) : waker u64 : function
        (#fn work-match ((choice Choice)) u64
          (#let result u64
            (#match choice
              (#case Await
                (#block
                  (#let increment Increment
                    (#struct-literal Increment ((value 1u64))))
                  (#let-mut awaited-value u64
                    (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
                  (#let second-value u64
                    (#await u64 Child ChildPending ChildReady child-poll (Waiting awaited-value)))
                  (#u64.+.wrap second-value (#get increment value))))
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
                (#case (Pending awaited-again)
                  (#match (#call poll (: task awaited-again : waker (#borrow waker)))
                    (#case (Ready awaited-third-ready) awaited-third-ready)
                    (#case (Pending awaited-third) (#block (#forget awaited-third) (#unreachable)))))))))
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
                (#case (MatchPending match-again)
                  (#match (#call match-poll (: task match-again : waker (#borrow waker)))
                    (#case (MatchReady match-third-ready) match-third-ready)
                    (#case (MatchPending match-third) (#block (#forget match-third) (#unreachable)))))))))
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
    let generated = build_and_run(source, 86);
    assert!(generated.contains(".choice-"), "{generated}");
    assert!(generated.contains("-poll-result"), "{generated}");
}

#[test]
fn async_conditional_branch_value_expressions_can_suspend() {
    let source = "(#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady 41u64))))))
      (#fn add-one ((value u64)) u64
        (#return (#u64.+.wrap value 1u64)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((choose bool)) u64
          (#return (#call add-one (: value
            (#block
              (#if choose
                (#u64.+.wrap
                  (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
                  1u64)
                0u64))))))))
      (#enum Choice (Await Immediate))
      (@async-fn (: names (MatchFrame MatchPoll MatchPending MatchReady match-poll) : waker u64 : function
        (#fn work-match ((choice Choice)) u64
          (#return (#call add-one (: value
            (#match choice
              (#case Await
                (#u64.+.wrap
                  (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
                  1u64))
              (#case Immediate 0u64))))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let if-first Poll
          (#call poll (: task (#call work (: choose true)) : waker (#borrow waker))))
        (#let if-value u64
          (#match if-first
            (#case (Pending if-child)
              (#match (#call poll (: task if-child : waker (#borrow waker)))
                (#case (Ready value) value)
                (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
            (#case (Ready value) value)))
        (#let if-immediate Poll
          (#call poll (: task (#call work (: choose false)) : waker (#borrow waker))))
        (#let if-immediate-value u64
          (#match if-immediate
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#let match-first MatchPoll
          (#call match-poll (: task (#call work-match (: choice Await)) : waker (#borrow waker))))
        (#let match-value u64
          (#match match-first
            (#case (MatchPending match-child)
              (#match (#call match-poll (: task match-child : waker (#borrow waker)))
                (#case (MatchReady value) value)
                (#case (MatchPending unexpected) (#block (#forget unexpected) 0u64))))
            (#case (MatchReady value) value)))
        (#let match-immediate MatchPoll
          (#call match-poll (: task (#call work-match (: choice Immediate)) : waker (#borrow waker))))
        (#let match-immediate-value u64
          (#match match-immediate
            (#case (MatchReady value) value)
            (#case (MatchPending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return (#u64.+.wrap
          (#u64.+.wrap if-value if-immediate-value)
          (#u64.+.wrap match-value match-immediate-value))))";
    let generated = build_and_run(source, 88);
    assert!(generated.contains("-expression-frame"), "{generated}");
}

#[test]
fn async_conditional_value_await_captures_typed_function_parameters() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((offset u64)) u64
          (#return (#if true
            (#u64.+.wrap
              (#await u64 Child ChildPending ChildReady child-poll (Waiting 2u64))
              offset)
            0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (: offset 40u64)))
        (#let result Poll (#call poll (: task task : waker (#borrow waker))))
        (#let value u64
          (#match result
            (#case (Ready value) value)
            (#case (Pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("offset u64"), "{generated}");
}

#[test]
fn async_conditional_value_await_captures_typed_local_bindings() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let offset u64 40u64)
          (#return (#if true
            (#u64.+.wrap
              (#await u64 Child ChildPending ChildReady child-poll (Waiting 2u64))
              offset)
            0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (:)))
        (#let result Poll (#call poll (: task task : waker (#borrow waker))))
        (#let value u64
          (#match result
            (#case (Ready value) value)
            (#case (Pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("offset u64"), "{generated}");
}

#[test]
fn async_conditional_block_continuation_captures_typed_locals() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((offset u64)) u64
          (#return (#if true
            (#block
              (#let result u64
                (#await u64 Child ChildPending ChildReady child-poll (Waiting 2u64)))
              (#u64.+.wrap result offset))
            0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (: offset 40u64)))
        (#let result Poll (#call poll (: task task : waker (#borrow waker))))
        (#let value u64
          (#match result
            (#case (Ready value) value)
            (#case (Pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("offset u64"), "{generated}");
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
fn pinned_async_frame_retains_an_external_pinned_borrow_across_pending() {
    let source = "(#enum Child ((Waiting u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady count))))))
      (@async-fn-pinned (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn read-after-await ((view (#pin-ref u64))) u64
          (#let result u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#return (#u64.+.wrap (#deref view) result)))))
      (#fn main () u64
        (#let-mut owner u64 40u64)
        (#let view (#pin-ref u64) (#pin-borrow owner))
        (#let-mut frame Frame (#call read-after-await (: view view)))
        (#forget view)
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
        (#set owner 41u64)
        (#forget waker)
        (#return (#if (#u64.== result 41u64) owner 0u64)))";

    let mutation_while_pending = source.replace(
        "        (#let second Poll",
        "        (#set owner 99u64)\n        (#let second Poll",
    );
    let error =
        lim::check_types(&lim::parse_program(&mutation_while_pending).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("pinned") || error.contains("access"),
        "a suspended pinned frame must keep its external owner borrowed: {error}"
    );

    let generated = build_and_run(source, 41);
    assert!(generated.contains("(#pin-ref u64)"), "{generated}");
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
                (#await u64 Child ChildPending ChildReady child-poll (Waiting task-input)))
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
    let generated = build_and_run(&source, 2);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_while_body_suspends_inside_a_call_argument() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting u64)))
         (#linear ChildTask)
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
         (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
           (#return (#match task
             (#case (Waiting remaining)
               (#if (#u64.== remaining 0u64)
                 (ChildPending (Waiting 1u64))
                 (ChildReady 42u64))))))
         (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work ((cell (#ref CellU64))) u64
             (#let-mut iteration u64 0u64)
             (#while (#u64.< iteration 1u64)
               (#call CellU64-set (: cell cell : value
                 (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64))))
               (#set iteration (#u64.+.wrap iteration 1u64)))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker u64 0u64)
           (#let task Frame (#call work (: cell (#borrow cell))))
           (#let first Poll (#call poll (: task task : waker (#borrow waker))))
           (#let-else (Pending pending) Poll first (#unreachable))
           (#let before u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
           (#let result u64
             (#match second
               (#case (Ready value) value)
               (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#u64.== result 42u64))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run(&source, 42);
    assert!(generated.contains("-body-frame"), "{generated}");
}

#[test]
fn async_for_body_suspends_inside_a_call_argument() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting u64)))
         (#linear ChildTask)
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
         (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
           (#return (#match task
             (#case (Waiting remaining)
               (#if (#u64.== remaining 0u64)
                 (ChildPending (Waiting 1u64))
                 (ChildReady 42u64))))))
         (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work ((cell (#ref CellU64))) u64
             (#for (#let-mut iteration u64 0u64)
                   (#u64.< iteration 1u64)
                   (#set iteration (#u64.+.wrap iteration 1u64))
               (#call CellU64-set (: cell cell : value
                 (#await u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker u64 0u64)
           (#let task Frame (#call work (: cell (#borrow cell))))
           (#let first Poll (#call poll (: task task : waker (#borrow waker))))
           (#let-else (Pending pending) Poll first (#unreachable))
           (#let before u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
           (#let result u64
             (#match second
               (#case (Ready value) value)
               (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#u64.== result 42u64))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run(&source, 42);
    assert!(generated.contains("-body-frame"), "{generated}");
}

#[test]
fn async_function_resumes_a_child_await_in_a_while_condition() {
    let source = include_str!("../examples/async_fn_while_condition.lim");
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_while_condition_sequences_short_circuit_awaits() {
    let source = "(#enum BoolTask ((Waiting bool) (Resuming bool)))
      (#linear BoolTask)
      (#enum BoolPoll ((BoolPending BoolTask) (BoolReady bool)))
      (#fn bool-poll ((task BoolTask) (waker (#ref u64))) BoolPoll
        (#return (#match task
          (#case (Waiting value) (BoolPending (Resuming value)))
          (#case (Resuming value) (BoolReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iterations u64 0u64)
          (#while (#bool.&&
            (#await bool BoolTask BoolPending BoolReady bool-poll (Waiting true))
            (#await bool BoolTask BoolPending BoolReady bool-poll (Waiting true)))
            (#set iterations (#u64.+.wrap iterations 1u64))
            (#break))
          (#return iterations))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending after-first) Poll first (#unreachable))
        (#let second Poll (#call poll (: task after-first : waker (#borrow waker))))
        (#let-else (Pending after-second) Poll second (#unreachable))
        (#let third Poll (#call poll (: task after-second : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 1);
    assert!(generated.contains("choice-"), "{generated}");
}

#[test]
fn async_while_condition_keeps_global_names_out_of_frame_captures() {
    let source = "(#const fallback bool false)
      (#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while
            (#if (#bool.&&
                (#await bool ChildTask ChildPending ChildReady child-poll (Waiting 0u64))
                (#await bool ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))
              true
              fallback)
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-frame) Poll first (#unreachable))
        (#let second Poll (#call poll (: task first-frame : waker (#borrow waker))))
        (#let-else (Pending second-frame) Poll second (#unreachable))
        (#let third Poll (#call poll (: task second-frame : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
    let invalid_source = source
        .replace(
            "(#const fallback bool false)",
            "(#const unrelated bool false)",
        )
        .replace("              fallback)", "              missing_global)");
    let invalid_program = lim::parse_program(&invalid_source).unwrap();
    let error = match lim::CheckedProgram::validate(&invalid_program) {
        Ok(_) => panic!("an unresolved name in the generated async body must be rejected"),
        Err(error) => error,
    };
    assert!(
        format!("{error:?}").contains("unknown variable or enum variant"),
        "{error:?}"
    );
}

#[test]
fn awaited_while_condition_preserves_terminal_break_and_continue() {
    let source = "(#enum ConditionTask ((Waiting u64)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ConditionPending (Waiting 1u64))
              (ConditionReady true))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting iteration))
            (#set iteration (#u64.+.wrap iteration 1u64))
            (#match iteration
              (#case 2u64 (#break))
              (#case _ (#continue))))
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let result Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let value u64 (#match result
          (#case (Ready ready) ready)
          (#case (Pending pending-again) (#block (#forget pending-again) 0u64))))
        (#forget waker)
        (#return (#if (#u64.== value 2u64) 42u64 0u64)))";
    build_and_run(source, 42);
}

#[test]
fn awaited_while_condition_and_body_resume_in_source_order() {
    let source = "(#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady true)))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input u64)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll ConditionWaiting)
            (#let value u64
              (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting input)))
            (#assert (#u64.== value input))
            (#break))
          (#return input))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (: input 42u64)) : waker (#borrow waker))))
        (#let-else (Pending condition-pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (Pending body-pending) Poll second (#unreachable))
        (#let third Poll (#call poll (: task body-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("condition-body-task"), "{generated}");
    assert!(generated.contains("wait-condition"), "{generated}");
    assert!(generated.contains("wait-body"), "{generated}");

    let conditional_source = source.replace(
        "(#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting input))",
        "(#if true\n                (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting input))\n                42u64)",
    );
    let generated = build_and_run(&conditional_source, 42);
    assert!(generated.contains("choice"), "{generated}");

    let for_source = source
        .replace(
            "#while (#await ConditionTask",
            "#for () (#await ConditionTask",
        )
        .replace(
            "condition-poll ConditionWaiting)\n            (#let value",
            "condition-poll ConditionWaiting) ()\n            (#let value",
        );
    let generated = build_and_run(&for_source, 42);
    assert!(generated.contains("condition-body-task"), "{generated}");
}

#[test]
fn awaited_false_while_condition_does_not_poll_the_body_task() {
    let source = "(#enum ConditionTask (ConditionStart))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (ConditionReady false)))
      (#enum BodyTask (BodyStart))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#unreachable)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll ConditionStart)
            (#let value u64
              (#await u64 BodyTask BodyPending BodyReady body-poll BodyStart))
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value u64
          (#match result
            (#case (Ready ready) ready)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return value))";
    build_and_run(source, 42);

    let for_source = source
        .replace(
            "#while (#await ConditionTask",
            "#for () (#await ConditionTask",
        )
        .replace(
            "condition-poll ConditionStart)\n            (#let value",
            "condition-poll ConditionStart) ()\n            (#let value",
        );
    build_and_run(&for_source, 42);
}

#[test]
fn awaited_while_body_reports_noncopy_task_captures() {
    let source = "(#struct Resource ((value u64)))
      (#linear Resource)
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady true)))))
      (#enum BodyTask ((BodyWaiting Resource)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting resource) (BodyPending (BodyWaiting resource))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((resource Resource)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll ConditionWaiting)
            (#let value u64
              (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting resource)))
            (#break))
          (#return 42u64))))";
    let scratch = support::Scratch::new("async-while-noncopy-capture");
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("composed awaited while body captures non-Copy local 'resource'"),
        "{error:?}"
    );
}

#[test]
fn async_while_body_can_return_after_awaited_condition() {
    let source = "(#enum Child ((Waiting bool) (Resuming bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#await Child ChildPending ChildReady child-poll (Waiting decision))
            (#return 7u64))
          (#return 0u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-pending) Poll true-first (#unreachable))
        (#let true-second Poll (#call poll (: task true-pending : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-second (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-pending) Poll false-first (#unreachable))
        (#let false-second Poll (#call poll (: task false-pending : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    let generated = build_and_run(source, 7);
    assert!(
        generated.contains("(#if lim.async.work.choice-0"),
        "{generated}"
    );
}

#[test]
fn async_while_body_returns_after_a_composed_awaited_condition() {
    let source = "(#enum Child ((Waiting bool) (Resuming bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#enum TailTask ((TailWaiting u64) (TailResuming u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#if decision
                    (#await bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
            (#return 7u64))
          (#let fallback u64
            (#await u64 TailTask TailPending TailReady tail-poll (TailWaiting 3u64)))
          (#return fallback))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-pending) Poll true-first (#unreachable))
        (#let true-second Poll (#call poll (: task true-pending : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-second (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-pending) Poll false-first (#unreachable))
        (#let false-second Poll (#call poll (: task false-pending : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_fall_through_to_another_iteration() {
    let source = "(#enum Child ((Waiting bool) (Resuming bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#let-mut first bool true)
          (#while (#if decision
                    (#await bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
            (#if first
              (#block (#set first false) ())
              (#return 7u64)))
          (#let fallback u64 3u64)
          (#return fallback))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-pending) Poll true-first (#unreachable))
        (#let true-second Poll (#call poll (: task true-pending : waker (#borrow waker))))
        (#let-else (PollPending true-pending-again) Poll true-second (#unreachable))
        (#let true-third Poll (#call poll (: task true-pending-again : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-third (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-first (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_skip_a_direct_awaited_tail() {
    let source = "(#enum Child ((Waiting bool) (Resuming bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#enum TailTask ((TailWaiting u64) (TailResuming u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#let-mut first bool true)
          (#while (#if decision
                    (#await bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
          (#if first
              (#block (#set first false) ())
              (#return 7u64)))
          (#return (#await u64 TailTask TailPending TailReady tail-poll
            (TailWaiting 3u64))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-pending) Poll true-first (#unreachable))
        (#let true-second Poll (#call poll (: task true-pending : waker (#borrow waker))))
        (#let-else (PollPending true-pending-again) Poll true-second (#unreachable))
        (#let true-third Poll (#call poll (: task true-pending-again : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-third (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-pending) Poll false-first (#unreachable))
        (#let false-second Poll (#call poll (: task false-pending : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_suspend_post_loop_continuation() {
    let source = "(#enum Child ((Waiting bool) (Resuming bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady bool)))
      (#enum TailTask ((TailWaiting u64) (TailResuming u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#let-mut first bool true)
          (#while (#if decision
                    (#await bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
            (#if first
              (#block (#set first false) ())
              (#return 7u64)))
          (#let fallback u64
            (#await u64 TailTask TailPending TailReady tail-poll (TailWaiting 3u64)))
          (#return fallback))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-pending) Poll true-first (#unreachable))
        (#let true-second Poll (#call poll (: task true-pending : waker (#borrow waker))))
        (#let-else (PollPending true-pending-again) Poll true-second (#unreachable))
        (#let true-third Poll (#call poll (: task true-pending-again : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-third (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-pending) Poll false-first (#unreachable))
        (#let false-second Poll (#call poll (: task false-pending : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_early_return_can_skip_a_nested_awaited_tail() {
    let source = "(#enum ConditionTask ((Waiting bool) (Resuming bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#enum TailTask ((TailWaiting u64) (TailResuming u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady u64)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting decision) (ConditionPending (Resuming decision)))
          (#case (Resuming decision) (ConditionReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting decision))
            (#return 7u64))
          (#return (#u64.+.wrap
            (#await u64 TailTask TailPending TailReady tail-poll (TailWaiting 3u64))
            2u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-pending) Poll true-first (#unreachable))
        (#let true-second Poll (#call poll (: task true-pending : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-second (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-pending) Poll false-first (#unreachable))
        (#let false-second Poll (#call poll (: task false-pending : waker (#borrow waker))))
        (#let-else (PollPending false-tail-pending) Poll false-second (#unreachable))
        (#let false-third Poll (#call poll (: task false-tail-pending : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-third (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 12);
}

#[test]
fn async_while_early_return_can_skip_a_direct_awaited_tail() {
    let source = "(#enum ConditionTask ((Waiting bool) (Resuming bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#enum TailTask ((TailWaiting u64) (TailResuming u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady u64)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting decision) (ConditionPending (Resuming decision)))
          (#case (Resuming decision) (ConditionReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting decision))
            (#return 7u64))
          (#return (#await u64 TailTask TailPending TailReady tail-poll
            (TailWaiting 3u64))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-pending) Poll true-first (#unreachable))
        (#let true-second Poll (#call poll (: task true-pending : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-second (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-pending) Poll false-first (#unreachable))
        (#let false-second Poll (#call poll (: task false-pending : waker (#borrow waker))))
        (#let-else (PollPending false-tail-pending) Poll false-second (#unreachable))
        (#let false-third Poll (#call poll (: task false-tail-pending : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-third (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_body_can_return_after_body_await() {
    let source = "(#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let body-value u64
              (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting 13u64)))
            (#return body-value))
          (#return 5u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-after-condition) Poll true-first (#unreachable))
        (#let true-second Poll
          (#call poll (: task true-after-condition : waker (#borrow waker))))
        (#let-else (PollPending true-after-body-start) Poll true-second (#unreachable))
        (#let true-third Poll
          (#call poll (: task true-after-body-start : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-third (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-after-condition) Poll false-first (#unreachable))
        (#let false-second Poll
          (#call poll (: task false-after-condition : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    let generated = build_and_run(source, 18);
    assert!(generated.contains("choice"), "{generated}");

    let linear_source = source
        .replace(
            "(#enum ConditionTask",
            "(#struct Payload ((value u64)))\n      (#linear Payload)\n      (#enum ConditionTask",
        )
        .replace(
            "(#fn work ((decision bool)) u64",
            "(#fn work ((decision bool)) Payload",
        )
        .replace(
            "(#return body-value)",
            "(#return (#struct-literal Payload ((value body-value))))",
        )
        .replace(
            "(#return 5u64)",
            "(#return (#struct-literal Payload ((value 5u64))))",
        )
        .replace(
            "(#return (#u64.+.wrap true-result false-result))",
            "(#let true-value u64 (#get true-result value))\n\
             (#let false-value u64 (#get false-result value))\n\
             (#forget true-result)\n\
             (#forget false-result)\n\
             (#return (#u64.+.wrap true-value false-value))",
        );
    let generated = build_and_run(&linear_source, 18);
    assert!(
        generated.contains("expression-ready Payload"),
        "{generated}"
    );
}

#[test]
fn async_while_body_transfers_a_mutated_linear_capture_after_suspension() {
    let source = "(#import \"{}/library/tasks.lim\")
      (#struct Payload ((value u64)))
      (#linear Payload)
      (#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((#mut decision bool)) Payload
          (#let-mut payload Payload
            (#struct-literal Payload ((value 1u64))))
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let first u64
              (#await u64 BodyTask BodyPending BodyReady body-poll
                (BodyWaiting 1u64)))
            (#let second u64
            (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting first)))
            (#let replacement Payload
              (#struct-literal Payload ((value (#u64.+.wrap second 1u64)))))
            (#forget payload)
            (#set payload replacement)
            (#set decision false))
          (#return payload))))
      (#fn cancel-body-start ((task (#tuple bool Payload))) ()
        (#let (#tuple decision payload) (#tuple bool Payload) task)
        (#forget payload) (#return ()))
      (#fn cancel-body-await-0 ((task (#tuple bool Payload BodyTask))) ()
        (#let (#tuple decision payload child) (#tuple bool Payload BodyTask) task)
        (#forget payload) (#forget child) (#return ()))
      (#fn cancel-body-await-1 ((task (#tuple bool Payload BodyTask))) ()
        (#let (#tuple decision payload child) (#tuple bool Payload BodyTask) task)
        (#forget payload) (#forget child) (#return ()))
      (@task-cancel cancel-body lim.async.work.choice-0-body-frame
        ((lim.async.work.choice-0-body-frame-start cancel-body-start ((decision bool) (payload Payload)))
         (lim.async.work.choice-0-body-frame-await-0 cancel-body-await-0 ((decision bool) (payload Payload) (child BodyTask)))
         (lim.async.work.choice-0-body-frame-await-1 cancel-body-await-1 ((decision bool) (payload Payload) (child BodyTask)))))
      (#fn cancel-condition-wait ((task (#tuple ConditionTask bool Payload))) ()
        (#let (#tuple child decision payload) (#tuple ConditionTask bool Payload) task)
        (#forget child) (#forget payload) (#return ()))
      (#fn cancel-body-wait ((task (#tuple lim.async.work.choice-0-body-frame))) ()
        (#let (#tuple child) (#tuple lim.async.work.choice-0-body-frame) task)
        (#call cancel-body (: task child)) (#return ()))
      (@task-cancel cancel-condition-body lim.async.work.choice-2-condition-body-task
        ((lim.async.work.choice-2-wait-condition cancel-condition-wait ((child ConditionTask) (decision bool) (payload Payload)))
         (lim.async.work.choice-2-wait-body cancel-body-wait ((child lim.async.work.choice-0-body-frame)))))
      (#fn cancel-run-start ((task (#tuple bool Payload bool))) ()
        (#let (#tuple decision payload stopped) (#tuple bool Payload bool) task)
        (#forget payload) (#return ()))
      (#fn cancel-run-wait ((task (#tuple bool bool lim.async.work.choice-2-condition-body-task))) ()
        (#let (#tuple decision stopped child) (#tuple bool bool lim.async.work.choice-2-condition-body-task) task)
        (#call cancel-condition-body (: task child)) (#return ()))
      (@task-cancel cancel-run lim.async.work.choice-13-task
        ((lim.async.work.choice-13-start cancel-run-start ((decision bool) (payload Payload) (stopped bool)))
         (lim.async.work.choice-13-wait cancel-run-wait ((decision bool) (stopped bool) (child lim.async.work.choice-2-condition-body-task)))))
      (#fn cancel-frame-start ((task (#tuple bool))) ()
        (#let (#tuple decision) (#tuple bool) task) (#return ()))
      (#fn cancel-frame-await ((task (#tuple lim.async.work.choice-13-task))) ()
        (#let (#tuple child) (#tuple lim.async.work.choice-13-task) task)
        (#call cancel-run (: task child)) (#return ()))
      (@task-cancel cancel-frame Frame
        ((Frame-start cancel-frame-start ((decision bool)))
         (Frame-await-0 cancel-frame-await ((child lim.async.work.choice-13-task)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (: decision true)) : waker (#borrow waker))))
        (#let-else (Pending condition-pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (Pending first-body-pending) Poll second (#unreachable))
        (#let third Poll (#call poll (: task first-body-pending : waker (#borrow waker))))
        (#let-else (Pending second-body-pending) Poll third (#unreachable))
        (#let fourth Poll (#call poll (: task second-body-pending : waker (#borrow waker))))
        (#let-else (Pending final-condition-pending) Poll fourth (#unreachable))
        (#let fifth Poll (#call poll (: task final-condition-pending : waker (#borrow waker))))
        (#let-else (Ready payload) Poll fifth (#unreachable))
        (#let result u64 (#get payload value))
        (#forget payload)
        (#let cancel-first Poll
          (#call poll (: task (#call work (: decision true)) : waker (#borrow waker))))
        (#let-else (Pending cancel-pending-first) Poll cancel-first (#unreachable))
        (#let cancel-second Poll
          (#call poll (: task cancel-pending-first : waker (#borrow waker))))
        (#let-else (Pending cancel-pending-second) Poll cancel-second (#unreachable))
        (#call cancel-frame (: task cancel-pending-second))
        (#forget waker)
        (#return result))"
        .replace("{}", env!("CARGO_MANIFEST_DIR"));
    let generated = build_and_run(&source, 2);
    assert!(generated.contains("Payload"), "{generated}");
}

#[test]
fn async_suspending_while_body_can_return_after_setup() {
    let source = "(#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let setup u64 13u64)
            (#let value u64
              (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting setup)))
            (#return value))
          (#return 5u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-after-condition) Poll true-first (#unreachable))
        (#let true-second Poll
          (#call poll (: task true-after-condition : waker (#borrow waker))))
        (#let-else (PollPending true-after-body) Poll true-second (#unreachable))
        (#let true-third Poll
          (#call poll (: task true-after-body : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-third (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-after-condition) Poll false-first (#unreachable))
        (#let false-second Poll
          (#call poll (: task false-after-condition : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    let generated = build_and_run(source, 18);
    assert!(generated.contains("choice"), "{generated}");
}

#[test]
fn async_suspending_while_body_can_return_after_multiple_awaits() {
    let source = "(#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let setup u64 13u64)
            (#let first u64
              (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting setup)))
            (#let second u64
              (#await u64 BodyTask BodyPending BodyReady body-poll
                (BodyWaiting (#u64.+.wrap first 1u64))))
            (#return (#u64.+.wrap first second)))
          (#return 5u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let true-task Frame (#call work (: decision true)))
        (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
        (#let-else (PollPending true-after-condition) Poll true-first (#unreachable))
        (#let true-second Poll
          (#call poll (: task true-after-condition : waker (#borrow waker))))
        (#let-else (PollPending true-after-first) Poll true-second (#unreachable))
        (#let true-third Poll
          (#call poll (: task true-after-first : waker (#borrow waker))))
        (#let-else (PollPending true-after-second) Poll true-third (#unreachable))
        (#let true-fourth Poll
          (#call poll (: task true-after-second : waker (#borrow waker))))
        (#let-else (PollReady true-result) Poll true-fourth (#unreachable))
        (#let false-task Frame (#call work (: decision false)))
        (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-after-condition) Poll false-first (#unreachable))
        (#let false-second Poll
          (#call poll (: task false-after-condition : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    let generated = build_and_run(source, 32);
    assert!(
        generated.contains("expression-frame-await-1"),
        "{generated}"
    );
}

#[test]
fn async_suspending_while_body_return_reaches_enclosing_function() {
    let source = "(#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let first u64
              (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting 20u64)))
            (#let second u64
              (#await u64 BodyTask BodyPending BodyReady body-poll
                (BodyWaiting (#u64.+.wrap first 7u64))))
            (#return (#u64.+.wrap first second)))
          (#return 5u64))))
      (#fn run ((decision bool) (waker (#ref u64))) u64
        (#let task Frame (#call work (: decision decision)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#let-else (PollPending after-condition) Poll first (#unreachable))
        (#return (#if decision
          (#block
            (#let second Poll (#call poll (: task after-condition : waker waker)))
            (#let-else (PollPending after-first-body) Poll second (#unreachable))
            (#let third Poll (#call poll (: task after-first-body : waker waker)))
            (#let-else (PollPending after-second-body) Poll third (#unreachable))
            (#let fourth Poll (#call poll (: task after-second-body : waker waker)))
            (#let-else (PollReady result) Poll fourth (#unreachable))
            result)
          (#block
            (#let second Poll (#call poll (: task after-condition : waker waker)))
            (#let-else (PollReady result) Poll second (#unreachable))
            result))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let returned u64 (#call run (: decision true : waker (#borrow waker))))
        (#let skipped u64 (#call run (: decision false : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap returned skipped)))";
    build_and_run(source, 52);
}

#[test]
fn async_awaited_while_body_returns_from_both_if_branches() {
    let source = "(#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool) (pick bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#if pick (#return 13u64) (#return 17u64)))
          (#return 5u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first-task Frame (#call work (: decision true : pick true)))
        (#let first-poll Poll (#call poll (: task first-task : waker (#borrow waker))))
        (#let-else (PollPending first-pending) Poll first-poll (#unreachable))
        (#let first-ready Poll (#call poll (: task first-pending : waker (#borrow waker))))
        (#let-else (PollReady first-result) Poll first-ready (#unreachable))
        (#let second-task Frame (#call work (: decision true : pick false)))
        (#let second-poll Poll (#call poll (: task second-task : waker (#borrow waker))))
        (#let-else (PollPending second-pending) Poll second-poll (#unreachable))
        (#let second-ready Poll (#call poll (: task second-pending : waker (#borrow waker))))
        (#let-else (PollReady second-result) Poll second-ready (#unreachable))
        (#let false-task Frame (#call work (: decision false : pick true)))
        (#let false-poll Poll (#call poll (: task false-task : waker (#borrow waker))))
        (#let-else (PollPending false-pending) Poll false-poll (#unreachable))
        (#let false-ready Poll (#call poll (: task false-pending : waker (#borrow waker))))
        (#let-else (PollReady false-result) Poll false-ready (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap
          (#u64.+.wrap first-result second-result) false-result)))";
    build_and_run(source, 35);
}

#[test]
fn async_awaited_while_body_returns_from_match_arms() {
    let source = "(#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool) (pick bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#block
              (#let offset u64 1u64)
              (#match pick
                (#case true (#return (#u64.+.wrap 12u64 offset)))
                (#case false (#return (#u64.+.wrap 16u64 offset))))))
          (#return 5u64))))
      (#fn drive ((decision bool) (pick bool) (waker (#ref u64))) u64
        (#let task Frame (#call work (: decision decision : pick pick)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#let-else (PollPending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker waker)))
        (#return (#match second
          (#case (PollReady result) result)
          (#case (PollPending still-pending)
            (#block (#forget still-pending) 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first-result u64
          (#call drive (: decision true : pick true : waker (#borrow waker))))
        (#let second-result u64
          (#call drive (: decision true : pick false : waker (#borrow waker))))
        (#let false-result u64
          (#call drive (: decision false : pick true : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap
          (#u64.+.wrap first-result second-result) false-result)))";
    build_and_run(source, 35);
}

#[test]
fn async_awaited_while_return_branch_and_break_branch_diverge_correctly() {
    let source = "(#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((decision bool) (leave-body bool)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#block
              (#let return-value u64 13u64)
              (#if leave-body (#return return-value) (#break))))
          (#return 5u64))))
      (#fn drive ((decision bool) (leave-body bool) (waker (#ref u64))) u64
        (#let task Frame (#call work (: decision decision : leave-body leave-body)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#let-else (PollPending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker waker)))
        (#return (#match second
          (#case (PollReady result) result)
          (#case (PollPending still-pending)
            (#block (#forget still-pending) 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let returned u64
          (#call drive (: decision true : leave-body true : waker (#borrow waker))))
        (#let broken u64
          (#call drive (: decision true : leave-body false : waker (#borrow waker))))
        (#let condition-false u64
          (#call drive (: decision false : leave-body true : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap (#u64.+.wrap returned broken) condition-false)))";
    build_and_run(source, 23);
}

#[test]
fn async_awaited_while_return_branch_and_continue_branch_resume_correctly() {
    let source = "(#enum ConditionTask ((Waiting u64) (Resuming u64)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting iteration) (ConditionPending (Resuming iteration)))
          (#case (Resuming iteration)
            (ConditionReady (#u64.== iteration 0u64))))))
      (@async-fn (: names (Frame Poll PollPending PollReady poll) : waker u64 : function
        (#fn work ((should-return bool)) u64
          (#let-mut iteration u64 0u64)
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting iteration))
            (#if should-return
              (#return 13u64)
              (#block
                (#set iteration 1u64)
                (#continue))))
          (#return 5u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let return-task Frame (#call work (: should-return true)))
        (#let first Poll (#call poll (: task return-task : waker (#borrow waker))))
        (#let-else (PollPending after-return-first) Poll first (#unreachable))
        (#let return-ready Poll
          (#call poll (: task after-return-first : waker (#borrow waker))))
        (#let-else (PollReady returned) Poll return-ready (#unreachable))
        (#let continue-task Frame (#call work (: should-return false)))
        (#let continue-first Poll
          (#call poll (: task continue-task : waker (#borrow waker))))
        (#let-else (PollPending after-continue-first) Poll continue-first (#unreachable))
        (#let continue-second Poll
          (#call poll (: task after-continue-first : waker (#borrow waker))))
        (#let-else (PollPending after-continue-second) Poll continue-second (#unreachable))
        (#let continue-ready Poll
          (#call poll (: task after-continue-second : waker (#borrow waker))))
        (#let-else (PollReady continued) Poll continue-ready (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap returned continued)))";
    build_and_run(source, 18);

    let linear_source = source
        .replace(
            "(#enum ConditionTask",
            "(#struct Payload ((value u64)))\n      (#linear Payload)\n      (#enum ConditionTask",
        )
        .replace(
            "(#fn work ((should-return bool)) u64",
            "(#fn work ((should-return bool)) Payload",
        )
        .replace(
            "(#return 13u64)",
            "(#return (#struct-literal Payload ((value 13u64))))",
        )
        .replace(
            "(#return 5u64)",
            "(#return (#struct-literal Payload ((value 5u64))))",
        )
        .replace(
            "(#return (#u64.+.wrap returned continued))",
            "(#let returned-value u64 (#get returned value))\n\
             (#let continued-value u64 (#get continued value))\n\
             (#forget returned)\n\
             (#forget continued)\n\
             (#return (#u64.+.wrap returned-value continued-value))",
        );
    let generated = build_and_run(&linear_source, 18);
    assert!(
        generated.contains("#linear lim.async.work.choice"),
        "{generated}"
    );
}

#[test]
fn async_while_let_awaits_each_scrutinee_until_the_pattern_stops_matching() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ChildTask ((Waiting u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Maybe)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting stage)
            (#if (#u64.== stage 0u64)
              (ChildPending (Waiting 1u64))
              (#if (#u64.== stage 1u64)
                (ChildReady (Some 10u64))
                (ChildReady None)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#while-let (Some payload)
            (#await Maybe ChildTask ChildPending ChildReady child-poll
              (Waiting (#if (#u64.== iteration 0u64) 0u64 2u64)))
            (#set iteration payload))
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-frame) Poll first (#unreachable))
        (#let second Poll (#call poll (: task first-frame : waker (#borrow waker))))
        (#let value u64 (#match second
          (#case (Ready result) result)
          (#case (Pending pending-frame) (#block (#forget pending-frame) 0u64))))
        (#forget waker)
        (#return (#if (#u64.== value 10u64) 42u64 0u64)))";
    build_and_run(source, 42);
    let break_source = source.replace(
        "(#set iteration payload)",
        "(#block (#set iteration payload) (#break))",
    );
    build_and_run(&break_source, 42);
    let continue_source = source.replace(
        "(#set iteration payload)",
        "(#block (#set iteration payload) (#continue))",
    );
    build_and_run(&continue_source, 42);
}

#[test]
fn async_while_let_sequences_awaits_in_its_scrutinee_expression() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while-let true
            (#bool.&&
              (#await bool ChildTask ChildPending ChildReady child-poll (Waiting 42u64))
              (#await bool ChildTask ChildPending ChildReady child-poll (Waiting 42u64)))
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-frame) Poll first (#unreachable))
        (#let second Poll (#call poll (: task first-frame : waker (#borrow waker))))
        (#let-else (Pending second-frame) Poll second (#unreachable))
        (#let third Poll (#call poll (: task second-frame : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_for_condition_sequences_awaits_in_a_value_expression() {
    let source = "(#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for (#let-mut index u64 0u64)
            (#bool.&&
              (#u64.< index 1u64)
              (#bool.&&
                (#await bool ChildTask ChildPending ChildReady child-poll (Waiting index))
                (#await bool ChildTask ChildPending ChildReady child-poll (Waiting index))))
            (#set index (#u64.+.wrap index 1u64))
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-frame) Poll first (#unreachable))
        (#let second Poll (#call poll (: task first-frame : waker (#borrow waker))))
        (#let-else (Pending second-frame) Poll second (#unreachable))
        (#let third Poll (#call poll (: task second-frame : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_while_let_body_can_suspend_multiple_times_after_matching() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady (Some 42u64))))))
      (#enum BodyTask (BodyWaiting BodyResuming))
      (#linear BodyTask)
      (#fn start-body-task () BodyTask (#return BodyWaiting))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case BodyWaiting (BodyPending BodyResuming))
          (#case BodyResuming (BodyReady 7u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady
              condition-poll ConditionWaiting)
            (#let first u64
              (#await u64 BodyTask BodyPending BodyReady body-poll
                (#call start-body-task (:))))
            (#let second u64
              (#await u64 BodyTask BodyPending BodyReady body-poll
                (#call start-body-task (:))))
            (#assert (#u64.== first second))
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending condition-pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (Pending body-first-pending) Poll second (#unreachable))
        (#let third Poll
          (#call poll (: task body-first-pending : waker (#borrow waker))))
        (#let-else (Pending body-second-pending) Poll third (#unreachable))
        (#let fourth Poll
          (#call poll (: task body-second-pending : waker (#borrow waker))))
        (#let result u64
          (#match fourth
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
    assert!(generated.contains("body-poll-resume-1"), "{generated}");

    let linear_source = source.replace(
        "(#enum Maybe ((Some u64) None))",
        "(#enum Maybe ((Some u64) None))\n      (#linear Maybe)",
    );
    let generated = build_and_run(&linear_source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
}

#[test]
fn async_while_let_suspends_in_a_nested_body_statement() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ConditionTask (ConditionWaiting))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#forget task)
        (#return (ConditionReady (Some 42u64))))
      (#enum BodyTask (BodyWaiting BodyResuming))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case BodyWaiting (BodyPending BodyResuming))
          (#case BodyResuming (BodyReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady
              condition-poll ConditionWaiting)
            (#assert (#await bool BodyTask BodyPending BodyReady body-poll BodyWaiting))
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending-frame) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending-frame : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
}

#[test]
fn async_while_let_does_not_poll_the_unselected_scrutinee_branch() {
    let source = "(#enum Maybe (Some None))
      (#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Maybe)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#forget task)
        (#assert false)
        (#return (ChildReady None)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while-let Some
            (#if false
              (#await Maybe ChildTask ChildPending ChildReady child-poll Waiting)
              None)
            (#assert false))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let outcome Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result u64
          (#match outcome
            (#case (Ready value) 42u64)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("choice"), "{generated}");

    let pending_source = source
        .replace(
            "        (#forget task)\n        (#assert false)\n        (#return (ChildReady None))",
            "        (#return (#match task\n          (#case Waiting (ChildPending Resuming))\n          (#case Resuming (ChildReady None))))",
        )
        .replace("(#if false", "(#if true")
        .replace(
            "        (#let outcome Poll\n          (#call poll (: task (#call work (:)) : waker (#borrow waker))))",
            "        (#let first Poll\n          (#call poll (: task (#call work (:)) : waker (#borrow waker))))\n        (#let-else (Pending pending) Poll first (#unreachable))\n        (#let outcome Poll\n          (#call poll (: task pending : waker (#borrow waker))))",
        );
    build_and_run(&pending_source, 42);
}

#[test]
fn async_await_preserves_boolean_short_circuiting() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting (#ref CellU64))))
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
         (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
           (#return (#match task
             (#case (Waiting cell)
               (#block
                 (#call CellU64-set (: cell cell : value
                   (#u64.+.wrap (#call CellU64-get (: cell cell)) 1u64)))
                 (ChildReady true))))))
         (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work ((cell (#ref CellU64))) u64
             (#let ignored bool
               (#bool.&& false
                 (#await bool ChildTask ChildPending ChildReady child-poll (Waiting cell))))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker u64 0u64)
           (#let result Poll
             (#call poll (: task (#call work (: cell (#borrow cell))) : waker (#borrow waker))))
           (#let value u64 (#match result
             (#case (Ready ready) ready)
             (#case (Pending pending) (#block (#forget pending) 1u64))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#u64.== value 0u64) 42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    build_and_run(&source, 42);
    let or_source = source.replace("#bool.&& false", "#bool.|| true");
    build_and_run(&or_source, 42);
}

#[test]
fn async_await_preserves_match_guard_selection() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting (#ref CellU64))))
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
         (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
           (#return (#match task
             (#case (Waiting cell)
               (#block
                 (#call CellU64-set (: cell cell : value
                   (#u64.+.wrap (#call CellU64-get (: cell cell)) 1u64)))
                 (ChildReady true))))))
         (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work ((cell (#ref CellU64))) u64
             (#let ignored bool
               (#match true
                 (#case true (#when false)
                   (#await bool ChildTask ChildPending ChildReady child-poll (Waiting cell)))
                 (#case _ false)))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker u64 0u64)
           (#let result Poll
             (#call poll (: task (#call work (: cell (#borrow cell))) : waker (#borrow waker))))
           (#let value u64 (#match result
             (#case (Ready ready) ready)
             (#case (Pending pending) (#block (#forget pending) 1u64))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#u64.== value 0u64) 42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    build_and_run(&source, 42);
    let selected_source = source.replace("(#when false)", "(#when true)");
    build_and_run(&selected_source, 0);
}

#[test]
fn async_await_preserves_if_let_branch_selection() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum Maybe ((Some u64) None))
         (#enum ChildTask ((Waiting (#ref CellU64))))
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
         (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
           (#return (#match task
             (#case (Waiting cell)
               (#block
                 (#call CellU64-set (: cell cell : value
                   (#u64.+.wrap (#call CellU64-get (: cell cell)) 1u64)))
                 (ChildReady true))))))
         (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
           (#fn work ((maybe Maybe) (cell (#ref CellU64))) u64
             (#let ignored bool
               (#if-let (Some payload) maybe
                 (#await bool ChildTask ChildPending ChildReady child-poll (Waiting cell))
                 false))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker u64 0u64)
           (#let result Poll
             (#call poll (: task (#call work (: maybe None : cell (#borrow cell))) : waker (#borrow waker))))
           (#let value u64 (#match result
             (#case (Ready ready) ready)
             (#case (Pending pending) (#block (#forget pending) 1u64))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#u64.== value 0u64) 42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    build_and_run(&source, 42);
    let selected_source = source.replace(": maybe None", ": maybe (Some 7u64)");
    build_and_run(&selected_source, 0);
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
fn async_for_range_suspends_in_a_non_binding_body_statement() {
    let source = "(#enum BodyTask (Waiting Resuming))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case Waiting (BodyPending Resuming))
          (#case Resuming (BodyReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for-range (iteration u64) 0u64 2u64
            (#assert (#await bool BodyTask BodyPending BodyReady body-poll Waiting))
            (#if (#u64.== iteration 0u64)
              (#continue)
              (#break)))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task first-pending : waker (#borrow waker))))
        (#let-else (Pending second-pending) Poll second (#unreachable))
        (#let third Poll (#call poll (: task second-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
}

#[test]
fn async_for_range_awaits_bounds_in_source_order_before_iterating() {
    let source = "(#enum Child ((Waiting u64) (Resuming u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for-range (iteration u64)
            (#await u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
            (#await u64 Child ChildPending ChildReady child-poll (Waiting 2u64))
            (#assert (#u64.< iteration 3u64)))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task first-pending : waker (#borrow waker))))
        (#let-else (Pending second-pending) Poll second (#unreachable))
        (#let third Poll
          (#call poll (: task second-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(!generated.contains("(#await"), "{generated}");
}

#[test]
fn async_for_range_composes_awaited_bounds_with_awaited_body() {
    let source = "(#enum Child ((BoundWaiting u64) (BoundResuming u64) (Body u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (BoundWaiting value) (ChildPending (BoundResuming value)))
          (#case (BoundResuming value) (ChildReady value))
          (#case (Body value) (ChildReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for-range (iteration u64)
            (#await u64 Child ChildPending ChildReady child-poll (BoundWaiting 0u64))
            (#await u64 Child ChildPending ChildReady child-poll (BoundWaiting 2u64))
            (#let result u64
              (#await Child ChildPending ChildReady child-poll (Body iteration))))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task first-pending : waker (#borrow waker))))
        (#let-else (Pending second-pending) Poll second (#unreachable))
        (#let third Poll
          (#call poll (: task second-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("BoundWaiting"), "{generated}");
    assert!(generated.contains("Body"), "{generated}");
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
fn async_for_condition_can_await_and_step_only_after_ready_true() {
    let source = "(#enum ChildTask ((Waiting u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady (#u64.< value 2u64)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for (#set iteration 0u64)
                (#await ChildTask ChildPending ChildReady child-poll (Waiting iteration))
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#assert true))
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let value u64 (#match second
          (#case (Ready result) result)
          (#case (Pending pending-again) (#block (#forget pending-again) 0u64))))
        (#forget waker)
        (#return (#if (#u64.== value 2u64) 42u64 0u64)))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_for_condition_can_suspend_with_an_awaited_step() {
    let source = "(#enum ConditionTask ((Waiting u64) (Resuming u64)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting iteration) (ConditionPending (Resuming iteration)))
          (#case (Resuming iteration)
            (ConditionReady (#u64.< iteration 1u64))))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting iteration) (BodyPending (BodyResuming iteration)))
          (#case (BodyResuming iteration) (BodyReady true)))))
      (#enum StepTask ((StepWaiting u64 bool) (StepResuming u64 bool)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady u64)))
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case (StepWaiting iteration body-ran)
            (#block (#assert body-ran)
              (StepPending (StepResuming iteration body-ran))))
          (#case (StepResuming iteration body-ran)
            (#block (#assert body-ran)
              (StepReady (#u64.+.wrap iteration 1u64)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for (#set iteration 0u64)
                (#await ConditionTask ConditionPending ConditionReady
                  condition-poll (Waiting iteration))
                (#set iteration
                  (#await u64 StepTask StepPending StepReady step-poll
                    (StepWaiting iteration body-ran)))
            (#let body-ran bool true))
          (#return (#if (#u64.== iteration 1u64) 42u64 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending condition-pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (Pending step-pending) Poll second (#unreachable))
        (#let third Poll (#call poll (: task step-pending : waker (#borrow waker))))
        (#let-else (Pending resumed-condition) Poll third (#unreachable))
        (#let fourth Poll (#call poll (: task resumed-condition : waker (#borrow waker))))
        (#let result u64
          (#match fourth
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("condition-body-task"), "{generated}");

    let three_phase_source = source
        .replace(
            "(#let-mut iteration u64 0u64)",
            "(#let-mut iteration u64 0u64)\n          (#let-mut total u64 0u64)",
        )
        .replace(
            "(#let body-ran bool true)",
            "(#let body-ran bool\n              (#await bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#set total (#u64.+.wrap total 1u64))",
        )
        .replace(
            "(#return (#if (#u64.== iteration 1u64) 42u64 0u64))",
            "(#return (#if (#u64.== iteration 1u64)\n            (#if (#u64.== total 1u64) 42u64 0u64)\n            0u64))",
        );
    let (prefix, _) = three_phase_source.split_once("(#fn main () u64").unwrap();
    let three_phase_source = format!(
        "{prefix}(#fn main () u64
          (#let waker u64 0u64)
          (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
          (#let-else (Pending condition-pending) Poll first (#unreachable))
          (#let second Poll (#call poll (: task condition-pending : waker (#borrow waker))))
          (#let-else (Pending body-pending) Poll second (#unreachable))
          (#let third Poll (#call poll (: task body-pending : waker (#borrow waker))))
          (#let-else (Pending step-pending) Poll third (#unreachable))
          (#let fourth Poll (#call poll (: task step-pending : waker (#borrow waker))))
          (#let-else (Pending resumed-condition) Poll fourth (#unreachable))
          (#let fifth Poll (#call poll (: task resumed-condition : waker (#borrow waker))))
          (#let result u64
            (#match fifth
              (#case (Ready value) value)
              (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result))"
    );
    let generated = build_and_run(&three_phase_source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let shared_reference_source = three_phase_source
        .replace(
            "(#fn work () u64",
            "(#fn work ((view (#ref u64))) u64",
        )
        .replace(
            "(#set total (#u64.+.wrap total 1u64))",
            "(#assert (#u64.== (#deref view) 41u64))\n            (#set total (#u64.+.wrap total 1u64))",
        )
        .replace(
            "(#return (#if (#u64.== iteration 1u64)\n            (#if (#u64.== total 1u64) 42u64 0u64)\n            0u64))",
            "(#return (#if (#u64.== (#deref view) 41u64)\n            (#if (#u64.== iteration 1u64)\n              (#if (#u64.== total 1u64) 42u64 0u64)\n              0u64)\n            0u64))",
        );
    let (prefix, _) = shared_reference_source
        .split_once("(#fn main () u64")
        .unwrap();
    let shared_reference_source = format!(
        "{prefix}(#fn main () u64
          (#let-mut owner u64 41u64)
          (#let waker u64 0u64)
          (#let task Frame (#call work (: view (#borrow owner))))
          (#let first Poll (#call poll (: task task : waker (#borrow waker))))
          (#let-else (Pending condition-pending) Poll first (#unreachable))
          (#let second Poll (#call poll (: task condition-pending : waker (#borrow waker))))
          (#let-else (Pending body-pending) Poll second (#unreachable))
          (#let third Poll (#call poll (: task body-pending : waker (#borrow waker))))
          (#let-else (Pending step-pending) Poll third (#unreachable))
          (#let fourth Poll (#call poll (: task step-pending : waker (#borrow waker))))
          (#let-else (Pending resumed-condition) Poll fourth (#unreachable))
          (#let fifth Poll (#call poll (: task resumed-condition : waker (#borrow waker))))
          (#let result u64
            (#match fifth
              (#case (Ready value) value)
              (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#set owner 43u64)
          (#forget waker)
          (#return (#if (#u64.== result 42u64)
            (#if (#u64.== owner 43u64) 42u64 0u64) 0u64)))"
    );
    let generated = build_and_run(&shared_reference_source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let mutation_before_poll = shared_reference_source.replace(
        "(#let task Frame (#call work (: view (#borrow owner))))",
        "(#let task Frame (#call work (: view (#borrow owner))))\n          (#set owner 42u64)",
    );
    let error = lim::check_types(&lim::parse_program(&mutation_before_poll).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );

    let mutation_while_pending = shared_reference_source.replace(
        "(#let-else (Pending condition-pending) Poll first (#unreachable))",
        "(#let-else (Pending condition-pending) Poll first (#unreachable))\n          (#set owner 42u64)",
    );
    let error =
        lim::check_types(&lim::parse_program(&mutation_while_pending).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the external shared loan must remain live while the composed task is Pending: {error}"
    );

    let mutable_reference_source = shared_reference_source
        .replace(
            "(#fn work ((view (#ref u64)))",
            "(#fn work ((view (#ref-mut u64)))",
        )
        .replace(
            "(#assert (#u64.== (#deref view) 41u64))",
            "(#deref-set view 42u64)",
        )
        .replace(
            "(#u64.== (#deref view) 41u64)",
            "(#u64.== (#deref view) 42u64)",
        )
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    let generated = build_and_run(&mutable_reference_source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let multi_await_source = mutable_reference_source.replace(
        "(#let body-ran bool\n              (#await bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#deref-set view 42u64)\n            (#set total (#u64.+.wrap total 1u64))",
        "(#let body-ran bool\n              (#await bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#let second-body-ran bool\n              (#await bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#let third-body-ran bool\n              (#await bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#deref-set view 42u64)\n            (#set total (#u64.+.wrap total 1u64))",
    );
    let (prefix, _) = multi_await_source.split_once("(#fn main () u64").unwrap();
    let mut poll_chain = "(#block (#forget pending-7) 0u64)".to_owned();
    for index in (0..7).rev() {
        let task = if index == 0 {
            "(#call work (: view (#borrow-mut owner)))".to_owned()
        } else {
            format!("pending-{index}")
        };
        let next = index + 1;
        poll_chain = format!(
            "(#match (#call poll (: task {task} : waker (#borrow waker)))\n\
               (#case (Pending pending-{next}) {poll_chain})\n\
               (#case (Ready ready-{index}) ready-{index}))"
        );
    }
    let multi_await_source = format!(
        "{prefix}(#fn main () u64\n\
          (#let-mut owner u64 41u64)\n\
          (#let waker u64 0u64)\n\
          (#let result u64 {poll_chain})\n\
          (#set owner 43u64)\n\
          (#forget waker)\n\
          (#return (#if (#u64.== owner 43u64) result 0u64)))"
    );
    let generated = build_and_run(&multi_await_source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");
    let (prefix, _) = multi_await_source.split_once("(#fn main () u64").unwrap();
    let cancel_source = format!(
        "{prefix}(#fn main () u64
          (#let-mut owner u64 41u64)
          (#let waker u64 0u64)
          (#let task Frame (#call work (: view (#borrow-mut owner))))
          (#let first Poll (#call poll (: task task : waker (#borrow waker))))
          (#let-else (Pending condition-pending) Poll first (#unreachable))
          (#let second Poll
            (#call poll (: task condition-pending : waker (#borrow waker))))
          (#let-else (Pending pending) Poll second (#unreachable))
          (#forget pending)
          (#set owner 43u64)
          (#forget waker)
          (#return owner))"
    );
    build_and_run(&cancel_source, 43);
    let mutation_while_pending = cancel_source.replace(
        "          (#forget pending)",
        "          (#set owner 42u64)\n          (#forget pending)",
    );
    let error =
        lim::check_types(&lim::parse_program(&mutation_while_pending).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the multi-await body must retain the transferred exclusive loan while Pending: {error}"
    );

    let (prefix, _) = mutable_reference_source
        .split_once("(#fn main () u64")
        .unwrap();
    let cancelled_mutable_reference = format!(
        "{prefix}(#fn main () u64
          (#let-mut owner u64 41u64)
          (#let waker u64 0u64)
          (#let task Frame (#call work (: view (#borrow-mut owner))))
          (#let first Poll
            (#call poll (: task task : waker (#borrow waker))))
          (#let-else (Pending pending) Poll first (#unreachable))
          (#forget pending)
          (#set owner 42u64)
          (#forget waker)
          (#return (#if (#u64.== owner 42u64) 42u64 0u64)))"
    );
    let generated = build_and_run(&cancelled_mutable_reference, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let pinned_reference_source = shared_reference_source
        .replace("(view (#ref u64))", "(view (#pin-ref-mut u64))")
        .replace("(#borrow owner)", "(#pin-borrow-mut owner)");
    let generated = build_and_run(&pinned_reference_source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");
    let (prefix, _) = pinned_reference_source
        .split_once("(#fn main () u64")
        .unwrap();
    let cancelled_pinned_reference = format!(
        "{prefix}(#fn main () u64
          (#let-mut owner u64 41u64)
          (#let view (#pin-ref-mut u64) (#pin-borrow-mut owner))
          (#let waker u64 0u64)
          (#let task Frame (#call work (: view view)))
          (#let first Poll
            (#call poll (: task task : waker (#borrow waker))))
          (#let-else (Pending pending) Poll first (#unreachable))
          (#forget pending)
          (#set owner 42u64)
          (#forget waker)
          (#return (#if (#u64.== owner 42u64) 42u64 0u64)))"
    );
    let generated = build_and_run(&cancelled_pinned_reference, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let mutation_while_pending = mutable_reference_source.replace(
        "(#let-else (Pending condition-pending) Poll first (#unreachable))",
        "(#let-else (Pending condition-pending) Poll first (#unreachable))\n          (#set owner 42u64)",
    );
    let error =
        lim::check_types(&lim::parse_program(&mutation_while_pending).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the external exclusive loan must remain live while the composed task is Pending: {error}"
    );
}

#[test]
fn async_for_three_phase_transfers_preserve_continue_break_and_return() {
    let source = "(#enum ConditionTask ((Waiting u64) (Resuming u64)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting iteration) (ConditionPending (Resuming iteration)))
          (#case (Resuming iteration)
            (ConditionReady (#u64.< iteration 2u64))))))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting iteration) (BodyPending (BodyResuming iteration)))
          (#case (BodyResuming iteration) (BodyReady true)))))
      (#enum StepTask ((StepWaiting u64) (StepResuming u64)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady u64)))
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case (StepWaiting iteration)
            (#block (#assert (#u64.== iteration 0u64))
              (StepPending (StepResuming iteration))))
          (#case (StepResuming iteration)
            (#block (#assert (#u64.== iteration 0u64))
              (StepReady (#u64.+.wrap iteration 1u64)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for (#set iteration 0u64)
                (#await ConditionTask ConditionPending ConditionReady
                  condition-poll (Waiting iteration))
                (#set iteration
                  (#await u64 StepTask StepPending StepReady step-poll
                    (StepWaiting iteration)))
            (#let body-ran bool
              (#await bool BodyTask BodyPending BodyReady body-poll
                (BodyWaiting iteration)))
            (#if (#u64.== iteration 0u64) (#continue) (#break)))
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task first-pending : waker (#borrow waker))))
        (#let-else (Pending second-pending) Poll second (#unreachable))
        (#let third Poll (#call poll (: task second-pending : waker (#borrow waker))))
        (#let-else (Pending third-pending) Poll third (#unreachable))
        (#let fourth Poll (#call poll (: task third-pending : waker (#borrow waker))))
        (#let-else (Pending fourth-pending) Poll fourth (#unreachable))
        (#let fifth Poll (#call poll (: task fourth-pending : waker (#borrow waker))))
        (#let-else (Pending fifth-pending) Poll fifth (#unreachable))
        (#let sixth Poll (#call poll (: task fifth-pending : waker (#borrow waker))))
        (#let result u64
          (#match sixth
            (#case (Ready value) value)
            (#case (Pending sixth-pending)
              (#block
                (#let seventh Poll
                  (#call poll (: task sixth-pending : waker (#borrow waker))))
                (#match seventh
                  (#case (Ready value) value)
                  (#case (Pending unexpected)
                    (#block (#forget unexpected) 77u64)))))))
        (#forget waker)
        (#return (#if (#u64.== result 1u64) 42u64 0u64)))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let return_source = source
        .replace(
            "(#if (#u64.== iteration 0u64) (#continue) (#break))",
            "(#if true (#return 42u64) ())",
        )
        .replace("(#assert (#u64.== iteration 0u64))", "(#assert false)")
        .replace(
            "(#return iteration))))",
            "(#assert false) (#return iteration))))",
        );
    let (prefix, _) = return_source.split_once("(#fn main () u64").unwrap();
    let mut poll_chain = "(#block (#forget pending-8) 0u64)".to_owned();
    for index in (0..8).rev() {
        let task = if index == 0 {
            "(#call work (:))".to_owned()
        } else {
            format!("pending-{index}")
        };
        poll_chain = format!(
            "(#match (#call poll (: task {task} : waker (#borrow waker)))
              (#case (Pending pending-{next}) {poll_chain})
              (#case (Ready ready-{index}) ready-{index}))",
            next = index + 1,
        );
    }
    let return_source = format!(
        "{prefix}(#fn main () u64
          (#let waker u64 0u64)
          (#let result u64 {poll_chain})
          (#forget waker)
          (#return result))"
    );
    let generated = build_and_run(&return_source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let linear_prefix = prefix
        .replace(
            "(#enum ConditionTask",
            "(#struct Payload ((value u64)))\n      (#linear Payload)\n      (#enum ConditionTask",
        )
        .replace("(#fn work () u64", "(#fn work () Payload")
        .replace(
            "(#return 42u64)",
            "(#return (#struct-literal Payload ((value 42u64))))",
        )
        .replace(
            "(#return iteration))))",
            "(#return (#struct-literal Payload ((value iteration)))))))",
        );
    let mut linear_poll_chain = "(#block (#forget pending-8) 0u64)".to_owned();
    for index in (0..8).rev() {
        let task = if index == 0 {
            "(#call work (:))".to_owned()
        } else {
            format!("pending-{index}")
        };
        linear_poll_chain = format!(
            "(#match (#call poll (: task {task} : waker (#borrow waker)))
              (#case (Pending pending-{next}) {linear_poll_chain})
              (#case (Ready ready-{index})
                (#block
                  (#let result u64 (#get ready-{index} value))
                  (#forget ready-{index})
                  result)))",
            next = index + 1,
        );
    }
    let linear_return_source = format!(
        "{linear_prefix}(#fn main () u64
          (#let waker u64 0u64)
          (#let result u64 {linear_poll_chain})
          (#forget waker)
          (#return result))"
    );
    let generated = build_and_run(&linear_return_source, 42);
    assert!(generated.contains("#linear lim.async.work"), "{generated}");
}

#[test]
fn async_for_condition_awaits_only_the_selected_branch_each_iteration() {
    let source = "(#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut should-await bool true)
          (#for ()
                (#bool.&& should-await
                  (#await bool ChildTask ChildPending ChildReady child-poll
                    Waiting))
                (#set should-await false)
            (#assert true))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("choice"),
        "conditional await should use a concrete choice task: {generated}"
    );
}

#[test]
fn async_loop_short_circuit_conditions_do_not_poll_unselected_awaits() {
    let source = "(#enum ChildTask (Waiting))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#linear ChildPoll)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#forget task)
        (#assert false)
        (#return (ChildReady true)))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while
            (#bool.&& false
              (#await bool ChildTask ChildPending ChildReady child-poll Waiting))
            (#assert false))
          (#for ()
                (#bool.|| true
                  (#await bool ChildTask ChildPending ChildReady child-poll Waiting))
                ()
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let result Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value u64
          (#match result
            (#case (Ready ready) ready)
            (#case (Pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    build_and_run(source, 42);
}

#[test]
fn async_while_let_resumes_a_body_await_only_after_the_pattern_matches() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady (Some 42u64))))) )
      (#enum BodyTask (BodyWaiting BodyResuming))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case BodyWaiting (BodyPending BodyResuming))
          (#case BodyResuming (BodyReady 7u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady condition-poll ConditionWaiting)
            (#let result u64
              (#await u64 BodyTask BodyPending BodyReady body-poll BodyWaiting))
            (#assert (#u64.== payload 42u64))
            (#assert (#u64.== result 7u64))
            (#match payload
              (#case 42u64 (#break))
              (#case _ (#continue))))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending condition-pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (Pending body-pending) Poll second (#unreachable))
        (#let third Poll (#call poll (: task body-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("scrutinee-body-task"), "{generated}");

    let conditional_source = source.replace(
        "(#await u64 BodyTask BodyPending BodyReady body-poll BodyWaiting)",
        "(#if true\n                (#await u64 BodyTask BodyPending BodyReady body-poll BodyWaiting)\n                7u64)",
    );
    let generated = build_and_run(&conditional_source, 42);
    assert!(generated.contains("choice"), "{generated}");

    let (prefix, _) = source.split_once("      (#fn main () u64").unwrap();
    let unmatched_source = format!(
        "{}{}",
        prefix
            .replace("(ConditionReady (Some 42u64))", "(ConditionReady None)")
            .replace(
                "(#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll\n        (#return (#match task\n          (#case BodyWaiting (BodyPending BodyResuming))\n          (#case BodyResuming (BodyReady 7u64)))))",
                "(#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll\n        (#forget task)\n        (#return (BodyPending BodyWaiting)))",
            ),
        "      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending condition-pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task condition-pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))"
    );
    build_and_run(&unmatched_source, 42);
}

#[test]
fn async_while_let_carries_named_copy_aggregate_to_body_task() {
    let source = "(#struct Captures ((left u64) (right u64)))
      (#enum Maybe ((Some u64) None))
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady (Some 1u64))))) )
      (#enum BodyTask ((BodyWaiting Captures) (BodyResuming Captures)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting captures) (BodyPending (BodyResuming captures)))
          (#case (BodyResuming captures)
            (BodyReady (#u64.+.wrap
              (#get captures left) (#get captures right)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((captures Captures)) u64
          (#let-mut total u64 0u64)
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady condition-poll ConditionWaiting)
            (#let result u64
              (#await u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting captures)))
            (#set total (#u64.+.wrap payload result))
            (#break))
          (#return total))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let captures Captures
          (#struct-literal Captures ((left 20u64) (right 22u64))))
        (#let first Poll
          (#call poll (: task (#call work (: captures captures)) : waker (#borrow waker))))
        (#let-else (Pending condition-pending) Poll first (#unreachable))
        (#let second Poll (#call poll
          (: task condition-pending : waker (#borrow waker))))
        (#let-else (Pending body-pending) Poll second (#unreachable))
        (#let third Poll (#call poll (: task body-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 43);
    assert!(generated.contains("scrutinee-body-task"), "{generated}");

    let linear_source = source.replace(
        "(#struct Captures ((left u64) (right u64)))",
        "(#struct Captures ((left u64) (right u64))) (#linear Captures)",
    );
    let error = lim::parse_program(&linear_source).unwrap_err();
    assert!(
        error.contains("non-Copy local 'captures'"),
        "explicitly linear aggregates must not be treated as Copy captures: {error}"
    );
}

#[test]
fn async_while_condition_composes_multiple_body_awaits_in_a_child_frame() {
    let source = "(#struct Captures ((left u64) (right u64)))
      (#struct Counter ((value (#atomic u64))))
      (#linear Counter)
      (#fn counter-create () Counter
        (#return (#struct-literal Counter ((value (#atomic-init u64 1u64))))))
      (#fn counter-get ((counter (#ref Counter))) u64
        (#return (#atomic-load (#borrow (#get counter value)) #memory-relaxed)))
      (#fn counter-clear ((counter (#ref Counter))) ()
        (#atomic-store (#borrow (#get counter value)) 0u64 #memory-relaxed)
        (#return ()))
      (#enum ChildTask ((Waiting u64) (Resuming u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#enum ConditionTask ((ConditionWaiting (#ref Counter))))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting counter)
            (#if (#u64.== (#call counter-get (: counter counter)) 0u64)
              (ConditionReady false)
              (#block
                (#call counter-clear (: counter counter))
                (ConditionReady true)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((counter (#ref Counter)) (captures Captures) (view (#ref u64)) (#mut total u64)) u64
          (#while (#await ConditionTask ConditionPending ConditionReady condition-poll
                    (ConditionWaiting counter))
            (#let-mut subtotal u64 0u64)
            (#let-mut inner-iterations u64 0u64)
            (#while (#u64.== inner-iterations 0u64)
              (#set inner-iterations 1u64)
              (#break))
            (#let first u64
              (#await ChildTask ChildPending ChildReady child-poll
                (Waiting (#u64.+.wrap (#get captures left) (#deref view)))))
            (#let second u64
              (#await ChildTask ChildPending ChildReady child-poll
                (Waiting (#u64.+.wrap (#get captures right) (#deref view)))))
            (#set subtotal (#u64.+.wrap first second))
            (#set total (#u64.+.wrap total subtotal)))
          (#return (#u64.+.wrap
            (#u64.+.wrap total (#get captures left))
            (#u64.+.wrap (#get captures right) (#deref view)))))))
      (#fn main () u64
        (#let counter Counter (#call counter-create (:)))
        (#let captures Captures
          (#struct-literal Captures ((left 20u64) (right 22u64))))
        (#let-mut view-owner u64 1u64)
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work
            (: counter (#borrow counter) : captures captures : view (#borrow view-owner) : total 0u64))
            : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let-else (Pending pending-again) Poll second (#unreachable))
        (#let third Poll (#call poll (: task pending-again : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending task) (#block (#forget task) 0u64))))
        (#forget counter)
        (#set view-owner 0u64)
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 87);
    assert!(generated.contains("body-function"), "{generated}");
    assert!(generated.contains("body-poll-resume"), "{generated}");

    let linear_capture_source = source.replace(
        "(#struct Captures ((left u64) (right u64)))",
        "(#struct Captures ((left u64) (right u64))) (#linear Captures)",
    );
    let error = lim::parse_program(&linear_capture_source).unwrap_err();
    assert!(
        error.contains("non-Copy local 'captures'"),
        "linear aggregate captures must retain their ownership diagnostic: {error}"
    );

    let pending_mutation = source.replace(
        "(#let-else (Pending pending) Poll first (#unreachable))",
        "(#let-else (Pending pending) Poll first (#unreachable))\n        (#set view-owner 9u64)",
    );
    let program = lim::parse_program(&pending_mutation).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the nested async body must retain the external borrow while Pending: {error}"
    );

    let continue_source = source.replace(
        "(#set total (#u64.+.wrap total subtotal)))",
        "(#set total (#u64.+.wrap total subtotal))\n            (#continue))",
    );
    build_and_run(&continue_source, 87);

    let break_source = source.replace(
        "(#set total (#u64.+.wrap total subtotal)))",
        "(#set total (#u64.+.wrap total subtotal))\n            (#break))",
    );
    build_and_run(&break_source, 87);

    let branch_continue_source = source.replace(
        "(#set total (#u64.+.wrap total subtotal)))",
        "(#set total (#u64.+.wrap total subtotal))\n            (#if (#u64.== first 21u64) (#continue) (#break)))",
    );
    build_and_run(&branch_continue_source, 87);

    let branch_break_source = source.replace(
        "(#set total (#u64.+.wrap total subtotal)))",
        "(#set total (#u64.+.wrap total subtotal))\n            (#if (#u64.== first 21u64) (#break) (#continue)))",
    );
    build_and_run(&branch_break_source, 87);

    let match_continue_source = source.replace(
        "(#set total (#u64.+.wrap total subtotal)))",
        "(#set total (#u64.+.wrap total subtotal))\n            (#match first (#case 21u64 (#continue)) (#case _ (#break))))",
    );
    build_and_run(&match_continue_source, 87);

    let conditional_await_source = source.replace(
        "(#await ChildTask ChildPending ChildReady child-poll\n                (Waiting (#get captures right)))",
        "(#if true\n                (#await u64 ChildTask ChildPending ChildReady child-poll\n                  (Waiting (#get captures right)))\n                0u64)",
    );
    build_and_run(&conditional_await_source, 87);
}

#[test]
fn async_while_condition_awaits_only_the_selected_branch_each_iteration() {
    let source = "(#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut should-await bool true)
          (#while
            (#bool.&& should-await
              (#await bool ChildTask ChildPending ChildReady child-poll Waiting))
            (#set should-await false))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(&source, 42);
    assert!(generated.contains("choice"), "{generated}");
}

#[test]
fn async_while_body_binding_awaits_only_the_selected_branch() {
    let source = "(#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut keep-going bool true)
          (#while keep-going
            (#let result bool
              (#if keep-going
                (#await bool ChildTask ChildPending ChildReady child-poll Waiting)
                false))
            (#set keep-going false)
            (#assert result))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("choice"), "{generated}");
}

#[test]
fn async_loop_sequences_two_awaits_in_one_iteration() {
    let source = "(#enum SecondTask ((SecondWaiting u64) (SecondResuming u64)))
      (#linear SecondTask)
      (#enum SecondPoll ((SecondPending SecondTask) (SecondReady u64)))
      (#fn second-poll ((task SecondTask) (waker (#ref u64))) SecondPoll
        (#return (#match task
          (#case (SecondWaiting value) (SecondPending (SecondResuming value)))
          (#case (SecondResuming value) (SecondReady (#u64.+.wrap value 2u64))))))
      (#enum FirstTask (FirstWaiting FirstResuming))
      (#linear FirstTask)
      (#enum FirstPoll ((FirstPending FirstTask) (FirstReady u64)))
      (#fn first-poll ((task FirstTask) (waker (#ref u64))) FirstPoll
        (#return (#match task
          (#case FirstWaiting (FirstPending FirstResuming))
          (#case FirstResuming (FirstReady 40u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut keep-going bool true)
          (#while keep-going
            (#let next-value u64
              (#await FirstTask FirstPending FirstReady first-poll FirstWaiting))
            (#assert (#u64.== next-value 40u64))
            (#let result u64
              (#await SecondTask SecondPending SecondReady second-poll (SecondWaiting next-value)))
            (#set keep-going false)
            (#assert (#u64.== result 42u64)))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task first-pending : waker (#borrow waker))))
        (#let-else (Pending second-pending) Poll second (#unreachable))
        (#let third Poll
          (#call poll (: task second-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("sequence-task"), "{generated}");
    assert!(generated.contains("wait-first"), "{generated}");
    assert!(generated.contains("wait-second"), "{generated}");
}

#[test]
fn async_loop_sequences_three_adjacent_awaits_in_one_iteration() {
    let source = "(#enum ThirdTask (ThirdWaiting ThirdResuming))
      (#linear ThirdTask)
      (#enum ThirdPoll ((ThirdPending ThirdTask) (ThirdReady u64)))
      (#fn third-poll ((task ThirdTask) (waker (#ref u64))) ThirdPoll
        (#return (#match task
          (#case ThirdWaiting (ThirdPending ThirdResuming))
          (#case ThirdResuming (ThirdReady 42u64)))))
      (#enum SecondTask (SecondWaiting SecondResuming))
      (#linear SecondTask)
      (#enum SecondPoll ((SecondPending SecondTask) (SecondReady ThirdTask)))
      (#fn second-poll ((task SecondTask) (waker (#ref u64))) SecondPoll
        (#return (#match task
          (#case SecondWaiting (SecondPending SecondResuming))
          (#case SecondResuming (SecondReady ThirdWaiting)))))
      (#enum FirstTask (FirstWaiting FirstResuming))
      (#linear FirstTask)
      (#enum FirstPoll ((FirstPending FirstTask) (FirstReady SecondTask)))
      (#fn first-poll ((task FirstTask) (waker (#ref u64))) FirstPoll
        (#return (#match task
          (#case FirstWaiting (FirstPending FirstResuming))
          (#case FirstResuming (FirstReady SecondWaiting)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut keep-going bool true)
          (#while keep-going
            (#let second-task SecondTask
              (#await FirstTask FirstPending FirstReady first-poll FirstWaiting))
            (#let third-task ThirdTask
              (#await SecondTask SecondPending SecondReady second-poll second-task))
            (#let result u64
              (#await ThirdTask ThirdPending ThirdReady third-poll third-task))
            (#set keep-going false)
            (#assert (#u64.== result 42u64)))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task first-pending : waker (#borrow waker))))
        (#let-else (Pending second-pending) Poll second (#unreachable))
        (#let third Poll
          (#call poll (: task second-pending : waker (#borrow waker))))
        (#let-else (Pending third-pending) Poll third (#unreachable))
        (#let fourth Poll
          (#call poll (: task third-pending : waker (#borrow waker))))
        (#let result u64
          (#match fourth
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
}

#[test]
fn async_for_initializer_awaits_once_before_entering_the_loop() {
    let source = "(#enum InitTask ((Waiting u64) (Resuming u64)))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady u64)))
      (#fn init-poll ((task InitTask) (waker (#ref u64))) InitPoll
        (#return (#match task
          (#case (Waiting count)
            (InitPending (Resuming count)))
          (#case (Resuming count)
            (InitReady (#u64.+.wrap count 2u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut total u64 0u64)
          (#for (#let-mut iteration u64
                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))
                (#u64.< iteration 3u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#set total (#u64.+.wrap total iteration)))
          (#return (#if (#u64.== total 2u64) 42u64 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("InitPending"), "{generated}");

    let conditional_initializer = source
        .replace(
            "(#let-mut iteration u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
            "(#let-mut iteration u64\n                  (#if false\n                    (#await u64 InitTask InitPending InitReady init-poll (Waiting 0u64))\n                    2u64))",
        )
        .replace(
            "(#let-else (Pending pending) Poll first (#unreachable))\n        (#let second Poll\n          (#call poll (: task pending : waker (#borrow waker))))\n        (#let result u64\n          (#match second\n            (#case (Ready value) value)\n            (#case (Pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
            "(#let result u64\n          (#match first\n            (#case (Ready value) value)\n            (#case (Pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
    );
    assert_ne!(conditional_initializer, source);
    let generated = build_and_run(&conditional_initializer, 42);
    assert!(generated.contains("(#fn poll"), "{generated}");

    let nested_initializer = source.replace(
        "(#let-mut iteration u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
        "(#let-mut iteration u64\n                  (#u64.+.wrap 0u64 (#await u64 InitTask InitPending InitReady init-poll (Waiting 0u64))))",
    );
    let generated = build_and_run(&nested_initializer, 42);
    assert!(generated.contains("InitPending"), "{generated}");

    let multiple_nested_initializers = source
        .replace("(#u64.< iteration 3u64)", "(#u64.< iteration 5u64)")
        .replace("(#u64.== total 2u64)", "(#u64.== total 4u64)")
        .replace(
            "(#let-mut iteration u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
            "(#let-mut iteration u64\n                  (#u64.+.wrap\n                    (#await u64 InitTask InitPending InitReady init-poll (Waiting 0u64))\n                    (#await u64 InitTask InitPending InitReady init-poll (Waiting 0u64))))",
        )
        .replace(
            "(#let result u64\n          (#match second\n            (#case (Ready value) value)\n            (#case (Pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
            "(#let-else (Pending second-pending) Poll second (#unreachable))\n        (#let third Poll\n          (#call poll (: task second-pending : waker (#borrow waker))))\n        (#let result u64\n          (#match third\n            (#case (Ready value) value)\n            (#case (Pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
        );
    assert_ne!(multiple_nested_initializers, source);
    let generated = build_and_run(&multiple_nested_initializers, 42);
    assert!(generated.contains("InitPending"), "{generated}");

    let initializer_then_body_await = source
        .replace(
            "(#case (Waiting count)\n            (InitPending (Resuming count)))",
            "(#case (Waiting count)\n            (#if (#u64.== count 0u64)\n              (InitPending (Resuming count))\n              (InitReady count)))",
        )
        .replace(
            "(#set total (#u64.+.wrap total iteration))",
            "(#let body-value u64\n              (#await InitTask InitPending InitReady init-poll (Waiting iteration)))\n            (#set total (#u64.+.wrap total body-value))",
        );
    let generated = build_and_run(&initializer_then_body_await, 42);
    assert!(generated.contains("InitPending"), "{generated}");

    let initializer_then_condition_await = source
        .replace(
            "      (@async-fn",
            "      (#enum ConditionTask ((ConditionStart u64) (ConditionResume u64)))\n      (#linear ConditionTask)\n      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))\n      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll\n        (#return (#match task\n          (#case (ConditionStart iteration) (ConditionPending (ConditionResume iteration)))\n          (#case (ConditionResume iteration)\n            (ConditionReady (#u64.< iteration 3u64))))))\n      (@async-fn",
        )
        .replace(
            "                (#u64.< iteration 3u64)\n                (#set iteration",
            "                (#await ConditionTask ConditionPending ConditionReady condition-poll (ConditionStart iteration))\n                (#set iteration",
        )
        .replace("          (#let-mut total u64 0u64)\n", "")
        .replace("            (#set total (#u64.+.wrap total iteration))", "            (#assert true)")
        .replace(
            "(#return (#if (#u64.== total 2u64) 42u64 0u64))",
            "(#return 42u64)",
        )
        .replace(
            "(#let second Poll\n          (#call poll (: task pending : waker (#borrow waker))))\n        (#let result u64\n          (#match second",
            "(#let second Poll\n          (#call poll (: task pending : waker (#borrow waker))))\n        (#let-else (Pending condition-pending) Poll second (#unreachable))\n        (#let third Poll\n          (#call poll (: task condition-pending : waker (#borrow waker))))\n        (#let-else (Pending resumed-condition-pending) Poll third (#unreachable))\n        (#let fourth Poll\n          (#call poll (: task resumed-condition-pending : waker (#borrow waker))))\n        (#let result u64\n          (#match fourth",
        );
    assert_ne!(initializer_then_condition_await, source);
    let generated = build_and_run(&initializer_then_condition_await, 42);
    assert!(generated.contains("ConditionPending"), "{generated}");

    let unsupported = source.replace(
        "(#let-mut iteration u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
        "(#let-mut iteration u64\n                  (#u64.+.wrap 1u64 (#await InitTask InitPending InitReady init-poll (Waiting 0u64))))",
    );
    let error = match lim::parse_program(&unsupported) {
        Err(error) => error,
        Ok(program) => lim::check_types(&program).unwrap_err(),
    };
    assert!(
        error.contains("nested #await requires an explicit result type"),
        "nested initializer suspension should be diagnosed explicitly: {error}"
    );

    let task_initializer = "(#enum OuterTask ((Waiting u64) (Resuming u64)))
      (#linear OuterTask)
      (#enum OuterPoll ((OuterPending OuterTask) (OuterReady u64)))
      (#fn outer-poll ((task OuterTask) (waker (#ref u64))) OuterPoll
        (#return (#match task
          (#case (Waiting value) (OuterPending (Resuming value)))
          (#case (Resuming value) (OuterReady value)))))
      (#enum InnerTask (MakeOuter))
      (#enum InnerPoll ((InnerPending InnerTask) (InnerReady OuterTask)))
      (#fn inner-poll ((task InnerTask) (waker (#ref u64))) InnerPoll
        (#return (#match task
          (#case MakeOuter (InnerReady (Waiting 42u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for (#let-mut initial u64
                  (#await OuterTask OuterPending OuterReady outer-poll
                    (#await OuterTask InnerTask InnerPending InnerReady inner-poll MakeOuter)))
                false
                ()
            (#assert false))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(task_initializer, 42);
    assert!(!generated.contains("(#await"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_suspends_before_entering_the_loop() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum InitTask (Waiting Resuming))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref u64))) InitPoll
        (#return (#match task
          (#case Waiting (InitPending Resuming))
          (#case Resuming (InitReady (Some 0u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#for (#let-else (Some index) Maybe
                  (#await InitTask InitPending InitReady init-poll Waiting)
                  (#unreachable))
                (#u64.< index 1u64)
                (#u64.+.wrap index 1u64)
            (#assert (#u64.== index 0u64))
            (#break))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("InitPending"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_composes_with_a_suspending_body() {
    let source = "(#enum Maybe ((Some u64) None))
      (#type MaybeAlias Maybe)
      (#enum InitTask (Waiting Resuming))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref u64))) InitPoll
        (#return (#match task
          (#case Waiting (InitPending Resuming))
          (#case Resuming (InitReady (Some 9u64))))))
      (#struct Resource ((value u64)))
      (#linear Resource)
      (#fn Resource-destroy ((resource Resource)) u64
        (#let result u64 (#get resource value))
        (#forget resource)
        (#return result))
      (#enum BodyTask ((BodyWaiting u64) (BodyResuming u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady Resource)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value)
            (#block (#forget value)
              (BodyReady (#struct-literal Resource ((value 9u64)))))))))
      (#enum SecondBodyTask (SecondBodyWaiting SecondBodyResuming))
      (#linear SecondBodyTask)
      (#enum SecondBodyPoll ((SecondBodyPending SecondBodyTask) (SecondBodyReady u64)))
      (#fn second-body-poll ((task SecondBodyTask) (waker (#ref u64))) SecondBodyPoll
        (#return (#match task
          (#case SecondBodyWaiting (SecondBodyPending SecondBodyResuming))
          (#case SecondBodyResuming (SecondBodyReady 9u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut done bool false)
          (#for (#let-else (Some index) MaybeAlias
                  (#await InitTask InitPending InitReady init-poll Waiting)
                  (#unreachable))
                (#bool.== done false)
                ()
            (#let value Resource
              (#await BodyTask BodyPending BodyReady body-poll (BodyWaiting index)))
            (#let second-value u64
              (#await SecondBodyTask SecondBodyPending SecondBodyReady
                second-body-poll SecondBodyWaiting))
            (#assert (#u64.== second-value 9u64))
            (#let destroyed u64 (#call Resource-destroy (: resource value)))
            (#assert (#u64.== destroyed second-value))
            (#set done true))
          (#return 42u64))))
      (#fn cancel-empty ((task ())) () (#return ()))
      (#fn cancel-initializer-state ((task (#tuple bool InitTask))) ()
        (#let (#tuple done child) (#tuple bool InitTask) task)
        (#forget child)
        (#return ()))
      (#fn cancel-body-task ((task BodyTask)) ()
        (#forget task)
        (#return ()))
      (#fn cancel-second-body-task ((task SecondBodyTask)) ()
        (#forget task)
        (#return ()))
      (#fn cancel-sequence-task ((task lim.async.work.choice-2-sequence-task)) ()
        (#return (#match task
          (#case (lim.async.work.choice-2-wait-first child)
            (#call cancel-body-task (: task child)))
          (#case (lim.async.work.choice-2-wait-second resource child)
            (#block
              (#let destroyed u64 (#call Resource-destroy (: resource resource)))
              (#assert (#u64.== destroyed 9u64))
              (#call cancel-second-body-task (: task child))
              (#return ()))))))
      (#fn cancel-loop-task ((task lim.async.work.choice-4-task)) ()
        (#return (#match task
          (#case (lim.async.work.choice-4-start done index) ())
          (#case (lim.async.work.choice-4-wait done index child)
            (#call cancel-sequence-task (: task child))))))
      (@task-cancel cancel-frame Frame
        ((Frame-start cancel-empty ())
         (Frame-await-0 cancel-initializer-state ((done bool) (child InitTask)))
         (Frame-await-1 cancel-loop-task)))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (:)))
        (#let first Poll (#call poll (: task task : waker (#borrow waker))))
        (#let-else (Pending after-init) Poll first (#unreachable))
        (#let second Poll (#call poll (: task after-init : waker (#borrow waker))))
        (#let-else (Pending after-body) Poll second (#unreachable))
        (#let third Poll (#call poll (: task after-body : waker (#borrow waker))))
        (#let-else (Pending after-second-body) Poll third (#unreachable))
        (#let fourth Poll (#call poll (: task after-second-body : waker (#borrow waker))))
        (#let result u64
          (#match fourth
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#let cancel-task Frame (#call work (:)))
        (#let cancel-first Poll (#call poll (: task cancel-task : waker (#borrow waker))))
        (#let-else (Pending cancel-after-init) Poll cancel-first (#unreachable))
        (#let cancel-second Poll
          (#call poll (: task cancel-after-init : waker (#borrow waker))))
        (#let-else (Pending cancel-after-body) Poll cancel-second (#unreachable))
        (#let cancel-third Poll
          (#call poll (: task cancel-after-body : waker (#borrow waker))))
        (#let-else (Pending cancel-after-second-body) Poll cancel-third (#unreachable))
        (#call cancel-frame (: task cancel-after-second-body))
        (#forget waker)
        (#return result))";
    let source = format!(
        "(#import \"{}/library/tasks.lim\")\n{source}",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run(&source, 42);
    assert!(generated.contains("BodyPending"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_composes_with_an_awaited_step() {
    let source = "(#enum Maybe ((Some u64) None))
      (#type MaybeAlias Maybe)
      (#enum InitTask (InitWaiting InitResuming))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref u64))) InitPoll
        (#return (#match task
          (#case InitWaiting (InitPending InitResuming))
          (#case InitResuming (InitReady (Some 9u64))))))
      (#enum StepTask (StepWaiting StepResuming))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady bool)))
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case StepWaiting (StepPending StepResuming))
          (#case StepResuming (StepReady true)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut done bool false)
          (#for (#let-else (Some index) MaybeAlias
                  (#await InitTask InitPending InitReady init-poll InitWaiting)
                  (#unreachable))
                (#bool.== done false)
                (#set done
                  (#await bool StepTask StepPending StepReady step-poll StepWaiting))
            (#assert (#u64.== index 9u64)))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let task Frame (#call work (:)))
        (#let first Poll (#call poll (: task task : waker (#borrow waker))))
        (#let-else (Pending after-init) Poll first (#unreachable))
        (#let second Poll (#call poll (: task after-init : waker (#borrow waker))))
        (#let-else (Pending after-step) Poll second (#unreachable))
        (#let third Poll (#call poll (: task after-step : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPending"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_returns_ready_on_mismatch() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum InitTask ((Waiting Maybe) (Resuming Maybe)))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref u64))) InitPoll
        (#return (#match task
          (#case (Waiting value) (InitPending (Resuming value)))
          (#case (Resuming value) (InitReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe)) u64
          (#for (#let-else (Some index) Maybe
                  (#await InitTask InitPending InitReady init-poll (Waiting input))
                  (#return 7u64))
                false
                ()
            ())
          (#return 35u64))))
      (#fn poll-work ((input Maybe) (waker (#ref u64))) u64
        (#let task Frame (#call work (: input input)))
        (#let first Poll (#call poll (: task task : waker waker)))
        (#return (#match first
          (#case (Ready value) value)
          (#case (Pending pending) (#block
            (#let second Poll (#call poll (: task pending : waker waker)))
            (#match second
              (#case (Ready value) value)
              (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let mismatch u64 (#call poll-work (: input None : waker (#borrow waker))))
        (#let matched u64 (#call poll-work (: input (Some 7u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap mismatch matched)))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(#return (Ready (#literal u64 7)))"),
        "{generated}"
    );
}

#[test]
fn async_for_let_else_initializer_can_suspend_in_condition() {
    let source = "(#enum Maybe ((Some u64) None))
      (#enum InitTask ((Waiting Maybe) (Resuming Maybe)))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref u64))) InitPoll
        (#return (#match task
          (#case (Waiting value) (InitPending (Resuming value)))
          (#case (Resuming value) (InitReady value)))))
      (#enum ConditionTask ((ConditionWaiting bool) (ConditionResuming bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting value) (ConditionPending (ConditionResuming value)))
          (#case (ConditionResuming value) (ConditionReady value)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((input Maybe) (condition bool)) u64
          (#let-mut body-ran bool false)
          (#for (#let-else (Some index) Maybe
                  (#await InitTask InitPending InitReady init-poll (Waiting input))
                  (#return 7u64))
                (#await ConditionTask ConditionPending ConditionReady
                  condition-poll (ConditionWaiting condition))
                ()
            (#set body-ran true)
            (#break))
          (#return (#if body-ran 43u64 42u64)))))";
    let source = format!(
        "{source}
        (#fn main () u64
          (#let waker u64 0u64)
          (#let mismatch-task Frame (#call work (: input None : condition false)))
          (#let mismatch-first Poll (#call poll (: task mismatch-task : waker (#borrow waker))))
          (#let-else (Pending mismatch-after-init) Poll mismatch-first (#unreachable))
          (#let mismatch-second Poll
            (#call poll (: task mismatch-after-init : waker (#borrow waker))))
          (#let-else (Ready mismatch) Poll mismatch-second (#unreachable))
          (#let false-task Frame (#call work (: input (Some 7u64) : condition false)))
          (#let false-first Poll (#call poll (: task false-task : waker (#borrow waker))))
          (#let-else (Pending false-after-init) Poll false-first (#unreachable))
          (#let false-second Poll
            (#call poll (: task false-after-init : waker (#borrow waker))))
          (#let-else (Pending false-after-condition-start) Poll false-second (#unreachable))
          (#let false-third Poll
            (#call poll (: task false-after-condition-start : waker (#borrow waker))))
          (#let-else (Ready matched-false) Poll false-third (#unreachable))
          (#let true-task Frame (#call work (: input (Some 7u64) : condition true)))
          (#let true-first Poll (#call poll (: task true-task : waker (#borrow waker))))
          (#let-else (Pending true-after-init) Poll true-first (#unreachable))
          (#let true-second Poll
            (#call poll (: task true-after-init : waker (#borrow waker))))
          (#let-else (Pending true-after-condition-start) Poll true-second (#unreachable))
          (#let true-third Poll
            (#call poll (: task true-after-condition-start : waker (#borrow waker))))
          (#let-else (Ready matched-true) Poll true-third (#unreachable))
          (#forget waker)
          (#return (#u64.+.wrap mismatch
            (#u64.+.wrap matched-false matched-true))))"
    );
    let generated = build_and_run(&source, 92);
    assert!(generated.contains("ConditionPending"), "{generated}");
}

#[test]
fn async_for_condition_and_step_await_preserve_body_continue_and_break() {
    let source = "(#enum ConditionTask ((ConditionWaiting u64) (ConditionResuming u64)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting iteration)
            (ConditionPending (ConditionResuming iteration)))
          (#case (ConditionResuming iteration) (ConditionReady true)))))
      (#enum StepTask ((StepWaiting u64) (StepResuming u64)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady u64)))
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case (StepWaiting iteration)
            (StepPending (StepResuming iteration)))
          (#case (StepResuming iteration)
            (StepReady (#u64.+.wrap iteration 1u64))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for ()
            (#await ConditionTask ConditionPending ConditionReady
              condition-poll (ConditionWaiting iteration))
            (#set iteration
              (#await u64 StepTask StepPending StepReady step-poll
                (StepWaiting iteration)))
            (#if (#u64.== iteration 0u64) (#continue) (#break)))
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending-1) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending-1 : waker (#borrow waker))))
        (#let-else (Pending pending-2) Poll second (#unreachable))
        (#let third Poll (#call poll (: task pending-2 : waker (#borrow waker))))
        (#let-else (Pending pending-3) Poll third (#unreachable))
        (#let fourth Poll (#call poll (: task pending-3 : waker (#borrow waker))))
        (#let result u64
          (#match fourth
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 1);
    assert!(generated.contains("step-choice-skip"), "{generated}");
    assert!(generated.contains("step-choice-run"), "{generated}");

    let (prefix, _) = source
        .split_once("(#fn main () u64")
        .expect("async main function");
    let return_prefix = prefix.replace(
        "(#if (#u64.== iteration 0u64) (#continue) (#break))",
        "(#return 42u64)",
    );
    let return_source = format!(
        "{return_prefix}
        (#fn main () u64
          (#let waker u64 0u64)
          (#let first Poll
            (#call poll (: task (#call work (:)) : waker (#borrow waker))))
          (#let-else (Pending pending) Poll first (#unreachable))
          (#let second Poll
            (#call poll (: task pending : waker (#borrow waker))))
          (#let result u64
            (#match second
              (#case (Ready value) value)
              (#case (Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result))"
    );
    let returned = build_and_run(&return_source, 42);
    assert!(returned.contains("iteration-function"), "{returned}");
}

#[test]
fn async_for_step_can_suspend_after_the_loop_body() {
    let source = "(#enum StepTask ((Waiting u64) (Resuming u64)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady u64)))
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case (Waiting iteration)
            (#block
              (#assert (#u64.== (#u64.%.wrap iteration 2u64) 1u64))
              (#if (#u64.== iteration 1u64)
                (StepPending (Resuming iteration))
                (StepReady (#u64.+.wrap iteration 1u64)))))
          (#case (Resuming iteration)
            (#block
              (#assert (#u64.== (#u64.%.wrap iteration 2u64) 1u64))
              (StepReady (#u64.+.wrap iteration 1u64)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for (#set iteration 0u64)
                (#u64.< iteration 6u64)
                (#set iteration
                  (#await StepTask StepPending StepReady step-poll
                    (Waiting iteration)))
            (#set iteration (#u64.+.wrap iteration 1u64)))
          (#return (#if (#u64.== iteration 6u64) 42u64 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPending"), "{generated}");
}

#[test]
fn async_for_step_can_suspend_after_a_suspending_body() {
    let source = "(#enum BodyTask ((Waiting u64) (Resuming u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref u64))) BodyPoll
        (#return (#match task
          (#case (Waiting value) (BodyPending (Resuming value)))
          (#case (Resuming value) (BodyReady value)))))
      (#enum StepTask (Start Resume))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady u64)))
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case Start (StepPending Resume))
          (#case Resume (StepReady 1u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for (#set iteration 0u64)
                (#u64.< iteration 1u64)
            (#set iteration
                  (#await StepTask StepPending StepReady step-poll Start))
            (#let body-value u64
              (#await BodyTask BodyPending BodyReady body-poll (Waiting 42u64)))
            (#assert (#u64.== body-value 42u64)))
          (#return (#if (#u64.== iteration 1u64) 42u64 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending body-pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task body-pending : waker (#borrow waker))))
        (#let-else (Pending step-pending) Poll second (#unreachable))
        (#let third Poll
          (#call poll (: task step-pending : waker (#borrow waker))))
        (#let result u64
          (#match third
            (#case (Ready value) value)
            (#case (Pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("sequence-task"), "{generated}");
}

#[test]
fn async_for_step_can_suspend_inside_assignment_expression() {
    let source = "(#enum StepTask (Waiting Resuming))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady u64)))
      (#fn step-poll ((task StepTask) (waker (#ref u64))) StepPoll
        (#return (#match task
          (#case Waiting (StepPending Resuming))
          (#case Resuming (StepReady 1u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for ()
                (#u64.< iteration 1u64)
                (#set iteration
                  (#u64.+.wrap iteration
                    (#await u64 StepTask StepPending StepReady step-poll Waiting)))
            (#assert true))
          (#return (#if (#u64.== iteration 1u64) 42u64 0u64)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task pending : waker (#borrow waker))))
        (#let result u64
          (#match second
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPending"), "{generated}");
}

#[test]
fn awaited_for_condition_runs_step_after_continue_but_not_break() {
    let source = "(#enum ChildTask ((Waiting u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady (#u64.< value 3u64)))))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut iteration u64 0u64)
          (#for (#set iteration 0u64)
                (#await ChildTask ChildPending ChildReady child-poll (Waiting iteration))
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#match iteration
              (#case 0u64 (#continue))
              (#case 1u64 ())
              (#case _ (#break))))
          (#return iteration))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending pending) Poll first (#unreachable))
        (#let second Poll (#call poll (: task pending : waker (#borrow waker))))
        (#let value u64 (#match second
          (#case (Ready result) result)
          (#case (Pending pending-again) (#block (#forget pending-again) 0u64))))
        (#forget waker)
        (#return (#if (#u64.== value 2u64) 42u64 0u64)))";
    build_and_run(source, 42);
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
      (#enum Decision (Stop Continue))
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
            (#let decision Decision
              (#if (#u64.== iteration 2u64) (Stop) (Continue)))
            (#match decision
              (#case Stop (#break))
              (#case Continue (#continue))))
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
fn async_loop_body_supports_more_than_two_suspensions() {
    let source = "(#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady u64)))
      (#fn child-poll ((task ChildTask) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady 2u64)))))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work () u64
          (#let-mut total u64 0u64)
          (#loop
            (#let first u64
              (#await u64 ChildTask ChildPending ChildReady child-poll Waiting))
            (#let second u64
              (#await u64 ChildTask ChildPending ChildReady child-poll Waiting))
            (#let third u64
              (#await u64 ChildTask ChildPending ChildReady child-poll Waiting))
            (#set total
              (#u64.+.wrap total
                (#u64.+.wrap first (#u64.+.wrap second third))))
            (#break))
          (#assert (#u64.== total 6u64))
          (#return 42u64))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let first Poll
          (#call poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (Pending first-task) Poll first (#unreachable))
        (#let second Poll
          (#call poll (: task first-task : waker (#borrow waker))))
        (#let-else (Pending second-task) Poll second (#unreachable))
        (#let third Poll
          (#call poll (: task second-task : waker (#borrow waker))))
        (#let-else (Pending third-task) Poll third (#unreachable))
        (#let fourth Poll
          (#call poll (: task third-task : waker (#borrow waker))))
        (#let result u64
          (#match fourth
            (#case (Ready value) value)
            (#case (Pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-poll-resume-2"), "{generated}");
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
        "(#return (#u64.+.wrap total offset))",
        "(#let second u64
           (#await Step StepPending StepReady step-poll (Waiting 1u64)))
         (#return (#u64.+.wrap total offset))",
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

#[test]
fn generated_async_frames_support_exhaustive_task_cancellation() {
    let source = "(#import \"{}/library/tasks.lim\")
      (#enum Child ((Waiting u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady u64)))
      (#fn child-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (#fn child-cancel ((task Child)) () (#forget task) (#return ()))
      (@async-fn (: names (Frame Poll Pending Ready poll) : waker u64 : function
        (#fn work ((offset u64)) u64
          (#let value u64
            (#await Child ChildPending ChildReady child-poll (Waiting 2u64)))
          (#return (#u64.+.wrap value offset)))))
      (#fn cancel-offset ((task u64)) () (#forget task) (#return ()))
      (#fn cancel-await-state ((task (#tuple u64 Child))) ()
        (#let (#tuple offset child) (#tuple u64 Child) task)
        (#call cancel-offset (: task offset))
        (#call child-cancel (: task child))
        (#return ()))
      (@task-cancel cancel-frame Frame
        ((Frame-start cancel-offset)
         (Frame-await-0 cancel-await-state ((offset u64) (child Child)))))
      (#fn main () u64
        (#let waker u64 0u64)
        (#let frame Frame (#call work (: offset 40u64)))
        (#let first Poll (#call poll (: task frame : waker (#borrow waker))))
        (#let-else (Pending pending-frame) Poll first (#unreachable))
        (#call cancel-frame (: task pending-frame))
        (#forget waker)
        (#return 42u64))";
    let source = source.replace("{}", env!("CARGO_MANIFEST_DIR"));
    build_and_run(&source, 42);
}
