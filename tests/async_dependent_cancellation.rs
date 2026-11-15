mod support;

use std::{process::Command, time::Duration};

fn source() -> &'static str {
    "#struct Owner (#linear) ((amount #u64))
#enum Child (#linear) ((Child.Holding (#tuple (#ref Owner) #u64)))
#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Holding (#tuple view count))
            (#if (#u64::eq count 0u64) (ChildPoll.Pending (Child.Holding (#tuple view 1u64)))
              (ChildPoll.Ready (#u64::add-wrap (#get view amount) 2u64))))))
  );
}
#fn cancel-child {
  #params = ((value Child));
  #returns = ();
  #body = (
          (#match value (#case (Child.Holding (#tuple view count))
            (#block (#assert (#u64::eq (#get view amount) 40u64))
              (#drop view) (#forget count) ())))
          (#return ())
  );
}
#fn destroy-owner {
  #params = ((value Owner));
  #returns = ();
  #body = (
          (#assert (#u64::eq (#get value amount) 40u64))
          (#forget value) (#return ())
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child))))
          (function (#fn work () #u64
            (#let owner Owner (#struct-literal Owner ((amount 40u64))))
            (#let answer #u64 (#await Child ChildPoll.Pending ChildPoll.Ready child-poll
              (Child.Holding (#tuple (#borrow owner) 0u64))))
            (#forget owner) (#return answer))))
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
          (#assert (#variant-is (#borrow (#get cleanup await-0)) Work::Frame::Cleanup::Await-0.Empty))
          (#call work-cancel ((task cleanup)))
          (#call Work::Poll::destroy ((task (#pin-borrow-mut task))))
          (#forget task) (#return 42u64)\n  );\n}\n"
}

#[test]
fn dependent_child_is_destroyed_before_exporting_its_owner() {
    run(source(), "async-dependent-cancellation");
}

#[test]
fn cancellation_selects_only_the_child_live_at_the_current_await() {
    let program = source()
        .replace("(await-0 cancel-child)", "(await-0 cancel-child) (await-1 cancel-second)")
        .replace("(#drop view) (#forget count)",
            "(#assert (#u64::eq count 1u64)) (#drop view) (#forget count)")
        .replace("(#forget owner) (#return answer)",
            "(#let second-answer #u64 (#await Child ChildPoll.Pending ChildPoll.Ready second-poll\n            (Child.Holding (#tuple (#borrow owner) 0u64))))\n          (#forget second-answer) (#forget owner) (#return answer)")
        .replace("(#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task pending))))",
            "(#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))\n        (#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))\n        (#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task second-pending))))")
        + "\n#fn second-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
              (#return (#match task (#case (Child.Holding (#tuple second-view second-count))
                (#block (#forget second-count) (ChildPoll.Pending (Child.Holding (#tuple second-view 5u64)))))))
  );
}
#fn cancel-second {
  #params = ((value Child));
  #returns = ();
  #body = (
              (#match value (#case (Child.Holding (#tuple second-view second-count))
                (#block (#assert (#u64::eq (#get second-view amount) 40u64))
                  (#assert (#u64::eq second-count 5u64))
                  (#drop second-view) (#forget second-count) ())))
              (#return ())\n  );\n}\n";
    assert!(program.contains("task second-pending"));
    run(&program, "async-dependent-two-await-cancellation");
}

#[test]
fn runtime_array_child_is_cancelled_before_destroying_its_selected_owner() {
    let program = source()
        .replace("#fn destroy-owner {\n  #params = ((value Owner));",
            "#fn destroy-owner {\n  #params = ((value (#array Owner 2)));")
        .replace("(#assert (#u64::eq (#get value amount) 40u64))",
            "(#assert (#u64::eq (#get (#index value 0usize) amount) 10u64))\n        (#assert (#u64::eq (#get (#index value 1usize) amount) 40u64))")
        .replace("(#let owner Owner (#struct-literal Owner ((amount 40u64))))",
            "(#let owner (#array Owner 2) (#array-of (#array Owner 2)\n            (#struct-literal Owner ((amount 10u64))) (#struct-literal Owner ((amount 40u64)))))\n          (#let-mut index #usize 1usize)")
        .replace("(Child.Holding (#tuple (#borrow owner) 0u64))",
            "(#block (#let selected (#ref Owner) (#borrow (#index owner index)))\n              (#set index 0usize) (Child.Holding (#tuple selected 0u64)))");
    assert!(program.contains("(#index owner index)"));
    run(&program, "async-runtime-array-dependent-cancellation");
}

#[test]
fn suspended_for_step_cancels_child_before_its_body_owner() {
    let original = "(#let owner Owner (#struct-literal Owner ((amount 40u64))))
            (#let answer #u64 (#await Child ChildPoll.Pending ChildPoll.Ready child-poll
              (Child.Holding (#tuple (#borrow owner) 0u64))))
            (#forget owner) (#return answer)";
    let program = source().replace(
        original,
        "(#let-mut total #u64 0u64)
          (#for (#let-mut iteration #u64 0u64) (#u64::lt iteration 1u64)
            (#block
              (#let answer #u64 (#await Child ChildPoll.Pending ChildPoll.Ready child-poll
                (Child.Holding (#tuple (#borrow owner) 0u64))))
              (#set total answer) (#forget owner) (#set iteration 1u64))
            (#let owner Owner (#struct-literal Owner ((amount 40u64)))))
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
        .replace("(#assert (#u64::eq (#get value amount) 40u64))",
            "(#assert (#u64::eq (#get value amount) 41u64))");
    assert!(program.contains("(#assert (#u64::eq (#get value amount) 41u64))"));
    run(&program, "async-exclusive-dependent-cancellation");
}

#[test]
fn dependent_child_cancellation_preserves_selected_internal_and_external_owners() {
    for choose in ["true", "false"] {
        let program = source()
            .replace("(#fn work () #u64", "(#fn work ((external (#ref Owner)) (choose #bool)) #u64")
            .replace("(#let answer #u64 (#await Child ChildPoll.Pending ChildPoll.Ready child-poll\n              (Child.Holding (#tuple (#borrow owner) 0u64))))",
                "(#let view (#ref Owner) (#if choose (#borrow owner) external))\n          (#let answer #u64 (#await Child ChildPoll.Pending ChildPoll.Ready child-poll (Child.Holding (#tuple view 0u64))))\n          (#drop view)")
            .replace("(#let waker #u64 0u64)", "(#let outside Owner (#struct-literal Owner ((amount 40u64))))\n        (#let waker #u64 0u64)")
            .replace("(#call work ())", &format!("(#call work ((external (#borrow outside)) (choose {choose})))"))
            .replace("(#forget task) (#return 42u64)", "(#forget task) (#forget outside) (#return 42u64)");
        assert!(program.contains("(#let view (#ref Owner)"));
        run(&program, "async-mixed-dependent-cancellation");
    }
}

#[test]
fn pinned_child_cancellation_preserves_selected_internal_and_external_owners() {
    for choose in ["true", "false"] {
        let program = pinned_source()
            .replace("(#fn parent () #u64", "(#fn parent ((external (#ref Owner)) (choose #bool)) #u64")
            .replace("(#let-mut nested Child::Frame (#call child ((view (#borrow owner)))))",
                "(#let view (#ref Owner) (#if choose (#borrow owner) external))\n          (#let-mut nested Child::Frame (#call child ((view view))))\n          (#drop view)")
            .replace("(#let waker #u64 0u64)", "(#let outside Owner (#struct-literal Owner ((amount 40u64))))\n        (#let waker #u64 0u64)")
            .replace("(#call parent ())", &format!("(#call parent ((external (#borrow outside)) (choose {choose})))"))
            .replace("(#forget task) (#return 42u64)", "(#forget task) (#forget outside) (#return 42u64)");
        assert!(program.contains("(#let view (#ref Owner)"));
        run(&program, "async-mixed-pinned-dependent-cancellation");
    }
}

#[test]
fn cancellation_before_first_poll_and_after_ready_is_idempotent() {
    let prefix = source().split("#fn main").next().unwrap();
    let program = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut unstarted Work::Frame (#call work ()))
          (#call Work::Poll::destroy ((task (#pin-borrow-mut unstarted))))
          (#call Work::Poll::destroy ((task (#pin-borrow-mut unstarted))))
          (#forget unstarted)
          (#let-mut task Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll
            ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready answer) Work::Poll second (#unreachable))
          (#call Work::Poll::destroy ((task (#pin-borrow-mut task))))
          (#call Work::Poll::destroy ((task (#pin-borrow-mut task))))
          (#forget task) (#return answer)\n  );\n}}\n"
    );
    run(&program, "async-dependent-terminal-cancellation");
}

fn pinned_source() -> &'static str {
    "#struct Owner (#linear) ((amount #u64))
#enum Step (#linear) ((Step.Start #u64))
#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task (#case (Step.Start count)
            (#if (#u64::eq count 0u64) (StepPoll.StepPending (Step.Start 1u64)) (StepPoll.StepReady count)))))
  );
}
#fn cancel-step {
  #params = ((value Step));
  #returns = ();
  #body = ( (#forget value) (#return ())
  );
}
#fn destroy-owner {
  #params = ((value Owner));
  #returns = ();
  #body = (
          (#assert (#u64::eq (#get value amount) 40u64)) (#forget value) (#return ())
  );
}
#generate #async-fn-pinned ((protocol ChildAwait) (waker #u64)
          (cancel (child-cancel ((await-0 cancel-step))))
          (function (#fn child ((view (#ref Owner))) #u64
            (#let result #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start 0u64)))
            (#return (#u64::add-wrap (#get view amount) result)))))
#generate #async-fn-pinned ((protocol ParentAwait) (waker #u64)
          (cancel (parent-cancel ((owner destroy-owner) (nested Child::Poll::destroy))))
          (function (#fn parent () #u64
            (#let owner Owner (#struct-literal Owner ((amount 40u64))))
            (#let-mut nested Child::Frame (#call child ((view (#borrow owner)))))
            (#let answer #u64 (#await ChildAwait (#pin-borrow-mut nested)))
            (#forget nested) (#forget owner) (#return answer))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut task Parent::Frame (#call parent ()))
          (#let first Parent::Poll (#call Parent::poll
            ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
          (#let-else (Parent::Poll.Pending pending) Parent::Poll first (#unreachable))
          (#call Parent::Poll::destroy ((task pending)))
          (#call Parent::Poll::destroy ((task (#pin-borrow-mut task))))
          (#forget task) (#return 42u64)\n  );\n}\n"
}

#[test]
fn pinned_generated_child_is_cancelled_without_moving_its_frame() {
    run(pinned_source(), "async-dependent-pinned-child");
}

#[test]
fn generated_word_destroy_names_cannot_collide_with_source_functions() {
    let program = format!(
        "{}\n#fn Child::Poll::destroy-words {{\n  #params = ();\n  #returns = ();\n  #body = ( (#return ())\n  );\n}}\n",
        pinned_source()
    );
    let scratch = support::Scratch::new("async-word-destroy-name-collision");
    let error = lim::compile_source_to_assembly(
        &program,
        &scratch.path().join("input.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("Child::Poll::destroy-words") && error.message.contains("conflicts"),
        "{error:?}"
    );
    assert!(!scratch.path().join("generated").exists());
}

#[test]
fn metadata_discard_does_not_allow_forgetting_a_live_childs_owner() {
    let program = pinned_source().replace(
        "(#let answer #u64 (#await ChildAwait (#pin-borrow-mut nested)))",
        "(#forget owner) (#let answer #u64 (#await ChildAwait (#pin-borrow-mut nested)))",
    );
    let scratch = support::Scratch::new("async-word-owner-live-child-rejection");
    let error = lim::compile_source_to_assembly(
        &program,
        &scratch.path().join("input.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        matches!(
            error.code,
            lim::DiagnosticCode::Borrow | lim::DiagnosticCode::Linear
        ),
        "{error:?}"
    );
    assert!(!scratch.path().join("generated").exists());
}

#[test]
fn reference_free_pinned_child_cancels_in_word_storage_exactly_once() {
    // The child function is literal #generate AST data, not an authored declaration.
    let program = pinned_source()
        .replace("(#fn child ((view (#ref Owner)))", "(#fn child ((amount #u64))")
        .replace("(#get view amount)", "amount")
        .replace("#call child ((view (#borrow owner)))", "#call child ((amount (#get owner amount)))")
        .replace("#fn cancel-step {\n  #params = ((value Step));\n  #returns = ();\n  #body = ( (#forget value) (#return ())\n  );\n}",
            "#fn cancel-step {\n  #params = ((value Step));\n  #returns = ();\n  #body = ( (#let byte #u8 67u8) (#assert (#i64::eq (#unsafe (#linux-syscall #i64 1usize (1i64 (#borrow byte) 1usize))) 1i64)) (#forget value) (#return ())\n  );\n}");
    run_with_output(&program, "async-pinned-word-child-cancellation", b"C");
    let heap = heap_pinned_source(&program);
    run_with_output(&heap, "async-pinned-word-heap-child-cancellation", b"C");
}

#[test]
fn reference_free_pinned_child_rejects_moving_cancellation_handlers() {
    let program = pinned_source()
        .replace(
            "(#fn child ((view (#ref Owner)))",
            "(#fn child ((amount #u64))",
        )
        .replace("(#get view amount)", "amount")
        .replace(
            "#call child ((view (#borrow owner)))",
            "#call child ((amount (#get owner amount)))",
        )
        .replace("(nested Child::Poll::destroy)", "(nested discard-child)")
        + "\n#fn discard-child {\n  #params = ((value Child::Frame));\n  #returns = ();\n  #body = ( (#forget value) (#return ())\n  );\n}\n";
    let scratch = support::Scratch::new("async-word-child-moving-cancel");
    let error = lim::compile_source_to_assembly(
        &program,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("pinned mutable reference"),
        "{error:?}"
    );
    assert!(
        !scratch.path().join("generated").exists(),
        "no partially checked child is published"
    );
}

fn heap_pinned_source(source: &str) -> String {
    source
        .replace("(#call Parent::Poll::destroy ((task pending)))",
            "(#call Parent::Poll::destroy ((task pending))) (#forget pending)")
        .replace("(#let-mut task Parent::Frame (#call parent ()))",
            "(#let pointer (#ptr-mut Parent::Frame) (#unsafe (#linux-syscall (#ptr-mut Parent::Frame)\n          9usize (0usize (#size-of Parent::Frame) 3usize 34usize -1i64 0usize))))\n        (#let initial Parent::Frame (#call parent ()))\n        (#let-mut task (#pin-own Parent::Frame) (#unsafe (#pin-own-of pointer initial)))")
        .replace("(#pin-borrow-mut task)", "(#pin-own-borrow-mut task)")
        .replace("(#forget task)",
            "(#let raw (#ptr-mut Parent::Frame) (#unsafe (#pin-release task)))\n        (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (raw (#size-of Parent::Frame)))) 0i64))")
}

#[test]
fn pinned_child_cancellation_preserves_heap_frame_layout() {
    let program = heap_pinned_source(pinned_source());
    assert!(program.contains("#pin-own-borrow-mut"));
    run(&program, "async-dependent-pinned-heap-child");
    let rejected = program.replace(" (#forget pending)", "");
    assert_ne!(rejected, program);
    let scratch = support::Scratch::new("async-dependent-pinned-heap-conflict");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let error = lim::compile_source_to_assembly(
        &rejected,
        &scratch.path().join("input.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("pinning does not authorize overlapping allocation borrows");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(
        error.message.contains("retains a conflicting borrow"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("the overlapping borrow needs a source span");
    assert_eq!(&rejected[span.start..span.end], "(#pin-release task)");
}

#[test]
fn pinned_child_rejects_a_by_value_cancellation_handler() {
    let program = pinned_source().replace("(nested Child::Poll::destroy)", "(nested forget-child)")
        + "\n#fn forget-child {\n  #params = ((value Child::Frame));\n  #returns = ();\n  #body = ( (#forget value) (#return ())\n  );\n}\n";
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
    assert!(!scratch.path().join("cache").exists());
    assert!(!scratch.path().join("generated").exists());
}

#[test]
fn removed_work_poll_cancel_is_an_unknown_function() {
    let program = source().replace(
        "(#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task pending))))",
        "(#let cleanup Work::Frame::Cleanup (#call Work::Poll::cancel ((task pending))))",
    );
    assert_ne!(program, source());
    let scratch = support::Scratch::new("async-dependent-removed-cancellation");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let error = lim::compile_source_to_assembly(
        &program,
        &scratch.path().join("input.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("the removed Work::Poll::cancel function must not compile");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error
            .message
            .contains("unknown function 'Work::Poll::cancel'"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("unknown function diagnostic should have a source span");
    assert_eq!(&program[span.start..span.end], "Work::Poll::cancel");
    assert!(!scratch.path().join("generated").exists());
}

fn run(source: &str, label: &str) {
    run_with_output(source, label, b"");
}

fn run_with_output(source: &str, label: &str, expected_stdout: &[u8]) {
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
    // Inspect the actual cached Lim source, not only an assembly artifact.
    // Child occupancy comes from the externally visible dispatcher PC;
    // neither cleanup entry point may add a variant-is conditional per child.
    let mut inspected = 0;
    let mut inspected_word_destroyers = 0;
    for entry in std::fs::read_dir(scratch.path().join("generated")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|extension| extension != "lim") {
            continue;
        }
        let generated = std::fs::read_to_string(path).unwrap();
        for node in lim::parse_source_unit(&generated).unwrap() {
            let lim::Expr::List(parts) = node.expr else {
                continue;
            };
            if matches!(parts.first(), Some(lim::Expr::Symbol(head)) if head == "#unsafe-fn")
                && matches!(parts.get(1), Some(lim::Expr::Symbol(name)) if name == "Child::Poll::destroy-words")
            {
                let source = format!("{parts:?}");
                assert!(
                    source.contains("#word-forget") && source.contains("#word-take"),
                    "{generated}"
                );
                assert!(
                    !source.contains("#word-view") && !source.contains("#pin-read"),
                    "unused reference captures must not be reified: {generated}"
                );
                inspected_word_destroyers += 1;
            }
            if !matches!(parts.first(), Some(lim::Expr::Symbol(head)) if head == "#fn")
                || !matches!(parts.get(1), Some(lim::Expr::Symbol(name))
                    if ["Work::Poll::cleanup", "Work::Poll::destroy", "Parent::Poll::cleanup", "Parent::Poll::destroy"].contains(&name.as_str()))
            {
                continue;
            }
            fn contains(expr: &lim::Expr, needle: &str) -> bool {
                matches!(expr, lim::Expr::Symbol(name) if name == needle)
                    || matches!(expr, lim::Expr::List(items) if items.iter().any(|item| contains(item, needle)))
            }
            fn has_tag_conditional(expr: &lim::Expr) -> bool {
                let lim::Expr::List(items) = expr else {
                    return false;
                };
                (matches!(items.first(), Some(lim::Expr::Symbol(name)) if name == "#if")
                    && items
                        .get(1)
                        .is_some_and(|condition| contains(condition, "#variant-is")))
                    || items.iter().any(has_tag_conditional)
            }
            assert!(!parts.iter().any(has_tag_conditional), "{generated}");
            fn has_state_match(part: &lim::Expr) -> bool {
                matches!(part, lim::Expr::List(items)
                    if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#match")
                        && matches!(items.get(1), Some(lim::Expr::List(selector))
                    if selector.as_slice() == &[lim::Expr::Symbol("#get".into()), lim::Expr::Symbol("task".into()), lim::Expr::Symbol("pc".into())]))
                    || matches!(part, lim::Expr::List(items) if items.iter().any(has_state_match))
            }
            assert!(parts.iter().any(has_state_match), "{generated}");
            if matches!(parts.get(1), Some(lim::Expr::Symbol(name)) if name.starts_with("Parent::"))
            {
                assert!(
                    parts
                        .iter()
                        .any(|part| contains(part, "#pin-get-payload-unchecked-mut")
                            || contains(part, "#word-view")
                            || contains(part, "Child::Poll::destroy-words")),
                    "{generated}"
                );
                assert!(
                    !parts
                        .iter()
                        .any(|part| contains(part, "#pin-get-payload-mut")),
                    "{generated}"
                );
            }
            inspected += 1;
        }
    }
    assert_eq!(
        inspected, 2,
        "both dependent cleanup entry points must be inspected"
    );
    if source.contains("(protocol ChildAwait)") {
        assert_eq!(
            inspected_word_destroyers, 1,
            "inspect the child word destroyer too"
        );
    }
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
    assert_eq!(status.code(), Some(42), "{status:?}: {stderr:?}");
    assert_eq!(stdout, expected_stdout);
    assert!(stderr.is_empty());
}
