mod support;

use std::{fs, process::Command, time::Duration};

fn assert_single_poll(generated: &str, poll: &str) {
    let nodes = lim::parse(generated).unwrap();
    let names = nodes
        .iter()
        .filter_map(|node| {
            let lim::Expr::List(items) = &node.expr else {
                return None;
            };
            if !matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#fn") {
                return None;
            }
            match items.get(1) {
                Some(lim::Expr::Symbol(name)) => Some(name.clone()),
                _ => None,
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(names.iter().filter(|name| *name == poll).count(), 1);
    for name in &names {
        assert!(
            ![format!("{poll}-start"), format!("{poll}-move")].contains(name),
            "{name}"
        );
        assert!(!name.starts_with(&format!("{poll}-child-")), "{name}");
        assert!(!name.starts_with(&format!("{poll}-resume-")), "{name}");
        assert!(!name.starts_with(&format!("{poll}-move-child-")), "{name}");
        assert!(!name.starts_with(&format!("{poll}-move-resume-")), "{name}");
    }
    // Both routes execute one dispatcher inside the public poll function.
    // Check the graph's actual PC loop, not the legacy label spelling.
    let body = nodes
        .iter()
        .find_map(|node| match &node.expr {
            lim::Expr::List(items)
                if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#fn")
                    && matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == poll) =>
            {
                Some(&items[4..])
            }
            _ => None,
        })
        .unwrap();
    fn has_pc_dispatch(expr: &lim::Expr) -> bool {
        let lim::Expr::List(items) = expr else {
            return false;
        };
        if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#loop") {
            if let Some(lim::Expr::List(dispatch)) = items.get(1) {
                if matches!(dispatch.first(), Some(lim::Expr::Symbol(head)) if head == "#match") {
                    if let Some(lim::Expr::List(value)) = dispatch.get(1) {
                        if matches!(value.as_slice(), [lim::Expr::Symbol(get), _, lim::Expr::Symbol(field)] if get == "#get" && field == "pc")
                        {
                            return true;
                        }
                    }
                }
            }
        }
        items.iter().any(has_pc_dispatch)
    }
    fn has_symbol(expr: &lim::Expr, predicate: fn(&str) -> bool) -> bool {
        match expr {
            lim::Expr::Symbol(name) => predicate(name),
            lim::Expr::List(items) => items.iter().any(|item| has_symbol(item, predicate)),
            _ => false,
        }
    }
    let legacy_dispatch = body
        .iter()
        .any(|expr| has_symbol(expr, |name| name.ends_with(".dispatch")))
        && body
            .iter()
            .any(|expr| has_symbol(expr, |name| name == "#continue-to"));
    assert!(
        body.iter().any(has_pc_dispatch) || legacy_dispatch,
        "{poll} must contain a single resumable dispatcher"
    );
}

#[test]
fn async_protocols_compose_with_forward_references_and_derived_names() {
    let source = "(#enum Tick ((TickStart #u64) (TickResume #u64)))
      (#enum TickPoll ((TickPending Tick) (TickReady #u64)))
      (#syntax TickAwait (#u64 Tick TickPending TickReady tick-poll))
      (#fn tick-poll (: task Tick : waker (#ref #u64)) TickPoll
        (#return (#match task
          (#case (TickStart amount) (TickPending (TickResume amount)))
          (#case (TickResume amount) (TickReady amount)))))
      (@#async-fn (: protocol ParentAwait : waker #u64 : function
        (#fn parent (: amount #u64) #u64
          (#let answer #u64 (#await ChildAwait (#call child (($ amount)))))
          (#return (#u64.+.wrap answer 2u64)))))
      (@#async-fn (: protocol ChildAwait : waker #u64 : function
        (#fn child (: amount #u64) #u64
          (#return (#await TickAwait (TickStart amount))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Parent-poll-result
          (#call parent-poll (: task (#call parent (: amount 40u64)) : waker (#borrow waker))))
        (#let-else (parent-pending pending-task) Parent-poll-result first (#unreachable))
        (#let second Parent-poll-result
          (#call parent-poll (: task pending-task : waker (#borrow waker))))
        (#return (#match second
          (#case (parent-ready value) value)
          (#case (parent-pending unexpected) (#block (#forget unexpected) (#unreachable))))))";
    let generated = build_and_run(source, 42);
    assert_generated_type_names_are_capitalized(&generated);
    for declaration in [
        "(#syntax ParentAwait (#u64 Parent-task parent-pending parent-ready parent-poll))",
        "(#syntax ChildAwait (#u64 Child-task child-pending child-ready child-poll))",
    ] {
        assert!(generated.contains(declaration), "{generated}");
        assert_eq!(generated.matches(declaration).count(), 1);
    }
    assert_single_poll(&generated, "parent-poll");
    assert_single_poll(&generated, "child-poll");
}

fn assert_frame_has_program_counter(generated: &str, name: &str) {
    let nodes = lim::parse(generated).unwrap();
    let fields = nodes.iter().find_map(|node| match &node.expr {
        lim::Expr::List(items)
            if matches!(items.as_slice(), [lim::Expr::Symbol(head), lim::Expr::Symbol(frame), ..]
                if head == "#struct" && frame == name) => match items.get(2) {
                    Some(lim::Expr::List(fields)) => Some(fields),
                    _ => None,
                },
        _ => None,
    }).expect("the generated frame must be a struct");
    assert!(fields.iter().any(|field| matches!(field,
        lim::Expr::List(items) if matches!(items.as_slice(),
            [lim::Expr::Symbol(field), lim::Expr::Symbol(ty)] if field == "pc" && ty == "#u32"))));
}

fn assert_generated_signature(generated: &str, signature: &str) {
    let expected = lim::parse(signature).unwrap().remove(0).expr;
    let lim::Expr::List(expected) = expected else {
        panic!("expected a signature");
    };
    assert_eq!(expected.len(), 4);
    assert!(
        lim::parse(generated)
            .unwrap()
            .iter()
            .any(|node| matches!(&node.expr,
        lim::Expr::List(items) if items.get(..4) == Some(expected.as_slice()))),
        "missing generated signature: {signature}"
    );
}

fn assert_generated_type_names_are_capitalized(generated: &str) {
    for node in lim::parse(generated).unwrap() {
        let lim::Expr::List(items) = node.expr else {
            continue;
        };
        if !matches!(items.first(), Some(lim::Expr::Symbol(head))
            if matches!(head.as_str(), "#struct" | "#enum" | "#type"))
        {
            continue;
        }
        let Some(lim::Expr::Symbol(name)) = items.get(1) else {
            panic!("missing type name");
        };
        assert!(
            name.chars().next().is_some_and(char::is_uppercase),
            "{name}"
        );
    }
}

#[test]
fn pinned_async_protocols_lend_the_frame_instead_of_moving_it() {
    let source = "(#enum Tick ((Waiting #u64)))
      (#enum TickPoll ((TickPending Tick) (TickReady #u64)))
      (#syntax TickAwait (#u64 Tick TickPending TickReady tick-poll))
      (#fn tick-poll (: task Tick : waker (#ref #u64)) TickPoll
        (#return (#match task (#case (Waiting count)
          (#if (#u64.== count 0u64) (TickPending (Waiting 1u64)) (TickReady count))))))
      (@#async-fn-pinned (: protocol ChildAwait : waker #u64 : function
        (#fn child (: amount #u64) #u64
          (#let ignored #u64 (#await TickAwait (Waiting 0u64)))
          (#forget ignored) (#return amount))))
      (@#async-fn (: protocol ParentAwait : waker #u64 : function
        (#fn parent (: task (#pin-ref-mut Child-frame)) #u64
          (#return (#await ChildAwait task)))))
      (#fn main () #u64
        (#let-mut frame Child-frame (#call child (: amount 42u64)))
        (#let waker #u64 0u64)
        (#let first Parent-poll-result
          (#call parent-poll (: task (#call parent (: task (#pin-borrow-mut frame))) : waker (#borrow waker))))
        (#let-else (parent-pending pending-task) Parent-poll-result first (#unreachable))
        (#let result Parent-poll-result
          (#call parent-poll (: task pending-task : waker (#borrow waker))))
        (#let answer #u64 (#match result
          (#case (parent-ready value) value)
          (#case (parent-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget frame) (#return answer))";
    let generated = build_and_run_graph(source, 42);
    assert!(generated.contains("(#syntax ChildAwait (#u64 (#pin-ref-mut Child-frame) child-pending child-ready child-poll))"), "{generated}");
    assert_single_poll(&generated, "parent-poll");
    let repeated = source
        .replace("(#u64.== count 0u64)", "(#u64.< count 2u64)")
        .replace(
            "(TickPending (Waiting 1u64))",
            "(TickPending (Waiting (#u64.+.wrap count 1u64)))",
        )
        .replace(
            "(#let answer #u64 (#match result",
            "(#let-else (parent-pending again) Parent-poll-result result (#unreachable))
          (#let third Parent-poll-result
            (#call parent-poll (: task again : waker (#borrow waker))))
          (#let answer #u64 (#match third",
        );
    build_and_run_graph(&repeated, 42);

    let cancellation = source
        .replace("(#let result Parent-poll-result\n          (#call parent-poll (: task pending-task : waker (#borrow waker))))",
          "(#let cleanup Parent-task-cleanup (#call parent-poll-cleanup (: task pending-task)))
          (#forget cleanup)
          (#let result Child-poll-result
            (#call child-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))")
        .replace("(#case (parent-ready value)", "(#case (child-ready value)")
        .replace("(#case (parent-pending unexpected)", "(#case (child-pending unexpected)");
    assert_ne!(cancellation, source);
    build_and_run_graph(&cancellation, 42);

    let premature = source
        .replace(
            "        (#forget frame) (#return answer)",
            "        (#return answer)",
        )
        .replace(
            "        (#let result Parent-poll-result",
            "        (#forget frame)\n        (#let result Parent-poll-result",
        );
    let error = graph_compile_error(&premature, "async-child-frame-retained-pin");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.message.contains("frame"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&premature[span.start..span.end], "#forget");
}

#[test]
fn async_protocols_cross_internal_and_external_imports() {
    for (import, prefix) in [("#import", ""), ("#import-external", "ext-")] {
        let scratch = support::Scratch::new("async-protocol-import");
        fs::write(
            scratch.path().join("child.lim"),
            "(#type Amount #u64)
             (@#async-fn (: protocol ChildAwait : waker #u64 : function
              (#fn child (: amount Amount) Amount (#return amount))))",
        )
        .unwrap();
        let source = format!("({import} \"child.lim\" {prefix})
          (@#async-fn (: protocol ParentAwait : waker #u64 : function
            (#fn parent () #u64
              (#return (#await {prefix}ChildAwait (#call {prefix}child (: {prefix}amount 42u64)))))))
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#return (#match (#call parent-poll (: task (#call parent (:)) : waker (#borrow waker)))
              (#case (parent-ready value) value)
              (#case (parent-pending task) (#block (#forget task) (#unreachable))))))");
        let program =
            lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
        lim::check_types(&program).unwrap();
        lim::generate_assembly(&program).unwrap();
    }
}

#[test]
fn async_protocols_keep_unknown_name_and_result_mismatch_spans() {
    let scratch = support::Scratch::new("async-protocol-errors");
    for (source, message, offending) in [
        (
            "(@#async-fn (: protocol WorkAwait : waker #u64 : function
            (#fn work () #u64 (#return (#await Missing task)))))",
            "unknown syntax bundle 'Missing'",
            "Missing",
        ),
        (
            "(@#async-fn (: protocol ChildAwait : waker #u64 : function
            (#fn child () #u64 (#return 42u64))))
          (@#async-fn (: protocol ParentAwait : waker #u64 : function
            (#fn parent () #u64
              (#let value #u32 (#await ChildAwait (#call child (:))))
              (#return (#as value #u64)))))",
            "result type does not match",
            "#await",
        ),
    ] {
        let error = lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(error.message.contains(message), "{error:?}");
        let span = error.span.expect("protocol errors retain a source span");
        assert_eq!(&source[span.start..span.end], offending, "{error:?}");
    }
}

#[test]
fn async_protocols_reject_invalid_declarations_and_name_collisions() {
    for (source, message) in [
        ("(@#async-fn (: waker #u64 : function (#fn work () #u64 (#return 42u64))))",
            "missing argument 'protocol'"),
        ("(@#async-fn (: protocol #u64 : waker #u64 : function (#fn work () #u64 (#return 42u64))))",
            "protocol names must be user-defined"),
        ("(@#async-fn (: protocol A : protocol B : waker #u64 : function (#fn work () #u64 (#return 42u64))))",
            "repeats argument 'protocol'"),
        ("(#syntax WorkAwait ())
          (@#async-fn (: protocol WorkAwait : waker #u64 : function (#fn work () #u64 (#return 42u64))))",
            "duplicate syntax bundle"),
        ("(#struct WorkAwait ())
          (@#async-fn (: protocol WorkAwait : waker #u64 : function (#fn work () #u64 (#return 42u64))))",
            "conflicts with a syntax bundle"),
        ("(@#async-fn (: protocol Work-task : waker #u64 : function (#fn work () #u64 (#return 42u64))))",
            "conflicts with a syntax bundle"),
    ] {
        let error = lim::parse_program(source).unwrap_err();
        assert!(error.contains(message), "{error}");
    }
}

#[test]
fn async_protocols_reject_names_as_an_unknown_argument() {
    for generator in ["#async-fn", "#async-fn-pinned"] {
        let source = format!(
            "(@{generator} (: protocol WorkAwait
          : names (Frame Poll Pending Ready poll) : waker #u64
          : function (#fn work () #u64 (#return 42u64))))"
        );
        let error = lim::parse_program(&source).unwrap_err();
        assert!(
            error.contains(&format!("@{generator} has no argument 'names'")),
            "{error}"
        );
    }
}

#[test]
fn async_protocols_are_exported_by_generator_produced_functions() {
    let source = "(#gn emit ()
        `((@#async-fn (: protocol ChildAwait : waker #u64 : function
           (#fn child () #u64 (#return 42u64))))))
      (@emit)
      (@#async-fn (: protocol ParentAwait : waker #u64 : function
        (#fn parent () #u64 (#return (#await ChildAwait (#call child (:)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#return (#match (#call parent-poll (: task (#call parent (:)) : waker (#borrow waker)))
          (#case (parent-ready value) value)
          (#case (parent-pending task) (#block (#forget task) (#unreachable))))))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains(
            "(#syntax ChildAwait (#u64 Child-task child-pending child-ready child-poll))"
        ),
        "{generated}"
    );
}

#[test]
fn async_task_named_capture_survives_pending_without_shadowing_the_poll_parameter() {
    let source = example_without_cancel_work().replace("offset", "task");
    let generated = build_and_run(&source, 42);
    assert_single_poll(&generated, "work-poll");
    assert!(generated.contains("(#fn work ((task #u64))"), "{generated}");
    assert!(
        generated.contains("(: task ") || generated.contains("((task "),
        "{generated}"
    );
}

#[test]
fn async_task_named_capture_without_await_keeps_explicit_public_argument_key() {
    let source = "(@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work (: task #u64) #u64 (#return task))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result Work-poll-result (#call work-poll (: task (#call work (: task 42u64)) : waker (#borrow waker))))
        (#return (#match result
          (#case (work-ready value) value)
          (#case (work-pending waiting) (#block (#forget waiting) (#unreachable))))))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("lim.gensym."), "{generated}");
}

#[test]
fn async_task_named_reference_capture_retains_its_referent_across_pending() {
    for ty in ["#ref", "#ref-mut"] {
        let borrow = if ty == "#ref" {
            "#borrow"
        } else {
            "#borrow-mut"
        };
        let source = format!("(#enum Step (: Waiting #u64)) (#linear Step)
          (#enum StepPoll (: StepPending Step : StepReady #u64))
          (#fn step-poll (: task Step : waker (#ref #u64)) StepPoll
            (#return (#match task (#case (Waiting remaining)
              (#if (#u64.== remaining 0u64) (StepReady 0u64)
                (StepPending (Waiting 0u64)))))))
          (@#async-fn (: protocol work-await : waker #u64 : function
            (#fn work (: task ({ty} #u64)) #u64
              (#let step-result #u64 (#await Step StepPending StepReady step-poll (Waiting 1u64)))
              (#return (#u64.+.wrap (#deref task) step-result)))))
          (#fn main () #u64
            (#let-mut value #u64 42u64) (#let waker #u64 0u64)
            (#let result Work-poll-result (#call work-poll (: task (#call work (: task ({borrow} value))) : waker (#borrow waker))))
            (#let-else (work-pending waiting) Work-poll-result result (#unreachable))
            (#let completed Work-poll-result (#call work-poll (: task waiting : waker (#borrow waker))))
            (#return (#match completed (#case (work-ready answer) answer)
              (#case (work-pending unfinished) (#block (#forget unfinished) (#unreachable))))))");
        build_and_run(&source, 42);
        let forbidden = source.replace(
            "(#let completed Work-poll-result",
            "(#set value 99u64)\n (#let completed Work-poll-result",
        );
        let scratch = support::Scratch::new("async-task-reference");
        let error = lim::compile_source_to_assembly(
            &forbidden,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        let span = error.span.unwrap();
        assert!(
            forbidden[span.start..span.end].contains("#set"),
            "{error:?}"
        );
    }
}

#[test]
fn one_poll_dispatcher_runs_inside_an_opaque_stationary_pin_scope() {
    let source = include_str!("../examples/async_single_poll.lim").replace(
        "../library/pin.lim",
        &format!("{}/library/pin.lim", env!("CARGO_MANIFEST_DIR")),
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "work-poll");
    assert!(
        generated.contains("Work-frame-cleanup-await-1")
            || generated.contains("work-frame-await-1")
    );
    assert!(generated.contains("(#fn work-poll-cancel"));

    // Cached inspectable output is precisely the executable dispatcher, not
    // the private helper-shaped capture-analysis witness.
    let scratch = support::Scratch::new("async-single-poll-cache");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let compile = || {
        lim::compile_source_with_generated_sources(
            &source,
            &scratch.path().join("main.lim"),
            &config,
            &scratch.path().join(".lim/cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
            None,
            &scratch.path().join(".lim"),
        )
        .unwrap()
    };
    let sources = || {
        let mut artifacts = fs::read_dir(scratch.path().join(".lim/generated"))
            .unwrap()
            .filter_map(Result::ok)
            .filter(|entry| {
                entry
                    .path()
                    .extension()
                    .is_some_and(|extension| extension == "lim")
            })
            .map(|entry| (entry.file_name(), fs::read(entry.path()).unwrap()))
            .collect::<Vec<_>>();
        artifacts.sort_by(|left, right| left.0.cmp(&right.0));
        artifacts
    };
    let cold = compile();
    let artifacts = sources();
    assert_eq!(compile(), cold);
    assert_eq!(sources(), artifacts);
    assert!(artifacts.iter().any(|(_, source)| {
        let source = String::from_utf8_lossy(source);
        source.contains("(#match (#get task pc)") || source.contains(".dispatch")
    }));
}

#[test]
fn many_ready_awaits_advance_within_one_poll_without_stage_calls() {
    let awaits = (0..16)
        .map(|index| {
            format!(
        "(#let value-{index} #u64 (#await Step StepPending StepReady step-poll (Waiting 42u64)))"
    )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let source = format!("(#enum Step (: Waiting #u64)) (#linear Step)
      (#enum StepPoll (: StepPending Step : StepReady #u64))
      (#fn step-poll (: task Step : waker (#ref #u64)) StepPoll
        (#return (#match task (#case (Waiting value) (StepReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64 {awaits} (#return value-15))))
      (#fn main () #u64 (#let waker #u64 0u64)
        (#let outcome Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#return (#match outcome
          (#case (work-ready value) value) (#case (work-pending task) (#block (#forget task) (#unreachable))))))");
    let generated = build_and_run(&source, 42);
    assert_single_poll(&generated, "work-poll");
    // Each source await has its own child poll edge, but no separate resume
    // function. Do not require legacy physical state-constructor names.
    fn count_child_polls(expr: &lim::Expr) -> usize {
        let lim::Expr::List(items) = expr else {
            return 0;
        };
        usize::from(matches!(items.as_slice(),
            [lim::Expr::Symbol(head), lim::Expr::Symbol(name), ..]
                if head == "#call" && name == "step-poll"))
            + items.iter().map(count_child_polls).sum::<usize>()
    }
    assert_eq!(
        lim::parse(&generated)
            .unwrap()
            .iter()
            .map(|node| count_child_polls(&node.expr))
            .sum::<usize>(),
        16
    );
}

#[test]
fn pinned_dispatcher_preserves_user_task_bindings() {
    let source = include_str!("../examples/async_fn_pinned.lim").replace(
        "(#return (#u64.+.wrap value offset))",
        "(#let task #u64 offset) (#return (#u64.+.wrap value task))",
    );
    assert_single_poll(&build_and_run_graph(&source, 41), "work-poll");
}

#[test]
fn generator_produced_async_declaration_keeps_its_checked_source_body() {
    let source = "
      (#enum Child ((Waiting #u64))) (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn step-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (#gn produce ()
        `((@#async-fn (: protocol work-await : waker #u64
          : function (#fn work ((seed #u64)) #u64
            (#return (#await Child ChildPending ChildReady step-poll (Waiting seed))))))))
      (@produce)
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#return (#match (#call work-poll (: task (#call work (: seed 42u64)) : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending task) (#block (#forget task) (#unreachable))))))";
    build_and_run(source, 42);
    let invalid = source.replace("(Waiting seed)", "(Waiting true)");
    let scratch = support::Scratch::new("generated-async-source-types");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("generated async original bodies must still be checked");
    assert_eq!(error.code, lim::DiagnosticCode::Type);
    let text = error.source_text.as_deref().unwrap();
    let span = error.span.unwrap();
    assert_eq!(&text[span.start..span.end], "true");
    assert!(error.source_name.as_deref().unwrap().contains("generated"));
}

#[test]
fn async_while_let_returns_after_multiple_body_awaits() {
    let source = include_str!("../examples/async_while_let_return.lim");
    build_and_run(source, 42);
    let immediate = source.replace("(StepPending (Resume value))", "(StepReady value)");
    build_and_run(&immediate, 42);

    // The pattern mismatch must not execute either child await.
    let guarded = source.replace(
        "(#case (Start value) (StepPending (Resume value)))",
        "(#case (Start value) (#block (#assert (#u64.== value 37u64)) (StepPending (Resume value))))",
    );
    build_and_run(&guarded, 42);

    let one_await = source.replace(
        "(#let second #u64 (#await #u64 Step StepPending StepReady step-poll (Start first)))\n      (#return second)",
        "(#return first)",
    ).replace(
        "(#let-else (work-pending after-second) Work-poll-result third (#unreachable))\n        (#let fourth Work-poll-result (#call work-poll (: task after-second : waker waker)))\n        (#match fourth",
        "(#match third",
    );
    assert_ne!(one_await, source);
    build_and_run(&one_await, 42);

    let synchronous_body = source.replace(
        "(#let first #u64 (#await #u64 Step StepPending StepReady step-poll (Start value)))\n      (#let second #u64 (#await #u64 Step StepPending StepReady step-poll (Start first)))\n      (#return second)",
        "(#return value)",
    );
    assert_ne!(synchronous_body, source);
    build_and_run(&synchronous_body, 42);

    let linear =
        format!(
        "(#struct Resource ((value #u64))) (#linear Resource)\n{}",
        source.replace(
            "(#let first #u64",
            "(#let token Resource (#struct-literal Resource ((value value)))) (#let first #u64",
        ).replace("(#return second)", "(#forget token) (#return second)"),
    );
    build_and_run(&linear, 42);
    let missing_consumption = linear.replace("(#forget token)", "()");
    let scratch = support::Scratch::new("async-while-let-return-linear");
    let error = lim::compile_source_to_assembly(
        &missing_consumption,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("unused linear locals must survive suspension analysis");
    assert!(
        error.message.contains("token") && error.message.contains("consum"),
        "{error:?}"
    );
}

#[test]
fn async_while_let_returned_references_keep_their_source_loan() {
    let source = include_str!("../examples/async_while_let_return.lim")
        .replace(
            "(#fn work ((choice Choice)) #u64",
            "(#fn work ((choice Choice) (counter (#ref #u64))) (#ref #u64)",
        )
        .replace("(#return second)", "(#return counter)")
        .replace("(#return 5u64)", "(#return counter)")
        .replace(
            "(#fn run ((choice Choice) (waker (#ref #u64))) #u64",
            "(#fn run ((choice Choice) (counter (#ref #u64)) (waker (#ref #u64))) (#ref #u64)",
        )
        .replace(
            "(#call work (: choice choice))",
            "(#call work (: choice choice : counter counter))",
        )
        .replace(
            "(#let waker #u64 0u64)",
            "(#let waker #u64 0u64) (#let storage #u64 37u64)",
        )
        .replace("(#let chosen #u64", "(#let chosen (#ref #u64)")
        .replace("(#let empty #u64", "(#let empty (#ref #u64)")
        .replace(
            ": choice (Chosen 37u64) : waker",
            ": choice (Chosen 37u64) : counter (#borrow storage) : waker",
        )
        .replace(
            ": choice Empty : waker",
            ": choice Empty : counter (#borrow storage) : waker",
        )
        .replace(
            "(#u64.+.wrap chosen empty)",
            "(#u64.+.wrap (#deref chosen) (#deref empty))",
        );
    build_and_run(&source, 74);
    let prefix = source.split_once("(#fn main").unwrap().0;
    let escaping = format!("{prefix}
      (#fn main () (#ref #u64)
        (#let waker #u64 0u64)
        (#let storage #u64 37u64)
        (#return (#call run (: choice (Chosen 37u64) : counter (#borrow storage) : waker (#borrow waker)))))");
    let pending = format!(
        "{prefix}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut storage #u64 37u64)
        (#let frame Work-task (#call work (: choice (Chosen 37u64) : counter (#borrow storage))))
        (#let first Work-poll-result (#call work-poll (: task frame : waker (#borrow waker))))
        (#let-else (work-pending task) Work-poll-result first (#unreachable))
        (#set storage 42u64)
        (#forget task)
        (#return storage))"
    );
    let scratch = support::Scratch::new("async-while-let-return-loans");
    for (source, expected, offending_line) in [
        (&escaping, "reference", "(#return (#call run"),
        (&pending, "borrow", "(#set storage 42u64)"),
    ] {
        let error = lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .err()
        .expect("returned and pending references must retain their source loan");
        assert!(error.message.contains(expected), "{error:?}");
        let span = error
            .span
            .expect("borrow failures must underline their source");
        let line = source.lines().nth(span.line - 1).unwrap();
        assert!(line.contains(offending_line), "{error:?}: {line}");
    }
    let cancelled = pending.replace(
        "(#set storage 42u64)\n        (#forget task)",
        "(#forget task)\n        (#set storage 42u64)",
    );
    build_and_run(&cancelled, 42);
}

fn example_source() -> String {
    include_str!("../examples/async_fn.lim")
        .replace(
            "../library/linux_x86_64.lim",
            &format!("{}/library/linux_x86_64.lim", env!("CARGO_MANIFEST_DIR")),
        )
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
    let declaration = ": cancel (cancel-work ((step cancel-step) (await-0 cancel-step)))";
    let invocation = "  (#call cancel-work (: task (#call work-poll-cleanup (: task (#call work (: offset 99u64))))))\n";
    assert_eq!(original.matches(declaration).count(), 1);
    assert_eq!(original.matches(invocation).count(), 1);
    original.replace(declaration, "").replace(invocation, "")
}

fn build_and_run(source: &str, expected: i32) -> String {
    build_and_run_route(source, expected, false)
}

fn build_and_run_graph(source: &str, expected: i32) -> String {
    build_and_run_route(source, expected, true)
}

fn graph_compile_error(source: &str, label: &str) -> lim::Diagnostic {
    let scratch = support::Scratch::new(label);
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("the checked graph source must be rejected")
}

fn build_and_run_route(source: &str, expected: i32, graph: bool) -> String {
    build_and_run_route_status(source, Some(expected), graph)
}

fn build_and_run_route_status(source: &str, expected: Option<i32>, graph: bool) -> String {
    let scratch = support::Scratch::new("async-fn");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.arg(&input).arg("-o").arg(&binary);
    if graph {
        command.arg("--cfg").arg("async-lowering=graph");
    }
    let (status, _, stderr) =
        support::run(&mut command, Duration::from_secs(20), 1024 * 1024).unwrap();
    let generated_sources = fs::read_dir(scratch.path().join(".lim/generated"))
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
        expected,
        "{status:?}: {}\ngenerated source:\n{generated}",
        String::from_utf8_lossy(&stderr),
    );
    #[cfg(unix)]
    if expected.is_none() {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(
            status.signal(),
            Some(4),
            "bounds failures must trap with SIGILL"
        );
    }
    generated
}

#[test]
fn async_generated_code_does_not_allow_shadowing_in_nested_branches() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (ChildReady 0u64)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((value #u64)) #u64
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#if true
            (#block (#let value #u64 2u64) ())
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
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((finish-early #bool) (range-early #bool) (for-early #bool)) #u64
          (#while finish-early
            (#return 41u64))
          (#for-range (iteration #u32) 0u32
            (#if range-early 1u32 0u32)
            (#return 40u64))
          (#for (#let-mut iteration #u32 0u32)
                (#u32.< iteration (#if for-early 1u32 0u32))
                (#set iteration (#u32.+.wrap iteration 1u32))
            (#return 39u64))
          (#let value #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 42u64)))
          (#return value))))
      (#fn work-poll-work ((finish-early #bool) (range-early #bool) (for-early #bool) (waker (#ref #u64))) #u64
        (#let task Work-task
          (#call work (: finish-early finish-early : range-early range-early : for-early for-early)))
        (#let result Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match result
          (#case (work-ready value) value)
          (#case (work-pending pending) (#block (#forget pending) 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let early #u64
          (#call work-poll-work (: finish-early true : range-early false : for-early false : waker (#borrow waker))))
        (#let range #u64
          (#call work-poll-work (: finish-early false : range-early true : for-early false : waker (#borrow waker))))
        (#let for #u64
          (#call work-poll-work (: finish-early false : range-early false : for-early true : waker (#borrow waker))))
        (#let resumed #u64
          (#call work-poll-work (: finish-early false : range-early false : for-early false : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap early (#u64.+.wrap range (#u64.+.wrap for resumed)))))";
    build_and_run(source, 162);
}

#[test]
fn async_returning_branch_skips_a_suspending_common_tail() {
    let source = include_str!("../examples/async_conditional_return.lim");
    build_and_run(source, 49);
    let matched = source
        .replace("(#if early", "(#match early (#case true")
        .replace(
            "(#return first))\n      ())",
            "(#return first))) (#case false ()))",
        );
    assert_ne!(matched, source);
    build_and_run(&matched, 49);
    let borrowed = source
        .replace(
            "(#fn work ((early #bool))",
            "(#fn work ((early #bool) (counter (#ref-mut #u64)))",
        )
        .replace(
            "(#fn run ((early #bool)",
            "(#fn run ((early #bool) (counter (#ref-mut #u64))",
        )
        .replace(
            "(#call work (: early early))",
            "(#call work (: early early : counter counter))",
        )
        .replace(
            "(#return first)",
            "(#deref-set counter first) (#return (#deref counter))",
        )
        .replace(
            "(#return result)",
            "(#deref-set counter result) (#return (#deref counter))",
        )
        .replace(
            "(#let early #u64",
            "(#let-mut counter #u64 0u64) (#let early #u64",
        )
        .replace(
            ": early true : waker",
            ": early true : counter (#borrow-mut counter) : waker",
        )
        .replace(
            ": early false : waker",
            ": early false : counter (#borrow-mut counter) : waker",
        )
        .replace(
            "(#let later #u64",
            "(#assert (#u64.== counter 7u64)) (#let later #u64",
        )
        .replace(
            "(#return (#u64.+.wrap early later))",
            "(#assert (#u64.== counter 42u64)) (#return (#u64.+.wrap early later))",
        );
    build_and_run(&borrowed, 49);
    let borrowed_work = borrowed.split_once("(#fn run").unwrap().0;
    let pending = format!(
        "{borrowed_work}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut counter #u64 0u64)
        (#let frame Work-task (#call work (: early true : counter (#borrow-mut counter))))
        (#let first Work-poll-result (#call work-poll (: task frame : waker (#borrow waker))))
        (#let-else (work-pending task) Work-poll-result first (#unreachable))
        (#set counter 42u64)
        (#forget task)
        (#return counter))"
    );
    let scratch = support::Scratch::new("async-conditional-return-borrow");
    let input = scratch.path().join("borrow.lim");
    let error = lim::compile_source_to_assembly(
        &pending,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("borrow"), "{error:?}");
    let cancelled = pending.replace(
        "(#set counter 42u64)\n        (#forget task)",
        "(#forget task)\n        (#set counter 42u64)",
    );
    build_and_run(&cancelled, 42);

    let linear = format!(
        "(#struct Resource ((value #u64))) (#linear Resource)\n{}",
        source
            .replace(
                "(#fn work ((early #bool))",
                "(#fn work ((early #bool) (resource Resource))"
            )
            .replace(
                "(#fn run ((early #bool)",
                "(#fn run ((early #bool) (resource Resource)"
            )
            .replace(
                "(#call work (: early early))",
                "(#call work (: early early : resource resource))"
            )
            .replace("(#let first #u64", "(#forget resource) (#let first #u64")
            .replace("(#let result #u64", "(#forget resource) (#let result #u64")
            .replace(
                ": early true : waker",
                ": early true : resource (#struct-literal Resource ((value 1u64))) : waker"
            )
            .replace(
                ": early false : waker",
                ": early false : resource (#struct-literal Resource ((value 2u64))) : waker"
            )
    );
    build_and_run(&linear, 49);
    let missing_consumption = linear.replacen("(#forget resource)", "()", 1);
    let error = lim::compile_source_to_assembly(
        &missing_consumption,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("resource") && error.message.contains("consumed"),
        "{error:?}"
    );
    let escaped = source.replace("(#return result)", "(#return first)");
    let error = lim::compile_source_to_assembly(
        &escaped,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("unknown") && error.message.contains("first"),
        "{error:?}"
    );
    let span = error.span.expect("escaped branch-local use span");
    assert_eq!(&escaped[span.start..span.end], "first");
    assert_eq!(
        span.start,
        escaped.rfind("(#return first)").unwrap() + "(#return ".len()
    );
}

#[test]
fn async_function_returns_ready_from_an_ordinary_if_branch() {
    let source = "(#enum Child (Waiting Resume))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resume))
          (#case Resume (ChildReady 42u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((early #bool)) #u64
          (#if early (#block (#return 7u64)) ())
          (#let result #u64
            (#await #u64 Child ChildPending ChildReady child-poll Waiting))
          (#return result))))
      (#fn run ((early #bool) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: early early)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready value) value)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready value) value)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let early #u64 (#call run (: early true : waker (#borrow waker))))
        (#let resumed #u64 (#call run (: early false : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap early resumed)))";
    build_and_run(source, 49);
}

#[test]
fn async_function_returns_ready_from_an_ordinary_match_branch() {
    let source = "(#enum Child (Waiting Resume))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#enum Action (ReturnNow Wait))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resume))
          (#case Resume (ChildReady 42u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((action Action)) #u64
          (#match action
            (#case ReturnNow (#block (#return 7u64)))
            (#case Wait ()))
          (#let result #u64
            (#await #u64 Child ChildPending ChildReady child-poll Waiting))
          (#return result))))
      (#fn run ((action Action) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: action action)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready value) value)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready value) value)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let early #u64 (#call run (: action ReturnNow : waker (#borrow waker))))
        (#let resumed #u64 (#call run (: action Wait : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap early resumed)))";
    build_and_run(source, 49);
}

#[test]
fn async_function_early_return_from_synchronous_loop_produces_ready() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#loop (#return 41u64))
          (#let value #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 42u64)))
          (#return value))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value #u64
          (#match result
            (#case (work-ready ready) ready)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    build_and_run(source, 41);
}

#[test]
fn async_lowering_errors_highlight_the_later_nested_await() {
    let source = "(#enum Step ((Waiting #u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
        (#return (#match task (#case (Waiting value) (StepReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let first #u64
            (#await Step StepPending StepReady step-poll (Waiting 1u64)))
          (#let second #u64
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
    let generated = build_and_run_graph(&example_source(), 42);
    assert_frame_has_program_counter(&generated, "Work-task");
    assert_single_poll(&generated, "work-poll");
    assert!(!generated.contains("#await"));
}

#[test]
fn pinned_async_frames_poll_in_place_and_cancel_explicitly() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (#fn cancel-child ((task Child)) () (#forget task) (#return ()))
      (@#async-fn-pinned (: protocol work-await : waker #u64 : function
        (#fn work ((offset #u64)) #u64
          (#let value #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64))
          )
          (#return (#u64.+.wrap value offset)))))
      (#fn main () #u64
        (#let-mut frame Work-frame (#call work (: offset 40u64)))
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (work-pending pinned-frame) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pinned-frame : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) (#unreachable)))))
        (#forget frame)
        (#let-mut cancelled-frame Work-frame (#call work (: offset 90u64)))
        (#let first-cancel Work-poll-result
          (#call work-poll (: task (#pin-borrow-mut cancelled-frame) : waker (#borrow waker))))
        (#let-else (work-pending cancel-pin) Work-poll-result first-cancel (#unreachable))
        (#let state-to-cancel Work-frame-cleanup (#call work-poll-cleanup (: task cancel-pin)))
        (#call cancel-frame (: task state-to-cancel))
        (#forget cancelled-frame)
        (#forget waker)
        (#return result))";
    let source = source.replace(
        ": waker #u64 : function",
        ": waker #u64 : cancel (cancel-frame ((await-0 cancel-child))) : function",
    );
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let moved = source.replace(
        "(#let second Work-poll-result",
        "(#let moved Work-frame frame)\n        (#let second Work-poll-result",
    );
    let scratch = support::Scratch::new("pinned-frame-move-span");
    let diagnostic = lim::compile_source_to_assembly(
        &moved,
        &scratch.path().join("main.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    let error = &diagnostic.message;
    assert!(
        error.contains("pinned")
            || error.contains("borrow")
            || error.contains("consumed")
            || error.contains("used more than once"),
        "{error}"
    );
    assert!(matches!(
        diagnostic.code,
        lim::DiagnosticCode::Linear | lim::DiagnosticCode::Borrow
    ));
    let span = diagnostic
        .span
        .expect("the move must retain its original source span");
    assert!(moved[span.start..span.end].contains("frame"));

    let escaping = source.replace(
        "(#fn main () #u64",
        "(#fn escape-frame () Work-poll-result
          (#let-mut frame Work-frame (#call work (: offset 40u64)))
          (#let waker #u64 0u64)
          (#return (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker)))))
        (#fn main () #u64",
    );
    let error = lim::compile_source_to_assembly(
        &escaping,
        &scratch.path().join("escape.lim"),
        &config,
        &scratch.path().join("escape-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("a pinned frame handle must not escape its owner")
    .message;
    assert!(
        error.contains("outlive")
            || error.contains("borrow")
            || error.contains("local")
            || error.contains("consumed"),
        "pinned frame handle must not escape its owner: {error}"
    );

    let generated = build_and_run_graph(&source, 41);
    assert!(
        generated.contains("(#pin-ref-mut Work-frame)"),
        "work-poll must borrow the pinned frame: {generated}"
    );
    assert_frame_has_program_counter(&generated, "Work-frame");
    assert_single_poll(&generated, "work-poll");
    assert!(!generated.contains("(#pin-read task)"), "{generated}");
    assert!(!generated.contains("(#pin-write task"), "{generated}");
    assert_generated_signature(
        &generated,
        "(#fn work-poll-cleanup ((task (#pin-ref-mut Work-frame))) Work-frame-cleanup)",
    );
    assert!(generated.contains("(#fn work-poll-cancel"), "{generated}");
}

#[test]
fn pinned_async_frames_keep_local_pins_stationary_across_suspension() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64) (ChildPending (Waiting 1u64)) (ChildReady 0u64))))))
      (@#async-fn-pinned (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut value #u64 41u64)
          (#let view (#pin-ref #u64) (#pin-borrow value))
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#return (#u64.+.wrap (#deref view) result)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut frame Work-frame (#call work ()))
        (#let first Work-poll-result
          (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let outcome Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let answer #u64 (#match outcome
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget frame) (#return answer))";
    build_and_run_graph(source, 41);
}

#[test]
fn pinned_async_frame_self_reference_survives_pending_and_is_cleared_on_cancel() {
    let source = include_str!("../examples/async_fn_self_reference.lim");
    let generated = build_and_run_graph(source, 58);
    assert_single_poll(&generated, "read-after-await-poll");
    assert_frame_has_program_counter(&generated, "Read-after-await-frame");

    let pending_mutation = source.replace(
        "  (#let second Read-after-await-poll-result",
        "  (#call read-after-await-owner-replace (: task (#pin-borrow-mut frame) : value (#struct-literal Owner ((payload (#struct-literal Payload ((left 99u64) (right 5u64))))))))\n  (#let second Read-after-await-poll-result",
    );
    assert_ne!(pending_mutation, source);
    let error = graph_compile_error(&pending_mutation, "async-pending-owner-replace");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);

    // Keep both disjoint shared projections alive through await, and reject
    // exclusive aliases formed from the source owner, not private frame fields.
    for field in ["left", "right"] {
        let overlapping = source.replace(
            "    (#let result #u64",
            &format!("    (#let conflict (#pin-ref-mut #u64) (#pin-borrow-mut (#get (#get owner payload) {field})))\n    (#let result #u64"),
        );
        assert_ne!(overlapping, source);
        let error = graph_compile_error(&overlapping, &format!("async-self-overlap-{field}"));
        assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    }

    let cancelled_mutation = source.replace(
        "  (#block\n    (#let cleanup Read-after-await-frame-cleanup",
        "  (#call read-after-await-owner-replace (: task (#pin-borrow-mut cancelled) : value (#struct-literal Owner ((payload (#struct-literal Payload ((left 11u64) (right 7u64))))))))\n  (#block\n    (#let cleanup Read-after-await-frame-cleanup",
    );
    assert_ne!(cancelled_mutation, source);
    let error = graph_compile_error(&cancelled_mutation, "async-before-cleanup-owner-replace");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);

    // Shared internal references do not forbid a simultaneous shared owner read.
    let direct_owner_use = source.replace(
        "(#u64.+.wrap (#u64.+.wrap (#deref view) (#deref right-view)) result)",
        "(#u64.+.wrap (#u64.+.wrap (#u64.+.wrap (#deref view) (#deref right-view)) result) (#get (#get owner payload) left))",
    );
    assert_ne!(direct_owner_use, source);
    build_and_run_graph(&direct_owner_use, 98);
}

#[test]
fn pinned_async_frame_retains_enum_payload_reference_across_pending() {
    let source = include_str!("../examples/async_fn_enum_self_reference.lim");
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "read-after-await-poll");

    let pending_mutation = source.replace(
        "    (#let result #u64",
        "    (#let choice-pin (#pin-ref-mut Choice)\n      (#pin-borrow-mut (#get owner choice)))\n    (#let result #u64",
    );
    assert_ne!(pending_mutation, source);
    let error = graph_compile_error(&pending_mutation, "async-enum-owner-overlap");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the enum owner must remain borrowed while its payload reference is pending: {error}"
    );
}

#[test]
fn pinned_async_frame_initializes_a_local_owner_before_self_borrowing_it() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim");
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "local-self-ref-poll");

    let late_owner = source.replace(
        "    (#let owner LocalOwner",
        "    (#let before-owner #u64 1u64)\n    (#let owner LocalOwner",
    );
    assert_ne!(late_owner, source);
    // Graph lowering executes source statements after pinning, without the
    // legacy restriction that the owner must be the first source statement.
    build_and_run_graph(&late_owner, 42);
}

#[test]
fn pinned_async_frame_retains_mutable_self_reference_across_pending() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim")
        .replace("(#let owner LocalOwner", "(#let-mut owner LocalOwner")
        .replace("(#pin-ref #u64)", "(#pin-ref-mut #u64)")
        .replace(
            "(#pin-borrow (#get (#get owner payload) left))",
            "(#pin-borrow-mut (#get (#get owner payload) left))",
        )
        .replace(
            "    (#return (#u64.+.wrap (#deref view) result))",
            "    (#unsafe (#pin-write view 41u64))\n    (#return (#u64.+.wrap (#deref view) result))",
        );
    let generated = build_and_run_graph(&source, 43);
    assert_single_poll(&generated, "local-self-ref-poll");

    let overlapping_owner_read = source.replace(
        "    (#unsafe (#pin-write view 41u64))",
        "    (#let overlapping #u64 (#get (#get owner payload) left))\n    (#unsafe (#pin-write view 41u64))",
    );
    assert_ne!(overlapping_owner_read, source);
    let error = graph_compile_error(&overlapping_owner_read, "async-exclusive-owner-overlap");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "reading through the owner must conflict with the retained exclusive projection: {error}"
    );

    let duplicate_exclusive_borrow = source.replace(
        "    (#let result #u64",
        "    (#let second-view (#pin-ref-mut #u64)\n      (#pin-borrow-mut (#get (#get owner payload) left)))\n    (#let result #u64",
    );
    assert_ne!(duplicate_exclusive_borrow, source);
    let error = graph_compile_error(
        &duplicate_exclusive_borrow,
        "async-exclusive-self-duplicate",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the same pinned projection must not be borrowed exclusively twice: {error}"
    );

    // Make the local owner explicitly linear so cleanup must return it after
    // clearing the internal exclusive reference; do not inspect private cells.
    let linear = source.replace("(#struct LocalOwner", "(#linear LocalOwner)\n(#struct LocalOwner")
        .replace("(#return (#u64.+.wrap (#deref view) result))",
            "(#let answer #u64 (#u64.+.wrap (#deref view) result))\n    (#drop view)\n    (#forget owner)\n    (#return answer)");
    let (prefix, after_second_poll) = linear
        .split_once("  (#let second Local-self-ref-poll-result")
        .unwrap();
    let (_, suffix) = after_second_poll.split_once("  (#forget frame)").unwrap();
    let cancelled = format!(
        "{prefix}\
          (#let cleanup Local-self-ref-frame-cleanup\n\
            (#call local-self-ref-poll-cleanup (: task pending-frame)))\n\
          (#let result #u64 (#match (#get cleanup owner)\n\
            (#case Local-self-ref-frame-cleanup-owner-empty (#unreachable))\n\
            (#case (Local-self-ref-frame-cleanup-owner-full extracted) (#block\n\
              (#let-mut owned LocalOwner extracted)\n\
              (#set-field owned payload (#struct-literal LocalPayload ((left 41u64) (right 5u64))))\n\
              (#let value #u64 (#get (#get owned payload) left))\n\
              (#forget owned) value))))\n\
          (#match (#get cleanup await-0)\n\
            (#case Local-self-ref-frame-cleanup-await-0-empty ())\n\
            (#case (Local-self-ref-frame-cleanup-await-0-full child) (#forget child)))\n\
          (#forget cleanup)\n\
          (#forget frame){suffix}"
    );
    let generated = build_and_run_graph(&cancelled, 41);
    assert_single_poll(&generated, "local-self-ref-poll");
}

#[test]
fn pinned_async_result_cannot_export_a_local_self_reference() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim")
        .replace(
            "(#fn local-self-ref ((seed #u64)) #u64",
            "(#fn local-self-ref ((seed #u64)) (#pin-ref #u64)",
        )
        .replace(
            "(#return (#u64.+.wrap (#deref view) result))",
            "(#return view)",
        )
        .replace(
            "(#let result #u64\n    (#match second",
            "(#let result (#pin-ref #u64)\n    (#match second",
        )
        .replace("(#return result))", "(#return (#deref result)))");
    let error = graph_compile_error(&source, "async-pinned-local-reference-result");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow")
            || error.contains("pinned")
            || error.contains("destroy")
            || error.contains("retaining a reference to local"),
        "the async result must not export a reference to local source storage: {error}"
    );
}

#[test]
fn async_function_can_complete_without_suspension() {
    let original = example_source();
    let (prefix, _) = original.split_once("(#fn main () #u64").unwrap();
    let source = format!(
        "{} (#fn main () #u64
           (#let executor Executor
             (#struct-literal Executor ((notifications
               (#call CellU64-create (: value 0u64))))))
           (#let waker LocalWaker
             (#call local-waker-create (: executor (#borrow executor) : metadata (#struct-literal WakeMetadata ((amount 1u64))))))
           (#let result Work-poll-result
             (#call work-poll (: task (#call work (: offset 1u64)) : waker (#borrow waker))))
           (#let value #u64
             (#match result
               (#case (work-ready value) value)
               (#case (work-pending task)
                 (#block (#forget task) (#unreachable)))))
           (#call local-waker-destroy (: waker waker))
           (#forget executor)
           (#return value))",
        prefix.replace(
            "(#let step Step (Waiting 1u64))",
            "(#let step Step (Waiting 0u64))"
        )
    );
    build_and_run_graph(&source, 41);
}

#[test]
fn async_function_without_await_runs_its_body_on_first_poll() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@#cell #u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (@#async-fn (: protocol work-await : waker #u64 : function
           (#fn work ((cell (#ref CellU64))) #u64
             (#call CellU64-set (: cell cell : value 1u64))
             (#return (#u64.+.wrap (#call CellU64-get (: cell cell)) 41u64)))))
         (#fn main () #u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let task Work-task (#call work (: cell (#borrow cell))))
           (#let before #u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let waker #u64 0u64)
           (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
           (#let result #u64
             (#match outcome
               (#case (work-ready value) value)
               (#case (work-pending pending) (#block (#forget pending) 0u64))))
           (#let after #u64 (#call CellU64-get (: cell (#borrow cell))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#bool.&& (#u64.== result 42u64)
                                            (#u64.== after 1u64)))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "work-poll");
    assert!(generated.contains("(work-ready"), "{generated}");
}

#[test]
fn pinned_async_function_without_await_runs_on_first_poll() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@#cell #u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (@#async-fn-pinned (: protocol work-await : waker #u64 : function
           (#fn work ((cell (#ref CellU64))) #u64
             (#call CellU64-set (: cell cell : value 1u64))
             (#return (#u64.+.wrap (#call CellU64-get (: cell cell)) 41u64)))))
         (#fn main () #u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let-mut frame Work-frame (#call work (: cell (#borrow cell))))
           (#let before #u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let waker #u64 0u64)
           (#let outcome Work-poll-result
             (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
           (#let result #u64
             (#match outcome
               (#case (work-ready value) value)
               (#case (work-pending pending) (#block (#forget pending) 0u64))))
           (#let after #u64 (#call CellU64-get (: cell (#borrow cell))))
           (#forget frame)
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#bool.&& (#u64.== result 42u64)
                                            (#u64.== after 1u64)))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "work-poll");
    assert!(
        generated.contains("(#pin-ref-mut Work-frame)"),
        "{generated}"
    );
    assert!(generated.contains("(#fn work-poll-cancel"), "{generated}");
}

#[test]
fn async_function_keeps_live_values_distinct_across_suspension() {
    let source = "(#struct Box ((value #u64)))
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (#block (#forget value) (ChildReady 1u64))))))
      (#fn echo ((value #u64)) #u64 (#return value))
      (@#async-fn (: protocol work-await : waker #u64 : function
      (#fn work ((first #u64)) #u64
          (#let value #u64 5u64)
          (#let box Box (#struct-literal Box ((value 7u64))))
          (#let child Child (Waiting 0u64))
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll child))
          (#return (#u64.+.wrap
            (#call echo (: value 8u64))
            (#u64.+.wrap first (#get box value)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let outcome Work-poll-result
          (#call work-poll (: task (#call work (: first 2u64)) : waker (#borrow waker))))
        (#return (#match outcome
          (#case (work-ready result) result)
          (#case (work-pending task) (#block (#forget task) (#unreachable))))))";
    let source = source.replace(
        "(#block (#forget value) (ChildReady 1u64))",
        "(#if (#u64.== value 0u64) (ChildPending (Waiting 1u64)) (ChildReady 1u64))"
    ).replace("(#return (#match outcome",
        "(#let-else (work-pending pending) Work-poll-result outcome (#unreachable))\n        (#let resumed Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))\n        (#return (#match resumed");
    let generated = build_and_run_graph(&source, 17);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_requires_unused_linear_values_to_be_consumed_before_return() {
    let source = "(#struct Token ((value #u64)))
      (#linear Token)
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (#block (#forget value) (ChildReady 1u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let token Token (#struct-literal Token ((value 1u64))))
          (#let child Child (Waiting 0u64))
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll child))
          (#return result))))
      (#fn main () () (#return ()))";
    let error = graph_compile_error(source, "async-unused-linear").message;
    assert!(
        error.contains("token") && (error.contains("linear") || error.contains("consum")),
        "{error:?}"
    );
}

#[test]
fn async_function_rejects_reference_to_pre_suspension_local() {
    let source = "(#struct Waker ((count #u64)))
        (#enum Child ((Waiting #u64)))
        (#linear Child)
        (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
        (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
          (#return (ChildPending task)))
        (@#async-fn (: protocol make-await : waker Waker : function (#fn make () #u64
            (#let owner #u64 1u64)
            (#let view (#ref #u64) (#borrow owner))
            (#let child Child (Waiting 1u64))
            (#let value #u64
              (#await Child ChildPending ChildReady child-poll child))
            (#return (#deref view)))))
        (#fn main () #u64 (#return 0u64))";
    let error = graph_compile_error(source, "async-movable-local-borrow").message;
    assert!(
        error.contains("local") || error.contains("outlive") || error.contains("borrow"),
        "{error}"
    );
}

#[test]
fn async_function_accepts_no_arguments_or_captures() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#forget task)
        (#return (ChildReady 7u64)))
      (@#async-fn (: protocol work-await : waker Waker : function (#fn work () #u64
          (#let value #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#return value))))
      (#fn main () #u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let outcome Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    build_and_run_graph(source, 7);
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
         (#let second #u64
           (#await Step StepPending StepReady step-poll (Waiting 0u64)))
         (#return (#u64.+.wrap total offset))",
        )
        .replace("((offset #u64)) #u64", "((#mut offset #u64)) #u64");
    let generated = build_and_run_graph(&source, 48);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_has_no_fixed_suspension_count_limit() {
    let mut body = String::new();
    for index in 0..33 {
        body.push_str(&format!(
            "(#let result-{index} #u64 (#await Step StepPending StepReady step-poll (Waiting {index}u64)))\n"
        ));
    }
    body.push_str("(#return result-32)");
    let source = format!(
        "(#enum Step ((Waiting #u64)))
         (#linear Step)
         (#enum StepPoll ((StepPending Step) (StepReady #u64)))
         (#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
           (#return (#match task (#case (Waiting value) (StepReady value)))))
         (@#async-fn (: protocol work-await : waker #u64 : function
           (#fn work () #u64 {body})))
         (#fn main () #u64
           (#let waker #u64 0u64)
           (#let outcome Work-poll-result
             (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
           (#let result #u64
             (#match outcome
               (#case (work-ready value) value)
               (#case (work-pending task) (#block (#forget task) 0u64))))
           (#forget waker)
           (#return result))"
    );
    let generated = build_and_run_graph(&source, 32);
    assert_single_poll(&generated, "work-poll");
    assert!(
        generated.contains("Work-task-cleanup-await-32"),
        "{generated}"
    );
}

#[test]
fn async_function_awaits_a_task_produced_by_an_earlier_await() {
    let source = "(#enum OuterTask ((Waiting #u64) (Resuming #u64)))
      (#linear OuterTask)
      (#enum OuterPoll ((OuterPending OuterTask) (OuterReady #u64)))
      (#fn outer-poll ((task OuterTask) (waker (#ref #u64))) OuterPoll
        (#return (#match task
          (#case (Waiting value) (OuterPending (Resuming value)))
          (#case (Resuming value) (OuterReady value)))))
      (#enum InnerTask (MakeOuter))
      (#enum InnerPoll ((InnerPending InnerTask) (InnerReady OuterTask)))
      (#fn inner-poll ((task InnerTask) (waker (#ref #u64))) InnerPoll
        (#return (#match task
          (#case MakeOuter (InnerReady (Waiting 42u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#await OuterTask OuterPending OuterReady outer-poll
              (#await OuterTask InnerTask InnerPending InnerReady inner-poll MakeOuter)))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
    assert!(!generated.contains("(#await"), "{generated}");

    // The same task dependency must work when the outer await is an operand,
    // not only when it is the direct RHS of a binding.
    let nested_operand = source.replace(
        "(#await OuterTask OuterPending OuterReady outer-poll\n              (#await OuterTask InnerTask InnerPending InnerReady inner-poll MakeOuter))",
        "(#u64.+.wrap 0u64\n            (#await #u64 OuterTask OuterPending OuterReady outer-poll\n              (#await OuterTask InnerTask InnerPending InnerReady inner-poll MakeOuter)))",
    );
    assert_ne!(nested_operand, source);
    let generated = build_and_run_graph(&nested_operand, 42);
    assert_single_poll(&generated, "work-poll");
    assert!(!generated.contains("(#await"), "{generated}");

    // Both dependencies may return Pending. Completing the inner await must
    // initialize the outer task exactly once, then retain it for its own retry.
    let both_pending = nested_operand
        .replace("(#enum InnerTask (MakeOuter))", "(#enum InnerTask (MakeOuter ResumeOuter))")
        .replace(
            "(#case MakeOuter (InnerReady (Waiting 42u64)))",
            "(#case MakeOuter (InnerPending ResumeOuter))\n          (#case ResumeOuter (InnerReady (Waiting 42u64)))",
        )
        .replace(
            "(#let second Work-poll-result\n          (#call work-poll (: task pending : waker (#borrow waker))))",
            "(#let middle Work-poll-result\n          (#call work-poll (: task pending : waker (#borrow waker))))\n        (#let-else (work-pending outer-pending) Work-poll-result middle (#unreachable))\n        (#let second Work-poll-result\n          (#call work-poll (: task outer-pending : waker (#borrow waker))))",
        );
    assert_ne!(both_pending, nested_operand);
    build_and_run_graph(&both_pending, 42);
    build_and_run_graph(include_str!("../examples/async_nested_await.lim"), 42);
}

#[test]
fn async_function_awaits_directly_in_explicit_return() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Step ((Waiting #u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (StepPending (Waiting 1u64))
              (StepReady count))))))
      (@#async-fn (: protocol work-await : waker Waker : function
        (#fn work ((initial #u64)) #u64
          (#return (#await Step StepPending StepReady step-poll (Waiting initial))))))
      (#fn main () #u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: initial 0u64)) : waker (#borrow waker))))
        (#let-else (work-pending first-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task first-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 1);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_extracts_typed_awaits_from_value_expressions() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (#fn sum ((a #u64) (b #u64)) #u64 (#return (#u64.+.wrap a b)))
      (@#async-fn (: protocol work-await : waker Waker : function
        (#fn work () #u64
          (#let result #u64 (#call sum (:
            b (#await #u64 Child ChildPending ChildReady child-poll (Waiting 20u64))
            : a (#await #u64 Child ChildPending ChildReady child-poll (Waiting 10u64)))))
          (#return result))))
      (#fn main () #u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let outcome Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 30);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_call_arguments_are_evaluated_in_declaration_order_before_suspension() {
    let source = "(#enum Child (Waiting))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Waiting)))))
      (#fn mark ((counter (#ref-mut #u64))) #u64
        (#deref-set counter 1u64)
        (#return 3u64))
      (#fn sum ((first #u64) (second #u64)) #u64
        (#return (#u64.+.wrap first second)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((counter (#ref-mut #u64))) #u64
          (#let result #u64
            (#call sum (:
              first (#call mark (: counter counter))
              : second (#await #u64 Child ChildPending ChildReady child-poll Waiting))))
          (#return result))))
      (#fn main () #u64
        (#let-mut counter #u64 0u64)
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: counter (#borrow-mut counter))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result outcome (#unreachable))
        (#forget pending)
        (#forget waker)
        (#return counter))";
    let generated = build_and_run_graph(source, 1);
    assert!(generated.contains("(#call mark"), "{generated}");
    let reordered = source.replace(
        "first (#call mark (: counter counter))\n              : second (#await #u64 Child ChildPending ChildReady child-poll Waiting)",
        "second (#await #u64 Child ChildPending ChildReady child-poll Waiting)\n              : first (#call mark (: counter counter))");
    assert_ne!(reordered, source);
    build_and_run_graph(&reordered, 1);
}

#[test]
fn async_numeric_operands_are_evaluated_in_source_order_before_suspension() {
    let source = "(#enum Child (Waiting))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Waiting)))))
      (#fn mark ((counter (#ref-mut #u64))) #u64
        (#deref-set counter 1u64)
        (#return 3u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((counter (#ref-mut #u64))) #u64
          (#return (#u64.+.wrap
            (#call mark (: counter counter))
            (#await #u64 Child ChildPending ChildReady child-poll Waiting))))))
      (#fn main () #u64
        (#let-mut counter #u64 0u64)
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: counter (#borrow-mut counter))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result outcome (#unreachable))
        (#forget pending)
        (#forget waker)
        (#return counter))";
    build_and_run_graph(source, 1);
}

#[test]
fn async_enum_payloads_are_evaluated_in_source_order_before_awaits() {
    let source = "(#enum Data ((Pair #u64 #u64)))
      (#enum Child (Waiting))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Waiting)))))
      (#fn mark ((counter (#ref-mut #u64))) #u64
        (#deref-set counter 1u64)
        (#return 3u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((counter (#ref-mut #u64))) #u64
          (#let value Data
            (Pair
              (#call mark (: counter counter))
              (#await #u64 Child ChildPending ChildReady child-poll Waiting)))
          (#return 0u64))))
      (#fn main () #u64
        (#let-mut counter #u64 0u64)
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: counter (#borrow-mut counter))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result outcome (#unreachable))
        (#forget pending)
        (#forget waker)
        (#return counter))";
    build_and_run_graph(source, 1);
}

#[test]
fn async_nested_block_bindings_survive_suspension_inside_an_initializer() {
    let source = "(#enum Child (Waiting Resume))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resume))
          (#case Resume (ChildReady 42u64)))))
      (#fn mark ((counter (#ref-mut #u64))) #u64
        (#deref-set counter 1u64)
        (#return 3u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((counter (#ref-mut #u64))) #u64
          (#let result #u64
            (#block
              (#let before #u64 (#call mark (: counter counter)))
              (#let total #u64
                (#u64.+.wrap before
                  (#await #u64 Child ChildPending ChildReady child-poll Waiting)))
              total))
          (#return result))))
      (#fn main () #u64
        (#let-mut counter #u64 0u64)
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: counter (#borrow-mut counter))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result outcome (#unreachable))
        (#let resumed Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match resumed
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return (#u64.+.wrap counter result)))";
    build_and_run_graph(source, 46);
}

#[test]
fn async_nested_block_assignments_resume_after_awaited_rhs_values() {
    let source = "(#enum Child (Waiting Resume))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resume))
          (#case Resume (ChildReady 42u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#block
              (#let-mut total #u64 3u64)
              (#set total
                (#u64.+.wrap total
                  (#await #u64 Child ChildPending ChildReady child-poll Waiting)))
              total))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    build_and_run_graph(source, 45);
}

#[test]
fn async_nested_block_effect_statements_can_await() {
    let source = "(#enum Child (Waiting Resume))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resume))
          (#case Resume (ChildReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#block
              (#assert (#await #bool Child ChildPending ChildReady child-poll Waiting))
              42u64))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 42);
}

#[test]
fn async_struct_fields_are_evaluated_in_source_order_before_suspension() {
    let source = "(#struct Pair ((first #u64) (second #u64)))
      (#enum Child (Waiting))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Waiting)))))
      (#fn mark ((counter (#ref-mut #u64))) #u64
        (#deref-set counter 1u64)
        (#return 3u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((counter (#ref-mut #u64))) #u64
          (#let pair Pair
            (#struct-literal Pair (
              (first (#call mark (: counter counter)))
              (second (#await #u64 Child ChildPending ChildReady child-poll Waiting)))))
          (#return (#get pair first)))))
      (#fn main () #u64
        (#let-mut counter #u64 0u64)
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: counter (#borrow-mut counter))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result outcome (#unreachable))
        (#forget pending)
        (#forget waker)
        (#return counter))";
    let generated = build_and_run(source, 1);
    assert!(generated.contains("(#call mark"), "{generated}");
}

#[test]
fn async_tuple_and_array_elements_are_evaluated_before_later_awaits() {
    let source = "(#enum Child (Waiting))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Waiting)))))
      (#fn mark ((counter (#ref-mut #u64))) #u64
        (#deref-set counter 1u64)
        (#return 3u64))
      (@#async-fn (: protocol work-tuple-await : waker #u64 : function
        (#fn work-tuple ((counter (#ref-mut #u64))) #u64
          (#let pair (#tuple #u64 #u64)
            (#tuple (#tuple #u64 #u64)
              (#call mark (: counter counter))
              (#await #u64 Child ChildPending ChildReady child-poll Waiting)))
          (#return 0u64))))
      (@#async-fn (: protocol work-array-await : waker #u64 : function
        (#fn work-array ((counter (#ref-mut #u64))) #u64
          (#let values (#array #u64 2)
            (#array-of (#array #u64 2)
              (#call mark (: counter counter))
              (#await #u64 Child ChildPending ChildReady child-poll Waiting)))
          (#return 0u64))))
      (#fn main () #u64
        (#let-mut tuple-counter #u64 0u64)
        (#let-mut array-counter #u64 0u64)
        (#let waker #u64 0u64)
        (#let tuple-task Work-tuple-task
          (#call work-tuple (: counter (#borrow-mut tuple-counter))))
        (#let tuple-outcome Work-tuple-poll-result
          (#call work-tuple-poll (: task tuple-task : waker (#borrow waker))))
        (#let-else (work-tuple-pending tuple-pending) Work-tuple-poll-result tuple-outcome (#unreachable))
        (#forget tuple-pending)
        (#let array-task Work-array-task
          (#call work-array (: counter (#borrow-mut array-counter))))
        (#let array-outcome Work-array-poll-result
          (#call work-array-poll (: task array-task : waker (#borrow waker))))
        (#let-else (work-array-pending array-pending) Work-array-poll-result array-outcome (#unreachable))
        (#forget array-pending)
        (#forget waker)
        (#return (#u64.+.wrap tuple-counter array-counter)))";
    build_and_run(source, 2);
}

#[test]
fn async_function_extracts_typed_await_from_another_await_task() {
    let source = "(#enum ChildTask ((Waiting #u64)))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#await #u64 ChildTask ChildPending ChildReady child-poll
              (Waiting
                (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 42u64)))))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let outcome Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");

    let inferred_source = source.replacen(
        "#await #u64 ChildTask ChildPending ChildReady child-poll\n              (Waiting",
        "#await ChildTask ChildPending ChildReady child-poll\n              (Waiting",
        1,
    );
    assert_ne!(inferred_source, source);
    let generated = build_and_run_graph(&inferred_source, 42);
    assert_single_poll(&generated, "work-poll");

    let return_source = source
        .replace("(#let result #u64\n            ", "(#return ")
        .replace("          (#return result)", "");
    assert_ne!(return_source, source);
    let generated = build_and_run_graph(&return_source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_suspends_in_a_value_block_with_conditional_await() {
    let source = "(#enum StepTask ((Waiting #u64) (Resuming #u64)))
      (#enum StepPoll ((StepPending StepTask) (StepReady #u64)))
      (#linear StepTask)
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (Waiting value) (StepPending (Resuming value)))
          (#case (Resuming value) (StepReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((choose #bool)) #u64
          (#let value #u64
            (#block
              (#let base #u64 13u64)
              (#if choose
                (#await #u64 StepTask StepPending StepReady step-poll (Waiting base))
                0u64)))
          (#return (#u64.+.wrap value 13u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: choose true)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let result #u64
          (#match first
            (#case (work-ready first-value) first-value)
            (#case (work-pending pending)
              (#match (#call work-poll (: task pending : waker (#borrow waker)))
                (#case (work-ready second-value) second-value)
                (#case (work-pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 26);
    assert_single_poll(&generated, "work-poll");
    let immediate = source.replace("(: choose true)", "(: choose false)");
    assert_ne!(immediate, source);
    build_and_run_graph(&immediate, 13);
}

#[test]
fn async_function_suspends_inside_mutable_assignment_rhs() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker Waker : function
        (#fn work () #u64
          (#let-mut total #u64 10u64)
          (#set total
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
          (#return total))))
      (#fn main () #u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_loop_expression_can_be_suspended_as_a_nested_value() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let ignored ()
            (#loop
              (#let result #u64
                (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
              (#break)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let-else (work-ready result) Work-poll-result second (#unreachable))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_while_expression_can_be_suspended_as_a_nested_value() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let ignored ()
            (#block
              (#let-mut iteration #u64 0u64)
              (#while (#u64.< iteration 1u64)
                (#let result #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#set iteration 1u64))))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let-else (work-ready result) Work-poll-result second (#unreachable))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_loop_expression_can_be_suspended_in_a_selected_branch() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((choose #bool)) #u64
          (#let ignored ()
            (#if choose
              (#loop
                (#let value #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break))
              ()))
          (#return 42u64))))
      (#fn run ((choose #bool) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: choose choose)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let awaited #u64 (#call run (: choose true : waker (#borrow waker))))
        (#let immediate #u64 (#call run (: choose false : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap awaited immediate)))";
    let generated = build_and_run_graph(source, 84);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_suspension_inside_nested_value_block_preserves_block_scope() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn identity ((value #u64)) #u64 (#return value))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call identity (: value
              (#block
                (#let value #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                value))))
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 41);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_value_loop_results_use_declared_expression_types() {
    let source = include_str!("../examples/async_loop_breaks.lim");
    let called = source
        .replace(
            "(#break 42u64)",
            "(#break (#call identity (: value 42u64)))",
        )
        .replace(
            "(#break awaited)",
            "(#break (#call identity (: value awaited)))",
        );
    assert_ne!(called, source);
    build_and_run_graph(&called, 42);

    let comparison = source
        .replace(
            "(#fn identity ((value #u64)) #u64 (#return value))",
            "(#fn identity ((value #bool)) #u64 (#return (#if value 42u64 0u64)))",
        )
        .replace("(#break 42u64)", "(#break (#u64.== awaited 41u64))")
        .replace("(#break awaited)", "(#break (#u64.< awaited 42u64))")
        .replace("(#u64.== final 41u64)", "(#u64.== final 42u64)");
    build_and_run_graph(&comparison, 42);

    for (declarations, consumer, first, second) in [
        (
            "(#struct Token ((value #u64)))",
            "(#fn identity ((token Token)) #u64 (#let value #u64 (#get token value)) (#forget token) (#return value))",
            "(#struct-literal Token ((value 42u64)))",
            "(#struct-literal Token ((value awaited)))",
        ),
        (
            "(#enum Outcome ((Value #u64)))",
            "(#fn identity ((token Outcome)) #u64 (#return (#match token (#case (Value value) value))))",
            "(Value 42u64)",
            "(Value awaited)",
        ),
        (
            "",
            "(#fn identity ((token (#tuple #u64 #bool))) #u64 (#return (#get token 0)))",
            "(#tuple (#tuple #u64 #bool) 42u64 true)",
            "(#tuple (#tuple #u64 #bool) awaited false)",
        ),
        (
            "",
            "(#fn identity ((token #u32)) #u64 (#return (#as token #u64)))",
            "(#as 42u64 #u32)",
            "(#as awaited #u32)",
        ),
    ] {
        let constructed = format!("{declarations}\n{}", source
            .replace("(#fn identity ((value #u64)) #u64 (#return value))", consumer)
            .replace("(#call identity (: value", "(#call identity (: token")
            .replace("(#break 42u64)", &format!("(#break {first})"))
            .replace("(#break awaited)", &format!("(#break {second})")));
        build_and_run_graph(&constructed, 42);
    }
    let blocked = called.replace(
        "(#break (#call identity (: value 42u64)))",
        "(#break (#block (#let local #u64 42u64) (#call identity (: value local))))",
    );
    build_and_run_graph(&blocked, 42);
    let conditional = called.replace(
        "(#break (#call identity (: value 42u64)))",
        "(#break (#if choose (#call identity (: value 42u64)) 0u64))",
    );
    build_and_run_graph(&conditional, 42);

    let invalid = format!(
        "(#fn wrong-type () #u32 (#return 42u32))\n{}",
        called.replace("(#call identity (: value 42u64))", "(#call wrong-type ())")
    );
    let scratch = support::Scratch::new("async-loop-expression-result-type");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &{
            let mut config = lim::CompileConfig::default();
            config.set("async-lowering", "graph");
            config
        },
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("different declared break-result types must be rejected");
    assert_eq!(error.code, lim::DiagnosticCode::Type);
    assert!(error.span.is_some(), "{error:?}");
    build_and_run_graph(include_str!("../examples/async_loop_results.lim"), 42);
}

#[test]
fn async_value_loop_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn identity ((value #u64)) #u64 (#return value))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call identity (: value
              (#loop
                (#let awaited #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break awaited)))))
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 41);
    assert_single_poll(&generated, "work-poll");

    let early_break = source.replace(
        "(#break awaited)",
        "(#if (#u64.== awaited 41u64) (#break 42u64) ())\n                (#break awaited)",
    );
    assert_ne!(early_break, source);
    build_and_run_graph(&early_break, 42);
    let fallthrough = early_break.replace("(#u64.== awaited 41u64)", "(#u64.== awaited 0u64)");
    build_and_run_graph(&fallthrough, 41);
    let branch_only = source.replace(
        "(#break awaited)",
        "(#if (#u64.== awaited 41u64) (#break 42u64) (#break awaited))",
    );
    build_and_run_graph(&branch_only, 42);
    let branch_fallthrough =
        branch_only.replace("(#u64.== awaited 41u64)", "(#u64.== awaited 0u64)");
    build_and_run_graph(&branch_fallthrough, 41);
    let branch_match = branch_only.replace(
        "(#if (#u64.== awaited 41u64) (#break 42u64) (#break awaited))",
        "(#match (#u64.== awaited 41u64) (#case true (#break 42u64)) (#case false (#break awaited)))",
    );
    build_and_run_graph(&branch_match, 42);
    let nested_branch = branch_only.replace(
        "(#if (#u64.== awaited 41u64)",
        "(#let inner #u32 (#loop (#break 7u32)))\n                (#assert (#u32.== inner 7u32))\n                (#if (#u64.== awaited 41u64)",
    );
    build_and_run_graph(&nested_branch, 42);
    let outer_value = branch_only
        .replace("(#fn work () #u64", "(#fn work ((fallback #u64)) #u64")
        .replace("(#call work ())", "(#call work (: fallback 42u64))")
        .replace("(#break 42u64)", "(#break fallback)");
    assert_ne!(outer_value, branch_only);
    build_and_run_graph(&outer_value, 42);
    let nested_loop = early_break.replace(
        "(#if (#u64.== awaited 41u64)",
        "(#let nested #u64 (#loop (#break 7u64)))\n                (#assert (#u64.== nested 7u64))\n                (#if (#u64.== awaited 41u64)",
    );
    build_and_run_graph(&nested_loop, 42);
    let invalid = early_break.replace("(#break 42u64)", "(#break 42u32)");
    let scratch = support::Scratch::new("async-value-loop-break-type");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &{
            let mut config = lim::CompileConfig::default();
            config.set("async-lowering", "graph");
            config
        },
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("all break values must still match the loop result type");
    assert_eq!(error.code, lim::DiagnosticCode::Type);
    let message = error.message.to_ascii_lowercase();
    assert!(
        message.contains("u64") && message.contains("u32"),
        "{}",
        error.message
    );
    assert!(
        error.span.is_some(),
        "break type mismatch needs a source span"
    );
    build_and_run_graph(include_str!("../examples/async_loop_breaks.lim"), 42);
}

#[test]
fn async_value_loop_break_moves_linear_payload_across_pending() {
    let source = "(#struct Token ((value #u64)))
      (#linear Token)
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Token)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value)
            (ChildReady (#struct-literal Token ((value value))))))))
      (#fn consume-token ((token Token)) #u64
        (#let value #u64 (#get token value))
        (#forget token)
        (#return value))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call consume-token (: token
              (#loop
                (#let token Token
                  (#await Token ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break token)))))
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    build_and_run_graph(source, 41);
    let early_break = source.replace(
        "(#break token)",
        "(#if (#u64.== (#get token value) 41u64) (#break token) ())\n                (#break token)",
    );
    assert_ne!(early_break, source);
    build_and_run_graph(&early_break, 41);
    let branch_only = source.replace(
        "(#break token)",
        "(#if (#u64.== (#get token value) 41u64) (#break token) (#break token))",
    );
    build_and_run_graph(&branch_only, 41);
}

#[test]
fn async_value_loop_statement_can_discard_a_copy_break_result() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#loop
            (#let value #u64
              (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
            (#break (#u64.+.wrap value 1u64)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending pending-again)
              (#block (#forget pending-again) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_value_loop_statement_cannot_discard_a_linear_break_result() {
    let source = "(#struct Token ((value #u64)))
      (#linear Token)
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Token)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value)
            (ChildReady (#struct-literal Token ((value value))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#loop
            (#let value Token
              (#await Token ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
            (#break value))
          (#return 42u64))))
      (#fn main () #u64 (#return 0u64))";
    let error = lim::parse_program(source).unwrap_err();
    assert!(
        error.contains("cannot discard a non-Copy result from an awaited #loop"),
        "{error}"
    );
}

#[test]
fn async_unit_loop_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) #u64 (#return 42u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call consume-unit (: value
              (#loop
                (#let awaited #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break)))))
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_unit_while_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) #u64 (#return 43u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call consume-unit (: value
              (#while true
                (#let awaited #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 41u64)))
                (#break)))))
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 43);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_for_range_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) #u64 (#return 44u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call consume-unit (: value
              (#for-range (iteration #u64) 0u64 1u64
                (#let awaited #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll
                    (Waiting iteration)))))))
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 44);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_for_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#fn consume-unit ((value ())) #u64 (#return 45u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call consume-unit (: value
              (#for (#let-mut iteration #u64 0u64)
                    (#u64.< iteration 1u64)
                    (#set iteration (#u64.+.wrap iteration 1u64))
                (#let awaited #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll
                    (Waiting iteration)))))))
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 45);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_while_let_expression_can_be_suspended_in_a_call_argument() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Maybe)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady None)))))
      (#fn consume-unit ((value ())) #u64 (#return 46u64))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#call consume-unit (: value
              (#while-let (Some payload)
                (#await Maybe ChildTask ChildPending ChildReady child-poll (Waiting 0u64))
                ()))) )
          (#return result))))
      (#fn run ((waker (#ref #u64))) #u64
        (#let task Work-task (#call work ()))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result #u64 (#call run (: waker (#borrow waker))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 46);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_function_suspends_inside_projected_assignment_rhs() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 0u64))
          (#set-index values 0usize
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
          (#return (#index values 0usize)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_awaits_before_selecting_an_if_branch() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady true)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#if (#await #bool Child ChildPending ChildReady child-poll (Waiting 1u64))
              42u64
              0u64))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
    let false_branch = source.replace("(ChildReady true)", "(ChildReady false)");
    assert_ne!(false_branch, source);
    build_and_run_graph(&false_branch, 0);
}

#[test]
fn async_function_awaits_before_selecting_a_match_arm() {
    let source = "(#enum Decision ((Continue #u64) Stop))
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady Decision)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady (Continue 42u64))
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#return (#match (#await Decision Child ChildPending ChildReady child-poll (Waiting 1u64))
            (#case (Continue value) value)
            (#case Stop 0u64))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
    let stopped = source.replace("(ChildReady (Continue 42u64))", "(ChildReady Stop)");
    assert_ne!(stopped, source);
    build_and_run_graph(&stopped, 0);
}

#[test]
fn async_function_resumes_inside_a_value_producing_block() {
    let source = "(#struct DecisionResult ((condition #bool) (value #u64)))
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady true)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result DecisionResult
            (#block
              (#let offset #u64 40u64)
              (#let choose #bool true)
              (#let condition #bool
                (#if choose
                  (#await #bool Child ChildPending ChildReady child-poll
                    (Waiting (#u64.-.wrap offset 39u64)))
                  false))
              (#struct-literal DecisionResult
                ((condition condition)
                 (value (#if condition (#u64.+.wrap offset 2u64) 0u64))))))
          (#return (#get result value)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_assigns_conditional_await_result_inside_a_block() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady 42u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((choose #bool)) #u64
          (#return (#block
            (#let-mut result #u64 0u64)
            (#set result
              (#if choose
                (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
                7u64))
            result)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (: choose true)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    build_and_run_graph(source, 42);
}

#[test]
fn async_function_resumes_multiple_awaits_inside_one_block() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady true)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#block
              (#let first #bool
                (#await #bool Child ChildPending ChildReady child-poll (Waiting 1u64)))
              (#let second #bool
                (#await #bool Child ChildPending ChildReady child-poll (Waiting 2u64)))
              (#if (#bool.&& first second) 42u64 0u64)))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending after-first) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task after-first : waker (#borrow waker))))
        (#let-else (work-pending after-second) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task after-second : waker (#borrow waker))))
        (#let-else (work-pending after-third) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result (#call work-poll (: task after-third : waker (#borrow waker))))
        (#let result #u64
          (#match fourth
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_assigns_a_block_local_after_await_resumes() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut total (#array #u64 1)
            (#array-of (#array #u64 1) 1u64))
          (#let result #u64
            (#block
              (#set-index total 0usize
                (#await #u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
              (#index total 0usize)))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(#set-index total (#literal #usize 0) lim.async.nested-await-0)"),
        "{generated}"
    );
    assert!(
        generated.contains("(#let-mut total (#array #u64 1)"),
        "the mutable assignment target must survive work-pending: {generated}"
    );
}

#[test]
fn async_function_preserves_mutability_of_block_await_bindings() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 41u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#block
              (#let-mut value #u64
                (#await #u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))
              (#set value (#u64.+.wrap value 1u64))
              value))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(#let-mut lim.async.nested-await-0 #u64"),
        "the dispatch arm must restore a mutable binding: {generated}"
    );
}

#[test]
fn async_function_runs_block_prefix_side_effect_once_before_await() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady 42u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut count #u64 0u64)
          (#let result #u64
            (#block
              (#set count (#u64.+.wrap count 1u64))
              (#let value #u64
                (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
              (#u64.+.wrap value count)))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending running-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task running-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 43);
}

#[test]
fn async_function_suspends_on_a_discarded_copy_await_in_a_block() {
    let source = "(#enum ChildTask (Start Resume))
      (#linear ChildTask)
      (#enum ChildPoll ((Pending ChildTask) (Ready ())))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Start (Pending Resume))
          (#case Resume (Ready ())))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
            (#block
              (#let base #u64 40u64)
              (#await () ChildTask Pending Ready child-poll Start)
              (#u64.+.wrap base 2u64)))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll.dispatch"), "{generated}");
}

#[test]
fn async_function_rejects_discarding_a_linear_await_result_in_a_block() {
    let source = "(#struct Resource ((value #u64)))
      (#linear Resource)
      (#enum ChildTask (Start Resume))
      (#linear ChildTask)
      (#enum ChildPoll ((Pending ChildTask) (Ready Resource)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Start (Pending Resume))
          (#case Resume (Ready (#struct-literal Resource ((value 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let result #u64
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
        "          (#let result #u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
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
        "          (#let result #u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
        "          (#block\n            (#await Resource ChildTask Pending Ready child-poll Start))\n          (#return 42u64)",
    );
    assert_ne!(terminal_block_source, source);
    let type_error = lim::parse_program(&terminal_block_source).unwrap_err();
    assert!(
        type_error.contains("cannot discard a non-Copy #await result"),
        "{type_error}"
    );

    let conditional_source = source.replace(
        "          (#let result #u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
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
        "          (#let result #u64\n            (#block\n              (#await Resource ChildTask Pending Ready child-poll Start)\n              42u64))\n          (#return result)",
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
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe) (after Maybe)) #u64
          (#let-else (Some payload) Maybe input (#return 7u64))
          (#let value #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 42u64)))
          (#let-else (Some ignored) Maybe after (#return 9u64))
          (#return value))))
      (#fn work-poll-work ((input Maybe) (after Maybe) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: input input : after after)))
        (#let result Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match result
          (#case (work-ready value) value)
          (#case (work-pending pending) (#block (#forget pending) 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let early #u64
          (#call work-poll-work (: input None : after (Some 1u64) : waker (#borrow waker))))
        (#let post-await #u64
          (#call work-poll-work (: input (Some 1u64) : after None : waker (#borrow waker))))
        (#let awaited #u64
          (#call work-poll-work (: input (Some 1u64) : after (Some 1u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap (#u64.+.wrap early post-await) awaited)))";
    let generated = build_and_run(source, 58);
    assert!(generated.contains("(work-ready"), "{generated}");
}

#[test]
fn async_function_can_await_let_else_scrutinee() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum Child ((Waiting Maybe)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady Maybe)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some value) Maybe
            (#await Child ChildPending ChildReady child-poll (Waiting input))
            (#return 7u64))
          (#return value))))
      (#fn work-poll-work ((input Maybe) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: input input)))
        (#let result Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match result
          (#case (work-ready value) value)
          (#case (work-pending pending) (#block (#forget pending) 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let unmatched #u64
          (#call work-poll-work (: input None : waker (#borrow waker))))
        (#let matched #u64
          (#call work-poll-work (: input (Some 42u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap unmatched matched)))";
    build_and_run(source, 49);
}

#[test]
fn async_function_awaits_inside_let_else_return_expression() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 7u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some value) Maybe input
            (#return (#u64.+.wrap 1u64
              (#await #u64 Child ChildPending ChildReady child-poll (Waiting 1u64)))))
          (#return value))))";
    let source = format!(
        "{source}
         (#fn work-poll-work ((input Maybe) (waker (#ref #u64))) #u64
           (#let task Work-task (#call work (: input input)))
           (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
           (#let result #u64
             (#match first
               (#case (work-ready value) value)
               (#case (work-pending pending) (#block
                 (#let second Work-poll-result (#call work-poll (: task pending : waker waker)))
                 (#match second
                   (#case (work-ready value) value)
                   (#case (work-pending unexpected) (#block (#forget unexpected) 0u64)))))))
           (#return result))
         (#fn main () #u64
           (#let waker #u64 0u64)
           (#let mismatch #u64 (#call work-poll-work (: input None : waker (#borrow waker))))
           (#let matched #u64 (#call work-poll-work (: input (Some 41u64) : waker (#borrow waker))))
           (#forget waker)
           (#return (#u64.+.wrap mismatch matched)))"
    );
    build_and_run(&source, 49);
}

#[test]
fn async_let_else_can_await_before_an_unreachable_failure() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some payload) Maybe input
            (#block
              (#let ignored #u64
                (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))
              (#unreachable)))
          (#return payload))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: input (Some 42u64))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let value #u64
          (#match outcome
            (#case (work-ready ready) ready)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll.dispatch"), "{generated}");
}

#[test]
fn async_let_else_can_await_before_a_diverging_panic() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some payload) Maybe input
            (#block
              (#let ignored #u64
                (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))
              (#panic)))
          (#return payload))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: input (Some 42u64))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) value)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll.dispatch"), "{generated}");
}

#[test]
fn async_let_else_can_suspend_in_one_panic_only_branch() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe) (wait #bool)) #u64
          (#let-else (Some payload) Maybe input
            (#if wait
              (#block
                (#let ignored #u64
                  (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))
                (#panic))
              (#panic)))
          (#return payload))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: input (Some 42u64) : wait true)))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) value)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll.dispatch"), "{generated}");
}

#[test]
fn async_let_else_can_suspend_in_one_panic_only_match_arm() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe) (wait #bool)) #u64
          (#let-else (Some payload) Maybe input
            (#match wait
              (#case true
                (#block
                  (#let ignored #u64
                    (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))
                  (#panic)))
              (#case false (#panic))))
          (#return payload))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: input (Some 42u64) : wait true)))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) value)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll.dispatch"), "{generated}");
}

#[test]
fn async_let_else_awaits_inside_an_assertion_before_unreachable() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask (Waiting))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildReady 42u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some value) Maybe input
            (#block
              (#assert (#u64.==
                (#await #u64 ChildTask ChildPending ChildReady child-poll Waiting)
                42u64))
              (#unreachable)))
          (#return value))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: input (Some 42u64))))
        (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) value)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("poll.dispatch"), "{generated}");
}

#[test]
fn async_let_else_accepts_conditional_awaited_return_arms() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe) (choose #bool)) #u64
          (#let-else (Some payload) Maybe input
            (#block
              (#let base #u64 13u64)
              (#if choose
                (#return (#await #u64 ChildTask ChildPending ChildReady
                  child-poll (Waiting base)))
                (#return (#u64.+.wrap base 4u64)))))
          (#return payload))))
      (#fn drive ((input Maybe) (choose #bool) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: input input : choose choose)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready first-value) first-value)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready second-value) second-value)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64)))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let awaited #u64
          (#call drive (: input None : choose true : waker (#borrow waker))))
        (#let immediate #u64
          (#call drive (: input None : choose false : waker (#borrow waker))))
        (#let matched #u64
          (#call drive (: input (Some 9u64) : choose true : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap (#u64.+.wrap awaited immediate) matched)))";
    build_and_run(source, 39);
}

#[test]
fn async_let_else_diverging_branch_can_return_after_multiple_awaits() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some matched) Maybe input
            (#block
              (#let first #u64
                (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 20u64)))
              (#let second #u64
                (#await #u64 ChildTask ChildPending ChildReady child-poll
                  (Waiting (#u64.+.wrap first 7u64))))
              (#return (#u64.+.wrap first second))))
          (#return matched))))
      (#fn run ((input Maybe) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: input input)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready result) result)
          (#case (work-pending after-first)
            (#match (#call work-poll (: task after-first : waker waker))
              (#case (work-ready result) result)
              (#case (work-pending after-second)
                (#match (#call work-poll (: task after-second : waker waker))
                  (#case (work-ready result) result)
                  (#case (work-pending unexpected)
                    (#block (#forget unexpected) 0u64)))))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let missing #u64 (#call run (: input None : waker (#borrow waker))))
        (#let present #u64 (#call run (: input (Some 9u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap missing present)))";
    build_and_run(source, 56);
}

#[test]
fn async_graph_nested_let_else_await_uses_the_child_result_contract() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some value) Maybe input
            (#return (#u64.+.wrap 1u64
              (#await Child ChildPending ChildReady child-poll (Waiting 7u64)))))
          (#return value))))";
    let source = format!(
        "{source}
        (#fn run (: input Maybe) #u64
          (#let waker #u64 0u64)
          (#let result Work-poll-result
            (#call work-poll (: task (#call work (: input input)) : waker (#borrow waker))))
          (#return (#match result
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
        (#fn main () #u64
          (#return (#u64.+.wrap
            (#call run (: input (Some 42u64)))
            (#call run (: input None)))))"
    );
    let generated = build_and_run_graph(&source, 50);
    assert_single_poll(&generated, "work-poll");
    let suspended = source
        .replace(
            "(ChildReady value)))))",
            "(#if (#u64.== value 7u64) (ChildPending (Waiting 8u64)) (ChildReady 7u64))))))",
        )
        .replace(
            "(#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))",
            "(#case (work-pending pending-task)
              (#block
                (#let second Work-poll-result
                  (#call work-poll (: task pending-task : waker (#borrow waker))))
                (#match second
                  (#case (work-ready resumed) resumed)
                  (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))",
        );
    assert_ne!(suspended, source);
    build_and_run_graph(&suspended, 50);
}

#[test]
fn async_function_only_polls_awaited_let_else_mismatch_arm() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 7u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let-else (Some value) Maybe input
            (#block
              (#let retry-count #u64 1u64)
              (#let first #u64
                (#await #u64 Child ChildPending ChildReady child-poll
                  (Waiting retry-count)))
              (#let second #u64
                (#await #u64 Child ChildPending ChildReady child-poll
                  (Waiting 0u64)))
              (#return (#u64.+.wrap first second))))
          (#let adjusted #u64 (#u64.+.wrap value 1u64))
          (#return adjusted))))
      (#fn work-poll-work ((input Maybe) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: input input)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready value) value)
          (#case (work-pending running-task)
            (#block
              (#let second Work-poll-result (#call work-poll (: task running-task : waker waker)))
              (#match second
                (#case (work-ready value) value)
                (#case (work-pending pending) (#block (#forget pending) 0u64))))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let mismatch #u64
          (#call work-poll-work (: input None : waker (#borrow waker))))
        (#let matched #u64
          (#call work-poll-work (: input (Some 42u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap mismatch matched)))";
    build_and_run(source, 57);
}

#[test]
fn async_function_resumes_suspension_after_awaited_let_else_success() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum Child ((Waiting #u64) (SuccessWaiting #u64 #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
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
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#let base #u64 1u64)
          (#let-else (Some value) Maybe input
          (#return (#await #u64 Child ChildPending ChildReady child-poll
              (Waiting 1u64))))
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll
              (SuccessWaiting 1u64 (#u64.+.wrap value base))))
          (#return result))))
      (#fn work-poll-work ((input Maybe) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: input input)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready value) value)
          (#case (work-pending running-task)
            (#block
              (#let second Work-poll-result (#call work-poll (: task running-task : waker waker)))
              (#match second
                (#case (work-ready value) value)
                (#case (work-pending pending) (#block (#forget pending) 0u64))))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let mismatch #u64
          (#call work-poll-work (: input None : waker (#borrow waker))))
        (#let matched #u64
          (#call work-poll-work (: input (Some 42u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap mismatch matched)))";
    build_and_run(source, 50);
}

#[test]
fn async_function_releases_let_else_success_borrow_after_ready() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum Child ((Waiting #u64) (WriteAfterResume (#ref-mut #u64) #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value))
          (#case (WriteAfterResume owner remaining)
            (#if (#u64.== remaining 0u64)
              (#block (#deref-set owner 42u64) (ChildReady 42u64))
              (ChildPending
                (WriteAfterResume owner (#u64.-.wrap remaining 1u64))))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe) (owner (#ref-mut #u64))) #u64
          (#let-else (Some value) Maybe input
            (#return (#await #u64 Child ChildPending ChildReady child-poll
              (Waiting 7u64))))
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll
              (WriteAfterResume owner 1u64)))
          (#return result))))
      (#fn main () #u64
        (#let-mut owner #u64 1u64)
        (#let waker #u64 0u64)
        (#let task Work-task (#call work
          (: input (Some 10u64) : owner (#borrow-mut owner))))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        MUTATE_WHILE_PENDING
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64 (#match second
          (#case (work-ready value) value)
          (#case (work-pending unfinished) (#block (#forget unfinished) 0u64))))
        (#set owner 3u64)
        (#forget waker)
        (#return (#u64.+.wrap result owner)))";
    let accepted = source.replace("MUTATE_WHILE_PENDING", "");
    build_and_run(&accepted, 45);

    let rejected = source.replace("MUTATE_WHILE_PENDING", "(#set owner 4u64)");
    let error = lim::check_types(&lim::parse_program(&rejected).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("loan"),
        "the success child must retain its exclusive borrow while work-pending: {error}"
    );
}

#[test]
fn async_graph_nested_await_uses_the_child_result_contract() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll (#return (ChildReady 1u64)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#return (#u64.+.wrap
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64))
            1u64)))))";
    let source = format!(
        "{source}
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let result Work-poll-result
            (#call work-poll (: task (#call work ()) : waker (#borrow waker))))
          (#return (#match result
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))"
    );
    let generated = build_and_run_graph(&source, 2);
    assert_single_poll(&generated, "work-poll");
    let suspended = source
        .replace(
            "(#return (ChildReady 1u64))",
            "(#return (#match task (#case (Waiting count)
              (#if (#u64.== count 0u64) (ChildPending (Waiting 1u64)) (ChildReady count)))))",
        )
        .replace(
            "(#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))",
            "(#case (work-pending pending-task)
              (#block
                (#let second Work-poll-result
                  (#call work-poll (: task pending-task : waker (#borrow waker))))
                (#match second
                  (#case (work-ready resumed) resumed)
                  (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))",
        );
    assert_ne!(suspended, source);
    build_and_run_graph(&suspended, 2);
    let mismatched = source.replace(
        "#await Child ChildPending",
        "#await #u32 Child ChildPending",
    );
    let error = graph_compile_error(&mismatched, "async-nested-await-contract");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(error.message.contains("Ready payload"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&mismatched[span.start..span.end], "#u32");
}

#[test]
fn async_function_extracts_awaits_from_keyed_struct_literals() {
    let source = "(#struct Waker ((count #u64)))
      (#struct Pair ((left #u64) (right #u64)))
      (#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker Waker : function
        (#fn work () Pair
          (#let result Pair (#struct-literal Pair
            ((right (#await #u64 Child ChildPending ChildReady child-poll (Waiting 20u64)))
             (left (#await #u64 Child ChildPending ChildReady child-poll (Waiting 10u64))))))
          (#return result))))
      (#fn main () #u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let outcome Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready pair)
              (#u64.+.wrap (#get pair left) (#u64.*.wrap 2u64 (#get pair right))))
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 50);
}

#[test]
fn async_function_awaits_after_conditional_task_selection() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#enum Choice ((Small) (Large)))
      (#fn child-poll ((task Child) (waker (#ref Waker))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol choose-if-await : waker Waker : function
        (#fn choose-if ((large #bool)) #u64
          (#return (#if large
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 20u64))
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 10u64)))))))
      (@#async-fn (: protocol choose-match-await : waker Waker : function
        (#fn choose-match ((choice Choice)) #u64
          (#return (#match choice
            (#case Small (#await #u64 Child ChildPending ChildReady child-poll (Waiting 10u64)))
            (#case Large (#await #u64 Child ChildPending ChildReady child-poll (Waiting 20u64))))))))
      (#fn main () #u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let if-result Choose-if-poll-result
          (#call choose-if-poll (: task (#call choose-if (: large true)) : waker (#borrow waker))))
        (#let match-result Choose-match-poll-result
          (#call choose-match-poll (: task (#call choose-match (: choice Large)) : waker (#borrow waker))))
        (#let total #u64
          (#u64.+.wrap
            (#match if-result
              (#case (choose-if-ready value) value)
              (#case (choose-if-pending task) (#block (#forget task) (#unreachable))))
            (#match match-result
              (#case (choose-match-ready value) value)
              (#case (choose-match-pending task) (#block (#forget task) (#unreachable))))))
        (#forget waker)
        (#return total))";
    let generated = build_and_run_graph(source, 40);
    assert_single_poll(&generated, "choose-if-poll");
    assert_single_poll(&generated, "choose-match-poll");
    let small = source
        .replace("(: large true)", "(: large false)")
        .replace("(: choice Large)", "(: choice Small)");
    assert_ne!(small, source);
    build_and_run_graph(&small, 20);
}

#[test]
fn async_conditional_await_joins_with_an_immediate_value() {
    let source = "(#enum Child ((Waiting #u64)))
      (#struct Increment ((value #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((choose #bool)) #u64
          (#let result #u64
            (#if choose
              (#block
                (#let increment Increment
                  (#struct-literal Increment ((value 1u64))))
                (#let-mut awaited-value #u64
                  (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
                (#let second-value #u64
                  (#await #u64 Child ChildPending ChildReady child-poll (Waiting awaited-value)))
                (#u64.+.wrap second-value (#get increment value)))
              41u64))
          (#return result))))
      (#enum Choice (Await Immediate))
      (@#async-fn (: protocol work-match-await : waker #u64 : function
        (#fn work-match ((choice Choice)) #u64
          (#let result #u64
            (#match choice
              (#case Await
                (#block
                  (#let increment Increment
                    (#struct-literal Increment ((value 1u64))))
                  (#let-mut awaited-value #u64
                    (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
                  (#let second-value #u64
                    (#await #u64 Child ChildPending ChildReady child-poll (Waiting awaited-value)))
                  (#u64.+.wrap second-value (#get increment value))))
              (#case Immediate 41u64)))
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let awaited Work-poll-result
          (#call work-poll (: task (#call work (: choose true)) : waker (#borrow waker))))
        (#let awaited-value #u64
          (#match awaited
            (#case (work-ready value) value)
            (#case (work-pending awaited-child)
              (#match (#call work-poll (: task awaited-child : waker (#borrow waker)))
                (#case (work-ready awaited-ready) awaited-ready)
                (#case (work-pending awaited-again)
                  (#match (#call work-poll (: task awaited-again : waker (#borrow waker)))
                    (#case (work-ready awaited-third-ready) awaited-third-ready)
                    (#case (work-pending awaited-third) (#block (#forget awaited-third) (#unreachable)))))))))
        (#let immediate Work-poll-result
          (#call work-poll (: task (#call work (: choose false)) : waker (#borrow waker))))
        (#let immediate-value #u64
          (#match immediate
            (#case (work-ready immediate-ready) immediate-ready)
            (#case (work-pending immediate-task) (#block (#forget immediate-task) (#unreachable)))))
        (#let match-awaited Work-match-poll-result
          (#call work-match-poll (: task (#call work-match (: choice Await)) : waker (#borrow waker))))
        (#let match-awaited-value #u64
          (#match match-awaited
            (#case (work-match-ready value) value)
            (#case (work-match-pending match-child)
              (#match (#call work-match-poll (: task match-child : waker (#borrow waker)))
                (#case (work-match-ready match-ready) match-ready)
                (#case (work-match-pending match-again)
                  (#match (#call work-match-poll (: task match-again : waker (#borrow waker)))
                    (#case (work-match-ready match-third-ready) match-third-ready)
                    (#case (work-match-pending match-third) (#block (#forget match-third) (#unreachable)))))))))
        (#let match-immediate Work-match-poll-result
          (#call work-match-poll (: task (#call work-match (: choice Immediate)) : waker (#borrow waker))))
        (#let match-immediate-value #u64
          (#match match-immediate
            (#case (work-match-ready match-immediate-ready) match-immediate-ready)
            (#case (work-match-pending match-immediate-task)
              (#block (#forget match-immediate-task) (#unreachable)))))
        (#return (#u64.+.wrap
          (#u64.+.wrap awaited-value immediate-value)
          (#u64.+.wrap match-awaited-value match-immediate-value))))";
    let generated = build_and_run_graph(source, 86);
    assert_single_poll(&generated, "work-poll");
    assert_single_poll(&generated, "work-match-poll");
}

#[test]
fn async_conditional_branch_value_expressions_can_suspend() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady 41u64))))))
      (#fn add-one ((value #u64)) #u64
        (#return (#u64.+.wrap value 1u64)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((choose #bool)) #u64
          (#return (#call add-one (: value
            (#block
              (#if choose
                (#u64.+.wrap
                  (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
                  1u64)
                0u64))))))))
      (#enum Choice (Await Immediate))
      (@#async-fn (: protocol work-match-await : waker #u64 : function
        (#fn work-match ((choice Choice)) #u64
          (#return (#call add-one (: value
            (#match choice
              (#case Await
                (#u64.+.wrap
                  (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
                  1u64))
              (#case Immediate 0u64))))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let if-first Work-poll-result
          (#call work-poll (: task (#call work (: choose true)) : waker (#borrow waker))))
        (#let if-value #u64
          (#match if-first
            (#case (work-pending if-child)
              (#match (#call work-poll (: task if-child : waker (#borrow waker)))
                (#case (work-ready value) value)
                (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
            (#case (work-ready value) value)))
        (#let if-immediate Work-poll-result
          (#call work-poll (: task (#call work (: choose false)) : waker (#borrow waker))))
        (#let if-immediate-value #u64
          (#match if-immediate
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#let match-first Work-match-poll-result
          (#call work-match-poll (: task (#call work-match (: choice Await)) : waker (#borrow waker))))
        (#let match-value #u64
          (#match match-first
            (#case (work-match-pending match-child)
              (#match (#call work-match-poll (: task match-child : waker (#borrow waker)))
                (#case (work-match-ready value) value)
                (#case (work-match-pending unexpected) (#block (#forget unexpected) 0u64))))
            (#case (work-match-ready value) value)))
        (#let match-immediate Work-match-poll-result
          (#call work-match-poll (: task (#call work-match (: choice Immediate)) : waker (#borrow waker))))
        (#let match-immediate-value #u64
          (#match match-immediate
            (#case (work-match-ready value) value)
            (#case (work-match-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return (#u64.+.wrap
          (#u64.+.wrap if-value if-immediate-value)
          (#u64.+.wrap match-value match-immediate-value))))";
    let generated = build_and_run_graph(source, 88);
    assert_single_poll(&generated, "work-poll");
    assert_single_poll(&generated, "work-match-poll");
}

fn check_graph_conditional_capture(source: &str) {
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
    assert_frame_has_program_counter(&generated, "Work-task");

    // The original immediate child alone cannot establish retention across
    // Pending. Force a suspension and consume its returned task on the retry.
    let suspended = source
        .replace("(#enum Child ((Waiting #u64)))", "(#enum Child ((Waiting #u64) (Resuming #u64)))")
        .replace("(#case (Waiting value) (ChildReady value))", "(#case (Waiting value) (ChildPending (Resuming value)))\n          (#case (Resuming value) (ChildReady value))")
        .replace("(#case (work-pending pending) (#block (#forget pending) 0u64))", "(#case (work-pending pending)\n              (#match (#call work-poll (: task pending : waker (#borrow waker)))\n                (#case (work-ready resumed) resumed)\n                (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))");
    assert_ne!(suspended, source);
    build_and_run_graph(&suspended, 42);
    let unselected = suspended.replace("(#if true", "(#if false");
    assert_eq!(unselected.matches("ChildPoll\n        (#return").count(), 1);
    let unselected = unselected.replace(
        "ChildPoll\n        (#return",
        "ChildPoll\n        (#assert false)\n        (#return",
    );
    build_and_run_graph(&unselected, 0);

    // Graph capture storage must not erase the original explicit type check.
    let invalid = source.replace("40u64", "40u32");
    assert_ne!(invalid, source);
    let error = graph_compile_error(&invalid, "graph-conditional-capture-type");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    let span = error
        .span
        .expect("explicit capture type mismatch has a span");
    assert_eq!(&invalid[span.start..span.end], "40u32", "{error:?}");
}

#[test]
fn async_conditional_value_await_captures_typed_function_parameters() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((offset #u64)) #u64
          (#return (#if true
            (#u64.+.wrap
              (#await #u64 Child ChildPending ChildReady child-poll (Waiting 2u64))
              offset)
            0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: offset 40u64)))
        (#let result Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let value #u64
          (#match result
            (#case (work-ready value) value)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    check_graph_conditional_capture(source);
}

#[test]
fn async_conditional_value_await_captures_typed_local_bindings() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let offset #u64 40u64)
          (#return (#if true
            (#u64.+.wrap
              (#await #u64 Child ChildPending ChildReady child-poll (Waiting 2u64))
              offset)
            0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let result Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let value #u64
          (#match result
            (#case (work-ready value) value)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    check_graph_conditional_capture(source);
}

#[test]
fn async_conditional_continuations_can_change_result_type() {
    let source = "(#enum Step ((Waiting #u64) (Resuming #u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (Waiting value) (StepPending (Resuming value)))
          (#case (Resuming value) (StepReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((choose #bool)) #bool
          (#return (#if choose
            (#block
              (#let awaited #u64 (#await #u64 Step StepPending StepReady step-poll (Waiting 41u64)))
              (#u64.== awaited 41u64))
            false)))))
      (#fn run ((choose #bool) (waker (#ref #u64))) #u64
        (#let first Work-poll-result (#call work-poll (: task (#call work (: choose choose)) : waker waker)))
        (#let result #bool (#match first
          (#case (work-ready value) value)
          (#case (work-pending pending)
            (#match (#call work-poll (: task pending : waker waker))
              (#case (work-ready value) value)
              (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))))
        (#return (#if result 42u64 0u64)))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let selected #u64 (#call run (: choose true : waker (#borrow waker))))
        (#let skipped #u64 (#call run (: choose false : waker (#borrow waker))))
        (#assert (#u64.== skipped 0u64))
        (#forget waker)
        (#return selected))";
    build_and_run(source, 42);
    let expression = source.replace(
        "(#block\n              (#let awaited #u64 (#await #u64 Step StepPending StepReady step-poll (Waiting 41u64)))\n              (#u64.== awaited 41u64))",
        "(#u64.== (#await #u64 Step StepPending StepReady step-poll (Waiting 41u64)) 41u64)",
    );
    assert_ne!(expression, source);
    build_and_run(&expression, 42);
    let multiple = source.replace(
        "(#u64.== awaited 41u64)",
        "(#block (#let another #u64 (#await #u64 Step StepPending StepReady step-poll (Resuming awaited))) (#u64.== another 41u64))",
    );
    build_and_run(&multiple, 42);

    let linear = format!(
        "(#struct Token ((value #u64)))\n{}",
        source
            .replace(
                "(#fn work ((choose #bool)) #bool",
                "(#fn work ((choose #bool)) Token"
            )
            .replace(
                "(#u64.== awaited 41u64)",
                "(#struct-literal Token ((value (#u64.+.wrap awaited 1u64))))"
            )
            .replacen("false", "(#struct-literal Token ((value 0u64)))", 1)
            .replace("(#let result #bool", "(#let result Token")
            .replace(
                "(#return (#if result 42u64 0u64))",
                "(#let value #u64 (#get result value)) (#forget result) (#return value)"
            )
    );
    build_and_run(&linear, 42);

    let invalid = source.replace("false)))))", "0u64)))))");
    let scratch = support::Scratch::new("async-conditional-result-type");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("both conditional branches must agree on the result type");
    assert_eq!(error.code, lim::DiagnosticCode::Type);
    assert!(error.span.is_some(), "{error:?}");
    let borrowed = source
        .replace(
            "(#fn work ((choose #bool)) #bool",
            "(#fn work ((choose #bool) (view (#ref #u64))) (#ref #u64)",
        )
        .replace("(#u64.== awaited 41u64)", "view")
        .replacen("false", "view", 1)
        .replace(
            "(#fn run ((choose #bool) (waker (#ref #u64)))",
            "(#fn run ((choose #bool) (view (#ref #u64)) (waker (#ref #u64)))",
        )
        .replace(
            "(#call work (: choose choose))",
            "(#call work (: choose choose : view view))",
        )
        .replace("(#let result #bool", "(#let result (#ref #u64)")
        .replace(
            "(#return (#if result 42u64 0u64))",
            "(#return (#deref result))",
        )
        .replace(
            "(#let waker #u64 0u64)",
            "(#let waker #u64 0u64) (#let-mut storage #u64 42u64)",
        )
        .replace(
            ": choose true : waker",
            ": choose true : view (#borrow storage) : waker",
        )
        .replace(
            ": choose false : waker",
            ": choose false : view (#borrow storage) : waker",
        )
        .replace("(#u64.== skipped 0u64)", "(#u64.== skipped 42u64)");
    build_and_run(&borrowed, 42);
    let definitions = borrowed.split_once("(#fn main").unwrap().0;
    let suspended = format!("{definitions}
      (#fn main () #u64
        (#let-mut storage #u64 42u64)
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (: choose true : view (#borrow storage))) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        MUTATE_HERE
        (#forget pending)
        (#set storage 42u64)
        (#forget waker)
        (#return storage))");
    build_and_run(&suspended.replace("MUTATE_HERE", "()"), 42);
    let invalid = suspended.replace("MUTATE_HERE", "(#set storage 0u64)");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("borrowed.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("borrow-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("a suspended conditional result keeps its captured referent borrowed");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let span = error
        .span
        .expect("suspended-loan errors need the original assignment span");
    let assignment = invalid.find("(#set storage 0u64)").unwrap();
    assert!(
        span.start >= assignment && span.end <= assignment + "(#set storage 0u64)".len(),
        "{error:?}"
    );
    build_and_run(include_str!("../examples/async_branch_results.lim"), 42);
}

#[test]
fn async_conditional_block_continuation_captures_typed_locals() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#linear Child)
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((offset #u64)) #u64
          (#return (#if true
            (#block
              (#let result #u64
                (#await #u64 Child ChildPending ChildReady child-poll (Waiting 2u64)))
              (#u64.+.wrap result offset))
            0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (: offset 40u64)))
        (#let result Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let value #u64
          (#match result
            (#case (work-ready value) value)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("offset #u64"), "{generated}");
}

#[test]
fn async_conditional_choice_captures_and_releases_a_borrow_on_cancel() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (#fn cancel-child ((task Child)) () (#forget task) (#return ()))
      (@#async-fn (: protocol work-await : waker #u64
        : cancel (cancel-work ((await-0 cancel-child))) : function
        (#fn work ((choose #bool) (view (#ref #u64))) #u64
          (#let result #u64
            (#if choose
              (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
              41u64))
          (#return (#u64.+.wrap result (#deref view))))))
      (#fn main () #u64
        (#let-mut owner #u64 1u64)
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: choose true : view (#borrow owner)))
            : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        CHECK_HERE
        (#call cancel-work (: task (#call work-poll-cleanup (: task pending))))
        (#set owner 42u64)
        (#let immediate Work-poll-result
          (#call work-poll (: task (#call work (: choose false : view (#borrow owner)))
            : waker (#borrow waker))))
        (#let answer #u64
          (#match immediate
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget waker)
        (#return answer))";

    let rejected = source.replace("CHECK_HERE", "(#set owner 40u64)");
    let error = graph_compile_error(&rejected, "async-conditional-pending-borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );

    let accepted = source.replace("CHECK_HERE", "");
    let generated = build_and_run_graph(&accepted, 83);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_rejects_conditional_awaits_with_different_result_types() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64) (ChildAlternateReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (#fn child-poll-alt ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (ChildAlternateReady 2u64)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#return (#if true
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 1u64))
            (#await #u64 Child ChildPending ChildAlternateReady child-poll-alt (Waiting 2u64)))))))";
    let mismatched = source.replace(
        "#await #u64 Child ChildPending ChildAlternateReady child-poll-alt",
        "#await #u32 Child ChildPending ChildAlternateReady child-poll-alt",
    );
    let error = graph_compile_error(&mismatched, "async-conditional-await-contract");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error.message.contains("#await result type does not match"),
        "{error:?}"
    );
    let span = error.span.unwrap();
    assert_eq!(&mismatched[span.start..span.end], "#u32");
    assert_eq!(
        span.start,
        mismatched.rfind("#await").unwrap() + "#await ".len()
    );
}

#[test]
fn async_conditional_awaits_support_distinct_child_poll_protocols() {
    let source = "(#enum LeftChild ((LeftWaiting #u64)))
      (#enum LeftPoll ((LeftPending LeftChild) (LeftReady #u64)))
      (#fn left-poll ((task LeftChild) (waker (#ref #u64))) LeftPoll
        (#return (#match task
          (#case (LeftWaiting value)
            (#if (#u64.== value 0u64)
              (LeftPending (LeftWaiting 1u64))
              (LeftReady value))))))
      (#enum RightChild ((RightWaiting #u64)))
      (#enum RightPoll ((RightPending RightChild) (RightReady #u64)))
      (#fn right-poll ((task RightChild) (waker (#ref #u64))) RightPoll
        (#return (#match task (#case (RightWaiting value) (RightReady (#u64.+.wrap value 1u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((choose-left #bool)) #u64
          (#return (#if choose-left
            (#await #u64 LeftChild LeftPending LeftReady left-poll (LeftWaiting 0u64))
            (#await #u64 RightChild RightPending RightReady right-poll (RightWaiting 2u64)))))))
      (#enum Choice (Left Right))
      (@#async-fn (: protocol work-match-await : waker #u64 : function
        (#fn work-match ((choice Choice)) #u64
          (#return (#match choice
            (#case Left
              (#await #u64 LeftChild LeftPending LeftReady left-poll (LeftWaiting 0u64)))
            (#case Right
              (#await #u64 RightChild RightPending RightReady right-poll (RightWaiting 2u64))))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let left-first Work-poll-result
          (#call work-poll (: task (#call work (: choose-left true)) : waker (#borrow waker))))
        (#let left Work-poll-result
          (#match left-first
            (#case (work-pending task)
              (#call work-poll (: task task : waker (#borrow waker))))
            (#case (work-ready value) (work-ready value))))
        (#let left-value #u64
          (#match left
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#let right Work-poll-result
          (#call work-poll (: task (#call work (: choose-left false)) : waker (#borrow waker))))
        (#let right-value #u64
          (#match right
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#let matched Work-match-poll-result
          (#call work-match-poll (: task (#call work-match (: choice Right)) : waker (#borrow waker))))
        (#let matched-value #u64
          (#match matched
            (#case (work-match-ready value) value)
            (#case (work-match-pending task) (#block (#forget task) (#unreachable)))))
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
    let source = "(#struct Waker ((count #u64)))
      (#enum Step ((Waiting #u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (StepPending (Waiting 1u64))
              (StepReady count))))))
      (@#async-fn (: protocol read-after-await-await : waker Waker : function
        (#fn read-after-await ((view (#ref #u64))) #u64
          (#let result #u64
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
          (#return (#u64.+.wrap (#deref view) result)))))
      (#fn main () #u64
        (#let-mut owner #u64 37u64)
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Read-after-await-poll-result
          (#call read-after-await-poll (: task (#call read-after-await (: view (#borrow owner)))
            : waker (#borrow waker))))
        (#let-else (read-after-await-pending task) Read-after-await-poll-result first (#unreachable))
        MUTATE_WHILE_PENDING
        (#let second Read-after-await-poll-result
          (#call read-after-await-poll (: task task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (read-after-await-ready value) value)
            (#case (read-after-await-pending extra-task) (#block (#forget extra-task) (#unreachable)))))
        (#set owner 39u64)
        (#forget waker)
        (#return (#u64.+.wrap owner result)))";
    let accepted = source.replace("MUTATE_WHILE_PENDING", "");
    build_and_run_graph(&accepted, 77);

    let rejected = source.replace(
        "MUTATE_WHILE_PENDING",
        "(#set owner (#u64.+.wrap owner 1u64))",
    );
    let error = graph_compile_error(&rejected, "async-shared-external-pending-mutation");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("mutate") || error.contains("loan"),
        "{error}"
    );

    let escaping = accepted.replace(
        "(#fn main () #u64",
        "(#fn escape () Read-after-await-task\n          (#let owner #u64 3u64)\n          (#return (#call read-after-await (: view (#borrow owner)))))\n      (#fn main () #u64",
    );
    let error = graph_compile_error(&escaping, "async-shared-external-escape");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("local") || error.contains("outlive") || error.contains("borrow"),
        "{error}"
    );
}

#[test]
fn async_function_retains_mutable_external_borrows_across_pending() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Step ((Waiting #u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (StepPending (Waiting 1u64))
              (StepReady count))))))
      (@#async-fn (: protocol write-after-await-await : waker Waker : function
        (#fn write-after-await ((view (#ref-mut #u64))) #u64
          (#let result #u64
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
          (#deref-set view (#u64.+.wrap (#deref view) result))
          (#return (#deref view)))))
      (#fn main () #u64
        (#let-mut owner #u64 37u64)
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Write-after-await-poll-result
          (#call write-after-await-poll (: task (#call write-after-await (: view (#borrow-mut owner)))
            : waker (#borrow waker))))
        (#let-else (write-after-await-pending task) Write-after-await-poll-result first (#unreachable))
        READ_WHILE_PENDING
        (#let second Write-after-await-poll-result
          (#call write-after-await-poll (: task task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (write-after-await-ready value) value)
            (#case (write-after-await-pending extra-task) (#block (#forget extra-task) (#unreachable)))))
        (#set owner 39u64)
        (#return (#u64.+.wrap result owner)))";
    let accepted = source.replace("READ_WHILE_PENDING", "");
    build_and_run_graph(&accepted, 77);

    let rejected = source.replace("READ_WHILE_PENDING", "(#let snapshot #u64 owner)");
    let error = graph_compile_error(&rejected, "async-exclusive-external-pending-read");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn pinned_async_frame_retains_an_external_pinned_borrow_across_pending() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady count))))))
      (@#async-fn-pinned (: protocol read-after-await-await : waker #u64 : function
        (#fn read-after-await ((view (#pin-ref #u64))) #u64
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#return (#u64.+.wrap (#deref view) result)))))
      (#fn main () #u64
        (#let-mut owner #u64 40u64)
        (#let view (#pin-ref #u64) (#pin-borrow owner))
        (#let-mut frame Read-after-await-frame (#call read-after-await (: view view)))
        (#forget view)
        (#let waker #u64 0u64)
        (#let first Read-after-await-poll-result
          (#call read-after-await-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (read-after-await-pending pinned-frame) Read-after-await-poll-result first (#unreachable))
        (#let second Read-after-await-poll-result
          (#call read-after-await-poll (: task pinned-frame : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (read-after-await-ready value) value)
            (#case (read-after-await-pending unexpected)
              (#block (#forget unexpected) (#unreachable)))))
        (#forget frame)
        (#set owner 41u64)
        (#forget waker)
        (#return (#if (#u64.== result 41u64) owner 0u64)))";

    let mutation_while_pending = source.replace(
        "        (#let second Read-after-await-poll-result",
        "        (#set owner 99u64)\n        (#let second Read-after-await-poll-result",
    );
    let error = graph_compile_error(
        &mutation_while_pending,
        "async-pinned-external-pending-mutation",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("pinned") || error.contains("access"),
        "a suspended pinned frame must keep its external owner borrowed: {error}"
    );

    let generated = build_and_run_graph(source, 41);
    assert!(generated.contains("(#pin-ref #u64)"), "{generated}");
}

#[test]
fn cancelling_a_pending_async_frame_releases_its_external_mutable_borrow() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Step ((Waiting #u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count) (StepPending (Waiting count))))))
      (#fn cancel-step ((task Step)) () (#forget task) (#return ()))
      (@#async-fn (: protocol work-await : waker Waker
        : cancel (cancel-work ((await-0 cancel-step))) : function
        (#fn work ((view (#ref-mut #u64))) #u64
          (#let result #u64
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
          (#return (#deref view)))))
      (#fn main () #u64
        (#let-mut owner #u64 37u64)
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: view (#borrow-mut owner)))
            : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        WHILE_PENDING
        (#call cancel-work (: task (#call work-poll-cleanup (: task pending))))
        (#set owner 42u64)
        (#return owner))";
    let accepted = source.replace("WHILE_PENDING", "");
    build_and_run_graph(&accepted, 42);

    let rejected = source.replace("WHILE_PENDING", "(#set owner 40u64)");
    let error = graph_compile_error(&rejected, "async-cancel-exclusive-borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );

    let shared = source
        .replace("#ref-mut", "#ref")
        .replace("#borrow-mut owner", "#borrow owner");
    let accepted = shared.replace("WHILE_PENDING", "");
    build_and_run_graph(&accepted, 42);
    let rejected = shared.replace("WHILE_PENDING", "(#set owner 40u64)");
    let error = graph_compile_error(&rejected, "async-cancel-shared-borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn async_function_carries_mutable_locals_across_pending_resume() {
    let source = "(#struct Waker ((count #u64)))
      (#enum Step ((Waiting #u64)))
      (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref Waker))) StepPoll
        (#return (#match task
          (#case (Waiting count)
            (#if (#u64.== count 0u64)
              (StepPending (Waiting 1u64))
              (StepReady count))))))
      (@#async-fn (: protocol work-await : waker Waker : function
        (#fn work ((#mut initial #u64)) #u64
          (#set initial (#u64.+.wrap initial 1u64))
          (#let-mut total #u64 initial)
          (#let-mut result #u64
            (#await Step StepPending StepReady step-poll (Waiting 0u64)))
          (#set result (#u64.+.wrap result 0u64))
          (#set total (#u64.+.wrap total result))
          (#return total))))
      (#fn main () #u64
        (#let waker Waker (#struct-literal Waker ((count 0u64))))
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: initial 2u64)) : waker (#borrow waker))))
        (#let-else (work-pending first-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task first-task : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 4);
    assert_single_poll(&generated, "work-poll");
    // Mutability belongs to the source body, not its capture-only constructor.
    assert_generated_signature(&generated, "(#fn work ((initial #u64)) Work-task)");
}

#[test]
fn async_function_rejects_assignment_to_immutable_capture() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll (#return (ChildReady 1u64)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let total #u64 2u64)
          (#let result #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#set total result)
          (#return result))))";
    let error = graph_compile_error(source, "async-immutable-capture");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error
            .message
            .contains("cannot assign to immutable variable 'total'"),
        "{error:?}"
    );
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "total");
}

#[test]
fn async_function_lowers_await_in_terminal_binding_block() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task (#case (Waiting value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#return (#if true
            (#block
              (#let task-input #u64 17u64)
              (#let result #u64
                (#await #u64 Child ChildPending ChildReady child-poll (Waiting task-input)))
              result)
            0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let outcome Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value #u64
          (#match outcome
            (#case (work-ready ready) ready)
            (#case (work-pending task) (#block (#forget task) (#unreachable)))))
        (#forget waker)
        (#return value))";
    let generated = build_and_run_graph(source, 17);
    assert_single_poll(&generated, "work-poll");
    // A source input consumed before poll must not become a cancellation slot.
    assert!(
        !generated.contains("Work-task-cleanup-task-input"),
        "{generated}"
    );
}

#[test]
fn async_function_resumes_a_child_await_inside_a_while_loop() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#while (#u64.< iteration 2u64)
            (#let child-input #u64 iteration)
            (#let result #u64
              (#await Child ChildPending ChildReady child-poll (Waiting child-input)))
            (#set iteration (#u64.+.wrap iteration 1u64)))
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(&source, 2);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_while_body_suspends_inside_a_call_argument() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@#cell #u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting #u64)))
         (#linear ChildTask)
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
         (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
           (#return (#match task
             (#case (Waiting remaining)
               (#if (#u64.== remaining 0u64)
                 (ChildPending (Waiting 1u64))
                 (ChildReady 42u64))))))
         (@#async-fn (: protocol work-await : waker #u64 : function
           (#fn work ((cell (#ref CellU64))) #u64
             (#let-mut iteration #u64 0u64)
             (#while (#u64.< iteration 1u64)
               (#call CellU64-set (: cell cell : value
                 (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64))))
               (#set iteration (#u64.+.wrap iteration 1u64)))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () #u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker #u64 0u64)
           (#let task Work-task (#call work (: cell (#borrow cell))))
           (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
           (#let-else (work-pending pending) Work-poll-result first (#unreachable))
           (#let before #u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
           (#let result #u64
             (#match second
               (#case (work-ready value) value)
               (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#u64.== result 42u64))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_for_body_suspends_inside_a_call_argument() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@#cell #u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting #u64)))
         (#linear ChildTask)
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
         (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
           (#return (#match task
             (#case (Waiting remaining)
               (#if (#u64.== remaining 0u64)
                 (ChildPending (Waiting 1u64))
                 (ChildReady 42u64))))))
         (@#async-fn (: protocol work-await : waker #u64 : function
           (#fn work ((cell (#ref CellU64))) #u64
             (#for (#let-mut iteration #u64 0u64)
                   (#u64.< iteration 1u64)
                   (#set iteration (#u64.+.wrap iteration 1u64))
               (#call CellU64-set (: cell cell : value
                 (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () #u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker #u64 0u64)
           (#let task Work-task (#call work (: cell (#borrow cell))))
           (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
           (#let-else (work-pending pending) Work-poll-result first (#unreachable))
           (#let before #u64 (#call CellU64-get (: cell (#borrow cell))))
           (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
           (#let result #u64
             (#match second
               (#case (work-ready value) value)
               (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
           (#forget waker)
           (#forget cell)
           (#return (#if (#bool.&& (#u64.== before 0u64)
                                  (#u64.== result 42u64))
                         42u64 0u64)))",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_function_resumes_a_child_await_in_a_while_condition() {
    let source = include_str!("../examples/async_fn_while_condition.lim");
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_block_owned_labeled_loop_keeps_its_scope_across_suspension() {
    let source = include_str!("../examples/async_block_loop.lim");
    build_and_run(source, 42);
    let returned = source.replace("(#let result #u64", "(#return").replace(
        "total))\n    ; The inner scope has ended; this is an independent declaration.\n    (#let index #u64 0u64)\n    (#return (#u64.+.wrap result index)))))",
        "total)))))",
    );
    build_and_run(&returned, 42);
    let outer_mutation = source.replace(
        "(#let result #u64\n      (#block\n        (#let-mut index #u64 0u64)\n        (#let-mut total #u64 40u64)",
        "(#let-mut total #u64 40u64)\n    (#let result #u64\n      (#block\n        (#let-mut index #u64 0u64)",
    ).replace("(#u64.+.wrap result index)", "(#u64.+.wrap result (#u64.-.wrap total 40u64))");
    build_and_run(&outer_mutation, 44);
    build_and_run(
        &outer_mutation.replace("(StepPending (Resume value))", "(StepReady value)"),
        44,
    );
    build_and_run(
        &outer_mutation.replace("(#await #u64 Step", "(#await Step"),
        44,
    );
    build_and_run(
        &outer_mutation
            .replace("(#u64.< index 2u64)", "false")
            .replace("(StepPending (Resume value))", "(#panic)"),
        40,
    );
    let borrowed_update = format!(
        "(#fn increment ((target (#ref-mut #u64)) (value #u64)) ()
        (#deref-set target (#u64.+.wrap (#deref target) value)) (#return ()))\n{}",
        outer_mutation.replace(
            "(#set total (#u64.+.wrap total value))",
            "(#call increment (: target (#borrow-mut total) : value value))"
        )
    );
    build_and_run(&borrowed_update, 44);
    let linear = format!("(#struct Counter ((value #u64))) (#linear Counter)\n{}", outer_mutation
        .replace("(#let-mut total #u64 40u64)", "(#let-mut total Counter (#struct-literal Counter (: value 40u64)))")
        .replace("(#set total (#u64.+.wrap total value))", "(#set-field total value (#u64.+.wrap (#get total value) value))")
        .replace("total))\n    ;", "(#get total value)))\n    ;")
        .replace("(#return (#u64.+.wrap result (#u64.-.wrap total 40u64)))", "(#let answer #u64 (#u64.+.wrap result (#u64.-.wrap (#get total value) 40u64))) (#forget total) (#return answer)"));
    build_and_run(&linear, 44);
    let scratch = support::Scratch::new("async-block-loop-scope");
    let error_for = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    let missing_cleanup = error_for(&linear.replace("(#forget total)", "()"));
    assert!(
        missing_cleanup.message.contains("total") && missing_cleanup.message.contains("consum"),
        "{missing_cleanup:?}"
    );
    let out_of_scope = error_for(&source.replace("(#let index #u64 0u64)", "()"));
    assert!(
        out_of_scope.message.contains("index") && out_of_scope.message.contains("unknown"),
        "{out_of_scope:?}"
    );
    let immutable = error_for(&outer_mutation.replace("(#let-mut total #u64", "(#let total #u64"));
    assert!(
        immutable.message.contains("total") && immutable.message.contains("mutable"),
        "{immutable:?}"
    );
}

#[test]
fn async_labeled_while_continues_to_its_label_after_body_await() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut index #u64 0u64)
          (#label outer
            (#while (#u64.< index 2u64)
              (#let ignored #u64
                (#await #u64 ChildTask ChildPending ChildReady child-poll (Waiting index)))
              (#set index (#u64.+.wrap index 1u64))
              (#continue-to outer)))
          (#return index))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending first-frame) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-frame : waker (#borrow waker))))
        (#let-else (work-pending second-frame) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task second-frame : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    build_and_run(source, 2);
}

#[test]
fn async_while_condition_sequences_short_circuit_awaits() {
    let source = "(#enum BoolTask ((Waiting #bool) (Resuming #bool)))
      (#linear BoolTask)
      (#enum BoolPoll ((BoolPending BoolTask) (BoolReady #bool)))
      (#fn bool-poll ((task BoolTask) (waker (#ref #u64))) BoolPoll
        (#return (#match task
          (#case (Waiting value) (BoolPending (Resuming value)))
          (#case (Resuming value) (BoolReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iterations #u64 0u64)
          (#while (#bool.&&
            (#await #bool BoolTask BoolPending BoolReady bool-poll (Waiting true))
            (#await #bool BoolTask BoolPending BoolReady bool-poll (Waiting true)))
            (#set iterations (#u64.+.wrap iterations 1u64))
            (#break))
          (#return iterations))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending after-first) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task after-first : waker (#borrow waker))))
        (#let-else (work-pending after-second) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task after-second : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 1);
    assert!(generated.contains("choice-"), "{generated}");
}

#[test]
fn async_while_condition_keeps_global_names_out_of_frame_captures() {
    let source = "(#const fallback #bool false)
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while
            (#if (#bool.&&
                (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting 0u64))
                (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting 0u64)))
              true
              fallback)
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-frame) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-frame : waker (#borrow waker))))
        (#let-else (work-pending second-frame) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task second-frame : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    let runtime = source.split_once("(@#async-fn").unwrap().0;
    let parsed = lim::parse_program(&format!("{runtime}\n{generated}")).unwrap();
    assert!(
        parsed.items.iter().all(|item| match item {
            lim::Item::Struct { fields, .. } => fields.iter().all(|field| field.name != "fallback"),
            _ => true,
        }),
        "globals must not become frame captures: {generated}"
    );
    assert!(parsed.items.iter().any(|item| matches!(item,
        lim::Item::Function(function) if function.name == "work" && function.parameters.is_empty()
    )), "global reads must not add factory arguments: {generated}");
    let fallback = source
        .replace("(ChildReady true)", "(ChildReady false)")
        .replace(
            "(#let-else (work-pending second-frame) Work-poll-result second (#unreachable))",
            "",
        )
        .replace(
            "(#let third Work-poll-result (#call work-poll (: task second-frame : waker (#borrow waker))))",
            "(#let third Work-poll-result second)",
        );
    build_and_run_graph(&fallback, 42);
    let static_fallback = fallback
        .replace(
            "(#const fallback #bool false)",
            "(#static fallback #bool false)",
        )
        .replace(
            "              fallback)",
            "              (#unsafe fallback))",
        );
    build_and_run_graph(&static_fallback, 42);
    let safe_static = static_fallback.replace("(#unsafe fallback)", "fallback");
    let error = graph_compile_error(&safe_static, "async-safe-static-read");
    assert_eq!(error.code, lim::DiagnosticCode::Unsafe, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&safe_static[span.start..span.end], "fallback");
    let invalid_source = source
        .replace(
            "(#const fallback #bool false)",
            "(#const unrelated #bool false)",
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
    let source = "(#enum ConditionTask ((Waiting #u64)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ConditionPending (Waiting 1u64))
              (ConditionReady true))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting iteration))
            (#set iteration (#u64.+.wrap iteration 1u64))
            (#match iteration
              (#case 2u64 (#break))
              (#case _ (#continue))))
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let result Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let value #u64 (#match result
          (#case (work-ready ready) ready)
          (#case (work-pending pending-again) (#block (#forget pending-again) 0u64))))
        (#forget waker)
        (#return (#if (#u64.== value 2u64) 42u64 0u64)))";
    build_and_run(source, 42);
}

#[test]
fn awaited_while_condition_and_body_resume_in_source_order() {
    let source = "(#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady true)))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input #u64)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll ConditionWaiting)
            (#let value #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting input)))
            (#assert (#u64.== value input))
            (#break))
          (#return input))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (: input 42u64)) : waker (#borrow waker))))
        (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (work-pending body-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task body-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("condition-body-task"), "{generated}");
    assert!(generated.contains("wait-condition"), "{generated}");
    assert!(generated.contains("wait-body"), "{generated}");

    let conditional_source = source.replace(
        "(#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting input))",
        "(#if true\n                (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting input))\n                42u64)",
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
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (ConditionReady false)))
      (#enum BodyTask (BodyStart))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#unreachable)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll ConditionStart)
            (#let value #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll BodyStart))
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value #u64
          (#match result
            (#case (work-ready ready) ready)
            (#case (work-pending unexpected)
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
    let source = "(#struct Resource ((value #u64)))
      (#linear Resource)
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady true)))))
      (#enum BodyTask ((BodyWaiting Resource)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting resource) (BodyPending (BodyWaiting resource))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((resource Resource)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll ConditionWaiting)
            (#let value #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting resource)))
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
    let source = "(#enum Child ((Waiting #bool) (Resuming #bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#await Child ChildPending ChildReady child-poll (Waiting decision))
            (#return 7u64))
          (#return 0u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-pending) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result (#call work-poll (: task true-pending : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-second (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-pending) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result (#call work-poll (: task false-pending : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    let generated = build_and_run(source, 7);
    assert!(
        generated.contains("(#if Lim.async.work.choice-0"),
        "{generated}"
    );

    let explicitly_typed = source.replace("#while (#await Child", "#while (#await #bool Child");
    assert_ne!(explicitly_typed, source);
    build_and_run(&explicitly_typed, 7);

    let wrong_result_type = source.replace("#while (#await Child", "#while (#await #u64 Child");
    let error = lim::parse_program(&wrong_result_type).unwrap_err();
    assert!(
        error.contains("result type does not match loop condition")
            && error.contains("found #u64, expected #bool"),
        "{error}"
    );
}

#[test]
fn async_while_body_returns_after_a_composed_awaited_condition() {
    let source = "(#enum Child ((Waiting #bool) (Resuming #bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#enum TailTask ((TailWaiting #u64) (TailResuming #u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref #u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#if decision
                    (#await #bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
            (#return 7u64))
          (#let fallback #u64
            (#await #u64 TailTask TailPending TailReady tail-poll (TailWaiting 3u64)))
          (#return fallback))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-pending) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result (#call work-poll (: task true-pending : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-second (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-pending) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result (#call work-poll (: task false-pending : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_fall_through_to_another_iteration() {
    let source = "(#enum Child ((Waiting #bool) (Resuming #bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#let-mut first #bool true)
          (#while (#if decision
                    (#await #bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
            (#if first
              (#block (#set first false) ())
              (#return 7u64)))
          (#let fallback #u64 3u64)
          (#return fallback))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-pending) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result (#call work-poll (: task true-pending : waker (#borrow waker))))
        (#let-else (work-pending true-pending-again) Work-poll-result true-second (#unreachable))
        (#let true-third Work-poll-result (#call work-poll (: task true-pending-again : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-third (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-first (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_skip_a_direct_awaited_tail() {
    let source = "(#enum Child ((Waiting #bool) (Resuming #bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#enum TailTask ((TailWaiting #u64) (TailResuming #u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref #u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#let-mut first #bool true)
          (#while (#if decision
                    (#await #bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
          (#if first
              (#block (#set first false) ())
              (#return 7u64)))
          (#return (#await #u64 TailTask TailPending TailReady tail-poll
            (TailWaiting 3u64))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-pending) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result (#call work-poll (: task true-pending : waker (#borrow waker))))
        (#let-else (work-pending true-pending-again) Work-poll-result true-second (#unreachable))
        (#let true-third Work-poll-result (#call work-poll (: task true-pending-again : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-third (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-pending) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result (#call work-poll (: task false-pending : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_suspend_post_loop_continuation() {
    let source = "(#enum Child ((Waiting #bool) (Resuming #bool)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #bool)))
      (#enum TailTask ((TailWaiting #u64) (TailResuming #u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting decision) (ChildPending (Resuming decision)))
          (#case (Resuming decision) (ChildReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref #u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#let-mut first #bool true)
          (#while (#if decision
                    (#await #bool Child ChildPending ChildReady child-poll (Waiting true))
                    false)
            (#if first
              (#block (#set first false) ())
              (#return 7u64)))
          (#let fallback #u64
            (#await #u64 TailTask TailPending TailReady tail-poll (TailWaiting 3u64)))
          (#return fallback))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-pending) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result (#call work-poll (: task true-pending : waker (#borrow waker))))
        (#let-else (work-pending true-pending-again) Work-poll-result true-second (#unreachable))
        (#let true-third Work-poll-result (#call work-poll (: task true-pending-again : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-third (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-pending) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result (#call work-poll (: task false-pending : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_early_return_can_skip_a_nested_awaited_tail() {
    let source = "(#enum ConditionTask ((Waiting #bool) (Resuming #bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#enum TailTask ((TailWaiting #u64) (TailResuming #u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady #u64)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting decision) (ConditionPending (Resuming decision)))
          (#case (Resuming decision) (ConditionReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref #u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting decision))
            (#return 7u64))
          (#return (#u64.+.wrap
            (#await #u64 TailTask TailPending TailReady tail-poll (TailWaiting 3u64))
            2u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-pending) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result (#call work-poll (: task true-pending : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-second (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-pending) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result (#call work-poll (: task false-pending : waker (#borrow waker))))
        (#let-else (work-pending false-tail-pending) Work-poll-result false-second (#unreachable))
        (#let false-third Work-poll-result (#call work-poll (: task false-tail-pending : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-third (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 12);
}

#[test]
fn async_while_early_return_can_skip_a_direct_awaited_tail() {
    let source = "(#enum ConditionTask ((Waiting #bool) (Resuming #bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#enum TailTask ((TailWaiting #u64) (TailResuming #u64)))
      (#linear TailTask)
      (#enum TailPoll ((TailPending TailTask) (TailReady #u64)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting decision) (ConditionPending (Resuming decision)))
          (#case (Resuming decision) (ConditionReady decision)))))
      (#fn tail-poll ((task TailTask) (waker (#ref #u64))) TailPoll
        (#return (#match task
          (#case (TailWaiting value) (TailPending (TailResuming value)))
          (#case (TailResuming value) (TailReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting decision))
            (#return 7u64))
          (#return (#await #u64 TailTask TailPending TailReady tail-poll
            (TailWaiting 3u64))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-pending) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result (#call work-poll (: task true-pending : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-second (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-pending) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result (#call work-poll (: task false-pending : waker (#borrow waker))))
        (#let-else (work-pending false-tail-pending) Work-poll-result false-second (#unreachable))
        (#let false-third Work-poll-result (#call work-poll (: task false-tail-pending : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-third (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    build_and_run(source, 10);
}

#[test]
fn async_while_body_can_return_after_body_await() {
    let source = "(#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let body-value #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting 13u64)))
            (#return body-value))
          (#return 5u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-after-condition) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result
          (#call work-poll (: task true-after-condition : waker (#borrow waker))))
        (#let-else (work-pending true-after-body-start) Work-poll-result true-second (#unreachable))
        (#let true-third Work-poll-result
          (#call work-poll (: task true-after-body-start : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-third (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-after-condition) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result
          (#call work-poll (: task false-after-condition : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    let generated = build_and_run(source, 18);
    assert!(generated.contains("choice"), "{generated}");

    let linear_source = source
        .replace(
            "(#enum ConditionTask",
            "(#struct Payload ((value #u64)))\n      (#linear Payload)\n      (#enum ConditionTask",
        )
        .replace(
            "(#fn work ((decision #bool)) #u64",
            "(#fn work ((decision #bool)) Payload",
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
            "(#let true-value #u64 (#get true-result value))\n\
             (#let false-value #u64 (#get false-result value))\n\
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
      (#struct Payload ((value #u64)))
      (#linear Payload)
      (#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((#mut decision #bool)) Payload
          (#let-mut payload Payload
            (#struct-literal Payload ((value 1u64))))
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let first #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll
                (BodyWaiting 1u64)))
            (#let second #u64
            (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting first)))
            (#let replacement Payload
              (#struct-literal Payload ((value (#u64.+.wrap second 1u64)))))
            (#forget payload)
            (#set payload replacement)
            (#set decision false))
          (#return payload))))
      (#fn cancel-body-start ((task (#tuple #bool Payload))) ()
        (#let (#tuple decision payload) (#tuple #bool Payload) task)
        (#forget payload) (#return ()))
      (#fn cancel-body-await-0 ((task (#tuple #bool Payload BodyTask))) ()
        (#let (#tuple decision payload child) (#tuple #bool Payload BodyTask) task)
        (#forget payload) (#forget child) (#return ()))
      (#fn cancel-body-await-1 ((task (#tuple #bool Payload BodyTask))) ()
        (#let (#tuple decision payload child) (#tuple #bool Payload BodyTask) task)
        (#forget payload) (#forget child) (#return ()))
      (@#task-cancel cancel-body Lim.async.work.choice-0-body-frame
        ((Lim.async.work.choice-0-body-frame-start cancel-body-start ((decision #bool) (payload Payload)))
         (Lim.async.work.choice-0-body-frame-await-0 cancel-body-await-0 ((decision #bool) (payload Payload) (child BodyTask)))
         (Lim.async.work.choice-0-body-frame-await-1 cancel-body-await-1 ((decision #bool) (payload Payload) (child BodyTask)))))
      (#fn cancel-condition-wait ((task (#tuple ConditionTask #bool Payload))) ()
        (#let (#tuple child decision payload) (#tuple ConditionTask #bool Payload) task)
        (#forget child) (#forget payload) (#return ()))
      (#fn cancel-body-wait ((task (#tuple Lim.async.work.choice-0-body-frame))) ()
        (#let (#tuple child) (#tuple Lim.async.work.choice-0-body-frame) task)
        (#call cancel-body (: task child)) (#return ()))
      (@#task-cancel cancel-condition-body Lim.async.work.choice-2-condition-body-task
        ((Lim.async.work.choice-2-wait-condition cancel-condition-wait ((child ConditionTask) (decision #bool) (payload Payload)))
         (Lim.async.work.choice-2-wait-body cancel-body-wait ((child Lim.async.work.choice-0-body-frame)))))
      (#fn cancel-run-start ((task (#tuple #bool Payload #bool))) ()
        (#let (#tuple decision payload stopped) (#tuple #bool Payload #bool) task)
        (#forget payload) (#return ()))
      (#fn cancel-run-wait ((task (#tuple #bool #bool Lim.async.work.choice-2-condition-body-task))) ()
        (#let (#tuple decision stopped child) (#tuple #bool #bool Lim.async.work.choice-2-condition-body-task) task)
        (#call cancel-condition-body (: task child)) (#return ()))
      (@#task-cancel cancel-run Lim.async.work.choice-13-task
        ((Lim.async.work.choice-13-start cancel-run-start ((decision #bool) (payload Payload) (stopped #bool)))
         (Lim.async.work.choice-13-wait cancel-run-wait ((decision #bool) (stopped #bool) (child Lim.async.work.choice-2-condition-body-task)))))
      (#fn cancel-frame-start ((task (#tuple #bool))) ()
        (#let (#tuple decision) (#tuple #bool) task) (#return ()))
      (#fn cancel-frame-await ((task (#tuple Lim.async.work.choice-13-task))) ()
        (#let (#tuple child) (#tuple Lim.async.work.choice-13-task) task)
        (#call cancel-run (: task child)) (#return ()))
      (@#task-cancel cancel-frame Work-task
        ((work-task-start cancel-frame-start ((decision #bool)))
         (work-task-await-0 cancel-frame-await ((child Lim.async.work.choice-13-task)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (: decision true)) : waker (#borrow waker))))
        (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (work-pending first-body-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task first-body-pending : waker (#borrow waker))))
        (#let-else (work-pending second-body-pending) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result (#call work-poll (: task second-body-pending : waker (#borrow waker))))
        (#let-else (work-pending final-condition-pending) Work-poll-result fourth (#unreachable))
        (#let fifth Work-poll-result (#call work-poll (: task final-condition-pending : waker (#borrow waker))))
        (#let-else (work-ready payload) Work-poll-result fifth (#unreachable))
        (#let result #u64 (#get payload value))
        (#forget payload)
        (#let cancel-first Work-poll-result
          (#call work-poll (: task (#call work (: decision true)) : waker (#borrow waker))))
        (#let-else (work-pending cancel-pending-first) Work-poll-result cancel-first (#unreachable))
        (#let cancel-second Work-poll-result
          (#call work-poll (: task cancel-pending-first : waker (#borrow waker))))
        (#let-else (work-pending cancel-pending-second) Work-poll-result cancel-second (#unreachable))
        (#call cancel-frame (: task cancel-pending-second))
        (#forget waker)
        (#return result))"
        .replace("{}", env!("CARGO_MANIFEST_DIR"));
    let generated = build_and_run(&source, 2);
    assert!(generated.contains("Payload"), "{generated}");

    let returning_source = source.replace("(#set decision false)", "(#return payload)");
    let (prefix, _) = returning_source
        .split_once("(#fn cancel-body-start")
        .expect("cancellation helpers follow the async declaration");
    let returning_source = format!(
        "{prefix}(#fn main () #u64
          (#let waker #u64 0u64)
          (#let task Work-task (#call work (: decision true)))
          (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending after-condition) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task after-condition : waker (#borrow waker))))
          (#let-else (work-pending after-first) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task after-first : waker (#borrow waker))))
          (#let-else (work-pending after-second) Work-poll-result third (#unreachable))
          (#let fourth Work-poll-result (#call work-poll (: task after-second : waker (#borrow waker))))
          (#let-else (work-ready payload) Work-poll-result fourth (#unreachable))
          (#let result #u64 (#get payload value))
          (#forget payload)
          (#forget waker)
          (#return (#if (#u64.== result 2u64) 42u64 0u64)))"
    );
    build_and_run(&returning_source, 42);
}

#[test]
fn async_suspending_while_body_can_return_after_setup() {
    let source = "(#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let setup #u64 13u64)
            (#let value #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting setup)))
            (#return value))
          (#return 5u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-after-condition) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result
          (#call work-poll (: task true-after-condition : waker (#borrow waker))))
        (#let-else (work-pending true-after-body) Work-poll-result true-second (#unreachable))
        (#let true-third Work-poll-result
          (#call work-poll (: task true-after-body : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-third (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-after-condition) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result
          (#call work-poll (: task false-after-condition : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-second (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap true-result false-result)))";
    let generated = build_and_run(source, 18);
    assert!(generated.contains("choice"), "{generated}");
}

#[test]
fn async_suspending_while_body_can_return_after_multiple_awaits() {
    let source = "(#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let setup #u64 13u64)
            (#let first #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting setup)))
            (#let second #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll
                (BodyWaiting (#u64.+.wrap first 1u64))))
            (#return (#u64.+.wrap first second)))
          (#return 5u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let true-task Work-task (#call work (: decision true)))
        (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
        (#let-else (work-pending true-after-condition) Work-poll-result true-first (#unreachable))
        (#let true-second Work-poll-result
          (#call work-poll (: task true-after-condition : waker (#borrow waker))))
        (#let-else (work-pending true-after-first) Work-poll-result true-second (#unreachable))
        (#let true-third Work-poll-result
          (#call work-poll (: task true-after-first : waker (#borrow waker))))
        (#let-else (work-pending true-after-second) Work-poll-result true-third (#unreachable))
        (#let true-fourth Work-poll-result
          (#call work-poll (: task true-after-second : waker (#borrow waker))))
        (#let-else (work-ready true-result) Work-poll-result true-fourth (#unreachable))
        (#let false-task Work-task (#call work (: decision false)))
        (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-after-condition) Work-poll-result false-first (#unreachable))
        (#let false-second Work-poll-result
          (#call work-poll (: task false-after-condition : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-second (#unreachable))
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
    let source = "(#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value) (BodyReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#let first #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting 20u64)))
            (#let second #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll
                (BodyWaiting (#u64.+.wrap first 7u64))))
            (#return (#u64.+.wrap first second)))
          (#return 5u64))))
      (#fn run ((decision #bool) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: decision decision)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#let-else (work-pending after-condition) Work-poll-result first (#unreachable))
        (#return (#if decision
          (#block
            (#let second Work-poll-result (#call work-poll (: task after-condition : waker waker)))
            (#let-else (work-pending after-first-body) Work-poll-result second (#unreachable))
            (#let third Work-poll-result (#call work-poll (: task after-first-body : waker waker)))
            (#let-else (work-pending after-second-body) Work-poll-result third (#unreachable))
            (#let fourth Work-poll-result (#call work-poll (: task after-second-body : waker waker)))
            (#let-else (work-ready result) Work-poll-result fourth (#unreachable))
            result)
          (#block
            (#let second Work-poll-result (#call work-poll (: task after-condition : waker waker)))
            (#let-else (work-ready result) Work-poll-result second (#unreachable))
            result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let returned #u64 (#call run (: decision true : waker (#borrow waker))))
        (#let skipped #u64 (#call run (: decision false : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap returned skipped)))";
    build_and_run(source, 52);
}

#[test]
fn async_awaited_while_body_returns_from_both_if_branches() {
    let source = "(#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool) (pick #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#if pick (#return 13u64) (#return 17u64)))
          (#return 5u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first-task Work-task (#call work (: decision true : pick true)))
        (#let first-poll Work-poll-result (#call work-poll (: task first-task : waker (#borrow waker))))
        (#let-else (work-pending first-pending) Work-poll-result first-poll (#unreachable))
        (#let first-ready Work-poll-result (#call work-poll (: task first-pending : waker (#borrow waker))))
        (#let-else (work-ready first-result) Work-poll-result first-ready (#unreachable))
        (#let second-task Work-task (#call work (: decision true : pick false)))
        (#let second-poll Work-poll-result (#call work-poll (: task second-task : waker (#borrow waker))))
        (#let-else (work-pending second-pending) Work-poll-result second-poll (#unreachable))
        (#let second-ready Work-poll-result (#call work-poll (: task second-pending : waker (#borrow waker))))
        (#let-else (work-ready second-result) Work-poll-result second-ready (#unreachable))
        (#let false-task Work-task (#call work (: decision false : pick true)))
        (#let false-poll Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
        (#let-else (work-pending false-pending) Work-poll-result false-poll (#unreachable))
        (#let false-ready Work-poll-result (#call work-poll (: task false-pending : waker (#borrow waker))))
        (#let-else (work-ready false-result) Work-poll-result false-ready (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap
          (#u64.+.wrap first-result second-result) false-result)))";
    build_and_run(source, 35);
}

#[test]
fn async_awaited_while_body_returns_from_match_arms() {
    let source = "(#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool) (pick #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#block
              (#let offset #u64 1u64)
              (#match pick
                (#case true (#return (#u64.+.wrap 12u64 offset)))
                (#case false (#return (#u64.+.wrap 16u64 offset))))))
          (#return 5u64))))
      (#fn drive ((decision #bool) (pick #bool) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: decision decision : pick pick)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker waker)))
        (#return (#match second
          (#case (work-ready result) result)
          (#case (work-pending still-pending)
            (#block (#forget still-pending) 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first-result #u64
          (#call drive (: decision true : pick true : waker (#borrow waker))))
        (#let second-result #u64
          (#call drive (: decision true : pick false : waker (#borrow waker))))
        (#let false-result #u64
          (#call drive (: decision false : pick true : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap
          (#u64.+.wrap first-result second-result) false-result)))";
    build_and_run(source, 35);
}

#[test]
fn async_awaited_while_return_branch_and_break_branch_diverge_correctly() {
    let source = "(#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting decision)
            (ConditionPending (ConditionResuming decision)))
          (#case (ConditionResuming decision) (ConditionReady decision)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((decision #bool) (leave-body #bool)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (ConditionWaiting decision))
            (#block
              (#let return-value #u64 13u64)
              (#if leave-body (#return return-value) (#break))))
          (#return 5u64))))
      (#fn drive ((decision #bool) (leave-body #bool) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: decision decision : leave-body leave-body)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker waker)))
        (#return (#match second
          (#case (work-ready result) result)
          (#case (work-pending still-pending)
            (#block (#forget still-pending) 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let returned #u64
          (#call drive (: decision true : leave-body true : waker (#borrow waker))))
        (#let broken #u64
          (#call drive (: decision true : leave-body false : waker (#borrow waker))))
        (#let condition-false #u64
          (#call drive (: decision false : leave-body true : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap (#u64.+.wrap returned broken) condition-false)))";
    build_and_run(source, 23);
}

#[test]
fn async_awaited_while_return_branch_and_continue_branch_resume_correctly() {
    let source = "(#enum ConditionTask ((Waiting #u64) (Resuming #u64)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting iteration) (ConditionPending (Resuming iteration)))
          (#case (Resuming iteration)
            (ConditionReady (#u64.== iteration 0u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((should-return #bool)) #u64
          (#let-mut iteration #u64 0u64)
          (#while (#await ConditionTask ConditionPending ConditionReady
                    condition-poll (Waiting iteration))
            (#if should-return
              (#return 13u64)
              (#block
                (#set iteration 1u64)
                (#continue))))
          (#return 5u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let return-task Work-task (#call work (: should-return true)))
        (#let first Work-poll-result (#call work-poll (: task return-task : waker (#borrow waker))))
        (#let-else (work-pending after-return-first) Work-poll-result first (#unreachable))
        (#let return-ready Work-poll-result
          (#call work-poll (: task after-return-first : waker (#borrow waker))))
        (#let-else (work-ready returned) Work-poll-result return-ready (#unreachable))
        (#let continue-task Work-task (#call work (: should-return false)))
        (#let continue-first Work-poll-result
          (#call work-poll (: task continue-task : waker (#borrow waker))))
        (#let-else (work-pending after-continue-first) Work-poll-result continue-first (#unreachable))
        (#let continue-second Work-poll-result
          (#call work-poll (: task after-continue-first : waker (#borrow waker))))
        (#let-else (work-pending after-continue-second) Work-poll-result continue-second (#unreachable))
        (#let continue-ready Work-poll-result
          (#call work-poll (: task after-continue-second : waker (#borrow waker))))
        (#let-else (work-ready continued) Work-poll-result continue-ready (#unreachable))
        (#forget waker)
        (#return (#u64.+.wrap returned continued)))";
    build_and_run(source, 18);

    let linear_source = source
        .replace(
            "(#enum ConditionTask",
            "(#struct Payload ((value #u64)))\n      (#linear Payload)\n      (#enum ConditionTask",
        )
        .replace(
            "(#fn work ((should-return #bool)) #u64",
            "(#fn work ((should-return #bool)) Payload",
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
            "(#let returned-value #u64 (#get returned value))\n\
             (#let continued-value #u64 (#get continued value))\n\
             (#forget returned)\n\
             (#forget continued)\n\
             (#return (#u64.+.wrap returned-value continued-value))",
        );
    let generated = build_and_run(&linear_source, 18);
    assert!(
        generated.contains("#linear Lim.async.work.choice"),
        "{generated}"
    );
}

#[test]
fn async_while_let_awaits_each_scrutinee_until_the_pattern_stops_matching() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ChildTask ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady Maybe)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting stage)
            (#if (#u64.== stage 0u64)
              (ChildPending (Waiting 1u64))
              (#if (#u64.== stage 1u64)
                (ChildReady (Some 10u64))
                (ChildReady None)))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#while-let (Some payload)
            (#await Maybe ChildTask ChildPending ChildReady child-poll
              (Waiting (#if (#u64.== iteration 0u64) 0u64 2u64)))
            (#set iteration payload))
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-frame) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-frame : waker (#borrow waker))))
        (#let value #u64 (#match second
          (#case (work-ready result) result)
          (#case (work-pending pending-frame) (#block (#forget pending-frame) 0u64))))
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
fn async_while_let_can_suspend_only_in_its_body() {
    let source = r#"
      (#enum Value ((Some #u64) None))
      (#fn next-value ((counter (#ref-mut #u64))) Value
        (#let index #u64 (#deref counter))
        (#deref-set counter (#u64.+.wrap index 1u64))
        (#return (#match index
          (#case 0u64 (Some 20u64))
          (#case 1u64 (Some 22u64))
          (#case _ None))))
      (#enum BodyTask ((Start #u64) (Resume #u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (Start value) (BodyPending (Resume value)))
          (#case (Resume value) (BodyReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut counter #u64 0u64)
          (#let-mut total #u64 0u64)
          (#while-let (Some amount) (#call next-value (: counter (#borrow-mut counter)))
            (#let result #u64 (#await BodyTask BodyPending BodyReady body-poll (Start amount)))
            (#set total (#u64.+.wrap total result)))
          (#assert (#u64.== counter 3u64))
          (#return total))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work ()) : waker (#borrow waker))))
        (#let-else (work-pending first-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-task : waker (#borrow waker))))
        (#let-else (work-pending second-task) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task second-task : waker (#borrow waker))))
        (#return (#match third
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
    "#;
    build_and_run(source, 42);
    build_and_run(include_str!("../examples/async_while_let_body.lim"), 42);
    let prefix = source.split_once("(#fn main () #u64").unwrap().0;
    let never_matches = format!(
        r#"{}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work ()) : waker (#borrow waker))))
        (#let value #u64 (#match first
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#assert (#u64.== value 0u64))
        (#return 42u64))
    "#,
        prefix.replace(
            "(#let-mut counter #u64 0u64)",
            "(#let-mut counter #u64 2u64)"
        )
    );
    build_and_run(&never_matches, 42);
}

#[test]
fn async_while_let_synchronous_reference_payload_survives_body_suspension() {
    let source = r#"
      (#enum Value ((Some (#ref #u64)) None))
      (#enum BodyTask (Start Resume))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady ())))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case Start (BodyPending Resume))
          (#case Resume (BodyReady ())))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((owner (#ref #u64))) #u64
          (#let current Value (Some owner))
          (#let-mut result #u64 0u64)
          (#while-let (Some reference) current
            (#let ready () (#await () BodyTask BodyPending BodyReady body-poll Start))
            (#set result (#deref reference))
            (#break))
          (#return result))))
      (#fn main () #u64
        (#let-mut owner #u64 42u64)
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (: owner (#borrow owner))) : waker (#borrow waker))))
        (#let-else (work-pending task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#return (#match second
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
    "#;
    build_and_run(source, 42);
    let invalid = source.replace(
        "(#let second Work-poll-result",
        "(#set owner 43u64) (#let second Work-poll-result",
    );
    let scratch = support::Scratch::new("async-sync-while-let-borrow");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("borrow"), "{error:?}");
    let span = error
        .span
        .expect("owner mutation must retain its source span");
    let write = invalid.find("(#set owner 43u64)").unwrap();
    assert!(
        span.start >= write && span.end <= write + "(#set owner 43u64)".len(),
        "{error:?}"
    );
    let cancelled = format!(
        r#"{}
      (#fn main () #u64
        (#let-mut owner #u64 42u64)
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (: owner (#borrow owner))) : waker (#borrow waker))))
        (#let-else (work-pending task) Work-poll-result first (#unreachable))
        (#forget task)
        (#set owner 43u64)
        (#return owner))
    "#,
        source.split_once("(#fn main () #u64").unwrap().0
    );
    build_and_run(&cancelled, 43);
}

#[test]
fn async_while_let_sequences_awaits_in_its_scrutinee_expression() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while-let true
            (#bool.&&
              (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting 42u64))
              (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting 42u64)))
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-frame) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-frame : waker (#borrow waker))))
        (#let-else (work-pending second-frame) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task second-frame : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("expression-frame"), "{generated}");
}

#[test]
fn async_for_condition_sequences_awaits_in_a_value_expression() {
    let source = "(#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for (#let-mut index #u64 0u64)
            (#bool.&&
              (#u64.< index 1u64)
              (#bool.&&
                (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting index))
                (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting index))))
            (#set index (#u64.+.wrap index 1u64))
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-frame) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-frame : waker (#borrow waker))))
        (#let-else (work-pending second-frame) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task second-frame : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_while_let_body_can_suspend_multiple_times_after_matching() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady (Some 42u64))))))
      (#enum BodyTask (BodyWaiting BodyResuming))
      (#linear BodyTask)
      (#fn start-body-task () BodyTask (#return BodyWaiting))
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case BodyWaiting (BodyPending BodyResuming))
          (#case BodyResuming (BodyReady 7u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady
              condition-poll ConditionWaiting)
            (#let first #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll
                (#call start-body-task (:))))
            (#let second #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll
                (#call start-body-task (:))))
            (#assert (#u64.== first second))
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (work-pending body-first-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result
          (#call work-poll (: task body-first-pending : waker (#borrow waker))))
        (#let-else (work-pending body-second-pending) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result
          (#call work-poll (: task body-second-pending : waker (#borrow waker))))
        (#let result #u64
          (#match fourth
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
    assert!(generated.contains("body-poll.dispatch"), "{generated}");

    let linear_source = source.replace(
        "(#enum Maybe ((Some #u64) None))",
        "(#enum Maybe ((Some #u64) None))\n      (#linear Maybe)",
    );
    let generated = build_and_run(&linear_source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
}

#[test]
fn async_while_let_suspends_in_a_nested_body_statement() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ConditionTask (ConditionWaiting))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#forget task)
        (#return (ConditionReady (Some 42u64))))
      (#enum BodyTask (BodyWaiting BodyResuming))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case BodyWaiting (BodyPending BodyResuming))
          (#case BodyResuming (BodyReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady
              condition-poll ConditionWaiting)
            (#assert (#await #bool BodyTask BodyPending BodyReady body-poll BodyWaiting))
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending-frame) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending-frame : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
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
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#forget task)
        (#assert false)
        (#return (ChildReady None)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while-let Some
            (#if false
              (#await Maybe ChildTask ChildPending ChildReady child-poll Waiting)
              None)
            (#assert false))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let outcome Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-ready value) 42u64)
            (#case (work-pending unexpected)
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
            "        (#let outcome Work-poll-result\n          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))",
            "        (#let first Work-poll-result\n          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))\n        (#let-else (work-pending pending) Work-poll-result first (#unreachable))\n        (#let outcome Work-poll-result\n          (#call work-poll (: task pending : waker (#borrow waker))))",
        );
    build_and_run(&pending_source, 42);
}

#[test]
fn async_await_preserves_boolean_short_circuiting() {
    let source = format!(
        "(#import \"{}/library/cell.lim\")
         (@#cell #u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting (#ref CellU64))))
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
         (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
           (#return (#match task
             (#case (Waiting cell)
               (#block
                 (#call CellU64-set (: cell cell : value
                   (#u64.+.wrap (#call CellU64-get (: cell cell)) 1u64)))
                 (ChildReady true))))))
         (@#async-fn (: protocol work-await : waker #u64 : function
           (#fn work ((cell (#ref CellU64))) #u64
             (#let ignored #bool
               (#bool.&& false
                 (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting cell))))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () #u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker #u64 0u64)
           (#let result Work-poll-result
             (#call work-poll (: task (#call work (: cell (#borrow cell))) : waker (#borrow waker))))
           (#let value #u64 (#match result
             (#case (work-ready ready) ready)
             (#case (work-pending pending) (#block (#forget pending) 1u64))))
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
         (@#cell #u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum ChildTask ((Waiting (#ref CellU64))))
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
         (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
           (#return (#match task
             (#case (Waiting cell)
               (#block
                 (#call CellU64-set (: cell cell : value
                   (#u64.+.wrap (#call CellU64-get (: cell cell)) 1u64)))
                 (ChildReady true))))))
         (@#async-fn (: protocol work-await : waker #u64 : function
           (#fn work ((cell (#ref CellU64))) #u64
             (#let ignored #bool
               (#match true
                 (#case true (#when false)
                   (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting cell)))
                 (#case _ false)))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () #u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker #u64 0u64)
           (#let result Work-poll-result
             (#call work-poll (: task (#call work (: cell (#borrow cell))) : waker (#borrow waker))))
           (#let value #u64 (#match result
             (#case (work-ready ready) ready)
             (#case (work-pending pending) (#block (#forget pending) 1u64))))
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
         (@#cell #u64 CellU64 CellU64-create CellU64-get CellU64-set)
         (#enum Maybe ((Some #u64) None))
         (#enum ChildTask ((Waiting (#ref CellU64))))
         (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
         (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
           (#return (#match task
             (#case (Waiting cell)
               (#block
                 (#call CellU64-set (: cell cell : value
                   (#u64.+.wrap (#call CellU64-get (: cell cell)) 1u64)))
                 (ChildReady true))))))
         (@#async-fn (: protocol work-await : waker #u64 : function
           (#fn work ((maybe Maybe) (cell (#ref CellU64))) #u64
             (#let ignored #bool
               (#if-let (Some payload) maybe
                 (#await #bool ChildTask ChildPending ChildReady child-poll (Waiting cell))
                 false))
             (#return (#call CellU64-get (: cell cell))))))
         (#fn main () #u64
           (#let cell CellU64 (#call CellU64-create (: value 0u64)))
           (#let waker #u64 0u64)
           (#let result Work-poll-result
             (#call work-poll (: task (#call work (: maybe None : cell (#borrow cell))) : waker (#borrow waker))))
           (#let value #u64 (#match result
             (#case (work-ready ready) ready)
             (#case (work-pending pending) (#block (#forget pending) 1u64))))
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
    let source = "(#struct State ((value #u64)))
      (#linear State)
      (#struct Token ((limit #u64)))
      (#linear Token)
      (#enum ChildPoll ((ChildPending #u64) (ChildReady #u64)))
      (#fn child-poll ((task #u64) (waker (#ref #u64))) ChildPoll
        (#return (#if (#u64.== task 0u64)
          (ChildPending 1u64)
          (ChildReady task))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut state State (#struct-literal State ((value 0u64))))
          (#let token Token (#struct-literal Token ((limit 3u64))))
          (#while (#u64.< (#get state value) (#get token limit))
            (#let result #u64
              (#await #u64 ChildPending ChildReady child-poll (#get state value)))
            (#let next-value #u64 (#u64.+.wrap result 1u64))
            (#forget state)
            (#set state (#struct-literal State
              ((value next-value)))))
          (#return (#block
            (#let value #u64 (#get state value))
            (#forget state)
            (#forget token)
            value)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let cancel-frame Work-task (#call work (:)))
        (#let cancel-first Work-poll-result (#call work-poll (: task cancel-frame : waker (#borrow waker))))
        (#let-else (work-pending cancelled-task) Work-poll-result cancel-first (#unreachable))
        (#forget cancelled-task)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending pending-again)
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
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for-range (iteration #u64) 0u64 2u64
            (#let result #u64
              (#await Child ChildPending ChildReady child-poll (Waiting iteration))))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending pending-again)
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
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case Waiting (BodyPending Resuming))
          (#case Resuming (BodyReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for-range (iteration #u64) 0u64 2u64
            (#assert (#await #bool BodyTask BodyPending BodyReady body-poll Waiting))
            (#if (#u64.== iteration 0u64)
              (#continue)
              (#break)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-pending : waker (#borrow waker))))
        (#let-else (work-pending second-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task second-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
}

#[test]
fn async_for_range_awaits_bounds_in_source_order_before_iterating() {
    let source = "(#enum Child ((Waiting #u64) (Resuming #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for-range (iteration #u64)
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64))
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 2u64))
            (#assert (#u64.< iteration 3u64)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task first-pending : waker (#borrow waker))))
        (#let-else (work-pending second-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result
          (#call work-poll (: task second-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert!(!generated.contains("(#await"), "{generated}");
}

#[test]
fn range_bounds_are_once_with_side_effects_and_labeled_continue() {
    build_and_run(include_str!("../examples/range_bounds_once.lim"), 42);
    let source = include_str!("../examples/async_range_bounds_once.lim");
    build_and_run(source, 42);
    build_and_run_graph(source, 42);
    let immediate = source.replace("(ChildPending (Resume value))", "(ChildReady value)");
    build_and_run(&immediate, 42);
    build_and_run_graph(&immediate, 42);
    let breaking = source
        .replace("(#continue-to counting)", "(#break-to counting)")
        .replace("total 39u64", "total 42u64");
    build_and_run(&breaking, 42);
    build_and_run_graph(&breaking, 42);
}

#[test]
fn async_for_range_composes_awaited_bounds_with_awaited_body() {
    let source = "(#enum Child ((BoundWaiting #u64) (BoundResuming #u64) (Body #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (BoundWaiting value) (ChildPending (BoundResuming value)))
          (#case (BoundResuming value) (ChildReady value))
          (#case (Body value) (ChildReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for-range (iteration #u64)
            (#await #u64 Child ChildPending ChildReady child-poll (BoundWaiting 0u64))
            (#await #u64 Child ChildPending ChildReady child-poll (BoundWaiting 2u64))
            (#let result #u64
              (#await Child ChildPending ChildReady child-poll (Body iteration))))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task first-pending : waker (#borrow waker))))
        (#let-else (work-pending second-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result
          (#call work-poll (: task second-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert!(generated.contains("BoundWaiting"), "{generated}");
    assert!(generated.contains("Body"), "{generated}");
}

#[test]
fn async_function_resumes_child_await_inside_for_with_existing_counter() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady value))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for (#set iteration 0u64)
                (#u64.< iteration 2u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#let result #u64
              (#await Child ChildPending ChildReady child-poll (Waiting iteration))))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_for_condition_can_await_and_step_only_after_ready_true() {
    let source = "(#enum ChildTask ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady (#u64.< value 2u64)))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for (#set iteration 0u64)
                (#await ChildTask ChildPending ChildReady child-poll (Waiting iteration))
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#assert true))
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let value #u64 (#match second
          (#case (work-ready result) result)
          (#case (work-pending pending-again) (#block (#forget pending-again) 0u64))))
        (#forget waker)
        (#return (#if (#u64.== value 2u64) 42u64 0u64)))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_for_condition_can_suspend_with_an_awaited_step() {
    let source = "(#enum ConditionTask ((Waiting #u64) (Resuming #u64)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting iteration) (ConditionPending (Resuming iteration)))
          (#case (Resuming iteration)
            (ConditionReady (#u64.< iteration 1u64))))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting iteration) (BodyPending (BodyResuming iteration)))
          (#case (BodyResuming iteration) (BodyReady true)))))
      (#enum StepTask ((StepWaiting #u64 #bool) (StepResuming #u64 #bool)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady #u64)))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (StepWaiting iteration body-ran)
            (#block (#assert body-ran)
              (StepPending (StepResuming iteration body-ran))))
          (#case (StepResuming iteration body-ran)
            (#block (#assert body-ran)
              (StepReady (#u64.+.wrap iteration 1u64)))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for (#set iteration 0u64)
                (#await ConditionTask ConditionPending ConditionReady
                  condition-poll (Waiting iteration))
                (#set iteration
                  (#await #u64 StepTask StepPending StepReady step-poll
                    (StepWaiting iteration body-ran)))
            (#let body-ran #bool true))
          (#return (#if (#u64.== iteration 1u64) 42u64 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (work-pending step-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task step-pending : waker (#borrow waker))))
        (#let-else (work-pending resumed-condition) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result (#call work-poll (: task resumed-condition : waker (#borrow waker))))
        (#let result #u64
          (#match fourth
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");

    let three_phase_source = source
        .replace(
            "(#let-mut iteration #u64 0u64)",
            "(#let-mut iteration #u64 0u64)\n          (#let-mut total #u64 0u64)",
        )
        .replace(
            "(#let body-ran #bool true)",
            "(#let body-ran #bool\n              (#await #bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#set total (#u64.+.wrap total 1u64))",
        )
        .replace(
            "(#return (#if (#u64.== iteration 1u64) 42u64 0u64))",
            "(#return (#if (#u64.== iteration 1u64)\n            (#if (#u64.== total 1u64) 42u64 0u64)\n            0u64))",
        );
    let (prefix, _) = three_phase_source.split_once("(#fn main () #u64").unwrap();
    let three_phase_source = format!(
        "{prefix}(#fn main () #u64
          (#let waker #u64 0u64)
          (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
          (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task condition-pending : waker (#borrow waker))))
          (#let-else (work-pending body-pending) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task body-pending : waker (#borrow waker))))
          (#let-else (work-pending step-pending) Work-poll-result third (#unreachable))
          (#let fourth Work-poll-result (#call work-poll (: task step-pending : waker (#borrow waker))))
          (#let-else (work-pending resumed-condition) Work-poll-result fourth (#unreachable))
          (#let fifth Work-poll-result (#call work-poll (: task resumed-condition : waker (#borrow waker))))
          (#let result #u64
            (#match fifth
              (#case (work-ready value) value)
              (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result))"
    );
    let generated = build_and_run_graph(&three_phase_source, 42);
    assert_single_poll(&generated, "work-poll");

    let shared_reference_source = three_phase_source
        .replace(
            "(#fn work () #u64",
            "(#fn work ((view (#ref #u64))) #u64",
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
        .split_once("(#fn main () #u64")
        .unwrap();
    let shared_reference_source = format!(
        "{prefix}(#fn main () #u64
          (#let-mut owner #u64 41u64)
          (#let waker #u64 0u64)
          (#let task Work-task (#call work (: view (#borrow owner))))
          (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result (#call work-poll (: task condition-pending : waker (#borrow waker))))
          (#let-else (work-pending body-pending) Work-poll-result second (#unreachable))
          (#let third Work-poll-result (#call work-poll (: task body-pending : waker (#borrow waker))))
          (#let-else (work-pending step-pending) Work-poll-result third (#unreachable))
          (#let fourth Work-poll-result (#call work-poll (: task step-pending : waker (#borrow waker))))
          (#let-else (work-pending resumed-condition) Work-poll-result fourth (#unreachable))
          (#let fifth Work-poll-result (#call work-poll (: task resumed-condition : waker (#borrow waker))))
          (#let result #u64
            (#match fifth
              (#case (work-ready value) value)
              (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
          (#set owner 43u64)
          (#forget waker)
          (#return (#if (#u64.== result 42u64)
            (#if (#u64.== owner 43u64) 42u64 0u64) 0u64)))"
    );
    let generated = build_and_run_graph(&shared_reference_source, 42);
    assert_single_poll(&generated, "work-poll");

    let mutation_before_poll = shared_reference_source.replace(
        "(#let task Work-task (#call work (: view (#borrow owner))))",
        "(#let task Work-task (#call work (: view (#borrow owner))))\n          (#set owner 42u64)",
    );
    let error = graph_compile_error(
        &mutation_before_poll,
        "async-for-phase-mutation_before_poll",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );

    let mutation_while_pending = shared_reference_source.replace(
        "(#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))",
        "(#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))\n          (#set owner 42u64)",
    );
    let error = graph_compile_error(
        &mutation_while_pending,
        "async-for-phase-mutation_while_pending",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the external shared loan must remain live while the composed task is work-pending: {error}"
    );

    let mutable_reference_source = shared_reference_source
        .replace(
            "(#fn work ((view (#ref #u64)))",
            "(#fn work ((view (#ref-mut #u64)))",
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
    let generated = build_and_run_graph(&mutable_reference_source, 42);
    assert_single_poll(&generated, "work-poll");

    let multi_await_source = mutable_reference_source.replace(
        "(#let body-ran #bool\n              (#await #bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#deref-set view 42u64)\n            (#set total (#u64.+.wrap total 1u64))",
        "(#let body-ran #bool\n              (#await #bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#let second-body-ran #bool\n              (#await #bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#let third-body-ran #bool\n              (#await #bool BodyTask BodyPending BodyReady body-poll\n                (BodyWaiting iteration)))\n            (#deref-set view 42u64)\n            (#set total (#u64.+.wrap total 1u64))",
    );
    let (prefix, _) = multi_await_source.split_once("(#fn main () #u64").unwrap();
    let mut poll_chain = "(#block (#forget pending-7) 0u64)".to_owned();
    for index in (0..7).rev() {
        let task = if index == 0 {
            "(#call work (: view (#borrow-mut owner)))".to_owned()
        } else {
            format!("pending-{index}")
        };
        let next = index + 1;
        poll_chain = format!(
            "(#match (#call work-poll (: task {task} : waker (#borrow waker)))\n\
               (#case (work-pending pending-{next}) {poll_chain})\n\
               (#case (work-ready ready-{index}) ready-{index}))"
        );
    }
    let multi_await_source = format!(
        "{prefix}(#fn main () #u64\n\
          (#let-mut owner #u64 41u64)\n\
          (#let waker #u64 0u64)\n\
          (#let result #u64 {poll_chain})\n\
          (#set owner 43u64)\n\
          (#forget waker)\n\
          (#return (#if (#u64.== owner 43u64) result 0u64)))"
    );
    let generated = build_and_run_graph(&multi_await_source, 42);
    assert_single_poll(&generated, "work-poll");
    let (prefix, _) = multi_await_source.split_once("(#fn main () #u64").unwrap();
    let cancel_source = format!(
        "{prefix}(#fn main () #u64
          (#let-mut owner #u64 41u64)
          (#let waker #u64 0u64)
          (#let task Work-task (#call work (: view (#borrow-mut owner))))
          (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result
            (#call work-poll (: task condition-pending : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result second (#unreachable))
          (#forget pending)
          (#set owner 43u64)
          (#forget waker)
          (#return owner))"
    );
    build_and_run_graph(&cancel_source, 43);
    let mutation_while_pending = cancel_source.replace(
        "          (#forget pending)",
        "          (#set owner 42u64)\n          (#forget pending)",
    );
    let error = graph_compile_error(
        &mutation_while_pending,
        "async-for-phase-mutation_while_pending",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the multi-await body must retain the transferred exclusive loan while work-pending: {error}"
    );

    let (prefix, _) = mutable_reference_source
        .split_once("(#fn main () #u64")
        .unwrap();
    let cancelled_mutable_reference = format!(
        "{prefix}(#fn main () #u64
          (#let-mut owner #u64 41u64)
          (#let waker #u64 0u64)
          (#let task Work-task (#call work (: view (#borrow-mut owner))))
          (#let first Work-poll-result
            (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#forget pending)
          (#set owner 42u64)
          (#forget waker)
          (#return (#if (#u64.== owner 42u64) 42u64 0u64)))"
    );
    let generated = build_and_run_graph(&cancelled_mutable_reference, 42);
    assert_single_poll(&generated, "work-poll");

    let pinned_reference_source = shared_reference_source
        .replace("(view (#ref #u64))", "(view (#pin-ref-mut #u64))")
        .replace("(#borrow owner)", "(#pin-borrow-mut owner)");
    let generated = build_and_run_graph(&pinned_reference_source, 42);
    assert_single_poll(&generated, "work-poll");
    let (prefix, _) = pinned_reference_source
        .split_once("(#fn main () #u64")
        .unwrap();
    let cancelled_pinned_reference = format!(
        "{prefix}(#fn main () #u64
          (#let-mut owner #u64 41u64)
          (#let view (#pin-ref-mut #u64) (#pin-borrow-mut owner))
          (#let waker #u64 0u64)
          (#let task Work-task (#call work (: view view)))
          (#let first Work-poll-result
            (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#forget pending)
          (#set owner 42u64)
          (#forget waker)
          (#return (#if (#u64.== owner 42u64) 42u64 0u64)))"
    );
    let generated = build_and_run_graph(&cancelled_pinned_reference, 42);
    assert_single_poll(&generated, "work-poll");

    let mutation_while_pending = mutable_reference_source.replace(
        "(#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))",
        "(#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))\n          (#set owner 42u64)",
    );
    let error = graph_compile_error(
        &mutation_while_pending,
        "async-for-phase-mutation_while_pending",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the external exclusive loan must remain live while the composed task is work-pending: {error}"
    );
}

#[test]
fn async_for_three_phase_transfers_preserve_continue_break_and_return() {
    let source = "(#enum ConditionTask ((Waiting #u64) (Resuming #u64)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (Waiting iteration) (ConditionPending (Resuming iteration)))
          (#case (Resuming iteration)
            (ConditionReady (#u64.< iteration 2u64))))))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #bool)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting iteration) (BodyPending (BodyResuming iteration)))
          (#case (BodyResuming iteration) (BodyReady true)))))
      (#enum StepTask ((StepWaiting #u64) (StepResuming #u64)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady #u64)))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (StepWaiting iteration)
            (#block (#assert (#u64.== iteration 0u64))
              (StepPending (StepResuming iteration))))
          (#case (StepResuming iteration)
            (#block (#assert (#u64.== iteration 0u64))
              (StepReady (#u64.+.wrap iteration 1u64)))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for (#set iteration 0u64)
                (#await ConditionTask ConditionPending ConditionReady
                  condition-poll (Waiting iteration))
                (#set iteration
                  (#await #u64 StepTask StepPending StepReady step-poll
                    (StepWaiting iteration)))
            (#let body-ran #bool
              (#await #bool BodyTask BodyPending BodyReady body-poll
                (BodyWaiting iteration)))
            (#if (#u64.== iteration 0u64) (#continue) (#break)))
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task first-pending : waker (#borrow waker))))
        (#let-else (work-pending second-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task second-pending : waker (#borrow waker))))
        (#let-else (work-pending third-pending) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result (#call work-poll (: task third-pending : waker (#borrow waker))))
        (#let-else (work-pending fourth-pending) Work-poll-result fourth (#unreachable))
        (#let fifth Work-poll-result (#call work-poll (: task fourth-pending : waker (#borrow waker))))
        (#let-else (work-pending fifth-pending) Work-poll-result fifth (#unreachable))
        (#let sixth Work-poll-result (#call work-poll (: task fifth-pending : waker (#borrow waker))))
        (#let result #u64
          (#match sixth
            (#case (work-ready value) value)
            (#case (work-pending sixth-pending)
              (#block
                (#let seventh Work-poll-result
                  (#call work-poll (: task sixth-pending : waker (#borrow waker))))
                (#match seventh
                  (#case (work-ready value) value)
                  (#case (work-pending unexpected)
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
    let (prefix, _) = return_source.split_once("(#fn main () #u64").unwrap();
    let mut poll_chain = "(#block (#forget pending-8) 0u64)".to_owned();
    for index in (0..8).rev() {
        let task = if index == 0 {
            "(#call work (:))".to_owned()
        } else {
            format!("pending-{index}")
        };
        poll_chain = format!(
            "(#match (#call work-poll (: task {task} : waker (#borrow waker)))
              (#case (work-pending pending-{next}) {poll_chain})
              (#case (work-ready ready-{index}) ready-{index}))",
            next = index + 1,
        );
    }
    let return_source = format!(
        "{prefix}(#fn main () #u64
          (#let waker #u64 0u64)
          (#let result #u64 {poll_chain})
          (#forget waker)
          (#return result))"
    );
    let generated = build_and_run(&return_source, 42);
    assert!(generated.contains("iteration-function"), "{generated}");

    let linear_prefix = prefix
        .replace(
            "(#enum ConditionTask",
            "(#struct Payload ((value #u64)))\n      (#linear Payload)\n      (#enum ConditionTask",
        )
        .replace("(#fn work () #u64", "(#fn work () Payload")
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
            "(#match (#call work-poll (: task {task} : waker (#borrow waker)))
              (#case (work-pending pending-{next}) {linear_poll_chain})
              (#case (work-ready ready-{index})
                (#block
                  (#let result #u64 (#get ready-{index} value))
                  (#forget ready-{index})
                  result)))",
            next = index + 1,
        );
    }
    let linear_return_source = format!(
        "{linear_prefix}(#fn main () #u64
          (#let waker #u64 0u64)
          (#let result #u64 {linear_poll_chain})
          (#forget waker)
          (#return result))"
    );
    let generated = build_and_run(&linear_return_source, 42);
    assert!(generated.contains("#linear Lim.async.work"), "{generated}");
    assert_generated_type_names_are_capitalized(&generated);
}

#[test]
fn async_for_condition_awaits_only_the_selected_branch_each_iteration() {
    let source = "(#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut should-await #bool true)
          (#for ()
                (#bool.&& should-await
                  (#await #bool ChildTask ChildPending ChildReady child-poll
                    Waiting))
                (#set should-await false)
            (#assert true))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "work-poll");
}

#[test]
fn async_loop_short_circuit_conditions_do_not_poll_unselected_awaits() {
    let source = "(#enum ChildTask (Waiting))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#linear ChildPoll)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#forget task)
        (#assert false)
        (#return (ChildReady true)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while
            (#bool.&& false
              (#await #bool ChildTask ChildPending ChildReady child-poll Waiting))
            (#assert false))
          (#for ()
                (#bool.|| true
                  (#await #bool ChildTask ChildPending ChildReady child-poll Waiting))
                ()
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let value #u64
          (#match result
            (#case (work-ready ready) ready)
            (#case (work-pending pending) (#block (#forget pending) 0u64))))
        (#forget waker)
        (#return value))";
    build_and_run(source, 42);
}

#[test]
fn async_while_let_resumes_a_body_await_only_after_the_pattern_matches() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady (Some 42u64))))) )
      (#enum BodyTask (BodyWaiting BodyResuming))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case BodyWaiting (BodyPending BodyResuming))
          (#case BodyResuming (BodyReady 7u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady condition-poll ConditionWaiting)
            (#let result #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll BodyWaiting))
            (#assert (#u64.== payload 42u64))
            (#assert (#u64.== result 7u64))
            (#match payload
              (#case 42u64 (#break))
              (#case _ (#continue))))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task condition-pending : waker (#borrow waker))))
        (#let-else (work-pending body-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task body-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("scrutinee-body-task"), "{generated}");

    let conditional_source = source.replace(
        "(#await #u64 BodyTask BodyPending BodyReady body-poll BodyWaiting)",
        "(#if true\n                (#await #u64 BodyTask BodyPending BodyReady body-poll BodyWaiting)\n                7u64)",
    );
    let generated = build_and_run(&conditional_source, 42);
    assert!(generated.contains("choice"), "{generated}");

    let (prefix, _) = source.split_once("      (#fn main () #u64").unwrap();
    let unmatched_source = format!(
        "{}{}",
        prefix
            .replace("(ConditionReady (Some 42u64))", "(ConditionReady None)")
            .replace(
                "(#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll\n        (#return (#match task\n          (#case BodyWaiting (BodyPending BodyResuming))\n          (#case BodyResuming (BodyReady 7u64)))))",
                "(#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll\n        (#forget task)\n        (#return (BodyPending BodyWaiting)))",
            ),
        "      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task condition-pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))"
    );
    build_and_run(&unmatched_source, 42);
}

#[test]
fn async_while_let_carries_named_copy_aggregate_to_body_task() {
    let source = "(#struct Captures ((left #u64) (right #u64)))
      (#enum Maybe ((Some #u64) None))
      (#enum ConditionTask (ConditionWaiting ConditionResuming))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady Maybe)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case ConditionWaiting (ConditionPending ConditionResuming))
          (#case ConditionResuming (ConditionReady (Some 1u64))))) )
      (#enum BodyTask ((BodyWaiting Captures) (BodyResuming Captures)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting captures) (BodyPending (BodyResuming captures)))
          (#case (BodyResuming captures)
            (BodyReady (#u64.+.wrap
              (#get captures left) (#get captures right)))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((captures Captures)) #u64
          (#let-mut total #u64 0u64)
          (#while-let (Some payload)
            (#await Maybe ConditionTask ConditionPending ConditionReady condition-poll ConditionWaiting)
            (#let result #u64
              (#await #u64 BodyTask BodyPending BodyReady body-poll (BodyWaiting captures)))
            (#set total (#u64.+.wrap payload result))
            (#break))
          (#return total))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let captures Captures
          (#struct-literal Captures ((left 20u64) (right 22u64))))
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: captures captures)) : waker (#borrow waker))))
        (#let-else (work-pending condition-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll
          (: task condition-pending : waker (#borrow waker))))
        (#let-else (work-pending body-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task body-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 43);
    assert!(generated.contains("scrutinee-body-task"), "{generated}");

    let linear_source = source.replace(
        "(#struct Captures ((left #u64) (right #u64)))",
        "(#struct Captures ((left #u64) (right #u64))) (#linear Captures)",
    );
    let error = lim::parse_program(&linear_source).unwrap_err();
    assert!(
        error.contains("non-Copy local 'captures'"),
        "explicitly linear aggregates must not be treated as Copy captures: {error}"
    );
}

#[test]
fn async_while_condition_composes_multiple_body_awaits_in_a_child_frame() {
    let source = "(#struct Captures ((left #u64) (right #u64)))
      (#struct Counter ((value (#atomic #u64))))
      (#linear Counter)
      (#fn counter-create () Counter
        (#return (#struct-literal Counter ((value (#atomic-init #u64 1u64))))))
      (#fn counter-get ((counter (#ref Counter))) #u64
        (#return (#atomic-load (#borrow (#get counter value)) #memory-relaxed)))
      (#fn counter-clear ((counter (#ref Counter))) ()
        (#atomic-store (#borrow (#get counter value)) 0u64 #memory-relaxed)
        (#return ()))
      (#enum ChildTask ((Waiting #u64) (Resuming #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#linear ChildTask)
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Resuming value)))
          (#case (Resuming value) (ChildReady value)))))
      (#enum ConditionTask ((ConditionWaiting (#ref Counter))))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting counter)
            (#if (#u64.== (#call counter-get (: counter counter)) 0u64)
              (ConditionReady false)
              (#block
                (#call counter-clear (: counter counter))
                (ConditionReady true)))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((counter (#ref Counter)) (captures Captures) (view (#ref #u64)) (#mut total #u64)) #u64
          (#while (#await ConditionTask ConditionPending ConditionReady condition-poll
                    (ConditionWaiting counter))
            (#let-mut subtotal #u64 0u64)
            (#let-mut inner-iterations #u64 0u64)
            (#while (#u64.== inner-iterations 0u64)
              (#set inner-iterations 1u64)
              (#break))
            (#let first #u64
              (#await ChildTask ChildPending ChildReady child-poll
                (Waiting (#u64.+.wrap (#get captures left) (#deref view)))))
            (#let second #u64
              (#await ChildTask ChildPending ChildReady child-poll
                (Waiting (#u64.+.wrap (#get captures right) (#deref view)))))
            (#set subtotal (#u64.+.wrap first second))
            (#set total (#u64.+.wrap total subtotal)))
          (#return (#u64.+.wrap
            (#u64.+.wrap total (#get captures left))
            (#u64.+.wrap (#get captures right) (#deref view)))))))
      (#fn main () #u64
        (#let counter Counter (#call counter-create (:)))
        (#let captures Captures
          (#struct-literal Captures ((left 20u64) (right 22u64))))
        (#let-mut view-owner #u64 1u64)
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work
            (: counter (#borrow counter) : captures captures : view (#borrow view-owner) : total 0u64))
            : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let-else (work-pending pending-again) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task pending-again : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending task) (#block (#forget task) 0u64))))
        (#forget counter)
        (#set view-owner 0u64)
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 87);
    assert!(generated.contains("body-function"), "{generated}");
    assert!(generated.contains("body-poll.dispatch"), "{generated}");

    let linear_capture_source = source.replace(
        "(#struct Captures ((left #u64) (right #u64)))",
        "(#struct Captures ((left #u64) (right #u64))) (#linear Captures)",
    );
    let error = lim::parse_program(&linear_capture_source).unwrap_err();
    assert!(
        error.contains("non-Copy local 'captures'"),
        "linear aggregate captures must retain their ownership diagnostic: {error}"
    );

    let pending_mutation = source.replace(
        "(#let-else (work-pending pending) Work-poll-result first (#unreachable))",
        "(#let-else (work-pending pending) Work-poll-result first (#unreachable))\n        (#set view-owner 9u64)",
    );
    let program = lim::parse_program(&pending_mutation).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the nested async body must retain the external borrow while work-pending: {error}"
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
        "(#if true\n                (#await #u64 ChildTask ChildPending ChildReady child-poll\n                  (Waiting (#get captures right)))\n                0u64)",
    );
    build_and_run(&conditional_await_source, 87);
}

#[test]
fn async_while_condition_awaits_only_the_selected_branch_each_iteration() {
    let source = "(#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut should-await #bool true)
          (#while
            (#bool.&& should-await
              (#await #bool ChildTask ChildPending ChildReady child-poll Waiting))
            (#set should-await false))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
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
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut keep-going #bool true)
          (#while keep-going
            (#let result #bool
              (#if keep-going
                (#await #bool ChildTask ChildPending ChildReady child-poll Waiting)
                false))
            (#set keep-going false)
            (#assert result))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("choice"), "{generated}");
}

#[test]
fn async_loop_sequences_two_awaits_in_one_iteration() {
    let source = "(#enum SecondTask ((SecondWaiting #u64) (SecondResuming #u64)))
      (#linear SecondTask)
      (#enum SecondPoll ((SecondPending SecondTask) (SecondReady #u64)))
      (#fn second-poll ((task SecondTask) (waker (#ref #u64))) SecondPoll
        (#return (#match task
          (#case (SecondWaiting value) (SecondPending (SecondResuming value)))
          (#case (SecondResuming value) (SecondReady (#u64.+.wrap value 2u64))))))
      (#enum FirstTask (FirstWaiting FirstResuming))
      (#linear FirstTask)
      (#enum FirstPoll ((FirstPending FirstTask) (FirstReady #u64)))
      (#fn first-poll ((task FirstTask) (waker (#ref #u64))) FirstPoll
        (#return (#match task
          (#case FirstWaiting (FirstPending FirstResuming))
          (#case FirstResuming (FirstReady 40u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut keep-going #bool true)
          (#while keep-going
            (#let next-value #u64
              (#await FirstTask FirstPending FirstReady first-poll FirstWaiting))
            (#assert (#u64.== next-value 40u64))
            (#let result #u64
              (#await SecondTask SecondPending SecondReady second-poll (SecondWaiting next-value)))
            (#set keep-going false)
            (#assert (#u64.== result 42u64)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task first-pending : waker (#borrow waker))))
        (#let-else (work-pending second-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result
          (#call work-poll (: task second-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
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
      (#enum ThirdPoll ((ThirdPending ThirdTask) (ThirdReady #u64)))
      (#fn third-poll ((task ThirdTask) (waker (#ref #u64))) ThirdPoll
        (#return (#match task
          (#case ThirdWaiting (ThirdPending ThirdResuming))
          (#case ThirdResuming (ThirdReady 42u64)))))
      (#enum SecondTask (SecondWaiting SecondResuming))
      (#linear SecondTask)
      (#enum SecondPoll ((SecondPending SecondTask) (SecondReady ThirdTask)))
      (#fn second-poll ((task SecondTask) (waker (#ref #u64))) SecondPoll
        (#return (#match task
          (#case SecondWaiting (SecondPending SecondResuming))
          (#case SecondResuming (SecondReady ThirdWaiting)))))
      (#enum FirstTask (FirstWaiting FirstResuming))
      (#linear FirstTask)
      (#enum FirstPoll ((FirstPending FirstTask) (FirstReady SecondTask)))
      (#fn first-poll ((task FirstTask) (waker (#ref #u64))) FirstPoll
        (#return (#match task
          (#case FirstWaiting (FirstPending FirstResuming))
          (#case FirstResuming (FirstReady SecondWaiting)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut keep-going #bool true)
          (#while keep-going
            (#let second-task SecondTask
              (#await FirstTask FirstPending FirstReady first-poll FirstWaiting))
            (#let third-task ThirdTask
              (#await SecondTask SecondPending SecondReady second-poll second-task))
            (#let result #u64
              (#await ThirdTask ThirdPending ThirdReady third-poll third-task))
            (#set keep-going false)
            (#assert (#u64.== result 42u64)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task first-pending : waker (#borrow waker))))
        (#let-else (work-pending second-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result
          (#call work-poll (: task second-pending : waker (#borrow waker))))
        (#let-else (work-pending third-pending) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result
          (#call work-poll (: task third-pending : waker (#borrow waker))))
        (#let result #u64
          (#match fourth
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-frame"), "{generated}");
}

#[test]
fn async_for_initializer_awaits_once_before_entering_the_loop() {
    let source = "(#enum InitTask ((Waiting #u64) (Resuming #u64)))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady #u64)))
      (#fn init-poll ((task InitTask) (waker (#ref #u64))) InitPoll
        (#return (#match task
          (#case (Waiting count)
            (InitPending (Resuming count)))
          (#case (Resuming count)
            (InitReady (#u64.+.wrap count 2u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut total #u64 0u64)
          (#for (#let-mut iteration #u64
                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))
                (#u64.< iteration 3u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#set total (#u64.+.wrap total iteration)))
          (#return (#if (#u64.== total 2u64) 42u64 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("InitPending"), "{generated}");

    let conditional_initializer = source
        .replace(
            "(#let-mut iteration #u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
            "(#let-mut iteration #u64\n                  (#if false\n                    (#await #u64 InitTask InitPending InitReady init-poll (Waiting 0u64))\n                    2u64))",
        )
        .replace(
            "(#let-else (work-pending pending) Work-poll-result first (#unreachable))\n        (#let second Work-poll-result\n          (#call work-poll (: task pending : waker (#borrow waker))))\n        (#let result #u64\n          (#match second\n            (#case (work-ready value) value)\n            (#case (work-pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
            "(#let result #u64\n          (#match first\n            (#case (work-ready value) value)\n            (#case (work-pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
    );
    assert_ne!(conditional_initializer, source);
    let generated = build_and_run(&conditional_initializer, 42);
    assert!(generated.contains("(#fn work-poll"), "{generated}");

    let nested_initializer = source.replace(
        "(#let-mut iteration #u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
        "(#let-mut iteration #u64\n                  (#u64.+.wrap 0u64 (#await #u64 InitTask InitPending InitReady init-poll (Waiting 0u64))))",
    );
    let generated = build_and_run(&nested_initializer, 42);
    assert!(generated.contains("InitPending"), "{generated}");

    let multiple_nested_initializers = source
        .replace("(#u64.< iteration 3u64)", "(#u64.< iteration 5u64)")
        .replace("(#u64.== total 2u64)", "(#u64.== total 4u64)")
        .replace(
            "(#let-mut iteration #u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
            "(#let-mut iteration #u64\n                  (#u64.+.wrap\n                    (#await #u64 InitTask InitPending InitReady init-poll (Waiting 0u64))\n                    (#await #u64 InitTask InitPending InitReady init-poll (Waiting 0u64))))",
        )
        .replace(
            "(#let result #u64\n          (#match second\n            (#case (work-ready value) value)\n            (#case (work-pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
            "(#let-else (work-pending second-pending) Work-poll-result second (#unreachable))\n        (#let third Work-poll-result\n          (#call work-poll (: task second-pending : waker (#borrow waker))))\n        (#let result #u64\n          (#match third\n            (#case (work-ready value) value)\n            (#case (work-pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
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
            "(#let body-value #u64\n              (#await InitTask InitPending InitReady init-poll (Waiting iteration)))\n            (#set total (#u64.+.wrap total body-value))",
        );
    let generated = build_and_run(&initializer_then_body_await, 42);
    assert!(generated.contains("InitPending"), "{generated}");

    let initializer_then_condition_await = source
        .replace(
            "      (@#async-fn",
            "      (#enum ConditionTask ((ConditionStart #u64) (ConditionResume #u64)))\n      (#linear ConditionTask)\n      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))\n      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll\n        (#return (#match task\n          (#case (ConditionStart iteration) (ConditionPending (ConditionResume iteration)))\n          (#case (ConditionResume iteration)\n            (ConditionReady (#u64.< iteration 3u64))))))\n      (@#async-fn",
        )
        .replace(
            "                (#u64.< iteration 3u64)\n                (#set iteration",
            "                (#await ConditionTask ConditionPending ConditionReady condition-poll (ConditionStart iteration))\n                (#set iteration",
        )
        .replace("          (#let-mut total #u64 0u64)\n", "")
        .replace("            (#set total (#u64.+.wrap total iteration))", "            (#assert true)")
        .replace(
            "(#return (#if (#u64.== total 2u64) 42u64 0u64))",
            "(#return 42u64)",
        )
        .replace(
            "(#let second Work-poll-result\n          (#call work-poll (: task pending : waker (#borrow waker))))\n        (#let result #u64\n          (#match second",
            "(#let second Work-poll-result\n          (#call work-poll (: task pending : waker (#borrow waker))))\n        (#let-else (work-pending condition-pending) Work-poll-result second (#unreachable))\n        (#let third Work-poll-result\n          (#call work-poll (: task condition-pending : waker (#borrow waker))))\n        (#let-else (work-pending resumed-condition-pending) Work-poll-result third (#unreachable))\n        (#let fourth Work-poll-result\n          (#call work-poll (: task resumed-condition-pending : waker (#borrow waker))))\n        (#let result #u64\n          (#match fourth",
        );
    assert_ne!(initializer_then_condition_await, source);
    let generated = build_and_run(&initializer_then_condition_await, 42);
    assert!(generated.contains("ConditionPending"), "{generated}");

    let unsupported = source.replace(
        "(#let-mut iteration #u64\n                  (#await InitTask InitPending InitReady init-poll (Waiting 0u64)))",
        "(#let-mut iteration #u64\n                  (#u64.+.wrap 1u64 (#await InitTask InitPending InitReady init-poll (Waiting 0u64))))",
    );
    let error = match lim::parse_program(&unsupported) {
        Err(error) => error,
        Ok(program) => lim::check_types(&program).unwrap_err(),
    };
    assert!(
        error.contains("nested #await requires an explicit result type"),
        "nested initializer suspension should be diagnosed explicitly: {error}"
    );

    let task_initializer = "(#enum OuterTask ((Waiting #u64) (Resuming #u64)))
      (#linear OuterTask)
      (#enum OuterPoll ((OuterPending OuterTask) (OuterReady #u64)))
      (#fn outer-poll ((task OuterTask) (waker (#ref #u64))) OuterPoll
        (#return (#match task
          (#case (Waiting value) (OuterPending (Resuming value)))
          (#case (Resuming value) (OuterReady value)))))
      (#enum InnerTask (MakeOuter))
      (#enum InnerPoll ((InnerPending InnerTask) (InnerReady OuterTask)))
      (#fn inner-poll ((task InnerTask) (waker (#ref #u64))) InnerPoll
        (#return (#match task
          (#case MakeOuter (InnerReady (Waiting 42u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for (#let-mut initial #u64
                  (#await OuterTask OuterPending OuterReady outer-poll
                    (#await OuterTask InnerTask InnerPending InnerReady inner-poll MakeOuter)))
                false
                ()
            (#assert false))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(task_initializer, 42);
    assert!(!generated.contains("(#await"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_suspends_before_entering_the_loop() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum InitTask (Waiting Resuming))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref #u64))) InitPoll
        (#return (#match task
          (#case Waiting (InitPending Resuming))
          (#case Resuming (InitReady (Some 0u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for (#let-else (Some index) Maybe
                  (#await InitTask InitPending InitReady init-poll Waiting)
                  (#unreachable))
                (#u64.< index 1u64)
                (#u64.+.wrap index 1u64)
            (#assert (#u64.== index 0u64))
            (#break))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("InitPending"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_composes_with_a_suspending_body() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#type MaybeAlias Maybe)
      (#enum InitTask (Waiting Resuming))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref #u64))) InitPoll
        (#return (#match task
          (#case Waiting (InitPending Resuming))
          (#case Resuming (InitReady (Some 9u64))))))
      (#struct Resource ((value #u64)))
      (#linear Resource)
      (#fn Resource-destroy ((resource Resource)) #u64
        (#let result #u64 (#get resource value))
        (#forget resource)
        (#return result))
      (#enum BodyTask ((BodyWaiting #u64) (BodyResuming #u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady Resource)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (BodyWaiting value) (BodyPending (BodyResuming value)))
          (#case (BodyResuming value)
            (#block (#forget value)
              (BodyReady (#struct-literal Resource ((value 9u64)))))))))
      (#enum SecondBodyTask (SecondBodyWaiting SecondBodyResuming))
      (#linear SecondBodyTask)
      (#enum SecondBodyPoll ((SecondBodyPending SecondBodyTask) (SecondBodyReady #u64)))
      (#fn second-body-poll ((task SecondBodyTask) (waker (#ref #u64))) SecondBodyPoll
        (#return (#match task
          (#case SecondBodyWaiting (SecondBodyPending SecondBodyResuming))
          (#case SecondBodyResuming (SecondBodyReady 9u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut done #bool false)
          (#for (#let-else (Some index) MaybeAlias
                  (#await InitTask InitPending InitReady init-poll Waiting)
                  (#unreachable))
                (#bool.== done false)
                ()
            (#let value Resource
              (#await BodyTask BodyPending BodyReady body-poll (BodyWaiting index)))
            (#let second-value #u64
              (#await SecondBodyTask SecondBodyPending SecondBodyReady
                second-body-poll SecondBodyWaiting))
            (#assert (#u64.== second-value 9u64))
            (#let destroyed #u64 (#call Resource-destroy (: resource value)))
            (#assert (#u64.== destroyed second-value))
            (#set done true))
          (#return 42u64))))
      (#fn cancel-empty ((task ())) () (#return ()))
      (#fn cancel-initializer-state ((task (#tuple #bool InitTask))) ()
        (#let (#tuple done child) (#tuple #bool InitTask) task)
        (#forget child)
        (#return ()))
      (#fn cancel-body-task ((task BodyTask)) ()
        (#forget task)
        (#return ()))
      (#fn cancel-second-body-task ((task SecondBodyTask)) ()
        (#forget task)
        (#return ()))
      (#fn cancel-sequence-task ((task Lim.async.work.choice-2-sequence-task)) ()
        (#return (#match task
          (#case (Lim.async.work.choice-2-wait-first child)
            (#call cancel-body-task (: task child)))
          (#case (Lim.async.work.choice-2-wait-second resource child)
            (#block
              (#let destroyed #u64 (#call Resource-destroy (: resource resource)))
              (#assert (#u64.== destroyed 9u64))
              (#call cancel-second-body-task (: task child))
              (#return ()))))))
      (#fn cancel-loop-task ((task Lim.async.work.choice-4-task)) ()
        (#return (#match task
          (#case (Lim.async.work.choice-4-start done index) ())
          (#case (Lim.async.work.choice-4-wait done index child)
            (#call cancel-sequence-task (: task child))))))
      (@#task-cancel cancel-frame Work-task
        ((work-task-start cancel-empty ())
         (work-task-await-0 cancel-initializer-state ((done #bool) (child InitTask)))
         (work-task-await-1 cancel-loop-task)))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending after-init) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task after-init : waker (#borrow waker))))
        (#let-else (work-pending after-body) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task after-body : waker (#borrow waker))))
        (#let-else (work-pending after-second-body) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result (#call work-poll (: task after-second-body : waker (#borrow waker))))
        (#let result #u64
          (#match fourth
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#let cancel-task Work-task (#call work (:)))
        (#let cancel-first Work-poll-result (#call work-poll (: task cancel-task : waker (#borrow waker))))
        (#let-else (work-pending cancel-after-init) Work-poll-result cancel-first (#unreachable))
        (#let cancel-second Work-poll-result
          (#call work-poll (: task cancel-after-init : waker (#borrow waker))))
        (#let-else (work-pending cancel-after-body) Work-poll-result cancel-second (#unreachable))
        (#let cancel-third Work-poll-result
          (#call work-poll (: task cancel-after-body : waker (#borrow waker))))
        (#let-else (work-pending cancel-after-second-body) Work-poll-result cancel-third (#unreachable))
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
    let source = "(#enum Maybe ((Some #u64) None))
      (#type MaybeAlias Maybe)
      (#enum InitTask (InitWaiting InitResuming))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref #u64))) InitPoll
        (#return (#match task
          (#case InitWaiting (InitPending InitResuming))
          (#case InitResuming (InitReady (Some 9u64))))))
      (#enum StepTask (StepWaiting StepResuming))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady #bool)))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case StepWaiting (StepPending StepResuming))
          (#case StepResuming (StepReady true)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut done #bool false)
          (#for (#let-else (Some index) MaybeAlias
                  (#await InitTask InitPending InitReady init-poll InitWaiting)
                  (#unreachable))
                (#bool.== done false)
                (#set done
                  (#await #bool StepTask StepPending StepReady step-poll StepWaiting))
            (#assert (#u64.== index 9u64)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let task Work-task (#call work (:)))
        (#let first Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#let-else (work-pending after-init) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task after-init : waker (#borrow waker))))
        (#let-else (work-pending after-step) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task after-step : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPending"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_returns_ready_on_mismatch() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum InitTask ((Waiting Maybe) (Resuming Maybe)))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref #u64))) InitPoll
        (#return (#match task
          (#case (Waiting value) (InitPending (Resuming value)))
          (#case (Resuming value) (InitReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe)) #u64
          (#for (#let-else (Some index) Maybe
                  (#await InitTask InitPending InitReady init-poll (Waiting input))
                  (#return 7u64))
                false
                ()
            ())
          (#return 35u64))))
      (#fn work-poll-work ((input Maybe) (waker (#ref #u64))) #u64
        (#let task Work-task (#call work (: input input)))
        (#let first Work-poll-result (#call work-poll (: task task : waker waker)))
        (#return (#match first
          (#case (work-ready value) value)
          (#case (work-pending pending) (#block
            (#let second Work-poll-result (#call work-poll (: task pending : waker waker)))
            (#match second
              (#case (work-ready value) value)
              (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let mismatch #u64 (#call work-poll-work (: input None : waker (#borrow waker))))
        (#let matched #u64 (#call work-poll-work (: input (Some 7u64) : waker (#borrow waker))))
        (#forget waker)
        (#return (#u64.+.wrap mismatch matched)))";
    let generated = build_and_run(source, 42);
    assert!(
        generated.contains("(work-ready (#literal #u64 7))"),
        "{generated}"
    );
}

#[test]
fn async_for_let_else_initializer_can_suspend_in_condition() {
    let source = "(#enum Maybe ((Some #u64) None))
      (#enum InitTask ((Waiting Maybe) (Resuming Maybe)))
      (#linear InitTask)
      (#enum InitPoll ((InitPending InitTask) (InitReady Maybe)))
      (#fn init-poll ((task InitTask) (waker (#ref #u64))) InitPoll
        (#return (#match task
          (#case (Waiting value) (InitPending (Resuming value)))
          (#case (Resuming value) (InitReady value)))))
      (#enum ConditionTask ((ConditionWaiting #bool) (ConditionResuming #bool)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting value) (ConditionPending (ConditionResuming value)))
          (#case (ConditionResuming value) (ConditionReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((input Maybe) (condition #bool)) #u64
          (#let-mut body-ran #bool false)
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
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let mismatch-task Work-task (#call work (: input None : condition false)))
          (#let mismatch-first Work-poll-result (#call work-poll (: task mismatch-task : waker (#borrow waker))))
          (#let-else (work-pending mismatch-after-init) Work-poll-result mismatch-first (#unreachable))
          (#let mismatch-second Work-poll-result
            (#call work-poll (: task mismatch-after-init : waker (#borrow waker))))
          (#let-else (work-ready mismatch) Work-poll-result mismatch-second (#unreachable))
          (#let false-task Work-task (#call work (: input (Some 7u64) : condition false)))
          (#let false-first Work-poll-result (#call work-poll (: task false-task : waker (#borrow waker))))
          (#let-else (work-pending false-after-init) Work-poll-result false-first (#unreachable))
          (#let false-second Work-poll-result
            (#call work-poll (: task false-after-init : waker (#borrow waker))))
          (#let-else (work-pending false-after-condition-start) Work-poll-result false-second (#unreachable))
          (#let false-third Work-poll-result
            (#call work-poll (: task false-after-condition-start : waker (#borrow waker))))
          (#let-else (work-ready matched-false) Work-poll-result false-third (#unreachable))
          (#let true-task Work-task (#call work (: input (Some 7u64) : condition true)))
          (#let true-first Work-poll-result (#call work-poll (: task true-task : waker (#borrow waker))))
          (#let-else (work-pending true-after-init) Work-poll-result true-first (#unreachable))
          (#let true-second Work-poll-result
            (#call work-poll (: task true-after-init : waker (#borrow waker))))
          (#let-else (work-pending true-after-condition-start) Work-poll-result true-second (#unreachable))
          (#let true-third Work-poll-result
            (#call work-poll (: task true-after-condition-start : waker (#borrow waker))))
          (#let-else (work-ready matched-true) Work-poll-result true-third (#unreachable))
          (#forget waker)
          (#return (#u64.+.wrap mismatch
            (#u64.+.wrap matched-false matched-true))))"
    );
    let generated = build_and_run(&source, 92);
    assert!(generated.contains("ConditionPending"), "{generated}");
}

#[test]
fn async_for_condition_and_step_await_preserve_body_continue_and_break() {
    let source = "(#enum ConditionTask ((ConditionWaiting #u64) (ConditionResuming #u64)))
      (#linear ConditionTask)
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task
          (#case (ConditionWaiting iteration)
            (ConditionPending (ConditionResuming iteration)))
          (#case (ConditionResuming iteration) (ConditionReady true)))))
      (#enum StepTask ((StepWaiting #u64) (StepResuming #u64)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady #u64)))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (StepWaiting iteration)
            (StepPending (StepResuming iteration)))
          (#case (StepResuming iteration)
            (StepReady (#u64.+.wrap iteration 1u64))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for ()
            (#await ConditionTask ConditionPending ConditionReady
              condition-poll (ConditionWaiting iteration))
            (#set iteration
              (#await #u64 StepTask StepPending StepReady step-poll
                (StepWaiting iteration)))
            (#if (#u64.== iteration 0u64) (#continue) (#break)))
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending-1) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending-1 : waker (#borrow waker))))
        (#let-else (work-pending pending-2) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task pending-2 : waker (#borrow waker))))
        (#let-else (work-pending pending-3) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result (#call work-poll (: task pending-3 : waker (#borrow waker))))
        (#let result #u64
          (#match fourth
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 1);
    assert!(generated.contains("step-choice-skip"), "{generated}");
    assert!(generated.contains("step-choice-run"), "{generated}");

    let (prefix, _) = source
        .split_once("(#fn main () #u64")
        .expect("async main function");
    let return_prefix = prefix.replace(
        "(#if (#u64.== iteration 0u64) (#continue) (#break))",
        "(#return 42u64)",
    );
    let return_source = format!(
        "{return_prefix}
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let first Work-poll-result
            (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
          (#let-else (work-pending pending) Work-poll-result first (#unreachable))
          (#let second Work-poll-result
            (#call work-poll (: task pending : waker (#borrow waker))))
          (#let result #u64
            (#match second
              (#case (work-ready value) value)
              (#case (work-pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result))"
    );
    let returned = build_and_run(&return_source, 42);
    assert!(returned.contains("iteration-function"), "{returned}");
}

#[test]
fn async_for_step_can_suspend_after_the_loop_body() {
    let source = "(#enum StepTask ((Waiting #u64) (Resuming #u64)))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady #u64)))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
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
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for (#set iteration 0u64)
                (#u64.< iteration 6u64)
                (#set iteration
                  (#await StepTask StepPending StepReady step-poll
                    (Waiting iteration)))
            (#set iteration (#u64.+.wrap iteration 1u64)))
          (#return (#if (#u64.== iteration 6u64) 42u64 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPending"), "{generated}");
}

#[test]
fn async_for_step_can_suspend_after_a_suspending_body() {
    let source = "(#enum BodyTask ((Waiting #u64) (Resuming #u64)))
      (#linear BodyTask)
      (#enum BodyPoll ((BodyPending BodyTask) (BodyReady #u64)))
      (#fn body-poll ((task BodyTask) (waker (#ref #u64))) BodyPoll
        (#return (#match task
          (#case (Waiting value) (BodyPending (Resuming value)))
          (#case (Resuming value) (BodyReady value)))))
      (#enum StepTask (Start Resume))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady #u64)))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case Start (StepPending Resume))
          (#case Resume (StepReady 1u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for (#set iteration 0u64)
                (#u64.< iteration 1u64)
            (#set iteration
                  (#await StepTask StepPending StepReady step-poll Start))
            (#let body-value #u64
              (#await BodyTask BodyPending BodyReady body-poll (Waiting 42u64)))
            (#assert (#u64.== body-value 42u64)))
          (#return (#if (#u64.== iteration 1u64) 42u64 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending body-pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task body-pending : waker (#borrow waker))))
        (#let-else (work-pending step-pending) Work-poll-result second (#unreachable))
        (#let third Work-poll-result
          (#call work-poll (: task step-pending : waker (#borrow waker))))
        (#let result #u64
          (#match third
            (#case (work-ready value) value)
            (#case (work-pending unexpected) (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("sequence-task"), "{generated}");
}

#[test]
fn async_for_step_can_suspend_inside_assignment_expression() {
    let source = "(#enum StepTask (Waiting Resuming))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady #u64)))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case Waiting (StepPending Resuming))
          (#case Resuming (StepReady 1u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for ()
                (#u64.< iteration 1u64)
                (#set iteration
                  (#u64.+.wrap iteration
                    (#await #u64 StepTask StepPending StepReady step-poll Waiting)))
            (#assert true))
          (#return (#if (#u64.== iteration 1u64) 42u64 0u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPending"), "{generated}");
}

#[test]
fn async_branch_prefixes_capture_only_live_values() {
    let source = include_str!("../examples/async_await_destructure.lim");
    let block = source
        .replace(
            "(#let (Values (#tuple left right) bias) Values",
            "(#let result #u64 (#block (#let (Values (#tuple left right) bias) Values",
        )
        .replace(
            "(#return (#u64.+.wrap (#u64.+.wrap (#as left #u64) second) bias))",
            "(#u64.+.wrap (#u64.+.wrap (#as left #u64) second) bias))) (#return result)",
        );
    build_and_run(&block, 42);
    let branch = block
        .replace(
            "(#let result #u64 (#block",
            "(#let result #u64 (#if true (#block",
        )
        .replace(
            "bias))) (#return result)",
            "bias)) (#block (#forget values) 5u64))) (#return result)",
        );
    build_and_run(&branch, 42);
    let consumed_prefix = format!(
        "(#struct Token ((value #u64))) (#linear Token)\n{}",
        include_str!("../examples/async_pattern_blocks.lim")
            .replace("(a #u64)", "(a Token)")
            .replace(": a 22u64", ": a (#struct-literal Token (: value 22u64))")
            .replace(
                "(#let first #u64",
                "(#let bias-value #u64 (#get bias value)) (#forget bias) (#let first #u64",
            )
            .replace("first second) bias)", "first second) bias-value)")
    );
    build_and_run(&consumed_prefix, 47);
    build_and_run(
        &consumed_prefix.replace("(StepPending (Resume value))", "(StepReady value)"),
        47,
    );
    build_and_run(
        &consumed_prefix
            .replace("(StepPending (Resume value))", "(#panic)")
            .replace(": choose true : waker", ": choose false : waker"),
        10,
    );
    let destructor = format!(
        "(#fn destroy-token ((token Token)) #u64
          (#let value #u64 (#get token value)) (#forget token) (#return value))\n{}",
        consumed_prefix.replace(
            "(#let bias-value #u64 (#get bias value)) (#forget bias)",
            "(#let bias-value #u64 (#call destroy-token (: token bias)))",
        )
    );
    build_and_run(&destructor, 47);
    build_and_run(include_str!("../examples/async_prefix_cleanup.lim"), 47);
    let first_child_only = consumed_prefix
        .replace(
            "(Start (#as left #u64))",
            "(Start (#u64.+.wrap (#as left #u64) bias-value))",
        )
        .replace("first second) bias-value)", "first second) 0u64)");
    build_and_run(&first_child_only, 47);
    // An outer value used only by the first child, not by its continuation,
    // must also be an explicit helper parameter.
    let outer_child_only = include_str!("../examples/async_pattern_blocks.lim")
        .replace(
            "((choose #bool) (values Values))",
            "((choose #bool) (values Values) (offset #u64))",
        )
        .replace(
            "(Start (#as left #u64))",
            "(Start (#u64.+.wrap (#as left #u64) offset))",
        )
        .replace(
            ": choose choose : values",
            ": choose choose : offset 3u64 : values",
        );
    build_and_run(&outer_child_only, 50);
    let scratch = support::Scratch::new("async-prefix-ownership");
    let error_for = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    let missing_cleanup = error_for(&consumed_prefix.replace("(#forget bias)", "()"));
    assert_eq!(
        missing_cleanup.code,
        lim::DiagnosticCode::Linear,
        "{missing_cleanup:?}"
    );
    assert!(
        missing_cleanup.message.contains("bias"),
        "{missing_cleanup:?}"
    );
    assert!(missing_cleanup.span.is_some(), "{missing_cleanup:?}");
    let reused = error_for(&consumed_prefix.replace(
        "first second) bias-value)",
        "first second) (#get bias value))",
    ));
    assert_eq!(reused.code, lim::DiagnosticCode::Linear, "{reused:?}");
    assert!(reused.message.contains("bias"), "{reused:?}");
    assert!(reused.span.is_some(), "{reused:?}");
}

#[test]
fn async_scoped_blocks_keep_nested_pattern_captures() {
    let source = include_str!("../examples/async_destructure.lim");
    let block = source
        .replace(
            "(#let (Values (#tuple left right) bias) Values values)",
            "(#let result #u64 (#block (#let (Values (#tuple left right) bias) Values values)",
        )
        .replace(
            "(#return (#u64.+.wrap (#u64.+.wrap first second) bias))",
            "(#u64.+.wrap (#u64.+.wrap first second) bias))) (#return result)",
        );
    build_and_run(&block, 42);
    let branch = include_str!("../examples/async_pattern_blocks.lim");
    build_and_run(branch, 47);
    let immediate = branch.replace("(StepPending (Resume value))", "(StepReady value)");
    build_and_run(&immediate, 47);
    let skipped = branch
        .replace("(StepPending (Resume value))", "(#panic)")
        .replace(": choose true : waker", ": choose false : waker");
    build_and_run(&skipped, 10);
    let mutable = branch
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64.+.wrap bias 2u64)) (#let second #u64",
        );
    build_and_run(&mutable, 49);
    let bool_tail = block
        .replace("(a #u64)", "(a #bool)")
        .replace(": a 22u64", ": a true")
        .replace(
            "(#fn work ((values Values)) #u64",
            "(#fn work ((values Values)) #bool",
        )
        .replace("(#let result #u64", "(#let result #bool")
        .replace("(#u64.+.wrap (#u64.+.wrap first second) bias)", "bias")
        .replace("(#return value)", "(#return (#if value 42u64 0u64))");
    build_and_run(&bool_tail, 42);
    let owned = format!("(#struct Token ((value #u64))) (#linear Token)\n{}", branch
        .replace("(a #u64)", "(a Token)")
        .replace(": a 22u64", ": a (#struct-literal Token (: value 22u64))")
        .replace("(#u64.+.wrap (#u64.+.wrap first second) bias))", "(#let total #u64 (#u64.+.wrap (#u64.+.wrap first second) (#get bias value))) (#forget bias) total)"));
    build_and_run(&owned, 47);
    let referenced = branch
        .replace("(#tuple #u16 #u16)", "(#tuple #u16 (#ref #u64))")
        .replace("(#as right #u64)", "(#deref right)")
        .replace(
            "(#let-mut task Work-task",
            "(#let-mut owner #u64 11u64) (#let-mut task Work-task",
        )
        .replace("9u16 11u16", "9u16 (#borrow owner)");
    build_and_run(&referenced, 47);
    let exclusive = referenced
        .replace("(#tuple #u16 (#ref #u64))", "(#tuple #u16 (#ref-mut #u64))")
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    build_and_run_graph(&exclusive, 47);
    let scratch = support::Scratch::new("async-block-pattern-errors");
    let error_for = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    let invalid = referenced.replace(
        "(#block (#set task next) ())",
        "(#block (#set owner 99u64) (#set task next) ())",
    );
    let conflict = error_for(&invalid);
    assert!(
        conflict.message.contains("owner") && conflict.message.contains("borrow"),
        "{conflict:?}"
    );
    let span = conflict
        .span
        .expect("conditional pattern loan retains its exact origin");
    assert_eq!(&invalid[span.start..span.end], "#set", "{conflict:?}");
    assert_eq!(span.start, invalid.find("#set owner 99u64").unwrap());
    let missing_cleanup = error_for(&owned.replace("(#forget bias)", "()"));
    assert_eq!(
        missing_cleanup.code,
        lim::DiagnosticCode::Linear,
        "{missing_cleanup:?}"
    );
    assert!(
        missing_cleanup.message.contains("bias") && missing_cleanup.message.contains("consum"),
        "{missing_cleanup:?}"
    );
    let leaked_scope = error_for(&branch.replace(
        "(#block (#forget values) 5u64)",
        "(#block (#forget values) (#as left #u64))",
    ));
    assert!(
        leaked_scope.message.contains("left")
            && (leaked_scope.message.contains("unknown")
                || leaked_scope.message.contains("captures")),
        "{leaked_scope:?}"
    );
    assert!(leaked_scope.span.is_some(), "{leaked_scope:?}");
}

#[test]
fn async_awaited_aggregate_can_be_destructured_directly() {
    let source = include_str!("../examples/async_await_destructure.lim");
    build_and_run(source, 42);
    let immediate = source.replace("(InputPending (InputResume values))", "(InputReady values)");
    build_and_run(&immediate, 42);
    let without_result_type = source.replace("(#await Values InputTask", "(#await InputTask");
    build_and_run(&without_result_type, 42);
    let aliased = format!(
        "(#type ValuesAlias Values)\n{}",
        source
            .replace("(values Values)", "(values ValuesAlias)")
            .replace("bias) Values\n", "bias) ValuesAlias\n")
            .replace("(#await Values InputTask", "(#await ValuesAlias InputTask")
    );
    build_and_run(&aliased, 42);
    let mutable = source
        .replace("(#let (Values", "(#let-mut (Values")
        .replace("(#let second #u64", "(#set bias (#u64.+.wrap bias 2u64)) (#set right (#u16.+.wrap right 1u16)) (#let second #u64");
    build_and_run(&mutable, 45);
    let array = source
        .replace("(#tuple #u16 #u16)", "(#array #u16 2)")
        .replace("(#tuple left right)", "(#array left right)")
        .replace(
            "(#tuple (#array #u16 2) 9u16 11u16)",
            "(#array-of (#array #u16 2) 9u16 11u16)",
        );
    build_and_run(&array, 42);
    let tuple = source
        .replace(
            "(#struct Values ((z (#tuple #u16 #u16)) (a #u64)))",
            "(#type Values (#tuple (#tuple #u16 #u16) #u64))",
        )
        .replace(
            "(Values (#tuple left right) bias)",
            "(#tuple (#tuple left right) bias)",
        )
        .replace(
            "(#struct-literal Values (: a 22u64 : z (#tuple (#tuple #u16 #u16) 9u16 11u16)))",
            "(#tuple (#tuple (#tuple #u16 #u16) #u64) (#tuple (#tuple #u16 #u16) 9u16 11u16) 22u64)",
        );
    build_and_run(&tuple, 42);
    let single_variant = source
        .replace(
            "(#struct Values ((z (#tuple #u16 #u16)) (a #u64)))",
            "(#enum Values ((Only (#tuple #u16 #u16) #u64)))",
        )
        .replace(
            "(Values (#tuple left right) bias)",
            "(Only (#tuple left right) bias)",
        )
        .replace("(#let (Only", "(#let-else (Only")
        .replace(
            "input-poll (InputStart values)))",
            "input-poll (InputStart values)) (#unreachable))",
        )
        .replace(
            "(#struct-literal Values (: a 22u64 : z (#tuple (#tuple #u16 #u16) 9u16 11u16)))",
            "(Only (#tuple (#tuple #u16 #u16) 9u16 11u16) 22u64)",
        );
    build_and_run(&single_variant, 42);
    let enum_options = single_variant
        .replace(
            "(#enum Values ((Only (#tuple #u16 #u16) #u64)))",
            "(#enum Values ((Only (#tuple #u16 #u16) #u64) Missing))",
        )
        .replace(
            "input-poll (InputStart values)) (#unreachable))",
            "input-poll (InputStart values)) (#return 5u64))",
        );
    build_and_run(&enum_options, 42);
    let mismatched = enum_options
        .replace(
            "(Only (#tuple (#tuple #u16 #u16) 9u16 11u16) 22u64)",
            "Missing",
        )
        .replace("(StepPending (Resume value))", "(#panic)");
    build_and_run(&mismatched, 5);
    let owned = format!("(#struct Token ((value #u64))) (#linear Token)\n{}", source
        .replace("(a #u64)", "(a Token)")
        .replace(": a 22u64", ": a (#struct-literal Token (: value 22u64))")
        .replace("(#return (#u64.+.wrap (#u64.+.wrap (#as left #u64) second) bias))", "(#let total #u64 (#u64.+.wrap (#u64.+.wrap (#as left #u64) second) (#get bias value))) (#forget bias) (#return total)"));
    build_and_run(&owned, 42);
    let effect = format!(
        "(#fn make-input ((values Values) (count (#ref-mut #u64))) InputTask
      (#deref-set count (#u64.+.wrap (#deref count) 1u64))
      (#return (InputStart values)))\n{}",
        source
            .replace(
                "(#fn work ((values Values))",
                "(#fn work ((values Values) (counter (#ref-mut #u64)))"
            )
            .replace(
                "input-poll (InputStart values)",
                "input-poll (#call make-input (: values values : count counter))"
            )
            .replace(
                "(#let waker #u64",
                "(#let-mut touches #u64 0u64) (#let waker #u64"
            )
            .replace(
                "(#call work (: values",
                "(#call work (: counter (#borrow-mut touches) : values"
            )
            .replace(
                "(#block (#return value))",
                "(#block (#assert (#u64.== touches 1u64)) (#return value))"
            )
    );
    build_and_run(&effect, 42);
    let factory = format!("(#enum Factory ((FactoryStart Values) (FactoryResume Values)))
      (#enum FactoryPoll ((FactoryPending Factory) (FactoryReady InputTask)))
      (#fn factory-poll ((task Factory) (waker (#ref #u64))) FactoryPoll
        (#return (#match task
          (#case (FactoryStart values) (FactoryPending (FactoryResume values)))
          (#case (FactoryResume values) (FactoryReady (InputStart values))))))\n{}", source
        .replace("input-poll (InputStart values)", "input-poll (#await InputTask Factory FactoryPending FactoryReady factory-poll (FactoryStart values))")
        .replace("0u64 4u64", "0u64 5u64"));
    build_and_run(&factory, 42);
    let referenced = source
        .replace("(#tuple #u16 #u16)", "(#tuple #u16 (#ref #u64))")
        .replace("(#as right #u64)", "(#deref right)")
        .replace(
            "(#let waker #u64",
            "(#let-mut owner #u64 11u64) (#let waker #u64",
        )
        .replace("9u16 11u16", "9u16 (#borrow owner)");
    build_and_run(&referenced, 42);
    let exclusive = referenced
        .replace("(#tuple #u16 (#ref #u64))", "(#tuple #u16 (#ref-mut #u64))")
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    build_and_run_graph(&exclusive, 42);
    let released = exclusive.replace(
        "(#case (work-ready value) (#block (#return value)))",
        "(#case (work-ready value) (#block (#set owner 99u64) (#return value)))",
    );
    assert_ne!(released, exclusive);
    build_and_run_graph(&released, 42);
    let retained = exclusive.replace(
        "(#block (#set task next) ())",
        "(#block (#set owner 99u64) (#set task next) ())",
    );
    assert_ne!(retained, exclusive);
    let error = graph_compile_error(&retained, "graph-exclusive-pending-loan");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error
        .span
        .expect("Pending exclusive loan has a source span");
    assert_eq!(&retained[span.start..span.end], "#set", "{error:?}");
    assert_eq!(span.start, retained.find("#set owner 99u64").unwrap());
    let overlapping_waker = exclusive.replace("(#borrow waker)", "(#borrow owner)");
    assert_ne!(overlapping_waker, exclusive);
    let error = graph_compile_error(&overlapping_waker, "graph-exclusive-overlapping-waker");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.message.contains("overlapping borrows"), "{error:?}");
    let span = error.span.expect("overlapping waker has a source span");
    assert_eq!(
        &overlapping_waker[span.start..span.end],
        "(#borrow owner)",
        "{error:?}"
    );
    let invalid = referenced.replace(
        "(#block (#set task next) ())",
        "(#block (#set owner 99u64) (#set task next) ())",
    );
    let scratch = support::Scratch::new("async-awaited-pattern-borrow");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("owner") && error.message.contains("borrow"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("awaited pattern loan must retain its source span");
    assert_eq!(&invalid[span.start..span.end], "#set", "{error:?}");
    assert_eq!(span.start, invalid.find("#set owner 99u64").unwrap());
    let error_for = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    let missing_cleanup = owned.replace("(#forget bias)", "()");
    let error = error_for(&missing_cleanup);
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("bias") && error.message.contains("consum"),
        "{error:?}"
    );
    assert!(error.span.is_some(), "{error:?}");
    let duplicate = error_for(&source.replace("left right) bias", "left left) bias"));
    assert!(
        duplicate.message.contains("left")
            && (duplicate.message.contains("duplicate") || duplicate.message.contains("shadow")),
        "{duplicate:?}"
    );
    assert!(duplicate.span.is_some(), "{duplicate:?}");
    let wrong_arity = error_for(&source.replace(
        "(Values (#tuple left right) bias)",
        "(Values (#tuple left right) bias extra)",
    ));
    assert!(
        wrong_arity.message.contains("pattern") && wrong_arity.message.contains("fields"),
        "{wrong_arity:?}"
    );
    assert!(wrong_arity.span.is_some(), "{wrong_arity:?}");
    let mismatch = error_for(&source.replace("(#await Values InputTask", "(#await #u64 InputTask"));
    assert!(
        mismatch
            .message
            .contains("#await result type does not match binding"),
        "{mismatch:?}"
    );
    assert!(mismatch.span.is_some(), "{mismatch:?}");
}

#[test]
fn async_nested_local_destructuring_retains_all_declared_bindings() {
    let source = include_str!("../examples/async_destructure.lim");
    build_and_run(source, 42);
    let aliased = format!(
        "(#type ValuesAlias Values)\n{}",
        source
            .replace("(values Values)", "(values ValuesAlias)")
            .replace("bias) Values values", "bias) ValuesAlias values")
    );
    build_and_run(&aliased, 42);
    let array = source
        .replace("(#tuple #u16 #u16)", "(#array #u16 2)")
        .replace("(#tuple left right)", "(#array left right)")
        .replace(
            "(#tuple (#array #u16 2) 9u16 11u16)",
            "(#array-of (#array #u16 2) 9u16 11u16)",
        );
    build_and_run(&array, 42);
    let nested_struct = format!(
        "(#struct Bits ((first #u16) (second #u16)))\n{}",
        source
            .replace("(z (#tuple #u16 #u16))", "(z Bits)")
            .replace("(#tuple left right)", "(Bits left right)")
            .replace(
                "(#tuple (#tuple #u16 #u16) 9u16 11u16)",
                "(#struct-literal Bits (: first 9u16 : second 11u16))"
            )
    );
    build_and_run(&nested_struct, 42);
    let mutable = source
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64.+.wrap bias 2u64)) (#let second #u64",
        );
    build_and_run(&mutable, 44);
    let between = source
        .replace(
            "    (#let (Values (#tuple left right) bias) Values values)\n",
            "",
        )
        .replace("(Start (#as left #u64))", "(Start 9u64)")
        .replace(
            "(#let second #u64",
            "(#let (Values (#tuple left right) bias) Values values) (#let second #u64",
        );
    build_and_run(&between, 42);
    let mutable_between = between
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64.+.wrap bias 2u64)) (#let second #u64",
        );
    build_and_run(&mutable_between, 44);
    let both_updated = mutable_between.replace(
        "(#let second #u64",
        "(#set right (#u16.+.wrap right 1u16)) (#let second #u64",
    );
    build_and_run(&both_updated, 45);
    let final_prefix = source
        .replace("    (#let (Values (#tuple left right) bias) Values values)\n", "")
        .replace("(Start (#as left #u64))", "(Start 9u64)")
        .replace("(Start (#as right #u64))", "(Start 11u64)")
        .replace("(#return (#u64.+.wrap", "(#let-mut (Values (#tuple left right) bias) Values values) (#set bias 24u64) (#return (#u64.+.wrap");
    build_and_run(&final_prefix, 44);
    let immutable_update = mutable_between.replace("(#let-mut (Values", "(#let (Values");
    let scratch = support::Scratch::new("async-resume-pattern-immutable");
    let error = lim::compile_source_to_assembly(
        &immutable_update,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("assignment to 'bias' requires a mutable"),
        "{error:?}"
    );
    assert!(
        error.span.is_some(),
        "immutable pattern update must be source-spanned: {error:?}"
    );
    let owned = format!(
        "(#struct Token ((value #u64))) (#linear Token)\n{}",
        source
            .replace("(a #u64)", "(a Token)")
            .replace(": a 22u64", ": a (#struct-literal Token (: value 22u64))")
            .replace("(#return (#u64.+.wrap (#u64.+.wrap first second) bias))", "(#let total #u64 (#u64.+.wrap (#u64.+.wrap first second) (#get bias value))) (#forget bias) (#return total)")
    );
    build_and_run(&owned, 42);
    let referenced = source
        .replace("(#tuple #u16 #u16)", "(#tuple #u16 (#ref #u64))")
        .replace("(#as right #u64)", "(#deref right)")
        .replace(
            "(#let waker #u64",
            "(#let-mut owner #u64 11u64) (#let waker #u64",
        )
        .replace("9u16 11u16", "9u16 (#borrow owner)");
    build_and_run(&referenced, 42);
    let exclusive = referenced
        .replace("(#ref #u64)", "(#ref-mut #u64)")
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    // Keep the poller's waker shared; only the destructured data field is exclusive.
    let exclusive = exclusive.replace("(waker (#ref-mut #u64))", "(waker (#ref #u64))");
    build_and_run_graph(&exclusive, 42);
    let definitions = referenced.split_once("(#fn main").unwrap().0;
    let cancelled = format!(
        "{definitions}
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut owner #u64 11u64)
        (#let frame Work-task (#call work (: values
          (#struct-literal Values (: a 22u64 : z
            (#tuple (#tuple #u16 (#ref #u64)) 9u16 (#borrow owner)))))))
        (#let-else (work-pending pending) Work-poll-result
          (#call work-poll (: task frame : waker (#borrow waker))) (#unreachable))
        (#forget pending)
        (#set owner 42u64)
        (#return owner))"
    );
    build_and_run(&cancelled, 42);
    let invalid = referenced.replace(
        "(#block (#set task next) ())",
        "(#block (#set owner 99u64) (#set task next) ())",
    );
    assert_ne!(invalid, referenced);
    let scratch = support::Scratch::new("async-local-pattern-borrow");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("owner") && error.message.contains("borrow"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("retained pattern loan has an exact source span");
    assert_eq!(&invalid[span.start..span.end], "#set", "{error:?}");
    assert_eq!(span.start, invalid.find("#set owner 99u64").unwrap());
}

#[test]
fn graph_nested_destructuring_preserves_projection_types_and_retained_loans() {
    let source = include_str!("../examples/async_destructure.lim");
    build_and_run_graph(source, 42);
    let aliased = format!(
        "(#type ValuesAlias Values)\n{}",
        source
            .replace("(values Values)", "(values ValuesAlias)")
            .replace("bias) Values values", "bias) ValuesAlias values")
    );
    build_and_run_graph(&aliased, 42);
    let array = source
        .replace("(#tuple #u16 #u16)", "(#array #u16 2)")
        .replace("(#tuple left right)", "(#array left right)")
        .replace(
            "(#tuple (#array #u16 2) 9u16 11u16)",
            "(#array-of (#array #u16 2) 9u16 11u16)",
        );
    build_and_run_graph(&array, 42);
    let nested_struct = format!(
        "(#struct Bits ((first #u16) (second #u16)))\n{}",
        source
            .replace("(z (#tuple #u16 #u16))", "(z Bits)")
            .replace("(#tuple left right)", "(Bits left right)")
            .replace(
                "(#tuple (#tuple #u16 #u16) 9u16 11u16)",
                "(#struct-literal Bits (: first 9u16 : second 11u16))",
            )
    );
    build_and_run_graph(&nested_struct, 42);
    let row_literal =
        "(#struct-literal Row (: padding 0u128 : cells (#array-of (#array #u64 2) 41u64 17u64)))";
    let dynamic_struct = nested_struct
        .replace("(#array Row 1)", "(#array Row 2)")
        .replace(row_literal, &format!("{row_literal} {row_literal}"))
        .replace(
            "(#let row (#ref-mut Row)",
            "(#let-mut index #usize 1usize) (#let row (#ref-mut Row)",
        )
        .replace(
            "(#slice-mut-idx items 0usize)",
            "(#slice-mut-idx items index)",
        )
        .replace(
            "(#await () ChildTask",
            "(#set index 0usize) (#await () ChildTask",
        )
        .replace("(#index values 0usize)", "(#index values 1usize)");
    build_and_run_graph(&dynamic_struct, 42);
    let tuple = dynamic_struct
        .replace(
            "(#struct Row (: padding #u128 : cells (#array #u64 2)))",
            "(#type Row (#tuple #u128 (#array #u64 2)))",
        )
        .replace(
            row_literal,
            "(#tuple Row 0u128 (#array-of (#array #u64 2) 41u64 17u64))",
        )
        .replace("(#get row cells)", "(#get row 1)")
        .replace(
            "(#get (#index values 1usize) cells)",
            "(#get (#index values 1usize) 1)",
        );
    build_and_run_graph(&tuple, 42);
    let between = source
        .replace(
            "    (#let (Values (#tuple left right) bias) Values values)\n",
            "",
        )
        .replace("(Start (#as left #u64))", "(Start 9u64)")
        .replace(
            "(#let second #u64",
            "(#let (Values (#tuple left right) bias) Values values) (#let second #u64",
        );
    build_and_run_graph(&between, 42);
    let mutable = between
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64.+.wrap bias 2u64)) (#set right (#u16.+.wrap right 1u16)) (#let second #u64",
        );
    build_and_run_graph(&mutable, 45);
    let referenced = source
        .replace("(#tuple #u16 #u16)", "(#tuple #u16 (#ref #u64))")
        .replace("(#as right #u64)", "(#deref right)")
        .replace(
            "(#let waker #u64",
            "(#let-mut owner #u64 11u64) (#let waker #u64",
        )
        .replace("9u16 11u16", "9u16 (#borrow owner)");
    build_and_run_graph(&referenced, 42);
    let exclusive = referenced
        .replace("(#tuple #u16 (#ref #u64))", "(#tuple #u16 (#ref-mut #u64))")
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    build_and_run_graph(&exclusive, 42);
    // A single projected field may retain either external storage location.
    // Its source type and selected value must survive both suspension points.
    for (choice, expected) in [(true, 42), (false, 62)] {
        let selected = referenced
            .replace(
                "(#let-mut owner #u64 11u64)",
                "(#let-mut owner #u64 11u64) (#let-mut other #u64 31u64)",
            )
            .replace(
                "(#let waker #u64 0u64)",
                &format!(
                    "(#let waker #u64 {}u64) (#let choose #bool (#u64.== waker 0u64))",
                    if choice { 0 } else { 1 },
                ),
            )
            .replace(
                "9u16 (#borrow owner)",
                "9u16 (#if choose (#borrow owner) (#borrow other))",
            );
        build_and_run_graph(&selected, expected);
    }
    let definitions = referenced.split_once("(#fn main").unwrap().0;
    let cancelled = format!(
        "{definitions}
        (#fn main () #u64
          (#let waker #u64 0u64)
          (#let-mut owner #u64 11u64)
          (#let frame Work-task (#call work (: values
            (#struct-literal Values (: a 22u64 : z
              (#tuple (#tuple #u16 (#ref #u64)) 9u16 (#borrow owner)))))))
          (#let-else (work-pending pending) Work-poll-result
            (#call work-poll (: task frame : waker (#borrow waker))) (#unreachable))
          (#forget pending)
          (#set owner 42u64)
          (#return owner))"
    );
    build_and_run_graph(&cancelled, 42);
    let invalid = referenced.replace(
        "(#block (#set task next) ())",
        "(#block (#set owner 99u64) (#set task next) ())",
    );
    assert_ne!(invalid, referenced);
    let error = graph_compile_error(&invalid, "graph-destructured-retained-loan");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error
        .span
        .expect("retained projection keeps its source span");
    assert_eq!(&invalid[span.start..span.end], "#set", "{error:?}");
    assert_eq!(span.start, invalid.find("#set owner 99u64").unwrap());
    let immutable = mutable.replace("(#let-mut (Values", "(#let (Values");
    let error = graph_compile_error(&immutable, "graph-immutable-pattern-assignment");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error.message.contains("immutable variable 'bias'"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("immutable pattern assignment is source-spanned");
    assert_eq!(&immutable[span.start..span.end], "bias", "{error:?}");
    assert_eq!(
        span.start,
        immutable.find("#set bias").unwrap() + "#set ".len()
    );
}

#[test]
fn async_struct_payload_patterns_preserve_declared_field_order() {
    let source = include_str!("../examples/async_struct_patterns.lim");
    build_and_run(source, 42);
    let aliased = format!(
        "(#type ValuesAlias Values)\n{}",
        source.replace("(Chosen Values)", "(Chosen ValuesAlias)")
    );
    build_and_run(&aliased, 42);
    let nested = format!(
        "(#struct Bias ((only #u64)))\n{}",
        source
            .replace("(a #u64)", "(a Bias)")
            .replace("(Values value bias)", "(Values value (Bias bias))")
            .replace(": a 22u64", ": a (#struct-literal Bias (: only 22u64))")
    );
    build_and_run(&nested, 42);
    let referenced = source
        .replace("(z #u16)", "(z (#ref #u64))")
        .replace("(#as value #u64)", "(#deref value)")
        .replace(
            "\n          bias))",
            "\n          (#u64.+.wrap bias (#deref value))))",
        )
        .replace(
            "(#let waker #u64",
            "(#let owner #u64 20u64) (#let waker #u64",
        )
        .replace(": z 20u16", ": z (#borrow owner)");
    build_and_run(&referenced, 62);
    let invalid = referenced
        .replace("(#let owner #u64", "(#let-mut owner #u64")
        .replace(
            "(#block (#set task next) ())",
            "(#block (#set owner 100u64) (#set task next) ())",
        );
    assert_ne!(invalid, referenced);
    let scratch = support::Scratch::new("async-struct-pattern-borrow");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("a struct pattern's shared field must stay borrowed through work-pending");
    assert!(
        error.message.contains("owner") && error.message.contains("borrow"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("the owner assignment must retain its source span");
    assert!(
        invalid
            .lines()
            .nth(span.line - 1)
            .unwrap()
            .contains("#set owner 100u64"),
        "{error:?}"
    );
}

#[test]
fn async_while_let_aggregate_payloads_use_declared_capture_types() {
    let source = include_str!("../examples/async_while_let_dependencies.lim")
        .replace(
            "(#enum Choice ((Chosen #u64) Empty))",
            "(#enum Choice ((Chosen (#tuple #u64 #u64)) Empty))",
        )
        .replace(
            "(#while-let (Chosen value)",
            "(#while-let (Chosen (#tuple value bias))",
        )
        .replace("(Start value)))", "(Start (#u64.+.wrap value bias))))")
        .replace(
            "(Chosen 37u64)",
            "(Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))",
        );
    build_and_run(&source, 40);
    let aliased = format!(
        "(#type Pair (#tuple #u64 #u64))\n{}",
        source.replace("(Chosen (#tuple #u64 #u64))", "(Chosen Pair)")
    );
    build_and_run(&aliased, 40);
    let array = source
        .replace("(Chosen (#tuple #u64 #u64))", "(Chosen (#array #u64 2))")
        .replace(
            "(Chosen (#tuple value bias))",
            "(Chosen (#array value bias))",
        )
        .replace(
            "(Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))",
            "(Chosen (#array-of (#array #u64 2) 37u64 0u64))",
        );
    build_and_run(&array, 40);
    let alias_chain = format!(
        "(#type PairAlias Pair)\n{}",
        aliased.replace("(Chosen Pair)", "(Chosen PairAlias)")
    );
    build_and_run(&alias_chain, 40);
    let referenced = source
        .replace(
            "(Chosen (#tuple #u64 #u64))",
            "(Chosen (#tuple (#ref #u64) #u64))",
        )
        .replace(
            "(#u64.+.wrap value bias)",
            "(#u64.+.wrap (#deref value) bias)",
        )
        .replace(
            "(#let chosen #u64",
            "(#let owner #u64 37u64) (#let chosen #u64",
        )
        .replace(
            "(Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))",
            "(Chosen (#tuple (#tuple (#ref #u64) #u64) (#borrow owner) 0u64))",
        );
    build_and_run(&referenced, 40);
    let nested = source
        .replace("(Chosen (#tuple #u64 #u64))", "(Chosen (#tuple #u64 (#array #u64 2)))")
        .replace("(Chosen (#tuple value bias))", "(Chosen (#tuple value (#array bias padding)))")
        .replace("(Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))", "(Chosen (#tuple (#tuple #u64 (#array #u64 2)) 37u64 (#array-of (#array #u64 2) 0u64 0u64)))");
    build_and_run(&nested, 40);
    let scratch = support::Scratch::new("async-pattern-payload-errors");
    for invalid in [
        source.replace("(#tuple value bias)", "(#tuple value)"),
        source.replace("(#tuple value bias)", "(#tuple value value)"),
        array.replace("(#array value bias)", "(#array value)"),
    ] {
        let error = lim::compile_source_to_assembly(
            &invalid,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .err()
        .expect("invalid aggregate patterns must still be rejected");
        assert!(error.span.is_some(), "{error:?}");
    }
}

#[test]
fn async_while_let_can_await_its_scrutinee_task_inputs() {
    let definitions = include_str!("../examples/async_while_let_return.lim")
        .split_once("(#fn run")
        .unwrap()
        .0;
    let factory = "(#enum Factory ((MakeChoice Choice) (ResumeChoice Choice)))
      (#linear Factory)
      (#enum FactoryPoll ((FactoryPending Factory) (FactoryReady ChoiceTask)))
      (#fn factory-poll ((task Factory) (waker (#ref #u64))) FactoryPoll
        (#return (#match task
          (#case (MakeChoice choice) (FactoryPending (ResumeChoice choice)))
          (#case (ResumeChoice choice) (FactoryReady (ChoiceStart choice))))))";
    let source = format!("{factory}\n{}\n
      (#fn run ((choice Choice) (waker (#ref #u64))) #u64
        (#let-mut task Work-task (#call work (: choice choice)))
        (#for-range (attempt #u64) 0u64 8u64
          (#let polled Work-poll-result (#call work-poll (: task task : waker waker)))
          (#match polled
            (#case (work-pending next) (#block (#set task next) ()))
            (#case (work-ready result) (#block (#return result)))))
        (#forget task)
        (#return (#unreachable)))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let chosen #u64 (#call run (: choice (Chosen 37u64) : waker (#borrow waker))))
        (#let empty #u64 (#call run (: choice Empty : waker (#borrow waker))))
        (#return (#u64.+.wrap chosen empty)))", definitions.replace(
        "choice-poll (ChoiceStart choice)",
        "choice-poll (#await ChoiceTask Factory FactoryPending FactoryReady factory-poll (MakeChoice choice))",
    ));
    build_and_run(&source, 42);
    let immediate = source.replace(
        "(FactoryPending (ResumeChoice choice))",
        "(FactoryReady (ChoiceStart choice))",
    );
    build_and_run(&immediate, 42);
    let guarded = source.replace(
        "(#case (Start value) (StepPending (Resume value)))",
        "(#case (Start value) (#block (#assert (#u64.== value 37u64)) (StepPending (Resume value))))",
    );
    assert_ne!(guarded, source);
    build_and_run(&guarded, 42);
    let repeated = source
        .replace(
            "(#fn work ((choice Choice)) #u64",
            "(#fn work ((#mut choice Choice)) #u64\n    (#let-mut total #u64 0u64)",
        )
        .replace(
            "(#return second)",
            "(#set total (#u64.+.wrap total second)) (#set choice Empty)",
        )
        .replace("(#return 5u64)", "(#return total)");
    build_and_run(&repeated, 37);
    let effects = repeated.replace(
        "factory-poll (MakeChoice choice)",
        "factory-poll (#block (#set total (#u64.+.wrap total 1u64)) (MakeChoice choice))",
    );
    assert_ne!(effects, repeated);
    build_and_run(&effects, 40);
    let referenced = source
        .replace(
            "(#enum Choice ((Chosen #u64) Empty))",
            "(#enum Choice ((Chosen (#ref #u64)) Empty))",
        )
        .replace("(Start value)", "(Start (#deref value))")
        .replace(
            "(#let chosen #u64",
            "(#let owner #u64 37u64) (#let chosen #u64",
        )
        .replace("(Chosen 37u64)", "(Chosen (#borrow owner))");
    // Change only the async body's task input, not the poller's binding pattern.
    let referenced = referenced.replace("(#case (Start (#deref value))", "(#case (Start value)");
    build_and_run(&referenced, 42);
    let prefix = referenced.split_once("(#fn main").unwrap().0;
    let cancelled = format!(
        "{prefix}
      (#fn main () #u64
        (#let-mut owner #u64 37u64) (#let waker #u64 0u64)
        (#let frame Work-task (#call work (: choice (Chosen (#borrow owner)))))
        (#let first Work-poll-result (#call work-poll (: task frame : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#forget pending)
        (#set owner 42u64)
        (#return owner))"
    );
    build_and_run(&cancelled, 42);
    let borrowed_mutation = cancelled.replace(
        "(#forget pending)\n        (#set owner 42u64)",
        "(#set owner 42u64)\n        (#forget pending)",
    );
    assert_ne!(borrowed_mutation, cancelled);
    let scratch = support::Scratch::new("async-while-let-nested-loans");
    let error = lim::compile_source_to_assembly(
        &borrowed_mutation,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("a suspended nested task must retain its owner's loan");
    assert!(
        error.message.contains("owner") && error.message.contains("borrow"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("the owner's mutation must retain its source span");
    assert_eq!(
        &borrowed_mutation[span.start..span.end],
        "#set",
        "{error:?}"
    );
    assert!(
        borrowed_mutation
            .lines()
            .nth(span.line - 1)
            .unwrap()
            .contains("(#set owner 42u64)"),
        "{error:?}"
    );
    let invalid = source.replace("(#return 5u64)", "(#return value)");
    let scratch = support::Scratch::new("async-while-let-pattern-scope");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("the successful pattern's payload cannot escape its arm");
    assert!(
        error.message.contains("value") && error.message.contains("unknown"),
        "{error:?}"
    );
}

#[test]
fn async_loop_conditions_can_await_their_task_inputs() {
    let source = include_str!("../examples/async_early_continue.lim");
    let definitions = source.split_once("(#fn main").unwrap().0;
    let factory = "(#enum Factory ((MakeCondition #u64) (ResumeCondition #u64)))
      (#linear Factory)
      (#enum FactoryPoll ((FactoryPending Factory) (FactoryReady ConditionTask)))
      (#fn factory-poll ((task Factory) (waker (#ref #u64))) FactoryPoll
        (#return (#match task
          (#case (MakeCondition index) (FactoryPending (ResumeCondition index)))
          (#case (ResumeCondition index) (FactoryReady (Check index))))))";
    let source = format!("{factory}\n{}\n
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work-task (#call work ()))
        (#for-range (attempt #u64) 0u64 10u64
          (#let polled Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#match polled
            (#case (work-pending next) (#block (#set task next) ()))
            (#case (work-ready result) (#block (#return result)))))
        (#forget task)
        (#forget waker)
        (#return 0u64))", definitions.replace(
            "condition-poll (Check index)",
            "condition-poll (#await ConditionTask Factory FactoryPending FactoryReady factory-poll (MakeCondition index))",
        ));
    build_and_run(&source, 42);
    let implicit_condition_type =
        source.replace("(#await #bool ConditionTask", "(#await ConditionTask");
    build_and_run(&implicit_condition_type, 42);
    let repeated = source
        .replace(
            "(#let-mut index #u64 0u64)",
            "(#let-mut index #u64 0u64) (#let-mut total #u64 0u64)",
        )
        .replace(
            "(#return (#u64.+.wrap value index))",
            "(#set total (#u64.+.wrap total value))",
        )
        .replacen("(#return 0u64)", "(#return total)", 1);
    build_and_run(&repeated, 40);
    let effects = repeated.replace(
        "factory-poll (MakeCondition index)",
        "factory-poll (#block (#set total (#u64.+.wrap total 1u64)) (MakeCondition index))",
    );
    build_and_run(&effects, 43);
}

#[test]
fn async_mutating_branches_restore_their_outputs() {
    let source = "(#enum Step ((Start #u64) (Resume #u64))) (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (Start value) (StepPending (Resume value)))
          (#case (Resume value) (StepReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((selected #bool)) #u64
          (#let-mut total #u64 0u64)
          (#let value #u64 (#if selected
            (#block
              (#set total 1u64)
              (#let left #u64 (#await #u64 Step StepPending StepReady step-poll (Start 20u64)))
              (#set total 22u64)
              left)
            (#block
              (#set total 2u64)
              (#let right #u64 (#await #u64 Step StepPending StepReady step-poll (Start 30u64)))
              (#set total 12u64)
              right)))
          (#return (#u64.+.wrap total value)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work-task (#call work (: selected true)))
        (#for-range (attempt #u64) 0u64 5u64
          (#let polled Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#match polled
            (#case (work-pending next) (#block (#set task next) ()))
            (#case (work-ready result) (#block (#return result)))))
        (#forget task)
        (#return 0u64))";
    build_and_run_graph(source, 42);
    build_and_run_graph(&source.replace(": selected true", ": selected false"), 42);
    let immediate = source.replace("(StepPending (Resume value))", "(StepReady value)");
    build_and_run_graph(&immediate, 42);
    let matched = source
        .replace("(#if selected", "(#match selected (#case true")
        .replace(
            "left)\n            (#block",
            "left))\n            (#case false (#block",
        )
        .replace("right)))", "right))))");
    assert_ne!(matched, source);
    build_and_run_graph(&matched, 42);
    build_and_run_graph(&matched.replace(": selected true", ": selected false"), 42);
    let mixed = source.replace(
        "(#await #u64 Step StepPending StepReady step-poll (Start 30u64))",
        "30u64",
    );
    build_and_run_graph(&mixed, 42);
    build_and_run_graph(&mixed.replace(": selected true", ": selected false"), 42);
    let borrowed = format!(
        "(#fn put ((target (#ref-mut #u64)) (value #u64)) ()
      (#deref-set target value) (#return ()))\n{}",
        source
            .replace(
                "(#set total 22u64)",
                "(#call put (: target (#borrow-mut total) : value 22u64))"
            )
            .replace(
                "(#set total 12u64)",
                "(#call put (: target (#borrow-mut total) : value 12u64))"
            )
    );
    build_and_run_graph(&borrowed, 42);
    build_and_run_graph(&borrowed.replace(": selected true", ": selected false"), 42);
    let linear = format!("(#struct Counter ((value #u64))) (#linear Counter)\n{}", source
        .replace("(#let-mut total #u64 0u64)", "(#let-mut total Counter (#struct-literal Counter ((value 0u64))))")
        .replace("(#set total", "(#set-field total value")
        .replace("(#return (#u64.+.wrap total value))", "(#let result #u64 (#u64.+.wrap (#get total value) value)) (#forget total) (#return result)"));
    build_and_run_graph(&linear, 42);
    build_and_run_graph(&linear.replace(": selected true", ": selected false"), 42);
    let invalid = linear.replace("(#forget total)", "()");
    let error = graph_compile_error(&invalid, "async-branch-restored-owner");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(
        error.message.contains("total") && error.message.contains("consum"),
        "{error:?}"
    );
    assert!(error.span.is_some(), "{error:?}");
}

#[test]
fn async_restoring_a_local_does_not_destroy_its_previous_owner() {
    let source = "(#struct Counter ((value #u64))) (#linear Counter)
      (#enum Step ((Start #u64) (Resume #u64))) (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (Start value) (StepPending (Resume value)))
          (#case (Resume value) (StepReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut total Counter (#struct-literal Counter ((value 0u64))))
          (#forget total)
          (#let value #u64 (#await #u64 Step StepPending StepReady step-poll (Start 40u64)))
          (#set total (#struct-literal Counter ((value 2u64))))
          (#let result #u64 (#u64.+.wrap value (#get total value)))
          (#forget total)
          (#return result))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work ()) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task next : waker (#borrow waker))))
        (#return (#match second
          (#case (work-ready result) result)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))";
    build_and_run(source, 42);
    let invalid = source.replacen("(#forget total)", "()", 1);
    let scratch = support::Scratch::new("async-overwritten-owner");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("an overwritten old owner cannot disappear at suspension");
    assert!(
        error.message.contains("total") && error.message.contains("consum"),
        "{error:?}"
    );
}

#[test]
fn async_task_construction_precedes_capture_snapshots() {
    let source = "(#enum Step ((Start #u64) (Resume #u64))) (#linear Step)
      (#enum StepPoll ((StepPending Step) (StepReady #u64)))
      (#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case (Start value) (StepPending (Resume value)))
          (#case (Resume value) (StepReady value)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut total #u64 0u64)
          (#let left #u64 (#await #u64 Step StepPending StepReady step-poll
            (#block (#set total (#u64.+.wrap total 1u64)) (Start 20u64))))
          (#let right #u64 (#await #u64 Step StepPending StepReady step-poll
            (#block (#set total (#u64.+.wrap total 1u64)) (Start left))))
          (#return (#u64.+.wrap (#u64.+.wrap left right) total)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut task Work-task (#call work ()))
        (#for-range (attempt #u64) 0u64 5u64
          (#let polled Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#match polled
            (#case (work-pending next) (#block (#set task next) ()))
            (#case (work-ready result) (#block (#return result)))))
        (#forget task)
        (#return 0u64))";
    build_and_run(source, 42);
    let immediate = source.replace("(StepPending (Resume value))", "(StepReady value)");
    build_and_run(&immediate, 42);
    // Explicit task temporaries and direct task expressions have identical
    // sequencing, including construction of the second stage after resume.
    let temporaries = source.replace(
        "(#let left #u64 (#await #u64 Step StepPending StepReady step-poll\n            (#block (#set total (#u64.+.wrap total 1u64)) (Start 20u64))))",
        "(#let first Step (#block (#set total (#u64.+.wrap total 1u64)) (Start 20u64)))\n          (#let left #u64 (#await #u64 Step StepPending StepReady step-poll first))",
    ).replace(
        "(#let right #u64 (#await #u64 Step StepPending StepReady step-poll\n            (#block (#set total (#u64.+.wrap total 1u64)) (Start left))))",
        "(#let second Step (#block (#set total (#u64.+.wrap total 1u64)) (Start left)))\n          (#let right #u64 (#await #u64 Step StepPending StepReady step-poll second))",
    );
    assert_ne!(temporaries, source);
    build_and_run(&temporaries, 42);
}

#[test]
fn async_early_continue_skips_the_rest_of_the_iteration() {
    let source = include_str!("../examples/async_early_continue.lim");
    build_and_run(source, 42);
    let matched = source.replace(
        "(#if (#u64.== index 1u64) (#continue) ())",
        "(#match index (#case 1u64 (#continue)) (#case _ ()))",
    );
    assert_ne!(matched, source);
    build_and_run(&matched, 42);
    let guarded = format!("(#enum Index ((Current #u64)))\n{}", source.replace(
        "(#if (#u64.== index 1u64) (#continue) ())",
        "(#match (Current index) (#case (Current amount) (#when (#u64.== amount 1u64)) (#continue)) (#case _ ()))",
    ));
    assert_ne!(guarded, source);
    build_and_run(&guarded, 42);

    let scoped = source.replace(
        "(#if (#u64.== index 1u64) (#continue) ())",
        "(#if (#u64.== index 1u64) (#block (#let local #u64 1u64) (#assert (#u64.== local 1u64)) (#continue)) ())",
    );
    assert_ne!(scoped, source);
    build_and_run(&scoped, 42);
    let reused_local = scoped
        .replace("(#let value #u64", "(#let local #u64")
        .replace("(#u64.+.wrap value index)", "(#u64.+.wrap local index)");
    build_and_run(&reused_local, 42);
    let nested = source.replace(
        "(#set index (#u64.+.wrap index 1u64))",
        "(#set index (#u64.+.wrap index 1u64)) (#for-range (inner #u64) 0u64 1u64 (#break))",
    );
    build_and_run(&nested, 42);
    let short_main = "(#fn main () #u64
      (#let waker #u64 0u64)
      (#let first Work-poll-result (#call work-poll (: task (#call work ()) : waker (#borrow waker))))
      (#let-else (work-pending task) Work-poll-result first (#unreachable))
      (#let second Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
      (#return (#match second
        (#case (work-ready value) value)
        (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))";
    let work = source.split_once("(#fn main").unwrap().0;
    let broken = format!(
        "{}{}",
        work.replace("(#continue)", "(#break)")
            .replace("(#return 0u64)", "(#return 42u64)"),
        short_main
    );
    build_and_run(&broken, 42);
    let returned = format!(
        "{}{}",
        work.replace("(#continue)", "(#return 41u64)"),
        short_main
    );
    build_and_run(&returned, 41);
    let for_loop = source.replace(
        "(#while (#await #bool ConditionTask ConditionPending ConditionReady condition-poll (Check index))\n      (#set index (#u64.+.wrap index 1u64))",
        "(#for () (#await #bool ConditionTask ConditionPending ConditionReady condition-poll (Check index))\n      (#set index (#u64.+.wrap index 1u64))",
    ).replace("(#u64.== index 1u64)", "(#u64.== index 0u64)");
    assert_ne!(for_loop, source);
    build_and_run(&for_loop, 41);
}

#[test]
fn terminalized_async_branches_preserve_lexical_scope_and_shadowing_rules() {
    let source = include_str!("../examples/async_early_continue.lim");
    let scoped = source.replace(
        "(#if (#u64.== index 1u64) (#continue) ())",
        "(#if (#u64.== index 1u64) (#block (#let local #u64 1u64) (#continue)) ())",
    );
    let scratch = support::Scratch::new("async-terminal-scope");
    let input = scratch.path().join("scope.lim");
    let leaked = scoped.replace("(#u64.+.wrap value index)", "(#u64.+.wrap value local)");
    let error = lim::compile_source_to_assembly(
        &leaked,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("local") && error.message.contains("unknown"),
        "{error:?}"
    );
    let span = error.span.expect("escaped branch-local use span");
    assert_eq!(&leaked[span.start..span.end], "local");
    assert_eq!(
        span.start,
        leaked.find("value local").unwrap() + "value ".len()
    );
    let shadowed = scoped.replace("(#let local #u64 1u64)", "(#let index #u64 1u64)");
    let error = lim::compile_source_to_assembly(
        &shadowed,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("shadow"), "{error:?}");
    let span = error.span.expect("original shadowed declaration span");
    assert_eq!(&shadowed[span.start..span.end], "index");
    let global_shadow = format!("(#const local #u64 9u64)\n{scoped}");
    let error = lim::compile_source_to_assembly(
        &global_shadow,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("shadow"), "{error:?}");
    let resource = format!(
        "(#struct Resource ((value #u64))) (#linear Resource)\n{}",
        scoped.replace(
            "(#let local #u64 1u64)",
            "(#let local Resource (#struct-literal Resource ((value 1u64))))",
        )
    );
    let error = lim::compile_source_to_assembly(
        &resource,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("local") && error.message.contains("consumed"),
        "{error:?}"
    );
    let consumed = resource.replace("(#continue)", "(#forget local) (#continue)");
    build_and_run(&consumed, 42);
}

#[test]
fn async_for_effect_step_awaits_with_a_synchronous_condition() {
    let source = include_str!("../examples/async_for_effect_step.lim");
    build_and_run(source, 42);
    let returned = source.replace("(#break)", "(#return (#u64.+.wrap index 40u64))");
    build_and_run(&returned, 42);
    let matched = source.replace(
        "(#if (#u64.== index 0u64)\n        (#continue)\n        (#if stop (#break) ()))",
        "(#match index (#case 0u64 (#continue)) (#case _ (#if stop (#break) ())))",
    );
    assert_ne!(matched, source);
    build_and_run(&matched, 42);
    let effects = source
        .replace("(#fn advance", "(#fn touch (: counter (#ref-mut #u64)) #u64\n  (#deref-set counter (#u64.+.wrap (#deref counter) 1u64))\n  (#return 1u64))\n\n(#fn advance")
        .replace("(#let-mut index #u64 0u64)", "(#let-mut index #u64 0u64) (#let-mut touches #u64 0u64)")
        .replace("(: next (#await", "(: next (#u64.+.wrap (#call touch (: counter (#borrow-mut touches))) (#await")
        .replace("(Start (#u64.+.wrap index 1u64)))", "(Start index)))")
        .replace("(#return (#u64.+.wrap index 40u64))", "(#assert (#u64.== touches index)) (#return (#u64.+.wrap index 40u64))");
    assert_ne!(effects, source);
    build_and_run(&effects, 42);
}

#[test]
fn async_for_effect_step_consumes_linear_operands_and_results() {
    let source = include_str!("../examples/async_for_effect_step.lim");
    let source = format!(
        "(#struct Resource ((value #u64)))\n(#linear Resource)\n{}",
        source
            .replace(
                "((Start #u64) (Resume #u64))",
                "((Start Resource) (Resume Resource))"
            )
            .replace("(StepReady #u64)", "(StepReady Resource)")
            .replace("(: next #u64 : counter", "(: next Resource : counter")
            .replace(
                "(#deref-set counter next)",
                "(#deref-set counter (#get next value))\n  (#forget next)"
            )
            .replace("(#await #u64 StepTask", "(#await Resource StepTask")
            .replace(
                "(Start (#u64.+.wrap index 1u64))",
                "(Start (#struct-literal Resource ((value (#u64.+.wrap index 1u64)))))"
            )
    );
    build_and_run(&source, 42);

    // Cancel after the child owns a Resource; explicitly consume that state.
    let continuation = source.find("(#let second Work-poll-result").unwrap();
    let cancelled = format!(
        "{} (#forget first-task) (#return 42u64))",
        &source[..continuation]
    );
    build_and_run(&cancelled, 42);

    let missing_cleanup = source.replace("(#forget next)", "()");
    let scratch = support::Scratch::new("async-effect-step-linear-cleanup");
    let error = lim::compile_source_to_assembly(
        &missing_cleanup,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("next"), "{error:?}");
    assert!(error.message.contains("consum"), "{error:?}");
    assert!(error.span.is_some(), "{error:?}");

    let missing_cancellation = cancelled.replace("(#forget first-task)", "()");
    let error = lim::compile_source_to_assembly(
        &missing_cancellation,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cancel-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("first-task"), "{error:?}");
    assert!(error.message.contains("consum"), "{error:?}");
    assert!(error.span.is_some(), "{error:?}");
}

#[test]
fn async_for_effect_step_keeps_external_loans_until_ready_or_cancel() {
    let definitions = include_str!("../examples/async_for_effect_step.lim")
        .split("(@#async-fn")
        .next()
        .unwrap();
    let source = format!(
        r#"{definitions}
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work (: counter (#ref-mut #u64)) #u64
          (#for () (#u64.< (#deref counter) 2u64)
            (#call advance (: next (#await #u64 StepTask StepPending StepReady step-poll
                                      (Start (#u64.+.wrap (#deref counter) 1u64)))
                            : counter counter)) ())
          (#return (#u64.+.wrap (#deref counter) 40u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut owner #u64 0u64)
        (#let first Work-poll-result (#call work-poll
          (: task (#call work (: counter (#borrow-mut owner))) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let-else (work-pending last-task) Work-poll-result second (#unreachable))
        (#let third Work-poll-result (#call work-poll (: task last-task : waker (#borrow waker))))
        (#let-else (work-ready result) Work-poll-result third (#unreachable))
        (#assert (#u64.== owner 2u64))
        (#return result))"#
    );
    build_and_run(&source, 42);
    let continuation = source.find("(#let second Work-poll-result").unwrap();
    let cancelled = format!(
        "{} (#forget pending) (#set owner 42u64) (#return owner))",
        &source[..continuation]
    );
    build_and_run(&cancelled, 42);
    let invalid = source.replace(
        "(#let second Work-poll-result",
        "(#set owner 9u64) (#let second Work-poll-result",
    );
    let scratch = support::Scratch::new("async-effect-step-live-loan");
    let error = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("the suspended step retains its exclusive external loan");
    assert!(error.message.contains("borrow"), "{error:?}");
    let span = error.span.unwrap();
    let mutation = invalid.find("(#set owner 9u64)").unwrap();
    assert_eq!(span.start, mutation + 1);
    assert_eq!(&invalid[span.start..span.end], "#set");
}

#[test]
fn async_for_computed_step_composes_with_awaited_condition() {
    let source = include_str!("../examples/async_for_computed_step.lim");
    build_and_run(source, 42);
    let transfers = source
        .replace("(#u64.< index 2u64)", "(#u64.< index 4u64)")
        .replace(
            "(#let body-ran #bool true))",
            "(#let body-ran #bool true) (#if (#u64.== index 0u64) (#continue) (#break)))",
        );
    assert_ne!(transfers, source);
    build_and_run(&transfers, 42);
    let returned = transfers.replace("(#break)", "(#return (#u64.+.wrap index 40u64))");
    assert_ne!(returned, transfers);
    build_and_run(&returned, 42);
    for source in [&transfers, &returned] {
        let matched = source
            .replace(
                "(#if (#u64.== index 0u64) (#continue)",
                "(#match index (#case 0u64 (#continue)) (#case _",
            )
            .replace("(#break)))", "(#break))))")
            .replace(
                "(#return (#u64.+.wrap index 40u64))))",
                "(#return (#u64.+.wrap index 40u64)))))",
            );
        assert_ne!(matched, *source);
        build_and_run(&matched, 42);
    }
}

#[test]
fn async_loop_body_restores_values_mutated_through_borrowed_places() {
    for (ty, initial, place, argument, prefix, suffix) in [
        ("#u64", "0u64", "counter", "(#borrow-mut counter)", "", ""),
        (
            "Counter",
            "(#struct-literal Counter ((value 0u64)))",
            "(#get counter value)",
            "(#borrow-mut (#get container value))",
            "(#let container (#ref-mut Counter) (#borrow-mut counter))",
            "(#forget container)",
        ),
        (
            "(#array #u64 1)",
            "(#array-of (#array #u64 1) 0u64)",
            "(#index counter 0usize)",
            "(#slice-mut-idx container 0usize)",
            "(#let container (#slice-mut #u64) (#slice-mut-of (#borrow-mut counter)))",
            "(#forget container)",
        ),
    ] {
        let source = format!(
            r#"
          (#struct Counter ((value #u64)))
          (#enum ChildTask (Start Resume))
          (#linear ChildTask)
          (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
          (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
            (#return (#match task
              (#case Start (ChildPending Resume))
              (#case Resume (ChildReady true)))))
          (#fn touch ((value (#ref-mut #u64))) ()
            (#deref-set value (#u64.+.wrap (#deref value) 1u64))
            (#return ()))
          (@#async-fn (: protocol work-await : waker #u64 : function
            (#fn work () #u64
              (#let-mut counter {ty} {initial})
              (#let-mut keep #bool true)
              (#while keep
                {prefix}
                (#call touch (: value {argument}))
                {suffix}
                (#set keep (#bool.&&
                  (#await #bool ChildTask ChildPending ChildReady child-poll Start) false)))
              (#return (#u64.+.wrap {place} 41u64)))))
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let first Work-poll-result (#call work-poll (: task (#call work ()) : waker (#borrow waker))))
            (#let-else (work-pending task) Work-poll-result first (#unreachable))
            (#let second Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
            (#return (#match second
              (#case (work-ready value) value)
              (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
        "#
        );
        build_and_run_graph(&source, 42);
        if ty == "(#array #u64 1)" {
            let retained = source.replace(
                &format!("(#call touch (: value {argument}))"),
                &format!(
                    "(#let selected (#ref-mut #u64) {argument})
                     (#call touch (: value selected))
                     (#call touch (: value selected))
                     (#forget selected)"
                ),
            );
            build_and_run_graph(&retained, 43);
            let conflicting = retained.replace(
                "(#forget selected)",
                "(#set-index counter 0usize 0u64) (#forget selected)",
            );
            let error = graph_compile_error(&conflicting, "movable-slice-live-child");
            assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
            let span = error.span.unwrap();
            assert_eq!(&conflicting[span.start..span.end], "#set-index");
        }
    }
}

#[test]
fn pinned_mutable_slice_holder_reborrows_elements_without_moving_holder() {
    let source = r#"
      (#fn lend (: holder (#pin-ref-mut (#slice-mut #u64))) (#slice-mut #u64)
        (#return (#slice-mut-range (#deref holder) 0usize (#slice-mut-len (#deref holder)))))
      (#fn main () #u64
        (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 41u64))
        (#let-mut items (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
        (#let range (#slice-mut #u64) (#call lend (: holder (#pin items))))
        (#deref-set (#slice-mut-idx range 0usize) 42u64)
        (#forget range)
        (#forget items)
        (#return (#index values 0usize)))
    "#;
    build_and_run_graph(source, 42);
    let conflicting = source.replace(
        "(#forget range)",
        "(#set-index values 0usize 0u64) (#forget range)",
    );
    let error = graph_compile_error(&conflicting, "pinned-slice-retained-owner");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&conflicting[span.start..span.end], "#set-index");
    let shared = source
        .replace(
            "(#pin-ref-mut (#slice-mut #u64))",
            "(#pin-ref (#slice-mut #u64))",
        )
        .replace("(#pin items)", "(#pin-shared items)");
    let error = graph_compile_error(&shared, "pinned-slice-shared-holder");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(error.message.contains("exclusive"), "{error:?}");
}

fn external_mutable_slice_source() -> &'static str {
    r#"
      (#enum ChildTask (Start Resume))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady ())))
      (#fn child-poll (: task ChildTask : waker (#ref #u64)) ChildPoll
        (#return (#match task
          (#case Start (ChildPending Resume))
          (#case Resume (ChildReady ())))))
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work (: items (#slice-mut #u64)) #u64
          (#let view (#ref-mut #u64) (#slice-mut-idx items 0usize))
          (#deref-set view (#u64.+.wrap (#deref view) 1u64))
          (#forget view)
          (#await () ChildTask ChildPending ChildReady child-poll Start)
          (#let answer #u64 (#deref (#slice-mut-idx items 0usize)))
          (#forget items)
          (#return answer))))
      (#fn main () #u64
        (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 41u64))
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: items (#slice-mut-of (#borrow-mut values)))) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#assert (#u64.== (#index values 0usize) 42u64))
        (#return answer))
    "#
}

#[test]
fn graph_external_mutable_slice_indices_preserve_lending_and_pending() {
    let source = external_mutable_slice_source();
    let generated = build_and_run_graph(source, 42);
    let runtime = source.split_once("(@#async-fn").unwrap().0;
    let main = source.split_once("(#fn main").unwrap().1;
    let standalone = format!("{runtime}\n{generated}\n(#fn main{main}");
    build_and_run_graph(&standalone, 42);
    let aliased = format!(
        "(#type Items (#slice-mut #u64))\n{}",
        source.replace(": items (#slice-mut #u64)", ": items Items")
    );
    build_and_run_graph(&aliased, 42);
    let indexed = source
        .replace(
            "(#let view (#ref-mut #u64)",
            "(#let index #usize 0usize)\n          (#let view (#ref-mut #u64)",
        )
        .replace(
            "(#slice-mut-idx items 0usize)",
            "(#slice-mut-idx items index)",
        );
    build_and_run_graph(&indexed, 42);
    let conflicting = source.replace(
        "(#let answer #u64 (#match",
        "(#set-index values 0usize 0u64)\n        (#let answer #u64 (#match",
    );
    let error = graph_compile_error(&conflicting, "graph-slice-pending-owner-write");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&conflicting[span.start..span.end], "#set-index");
}

#[test]
fn graph_external_mutable_slice_element_reference_survives_pending() {
    let source = external_mutable_slice_source();
    let retained = source.replace("(#forget view)", "").replace(
        "(#let answer #u64 (#deref (#slice-mut-idx items 0usize)))",
        "(#let answer #u64 (#deref view)) (#forget view)",
    );
    let generated = build_and_run_graph(&retained, 42);
    let runtime = retained.split_once("(@#async-fn").unwrap().0;
    let main = retained.split_once("(#fn main").unwrap().1;
    build_and_run_graph(&format!("{runtime}\n{generated}\n(#fn main{main}"), 42);
    let indexed = retained
        .replace(
            "(#let view (#ref-mut #u64)",
            "(#let-mut index #usize 2usize)\n          (#let view (#ref-mut #u64)",
        )
        .replace(
            "(#slice-mut-idx items 0usize)",
            "(#slice-mut-idx items index)",
        )
        .replace(
            "(#await () ChildTask",
            "(#set index 0usize) (#await () ChildTask",
        )
        .replace("(#array #u64 1)", "(#array #u64 3)")
        .replace(
            "(#array-of (#array #u64 3) 41u64)",
            "(#array-of (#array #u64 3) 1u64 2u64 41u64)",
        )
        .replace("(#index values 0usize)", "(#index values 2usize)");
    build_and_run_graph(&indexed, 42);
    let aliased = format!(
        "(#type Items (#slice-mut #u64))\n{}",
        indexed.replace(": items (#slice-mut #u64)", ": items Items")
    );
    build_and_run_graph(&aliased, 42);
    let conflicting = indexed.replace(
        "(#let answer #u64 (#match",
        "(#set-index values 2usize 0u64)\n        (#let answer #u64 (#match",
    );
    let error = graph_compile_error(&conflicting, "retained-slice-element-owner-write");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&conflicting[span.start..span.end], "#set-index");
}

#[test]
fn graph_slice_element_anchors_preserve_wide_shared_and_zero_sized_layouts() {
    let retained = external_mutable_slice_source()
        .replace("(#forget view)", "")
        .replace(
            "(#let answer #u64 (#deref (#slice-mut-idx items 0usize)))",
            "(#let answer #u64 (#deref view)) (#forget view)",
        )
        .replace(
            "(#let view (#ref-mut #u64)",
            "(#let index #usize 1usize) (#let view (#ref-mut #u64)",
        )
        .replace(
            "(#slice-mut-idx items 0usize)",
            "(#slice-mut-idx items index)",
        )
        .replace("(#array #u64 1)", "(#array #u64 2)")
        .replace(
            "(#array-of (#array #u64 2) 41u64)",
            "(#array-of (#array #u64 2) 3u64 41u64)",
        )
        .replace("(#index values 0usize)", "(#index values 1usize)");
    build_and_run_graph(&retained.replace("u64", "u128"), 42);
    let shared = retained
        .replace("(#deref-set view (#u64.+.wrap (#deref view) 1u64))", "")
        .replace("41u64", "42u64")
        .replace("#ref-mut", "#ref")
        .replace("#slice-mut", "#slice")
        .replace("#borrow-mut values", "#borrow values");
    build_and_run_graph(&shared, 42);

    let runtime = external_mutable_slice_source()
        .split_once("(@#async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
      (#struct Empty ())
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work (: items (#slice-mut Empty)) #u64
          (#let index #usize 2usize)
          (#let view (#ref-mut Empty) (#slice-mut-idx items index))
          (#await () ChildTask ChildPending ChildReady child-poll Start)
          (#let observed Empty (#deref view)) (#forget observed)
          (#forget view) (#forget items) (#return 42u64))))
      (#fn main () #u64
        (#let-mut values (#array Empty 3) (#array-of (#array Empty 3)
          (#struct-literal Empty ()) (#struct-literal Empty ()) (#struct-literal Empty ())))
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: items (#slice-mut-of (#borrow-mut values)))) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))"#
    );
    build_and_run_graph(&source, 42);
}

#[test]
fn graph_slice_element_reference_selects_external_holders_across_branches() {
    let source = external_mutable_slice_source()
        .replace("(#forget view)", "")
        .replace(
            "(#let answer #u64 (#deref (#slice-mut-idx items 0usize)))",
            "(#let answer #u64 (#deref view)) (#forget view)",
        )
        .replace(
            ": items (#slice-mut #u64)",
            ": items (#slice-mut #u64) : other (#slice-mut #u64) : choose #bool",
        )
        .replace(
            "(#slice-mut-idx items 0usize)",
            "(#if choose (#slice-mut-idx items 0usize) (#slice-mut-idx other 0usize))",
        )
        .replace("(#forget items)", "(#forget items) (#forget other)")
        .replace(
            "(#let waker #u64 0u64)",
            "(#let-mut second (#array #u64 1) (#array-of (#array #u64 1) 41u64)) (#let waker #u64 0u64)",
        )
        .replace(
            ": items (#slice-mut-of (#borrow-mut values))",
            ": items (#slice-mut-of (#borrow-mut values)) : other (#slice-mut-of (#borrow-mut second)) : choose true",
        )
        .replace(
            "(#u64.== (#index values 0usize) 42u64)",
            "(#u64.== (#u64.+.wrap (#index values 0usize) (#index second 0usize)) 83u64)",
        );
    build_and_run_graph(&source, 42);
    build_and_run_graph(&source.replace(": choose true", ": choose false"), 42);
    for owner in ["values", "second"] {
        let conflicting = source.replace(
            "(#let answer #u64 (#match",
            &format!("(#set-index {owner} 0usize 0u64) (#let answer #u64 (#match"),
        );
        let error = graph_compile_error(&conflicting, "branched-slice-owner-write");
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        let span = error.span.unwrap();
        assert_eq!(&conflicting[span.start..span.end], "#set-index");
    }
}

#[test]
fn graph_slice_nested_array_selection_does_not_probe_a_dormant_invalid_branch() {
    let source = external_mutable_slice_source()
        .replace("(#forget view)", "")
        .replace(
            "(#let answer #u64 (#deref (#slice-mut-idx items 0usize)))",
            "(#let answer #u64 (#deref view)) (#forget view)",
        )
        .replace(": items (#slice-mut #u64)", ": items (#slice-mut (#array #u64 2)) : choose #bool")
        .replace(
            "(#slice-mut-idx items 0usize)",
            "(#if choose (#borrow-mut (#index row 0usize)) (#borrow-mut (#index row 2usize)))",
        )
        .replace("(#let view (#ref-mut #u64)", "(#let row (#ref-mut (#array #u64 2)) (#slice-mut-idx items 0usize)) (#let view (#ref-mut #u64)")
        .replace("(#forget view)", "(#forget view) (#forget row)")
        .replace("(#array #u64 1)", "(#array (#array #u64 2) 1)")
        .replace(
            "(#array-of (#array (#array #u64 2) 1) 41u64)",
            "(#array-of (#array (#array #u64 2) 1) (#array-of (#array #u64 2) 41u64 17u64))",
        )
        .replace(": items (#slice-mut-of (#borrow-mut values))", ": items (#slice-mut-of (#borrow-mut values)) : choose true")
        .replace("(#index values 0usize)", "(#index (#index values 0usize) 0usize)");
    build_and_run_graph(&source, 42);
    let invalid_first = source
        .replace("(#index row 0usize)", "(#index row swap)")
        .replace("(#index row 2usize)", "(#index row 0usize)")
        .replace("(#index row swap)", "(#index row 2usize)")
        .replace(": choose true", ": choose false");
    build_and_run_graph(&invalid_first, 42);
    let nested_struct = format!(
        "(#struct Row (: padding #u128 : cells (#array #u64 2)))\n{}",
        invalid_first
            .replace("(#slice-mut (#array #u64 2))", "(#slice-mut Row)")
            .replace("(#ref-mut (#array #u64 2))", "(#ref-mut Row)")
            .replace("(#array (#array #u64 2) 1)", "(#array Row 1)")
            .replace("(#array-of (#array #u64 2) 41u64 17u64)",
                "(#struct-literal Row (: padding 0u128 : cells (#array-of (#array #u64 2) 41u64 17u64)))")
            .replace("(#index row ", "(#index (#get row cells) ")
            .replace("(#index (#index values 0usize) 0usize)",
                "(#index (#get (#index values 0usize) cells) 0usize)")
    );
    build_and_run_graph(&nested_struct, 42);
    // Skipping an impossible reconstruction candidate does not authorize the
    // original selection: the selected invalid source branch still traps.
    build_and_run_route_status(
        &invalid_first.replace(": choose false", ": choose true"),
        None,
        true,
    );
}

#[test]
fn graph_slice_nested_runtime_coordinates_survive_index_mutation() {
    let runtime = external_mutable_slice_source()
        .split_once("(@#async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
      (#struct Row (: padding #u128 : cells (#array #u64 2)))
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work (: items (#slice-mut Row)) #u64
          (#let-mut outer #usize 1usize) (#let-mut inner #usize 1usize)
          (#let row (#ref-mut Row) (#slice-mut-idx items outer))
          (#let view (#ref-mut #u64) (#borrow-mut (#index (#get row cells) inner)))
          (#deref-set view (#u64.+.wrap (#deref view) 1u64))
          (#set outer 0usize) (#set inner 0usize)
          (#await () ChildTask ChildPending ChildReady child-poll Start)
          (#let answer #u64 (#deref view))
          (#forget view) (#forget row) (#forget items) (#return answer))))
      (#fn main () #u64
        (#let-mut values (#array Row 2) (#array-of (#array Row 2)
          (#struct-literal Row (: padding 0u128 : cells (#array-of (#array #u64 2) 3u64 4u64)))
          (#struct-literal Row (: padding 7u128 : cells (#array-of (#array #u64 2) 17u64 41u64)))))
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: items (#slice-mut-of (#borrow-mut values)))) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#assert (#u64.== (#index (#get (#index values 1usize) cells) 1usize) 42u64))
        (#assert (#u64.== (#index (#get (#index values 0usize) cells) 1usize) 4u64))
        (#return answer))"#
    );
    let generated = build_and_run_graph(&source, 42);
    let declarations = source.split_once("(@#async-fn").unwrap().0;
    let main = source.split_once("(#fn main").unwrap().1;
    build_and_run_graph(&format!("{declarations}\n{generated}\n(#fn main{main}"), 42);
    let shared = source
        .replace("(#deref-set view (#u64.+.wrap (#deref view) 1u64))", "")
        .replace("41u64", "42u64")
        .replace("#slice-mut", "#slice")
        .replace("#ref-mut", "#ref")
        .replace("#borrow-mut", "#borrow");
    build_and_run_graph(&shared, 42);
    let single = source
        .replace("(#array Row 2)", "(#array Row 1)")
        .replace(
            "(#let-mut outer #usize 1usize)",
            "(#let-mut outer #usize 0usize)",
        )
        .replace(
            "(#struct-literal Row (: padding 0u128 : cells (#array-of (#array #u64 2) 3u64 4u64)))",
            "",
        )
        .replace(
            "(#assert (#u64.== (#index (#get (#index values 0usize) cells) 1usize) 4u64))",
            "",
        )
        .replace("(#index values 1usize)", "(#index values 0usize)");
    build_and_run_graph(&single, 42);
    let nested = source
        .replace("(#array #u64 2)", "(#array (#array #u64 2) 2)")
        .replace("(#array-of (#array (#array #u64 2) 2) 3u64 4u64)", "(#array-of (#array (#array #u64 2) 2) (#array-of (#array #u64 2) 3u64 4u64) (#array-of (#array #u64 2) 3u64 4u64))")
        .replace("(#array-of (#array (#array #u64 2) 2) 17u64 41u64)", "(#array-of (#array (#array #u64 2) 2) (#array-of (#array #u64 2) 17u64 41u64) (#array-of (#array #u64 2) 17u64 41u64))")
        .replace("(#let view (#ref-mut #u64) (#borrow-mut (#index (#get row cells) inner)))", "(#let-mut deep #usize 1usize) (#let slab (#ref-mut (#array #u64 2)) (#borrow-mut (#index (#get row cells) inner))) (#let view (#ref-mut #u64) (#borrow-mut (#index slab deep)))")
        .replace("(#set inner 0usize)", "(#set inner 0usize) (#set deep 0usize)")
        .replace("(#forget view)", "(#forget view) (#forget slab)")
        .replace("(#index (#get (#index values 1usize) cells) 1usize)", "(#index (#index (#get (#index values 1usize) cells) 1usize) 1usize)")
        .replace("(#index (#get (#index values 0usize) cells) 1usize)", "(#index (#index (#get (#index values 0usize) cells) 1usize) 1usize)");
    build_and_run_graph(&nested, 42);
    let zero_sized = format!(
        "(#struct Empty ())\n{}",
        source
            .replace("(#array #u64 2)", "(#array Empty 2)")
            .replace(
                "3u64 4u64",
                "(#struct-literal Empty ()) (#struct-literal Empty ())"
            )
            .replace(
                "17u64 41u64",
                "(#struct-literal Empty ()) (#struct-literal Empty ())"
            )
            .replace("(#let view (#ref-mut #u64)", "(#let view (#ref-mut Empty)")
            .replace("(#deref-set view (#u64.+.wrap (#deref view) 1u64))", "")
            .replace(
                "(#let answer #u64 (#deref view))",
                "(#let observed Empty (#deref view)) (#forget observed) (#let answer #u64 42u64)"
            )
            .replace(
                "(#assert (#u64.== (#index (#get (#index values 1usize) cells) 1usize) 42u64))",
                ""
            )
            .replace(
                "(#assert (#u64.== (#index (#get (#index values 0usize) cells) 1usize) 4u64))",
                ""
            )
    );
    build_and_run_graph(&zero_sized, 42);
    let branched = source
        .replace(": items (#slice-mut Row)", ": items (#slice-mut Row) : choose #bool")
        .replace("(#borrow-mut (#index (#get row cells) inner))", "(#if choose (#borrow-mut (#index (#get row cells) inner)) (#borrow-mut (#index (#get row cells) 0usize)))")
        .replace(": items (#slice-mut-of (#borrow-mut values))", ": items (#slice-mut-of (#borrow-mut values)) : choose true");
    build_and_run_graph(&branched, 42);
    let constant_branch = branched.replace(": choose true", ": choose false").replace(
        "(#index (#get (#index values 1usize) cells) 1usize) 42u64",
        "(#index (#get (#index values 1usize) cells) 0usize) 18u64",
    );
    build_and_run_graph(&constant_branch, 18);
    let conflicting = source.replace("(#let answer #u64 (#match", "(#set-index values 1usize (#struct-literal Row (: padding 0u128 : cells (#array-of (#array #u64 2) 0u64 0u64)))) (#let answer #u64 (#match");
    let error = graph_compile_error(&conflicting, "nested-slice-pending-owner-write");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&conflicting[span.start..span.end], "#set-index");
}

#[test]
fn graph_selected_reference_mixes_slice_and_external_reference_targets() {
    let source = external_mutable_slice_source()
        .replace("(#forget view)", "")
        .replace("(#let answer #u64 (#deref (#slice-mut-idx items 0usize)))", "(#let answer #u64 (#deref view)) (#forget view)")
        .replace(": items (#slice-mut #u64)", ": items (#slice-mut #u64) : fallback (#ref-mut #u64) : choose #bool")
        .replace("(#slice-mut-idx items 0usize)", "(#if choose (#slice-mut-idx items 0usize) (#borrow-mut (#deref fallback)))")
        .replace("(#forget items)", "(#forget items) (#forget fallback)")
        .replace("(#let waker #u64 0u64)", "(#let-mut fallback #u64 41u64) (#let waker #u64 0u64)")
        .replace(": items (#slice-mut-of (#borrow-mut values))", ": items (#slice-mut-of (#borrow-mut values)) : fallback (#borrow-mut fallback) : choose true")
        .replace("(#u64.== (#index values 0usize) 42u64)", "(#u64.== (#u64.+.wrap (#index values 0usize) fallback) 83u64)");
    build_and_run_graph(&source, 42);
    build_and_run_graph(&source.replace(": choose true", ": choose false"), 42);
    let aliased = format!(
        "(#type Items (#slice-mut #u64)) (#type Fallback (#ref-mut #u64))\n{}",
        source
            .replace(": items (#slice-mut #u64)", ": items Items")
            .replace(": fallback (#ref-mut #u64)", ": fallback Fallback")
    );
    build_and_run_graph(&aliased, 42);
    let shared = source
        .replace("(#deref-set view (#u64.+.wrap (#deref view) 1u64))", "")
        .replace("41u64", "42u64")
        .replace("83u64", "84u64")
        .replace("#ref-mut", "#ref")
        .replace("#slice-mut", "#slice")
        .replace("#borrow-mut", "#borrow");
    build_and_run_graph(&shared, 42);
    build_and_run_graph(&shared.replace(": choose true", ": choose false"), 42);
    let field = format!(
        "(#struct Data (: padding #u128 : value #u64))\n{}",
        source
            .replace(": fallback (#ref-mut #u64)", ": fallback (#ref-mut Data)")
            .replace(
                "(#borrow-mut (#deref fallback))",
                "(#borrow-mut (#get fallback value))"
            )
            .replace(
                "(#let-mut fallback #u64 41u64)",
                "(#let-mut fallback Data (#struct-literal Data (: padding 0u128 : value 41u64)))"
            )
            .replace(
                "(#u64.+.wrap (#index values 0usize) fallback)",
                "(#u64.+.wrap (#index values 0usize) (#get fallback value))"
            )
    );
    build_and_run_graph(&field, 42);
    build_and_run_graph(&field.replace(": choose true", ": choose false"), 42);
    let array = source
        .replace(
            ": fallback (#ref-mut #u64)",
            ": fallback (#ref-mut (#array #u64 2))",
        )
        .replace(
            "(#let-mut fallback #u64 41u64)",
            "(#let-mut fallback (#array #u64 2) (#array-of (#array #u64 2) 17u64 41u64))",
        )
        .replace(
            "(#let view (#ref-mut #u64)",
            "(#let-mut index #usize 1usize) (#let view (#ref-mut #u64)",
        )
        .replace(
            "(#borrow-mut (#deref fallback))",
            "(#borrow-mut (#index fallback index))",
        )
        .replace(
            "(#await () ChildTask",
            "(#set index 0usize) (#await () ChildTask",
        )
        .replace(
            "(#u64.+.wrap (#index values 0usize) fallback)",
            "(#u64.+.wrap (#index values 0usize) (#index fallback 1usize))",
        );
    build_and_run_graph(&array, 42);
    build_and_run_graph(&array.replace(": choose true", ": choose false"), 42);
    for write in ["(#set fallback 0u64)", "(#set-index values 0usize 0u64)"] {
        let conflicting = source.replace(
            "(#let answer #u64 (#match",
            &format!("{write} (#let answer #u64 (#match"),
        );
        let error = graph_compile_error(&conflicting, "mixed-target-pending-owner-write");
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        let span = error.span.unwrap();
        let expected = if write.starts_with("(#set-index") {
            "#set-index"
        } else {
            "#set"
        };
        assert_eq!(&conflicting[span.start..span.end], expected);
    }
    let escaping = format!(
        "{source}\n(#fn escape (: items (#slice-mut #u64)) Work-task
      (#let-mut local #u64 41u64)
      (#return (#call work (: items items : fallback (#borrow-mut local) : choose false))))"
    );
    let error = graph_compile_error(&escaping, "mixed-target-local-reference-escape");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some());
    let overlapping = source.replace(
        ": fallback (#borrow-mut fallback)",
        ": fallback (#borrow-mut (#index values 0usize))",
    );
    let error = graph_compile_error(&overlapping, "mixed-target-overlapping-inputs");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.message.contains("overlap"), "{error:?}");
    assert!(error.span.is_some());
}

#[test]
fn graph_pinned_reference_selects_local_or_external_storage() {
    let runtime = external_mutable_slice_source()
        .split_once("(@#async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
      (#fn cancel-child (: task ChildTask) () (#forget task) (#return ()))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (cancel-frame ((await-0 cancel-child)))
        : function (#fn work (: other (#pin-ref-mut #u64) : choose #bool) #u64
          (#let-mut local #u64 42u64)
          (#let view (#pin-ref-mut #u64)
            (#if choose (#pin local) (#borrow-mut (#deref other))))
          (#assert (#u64.== (#deref view) 42u64))
          (#await () ChildTask ChildPending ChildReady child-poll Start)
          (#let answer #u64 (#deref view))
          (#forget view) (#forget other) (#forget local) (#return answer))))
      (#fn main () #u64
        (#let-mut other #u64 42u64) (#let waker #u64 0u64)
        (#let-mut frame Work-frame (#call work (: other (#pin other) : choose true)))
        (#let first Work-poll-result
          (#call work-poll (: task (#pin frame) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready result) result)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget frame) (#forget other) (#return answer))"#
    );
    build_and_run_graph(&source, 42);
    build_and_run_graph(&source.replace(": choose true", ": choose false"), 42);
    let shared = source
        .replace("#pin-ref-mut", "#pin-ref")
        .replace("(#pin local)", "(#pin-shared local)")
        .replace("(#pin other)", "(#pin-shared other)")
        .replace("(#borrow-mut (#deref other))", "(#borrow (#deref other))");
    build_and_run_graph(&shared, 42);
    build_and_run_graph(&shared.replace(": choose true", ": choose false"), 42);
    let projected = source
        .replace(
            "other (#pin-ref-mut #u64)",
            "other (#pin-ref-mut (#array #u64 3))",
        )
        .replace(
            "(#let-mut local #u64 42u64)",
            "(#let-mut local (#array #u64 2) (#array-of (#array #u64 2) 17u64 42u64))
             (#let-mut index #usize 1usize)",
        )
        .replace("(#pin local)", "(#pin-borrow-mut (#index local index))")
        .replace(
            "(#borrow-mut (#deref other))",
            "(#borrow-mut (#index other index))",
        )
        .replace(
            "(#await () ChildTask",
            "(#set index 0usize) (#await () ChildTask",
        )
        .replace(
            "(#let-mut other #u64 42u64)",
            "(#let-mut other (#array #u64 3) (#array-of (#array #u64 3) 17u64 42u64 91u64))",
        );
    assert_ne!(projected, source);
    build_and_run_graph(&projected, 42);
    build_and_run_graph(&projected.replace(": choose true", ": choose false"), 42);
    let second = "(#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready result) result)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))";
    let canceled = source.replace(
        second,
        "(#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task next)))
         (#call cancel-frame (: task cleanup)) (#let answer #u64 42u64)",
    );
    assert_ne!(canceled, source);
    build_and_run_graph(&canceled, 42);
    build_and_run_graph(&canceled.replace(": choose true", ": choose false"), 42);
    let conflicting = source.replace(
        second,
        &format!("(#unsafe (#pin-write (#pin-borrow-mut other) 0u64)) {second}"),
    );
    let error = graph_compile_error(&conflicting, "mixed-pinned-target-live-write");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some());
    let movable = source.replace("@#async-fn-pinned", "@#async-fn");
    let error = graph_compile_error(&movable, "movable-pinned-local-target");
    assert!(error.message.contains("pinned async frame"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&movable[span.start..span.end], "(#pin local)");
}

#[test]
fn graph_whole_pinned_reborrows_preserve_kind_before_and_after_pending() {
    let runtime = external_mutable_slice_source()
        .split_once("(@#async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work (: parent (#pin-ref-mut #u64)) #u64
          (#let first (#pin-ref-mut #u64) (#borrow-mut (#deref parent)))
          (#assert (#u64.== (#deref first) 42u64)) (#forget first)
          (#await () ChildTask ChildPending ChildReady child-poll Start)
          (#let second (#pin-ref-mut #u64) (#borrow-mut (#deref parent)))
          (#let answer #u64 (#deref second))
          (#forget second) (#forget parent) (#return answer))))
      (#fn main () #u64
        (#let-mut value #u64 42u64) (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (: parent (#pin value))) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready result) result)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget value) (#return answer))"#
    );
    build_and_run_graph(&source, 42);
    let downgraded = source.replace(
        "(#let first (#pin-ref-mut #u64)",
        "(#let first (#ref-mut #u64)",
    );
    let error = graph_compile_error(&downgraded, "whole-reborrow-pin-kind-downgrade");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(error.span.is_some());
}

#[test]
fn graph_pinned_parent_retains_a_local_mutable_slice_across_pending() {
    let runtime = external_mutable_slice_source()
        .split_once("(@#async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
      (#fn cancel-container (: view (#slice-mut #u64)) () (#forget view) (#return ()))
      (#fn cancel-child (: task ChildTask) () (#forget task) (#return ()))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (cancel-frame ((container cancel-container) (await-0 cancel-child)))
        : function (#fn work () #u64
          (#let-mut counter (#array #u64 1) (#array-of (#array #u64 1) 41u64))
          (#let container (#slice-mut #u64) (#slice-mut-of (#borrow-mut counter)))
          (#let view (#ref-mut #u64) (#slice-mut-idx container 0usize))
          (#deref-set view (#u64.+.wrap (#deref view) 1u64)) (#forget view)
          (#await () ChildTask ChildPending ChildReady child-poll Start)
          (#let answer #u64 (#deref (#slice-mut-idx container 0usize)))
          (#forget container) (#forget counter) (#return answer))))
      (#fn main () #u64
        (#let-mut frame Work-frame (#call work ())) (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#pin frame) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget frame) (#return answer))"#
    );
    build_and_run_graph(&source, 42);
}

#[test]
fn graph_parent_cancels_a_slice_borrowing_child_before_its_lender() {
    let source = r#"
      (#enum ChildTask ((Start (#slice-mut #u64)) (Resume (#slice-mut #u64))))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady ())))
      (#fn child-poll (: task ChildTask : waker (#ref #u64)) ChildPoll
        (#return (#match task
          (#case (Start initial) (ChildPending (Resume initial)))
          (#case (Resume final)
            (#block
              (#let element (#ref-mut #u64) (#slice-mut-idx final 0usize))
              (#deref-set element (#u64.+.wrap (#deref element) 1u64))
              (#forget element)
              (#forget final) (ChildReady ()))))))
      (#fn cancel-child (: task ChildTask) ()
        (#match task
          (#case (Start initial)
            (#block (#deref-set (#slice-mut-idx initial 0usize) 42u64) (#forget initial)))
          (#case (Resume final)
            (#block (#deref-set (#slice-mut-idx final 0usize) 42u64) (#forget final))))
        (#return ()))
      (#fn cancel-container (: view (#slice-mut #u64)) ()
        (#assert (#u64.== (#deref (#slice-mut-idx view 0usize)) 42u64))
        (#forget view) (#return ()))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (cancel-frame ((container cancel-container) (await-0 cancel-child)))
        : function (#fn work () #u64
          (#let-mut counter (#array #u64 1) (#array-of (#array #u64 1) 41u64))
          (#let container (#slice-mut #u64) (#slice-mut-of (#borrow-mut counter)))
          (#await () ChildTask ChildPending ChildReady child-poll
            (Start (#slice-mut-range container 0usize (#slice-mut-len container))))
          (#let answer #u64 (#deref (#slice-mut-idx container 0usize)))
          (#forget container) (#forget counter) (#return answer))))
      (#fn main () #u64
        (#let-mut frame Work-frame (#call work ())) (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#pin frame) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task next)))
        (#call cancel-frame (: task cleanup))
        (#forget frame) (#return 42u64))"#;
    build_and_run_graph(source, 42);
    // The same child must also release its loan on normal completion before
    // its parent reads and consumes the original lending slice.
    let resumed = source.replace(
        "(#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task next)))\n        (#call cancel-frame (: task cleanup))\n        (#forget frame) (#return 42u64))",
        "(#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget frame) (#return answer))",
    );
    assert_ne!(resumed, source);
    build_and_run_graph(&resumed, 42);
    let overlapping = source.replace(
        "(#await () ChildTask ChildPending ChildReady child-poll\n            (Start (#slice-mut-range container 0usize (#slice-mut-len container))))",
        "(#let child ChildTask (Start (#slice-mut-range container 0usize (#slice-mut-len container))))
          (#deref-set (#slice-mut-idx container 0usize) 0u64)
          (#await () ChildTask ChildPending ChildReady child-poll child)",
    );
    assert_ne!(overlapping, source);
    let error = graph_compile_error(&overlapping, "parent-access-with-live-slice-child");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some(), "{error:?}");
}

#[test]
fn graph_child_cancellation_retains_a_shared_slice_descriptor() {
    let source = r#"
      (#enum ChildTask ((Start (#ref (#slice #u64))) (Resume (#ref (#slice #u64)))))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady ())))
      (#fn child-poll (: task ChildTask : waker (#ref #u64)) ChildPoll
        (#return (#match task
          (#case (Start initial) (ChildPending (Resume initial)))
          (#case (Resume final) (#block (#forget final) (ChildReady ()))))))
      (#fn cancel-child (: task ChildTask) ()
        (#match task
          (#case (Start initial)
            (#assert (#u64.== (#deref (#slice-idx (#deref initial) 0usize)) 42u64)))
          (#case (Resume final)
            (#assert (#u64.== (#deref (#slice-idx (#deref final) 0usize)) 42u64))))
        (#return ()))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (cancel-frame ((await-0 cancel-child)))
        : function (#fn work () #u64
          (#let backing (#array #u64 1) (#array-of (#array #u64 1) 42u64))
          (#let container (#slice #u64) (#slice-of (#borrow backing)))
          (#await () ChildTask ChildPending ChildReady child-poll (Start (#borrow container)))
          (#let answer #u64 (#deref (#slice-idx container 0usize)))
          (#forget container) (#forget backing) (#return answer))))
      (#fn main () #u64
        (#let-mut frame Work-frame (#call work ())) (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#pin frame) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let cleanup Work-frame-cleanup (#call work-poll-cleanup (: task next)))
        (#call cancel-frame (: task cleanup))
        (#forget frame) (#return 42u64))"#;
    let generated = build_and_run_graph(source, 42);
    let cleanup = lim::parse(&generated)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == "work-poll-cleanup"))
        })
        .unwrap();
    let cleanup = &generated[cleanup.span.start..cleanup.span.end];
    assert!(
        cleanup.find("(#call cancel-child").unwrap()
            < cleanup
                .find("(#pin-borrow-mut (#get task binding.2))")
                .unwrap(),
        "the child's descriptor must not be cleared before its destructor"
    );
    // Exercise the opposite retained constructor too. Both destructor arms
    // read the descriptor; neither is rewritten into a dummy cleanup arm.
    let retained_start = source
        .replace(
            "(ChildPending (Resume initial))",
            "(ChildPending (Start initial))",
        )
        .replace(
            "(#block (#forget final) (ChildReady ()))",
            "(ChildPending (Start final))",
        )
        .replace(
            "(Start (#borrow container))",
            "(Resume (#borrow container))",
        );
    assert_ne!(retained_start, source);
    build_and_run_graph(&retained_start, 42);
}

#[test]
fn dereference_reborrows_keep_exclusivity_and_pin_kind() {
    let source = r#"(#fn main () #u64
      (#let-mut value #u64 41u64)
      (#let parent (#ref-mut #u64) (#borrow-mut value))
      (#let shared (#ref #u64) (#borrow (#deref parent)))
      (#assert (#u64.== (#deref shared) 41u64)) (#forget shared)
      (#let child (#ref-mut #u64) (#borrow-mut (#deref parent)))
      (#deref-set child 42u64) (#forget child) (#forget parent) (#return value))"#;
    build_and_run_graph(source, 42);
    let error = graph_compile_error(
        "(#fn bad (: view (#ref #u64)) (#ref-mut #u64) (#return (#borrow-mut (#deref view))))",
        "shared-dereference-reborrow",
    );
    assert!(error.message.contains("immutable"), "{error:?}");
    let error = graph_compile_error("(#fn bad (: view (#pin-ref-mut #u64)) (#ref-mut #u64) (#return (#borrow-mut (#deref view))))", "pinned-dereference-reborrow");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
}

#[test]
fn async_for_void_await_step_respects_continue_break_and_false_condition() {
    let source = r#"
      (#enum ConditionTask ((Check #bool)))
      (#enum ConditionPoll ((ConditionPending ConditionTask) (ConditionReady #bool)))
      (#fn condition-poll ((task ConditionTask) (waker (#ref #u64))) ConditionPoll
        (#return (#match task (#case (Check run) (ConditionReady run)))))
      (#enum StepTask (Start Resume))
      (#linear StepTask)
      (#enum StepPoll ((StepPending StepTask) (StepReady ())))
      (#fn step-poll ((task StepTask) (waker (#ref #u64))) StepPoll
        (#return (#match task
          (#case Start (StepPending Resume))
          (#case Resume (StepReady ())))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((run #bool) (stop #bool)) #u64
          (#let-mut keep #bool run)
          (#for ()
            (#await #bool ConditionTask ConditionPending ConditionReady condition-poll (Check keep))
            (#await () StepTask StepPending StepReady step-poll Start)
            (#set keep false)
            (#if stop (#break) (#continue)))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (: run true : stop false)) : waker (#borrow waker))))
        (#let-else (work-pending task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
        (#match second
          (#case (work-ready value) (#assert (#u64.== value 42u64)))
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))
        (#let broken Work-poll-result (#call work-poll (: task (#call work (: run true : stop true)) : waker (#borrow waker))))
        (#match broken
          (#case (work-ready value) (#assert (#u64.== value 42u64)))
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))
        (#let skipped Work-poll-result (#call work-poll (: task (#call work (: run false : stop false)) : waker (#borrow waker))))
        (#return (#match skipped
          (#case (work-ready value) value)
          (#case (work-pending unexpected) (#block (#forget unexpected) (#unreachable))))))
    "#;
    build_and_run(source, 42);
    let synchronous_condition = source.replace(
        "(#await #bool ConditionTask ConditionPending ConditionReady condition-poll (Check keep))",
        "keep",
    );
    assert_ne!(synchronous_condition, source);
    build_and_run(&synchronous_condition, 42);
    build_and_run(include_str!("../examples/async_for_unit_step.lim"), 42);
}

#[test]
fn awaited_for_condition_runs_step_after_continue_but_not_break() {
    let source = "(#enum ChildTask ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #bool)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value)
            (#if (#u64.== value 0u64)
              (ChildPending (Waiting 1u64))
              (ChildReady (#u64.< value 3u64)))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#for (#set iteration 0u64)
                (#await ChildTask ChildPending ChildReady child-poll (Waiting iteration))
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#match iteration
              (#case 0u64 (#continue))
              (#case 1u64 ())
              (#case _ (#break))))
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let value #u64 (#match second
          (#case (work-ready result) result)
          (#case (work-pending pending-again) (#block (#forget pending-again) 0u64))))
        (#forget waker)
        (#return (#if (#u64.== value 2u64) 42u64 0u64)))";
    build_and_run(source, 42);
}

#[test]
fn explicit_await_contracts_are_checked_before_loop_lowering() {
    let source = include_str!("../examples/async_for_patterns.lim");
    let invalid = source.replace(
        "(#set iteration (#u64.+.wrap iteration 1u64))",
        "(#set iteration (#await #u32 Step StepPending StepReady step-poll (Start (#u64.+.wrap iteration 1u64))))",
    );
    let scratch = support::Scratch::new("async-explicit-result-contracts");
    let result = lim::compile_source_to_assembly(
        &invalid,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    );
    assert!(
        result.is_err(),
        "lowering must not erase a contradictory explicit await result type"
    );
    let error = result.unwrap_err();
    assert!(
        error.message.contains("result type") && error.message.contains("iteration"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("an explicit await contract error has its own source span");
    assert_eq!(
        span.start,
        invalid.find("#await #u32").unwrap(),
        "{error:?}"
    );
    assert_eq!(&invalid[span.start..span.end], "#await", "{error:?}");
    let with_condition = format!("(#struct TestTask ((decision #bool)))
      (#enum TestPoll ((TestPending TestTask) (TestReady #bool)))
      (#fn test-poll ((task TestTask) (waker (#ref #u64))) TestPoll
        (#return (TestReady (#get task decision))))\n{}", source.replace(
        "(#u64.< iteration limit)",
        "(#await #bool TestTask TestPending TestReady test-poll (#struct-literal TestTask (: decision (#u64.< iteration limit))))"));
    let body_error =
        with_condition.replace("(#await Step StepPending", "(#await #u32 Step StepPending");
    let error = lim::compile_source_to_assembly(
        &body_error,
        &scratch.path().join("body.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("body-cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("result type") && error.message.contains("value"),
        "{error:?}"
    );
    let span = error.span.unwrap();
    assert_eq!(
        span.start,
        body_error.find("#await #u32").unwrap(),
        "{error:?}"
    );
    assert_eq!(&body_error[span.start..span.end], "#await");
    let aliased = format!("(#type Index #u64)\n{}", source
        .replace("(z (#tuple #u64 #u64))", "(z (#tuple Index #u64))")
        .replace("(#set iteration (#u64.+.wrap iteration 1u64))", "(#set iteration (#await #u64 Step StepPending StepReady step-poll (Start (#u64.+.wrap iteration 1u64))))")
        .replace("0u64 4u64", "0u64 8u64"));
    build_and_run(&aliased, 42);
}

#[test]
fn async_for_initializers_register_every_declared_pattern_leaf() {
    let source = include_str!("../examples/async_for_patterns.lim");
    build_and_run(source, 42);
    build_and_run(
        &source.replace("(StepPending (Resume value))", "(StepReady value)"),
        42,
    );
    build_and_run(
        &source
            .replace("0u64 2u64", "0u64 0u64")
            .replace("(StepPending (Resume value))", "(#panic)"),
        1,
    );
    let aliased = format!(
        "(#type BoundsAlias Bounds)\n{}",
        source
            .replace("(bounds Bounds)", "(bounds BoundsAlias)")
            .replace("bias) Bounds bounds", "bias) BoundsAlias bounds")
    );
    build_and_run(&aliased, 42);
    let narrow = source
        .replace(
            "(z (#tuple #u64 #u64)) (a #u64)",
            "(z (#tuple #u8 #u16)) (a #u32)",
        )
        .replace(
            "(#u64.< iteration limit)",
            "(#u8.< iteration (#as limit #u8))",
        )
        .replace("(#u64.+.wrap iteration 1u64)", "(#u8.+.wrap iteration 1u8)")
        .replace("(Start iteration)", "(Start (#as iteration #u64))")
        .replace("value bias)", "value (#as bias #u64))")
        .replace(
            ": a 20u64 : z (#tuple (#tuple #u64 #u64) 0u64 2u64)",
            ": a 20u32 : z (#tuple (#tuple #u8 #u16) 0u8 2u16)",
        );
    build_and_run(&narrow, 42);
    let awaited =
        format!("(#enum InitTask ((InitStart Bounds) (InitResume Bounds)))
      (#enum InitPoll ((InitPending InitTask) (InitReady Bounds)))
      (#fn init-poll ((task InitTask) (waker (#ref #u64))) InitPoll
        (#return (#match task
          (#case (InitStart bounds) (InitPending (InitResume bounds)))
          (#case (InitResume bounds) (InitReady bounds)))))\n{}", source.replace(
            "bias) Bounds bounds)",
            "bias) Bounds (#await InitTask InitPending InitReady init-poll (InitStart bounds)))"));
    build_and_run(&awaited, 42);
    build_and_run(
        &awaited.replace("(#await InitTask", "(#await Bounds InitTask"),
        42,
    );
    let condition = format!("(#struct TestTask ((decision #bool) (resume #bool)))
      (#enum TestPoll ((TestPending TestTask) (TestReady #bool)))
      (#fn test-poll ((task TestTask) (waker (#ref #u64))) TestPoll
        (#return (#if (#get task resume) (TestReady (#get task decision))
          (TestPending (#struct-literal TestTask (: decision (#get task decision) : resume true))))))\n{}", source
        .replace("(#u64.< iteration limit)", "(#await #bool TestTask TestPending TestReady test-poll (#struct-literal TestTask (: decision (#u64.< iteration limit) : resume false)))")
        .replace("0u64 4u64", "0u64 12u64"));
    build_and_run(&condition, 42);
    let step = source.replace(
        "(#set iteration (#u64.+.wrap iteration 1u64))",
        "(#set iteration (#await #u64 Step StepPending StepReady step-poll (Start (#u64.+.wrap iteration 1u64))))",
    ).replace("0u64 4u64", "0u64 12u64");
    build_and_run(&step, 42);
    let all_phases = condition.replace(
        "(#set iteration (#u64.+.wrap iteration 1u64))",
        "(#set iteration (#await #u64 Step StepPending StepReady step-poll (Start (#u64.+.wrap iteration 1u64))))",
    );
    build_and_run(&all_phases, 42);
    let referenced = source
        .replace("(a #u64)", "(a (#ref #u64))")
        .replace("value bias)", "value (#deref bias))")
        .replace(
            "(#let waker #u64",
            "(#let-mut owner #u64 20u64) (#let waker #u64",
        )
        .replace(": a 20u64", ": a (#borrow owner)");
    build_and_run(&referenced, 42);
    build_and_run(
        &referenced
            .replace("(a (#ref #u64))", "(a (#ref-mut #u64))")
            .replace("(#borrow owner)", "(#borrow-mut owner)"),
        42,
    );
    build_and_run(
        &referenced.replace(
            "(#block (#return value))",
            "(#block (#set owner 99u64) (#return value))",
        ),
        42,
    );
    build_and_run(
        &referenced.replace(
            "(#block (#set task next) ())",
            "(#block (#forget next) (#set owner 99u64) (#return owner))",
        ),
        99,
    );
    let scratch = support::Scratch::new("async-for-pattern-errors");
    let error_for = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    let immutable = error_for(&source.replace("(#for (#let-mut", "(#for (#let"));
    assert!(
        immutable.message.contains("mutable") && immutable.span.is_some(),
        "{immutable:?}"
    );
    let duplicate = error_for(&source.replace(
        "(#tuple iteration limit) bias",
        "(#tuple iteration iteration) bias",
    ));
    assert!(
        duplicate.message.contains("duplicate") || duplicate.message.contains("shadow"),
        "{duplicate:?}"
    );
    assert!(duplicate.span.is_some(), "{duplicate:?}");
    let conflict = error_for(&referenced.replace(
        "(#block (#set task next) ())",
        "(#block (#set owner 99u64) (#set task next) ())",
    ));
    assert!(
        conflict.message.contains("owner") && conflict.message.contains("borrow"),
        "{conflict:?}"
    );
    let span = conflict
        .span
        .expect("retained loop loan has an exact source operation");
    assert_eq!(
        &referenced.replace(
            "(#block (#set task next) ())",
            "(#block (#set owner 99u64) (#set task next) ())"
        )[span.start..span.end],
        "#set",
        "{conflict:?}"
    );
    let leaked = error_for(&source.replace(
        "(#return (#u64.+.wrap total",
        "(#let leaked #u64 limit) (#return (#u64.+.wrap total",
    ));
    assert!(
        leaked.message.contains("limit") && leaked.message.contains("unknown"),
        "{leaked:?}"
    );
    assert!(leaked.span.is_some(), "{leaked:?}");
    let mismatch =
        error_for(&condition.replace("(#await Step StepPending", "(#await #u32 Step StepPending"));
    assert!(
        mismatch.message.contains("result type") && mismatch.message.contains("value"),
        "{mismatch:?}"
    );
    assert!(mismatch.span.is_some(), "{mismatch:?}");
}

#[test]
fn async_function_resumes_child_await_inside_for_with_local_initializer() {
    let source = "(#struct Child ((iteration #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-value ((iteration #u64)) #u64 (#return iteration))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#let value #u64 (#get task iteration))
        (#return (#if (#u64.== value 0u64)
          (ChildPending (#struct-literal Child ((iteration 1u64))))
          (ChildReady value))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#for (#let-mut iteration #u64 0u64)
                (#u64.< iteration 2u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#let result #u64
              (#await Child ChildPending ChildReady child-poll
                (#struct-literal Child ((iteration
                  (#call child-value (: iteration iteration))))))))
          (#let iteration #u64 42u64)
          (#return iteration))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_rejects_for_initializer_shadowing() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (ChildReady 1u64)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 5u64)
          (#for (#let-mut iteration #u64 0u64)
                (#u64.< iteration 2u64)
                (#set iteration (#u64.+.wrap iteration 1u64))
            (#let result #u64
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
    let source = "(#enum ChildPoll ((ChildPending #u64) (ChildReady #u64)))
      (#enum Decision (Stop Continue))
      (#fn child-poll ((task #u64) (waker (#ref #u64))) ChildPoll
        (#return (#if (#u64.== task 0u64)
          (ChildPending 1u64)
          (ChildReady task))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#loop
            (#let result #u64
              (#await #u64 ChildPending ChildReady child-poll iteration))
            (#set iteration result)
            (#set iteration (#u64.+.wrap iteration 1u64))
            (#let decision Decision
              (#if (#u64.== iteration 2u64) (Stop) (Continue)))
            (#match decision
              (#case Stop (#break))
              (#case Continue (#continue))))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending pending) Work-poll-result first (#unreachable))
        (#let second Work-poll-result (#call work-poll (: task pending : waker (#borrow waker))))
        (#let result #u64
          (#match second
            (#case (work-ready value) value)
            (#case (work-pending pending-again)
              (#block (#forget pending-again) (#unreachable)))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("-wait"), "{generated}");
}

#[test]
fn async_function_does_not_hoist_awaits_out_of_loop_forms() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting value) (ChildPending (Waiting value))))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#loop
            (#let result #u64
              (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64))))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let outcome Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let result #u64
          (#match outcome
            (#case (work-pending pending) (#block (#forget pending) 42u64))
            (#case (work-ready value) value)))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("work-task-await-0"), "{generated}");
}

#[test]
fn async_loop_body_supports_more_than_two_suspensions() {
    let source = "(#enum ChildTask (Waiting Resuming))
      (#linear ChildTask)
      (#enum ChildPoll ((ChildPending ChildTask) (ChildReady #u64)))
      (#fn child-poll ((task ChildTask) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case Waiting (ChildPending Resuming))
          (#case Resuming (ChildReady 2u64)))))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut total #u64 0u64)
          (#loop
            (#let first #u64
              (#await #u64 ChildTask ChildPending ChildReady child-poll Waiting))
            (#let second #u64
              (#await #u64 ChildTask ChildPending ChildReady child-poll Waiting))
            (#let third #u64
              (#await #u64 ChildTask ChildPending ChildReady child-poll Waiting))
            (#set total
              (#u64.+.wrap total
                (#u64.+.wrap first (#u64.+.wrap second third))))
            (#break))
          (#assert (#u64.== total 6u64))
          (#return 42u64))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let first Work-poll-result
          (#call work-poll (: task (#call work (:)) : waker (#borrow waker))))
        (#let-else (work-pending first-task) Work-poll-result first (#unreachable))
        (#let second Work-poll-result
          (#call work-poll (: task first-task : waker (#borrow waker))))
        (#let-else (work-pending second-task) Work-poll-result second (#unreachable))
        (#let third Work-poll-result
          (#call work-poll (: task second-task : waker (#borrow waker))))
        (#let-else (work-pending third-task) Work-poll-result third (#unreachable))
        (#let fourth Work-poll-result
          (#call work-poll (: task third-task : waker (#borrow waker))))
        (#let result #u64
          (#match fourth
            (#case (work-ready value) value)
            (#case (work-pending unexpected)
              (#block (#forget unexpected) 0u64))))
        (#forget waker)
        (#return result))";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("body-poll.dispatch"), "{generated}");
}

#[test]
fn async_function_preserves_loop_locals_used_after_suspension() {
    let source = "(#enum Child ((Waiting #u64)))
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (ChildReady 1u64)))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work () #u64
          (#let-mut iteration #u64 0u64)
          (#while (#u64.< iteration 1u64)
            (#let-mut child-input #u64 iteration)
            (#let result #u64
              (#await Child ChildPending ChildReady child-poll (Waiting child-input)))
            (#set child-input result)
            (#set iteration (#u64.+.wrap iteration 1u64)))
          (#return 42u64))))";
    let driver = "(#fn main () #u64
        (#let waker #u64 0u64) (#let-mut task Work-task (#call work (:)))
        (#for-range (attempt #u64) 0u64 4u64
          (#let outcome Work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#match outcome
            (#case (work-pending next) (#block (#set task next) ()))
            (#case (work-ready value) (#block (#return value)))))
        (#forget task) (#return (#unreachable)))";
    build_and_run(&format!("{source}\n{driver}"), 42);
    let pending = source.replace(
        "(#return (ChildReady 1u64))",
        "(#return (#match task (#case (Waiting count)
          (#if (#u64.== count 0u64) (ChildPending (Waiting 1u64)) (ChildReady 1u64)))))",
    );
    build_and_run(&format!("{pending}\n{driver}"), 42);
}

#[test]
fn async_function_can_suspend_at_each_await() {
    let original = example_without_cancel_work();
    let (prefix, _) = original.split_once("(#fn main () #u64").unwrap();
    let prefix = prefix.replace(
        "(#return (#u64.+.wrap total offset))",
        "(#let second #u64
           (#await Step StepPending StepReady step-poll (Waiting 1u64)))
         (#return (#u64.+.wrap total offset))",
    );
    let source = format!(
        "{prefix} (#fn main () #u64
           (#let executor Executor
             (#struct-literal Executor ((notifications
               (#call CellU64-create (: value 0u64))))))
           (#let waker LocalWaker
             (#call local-waker-create (: executor (#borrow executor) : metadata (#struct-literal WakeMetadata ((amount 1u64))))))
           (#let first Work-poll-result
             (#call work-poll (: task (#call work (: offset 1u64)) : waker (#borrow waker))))
           (#let-else (work-pending first-task) Work-poll-result first (#unreachable))
           (#let second Work-poll-result
             (#call work-poll (: task first-task : waker (#borrow waker))))
           (#let-else (work-pending second-task) Work-poll-result second (#unreachable))
           (#let third Work-poll-result
             (#call work-poll (: task second-task : waker (#borrow waker))))
           (#let value #u64
             (#match third
               (#case (work-ready result) result)
               (#case (work-pending task)
                 (#block (#forget task) (#unreachable)))))
           (#call local-waker-destroy (: waker waker))
           (#let executor-ref (#ref Executor) (#borrow executor))
           (#let notifications #u64 (#call CellU64-get (: cell (#borrow (#get executor-ref notifications)))))
           (#drop executor-ref)
           (#forget executor)
           (#return (#u64.+.wrap value notifications)))"
    );
    build_and_run_graph(&source, 43);
}

#[test]
fn async_function_pending_state_can_be_cancelled_explicitly() {
    let original = example_source();
    let (prefix, _) = original.split_once("(#fn main () #u64").unwrap();
    let source = format!(
        "{prefix} (#fn main () #u64
           (#let executor Executor
             (#struct-literal Executor ((notifications
               (#call CellU64-create (: value 0u64))))))
           (#let waker LocalWaker
             (#call local-waker-create (: executor (#borrow executor) : metadata (#struct-literal WakeMetadata ((amount 1u64))))))
           (#let first Work-poll-result
             (#call work-poll (: task (#call work (: offset 1u64)) : waker (#borrow waker))))
           (#let-else (work-pending pending) Work-poll-result first (#unreachable))
           (#call cancel-work (: task (#call work-poll-cleanup (: task pending))))
           (#call local-waker-destroy (: waker waker))
           (#let executor-ref (#ref Executor) (#borrow executor))
           (#let notifications #u64 (#call CellU64-get (: cell (#borrow (#get executor-ref notifications)))))
           (#drop executor-ref)
           (#forget executor)
           (#return notifications))"
    );
    build_and_run_graph(&source, 1);
}

#[test]
fn generated_async_frames_support_source_named_task_cancellation() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting remaining)
            (#if (#u64.== remaining 0u64)
              (ChildReady 42u64)
              (ChildPending (Waiting (#u64.-.wrap remaining 1u64))))))))
      (#fn child-cancel ((task Child)) () (#forget task) (#return ()))
      (@#async-fn (: protocol work-await : waker #u64 : function
        (#fn work ((offset #u64)) #u64
          (#let value #u64
            (#await Child ChildPending ChildReady child-poll (Waiting 2u64)))
          (#return (#u64.+.wrap value offset)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let frame Work-task (#call work (: offset 40u64)))
        (#let first Work-poll-result (#call work-poll (: task frame : waker (#borrow waker))))
        (#let-else (work-pending pending-frame) Work-poll-result first (#unreachable))
        (#call cancel-frame (: task (#call work-poll-cleanup (: task pending-frame))))
        (#forget waker)
        (#return 42u64))";
    let source = source.replace(
        ": waker #u64 : function",
        ": waker #u64 : cancel (cancel-frame ((await-0 child-cancel))) : function",
    );
    build_and_run_graph(&source, 42);
}

#[test]
fn async_fn_generates_source_specific_cancel_dispatch() {
    let source = include_str!("../examples/async_fn_cancel_dispatch.lim");
    let generated = build_and_run_graph(source, 42);
    assert!(generated.contains("(#fn cancel-work ((task Work-task-cleanup)) ()"));
    assert!(generated.contains("Work-task-cleanup-token-full"));
    assert!(generated.contains("Work-task-cleanup-await-0-full"));
    assert!(generated.contains("child-cancel"));
}

#[test]
fn async_fn_cancel_mapping_must_cover_each_source_slot() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (ChildReady 1u64)))
      (@#async-fn (: protocol work-await
                  : waker #u64
                  : cancel (cancel-frame ())
                  : function
        (#fn work ((input #u64)) #u64
          (#let result #u64
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting input)))
          (#return result))))";
    let scratch = support::Scratch::new("async-cancel-missing-state");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .err()
    .expect("a linear child requires a cancellation handler");
    assert!(
        error
            .message
            .contains("missing graph cleanup handler for source slot 'await-0'"),
        "{error:?}"
    );
}

#[test]
fn pinned_async_fn_dispatches_cleanup_after_source_slot_extraction() {
    let source = "(#enum Child ((Waiting #u64)))
      (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (ChildPending task)))
      (#fn child-cancel ((task Child)) () (#forget task) (#return ()))
      (#enum Token ((TokenValue #u64)))
      (#linear Token)
      (#fn destroy-token ((task Token)) () (#forget task) (#return ()))
      (@#async-fn-pinned (: protocol work-await
                  : waker #u64
                  : cancel (cancel-frame
                    ((token destroy-token) (await-0 child-cancel)))
                  : function
        (#fn work ((token Token)) #u64
          (#let child-result #u64
            (#await #u64 Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#call destroy-token (: task token))
          (#return 42u64))))
      (#fn main () #u64
        (#let-mut frame Work-frame (#call work (: token (TokenValue 1u64))))
        (#let waker #u64 0u64)
        (#let outcome Work-poll-result
          (#call work-poll (: task (#pin-borrow-mut frame) : waker (#borrow waker))))
        (#let-else (work-pending cancel-pin) Work-poll-result outcome (#unreachable))
        (#let state Work-frame-cleanup (#call work-poll-cleanup (: task cancel-pin)))
        (#call cancel-frame (: task state))
        (#forget frame)
        (#forget waker)
        (#return 42u64))";
    build_and_run_graph(source, 42);
}
