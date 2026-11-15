mod support;

use std::{fs, process::Command, time::Duration};

fn ordinary_generated(source: &str) -> String {
    let mut result = source.to_owned();
    for node in lim::parse_source_unit(source).unwrap().into_iter().rev() {
        if matches!(node.children.first().map(|node| &node.expr), Some(lim::Expr::Symbol(head)) if head == "#generated-context")
        {
            result.replace_range(node.span.start..node.span.end, "");
        }
    }
    result
}

fn generated_contains_form(generated: &str, expected: &str) -> bool {
    fn same(actual: &lim::Expr, expected: &lim::Expr) -> bool {
        match (actual, expected) {
            (lim::Expr::Symbol(actual), lim::Expr::Symbol(expected)) => {
                actual
                    .split_once(".lim::")
                    .map_or(actual.as_str(), |(_, local)| local)
                    == expected.as_str()
            }
            (lim::Expr::List(actual), lim::Expr::List(expected)) => {
                actual.len() == expected.len()
                    && actual
                        .iter()
                        .zip(expected)
                        .all(|(actual, expected)| same(actual, expected))
            }
            _ => actual == expected,
        }
    }
    fn contains(actual: &lim::Expr, expected: &lim::Expr) -> bool {
        let lim::Expr::List(actual) = actual else {
            return false;
        };
        let lim::Expr::List(expected_items) = expected else {
            panic!("expected a form");
        };
        (actual.len() >= expected_items.len()
            && actual
                .iter()
                .zip(expected_items)
                .all(|(actual, expected)| same(actual, expected)))
            || actual.iter().any(|child| contains(child, expected))
    }
    let expected = lim::parse(expected).unwrap();
    assert_eq!(expected.len(), 1);
    lim::parse_source_unit(generated)
        .unwrap()
        .iter()
        .any(|node| contains(&node.expr, &expected[0].expr))
}

fn assert_single_poll(generated: &str, poll: &str) {
    let nodes = lim::parse_source_unit(generated).unwrap();
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
                Some(lim::Expr::Symbol(name)) => {
                    Some(name.rsplit(".lim::").next().unwrap().to_owned())
                }
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
                    && matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name.rsplit(".lim::").next() == Some(poll)) =>
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
    let source = "#enum Tick () ((Tick.TickStart #u64) (Tick.TickResume #u64))
#enum TickPoll () ((TickPoll.TickPending Tick) (TickPoll.TickReady #u64))
#syntax TickAwait (#u64 Tick TickPoll.TickPending TickPoll.TickReady tick-poll)
#fn tick-poll {
  #params = ((task Tick) (waker (#ref #u64)));
  #returns = TickPoll;
  #body = (
          (#return (#match task
            (#case (Tick.TickStart amount) (TickPoll.TickPending (Tick.TickResume amount)))
            (#case (Tick.TickResume amount) (TickPoll.TickReady amount))))
  );
}
#generate #async-fn ((protocol ParentAwait) (waker #u64) (function
          (#fn parent ((amount #u64)) #u64
            (#let answer #u64 (#await ChildAwait (#call child (($ amount)))))
            (#return (#u64::add-wrap answer 2u64)))))
#generate #async-fn ((protocol ChildAwait) (waker #u64) (function
          (#fn child ((amount #u64)) #u64
            (#return (#await TickAwait (Tick.TickStart amount))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Parent::Poll
            (#call Parent::poll ((task (#call parent ((amount 40u64)))) (waker (#borrow waker)))))
          (#let-else (Parent::Poll.Pending pending-task) Parent::Poll first (#unreachable))
          (#let second Parent::Poll
            (#call Parent::poll ((task pending-task) (waker (#borrow waker)))))
          (#return (#match second
            (#case (Parent::Poll.Ready value) value)
            (#case (Parent::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}\n";
    let generated = build_and_run(source, 42);
    assert_generated_type_names_are_capitalized(&generated);
    let nodes = lim::parse_source_unit(&generated).unwrap();
    for declaration in [
        "(#syntax ParentAwait (#u64 Parent::Task Parent::Poll.Pending Parent::Poll.Ready Parent::poll))",
        "(#syntax ChildAwait (#u64 Child::Task Child::Poll.Pending Child::Poll.Ready Child::poll))",
    ] {
        let expected = lim::parse(declaration).unwrap().remove(0).expr;
        assert_eq!(
            nodes.iter().filter(|node| node.expr == expected).count(),
            1,
            "{declaration}"
        );
    }
    assert_single_poll(&generated, "Parent::poll");
    assert_single_poll(&generated, "Child::poll");
}

fn assert_frame_has_program_counter(generated: &str, name: &str) {
    let nodes = lim::parse_source_unit(generated).unwrap();
    let fields = nodes.iter().find_map(|node| match &node.expr {
        lim::Expr::List(items)
            if matches!(items.as_slice(), [lim::Expr::Symbol(head), lim::Expr::Symbol(frame), ..]
                if head == "#struct" && frame.rsplit(".lim::").next() == Some(name)) => match items.get(3) {
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
        lim::parse_source_unit(generated)
            .unwrap()
            .iter()
            .any(|node| matches!(&node.expr,
        lim::Expr::List(items) if items.get(..4) == Some(expected.as_slice()))),
        "missing generated signature: {signature}"
    );
}

fn assert_generated_type_names_are_capitalized(generated: &str) {
    for node in lim::parse_source_unit(generated).unwrap() {
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
            name.rsplit(".lim::")
                .next()
                .unwrap()
                .chars()
                .next()
                .is_some_and(char::is_uppercase),
            "{name}"
        );
    }
}

#[test]
fn pinned_async_protocols_lend_the_frame_instead_of_moving_it() {
    let source = "#enum Tick () ((Tick.Waiting #u64))
#enum TickPoll () ((TickPoll.TickPending Tick) (TickPoll.TickReady #u64))
#syntax TickAwait (#u64 Tick TickPoll.TickPending TickPoll.TickReady tick-poll)
#fn tick-poll {
  #params = ((task Tick) (waker (#ref #u64)));
  #returns = TickPoll;
  #body = (
          (#return (#match task (#case (Tick.Waiting count)
            (#if (#u64::eq count 0u64) (TickPoll.TickPending (Tick.Waiting 1u64)) (TickPoll.TickReady count)))))
  );
}
#generate #async-fn-pinned ((protocol ChildAwait) (waker #u64) (function
          (#fn child ((amount #u64)) #u64
            (#let ignored #u64 (#await TickAwait (Tick.Waiting 0u64)))
            (#forget ignored) (#return amount))))
#generate #async-fn ((protocol ParentAwait) (waker #u64) (function
          (#fn parent ((task (#pin-ref-mut Child::Frame))) #u64
            (#return (#await ChildAwait task)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut frame Child::Frame (#call child ((amount 42u64))))
          (#let waker #u64 0u64)
          (#let first Parent::Poll
            (#call Parent::poll ((task (#call parent ((task (#pin-borrow-mut frame))))) (waker (#borrow waker)))))
          (#let-else (Parent::Poll.Pending pending-task) Parent::Poll first (#unreachable))
          (#let result Parent::Poll
            (#call Parent::poll ((task pending-task) (waker (#borrow waker)))))
          (#let answer #u64 (#match result
            (#case (Parent::Poll.Ready value) value)
            (#case (Parent::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame) (#return answer)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert!(generated_contains_form(&generated, "(#syntax ChildAwait (#u64 (#pin-ref-mut Child::Frame) Child::Poll.Pending Child::Poll.Ready Child::poll))"), "{generated}");
    assert_single_poll(&generated, "Parent::poll");
    let repeated = source
        .replace("(#u64::eq count 0u64)", "(#u64::lt count 2u64)")
        .replace(
            "(TickPoll.TickPending (Tick.Waiting 1u64))",
            "(TickPoll.TickPending (Tick.Waiting (#u64::add-wrap count 1u64)))",
        )
        .replace(
            "(#let answer #u64 (#match result",
            "(#let-else (Parent::Poll.Pending again) Parent::Poll result (#unreachable))
          (#let third Parent::Poll
            (#call Parent::poll ((task again) (waker (#borrow waker)))))
          (#let answer #u64 (#match third",
        );
    build_and_run_graph(&repeated, 42);

    let cancellation = source
        .replace("(#let result Parent::Poll\n            (#call Parent::poll ((task pending-task) (waker (#borrow waker)))))",
          "(#let cleanup Parent::Task::Cleanup (#call Parent::Poll::cleanup ((task pending-task))))
          (#forget cleanup)
          (#let result Child::Poll
            (#call Child::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))")
        .replace("(#case (Parent::Poll.Ready value)", "(#case (Child::Poll.Ready value)")
        .replace("(#case (Parent::Poll.Pending unexpected)", "(#case (Child::Poll.Pending unexpected)");
    assert_ne!(cancellation, source);
    build_and_run_graph(&cancellation, 42);

    let premature = source
        .replace(
            "        (#forget frame) (#return answer)",
            "        (#return answer)",
        )
        .replace(
            "        (#let result Parent::Poll",
            "        (#forget frame)\n        (#let result Parent::Poll",
        );
    let error = graph_compile_error(&premature, "async-child-frame-retained-pin");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.message.contains("frame"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&premature[span.start..span.end], "#forget");
}

#[test]
fn async_protocols_cross_relative_and_project_root_references() {
    for path in ["./child.lim", "project::child.lim"] {
        let scratch = support::Scratch::new("async-protocol-import");
        fs::write(
            scratch.path().join("child.lim"),
            "#type Amount #u64
#generate #async-fn ((protocol ChildAwait) (waker #u64) (function
                (#fn child ((amount Amount)) Amount (#return amount))))\n",
        )
        .unwrap();
        let source = format!(
            "#alias child = {path}::child
#alias ChildAwait = {path}::ChildAwait
#generate #async-fn ((protocol ParentAwait) (waker #u64) (function
              (#fn parent () #u64
                (#return (#await ChildAwait (#call child ((amount 42u64))))))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let waker #u64 0u64)
              (#return (#match (#call Parent::poll ((task (#call parent ())) (waker (#borrow waker))))
                (#case (Parent::Poll.Ready value) value)
                (#case (Parent::Poll.Pending task) (#block (#forget task) (#unreachable)))))\n  );\n}}\n"
        );
        let program =
            lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
        lim::check_types(&program).unwrap();
        lim::generate_assembly(&program).unwrap();
    }
}

#[test]
fn async_protocols_keep_unknown_name_and_result_mismatch_spans() {
    for (source, message, offending) in [
        (
            "#generate #async-fn ((protocol WorkAwait) (waker #u64) (function
              (#fn work () #u64 (#return (#await Values.Missing task)))))\n",
            "unknown syntax bundle 'Values.Missing'",
            "Values.Missing",
        ),
        (
            "#generate #async-fn ((protocol ChildAwait) (waker #u64) (function
              (#fn child () #u64 (#return 42u64))))
#generate #async-fn ((protocol ParentAwait) (waker #u64) (function
              (#fn parent () #u64
                (#let value #u32 (#await ChildAwait (#call child ())))
                (#return (#as value #u64)))))\n",
            "let 'value' has type U64, expected U32",
            "(#await ChildAwait (#call child ()))",
        ),
    ] {
        let error = graph_compile_error(source, "async-protocol-errors");
        assert!(error.message.contains(message), "{error:?}");
        let span = error.span.expect("protocol errors retain a source span");
        assert_eq!(&source[span.start..span.end], offending, "{error:?}");
    }
}

#[test]
fn async_protocols_reject_invalid_declarations_and_name_collisions() {
    for (source, message) in [
        ("#generate #async-fn ((waker #u64) (function (#fn work () #u64 (#return 42u64))))\n",
            "missing argument 'protocol'"),
        ("#generate #async-fn ((protocol #u64) (waker #u64) (function (#fn work () #u64 (#return 42u64))))\n",
            "protocol names must be user-defined"),
        ("#generate #async-fn ((protocol A) (protocol B) (waker #u64) (function (#fn work () #u64 (#return 42u64))))\n",
            "repeats argument 'protocol'"),
        ("#syntax WorkAwait ()
#generate #async-fn ((protocol WorkAwait) (waker #u64) (function (#fn work () #u64 (#return 42u64))))\n",
            "duplicate syntax bundle"),
        ("#struct WorkAwait () ()
#generate #async-fn ((protocol WorkAwait) (waker #u64) (function (#fn work () #u64 (#return 42u64))))\n",
            "conflicts with a syntax bundle"),
        ("#generate #async-fn ((protocol Work::Task) (waker #u64) (function (#fn work () #u64 (#return 42u64))))\n",
            "conflicts with a syntax bundle"),
    ] {
        let error = graph_compile_error(source, "async-protocol-declaration-conflicts");
        assert!(error.message.contains(message), "{error:?}");
        assert!(error.span.is_some(), "protocol conflicts need a source span: {error:?}");
    }
}

#[test]
fn async_protocols_reject_names_as_an_unknown_argument() {
    for generator in ["#async-fn", "#async-fn-pinned"] {
        let source = format!(
            "#generate {generator} ((protocol WorkAwait)
            (names (Frame Poll Pending Ready poll)) (waker #u64)
            (function (#fn work () #u64 (#return 42u64))))\n"
        );
        let error = lim::parse_program(&source).unwrap_err();
        assert!(
            error.contains(&format!("#generate {generator} has no argument 'names'")),
            "{error}"
        );
    }
}

#[test]
fn async_protocols_are_exported_by_generator_produced_functions() {
    let source = "#gn emit ()
          `((#generate #async-fn ((protocol ChildAwait) (waker #u64) (function
             (#fn child () #u64 (#return 42u64))))))
#generate emit
#generate #async-fn ((protocol ParentAwait) (waker #u64) (function
          (#fn parent () #u64 (#return (#await ChildAwait (#call child ()))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#return (#match (#call Parent::poll ((task (#call parent ())) (waker (#borrow waker))))
            (#case (Parent::Poll.Ready value) value)
            (#case (Parent::Poll.Pending task) (#block (#forget task) (#unreachable)))))\n  );\n}\n";
    let generated = build_and_run(source, 42);
    assert!(
        generated_contains_form(&generated,
            "(#syntax ChildAwait (#u64 Child::Task Child::Poll.Pending Child::Poll.Ready Child::poll))"
        ),
        "{generated}"
    );
}

#[test]
fn async_task_named_capture_survives_pending_without_shadowing_the_poll_parameter() {
    let source = example_without_cancel_work().replace("offset", "task");
    let generated = build_and_run(&source, 42);
    assert_single_poll(&generated, "Work::poll");
    assert!(
        generated_contains_form(&generated, "(#fn work ((task #u64)))"),
        "{generated}"
    );
    assert!(
        generated.contains("((task ") || generated.contains("((task "),
        "{generated}"
    );
}

#[test]
fn async_task_named_capture_without_await_keeps_explicit_public_argument_key() {
    let source = "#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((task #u64)) #u64 (#return task))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result Work::Poll (#call Work::poll ((task (#call work ((task 42u64)))) (waker (#borrow waker)))))
          (#return (#match result
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending waiting) (#block (#forget waiting) (#unreachable)))))\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_task_named_reference_capture_retains_its_referent_across_pending() {
    for ty in ["#ref", "#ref-mut"] {
        let borrow = if ty == "#ref" {
            "#borrow"
        } else {
            "#borrow-mut"
        };
        let source = format!("#enum Step (#linear) ((Step.Waiting #u64))
#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {{
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
              (#return (#match task (#case (Step.Waiting remaining)
                (#if (#u64::eq remaining 0u64) (StepPoll.StepReady 0u64)
                  (StepPoll.StepPending (Step.Waiting 0u64))))))
  );
}}
#generate #async-fn ((protocol work-await) (waker #u64) (function
              (#fn work ((task ({ty} #u64))) #u64
                (#let step-result #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 1u64)))
                (#return (#u64::add-wrap (#deref task) step-result)))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let-mut value #u64 42u64) (#let waker #u64 0u64)
              (#let result Work::Poll (#call Work::poll ((task (#call work ((task ({borrow} value))))) (waker (#borrow waker)))))
              (#let-else (Work::Poll.Pending waiting) Work::Poll result (#unreachable))
              (#let completed Work::Poll (#call Work::poll ((task waiting) (waker (#borrow waker)))))
              (#return (#match completed (#case (Work::Poll.Ready answer) answer)
                (#case (Work::Poll.Pending unfinished) (#block (#forget unfinished) (#unreachable)))))\n  );\n}}\n");
        build_and_run(&source, 42);
        let forbidden = source.replace(
            "(#let completed Work::Poll",
            "(#set value 99u64)\n (#let completed Work::Poll",
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
    assert_single_poll(&generated, "Work::poll");
    assert!(generated.contains("Work::Frame::Cleanup::Await-1"));
    assert!(generated_contains_form(
        &generated,
        "(#fn Work::Poll::cleanup)"
    ));

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
        "(#let value-{index} #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 42u64)))"
    )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let source = format!("#enum Step (#linear) ((Step.Waiting #u64))
#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {{
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task (#case (Step.Waiting value) (StepPoll.StepReady value))))
  );
}}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64 {awaits} (#return value-15))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = ( (#let waker #u64 0u64)
          (#let outcome Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#return (#match outcome
            (#case (Work::Poll.Ready value) value) (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))\n  );\n}}\n");
    let generated = build_and_run(&source, 42);
    assert_single_poll(&generated, "Work::poll");
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
        lim::parse_source_unit(&generated)
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
        "(#return (#u64::add-wrap value offset))",
        "(#let task #u64 offset) (#return (#u64::add-wrap value task))",
    );
    assert_single_poll(&build_and_run_graph(&source, 41), "Work::poll");
}

#[test]
fn generator_produced_async_declaration_keeps_its_checked_source_body() {
    let source = "
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn step-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#gn produce ()
          `((#generate #async-fn ((protocol work-await) (waker #u64)
            (function (#fn work ((seed #u64)) #u64
              (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting seed))))))))
#generate produce
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#return (#match (#call Work::poll ((task (#call work ((seed 42u64)))) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))\n  );\n}\n";
    build_and_run(source, 42);
    let invalid = source.replace("(Child.Waiting seed)", "(Child.Waiting true)");
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
    let immediate = source.replace(
        "(StepPoll.StepPending (Step.Resume value))",
        "(StepPoll.StepReady value)",
    );
    build_and_run(&immediate, 42);

    // The pattern mismatch must not execute either child await.
    let guarded = source.replace(
        "(#case (Step.Start value) (StepPoll.StepPending (Step.Resume value)))",
        "(#case (Step.Start value) (#block (#assert (#u64::eq value 37u64)) (StepPoll.StepPending (Step.Resume value))))",
    );
    build_and_run(&guarded, 42);

    let one_await = source.replace(
        "(#let second #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start first)))\n        (#return second)",
        "(#return first)",
    ).replace(
        "(#let-else (Work::Poll.Pending after-second) Work::Poll third (#unreachable))\n          (#let fourth Work::Poll (#call Work::poll ((task after-second) (waker waker))))\n          (#match fourth",
        "(#match third",
    );
    assert_ne!(one_await, source);
    build_and_run(&one_await, 42);

    let synchronous_body = source.replace(
        "(#let first #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start value)))\n        (#let second #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start first)))\n        (#return second)",
        "(#return value)",
    );
    assert_ne!(synchronous_body, source);
    build_and_run(&synchronous_body, 42);

    let linear =
        format!(
        "#struct Resource (#linear) ((value #u64))\n \n{}",
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
            "#fn run {\n  #params = ((choice Choice) (waker (#ref #u64)));\n  #returns = #u64;",
            "#fn run {\n  #params = ((choice Choice) (counter (#ref #u64)) (waker (#ref #u64)));\n  #returns = (#ref #u64);",
        )
        .replace(
            "(#call work ((choice choice)))",
            "(#call work ((choice choice) (counter counter)))",
        )
        .replace(
            "(#let waker #u64 0u64)",
            "(#let waker #u64 0u64) (#let storage #u64 37u64)",
        )
        .replace("(#let chosen #u64", "(#let chosen (#ref #u64)")
        .replace("(#let empty #u64", "(#let empty (#ref #u64)")
        .replace(
            "(choice (Choice.Chosen 37u64)) (waker",
            "(choice (Choice.Chosen 37u64)) (counter (#borrow storage)) (waker",
        )
        .replace(
            "(choice Choice.Empty) (waker",
            "(choice Choice.Empty) (counter (#borrow storage)) (waker",
        )
        .replace(
            "(#u64::add-wrap chosen empty)",
            "(#u64::add-wrap (#deref chosen) (#deref empty))",
        );
    build_and_run(&source, 74);
    let prefix = source.split_once("#fn main").unwrap().0;
    let escaping = format!("{prefix}
#fn main {{
  #params = ();
  #returns = (#ref #u64);
  #body = (
          (#let waker #u64 0u64)
          (#let storage #u64 37u64)
          (#return (#call run ((choice (Choice.Chosen 37u64)) (counter (#borrow storage)) (waker (#borrow waker)))))\n  );\n}}\n");
    let pending = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut storage #u64 37u64)
          (#let frame Work::Task (#call work ((choice (Choice.Chosen 37u64)) (counter (#borrow storage)))))
          (#let first Work::Poll (#call Work::poll ((task frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#set storage 42u64)
          (#forget task)\n          (#return storage)\n  );\n}}\n"
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
        "(#set storage 42u64)\n          (#forget task)",
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
    let declaration = "(cancel (cancel-work ((await-0 cancel-step))))";
    let invocation = "    (#call cancel-work ((task (#call Work::Poll::cleanup ((task (#call work ((offset 99u64)))))))))\n";
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
    .unwrap_or_else(|| panic!("the checked graph source must be rejected:\n{source}"))
}

fn build_and_run_route(source: &str, expected: i32, graph: bool) -> String {
    build_and_run_route_status(source, Some(expected), graph)
}

fn build_and_run_partial_storage(source: &str, expected: i32) -> String {
    let scratch = support::Scratch::new("async-partial-storage");
    let input = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let output = scratch.path().join("generated");
    let invocation = lim::parse_source_unit(source).unwrap().into_iter().find(|node| {
        matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.first(), Some(lim::Expr::Generate))
                && matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == "#async-fn" || name == "#async-fn-pinned"))
    }).unwrap();
    let mut previous = None;
    let mut previous_artifact = None;
    for cache_pass in 0..2 {
        let assembly = lim::compile_source_with_generated_sources(
            source,
            &input,
            &lim::CompileConfig::default(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
            None,
            &output,
        )
        .unwrap_or_else(|error| panic!("{error:?}"));
        let artifact = fs::read_dir(&output)
            .unwrap()
            .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
            .find(|text| generated_contains_form(text, "(#fn Work::poll)"))
            .unwrap();
        if let Some(previous) = &previous {
            assert_eq!(&assembly, previous);
        }
        if let Some(previous) = &previous_artifact {
            assert_eq!(&artifact, previous);
        }
        let standalone = format!(
            "{}\n{artifact}\n{}",
            &source[..invocation.span.start],
            &source[invocation.span.end..]
        );
        let ordinary = lim::parse_program(&ordinary_generated(&standalone)).unwrap();
        lim::check_types(&ordinary).unwrap_or_else(|error| panic!("{error}\n{standalone}"));
        let independently_emitted = lim::generate_assembly(&ordinary).unwrap();
        for (index, assembly) in [assembly.as_str(), independently_emitted.as_str()]
            .into_iter()
            .enumerate()
        {
            let binary = scratch.path().join(format!("program-{index}"));
            lim::link_native_binary(
                assembly,
                &binary,
                &[],
                &[],
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
            let (status, stdout, stderr) =
                support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
            assert_eq!(
                status.code(),
                Some(expected),
                "cache pass {cache_pass}, native route {index}: {stderr:?}\nsource:\n{source}"
            );
            assert!(stdout.is_empty() && stderr.is_empty());
        }
        previous = Some(assembly);
        previous_artifact = Some(artifact);
    }
    previous_artifact.unwrap()
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
    // Large suspension graphs and aggregate payload variants need more than
    // 20 seconds in the bounded runner; keep compilation capped at one minute.
    let (status, _, stderr) = support::run(&mut command, Duration::from_secs(60), 1024 * 1024)
        .unwrap_or_else(|error| panic!("{error}\ninput source:\n{source}"));
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
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (ChildPoll.ChildReady 0u64))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((value #u64)) #u64
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#if true
              (#block (#let value #u64 2u64) ())
              ())
            (#return result))))\n";
    let scratch = support::Scratch::new("async-shadow");
    let input = scratch.path().join("shadow.lim");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let diagnostic = lim::compile_source_to_assembly(
        source,
        &input,
        &config,
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
    assert_eq!(
        span.start,
        source.find("#let value").unwrap() + "#let ".len()
    );
    let matched = format!(
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)\n{}",
        source.replace(
            "(#block (#let value #u64 2u64) ())",
            "(#match (Maybe.Some 2u64) (#case (Maybe.Some value) ()) (#case Maybe.None ()))",
        )
    );
    let error = graph_compile_error(&matched, "async-match-arm-shadow");
    assert!(error.message.contains("shadow"), "{error:?}");
    let span = error
        .span
        .expect("match shadow has an original binder span");
    assert_eq!(&matched[span.start..span.end], "value");
    assert_eq!(span.start, matched.find("value) ()").unwrap());
}

#[test]
fn async_function_early_returns_from_synchronous_loops_produce_ready() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((finish-early #bool) (range-early #bool) (for-early #bool)) #u64
            (#while finish-early
              (#return 41u64))
            (#for-range (iteration #u32) 0u32
              (#if range-early 1u32 0u32)
              (#return 40u64))
            (#for (#let-mut iteration #u32 0u32)
                  (#u32::lt iteration (#if for-early 1u32 0u32))
                  (#set iteration (#u32::add-wrap iteration 1u32))
              (#return 39u64))
            (#let value #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 42u64)))
            (#return value))))
#fn Work::poll-work {
  #params = ((finish-early #bool) (range-early #bool) (for-early #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task
            (#call work ((finish-early finish-early) (range-early range-early) (for-early for-early))))
          (#let result Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match result
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let early #u64
            (#call Work::poll-work ((finish-early true) (range-early false) (for-early false) (waker (#borrow waker)))))
          (#let range #u64
            (#call Work::poll-work ((finish-early false) (range-early true) (for-early false) (waker (#borrow waker)))))
          (#let for #u64
            (#call Work::poll-work ((finish-early false) (range-early false) (for-early true) (waker (#borrow waker)))))
          (#let resumed #u64
            (#call Work::poll-work ((finish-early false) (range-early false) (for-early false) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap early (#u64::add-wrap range (#u64::add-wrap for resumed))))\n  );\n}\n";
    build_and_run(source, 162);
}

#[test]
fn async_returning_branch_skips_a_suspending_common_tail() {
    let source = include_str!("../examples/async_conditional_return.lim");
    build_and_run(source, 49);
    let matched = source
        .replace("(#if early", "(#match early (#case true")
        .replace(
            "(#return first))\n        ())",
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
            "#fn run {\n  #params = ((early #bool)",
            "#fn run {\n  #params = ((early #bool) (counter (#ref-mut #u64))",
        )
        .replace(
            "(#call work ((early early)))",
            "(#call work ((early early) (counter counter)))",
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
            "(early true) (waker",
            "(early true) (counter (#borrow-mut counter)) (waker",
        )
        .replace(
            "(early false) (waker",
            "(early false) (counter (#borrow-mut counter)) (waker",
        )
        .replace(
            "(#let later #u64",
            "(#assert (#u64::eq counter 7u64)) (#let later #u64",
        )
        .replace(
            "(#return (#u64::add-wrap early later))",
            "(#assert (#u64::eq counter 42u64)) (#return (#u64::add-wrap early later))",
        );
    build_and_run(&borrowed, 49);
    let borrowed_work = borrowed.split_once("#fn run").unwrap().0;
    let pending = format!(
        "{borrowed_work}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut counter #u64 0u64)
          (#let frame Work::Task (#call work ((early true) (counter (#borrow-mut counter)))))
          (#let first Work::Poll (#call Work::poll ((task frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#set counter 42u64)
          (#forget task)
          (#return counter)\n  );\n}}\n"
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
        "(#set counter 42u64)\n          (#forget task)",
        "(#forget task)\n        (#set counter 42u64)",
    );
    build_and_run(&cancelled, 42);

    let linear = format!(
        "#struct Resource (#linear) ((value #u64))\n \n{}",
        source
            .replace(
                "(#fn work ((early #bool))",
                "(#fn work ((early #bool) (resource Resource))"
            )
            .replace(
                "#fn run {\n  #params = ((early #bool)",
                "#fn run {\n  #params = ((early #bool) (resource Resource)"
            )
            .replace(
                "(#call work ((early early)))",
                "(#call work ((early early) (resource resource)))"
            )
            .replace("(#let first #u64", "(#forget resource) (#let first #u64")
            .replace("(#let result #u64", "(#forget resource) (#let result #u64")
            .replace(
                "(early true) (waker",
                "(early true) (resource (#struct-literal Resource ((value 1u64)))) (waker"
            )
            .replace(
                "(early false) (waker",
                "(early false) (resource (#struct-literal Resource ((value 2u64)))) (waker"
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
    let source = "#enum Child (#linear) (Child.Waiting Child.Resume)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Resume))
            (#case Child.Resume (ChildPoll.ChildReady 42u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((early #bool)) #u64
            (#if early (#block (#return 7u64)) ())
            (#let result #u64
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting))
            (#return result))))
#fn run {
  #params = ((early #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((early early))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let early #u64 (#call run ((early true) (waker (#borrow waker)))))
          (#let resumed #u64 (#call run ((early false) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap early resumed))\n  );\n}\n";
    build_and_run(source, 49);
}

#[test]
fn async_function_returns_ready_from_an_ordinary_match_branch() {
    let source = "#enum Child (#linear) (Child.Waiting Child.Resume)
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#enum Action () (Action.ReturnNow Action.Wait)

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Resume))
            (#case Child.Resume (ChildPoll.ChildReady 42u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((action Action)) #u64
            (#match action
              (#case Action.ReturnNow (#block (#return 7u64)))
              (#case Action.Wait ()))
            (#let result #u64
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting))
            (#return result))))
#fn run {
  #params = ((action Action) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((action action))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let early #u64 (#call run ((action Action.ReturnNow) (waker (#borrow waker)))))
          (#let resumed #u64 (#call run ((action Action.Wait) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap early resumed))\n  );\n}\n";
    build_and_run(source, 49);
}

#[test]
fn async_function_early_return_from_synchronous_loop_produces_ready() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#loop (#return 41u64))
            (#let value #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 42u64)))
            (#return value))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let value #u64
            (#match result
              (#case (Work::Poll.Ready ready) ready)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    build_and_run(source, 41);
}

#[test]
fn async_nested_awaits_use_protocol_types_and_highlight_the_later_mismatch() {
    let source = "#enum Step (#linear) ((Step.Waiting #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task (#case (Step.Waiting value) (StepPoll.StepReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let first #u64
              (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 1u64)))
            (#let second #u64
              (#await Step StepPoll.StepPending StepPoll.StepReady step-poll
                (Step.Waiting (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 2u64)))))
            (#return second))))\n";
    let runnable = format!(
        "{source}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#return (#match
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending) (#block (#forget pending) (#unreachable)))))\n  );\n}}\n"
    );
    let generated = build_and_run_graph(&runnable, 2);
    assert_single_poll(&generated, "Work::poll");
    let invalid = source.replace(
        "(Step.Waiting (#await Step",
        "(Step.Waiting (#await #u32 Step",
    );
    assert_ne!(invalid, source);
    let diagnostic = graph_compile_error(&invalid, "async-nested-await-contract-span");
    assert_eq!(diagnostic.code, lim::DiagnosticCode::Type, "{diagnostic:?}");
    assert!(
        diagnostic
            .message
            .contains("#await result type does not match its Ready payload"),
        "{diagnostic:?}"
    );
    let span = diagnostic
        .span
        .expect("nested await error has a source span");
    let await_tokens = invalid.match_indices("#await").collect::<Vec<_>>();
    assert_eq!(await_tokens.len(), 3);
    assert_eq!(span.start, await_tokens[2].0 + "#await ".len());
    assert_eq!(&invalid[span.start..span.end], "#u32");
}

#[test]
fn async_function_suspends_resumes_and_is_inspectable() {
    let generated = build_and_run_graph(&example_source(), 42);
    assert_frame_has_program_counter(&generated, "Work::Task");
    assert_single_poll(&generated, "Work::poll");
    assert!(!generated.contains("#await"));
}

#[test]
fn pinned_async_frames_poll_in_place_and_cancel_explicitly() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady value)))))
  );
}
#fn cancel-child {
  #params = ((task Child));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#generate #async-fn-pinned ((protocol work-await) (waker #u64) (function
          (#fn work ((offset #u64)) #u64
            (#let value #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))
            )
            (#return (#u64::add-wrap value offset)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut frame Work::Frame (#call work ((offset 40u64))))
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pinned-frame) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pinned-frame) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) (#unreachable)))))
          (#forget frame)
          (#let-mut cancelled-frame Work::Frame (#call work ((offset 90u64))))
          (#let first-cancel Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut cancelled-frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending cancel-pin) Work::Poll first-cancel (#unreachable))
          (#let state-to-cancel Work::Frame::Cleanup (#call Work::Poll::cleanup ((task cancel-pin))))
          (#call cancel-frame ((task state-to-cancel)))
          (#forget cancelled-frame)
          (#forget waker)
          (#return result)\n  );\n}\n";
    let source = source.replace(
        "(waker #u64) (function",
        "(waker #u64) (cancel (cancel-frame ((await-0 cancel-child)))) (function",
    );
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let moved = source.replace(
        "(#let second Work::Poll",
        "(#let moved Work::Frame frame)\n        (#let second Work::Poll",
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
        "#fn main {\n  #params = ();\n  #returns = #u64;",
        "#fn escape-frame {
  #params = ();
  #returns = Work::Poll;
  #body = (
          (#let-mut frame Work::Frame (#call work ((offset 40u64))))
          (#let waker #u64 0u64)
          (#return (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;",
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
        generated_contains_form(&generated, "(#pin-ref-mut Work::Frame)"),
        "Work::poll must borrow the pinned frame: {generated}"
    );
    assert_frame_has_program_counter(&generated, "Work::Frame");
    assert_single_poll(&generated, "Work::poll");
    assert!(!generated.contains("(#pin-read task)"), "{generated}");
    assert!(!generated.contains("(#pin-write task"), "{generated}");
    assert_generated_signature(
        &generated,
        "(#fn Work::Poll::cleanup ((task (#pin-ref-mut Work::Frame))) Work::Frame::Cleanup)",
    );
    assert!(
        generated_contains_form(&generated, "(#fn Work::Poll::cleanup)"),
        "{generated}"
    );
}

#[test]
fn pinned_async_frames_keep_local_pins_stationary_across_suspension() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value)
              (#if (#u64::eq value 0u64) (ChildPoll.ChildPending (Child.Waiting 1u64)) (ChildPoll.ChildReady 0u64)))))
  );
}
#generate #async-fn-pinned ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut value #u64 41u64)
            (#let view (#pin-ref #u64) (#pin-borrow value))
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#return (#u64::add-wrap (#deref view) result)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut frame Work::Frame (#call work ()))
          (#let first Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let outcome Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let answer #u64 (#match outcome
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame) (#return answer)\n  );\n}\n";
    build_and_run_graph(source, 41);
}

#[test]
fn pinned_async_frame_self_reference_survives_pending_and_is_cleared_on_cancel() {
    let source = include_str!("../examples/async_fn_self_reference.lim");
    let generated = build_and_run_graph(source, 58);
    assert_single_poll(&generated, "Read-after-await::poll");
    assert_frame_has_program_counter(&generated, "Read-after-await::Frame");

    let pending_mutation = source.replace(
        "  (#let second Read-after-await::Poll",
        "  (#call OwnerAccess::replace ((task (#pin-borrow-mut frame)) (value (#struct-literal Owner ((payload (#struct-literal Payload ((left 99u64) (right 5u64)))))))))\n  (#let second Read-after-await::Poll",
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
        "    (#block\n      (#let cleanup Read-after-await::Frame::Cleanup",
        "  (#call OwnerAccess::replace ((task (#pin-borrow-mut cancelled)) (value (#struct-literal Owner ((payload (#struct-literal Payload ((left 11u64) (right 7u64)))))))))\n  (#block\n    (#let cleanup Read-after-await::Frame::Cleanup",
    );
    assert_ne!(cancelled_mutation, source);
    let error = graph_compile_error(&cancelled_mutation, "async-before-cleanup-owner-replace");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);

    // Shared internal references do not forbid a simultaneous shared owner read.
    let direct_owner_use = source.replace(
        "(#u64::add-wrap (#u64::add-wrap (#deref view) (#deref right-view)) result)",
        "(#u64::add-wrap (#u64::add-wrap (#u64::add-wrap (#deref view) (#deref right-view)) result) (#get (#get owner payload) left))",
    );
    assert_ne!(direct_owner_use, source);
    build_and_run_graph(&direct_owner_use, 98);
}

#[test]
fn pinned_async_frame_retains_enum_payload_reference_across_pending() {
    let source = include_str!("../examples/async_fn_enum_self_reference.lim");
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Read-after-await::poll");

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
    assert_single_poll(&generated, "Local-self-ref::poll");

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
            "    (#return (#u64::add-wrap (#deref view) result))",
            "    (#unsafe (#pin-write view 41u64))\n    (#return (#u64::add-wrap (#deref view) result))",
        );
    let generated = build_and_run_graph(&source, 43);
    assert_single_poll(&generated, "Local-self-ref::poll");

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
        "      (#let result #u64",
        "    (#let second-view (#pin-ref-mut #u64)\n      (#pin-borrow-mut (#get (#get owner payload) left)))\n    (#let result #u64",
    );
    assert_ne!(duplicate_exclusive_borrow, source);
    let error = graph_compile_error(
        &duplicate_exclusive_borrow,
        "async-exclusive-self-duplicate",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access") || error.contains("pinned"),
        "the same pinned projection must not be borrowed exclusively twice: {error}"
    );

    // Make the local owner explicitly linear so cleanup must return it after
    // clearing the internal exclusive reference; do not inspect private cells.
    let linear = source.replace("#struct LocalOwner ()", "\n#struct LocalOwner (#linear)")
        .replace("(#return (#u64::add-wrap (#deref view) result))",
            "(#let answer #u64 (#u64::add-wrap (#deref view) result))\n    (#drop view)\n    (#forget owner)\n    (#return answer)");
    let (prefix, after_second_poll) = linear
        .split_once("  (#let second Local-self-ref::Poll")
        .unwrap();
    let (_, suffix) = after_second_poll.split_once("  (#forget frame)").unwrap();
    let cancelled = format!(
        "{prefix}
  (#let cleanup Local-self-ref::Frame::Cleanup
  (#call Local-self-ref::Poll::cleanup ((task pending-frame))))
  (#let result #u64 (#match (#get cleanup owner)
  (#case Local-self-ref::Frame::Cleanup::Owner.Empty (#unreachable))
  (#case (Local-self-ref::Frame::Cleanup::Owner.Full extracted) (#block
  (#let-mut owned LocalOwner extracted)
  (#set-field owned payload (#struct-literal LocalPayload ((left 41u64) (right 5u64))))
  (#let value #u64 (#get (#get owned payload) left))
  (#forget owned) value))))
  (#match (#get cleanup await-0)
  (#case Local-self-ref::Frame::Cleanup::Await-0.Empty ())
  (#case (Local-self-ref::Frame::Cleanup::Await-0.Full child) (#forget child)))
  (#forget cleanup)
  (#forget frame){suffix}"
    );
    let generated = build_and_run_graph(&cancelled, 41);
    assert_single_poll(&generated, "Local-self-ref::poll");
}

#[test]
fn pinned_async_result_cannot_export_a_local_self_reference() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim")
        .replace(
            "(#fn local-self-ref ((seed #u64)) #u64",
            "(#fn local-self-ref ((seed #u64)) (#pin-ref #u64)",
        )
        .replace(
            "(#return (#u64::add-wrap (#deref view) result))",
            "(#return view)",
        )
        .replace(
            "(#let result #u64\n      (#match second",
            "(#let result (#pin-ref #u64)\n    (#match second",
        )
        .replace("(#return result)", "(#return (#deref result))");
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
    let (prefix, _) = original.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let source = format!(
        "{}#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
             (#let executor Executor
               (#struct-literal Executor ((notifications
                 (#call CellU64::create ((value 0u64)))))))
             (#let waker LocalWaker
               (#call local-waker-create ((executor (#borrow executor)) (metadata (#struct-literal WakeMetadata ((amount 1u64)))))))
             (#let result Work::Poll
               (#call Work::poll ((task (#call work ((offset 1u64)))) (waker (#borrow waker)))))
             (#let value #u64
               (#match result
                 (#case (Work::Poll.Ready value) value)
                 (#case (Work::Poll.Pending task)
                   (#block (#forget task) (#unreachable)))))
             (#call local-waker-destroy ((waker waker)))
             (#forget executor)
             (#return value)\n  );\n}}\n",
        prefix.replace(
            "(#let step Step (Step.Waiting 1u64))",
            "(#let step Step (Step.Waiting 0u64))"
        )
    );
    build_and_run_graph(&source, 41);
}

#[test]
fn async_function_without_await_runs_its_body_on_first_poll() {
    let source = format!(
        "#alias lim-gen-cell = \"{0}/library/cell.lim::#cell\"\n#generate lim-gen-cell #u64 CellU64 CellU64::create CellU64::get CellU64::set\n#generate #async-fn ((protocol work-await) (waker #u64) (function\n             (#fn work ((cell (#ref CellU64))) #u64\n               (#call CellU64::set ((cell cell) (value 1u64)))\n               (#return (#u64::add-wrap (#call CellU64::get ((cell cell))) 41u64)))))\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#let cell CellU64 (#call CellU64::create ((value 0u64))))\n             (#let task Work::Task (#call work ((cell (#borrow cell)))))\n             (#let before #u64 (#call CellU64::get ((cell (#borrow cell)))))\n             (#let waker #u64 0u64)\n             (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))\n             (#let result #u64\n               (#match outcome\n                 (#case (Work::Poll.Ready value) value)\n                 (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))\n             (#let after #u64 (#call CellU64::get ((cell (#borrow cell)))))\n             (#forget waker)\n             (#forget cell)\n             (#return (#if (#bool::and (#u64::eq before 0u64)\n                                    (#bool::and (#u64::eq result 42u64)\n                                              (#u64::eq after 1u64)))\n                           42u64 0u64))\n  );\n}}\n",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "Work::poll");
    assert!(
        generated_contains_form(&generated, "(Work::Poll.Ready)"),
        "{generated}"
    );
}

#[test]
fn pinned_async_function_without_await_runs_on_first_poll() {
    let source = format!(
        "#alias lim-gen-cell = \"{0}/library/cell.lim::#cell\"\n#generate lim-gen-cell #u64 CellU64 CellU64::create CellU64::get CellU64::set\n#generate #async-fn-pinned ((protocol work-await) (waker #u64) (function\n             (#fn work ((cell (#ref CellU64))) #u64\n               (#call CellU64::set ((cell cell) (value 1u64)))\n               (#return (#u64::add-wrap (#call CellU64::get ((cell cell))) 41u64)))))\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#let cell CellU64 (#call CellU64::create ((value 0u64))))\n             (#let-mut frame Work::Frame (#call work ((cell (#borrow cell)))))\n             (#let before #u64 (#call CellU64::get ((cell (#borrow cell)))))\n             (#let waker #u64 0u64)\n             (#let outcome Work::Poll\n               (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))\n             (#let result #u64\n               (#match outcome\n                 (#case (Work::Poll.Ready value) value)\n                 (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))\n             (#let after #u64 (#call CellU64::get ((cell (#borrow cell)))))\n             (#forget frame)\n             (#forget waker)\n             (#forget cell)\n             (#return (#if (#bool::and (#u64::eq before 0u64)\n                                    (#bool::and (#u64::eq result 42u64)\n                                              (#u64::eq after 1u64)))\n                           42u64 0u64))\n  );\n}}\n",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "Work::poll");
    assert!(
        generated_contains_form(&generated, "(#pin-ref-mut Work::Frame)"),
        "{generated}"
    );
    assert!(
        generated_contains_form(&generated, "(#fn Work::Poll::cleanup)"),
        "{generated}"
    );
}

#[test]
fn async_function_keeps_live_values_distinct_across_suspension() {
    let source = "#struct Box () ((value #u64))
#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (#block (#forget value) (ChildPoll.ChildReady 1u64)))))
  );
}
#fn echo {
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
        (#fn work ((first #u64)) #u64
            (#let value #u64 5u64)
            (#let box Box (#struct-literal Box ((value 7u64))))
            (#let child Child (Child.Waiting 0u64))
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll child))
            (#return (#u64::add-wrap
              (#call echo ((value 8u64)))
              (#u64::add-wrap first (#get box value)))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let outcome Work::Poll
            (#call Work::poll ((task (#call work ((first 2u64)))) (waker (#borrow waker)))))
          (#return (#match outcome
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))\n  );\n}\n";
    let source = source.replace(
        "(#block (#forget value) (ChildPoll.ChildReady 1u64))",
        "(#if (#u64::eq value 0u64) (ChildPoll.ChildPending (Child.Waiting 1u64)) (ChildPoll.ChildReady 1u64))"
    ).replace("(#return (#match outcome",
        "(#let-else (Work::Poll.Pending pending) Work::Poll outcome (#unreachable))\n        (#let resumed Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))\n        (#return (#match resumed");
    let generated = build_and_run_graph(&source, 17);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_requires_unused_linear_values_to_be_consumed_before_return() {
    let source = "#struct Token (#linear) ((value #u64))

#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (#block (#forget value) (ChildPoll.ChildReady 1u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let token Token (#struct-literal Token ((value 1u64))))
            (#let child Child (Child.Waiting 0u64))
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll child))
            (#return result))))
#fn main {\n  #params = ();\n  #returns = ();\n  #body = ( (#return ())\n  );\n}\n";
    let error = graph_compile_error(source, "async-unused-linear").message;
    assert!(
        error.contains("token") && (error.contains("linear") || error.contains("consum")),
        "{error:?}"
    );
}

#[test]
fn async_function_rejects_reference_to_pre_suspension_local() {
    let source = "#struct Waker () ((count #u64))
#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref Waker)));
  #returns = ChildPoll;
  #body = (
            (#return (ChildPoll.ChildPending task))
  );
}
#generate #async-fn ((protocol make-await) (waker Waker) (function (#fn make () #u64
              (#let owner #u64 1u64)
              (#let view (#ref #u64) (#borrow owner))
              (#let child Child (Child.Waiting 1u64))
              (#let value #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll child))
              (#return (#deref view)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 0u64)\n  );\n}\n";
    let error = graph_compile_error(source, "async-movable-local-borrow").message;
    assert!(
        error.contains("local") || error.contains("outlive") || error.contains("borrow"),
        "{error}"
    );
}

#[test]
fn async_function_accepts_no_arguments_or_captures() {
    let source = "#struct Waker () ((count #u64))
#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref Waker)));
  #returns = ChildPoll;
  #body = (
          (#forget task)
          (#return (ChildPoll.ChildReady 7u64))
  );
}
#generate #async-fn ((protocol work-await) (waker Waker) (function (#fn work () #u64
            (#let value #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#return value))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let outcome Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run_graph(source, 7);
}

#[test]
fn async_function_supports_multiple_awaits() {
    let source = example_without_cancel_work()
        .replace(
            "(#return (#u64::add-wrap total offset))",
            "(#if (#u64::eq offset 1u64)
           (#block (#set offset (#u64::add-wrap offset 5u64)) ())
           (#block (#set offset (#u64::add-wrap offset 10u64)) ()))
         (#match offset
           (#case 6u64 (#block (#set offset (#u64::add-wrap offset 1u64)) ()))
           (#case _ (#block (#set offset 99u64) ())))
         (#let second #u64
           (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 0u64)))
         (#return (#u64::add-wrap total offset))",
        )
        .replace("((offset #u64)) #u64", "((#mut offset #u64)) #u64");
    let generated = build_and_run_graph(&source, 48);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_has_no_fixed_suspension_count_limit() {
    let mut body = String::new();
    for index in 0..33 {
        body.push_str(&format!(
            "(#let result-{index} #u64 (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting {index}u64)))\n"
        ));
    }
    body.push_str("(#return result-32)");
    let source = format!(
        "#enum Step (#linear) ((Step.Waiting #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {{
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
             (#return (#match task (#case (Step.Waiting value) (StepPoll.StepReady value))))
  );
}}
#generate #async-fn ((protocol work-await) (waker #u64) (function
             (#fn work () #u64 {body})))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
             (#let waker #u64 0u64)
             (#let outcome Work::Poll
               (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
             (#let result #u64
               (#match outcome
                 (#case (Work::Poll.Ready value) value)
                 (#case (Work::Poll.Pending task) (#block (#forget task) 0u64))))
             (#forget waker)
             (#return result)\n  );\n}}\n"
    );
    let generated = build_and_run_graph(&source, 32);
    assert_single_poll(&generated, "Work::poll");
    assert!(
        generated.contains("Work::Task::Cleanup::Await-32"),
        "{generated}"
    );
}

#[test]
fn async_function_awaits_a_task_produced_by_an_earlier_await() {
    let source = "#enum OuterTask (#linear) ((OuterTask.Waiting #u64) (OuterTask.Resuming #u64))

#enum OuterPoll () ((OuterPoll.OuterPending OuterTask) (OuterPoll.OuterReady #u64))
#fn outer-poll {
  #params = ((task OuterTask) (waker (#ref #u64)));
  #returns = OuterPoll;
  #body = (
          (#return (#match task
            (#case (OuterTask.Waiting value) (OuterPoll.OuterPending (OuterTask.Resuming value)))
            (#case (OuterTask.Resuming value) (OuterPoll.OuterReady value))))
  );
}
#enum InnerTask () (InnerTask.MakeOuter)
#enum InnerPoll () ((InnerPoll.InnerPending InnerTask) (InnerPoll.InnerReady OuterTask))
#fn inner-poll {
  #params = ((task InnerTask) (waker (#ref #u64)));
  #returns = InnerPoll;
  #body = (
          (#return (#match task
            (#case InnerTask.MakeOuter (InnerPoll.InnerReady (OuterTask.Waiting 42u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#await OuterTask OuterPoll.OuterPending OuterPoll.OuterReady outer-poll
                (#await OuterTask InnerTask InnerPoll.InnerPending InnerPoll.InnerReady inner-poll InnerTask.MakeOuter)))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    assert!(!generated.contains("(#await"), "{generated}");

    // The same task dependency must work when the outer await is an operand,
    // not only when it is the direct RHS of a binding.
    let nested_operand = source.replace(
        "(#await OuterTask OuterPoll.OuterPending OuterPoll.OuterReady outer-poll\n                (#await OuterTask InnerTask InnerPoll.InnerPending InnerPoll.InnerReady inner-poll InnerTask.MakeOuter))",
        "(#u64::add-wrap 0u64\n            (#await #u64 OuterTask OuterPoll.OuterPending OuterPoll.OuterReady outer-poll\n              (#await OuterTask InnerTask InnerPoll.InnerPending InnerPoll.InnerReady inner-poll InnerTask.MakeOuter)))",
    );
    assert_ne!(nested_operand, source);
    let generated = build_and_run_graph(&nested_operand, 42);
    assert_single_poll(&generated, "Work::poll");
    assert!(!generated.contains("(#await"), "{generated}");

    // Both dependencies may return Pending. Completing the inner await must
    // initialize the outer task exactly once, then retain it for its own retry.
    let both_pending = nested_operand
        .replace("#enum InnerTask () (InnerTask.MakeOuter)", "#enum InnerTask () (InnerTask.MakeOuter InnerTask.ResumeOuter)")
        .replace(
            "(#case InnerTask.MakeOuter (InnerPoll.InnerReady (OuterTask.Waiting 42u64)))",
            "(#case InnerTask.MakeOuter (InnerPoll.InnerPending InnerTask.ResumeOuter))\n          (#case InnerTask.ResumeOuter (InnerPoll.InnerReady (OuterTask.Waiting 42u64)))",
        )
        .replace(
            "(#let second Work::Poll\n            (#call Work::poll ((task pending) (waker (#borrow waker)))))",
            "(#let middle Work::Poll\n          (#call Work::poll ((task pending) (waker (#borrow waker)))))\n        (#let-else (Work::Poll.Pending outer-pending) Work::Poll middle (#unreachable))\n        (#let second Work::Poll\n          (#call Work::poll ((task outer-pending) (waker (#borrow waker)))))",
        );
    assert_ne!(both_pending, nested_operand);
    build_and_run_graph(&both_pending, 42);
    build_and_run_graph(include_str!("../examples/async_nested_await.lim"), 42);
}

#[test]
fn async_function_awaits_directly_in_explicit_return() {
    let source = "#struct Waker () ((count #u64))
#enum Step (#linear) ((Step.Waiting #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref Waker)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Waiting count)
              (#if (#u64::eq count 0u64)
                (StepPoll.StepPending (Step.Waiting 1u64))
                (StepPoll.StepReady count)))))
  );
}
#generate #async-fn ((protocol work-await) (waker Waker) (function
          (#fn work ((initial #u64)) #u64
            (#return (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting initial))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((initial 0u64)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-task) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task first-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 1);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_extracts_typed_awaits_from_value_expressions() {
    let source = "#struct Waker () ((count #u64))
#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref Waker)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#fn sum {
  #params = ((a #u64) (b #u64));
  #returns = #u64;
  #body = ( (#return (#u64::add-wrap a b))
  );
}
#generate #async-fn ((protocol work-await) (waker Waker) (function
          (#fn work () #u64
            (#let result #u64 (#call sum ((
              b (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 20u64)))
              (a (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 10u64))))))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let outcome Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 30);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_call_arguments_are_evaluated_in_written_order_before_suspension() {
    let source = "#enum Child (#linear) (Child.Waiting)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Waiting))))
  );
}
#fn mark {
  #params = ((counter (#ref-mut #u64)));
  #returns = #u64;
  #body = (
          (#deref-set counter 1u64)
          (#return 3u64)
  );
}
#fn sum {
  #params = ((first #u64) (second #u64));
  #returns = #u64;
  #body = (
          (#return (#u64::add-wrap first second))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((counter (#ref-mut #u64))) #u64
            (#let result #u64
              (#call sum ((
                first (#call mark ((counter counter))))
                (second (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting)))))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut counter #u64 0u64)
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((counter (#borrow-mut counter)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll outcome (#unreachable))
          (#forget pending)
          (#forget waker)
          (#return counter)\n  );\n}\n";
    let generated = build_and_run_graph(source, 1);
    assert!(generated.contains("(#call mark"), "{generated}");
    let reordered = source.replace(
        "first (#call mark ((counter counter))))\n                (second (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting)",
        "second (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting))\n              (first (#call mark ((counter counter)))");
    assert_ne!(reordered, source);
    build_and_run_graph(&reordered, 0);
}

#[test]
fn async_named_argument_trace_survives_pending_resume_without_repetition() {
    let source = "#static trace (#atomic #u64) (#atomic-init #u64 0u64)
#fn mark {
  #params = ((digit #u64));
  #returns = ();
  #body = (
          (#let previous #u64 (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)))
          (#unsafe (#atomic-store (#borrow trace) (#u64::add-wrap (#u64::mul-wrap previous 10u64) digit) #memory-relaxed))
          (#return ())
  );
}
#enum Child (#linear) ((Child.Waiting #u64) (Child.Ready #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (#block (#call mark ((digit 2u64))) (ChildPoll.ChildPending (Child.Ready value))))
            (#case (Child.Ready value) (#block (#call mark ((digit 3u64))) (ChildPoll.ChildReady value)))))
  );
}
#fn combine {
  #params = ((first #u64) (second #u64));
  #returns = #u64;
  #body = (
          (#call mark ((digit 5u64))) (#return (#u64::add-wrap first second))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64 (#return (#call combine
            ((second (#block (#call mark ((digit 1u64)))
               (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 2u64))))
             (first (#block (#call mark ((digit 4u64))) 40u64))))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)) 12u64))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#panic)))))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow trace) #memory-relaxed)) 12345u64))
          (#return answer)\n  );\n}\n";
    build_and_run_graph(source, 42);
}

#[test]
fn async_numeric_operands_are_evaluated_in_source_order_before_suspension() {
    let source = "#enum Child (#linear) (Child.Waiting)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Waiting))))
  );
}
#fn mark {
  #params = ((counter (#ref-mut #u64)));
  #returns = #u64;
  #body = (
          (#deref-set counter 1u64)
          (#return 3u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((counter (#ref-mut #u64))) #u64
            (#return (#u64::add-wrap
              (#call mark ((counter counter)))
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut counter #u64 0u64)
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((counter (#borrow-mut counter)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll outcome (#unreachable))
          (#forget pending)
          (#forget waker)
          (#return counter)\n  );\n}\n";
    build_and_run_graph(source, 1);
}

#[test]
fn async_enum_payloads_are_evaluated_in_source_order_before_awaits() {
    let source = "#enum Data () ((Data.Pair (#tuple #u64 #u64)))
#enum Child (#linear) (Child.Waiting)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Waiting))))
  );
}
#fn mark {
  #params = ((counter (#ref-mut #u64)));
  #returns = #u64;
  #body = (
          (#deref-set counter 1u64)
          (#return 3u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((counter (#ref-mut #u64))) #u64
            (#let value Data
              (Data.Pair (#tuple
                (#call mark ((counter counter)))
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting))))
            (#return 0u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut counter #u64 0u64)
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((counter (#borrow-mut counter)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll outcome (#unreachable))
          (#forget pending)
          (#forget waker)
          (#return counter)\n  );\n}\n";
    build_and_run_graph(source, 1);
}

#[test]
fn async_nested_block_bindings_survive_suspension_inside_an_initializer() {
    let source = "#enum Child (#linear) (Child.Waiting Child.Resume)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Resume))
            (#case Child.Resume (ChildPoll.ChildReady 42u64))))
  );
}
#fn mark {
  #params = ((counter (#ref-mut #u64)));
  #returns = #u64;
  #body = (
          (#deref-set counter 1u64)
          (#return 3u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((counter (#ref-mut #u64))) #u64
            (#let result #u64
              (#block
                (#let before #u64 (#call mark ((counter counter))))
                (#let total #u64
                  (#u64::add-wrap before
                    (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting)))
                total))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut counter #u64 0u64)
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((counter (#borrow-mut counter)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll outcome (#unreachable))
          (#let resumed Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match resumed
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return (#u64::add-wrap counter result))\n  );\n}\n";
    build_and_run_graph(source, 46);
}

#[test]
fn async_nested_block_assignments_resume_after_awaited_rhs_values() {
    let source = "#enum Child (#linear) (Child.Waiting Child.Resume)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Resume))
            (#case Child.Resume (ChildPoll.ChildReady 42u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#block
                (#let-mut total #u64 3u64)
                (#set total
                  (#u64::add-wrap total
                    (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting)))
                total))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run_graph(source, 45);
}

#[test]
fn async_nested_block_effect_statements_can_await() {
    let source = "#enum Child (#linear) (Child.Waiting Child.Resume)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Resume))
            (#case Child.Resume (ChildPoll.ChildReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#block
                (#assert (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting))
                42u64))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run(source, 42);
}

#[test]
fn async_struct_fields_are_evaluated_in_source_order_before_suspension() {
    let source = "#struct Pair () ((first #u64) (second #u64))
#enum Child (#linear) (Child.Waiting)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Waiting))))
  );
}
#fn mark {
  #params = ((counter (#ref-mut #u64)));
  #returns = #u64;
  #body = (
          (#deref-set counter 1u64)
          (#return 3u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((counter (#ref-mut #u64))) #u64
            (#let pair Pair
              (#struct-literal Pair (
                (first (#call mark ((counter counter))))
                (second (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting)))))
            (#return (#get pair first)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut counter #u64 0u64)
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((counter (#borrow-mut counter)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll outcome (#unreachable))
          (#forget pending)
          (#forget waker)
          (#return counter)\n  );\n}\n";
    let generated = build_and_run(source, 1);
    assert!(generated.contains("(#call mark"), "{generated}");
}

#[test]
fn async_tuple_and_array_elements_are_evaluated_before_later_awaits() {
    let source = "#enum Child (#linear) (Child.Waiting)

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case Child.Waiting (ChildPoll.ChildPending Child.Waiting))))
  );
}
#fn mark {
  #params = ((counter (#ref-mut #u64)));
  #returns = #u64;
  #body = (
          (#deref-set counter 1u64)
          (#return 3u64)
  );
}
#generate #async-fn ((protocol work-tuple-await) (waker #u64) (function
          (#fn work-tuple ((counter (#ref-mut #u64))) #u64
            (#let pair (#tuple #u64 #u64)
              (#tuple (#tuple #u64 #u64)
                (#call mark ((counter counter)))
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting)))
            (#return 0u64))))
#generate #async-fn ((protocol work-array-await) (waker #u64) (function
          (#fn work-array ((counter (#ref-mut #u64))) #u64
            (#let values (#array #u64 2)
              (#array-of (#array #u64 2)
                (#call mark ((counter counter)))
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll Child.Waiting)))
            (#return 0u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut tuple-counter #u64 0u64)
          (#let-mut array-counter #u64 0u64)
          (#let waker #u64 0u64)
          (#let tuple-task Work-tuple::Task
            (#call work-tuple ((counter (#borrow-mut tuple-counter)))))
          (#let tuple-outcome Work-tuple::Poll
            (#call Work-tuple::poll ((task tuple-task) (waker (#borrow waker)))))
          (#let-else (Work-tuple::Poll.Pending tuple-pending) Work-tuple::Poll tuple-outcome (#unreachable))
          (#forget tuple-pending)
          (#let array-task Work-array::Task
            (#call work-array ((counter (#borrow-mut array-counter)))))
          (#let array-outcome Work-array::Poll
            (#call Work-array::poll ((task array-task) (waker (#borrow waker)))))
          (#let-else (Work-array::Poll.Pending array-pending) Work-array::Poll array-outcome (#unreachable))
          (#forget array-pending)
          (#forget waker)
          (#return (#u64::add-wrap tuple-counter array-counter))\n  );\n}\n";
    build_and_run(source, 2);
}

#[test]
fn async_function_extracts_typed_await_from_another_await_task() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                (ChildTask.Waiting
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 42u64)))))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let outcome Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");

    let inferred_source = source.replacen(
        "#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll\n                (ChildTask.Waiting",
        "#await ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll\n              (ChildTask.Waiting",
        1,
    );
    assert_ne!(inferred_source, source);
    let generated = build_and_run_graph(&inferred_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let return_source = source
        .replace("(#let result #u64\n              ", "(#return ")
        .replace("            (#return result)", "");
    assert_ne!(return_source, source);
    let generated = build_and_run_graph(&return_source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_suspends_in_a_value_block_with_conditional_await() {
    let source = "#enum StepTask (#linear) ((StepTask.Waiting #u64) (StepTask.Resuming #u64))
#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #u64))

#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (StepTask.Waiting value) (StepPoll.StepPending (StepTask.Resuming value)))
            (#case (StepTask.Resuming value) (StepPoll.StepReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((choose #bool)) #u64
            (#let value #u64
              (#block
                (#let base #u64 13u64)
                (#if choose
                  (#await #u64 StepTask StepPoll.StepPending StepPoll.StepReady step-poll (StepTask.Waiting base))
                  0u64)))
            (#return (#u64::add-wrap value 13u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((choose true))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let result #u64
            (#match first
              (#case (Work::Poll.Ready first-value) first-value)
              (#case (Work::Poll.Pending pending)
                (#match (#call Work::poll ((task pending) (waker (#borrow waker))))
                  (#case (Work::Poll.Ready second-value) second-value)
                  (#case (Work::Poll.Pending unexpected)
                    (#block (#forget unexpected) 0u64))))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 26);
    assert_single_poll(&generated, "Work::poll");
    let immediate = source.replace("((choose true))", "((choose false))");
    assert_ne!(immediate, source);
    build_and_run_graph(&immediate, 13);
}

#[test]
fn async_function_suspends_inside_mutable_assignment_rhs() {
    let source = "#struct Waker () ((count #u64))
#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref Waker)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 42u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker Waker) (function
          (#fn work () #u64
            (#let-mut total #u64 10u64)
            (#set total
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64)))
            (#return total))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_loop_expression_can_be_suspended_as_a_nested_value() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let ignored ()
              (#loop
                (#let result #u64
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                (#break)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready result) Work::Poll second (#unreachable))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_expression_can_be_suspended_as_a_nested_value() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let ignored ()
              (#block
                (#let-mut iteration #u64 0u64)
                (#while (#u64::lt iteration 1u64)
                  (#let result #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                  (#set iteration 1u64))))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready result) Work::Poll second (#unreachable))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_loop_expression_can_be_suspended_in_a_selected_branch() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((choose #bool)) #u64
            (#let ignored ()
              (#if choose
                (#loop
                  (#let value #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                  (#break))
                ()))
            (#return 42u64))))
#fn run {
  #params = ((choose #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((choose choose))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let awaited #u64 (#call run ((choose true) (waker (#borrow waker)))))
          (#let immediate #u64 (#call run ((choose false) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap awaited immediate))\n  );\n}\n";
    let generated = build_and_run_graph(source, 84);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_suspension_inside_nested_value_block_preserves_block_scope() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#fn identity {
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call identity ((value
                (#block
                  (#let value #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                  value)))))
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 41);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_value_loop_results_use_declared_expression_types() {
    let source = include_str!("../examples/async_loop_breaks.lim");
    let called = source
        .replace(
            "(#break 42u64)",
            "(#break (#call identity ((value 42u64))))",
        )
        .replace(
            "(#break awaited)",
            "(#break (#call identity ((value awaited))))",
        );
    assert_ne!(called, source);
    build_and_run_graph(&called, 42);

    let comparison = source
        .replace(
            "#fn identity {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}",
            "#fn identity {\n  #params = ((value #bool));\n  #returns = #u64;\n  #body = ( (#return (#if value 42u64 0u64))\n  );\n}",
        )
        .replace("(#break 42u64)", "(#break (#u64::eq awaited 41u64))")
        .replace("(#break awaited)", "(#break (#u64::lt awaited 42u64))")
        .replace("(#u64::eq final 41u64)", "(#u64::eq final 42u64)");
    build_and_run_graph(&comparison, 42);

    for (declarations, consumer, first, second) in [
        (
            "#struct Token () ((value #u64))\n",
            "#fn identity {\n  #params = ((token Token));\n  #returns = #u64;\n  #body = ( (#let value #u64 (#get token value)) (#forget token) (#return value)\n  );\n}\n",
            "(#struct-literal Token ((value 42u64)))",
            "(#struct-literal Token ((value awaited)))",
        ),
        (
            "#enum Outcome () ((Outcome.Value #u64))\n",
            "#fn identity {\n  #params = ((token Outcome));\n  #returns = #u64;\n  #body = ( (#return (#match token (#case (Outcome.Value value) value)))\n  );\n}\n",
            "(Outcome.Value 42u64)",
            "(Outcome.Value awaited)",
        ),
        (
            "",
            "#fn identity {\n  #params = ((token (#tuple #u64 #bool)));\n  #returns = #u64;\n  #body = ( (#return (#get token 0))\n  );\n}\n",
            "(#tuple (#tuple #u64 #bool) 42u64 true)",
            "(#tuple (#tuple #u64 #bool) awaited false)",
        ),
        (
            "",
            "#fn identity {\n  #params = ((token #u32));\n  #returns = #u64;\n  #body = ( (#return (#as token #u64))\n  );\n}\n",
            "(#as 42u64 #u32)",
            "(#as awaited #u32)",
        ),
    ] {
        let constructed = format!("{declarations}\n{}", source
            .replace("#fn identity {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}", consumer)
            .replace("(#call identity ((value", "(#call identity ((token")
            .replace("(#break 42u64)", &format!("(#break {first})"))
            .replace("(#break awaited)", &format!("(#break {second})")));
        build_and_run_graph(&constructed, 42);
    }
    let blocked = called.replace(
        "(#break (#call identity ((value 42u64))))",
        "(#break (#block (#let local #u64 42u64) (#call identity ((value local)))))",
    );
    build_and_run_graph(&blocked, 42);
    let conditional = called.replace(
        "(#break (#call identity ((value 42u64))))",
        "(#break (#if choose (#call identity ((value 42u64))) 0u64))",
    );
    build_and_run_graph(&conditional, 42);

    let invalid = format!(
        "#fn wrong-type {{\n  #params = ();\n  #returns = #u32;\n  #body = ( (#return 42u32)\n  );\n}}\n{}",
        called.replace("(#call identity ((value 42u64)))", "(#call wrong-type ())")
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
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#fn identity {
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call identity ((value
                (#loop
                  (#let awaited #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                  (#break awaited))))))
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 41);
    assert_single_poll(&generated, "Work::poll");

    let early_break = source.replace(
        "(#break awaited)",
        "(#if (#u64::eq awaited 41u64) (#break 42u64) ())\n                (#break awaited)",
    );
    assert_ne!(early_break, source);
    build_and_run_graph(&early_break, 42);
    let fallthrough = early_break.replace("(#u64::eq awaited 41u64)", "(#u64::eq awaited 0u64)");
    build_and_run_graph(&fallthrough, 41);
    let branch_only = source.replace(
        "(#break awaited)",
        "(#if (#u64::eq awaited 41u64) (#break 42u64) (#break awaited))",
    );
    build_and_run_graph(&branch_only, 42);
    let branch_fallthrough =
        branch_only.replace("(#u64::eq awaited 41u64)", "(#u64::eq awaited 0u64)");
    build_and_run_graph(&branch_fallthrough, 41);
    let branch_match = branch_only.replace(
        "(#if (#u64::eq awaited 41u64) (#break 42u64) (#break awaited))",
        "(#match (#u64::eq awaited 41u64) (#case true (#break 42u64)) (#case false (#break awaited)))",
    );
    build_and_run_graph(&branch_match, 42);
    let nested_branch = branch_only.replace(
        "(#if (#u64::eq awaited 41u64)",
        "(#let inner #u32 (#loop (#break 7u32)))\n                (#assert (#u32::eq inner 7u32))\n                (#if (#u64::eq awaited 41u64)",
    );
    build_and_run_graph(&nested_branch, 42);
    let outer_value = branch_only
        .replace("(#fn work () #u64", "(#fn work ((fallback #u64)) #u64")
        .replace("(#call work ())", "(#call work ((fallback 42u64)))")
        .replace("(#break 42u64)", "(#break fallback)");
    assert_ne!(outer_value, branch_only);
    build_and_run_graph(&outer_value, 42);
    let nested_loop = early_break.replace(
        "(#if (#u64::eq awaited 41u64)",
        "(#let nested #u64 (#loop (#break 7u64)))\n                (#assert (#u64::eq nested 7u64))\n                (#if (#u64::eq awaited 41u64)",
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
    let source = "#struct Token (#linear) ((value #u64))

#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady Token))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value)
              (ChildPoll.ChildReady (#struct-literal Token ((value value)))))))
  );
}
#fn consume-token {
  #params = ((token Token));
  #returns = #u64;
  #body = (
          (#let value #u64 (#get token value))
          (#forget token)
          (#return value)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call consume-token ((token
                (#loop
                  (#let token Token
                    (#await Token ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                  (#break token))))))
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run_graph(source, 41);
    let early_break = source.replace(
        "(#break token)",
        "(#if (#u64::eq (#get token value) 41u64) (#break token) ())\n                (#break token)",
    );
    assert_ne!(early_break, source);
    build_and_run_graph(&early_break, 41);
    let branch_only = source.replace(
        "(#break token)",
        "(#if (#u64::eq (#get token value) 41u64) (#break token) (#break token))",
    );
    build_and_run_graph(&branch_only, 41);
}

#[test]
fn async_value_loop_statement_can_discard_a_copy_break_result() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#loop
              (#let value #u64
                (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
              (#break (#u64::add-wrap value 1u64)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending-again)
                (#block (#forget pending-again) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_value_loop_statement_cannot_discard_a_linear_break_result() {
    let source = "#struct Token (#linear) ((value #u64))

#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady Token))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value)
              (ChildPoll.ChildReady (#struct-literal Token ((value value)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#loop
              (#let value Token
                (#await Token ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
              (#break value))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 0u64)\n  );\n}\n";
    let error = graph_compile_error(source, "discarded-linear-loop-result");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn async_unit_loop_expression_can_be_suspended_in_a_call_argument() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#fn consume-unit {
  #params = ((value ()));
  #returns = #u64;
  #body = ( (#return 42u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call consume-unit ((value
                (#loop
                  (#let awaited #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                  (#break))))))
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_unit_while_expression_can_be_suspended_in_a_call_argument() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#fn consume-unit {
  #params = ((value ()));
  #returns = #u64;
  #body = ( (#return 43u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call consume-unit ((value
                (#while true
                  (#let awaited #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 41u64)))
                  (#break))))))
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 43);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_range_expression_can_be_suspended_in_a_call_argument() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#fn consume-unit {
  #params = ((value ()));
  #returns = #u64;
  #body = ( (#return 44u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call consume-unit ((value
                (#for-range (iteration #u64) 0u64 1u64
                  (#let awaited #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                      (ChildTask.Waiting iteration))))))))
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 44);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_expression_can_be_suspended_in_a_call_argument() {
    let source = "#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#fn consume-unit {
  #params = ((value ()));
  #returns = #u64;
  #body = ( (#return 45u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call consume-unit ((value
                (#for (#let-mut iteration #u64 0u64)
                      (#u64::lt iteration 1u64)
                      (#set iteration (#u64::add-wrap iteration 1u64))
                  (#let awaited #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                      (ChildTask.Waiting iteration))))))))
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 45);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_let_expression_can_be_suspended_in_a_call_argument() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask () ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady Maybe))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady Maybe.None))))
  );
}
#fn consume-unit {
  #params = ((value ()));
  #returns = #u64;
  #body = ( (#return 46u64)
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#call consume-unit ((value
                (#while-let (Maybe.Some payload)
                  (#await Maybe ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64))
                  ())))) )
            (#return result))))
#fn run {
  #params = ((waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result #u64 (#call run ((waker (#borrow waker)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 46);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_suspends_inside_projected_assignment_rhs() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 42u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 0u64))
            (#set-index values 0usize
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64)))
            (#return (#index values 0usize)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_awaits_before_selecting_an_if_branch() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady true)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#if (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64))
                42u64
                0u64))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    let false_branch = source.replace(
        "(ChildPoll.ChildReady true)",
        "(ChildPoll.ChildReady false)",
    );
    assert_ne!(false_branch, source);
    build_and_run_graph(&false_branch, 0);
}

#[test]
fn async_function_awaits_before_selecting_a_match_arm() {
    let source = "#enum Decision () ((Decision.Continue #u64) Decision.Stop)
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady Decision))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady (Decision.Continue 42u64))
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#return (#match (#await Decision Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64))
              (#case (Decision.Continue value) value)
              (#case Decision.Stop 0u64))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    let stopped = source.replace(
        "(ChildPoll.ChildReady (Decision.Continue 42u64))",
        "(ChildPoll.ChildReady Decision.Stop)",
    );
    assert_ne!(stopped, source);
    build_and_run_graph(&stopped, 0);
}

#[test]
fn async_function_resumes_inside_a_value_producing_block() {
    let source = "#struct DecisionResult () ((condition #bool) (value #u64))
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady true)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result DecisionResult
              (#block
                (#let offset #u64 40u64)
                (#let choose #bool true)
                (#let condition #bool
                  (#if choose
                    (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                      (Child.Waiting (#u64::sub-wrap offset 39u64)))
                    false))
                (#struct-literal DecisionResult
                  ((condition condition)
                   (value (#if condition (#u64::add-wrap offset 2u64) 0u64))))))
            (#return (#get result value)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_assigns_conditional_await_result_inside_a_block() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady 42u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((choose #bool)) #u64
            (#return (#block
              (#let-mut result #u64 0u64)
              (#set result
                (#if choose
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))
                  7u64))
              result)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((choose true)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run_graph(source, 42);
}

#[test]
fn async_function_resumes_multiple_awaits_inside_one_block() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady true)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#block
                (#let first #bool
                  (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64)))
                (#let second #bool
                  (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 2u64)))
                (#if (#bool::and first second) 42u64 0u64)))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-first) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task after-first) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-second) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task after-second) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-third) Work::Poll third (#unreachable))
          (#let fourth Work::Poll (#call Work::poll ((task after-third) (waker (#borrow waker)))))
          (#let result #u64
            (#match fourth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_assigns_a_block_local_after_await_resumes() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 42u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut total (#array #u64 1)
              (#array-of (#array #u64 1) 1u64))
            (#let result #u64
              (#block
                (#set-index total 0usize
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64)))
                (#index total 0usize)))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_preserves_mutability_of_block_await_bindings() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 41u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#block
                (#let-mut value #u64
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64)))
                (#set value (#u64::add-wrap value 1u64))
                value))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_runs_block_prefix_side_effect_once_before_await() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady 42u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut count #u64 0u64)
            (#let result #u64
              (#block
                (#set count (#u64::add-wrap count 1u64))
                (#let value #u64
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
                (#u64::add-wrap value count)))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending running-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task running-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run(source, 43);
}

#[test]
fn async_function_suspends_on_a_discarded_copy_await_in_a_block() {
    let source = "#enum ChildTask (#linear) (ChildTask.Start ChildTask.Resume)

#enum ChildPoll () ((ChildPoll.Pending ChildTask) (ChildPoll.Ready ()))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Start (ChildPoll.Pending ChildTask.Resume))
            (#case ChildTask.Resume (ChildPoll.Ready ()))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#block
                (#let base #u64 40u64)
                (#await () ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)
                (#u64::add-wrap base 2u64)))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_rejects_discarding_a_linear_await_result_in_a_block() {
    let rejected = |source: &str, label: &str| {
        let error = graph_compile_error(source, label);
        assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
        assert!(error.message.contains("consumed explicitly"), "{error:?}");
        let span = error.span.expect("discarded expression source span");
        assert!(source[span.start..span.end].contains("#await"), "{error:?}");
    };
    let source = "#struct Resource (#linear) ((value #u64))

#enum ChildTask (#linear) (ChildTask.Start ChildTask.Resume)

#enum ChildPoll () ((ChildPoll.Pending ChildTask) (ChildPoll.Ready Resource))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Start (ChildPoll.Pending ChildTask.Resume))
            (#case ChildTask.Resume (ChildPoll.Ready (#struct-literal Resource ((value 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let result #u64
              (#block
                (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)
                42u64))
            (#return result))))\n";
    rejected(source, "discarded-linear-await-prefix");

    let direct_source = source.replace(
        "            (#let result #u64\n              (#block\n                (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)\n                42u64))\n            (#return result)",
        "          (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)\n          (#return 42u64)",
    );
    assert_ne!(direct_source, source);
    rejected(&direct_source, "discarded-linear-await-statement");

    let untyped_source = direct_source.replace(
        "#await Resource ChildTask ChildPoll.Pending",
        "#await ChildTask ChildPoll.Pending",
    );
    assert_ne!(untyped_source, direct_source);
    rejected(&untyped_source, "discarded-linear-await-payload-type");

    let terminal_block_source = source.replace(
        "            (#let result #u64\n              (#block\n                (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)\n                42u64))\n            (#return result)",
        "          (#block\n            (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start))\n          (#return 42u64)",
    );
    assert_ne!(terminal_block_source, source);
    rejected(&terminal_block_source, "discarded-linear-await-tail-block");

    let conditional_source = source.replace(
        "            (#let result #u64\n              (#block\n                (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)\n                42u64))\n            (#return result)",
        "          (#if true\n            (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)\n            (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Resume))\n          (#return 42u64)",
    );
    assert_ne!(conditional_source, source);
    rejected(&conditional_source, "discarded-linear-await-if");

    let match_source = source.replace(
        "            (#let result #u64\n              (#block\n                (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start)\n                42u64))\n            (#return result)",
        "          (#match true\n            (#case true (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Start))\n            (#case false (#await Resource ChildTask ChildPoll.Pending ChildPoll.Ready child-poll ChildTask.Resume)))\n          (#return 42u64)",
    );
    assert_ne!(match_source, source);
    rejected(&match_source, "discarded-linear-await-match");
}

#[test]
fn async_function_let_else_returns_ready_before_and_after_suspension() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe) (after Maybe)) #u64
            (#let-else (Maybe.Some payload) Maybe input (#return 7u64))
            (#let value #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 42u64)))
            (#let-else (Maybe.Some ignored) Maybe after (#return 9u64))
            (#return value))))
#fn Work::poll-work {
  #params = ((input Maybe) (after Maybe) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((input input) (after after))))
          (#let result Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match result
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let early #u64
            (#call Work::poll-work ((input Maybe.None) (after (Maybe.Some 1u64)) (waker (#borrow waker)))))
          (#let post-await #u64
            (#call Work::poll-work ((input (Maybe.Some 1u64)) (after Maybe.None) (waker (#borrow waker)))))
          (#let awaited #u64
            (#call Work::poll-work ((input (Maybe.Some 1u64)) (after (Maybe.Some 1u64)) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap (#u64::add-wrap early post-await) awaited))\n  );\n}\n";
    let generated = build_and_run(source, 58);
    assert!(
        generated_contains_form(&generated, "(Work::Poll.Ready)"),
        "{generated}"
    );
}

#[test]
fn async_function_can_await_let_else_scrutinee() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum Child (#linear) ((Child.Waiting Maybe))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady Maybe))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some value) Maybe
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting input))
              (#return 7u64))
            (#return value))))
#fn Work::poll-work {
  #params = ((input Maybe) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((input input))))
          (#let result Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match result
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let unmatched #u64
            (#call Work::poll-work ((input Maybe.None) (waker (#borrow waker)))))
          (#let matched #u64
            (#call Work::poll-work ((input (Maybe.Some 42u64)) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap unmatched matched))\n  );\n}\n";
    build_and_run(source, 49);
}

#[test]
fn async_function_awaits_inside_let_else_return_expression() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 7u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some value) Maybe input
              (#return (#u64::add-wrap 1u64
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64)))))
            (#return value))))\n";
    let source = format!(
        "{source}
#fn Work::poll-work {{
  #params = ((input Maybe) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
             (#let task Work::Task (#call work ((input input))))
             (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
             (#let result #u64
               (#match first
                 (#case (Work::Poll.Ready value) value)
                 (#case (Work::Poll.Pending pending) (#block
                   (#let second Work::Poll (#call Work::poll ((task pending) (waker waker))))
                   (#match second
                     (#case (Work::Poll.Ready value) value)
                     (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64)))))))
             (#return result)
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
             (#let waker #u64 0u64)
             (#let mismatch #u64 (#call Work::poll-work ((input Maybe.None) (waker (#borrow waker)))))
             (#let matched #u64 (#call Work::poll-work ((input (Maybe.Some 41u64)) (waker (#borrow waker)))))
             (#forget waker)
             (#return (#u64::add-wrap mismatch matched))\n  );\n}}\n"
    );
    build_and_run(&source, 49);
}

#[test]
fn async_let_else_can_await_before_an_unreachable_failure() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some payload) Maybe input
              (#block
                (#let ignored #u64
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64)))
                (#unreachable)))
            (#return payload))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((input (Maybe.Some 42u64)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let value #u64
            (#match outcome
              (#case (Work::Poll.Ready ready) ready)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_let_else_can_await_before_a_diverging_panic() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some payload) Maybe input
              (#block
                (#let ignored #u64
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64)))
                (#panic)))
            (#return payload))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((input (Maybe.Some 42u64)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_let_else_can_suspend_in_one_panic_only_branch() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe) (wait #bool)) #u64
            (#let-else (Maybe.Some payload) Maybe input
              (#if wait
                (#block
                  (#let ignored #u64
                    (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64)))
                  (#panic))
                (#panic)))
            (#return payload))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((input (Maybe.Some 42u64)) (wait true))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_let_else_can_suspend_in_one_panic_only_match_arm() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe) (wait #bool)) #u64
            (#let-else (Maybe.Some payload) Maybe input
              (#match wait
                (#case true
                  (#block
                    (#let ignored #u64
                      (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64)))
                    (#panic)))
                (#case false (#panic))))
            (#return payload))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((input (Maybe.Some 42u64)) (wait true))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_let_else_awaits_inside_an_assertion_before_unreachable() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask (#linear) (ChildTask.Waiting)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Waiting (ChildPoll.ChildReady 42u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some value) Maybe input
              (#block
                (#assert (#u64::eq
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting)
                  42u64))
                (#unreachable)))
            (#return value))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((input (Maybe.Some 42u64)))))
          (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_let_else_accepts_conditional_awaited_return_arms() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe) (choose #bool)) #u64
            (#let-else (Maybe.Some payload) Maybe input
              (#block
                (#let base #u64 13u64)
                (#if choose
                  (#return (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady
                    child-poll (ChildTask.Waiting base)))
                  (#return (#u64::add-wrap base 4u64)))))
            (#return payload))))
#fn drive {
  #params = ((input Maybe) (choose #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((input input) (choose choose))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready first-value) first-value)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready second-value) second-value)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let awaited #u64
            (#call drive ((input Maybe.None) (choose true) (waker (#borrow waker)))))
          (#let immediate #u64
            (#call drive ((input Maybe.None) (choose false) (waker (#borrow waker)))))
          (#let matched #u64
            (#call drive ((input (Maybe.Some 9u64)) (choose true) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap (#u64::add-wrap awaited immediate) matched))\n  );\n}\n";
    build_and_run(source, 39);
}

#[test]
fn async_let_else_diverging_branch_can_return_after_multiple_awaits() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some matched) Maybe input
              (#block
                (#let first #u64
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 20u64)))
                (#let second #u64
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                    (ChildTask.Waiting (#u64::add-wrap first 7u64))))
                (#return (#u64::add-wrap first second))))
            (#return matched))))
#fn run {
  #params = ((input Maybe) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((input input))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending after-first)
              (#match (#call Work::poll ((task after-first) (waker waker)))
                (#case (Work::Poll.Ready result) result)
                (#case (Work::Poll.Pending after-second)
                  (#match (#call Work::poll ((task after-second) (waker waker)))
                    (#case (Work::Poll.Ready result) result)
                    (#case (Work::Poll.Pending unexpected)
                      (#block (#forget unexpected) 0u64))))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let missing #u64 (#call run ((input Maybe.None) (waker (#borrow waker)))))
          (#let present #u64 (#call run ((input (Maybe.Some 9u64)) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap missing present))\n  );\n}\n";
    build_and_run(source, 56);
}

#[test]
fn async_graph_nested_let_else_await_uses_the_child_result_contract() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some value) Maybe input
              (#return (#u64::add-wrap 1u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 7u64)))))
            (#return value))))\n";
    let source = format!(
        "{source}
#fn run {{
  #params = ((input Maybe));
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let result Work::Poll
              (#call Work::poll ((task (#call work ((input input)))) (waker (#borrow waker)))))
            (#return (#match result
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#return (#u64::add-wrap
              (#call run ((input (Maybe.Some 42u64))))
              (#call run ((input Maybe.None)))))\n  );\n}}\n"
    );
    let generated = build_and_run_graph(&source, 50);
    assert_single_poll(&generated, "Work::poll");
    let suspended = source
        .replace(
            "(ChildPoll.ChildReady value)))))",
            "(#if (#u64::eq value 7u64) (ChildPoll.ChildPending (Child.Waiting 8u64)) (ChildPoll.ChildReady 7u64))))))",
        )
        .replace(
            "(#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))",
            "(#case (Work::Poll.Pending pending-task)
              (#block
                (#let second Work::Poll
                  (#call Work::poll ((task pending-task) (waker (#borrow waker)))))
                (#match second
                  (#case (Work::Poll.Ready resumed) resumed)
                  (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable))))))",
        );
    assert_ne!(suspended, source);
    build_and_run_graph(&suspended, 50);
}

#[test]
fn async_function_only_polls_awaited_let_else_mismatch_arm() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 7u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let-else (Maybe.Some value) Maybe input
              (#block
                (#let retry-count #u64 1u64)
                (#let first #u64
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                    (Child.Waiting retry-count)))
                (#let second #u64
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                    (Child.Waiting 0u64)))
                (#return (#u64::add-wrap first second))))
            (#let adjusted #u64 (#u64::add-wrap value 1u64))
            (#return adjusted))))
#fn Work::poll-work {
  #params = ((input Maybe) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((input input))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending running-task)
              (#block
                (#let second Work::Poll (#call Work::poll ((task running-task) (waker waker))))
                (#match second
                  (#case (Work::Poll.Ready value) value)
                  (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64)))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let mismatch #u64
            (#call Work::poll-work ((input Maybe.None) (waker (#borrow waker)))))
          (#let matched #u64
            (#call Work::poll-work ((input (Maybe.Some 42u64)) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap mismatch matched))\n  );\n}\n";
    build_and_run(source, 57);
}

#[test]
fn async_function_resumes_suspension_after_awaited_let_else_success() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum Child (#linear) ((Child.Waiting #u64) (Child.SuccessWaiting (#tuple #u64 #u64)))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 7u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))
            (#case (Child.SuccessWaiting (#tuple remaining value))
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady value)
                (ChildPoll.ChildPending
                  (Child.SuccessWaiting (#tuple (#tuple #u64 #u64) (#u64::sub-wrap remaining 1u64) value)))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#let base #u64 1u64)
            (#let-else (Maybe.Some value) Maybe input
            (#return (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                (Child.Waiting 1u64))))
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                (Child.SuccessWaiting (#tuple (#tuple #u64 #u64) 1u64 (#u64::add-wrap value base)))))
            (#return result))))
#fn Work::poll-work {
  #params = ((input Maybe) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((input input))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending running-task)
              (#block
                (#let second Work::Poll (#call Work::poll ((task running-task) (waker waker))))
                (#match second
                  (#case (Work::Poll.Ready value) value)
                  (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64)))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let mismatch #u64
            (#call Work::poll-work ((input Maybe.None) (waker (#borrow waker)))))
          (#let matched #u64
            (#call Work::poll-work ((input (Maybe.Some 42u64)) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap mismatch matched))\n  );\n}\n";
    build_and_run(source, 50);
}

#[test]
fn async_function_releases_let_else_success_borrow_after_ready() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum Child (#linear) ((Child.Waiting #u64) (Child.WriteAfterResume (#tuple (#ref-mut #u64) #u64)))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))
            (#case (Child.WriteAfterResume (#tuple owner remaining))
              (#if (#u64::eq remaining 0u64)
                (#block (#deref-set owner 42u64) (ChildPoll.ChildReady 42u64))
                (ChildPoll.ChildPending
                  (Child.WriteAfterResume (#tuple (#tuple (#ref-mut #u64) #u64) owner (#u64::sub-wrap remaining 1u64))))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe) (owner (#ref-mut #u64))) #u64
            (#let-else (Maybe.Some value) Maybe input
              (#return (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                (Child.Waiting 7u64))))
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                (Child.WriteAfterResume (#tuple (#tuple (#ref-mut #u64) #u64) owner 1u64))))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 1u64)
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work
            ((input (Maybe.Some 10u64)) (owner (#borrow-mut owner)))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          MUTATE_WHILE_PENDING
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64 (#match second
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unfinished) (#block (#forget unfinished) 0u64))))
          (#set owner 3u64)
          (#forget waker)
          (#return (#u64::add-wrap result owner))\n  );\n}\n";
    let accepted = source.replace("MUTATE_WHILE_PENDING", "");
    build_and_run_graph(&accepted, 45);

    // The failure branch completes immediately without lending owner to a
    // child. Its unused factory capture must not survive the Ready result.
    let fallback = format!(
        "{}\n#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut owner #u64 1u64)
            (#let waker #u64 0u64)
            (#let task Work::Task (#call work
              ((input Maybe.None) (owner (#borrow-mut owner)))))
            (#let outcome Work::Poll
              (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Ready result) Work::Poll outcome (#unreachable))
            (#set owner 3u64)
            (#forget waker)
            (#return (#u64::add-wrap result owner))\n  );\n}}\n",
        source.split("#fn main").next().unwrap()
    );
    build_and_run_graph(&fallback, 10);

    let rejected = source.replace("MUTATE_WHILE_PENDING", "(#set owner 4u64)");
    let error = graph_compile_error(&rejected, "let-else-success-retained-borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let span = error
        .span
        .expect("the rejected mutation needs a source span");
    assert_eq!(&rejected[span.start..span.end], "#set");
    assert_eq!(span.start, rejected.find("#set owner 4u64").unwrap());
}

#[test]
fn async_graph_nested_await_uses_the_child_result_contract() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = ( (#return (ChildPoll.ChildReady 1u64))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#return (#u64::add-wrap
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))
              1u64)))))\n";
    let source = format!(
        "{source}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let result Work::Poll
              (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
            (#return (#match result
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}}\n"
    );
    let generated = build_and_run_graph(&source, 2);
    assert_single_poll(&generated, "Work::poll");
    let suspended = source
        .replace(
            "(#return (ChildPoll.ChildReady 1u64))",
            "(#return (#match task (#case (Child.Waiting count)
              (#if (#u64::eq count 0u64) (ChildPoll.ChildPending (Child.Waiting 1u64)) (ChildPoll.ChildReady count)))))",
        )
        .replace(
            "(#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))",
            "(#case (Work::Poll.Pending pending-task)
              (#block
                (#let second Work::Poll
                  (#call Work::poll ((task pending-task) (waker (#borrow waker)))))
                (#match second
                  (#case (Work::Poll.Ready resumed) resumed)
                  (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable))))))",
        );
    assert_ne!(suspended, source);
    build_and_run_graph(&suspended, 2);
    let mismatched = source.replace(
        "#await Child ChildPoll.ChildPending",
        "#await #u32 Child ChildPoll.ChildPending",
    );
    let error = graph_compile_error(&mismatched, "async-nested-await-contract");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(error.message.contains("Ready payload"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&mismatched[span.start..span.end], "#u32");
}

#[test]
fn async_function_extracts_awaits_from_keyed_struct_literals() {
    let source = "#struct Waker () ((count #u64))
#struct Pair () ((left #u64) (right #u64))
#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref Waker)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker Waker) (function
          (#fn work () Pair
            (#let result Pair (#struct-literal Pair
              ((right (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 20u64)))
               (left (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 10u64))))))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let outcome Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready pair)
                (#u64::add-wrap (#get pair left) (#u64::mul-wrap 2u64 (#get pair right))))
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run(source, 50);
}

#[test]
fn async_function_awaits_after_conditional_task_selection() {
    let source = "#struct Waker () ((count #u64))
#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#enum Choice () ((Choice.Small) (Choice.Large))
#fn child-poll {
  #params = ((task Child) (waker (#ref Waker)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol choose-if-await) (waker Waker) (function
          (#fn choose-if ((large #bool)) #u64
            (#return (#if large
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 20u64))
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 10u64)))))))
#generate #async-fn ((protocol choose-match-await) (waker Waker) (function
          (#fn choose-match ((choice Choice)) #u64
            (#return (#match choice
              (#case Choice.Small (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 10u64)))
              (#case Choice.Large (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 20u64))))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let if-result Choose-if::Poll
            (#call Choose-if::poll ((task (#call choose-if ((large true)))) (waker (#borrow waker)))))
          (#let match-result Choose-match::Poll
            (#call Choose-match::poll ((task (#call choose-match ((choice Choice.Large)))) (waker (#borrow waker)))))
          (#let total #u64
            (#u64::add-wrap
              (#match if-result
                (#case (Choose-if::Poll.Ready value) value)
                (#case (Choose-if::Poll.Pending task) (#block (#forget task) (#unreachable))))
              (#match match-result
                (#case (Choose-match::Poll.Ready value) value)
                (#case (Choose-match::Poll.Pending task) (#block (#forget task) (#unreachable))))))
          (#forget waker)
          (#return total)\n  );\n}\n";
    let generated = build_and_run_graph(source, 40);
    assert_single_poll(&generated, "Choose-if::poll");
    assert_single_poll(&generated, "Choose-match::poll");
    let small = source
        .replace("((large true))", "((large false))")
        .replace("((choice Choice.Large))", "((choice Choice.Small))");
    assert_ne!(small, source);
    build_and_run_graph(&small, 20);
}

#[test]
fn async_conditional_await_joins_with_an_immediate_value() {
    let source = "#enum Child () ((Child.Waiting #u64))
#struct Increment () ((value #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady value)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((choose #bool)) #u64
            (#let result #u64
              (#if choose
                (#block
                  (#let increment Increment
                    (#struct-literal Increment ((value 1u64))))
                  (#let-mut awaited-value #u64
                    (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
                  (#let second-value #u64
                    (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting awaited-value)))
                  (#u64::add-wrap second-value (#get increment value)))
                41u64))
            (#return result))))
#enum Choice () (Choice.Await Choice.Immediate)
#generate #async-fn ((protocol work-match-await) (waker #u64) (function
          (#fn work-match ((choice Choice)) #u64
            (#let result #u64
              (#match choice
                (#case Choice.Await
                  (#block
                    (#let increment Increment
                      (#struct-literal Increment ((value 1u64))))
                    (#let-mut awaited-value #u64
                      (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
                    (#let second-value #u64
                      (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting awaited-value)))
                    (#u64::add-wrap second-value (#get increment value))))
                (#case Choice.Immediate 41u64)))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let awaited Work::Poll
            (#call Work::poll ((task (#call work ((choose true)))) (waker (#borrow waker)))))
          (#let awaited-value #u64
            (#match awaited
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending awaited-child)
                (#match (#call Work::poll ((task awaited-child) (waker (#borrow waker))))
                  (#case (Work::Poll.Ready awaited-ready) awaited-ready)
                  (#case (Work::Poll.Pending awaited-again)
                    (#match (#call Work::poll ((task awaited-again) (waker (#borrow waker))))
                      (#case (Work::Poll.Ready awaited-third-ready) awaited-third-ready)
                      (#case (Work::Poll.Pending awaited-third) (#block (#forget awaited-third) (#unreachable)))))))))
          (#let immediate Work::Poll
            (#call Work::poll ((task (#call work ((choose false)))) (waker (#borrow waker)))))
          (#let immediate-value #u64
            (#match immediate
              (#case (Work::Poll.Ready immediate-ready) immediate-ready)
              (#case (Work::Poll.Pending immediate-task) (#block (#forget immediate-task) (#unreachable)))))
          (#let match-awaited Work-match::Poll
            (#call Work-match::poll ((task (#call work-match ((choice Choice.Await)))) (waker (#borrow waker)))))
          (#let match-awaited-value #u64
            (#match match-awaited
              (#case (Work-match::Poll.Ready value) value)
              (#case (Work-match::Poll.Pending match-child)
                (#match (#call Work-match::poll ((task match-child) (waker (#borrow waker))))
                  (#case (Work-match::Poll.Ready match-ready) match-ready)
                  (#case (Work-match::Poll.Pending match-again)
                    (#match (#call Work-match::poll ((task match-again) (waker (#borrow waker))))
                      (#case (Work-match::Poll.Ready match-third-ready) match-third-ready)
                      (#case (Work-match::Poll.Pending match-third) (#block (#forget match-third) (#unreachable)))))))))
          (#let match-immediate Work-match::Poll
            (#call Work-match::poll ((task (#call work-match ((choice Choice.Immediate)))) (waker (#borrow waker)))))
          (#let match-immediate-value #u64
            (#match match-immediate
              (#case (Work-match::Poll.Ready match-immediate-ready) match-immediate-ready)
              (#case (Work-match::Poll.Pending match-immediate-task)
                (#block (#forget match-immediate-task) (#unreachable)))))
          (#return (#u64::add-wrap
            (#u64::add-wrap awaited-value immediate-value)
            (#u64::add-wrap match-awaited-value match-immediate-value)))\n  );\n}\n";
    let generated = build_and_run_graph(source, 86);
    assert_single_poll(&generated, "Work::poll");
    assert_single_poll(&generated, "Work-match::poll");
}

#[test]
fn async_conditional_branch_value_expressions_can_suspend() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady 41u64)))))
  );
}
#fn add-one {
  #params = ((value #u64));
  #returns = #u64;
  #body = (
          (#return (#u64::add-wrap value 1u64))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((choose #bool)) #u64
            (#return (#call add-one ((value
              (#block
                (#if choose
                  (#u64::add-wrap
                    (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))
                    1u64)
                  0u64)))))))))
#enum Choice () (Choice.Await Choice.Immediate)
#generate #async-fn ((protocol work-match-await) (waker #u64) (function
          (#fn work-match ((choice Choice)) #u64
            (#return (#call add-one ((value
              (#match choice
                (#case Choice.Await
                  (#u64::add-wrap
                    (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))
                    1u64))
                (#case Choice.Immediate 0u64)))))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let if-first Work::Poll
            (#call Work::poll ((task (#call work ((choose true)))) (waker (#borrow waker)))))
          (#let if-value #u64
            (#match if-first
              (#case (Work::Poll.Pending if-child)
                (#match (#call Work::poll ((task if-child) (waker (#borrow waker))))
                  (#case (Work::Poll.Ready value) value)
                  (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
              (#case (Work::Poll.Ready value) value)))
          (#let if-immediate Work::Poll
            (#call Work::poll ((task (#call work ((choose false)))) (waker (#borrow waker)))))
          (#let if-immediate-value #u64
            (#match if-immediate
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#let match-first Work-match::Poll
            (#call Work-match::poll ((task (#call work-match ((choice Choice.Await)))) (waker (#borrow waker)))))
          (#let match-value #u64
            (#match match-first
              (#case (Work-match::Poll.Pending match-child)
                (#match (#call Work-match::poll ((task match-child) (waker (#borrow waker))))
                  (#case (Work-match::Poll.Ready value) value)
                  (#case (Work-match::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
              (#case (Work-match::Poll.Ready value) value)))
          (#let match-immediate Work-match::Poll
            (#call Work-match::poll ((task (#call work-match ((choice Choice.Immediate)))) (waker (#borrow waker)))))
          (#let match-immediate-value #u64
            (#match match-immediate
              (#case (Work-match::Poll.Ready value) value)
              (#case (Work-match::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return (#u64::add-wrap
            (#u64::add-wrap if-value if-immediate-value)
            (#u64::add-wrap match-value match-immediate-value)))\n  );\n}\n";
    let generated = build_and_run_graph(source, 88);
    assert_single_poll(&generated, "Work::poll");
    assert_single_poll(&generated, "Work-match::poll");
}

fn check_graph_conditional_capture(source: &str) {
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    assert_frame_has_program_counter(&generated, "Work::Task");

    // The original immediate child alone cannot establish retention across
    // Pending. Force a suspension and consume its returned task on the retry.
    let suspended = source
        .replace(
            "#enum Child (#linear) ((Child.Waiting #u64))",
            "#enum Child (#linear) ((Child.Waiting #u64) (Child.Resuming #u64))",
        )
        .replace("(#case (Child.Waiting value) (ChildPoll.ChildReady value))", "(#case (Child.Waiting value) (ChildPoll.ChildPending (Child.Resuming value)))\n            (#case (Child.Resuming value) (ChildPoll.ChildReady value))")
        .replace("(#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))", "(#case (Work::Poll.Pending pending)\n              (#match (#call Work::poll ((task pending) (waker (#borrow waker))))\n                (#case (Work::Poll.Ready resumed) resumed)\n                (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))");
    assert_ne!(suspended, source);
    build_and_run_graph(&suspended, 42);
    let unselected = suspended.replace("(#if true", "(#if false");
    assert_eq!(unselected.matches("ChildPoll\n          (#return").count(), 1);
    let unselected = unselected.replace(
        "ChildPoll\n          (#return",
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
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((offset #u64)) #u64
            (#return (#if true
              (#u64::add-wrap
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 2u64))
                offset)
              0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((offset 40u64))))
          (#let result Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let value #u64
            (#match result
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    check_graph_conditional_capture(source);
}

#[test]
fn async_conditional_value_await_captures_typed_local_bindings() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let offset #u64 40u64)
            (#return (#if true
              (#u64::add-wrap
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 2u64))
                offset)
              0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let result Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let value #u64
            (#match result
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    check_graph_conditional_capture(source);
}

#[test]
fn async_conditional_continuations_can_change_result_type() {
    let source = "#enum Step (#linear) ((Step.Waiting #u64) (Step.Resuming #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Waiting value) (StepPoll.StepPending (Step.Resuming value)))
            (#case (Step.Resuming value) (StepPoll.StepReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((choose #bool)) #bool
            (#return (#if choose
              (#block
                (#let awaited #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 41u64)))
                (#u64::eq awaited 41u64))
              false)))))
#fn run {
  #params = ((choose #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let first Work::Poll (#call Work::poll ((task (#call work ((choose choose)))) (waker waker))))
          (#let result #bool (#match first
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending pending)
              (#match (#call Work::poll ((task pending) (waker waker)))
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))))
          (#return (#if result 42u64 0u64))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let selected #u64 (#call run ((choose true) (waker (#borrow waker)))))
          (#let skipped #u64 (#call run ((choose false) (waker (#borrow waker)))))
          (#assert (#u64::eq skipped 0u64))
          (#forget waker)
          (#return selected)\n  );\n}\n";
    build_and_run(source, 42);
    let expression = source.replace(
        "(#block\n                (#let awaited #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 41u64)))\n                (#u64::eq awaited 41u64))",
        "(#u64::eq (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 41u64)) 41u64)",
    );
    assert_ne!(expression, source);
    build_and_run(&expression, 42);
    let multiple = source.replace(
        "(#u64::eq awaited 41u64)",
        "(#block (#let another #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Resuming awaited))) (#u64::eq another 41u64))",
    );
    build_and_run(&multiple, 42);

    let linear = format!(
        "#struct Token () ((value #u64))\n{}",
        source
            .replace(
                "(#fn work ((choose #bool)) #bool",
                "(#fn work ((choose #bool)) Token"
            )
            .replace(
                "(#u64::eq awaited 41u64)",
                "(#struct-literal Token ((value (#u64::add-wrap awaited 1u64))))"
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
        .replace("(#u64::eq awaited 41u64)", "view")
        .replacen("false", "view", 1)
        .replace(
            "#fn run {\n  #params = ((choose #bool) (waker (#ref #u64)));",
            "#fn run {\n  #params = ((choose #bool) (view (#ref #u64)) (waker (#ref #u64)));",
        )
        .replace(
            "(#call work ((choose choose)))",
            "(#call work ((choose choose) (view view)))",
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
            "(choose true) (waker",
            "(choose true) (view (#borrow storage)) (waker",
        )
        .replace(
            "(choose false) (waker",
            "(choose false) (view (#borrow storage)) (waker",
        )
        .replace("(#u64::eq skipped 0u64)", "(#u64::eq skipped 42u64)");
    build_and_run(&borrowed, 42);
    let definitions = borrowed.split_once("#fn main").unwrap().0;
    let suspended = format!("{definitions}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut storage #u64 42u64)
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((choose true) (view (#borrow storage))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          MUTATE_HERE
          (#forget pending)
          (#set storage 42u64)
          (#forget waker)\n          (#return storage)\n  );\n}}\n");
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
    let source = "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((offset #u64)) #u64
            (#return (#if true
              (#block
                (#let result #u64
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 2u64)))
                (#u64::add-wrap result offset))
              0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ((offset 40u64))))
          (#let result Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let value #u64
            (#match result
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("offset #u64"), "{generated}");
}

#[test]
fn async_conditional_choice_captures_and_releases_a_borrow_on_cancel() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady value)))))
  );
}
#fn cancel-child {
  #params = ((task Child));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#generate #async-fn ((protocol work-await) (waker #u64)
          (cancel (cancel-work ((await-0 cancel-child)))) (function
          (#fn work ((choose #bool) (view (#ref #u64))) #u64
            (#let result #u64
              (#if choose
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))
                41u64))
            (#return (#u64::add-wrap result (#deref view))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 1u64)
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((choose true) (view (#borrow owner)))))
              (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          CHECK_HERE
          (#call cancel-work ((task (#call Work::Poll::cleanup ((task pending))))))
          (#set owner 42u64)
          (#let immediate Work::Poll
            (#call Work::poll ((task (#call work ((choose false) (view (#borrow owner)))))
              (waker (#borrow waker)))))
          (#let answer #u64
            (#match immediate
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget waker)
          (#return answer)\n  );\n}\n";

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
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_rejects_conditional_awaits_with_different_result_types() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64) (ChildPoll.ChildAlternateReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#fn child-poll-alt {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (ChildPoll.ChildAlternateReady 2u64))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#return (#if true
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 1u64))
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildAlternateReady child-poll-alt (Child.Waiting 2u64)))))))\n";
    let mismatched = source.replace(
        "#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildAlternateReady child-poll-alt",
        "#await #u32 Child ChildPoll.ChildPending ChildPoll.ChildAlternateReady child-poll-alt",
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
    let source = "#enum LeftChild () ((LeftChild.LeftWaiting #u64))
#enum LeftPoll () ((LeftPoll.LeftPending LeftChild) (LeftPoll.LeftReady #u64))
#fn left-poll {
  #params = ((task LeftChild) (waker (#ref #u64)));
  #returns = LeftPoll;
  #body = (
          (#return (#match task
            (#case (LeftChild.LeftWaiting value)
              (#if (#u64::eq value 0u64)
                (LeftPoll.LeftPending (LeftChild.LeftWaiting 1u64))
                (LeftPoll.LeftReady value)))))
  );
}
#enum RightChild () ((RightChild.RightWaiting #u64))
#enum RightPoll () ((RightPoll.RightPending RightChild) (RightPoll.RightReady #u64))
#fn right-poll {
  #params = ((task RightChild) (waker (#ref #u64)));
  #returns = RightPoll;
  #body = (
          (#return (#match task (#case (RightChild.RightWaiting value) (RightPoll.RightReady (#u64::add-wrap value 1u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((choose-left #bool)) #u64
            (#return (#if choose-left
              (#await #u64 LeftChild LeftPoll.LeftPending LeftPoll.LeftReady left-poll (LeftChild.LeftWaiting 0u64))
              (#await #u64 RightChild RightPoll.RightPending RightPoll.RightReady right-poll (RightChild.RightWaiting 2u64)))))))
#enum Choice () (Choice.Left Choice.Right)
#generate #async-fn ((protocol work-match-await) (waker #u64) (function
          (#fn work-match ((choice Choice)) #u64
            (#return (#match choice
              (#case Choice.Left
                (#await #u64 LeftChild LeftPoll.LeftPending LeftPoll.LeftReady left-poll (LeftChild.LeftWaiting 0u64)))
              (#case Choice.Right
                (#await #u64 RightChild RightPoll.RightPending RightPoll.RightReady right-poll (RightChild.RightWaiting 2u64))))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let left-first Work::Poll
            (#call Work::poll ((task (#call work ((choose-left true)))) (waker (#borrow waker)))))
          (#let left Work::Poll
            (#match left-first
              (#case (Work::Poll.Pending task)
                (#call Work::poll ((task task) (waker (#borrow waker)))))
              (#case (Work::Poll.Ready value) (Work::Poll.Ready value))))
          (#let left-value #u64
            (#match left
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#let right Work::Poll
            (#call Work::poll ((task (#call work ((choose-left false)))) (waker (#borrow waker)))))
          (#let right-value #u64
            (#match right
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#let matched Work-match::Poll
            (#call Work-match::poll ((task (#call work-match ((choice Choice.Right)))) (waker (#borrow waker)))))
          (#let matched-value #u64
            (#match matched
              (#case (Work-match::Poll.Ready value) value)
              (#case (Work-match::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return (#u64::add-wrap (#u64::add-wrap left-value right-value) matched-value))\n  );\n}\n";
    let generated = build_and_run(source, 7);
    assert!(generated.contains("LeftChild"), "{generated}");
    assert!(generated.contains("RightChild"), "{generated}");
    assert!(generated.contains("left-poll"), "{generated}");
    assert!(generated.contains("right-poll"), "{generated}");
}

#[test]
fn async_function_retains_external_borrows_across_pending() {
    let source = "#struct Waker () ((count #u64))
#enum Step (#linear) ((Step.Waiting #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref Waker)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Waiting count)
              (#if (#u64::eq count 0u64)
                (StepPoll.StepPending (Step.Waiting 1u64))
                (StepPoll.StepReady count)))))
  );
}
#generate #async-fn ((protocol read-after-await-await) (waker Waker) (function
          (#fn read-after-await ((view (#ref #u64))) #u64
            (#let result #u64
              (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 0u64)))
            (#return (#u64::add-wrap (#deref view) result)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 37u64)
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let first Read-after-await::Poll
            (#call Read-after-await::poll ((task (#call read-after-await ((view (#borrow owner)))))
              (waker (#borrow waker)))))
          (#let-else (Read-after-await::Poll.Pending task) Read-after-await::Poll first (#unreachable))
          MUTATE_WHILE_PENDING
          (#let second Read-after-await::Poll
            (#call Read-after-await::poll ((task task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Read-after-await::Poll.Ready value) value)
              (#case (Read-after-await::Poll.Pending extra-task) (#block (#forget extra-task) (#unreachable)))))
          (#set owner 39u64)
          (#forget waker)
          (#return (#u64::add-wrap owner result))\n  );\n}\n";
    let accepted = source.replace("MUTATE_WHILE_PENDING", "");
    build_and_run_graph(&accepted, 77);

    let rejected = source.replace(
        "MUTATE_WHILE_PENDING",
        "(#set owner (#u64::add-wrap owner 1u64))",
    );
    let error = graph_compile_error(&rejected, "async-shared-external-pending-mutation");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("mutate") || error.contains("loan"),
        "{error}"
    );

    let escaping = accepted.replace(
        "#fn main {\n  #params = ();\n  #returns = #u64;",
        "#fn escape {\n  #params = ();\n  #returns = Read-after-await::Task;\n  #body = (\n          (#let owner #u64 3u64)\n          (#return (#call read-after-await ((view (#borrow owner)))))\n  );\n}\n#fn main {\n  #params = ();\n  #returns = #u64;",
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
    let source = "#struct Waker () ((count #u64))
#enum Step (#linear) ((Step.Waiting #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref Waker)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Waiting count)
              (#if (#u64::eq count 0u64)
                (StepPoll.StepPending (Step.Waiting 1u64))
                (StepPoll.StepReady count)))))
  );
}
#generate #async-fn ((protocol write-after-await-await) (waker Waker) (function
          (#fn write-after-await ((view (#ref-mut #u64))) #u64
            (#let result #u64
              (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 0u64)))
            (#deref-set view (#u64::add-wrap (#deref view) result))
            (#return (#deref view)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 37u64)
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let first Write-after-await::Poll
            (#call Write-after-await::poll ((task (#call write-after-await ((view (#borrow-mut owner)))))
              (waker (#borrow waker)))))
          (#let-else (Write-after-await::Poll.Pending task) Write-after-await::Poll first (#unreachable))
          READ_WHILE_PENDING
          (#let second Write-after-await::Poll
            (#call Write-after-await::poll ((task task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Write-after-await::Poll.Ready value) value)
              (#case (Write-after-await::Poll.Pending extra-task) (#block (#forget extra-task) (#unreachable)))))
          (#set owner 39u64)
          (#return (#u64::add-wrap result owner))\n  );\n}\n";
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
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting count)
              (#if (#u64::eq count 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady count)))))
  );
}
#generate #async-fn-pinned ((protocol read-after-await-await) (waker #u64) (function
          (#fn read-after-await ((view (#pin-ref #u64))) #u64
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#return (#u64::add-wrap (#deref view) result)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 40u64)
          (#let view (#pin-ref #u64) (#pin-borrow owner))
          (#let-mut frame Read-after-await::Frame (#call read-after-await ((view view))))
          (#forget view)
          (#let waker #u64 0u64)
          (#let first Read-after-await::Poll
            (#call Read-after-await::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Read-after-await::Poll.Pending pinned-frame) Read-after-await::Poll first (#unreachable))
          (#let second Read-after-await::Poll
            (#call Read-after-await::poll ((task pinned-frame) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Read-after-await::Poll.Ready value) value)
              (#case (Read-after-await::Poll.Pending unexpected)
                (#block (#forget unexpected) (#unreachable)))))
          (#forget frame)
          (#set owner 41u64)
          (#forget waker)
          (#return (#if (#u64::eq result 41u64) owner 0u64))\n  );\n}\n";

    let mutation_while_pending = source.replace(
        "        (#let second Read-after-await::Poll",
        "        (#set owner 99u64)\n        (#let second Read-after-await::Poll",
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
    let source = "#struct Waker () ((count #u64))
#enum Step (#linear) ((Step.Waiting #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref Waker)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Waiting count) (StepPoll.StepPending (Step.Waiting count)))))
  );
}
#fn cancel-step {
  #params = ((task Step));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#generate #async-fn ((protocol work-await) (waker Waker)
          (cancel (cancel-work ((await-0 cancel-step)))) (function
          (#fn work ((view (#ref-mut #u64))) #u64
            (#let result #u64
              (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 0u64)))
            (#return (#deref view)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 37u64)
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((view (#borrow-mut owner)))))
              (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          WHILE_PENDING
          (#call cancel-work ((task (#call Work::Poll::cleanup ((task pending))))))
          (#set owner 42u64)
          (#return owner)\n  );\n}\n";
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
    let source = "#struct Waker () ((count #u64))
#enum Step (#linear) ((Step.Waiting #u64))

#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref Waker)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Waiting count)
              (#if (#u64::eq count 0u64)
                (StepPoll.StepPending (Step.Waiting 1u64))
                (StepPoll.StepReady count)))))
  );
}
#generate #async-fn ((protocol work-await) (waker Waker) (function
          (#fn work ((#mut initial #u64)) #u64
            (#set initial (#u64::add-wrap initial 1u64))
            (#let-mut total #u64 initial)
            (#let-mut result #u64
              (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 0u64)))
            (#set result (#u64::add-wrap result 0u64))
            (#set total (#u64::add-wrap total result))
            (#return total))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((count 0u64))))
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((initial 2u64)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-task) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task first-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 4);
    assert_single_poll(&generated, "Work::poll");
    // Mutability belongs to the source body, not its capture-only constructor.
    assert_generated_signature(&generated, "(#fn work ((initial #u64)) Work::Task)");
}

#[test]
fn async_function_rejects_assignment_to_immutable_capture() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = ( (#return (ChildPoll.ChildReady 1u64))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let total #u64 2u64)
            (#let result #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#set total result)
            (#return result))))\n";
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
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task (#case (Child.Waiting value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#return (#if true
              (#block
                (#let task-input #u64 17u64)
                (#let result #u64
                  (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting task-input)))
                result)
              0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let outcome Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let value #u64
            (#match outcome
              (#case (Work::Poll.Ready ready) ready)
              (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable)))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    let generated = build_and_run_graph(source, 17);
    assert_single_poll(&generated, "Work::poll");
    // A source input consumed before poll must not become a cancellation slot.
    assert!(
        !generated.contains("Work::Task::Cleanup::Task::input"),
        "{generated}"
    );
}

#[test]
fn async_function_resumes_a_child_await_inside_a_while_loop() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady value)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#while (#u64::lt iteration 2u64)
              (#let child-input #u64 iteration)
              (#let result #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting child-input)))
              (#set iteration (#u64::add-wrap iteration 1u64)))
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending-again)
                (#block (#forget pending-again) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(&source, 2);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_body_suspends_inside_a_call_argument() {
    let source = format!(
        "#alias lim-gen-cell = \"{0}/library/cell.lim::#cell\"\n#generate lim-gen-cell #u64 CellU64 CellU64::create CellU64::get CellU64::set\n#enum ChildTask (#linear) ((ChildTask.Waiting #u64))\n\n#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))\n#fn child-poll {{\n  #params = ((task ChildTask) (waker (#ref #u64)));\n  #returns = ChildPoll;\n  #body = (\n             (#return (#match task\n               (#case (ChildTask.Waiting remaining)\n                 (#if (#u64::eq remaining 0u64)\n                   (ChildPoll.ChildPending (ChildTask.Waiting 1u64))\n                   (ChildPoll.ChildReady 42u64)))))\n  );\n}}\n#generate #async-fn ((protocol work-await) (waker #u64) (function\n             (#fn work ((cell (#ref CellU64))) #u64\n               (#let-mut iteration #u64 0u64)\n               (#while (#u64::lt iteration 1u64)\n                 (#call CellU64::set ((cell cell) (value\n                   (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64)))))\n                 (#set iteration (#u64::add-wrap iteration 1u64)))\n               (#return (#call CellU64::get ((cell cell)))))))\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#let cell CellU64 (#call CellU64::create ((value 0u64))))\n             (#let waker #u64 0u64)\n             (#let task Work::Task (#call work ((cell (#borrow cell)))))\n             (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))\n             (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))\n             (#let before #u64 (#call CellU64::get ((cell (#borrow cell)))))\n             (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))\n             (#let result #u64\n               (#match second\n                 (#case (Work::Poll.Ready value) value)\n                 (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))\n             (#forget waker)\n             (#forget cell)\n             (#return (#if (#bool::and (#u64::eq before 0u64)\n                                    (#u64::eq result 42u64))\n                           42u64 0u64))\n  );\n}}\n",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_body_suspends_inside_a_call_argument() {
    let source = format!(
        "#alias lim-gen-cell = \"{0}/library/cell.lim::#cell\"\n#generate lim-gen-cell #u64 CellU64 CellU64::create CellU64::get CellU64::set\n#enum ChildTask (#linear) ((ChildTask.Waiting #u64))\n\n#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))\n#fn child-poll {{\n  #params = ((task ChildTask) (waker (#ref #u64)));\n  #returns = ChildPoll;\n  #body = (\n             (#return (#match task\n               (#case (ChildTask.Waiting remaining)\n                 (#if (#u64::eq remaining 0u64)\n                   (ChildPoll.ChildPending (ChildTask.Waiting 1u64))\n                   (ChildPoll.ChildReady 42u64)))))\n  );\n}}\n#generate #async-fn ((protocol work-await) (waker #u64) (function\n             (#fn work ((cell (#ref CellU64))) #u64\n               (#for (#let-mut iteration #u64 0u64)\n                     (#u64::lt iteration 1u64)\n                     (#set iteration (#u64::add-wrap iteration 1u64))\n                 (#call CellU64::set ((cell cell) (value\n                   (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64))))))\n               (#return (#call CellU64::get ((cell cell)))))))\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#let cell CellU64 (#call CellU64::create ((value 0u64))))\n             (#let waker #u64 0u64)\n             (#let task Work::Task (#call work ((cell (#borrow cell)))))\n             (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))\n             (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))\n             (#let before #u64 (#call CellU64::get ((cell (#borrow cell)))))\n             (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))\n             (#let result #u64\n               (#match second\n                 (#case (Work::Poll.Ready value) value)\n                 (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))\n             (#forget waker)\n             (#forget cell)\n             (#return (#if (#bool::and (#u64::eq before 0u64)\n                                    (#u64::eq result 42u64))\n                           42u64 0u64))\n  );\n}}\n",
        env!("CARGO_MANIFEST_DIR")
    );
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_resumes_a_child_await_in_a_while_condition() {
    let source = include_str!("../examples/async_fn_while_condition.lim");
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_block_owned_labeled_loop_keeps_its_scope_across_suspension() {
    let source = include_str!("../examples/async_block_loop.lim");
    build_and_run(source, 42);
    let returned = source.replace("(#let result #u64", "(#return").replace(
        "total))\n      // The inner scope has ended; this is an independent declaration.\n      (#let index #u64 0u64)\n      (#return (#u64::add-wrap result index)))))",
        "total)))))",
    );
    build_and_run(&returned, 42);
    let outer_mutation = source.replace(
        "(#let result #u64\n        (#block\n          (#let-mut index #u64 0u64)\n          (#let-mut total #u64 40u64)",
        "(#let-mut total #u64 40u64)\n    (#let result #u64\n      (#block\n        (#let-mut index #u64 0u64)",
    ).replace("(#u64::add-wrap result index)", "(#u64::add-wrap result (#u64::sub-wrap total 40u64))");
    build_and_run(&outer_mutation, 44);
    build_and_run(
        &outer_mutation.replace(
            "(StepPoll.StepPending (Step.Resume value))",
            "(StepPoll.StepReady value)",
        ),
        44,
    );
    build_and_run(
        &outer_mutation.replace("(#await #u64 Step", "(#await Step"),
        44,
    );
    build_and_run(
        &outer_mutation
            .replace("(#u64::lt index 2u64)", "false")
            .replace("(StepPoll.StepPending (Step.Resume value))", "(#panic)"),
        40,
    );
    let borrowed_update = format!(
        "#fn increment {{
  #params = ((target (#ref-mut #u64)) (value #u64));
  #returns = ();
  #body = (
          (#deref-set target (#u64::add-wrap (#deref target) value)) (#return ())\n  );
}}
{}",
        outer_mutation.replace(
            "(#set total (#u64::add-wrap total value))",
            "(#call increment ((target (#borrow-mut total)) (value value)))"
        )
    );
    build_and_run(&borrowed_update, 44);
    let linear = format!("#struct Counter (#linear) ((value #u64))\n \n{}", outer_mutation
        .replace("(#let-mut total #u64 40u64)", "(#let-mut total Counter (#struct-literal Counter ((value 40u64))))")
        .replace("(#set total (#u64::add-wrap total value))", "(#set-field total value (#u64::add-wrap (#get total value) value))")
        .replace("total))\n      //", "(#get total value)))\n    //")
        .replace("(#return (#u64::add-wrap result (#u64::sub-wrap total 40u64)))", "(#let answer #u64 (#u64::add-wrap result (#u64::sub-wrap (#get total value) 40u64))) (#forget total) (#return answer)"));
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
    let source = "#enum ChildTask () ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut index #u64 0u64)
            (#label outer
              (#while (#u64::lt index 2u64)
                (#let ignored #u64
                  (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting index)))
                (#set index (#u64::add-wrap index 1u64))
                (#continue-to outer)))
            (#return index))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-frame) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-frame) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task second-frame) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    build_and_run(source, 2);
}

#[test]
fn async_while_condition_sequences_short_circuit_awaits() {
    let source = "#enum BoolTask (#linear) ((BoolTask.Waiting #bool) (BoolTask.Resuming #bool))

#enum BoolPoll () ((BoolPoll.BoolPending BoolTask) (BoolPoll.BoolReady #bool))
#fn bool-poll {
  #params = ((task BoolTask) (waker (#ref #u64)));
  #returns = BoolPoll;
  #body = (
          (#return (#match task
            (#case (BoolTask.Waiting value) (BoolPoll.BoolPending (BoolTask.Resuming value)))
            (#case (BoolTask.Resuming value) (BoolPoll.BoolReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iterations #u64 0u64)
            (#while (#bool::and
              (#await #bool BoolTask BoolPoll.BoolPending BoolPoll.BoolReady bool-poll (BoolTask.Waiting true))
              (#await #bool BoolTask BoolPoll.BoolPending BoolPoll.BoolReady bool-poll (BoolTask.Waiting true)))
              (#set iterations (#u64::add-wrap iterations 1u64))
              (#break))
            (#return iterations))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-first) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task after-first) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-second) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task after-second) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 1);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_condition_keeps_global_names_out_of_frame_captures() {
    let source = "#const fallback #bool false
#enum ChildTask () ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while
              (#if (#bool::and
                  (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64))
                  (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 0u64)))
                true
                fallback)
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-frame) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-frame) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task second-frame) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    let runtime = source.split_once("#generate #async-fn").unwrap().0;
    let parsed =
        lim::parse_program(&ordinary_generated(&format!("{runtime}\n{generated}"))).unwrap();
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
        .replace("(ChildPoll.ChildReady true)", "(ChildPoll.ChildReady false)")
        .replace(
            "(#let-else (Work::Poll.Pending second-frame) Work::Poll second (#unreachable))",
            "",
        )
        .replace(
            "(#let third Work::Poll (#call Work::poll ((task second-frame) (waker (#borrow waker)))))",
            "(#let third Work::Poll second)",
        );
    build_and_run_graph(&fallback, 42);
    let static_fallback = fallback
        .replace(
            "#const fallback #bool false",
            "#static fallback #bool false",
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
            "#const fallback #bool false",
            "#const unrelated #bool false",
        )
        .replace("              fallback)", "              missing_global)");
    let error = graph_compile_error(&invalid_source, "async-unresolved-global-read");
    assert!(
        error.message.contains("unknown variable or enum variant"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("unresolved names must retain their source span");
    assert_eq!(&invalid_source[span.start..span.end], "missing_global");
}

#[test]
fn awaited_while_condition_preserves_terminal_break_and_continue() {
    let source = "#enum ConditionTask () ((ConditionTask.Waiting #u64))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.Waiting value)
              (#if (#u64::eq value 0u64)
                (ConditionPoll.ConditionPending (ConditionTask.Waiting 1u64))
                (ConditionPoll.ConditionReady true)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.Waiting iteration))
              (#set iteration (#u64::add-wrap iteration 1u64))
              (#match iteration
                (#case 2u64 (#break))
                (#case _ (#continue))))
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let result Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let value #u64 (#match result
            (#case (Work::Poll.Ready ready) ready)
            (#case (Work::Poll.Pending pending-again) (#block (#forget pending-again) 0u64))))
          (#forget waker)
          (#return (#if (#u64::eq value 2u64) 42u64 0u64))\n  );\n}\n";
    build_and_run(source, 42);
}

#[test]
fn awaited_while_condition_and_body_resume_in_source_order() {
    let source = "#enum ConditionTask (#linear) (ConditionTask.ConditionWaiting ConditionTask.ConditionResuming)

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case ConditionTask.ConditionWaiting (ConditionPoll.ConditionPending ConditionTask.ConditionResuming))
            (#case ConditionTask.ConditionResuming (ConditionPoll.ConditionReady true))))
  );
}
#enum BodyTask (#linear) ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting value) (BodyPoll.BodyPending (BodyTask.BodyResuming value)))
            (#case (BodyTask.BodyResuming value) (BodyPoll.BodyReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input #u64)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll ConditionTask.ConditionWaiting)
              (#let value #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting input)))
              (#assert (#u64::eq value input))
              (#break))
            (#return input))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((input 42u64)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending body-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task body-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");

    let conditional_source = source.replace(
        "(#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting input))",
        "(#if true\n                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting input))\n                42u64)",
    );
    let generated = build_and_run_graph(&conditional_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let for_source = source
        .replace(
            "#while (#await ConditionTask",
            "#for () (#await ConditionTask",
        )
        .replace(
            "condition-poll ConditionTask.ConditionWaiting)\n              (#let value",
            "condition-poll ConditionTask.ConditionWaiting) ()\n            (#let value",
        );
    let generated = build_and_run_graph(&for_source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn awaited_false_while_condition_does_not_poll_the_body_task() {
    let source = "#enum ConditionTask () (ConditionTask.ConditionStart)
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (ConditionPoll.ConditionReady false))
  );
}
#enum BodyTask () (BodyTask.BodyStart)
#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#unreachable))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll ConditionTask.ConditionStart)
              (#let value #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll BodyTask.BodyStart))
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let value #u64
            (#match result
              (#case (Work::Poll.Ready ready) ready)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    build_and_run(source, 42);

    let for_source = source
        .replace(
            "#while (#await ConditionTask",
            "#for () (#await ConditionTask",
        )
        .replace(
            "condition-poll ConditionTask.ConditionStart)\n              (#let value",
            "condition-poll ConditionTask.ConditionStart) ()\n            (#let value",
        );
    build_and_run(&for_source, 42);
}

#[test]
fn awaited_while_body_rejects_unconsumed_linear_parameter_on_exit() {
    let source = "#struct Resource (#linear) ((value #u64))

#enum ConditionTask (#linear) (ConditionTask.ConditionWaiting ConditionTask.ConditionResuming)

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case ConditionTask.ConditionWaiting (ConditionPoll.ConditionPending ConditionTask.ConditionResuming))
            (#case ConditionTask.ConditionResuming (ConditionPoll.ConditionReady true))))
  );
}
#enum BodyTask (#linear) ((BodyTask.BodyWaiting Resource))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting resource) (BodyPoll.BodyPending (BodyTask.BodyWaiting resource)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((resource Resource)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll ConditionTask.ConditionWaiting)
              (#let value #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting resource)))
              (#break))
            (#return 42u64))))\n";
    let error = graph_compile_error(source, "async-while-noncopy-capture");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(error.message.contains("resource"), "{error:?}");
    assert!(
        error.span.is_some(),
        "linear parameter error must retain source location: {error:?}"
    );
}

#[test]
fn async_while_body_can_return_after_awaited_condition() {
    let source = "#enum Child (#linear) ((Child.Waiting #bool) (Child.Resuming #bool))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting decision) (ChildPoll.ChildPending (Child.Resuming decision)))
            (#case (Child.Resuming decision) (ChildPoll.ChildReady decision))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting decision))
              (#return 7u64))
            (#return 0u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll (#call Work::poll ((task true-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-second (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-pending) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll (#call Work::poll ((task false-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-second (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    let generated = build_and_run_graph(source, 7);
    assert_single_poll(&generated, "Work::poll");

    let explicitly_typed = source.replace("#while (#await Child", "#while (#await #bool Child");
    assert_ne!(explicitly_typed, source);
    build_and_run_graph(&explicitly_typed, 7);

    let wrong_result_type = source.replace("#while (#await Child", "#while (#await #u64 Child");
    let error = graph_compile_error(&wrong_result_type, "async-while-condition-result-type");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error
            .message
            .contains("#await result type does not match its Ready payload"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("explicit await type must retain its source span");
    assert_eq!(&wrong_result_type[span.start..span.end], "#u64");
}

#[test]
fn async_while_body_returns_after_a_composed_awaited_condition() {
    let source = "#enum Child (#linear) ((Child.Waiting #bool) (Child.Resuming #bool))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))
#enum TailTask (#linear) ((TailTask.TailWaiting #u64) (TailTask.TailResuming #u64))

#enum TailPoll () ((TailPoll.TailPending TailTask) (TailPoll.TailReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting decision) (ChildPoll.ChildPending (Child.Resuming decision)))
            (#case (Child.Resuming decision) (ChildPoll.ChildReady decision))))
  );
}
#fn tail-poll {
  #params = ((task TailTask) (waker (#ref #u64)));
  #returns = TailPoll;
  #body = (
          (#return (#match task
            (#case (TailTask.TailWaiting value) (TailPoll.TailPending (TailTask.TailResuming value)))
            (#case (TailTask.TailResuming value) (TailPoll.TailReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#if decision
                      (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting true))
                      false)
              (#return 7u64))
            (#let fallback #u64
              (#await #u64 TailTask TailPoll.TailPending TailPoll.TailReady tail-poll (TailTask.TailWaiting 3u64)))
            (#return fallback))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll (#call Work::poll ((task true-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-second (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-pending) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll (#call Work::poll ((task false-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-second (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_fall_through_to_another_iteration() {
    let source = "#enum Child (#linear) ((Child.Waiting #bool) (Child.Resuming #bool))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting decision) (ChildPoll.ChildPending (Child.Resuming decision)))
            (#case (Child.Resuming decision) (ChildPoll.ChildReady decision))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#let-mut first #bool true)
            (#while (#if decision
                      (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting true))
                      false)
              (#if first
                (#block (#set first false) ())
                (#return 7u64)))
            (#let fallback #u64 3u64)
            (#return fallback))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll (#call Work::poll ((task true-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending-again) Work::Poll true-second (#unreachable))
          (#let true-third Work::Poll (#call Work::poll ((task true-pending-again) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-third (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-first (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_skip_a_direct_awaited_tail() {
    let source = "#enum Child (#linear) ((Child.Waiting #bool) (Child.Resuming #bool))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))
#enum TailTask (#linear) ((TailTask.TailWaiting #u64) (TailTask.TailResuming #u64))

#enum TailPoll () ((TailPoll.TailPending TailTask) (TailPoll.TailReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting decision) (ChildPoll.ChildPending (Child.Resuming decision)))
            (#case (Child.Resuming decision) (ChildPoll.ChildReady decision))))
  );
}
#fn tail-poll {
  #params = ((task TailTask) (waker (#ref #u64)));
  #returns = TailPoll;
  #body = (
          (#return (#match task
            (#case (TailTask.TailWaiting value) (TailPoll.TailPending (TailTask.TailResuming value)))
            (#case (TailTask.TailResuming value) (TailPoll.TailReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#let-mut first #bool true)
            (#while (#if decision
                      (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting true))
                      false)
            (#if first
                (#block (#set first false) ())
                (#return 7u64)))
            (#return (#await #u64 TailTask TailPoll.TailPending TailPoll.TailReady tail-poll
              (TailTask.TailWaiting 3u64))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll (#call Work::poll ((task true-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending-again) Work::Poll true-second (#unreachable))
          (#let true-third Work::Poll (#call Work::poll ((task true-pending-again) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-third (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-pending) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll (#call Work::poll ((task false-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-second (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    build_and_run(source, 10);
}

#[test]
fn async_while_conditional_return_can_suspend_post_loop_continuation() {
    let source = "#enum Child (#linear) ((Child.Waiting #bool) (Child.Resuming #bool))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #bool))
#enum TailTask (#linear) ((TailTask.TailWaiting #u64) (TailTask.TailResuming #u64))

#enum TailPoll () ((TailPoll.TailPending TailTask) (TailPoll.TailReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting decision) (ChildPoll.ChildPending (Child.Resuming decision)))
            (#case (Child.Resuming decision) (ChildPoll.ChildReady decision))))
  );
}
#fn tail-poll {
  #params = ((task TailTask) (waker (#ref #u64)));
  #returns = TailPoll;
  #body = (
          (#return (#match task
            (#case (TailTask.TailWaiting value) (TailPoll.TailPending (TailTask.TailResuming value)))
            (#case (TailTask.TailResuming value) (TailPoll.TailReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#let-mut first #bool true)
            (#while (#if decision
                      (#await #bool Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting true))
                      false)
              (#if first
                (#block (#set first false) ())
                (#return 7u64)))
            (#let fallback #u64
              (#await #u64 TailTask TailPoll.TailPending TailPoll.TailReady tail-poll (TailTask.TailWaiting 3u64)))
            (#return fallback))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll (#call Work::poll ((task true-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending-again) Work::Poll true-second (#unreachable))
          (#let true-third Work::Poll (#call Work::poll ((task true-pending-again) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-third (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-pending) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll (#call Work::poll ((task false-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-second (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    build_and_run(source, 10);
}

#[test]
fn async_while_early_return_can_skip_a_nested_awaited_tail() {
    let source = "#enum ConditionTask (#linear) ((ConditionTask.Waiting #bool) (ConditionTask.Resuming #bool))

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#enum TailTask (#linear) ((TailTask.TailWaiting #u64) (TailTask.TailResuming #u64))

#enum TailPoll () ((TailPoll.TailPending TailTask) (TailPoll.TailReady #u64))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.Waiting decision) (ConditionPoll.ConditionPending (ConditionTask.Resuming decision)))
            (#case (ConditionTask.Resuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#fn tail-poll {
  #params = ((task TailTask) (waker (#ref #u64)));
  #returns = TailPoll;
  #body = (
          (#return (#match task
            (#case (TailTask.TailWaiting value) (TailPoll.TailPending (TailTask.TailResuming value)))
            (#case (TailTask.TailResuming value) (TailPoll.TailReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.Waiting decision))
              (#return 7u64))
            (#return (#u64::add-wrap
              (#await #u64 TailTask TailPoll.TailPending TailPoll.TailReady tail-poll (TailTask.TailWaiting 3u64))
              2u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll (#call Work::poll ((task true-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-second (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-pending) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll (#call Work::poll ((task false-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-tail-pending) Work::Poll false-second (#unreachable))
          (#let false-third Work::Poll (#call Work::poll ((task false-tail-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-third (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    build_and_run(source, 12);
}

#[test]
fn async_while_early_return_can_skip_a_direct_awaited_tail() {
    let source = "#enum ConditionTask (#linear) ((ConditionTask.Waiting #bool) (ConditionTask.Resuming #bool))

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#enum TailTask (#linear) ((TailTask.TailWaiting #u64) (TailTask.TailResuming #u64))

#enum TailPoll () ((TailPoll.TailPending TailTask) (TailPoll.TailReady #u64))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.Waiting decision) (ConditionPoll.ConditionPending (ConditionTask.Resuming decision)))
            (#case (ConditionTask.Resuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#fn tail-poll {
  #params = ((task TailTask) (waker (#ref #u64)));
  #returns = TailPoll;
  #body = (
          (#return (#match task
            (#case (TailTask.TailWaiting value) (TailPoll.TailPending (TailTask.TailResuming value)))
            (#case (TailTask.TailResuming value) (TailPoll.TailReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.Waiting decision))
              (#return 7u64))
            (#return (#await #u64 TailTask TailPoll.TailPending TailPoll.TailReady tail-poll
              (TailTask.TailWaiting 3u64))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-pending) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll (#call Work::poll ((task true-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-second (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-pending) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll (#call Work::poll ((task false-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-tail-pending) Work::Poll false-second (#unreachable))
          (#let false-third Work::Poll (#call Work::poll ((task false-tail-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-third (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    build_and_run(source, 10);
}

#[test]
fn async_while_body_can_return_after_body_await() {
    let source =
        "#enum ConditionTask (#linear) ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting decision)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))
            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#enum BodyTask (#linear) ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting value) (BodyPoll.BodyPending (BodyTask.BodyResuming value)))
            (#case (BodyTask.BodyResuming value) (BodyPoll.BodyReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.ConditionWaiting decision))
              (#let body-value #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting 13u64)))
              (#return body-value))
            (#return 5u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-after-condition) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll
            (#call Work::poll ((task true-after-condition) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-after-body-start) Work::Poll true-second (#unreachable))
          (#let true-third Work::Poll
            (#call Work::poll ((task true-after-body-start) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-third (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-after-condition) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll
            (#call Work::poll ((task false-after-condition) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-second (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    let generated = build_and_run_graph(source, 18);
    assert_single_poll(&generated, "Work::poll");

    let linear_source = source
        .replace(
            "#enum ConditionTask (#linear)",
            "#struct Payload (#linear) ((value #u64))\n      \n#enum ConditionTask (#linear)",
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
            "(#return (#u64::add-wrap true-result false-result))",
            "(#let true-value #u64 (#get true-result value))
  (#let false-value #u64 (#get false-result value))
  (#forget true-result)
  (#forget false-result)
  (#return (#u64::add-wrap true-value false-value))",
        );
    let generated = build_and_run_graph(&linear_source, 18);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_body_transfers_a_mutated_linear_capture_after_suspension() {
    let source = "#alias lim-gen-async = \"{}/library/tasks.lim::#async\"\n#alias lim-gen-async-wake = \"{}/library/tasks.lim::#async-wake\"\n#alias lim-gen-executor = \"{}/library/tasks.lim::#executor\"\n#alias lim-gen-task = \"{}/library/tasks.lim::#task\"\n#alias lim-gen-task-cancel = \"{}/library/tasks.lim::#task-cancel\"\n#alias lim-gen-threaded-executor = \"{}/library/tasks.lim::#threaded-executor\"\n#alias lim-gen-wake-executor = \"{}/library/tasks.lim::#wake-executor\"\n#alias async-complete = \"{}/library/tasks.lim::async-complete\"\n#alias async-poll-case = \"{}/library/tasks.lim::async-poll-case\"\n#alias async-state = \"{}/library/tasks.lim::async-state\"\n#alias async-wake-poll-case = \"{}/library/tasks.lim::async-wake-poll-case\"\n#alias executor-field = \"{}/library/tasks.lim::executor-field\"\n#alias executor-initialize = \"{}/library/tasks.lim::executor-initialize\"\n#alias executor-name = \"{}/library/tasks.lim::executor-name\"\n#alias executor-parameter = \"{}/library/tasks.lim::executor-parameter\"\n#alias executor-poll = \"{}/library/tasks.lim::executor-poll\"\n#alias executor-result = \"{}/library/tasks.lim::executor-result\"\n#alias task-cancel-case = \"{}/library/tasks.lim::task-cancel-case\"\n#alias task-eighth = \"{}/library/tasks.lim::task-eighth\"\n#alias task-fifth = \"{}/library/tasks.lim::task-fifth\"\n#alias task-fourth = \"{}/library/tasks.lim::task-fourth\"\n#alias task-second = \"{}/library/tasks.lim::task-second\"\n#alias task-seventh = \"{}/library/tasks.lim::task-seventh\"\n#alias task-sixth = \"{}/library/tasks.lim::task-sixth\"\n#alias task-third = \"{}/library/tasks.lim::task-third\"\n#alias wake-executor-cancel-call = \"{}/library/tasks.lim::wake-executor-cancel-call\"\n#alias wake-executor-field = \"{}/library/tasks.lim::wake-executor-field\"\n#alias wake-executor-generate = \"{}/library/tasks.lim::wake-executor-generate\"\n#alias wake-executor-initialize = \"{}/library/tasks.lim::wake-executor-initialize\"\n#alias wake-executor-poll = \"{}/library/tasks.lim::wake-executor-poll\"\n#alias wake-executor-result = \"{}/library/tasks.lim::wake-executor-result\"\n#alias wake-executor-result-field = \"{}/library/tasks.lim::wake-executor-result-field\"\n#alias wake-executor-slot = \"{}/library/tasks.lim::wake-executor-slot\"\n#alias wake-executor-slots-valid = \"{}/library/tasks.lim::wake-executor-slots-valid\"\n#alias wake-executor-state-name = \"{}/library/tasks.lim::wake-executor-state-name\"\n#alias wake-executor-task-parameter = \"{}/library/tasks.lim::wake-executor-task-parameter\"\n#alias wake-executor-task-parameter-form = \"{}/library/tasks.lim::wake-executor-task-parameter-form\"\n#alias wake-executor-wait-result = \"{}/library/tasks.lim::wake-executor-wait-result\"\n#alias wake-executor-waker-parameter = \"{}/library/tasks.lim::wake-executor-waker-parameter\"\n#alias wake-executor-waker-parameter-form = \"{}/library/tasks.lim::wake-executor-waker-parameter-form\"\n#struct Payload (#linear) ((value #u64))\n\n#enum ConditionTask () ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))\n#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))\n#fn condition-poll {\n  #params = ((task ConditionTask) (waker (#ref #u64)));\n  #returns = ConditionPoll;\n  #body = (\n          (#return (#match task\n            (#case (ConditionTask.ConditionWaiting decision)\n              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))\n            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))\n  );\n}\n#enum BodyTask () ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))\n#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))\n#fn body-poll {\n  #params = ((task BodyTask) (waker (#ref #u64)));\n  #returns = BodyPoll;\n  #body = (\n          (#return (#match task\n            (#case (BodyTask.BodyWaiting value) (BodyPoll.BodyPending (BodyTask.BodyResuming value)))\n            (#case (BodyTask.BodyResuming value) (BodyPoll.BodyReady value))))\n  );\n}\n#generate #async-fn ((protocol work-await) (waker #u64)\n          (cancel (cancel-frame ((payload cancel-payload))))\n          (function\n          (#fn work ((#mut decision #bool)) Payload\n            (#let-mut payload Payload\n              (#struct-literal Payload ((value 1u64))))\n            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady\n                      condition-poll (ConditionTask.ConditionWaiting decision))\n              (#let first #u64\n                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll\n                  (BodyTask.BodyWaiting 1u64)))\n              (#let second #u64\n              (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting first)))\n              (#let replacement Payload\n                (#struct-literal Payload ((value (#u64::add-wrap second 1u64)))))\n              (#forget payload)\n              (#set payload replacement)\n              (#set decision false))\n            (#return payload))))\n#fn cancel-payload {\n  #params = ((value Payload));\n  #returns = ();\n  #body = (\n          (#assert (#u64::eq (#get value value) 1u64))\n          (#forget value) (#return ())\n  );\n}\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n          (#let waker #u64 0u64)\n          (#let first Work::Poll (#call Work::poll ((task (#call work ((decision true)))) (waker (#borrow waker)))))\n          (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))\n          (#let second Work::Poll (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))\n          (#let-else (Work::Poll.Pending first-body-pending) Work::Poll second (#unreachable))\n          (#let third Work::Poll (#call Work::poll ((task first-body-pending) (waker (#borrow waker)))))\n          (#let-else (Work::Poll.Pending second-body-pending) Work::Poll third (#unreachable))\n          (#let fourth Work::Poll (#call Work::poll ((task second-body-pending) (waker (#borrow waker)))))\n          (#let-else (Work::Poll.Pending final-condition-pending) Work::Poll fourth (#unreachable))\n          (#let fifth Work::Poll (#call Work::poll ((task final-condition-pending) (waker (#borrow waker)))))\n          (#let-else (Work::Poll.Ready payload) Work::Poll fifth (#unreachable))\n          (#let result #u64 (#get payload value))\n          (#forget payload)\n          (#let cancel-first Work::Poll\n            (#call Work::poll ((task (#call work ((decision true)))) (waker (#borrow waker)))))\n          (#let-else (Work::Poll.Pending cancel-pending-first) Work::Poll cancel-first (#unreachable))\n          (#let cancel-second Work::Poll\n            (#call Work::poll ((task cancel-pending-first) (waker (#borrow waker)))))\n          (#let-else (Work::Poll.Pending cancel-pending-second) Work::Poll cancel-second (#unreachable))\n          (#call cancel-frame ((task (#call Work::Poll::cleanup ((task cancel-pending-second))))))\n          (#forget waker)\n          (#return result)\n  );\n}\n"
        .replace("{}", env!("CARGO_MANIFEST_DIR"));
    let generated = build_and_run_graph(&source, 2);
    assert!(generated.contains("Payload"), "{generated}");

    let returning_source = source.replace("(#set decision false)", "(#return payload)");
    let (prefix, _) = returning_source
        .split_once("#fn main")
        .expect("main follows the async declaration and cancellation helpers");
    let returning_source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let task Work::Task (#call work ((decision true))))
            (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending after-condition) Work::Poll first (#unreachable))
            (#let second Work::Poll (#call Work::poll ((task after-condition) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending after-first) Work::Poll second (#unreachable))
            (#let third Work::Poll (#call Work::poll ((task after-first) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending after-second) Work::Poll third (#unreachable))
            (#let fourth Work::Poll (#call Work::poll ((task after-second) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Ready payload) Work::Poll fourth (#unreachable))
            (#let result #u64 (#get payload value))
            (#forget payload)
            (#forget waker)
            (#return (#if (#u64::eq result 2u64) 42u64 0u64))
  );\n}}\n"
    );
    build_and_run_graph(&returning_source, 42);

    let (prefix, _) = source.split_once("#fn main").unwrap();
    for (polls, expected) in [
        (0, None),
        (1, Some(1)),
        (2, Some(1)),
        (3, Some(1)),
        (4, Some(2)),
    ] {
        let assertion = expected.map_or_else(
            || "(#assert false)".into(),
            |value| format!("(#assert (#u64::eq (#get value value) {value}u64))"),
        );
        let prefix = prefix.replace("(#assert (#u64::eq (#get value value) 1u64))", &assertion);
        let mut canceled = format!(
            "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let waker #u64 0u64)
              (#let state-0 Work::Task (#call work ((decision true))))\n"
        );
        for index in 0..polls {
            canceled.push_str(&format!(
                "
              (#let outcome-{index} Work::Poll
                (#call Work::poll ((task state-{index}) (waker (#borrow waker)))))
              (#let-else (Work::Poll.Pending state-{}) Work::Poll outcome-{index} (#unreachable))",
                index + 1
            ));
        }
        canceled.push_str(&format!(
            "
            (#call cancel-frame ((task (#call Work::Poll::cleanup ((task state-{polls}))))))
            (#forget waker) (#return 42u64)\n  );\n}}"
        ));
        build_and_run_graph(&canceled, 42);
    }
}

#[test]
fn async_suspending_while_body_can_return_after_setup() {
    let source = "#enum ConditionTask () ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting decision)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))
            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#enum BodyTask () ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))
#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting value) (BodyPoll.BodyPending (BodyTask.BodyResuming value)))
            (#case (BodyTask.BodyResuming value) (BodyPoll.BodyReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.ConditionWaiting decision))
              (#let setup #u64 13u64)
              (#let value #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting setup)))
              (#return value))
            (#return 5u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-after-condition) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll
            (#call Work::poll ((task true-after-condition) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-after-body) Work::Poll true-second (#unreachable))
          (#let true-third Work::Poll
            (#call Work::poll ((task true-after-body) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-third (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-after-condition) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll
            (#call Work::poll ((task false-after-condition) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-second (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    let generated = build_and_run_graph(source, 18);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_suspending_while_body_can_return_after_multiple_awaits() {
    let source = "#enum ConditionTask () ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting decision)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))
            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#enum BodyTask () ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))
#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting value) (BodyPoll.BodyPending (BodyTask.BodyResuming value)))
            (#case (BodyTask.BodyResuming value) (BodyPoll.BodyReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.ConditionWaiting decision))
              (#let setup #u64 13u64)
              (#let first #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting setup)))
              (#let second #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll
                  (BodyTask.BodyWaiting (#u64::add-wrap first 1u64))))
              (#return (#u64::add-wrap first second)))
            (#return 5u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let true-task Work::Task (#call work ((decision true))))
          (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-after-condition) Work::Poll true-first (#unreachable))
          (#let true-second Work::Poll
            (#call Work::poll ((task true-after-condition) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-after-first) Work::Poll true-second (#unreachable))
          (#let true-third Work::Poll
            (#call Work::poll ((task true-after-first) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending true-after-second) Work::Poll true-third (#unreachable))
          (#let true-fourth Work::Poll
            (#call Work::poll ((task true-after-second) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready true-result) Work::Poll true-fourth (#unreachable))
          (#let false-task Work::Task (#call work ((decision false))))
          (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-after-condition) Work::Poll false-first (#unreachable))
          (#let false-second Work::Poll
            (#call Work::poll ((task false-after-condition) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-second (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap true-result false-result))\n  );\n}\n";
    let generated = build_and_run_graph(source, 32);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_suspending_while_body_return_reaches_enclosing_function() {
    let source = "#enum ConditionTask () ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting decision)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))
            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#enum BodyTask () ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))
#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting value) (BodyPoll.BodyPending (BodyTask.BodyResuming value)))
            (#case (BodyTask.BodyResuming value) (BodyPoll.BodyReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.ConditionWaiting decision))
              (#let first #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting 20u64)))
              (#let second #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll
                  (BodyTask.BodyWaiting (#u64::add-wrap first 7u64))))
              (#return (#u64::add-wrap first second)))
            (#return 5u64))))
#fn run {
  #params = ((decision #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((decision decision))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#let-else (Work::Poll.Pending after-condition) Work::Poll first (#unreachable))
          (#return (#if decision
            (#block
              (#let second Work::Poll (#call Work::poll ((task after-condition) (waker waker))))
              (#let-else (Work::Poll.Pending after-first-body) Work::Poll second (#unreachable))
              (#let third Work::Poll (#call Work::poll ((task after-first-body) (waker waker))))
              (#let-else (Work::Poll.Pending after-second-body) Work::Poll third (#unreachable))
              (#let fourth Work::Poll (#call Work::poll ((task after-second-body) (waker waker))))
              (#let-else (Work::Poll.Ready result) Work::Poll fourth (#unreachable))
              result)
            (#block
              (#let second Work::Poll (#call Work::poll ((task after-condition) (waker waker))))
              (#let-else (Work::Poll.Ready result) Work::Poll second (#unreachable))
              result)))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let returned #u64 (#call run ((decision true) (waker (#borrow waker)))))
          (#let skipped #u64 (#call run ((decision false) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap returned skipped))\n  );\n}\n";
    build_and_run(source, 52);
}

#[test]
fn async_awaited_while_body_returns_from_both_if_branches() {
    let source = "#enum ConditionTask () ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting decision)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))
            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool) (pick #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.ConditionWaiting decision))
              (#if pick (#return 13u64) (#return 17u64)))
            (#return 5u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first-task Work::Task (#call work ((decision true) (pick true))))
          (#let first-poll Work::Poll (#call Work::poll ((task first-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-pending) Work::Poll first-poll (#unreachable))
          (#let first-ready Work::Poll (#call Work::poll ((task first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready first-result) Work::Poll first-ready (#unreachable))
          (#let second-task Work::Task (#call work ((decision true) (pick false))))
          (#let second-poll Work::Poll (#call Work::poll ((task second-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-pending) Work::Poll second-poll (#unreachable))
          (#let second-ready Work::Poll (#call Work::poll ((task second-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready second-result) Work::Poll second-ready (#unreachable))
          (#let false-task Work::Task (#call work ((decision false) (pick true))))
          (#let false-poll Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending false-pending) Work::Poll false-poll (#unreachable))
          (#let false-ready Work::Poll (#call Work::poll ((task false-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready false-result) Work::Poll false-ready (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap
            (#u64::add-wrap first-result second-result) false-result))\n  );\n}\n";
    build_and_run(source, 35);
}

#[test]
fn async_awaited_while_body_returns_from_match_arms() {
    let source = "#enum ConditionTask () ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting decision)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))
            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool) (pick #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.ConditionWaiting decision))
              (#block
                (#let offset #u64 1u64)
                (#match pick
                  (#case true (#return (#u64::add-wrap 12u64 offset)))
                  (#case false (#return (#u64::add-wrap 16u64 offset))))))
            (#return 5u64))))
#fn drive {
  #params = ((decision #bool) (pick #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((decision decision) (pick pick))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker waker))))
          (#return (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending still-pending)
              (#block (#forget still-pending) 0u64))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first-result #u64
            (#call drive ((decision true) (pick true) (waker (#borrow waker)))))
          (#let second-result #u64
            (#call drive ((decision true) (pick false) (waker (#borrow waker)))))
          (#let false-result #u64
            (#call drive ((decision false) (pick true) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap
            (#u64::add-wrap first-result second-result) false-result))\n  );\n}\n";
    build_and_run(source, 35);
}

#[test]
fn async_awaited_while_return_branch_and_break_branch_diverge_correctly() {
    let source = "#enum ConditionTask () ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting decision)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming decision)))
            (#case (ConditionTask.ConditionResuming decision) (ConditionPoll.ConditionReady decision))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((decision #bool) (leave-body #bool)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.ConditionWaiting decision))
              (#block
                (#let return-value #u64 13u64)
                (#if leave-body (#return return-value) (#break))))
            (#return 5u64))))
#fn drive {
  #params = ((decision #bool) (leave-body #bool) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((decision decision) (leave-body leave-body))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker waker))))
          (#return (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending still-pending)
              (#block (#forget still-pending) 0u64))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let returned #u64
            (#call drive ((decision true) (leave-body true) (waker (#borrow waker)))))
          (#let broken #u64
            (#call drive ((decision true) (leave-body false) (waker (#borrow waker)))))
          (#let condition-false #u64
            (#call drive ((decision false) (leave-body true) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap (#u64::add-wrap returned broken) condition-false))\n  );\n}\n";
    build_and_run(source, 23);
}

#[test]
fn async_awaited_while_return_branch_and_continue_branch_resume_correctly() {
    let source = "#enum ConditionTask () ((ConditionTask.Waiting #u64) (ConditionTask.Resuming #u64))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.Waiting iteration) (ConditionPoll.ConditionPending (ConditionTask.Resuming iteration)))
            (#case (ConditionTask.Resuming iteration)
              (ConditionPoll.ConditionReady (#u64::eq iteration 0u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((should-return #bool)) #u64
            (#let-mut iteration #u64 0u64)
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                      condition-poll (ConditionTask.Waiting iteration))
              (#if should-return
                (#return 13u64)
                (#block
                  (#set iteration 1u64)
                  (#continue))))
            (#return 5u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let return-task Work::Task (#call work ((should-return true))))
          (#let first Work::Poll (#call Work::poll ((task return-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-return-first) Work::Poll first (#unreachable))
          (#let return-ready Work::Poll
            (#call Work::poll ((task after-return-first) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready returned) Work::Poll return-ready (#unreachable))
          (#let continue-task Work::Task (#call work ((should-return false))))
          (#let continue-first Work::Poll
            (#call Work::poll ((task continue-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-continue-first) Work::Poll continue-first (#unreachable))
          (#let continue-second Work::Poll
            (#call Work::poll ((task after-continue-first) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-continue-second) Work::Poll continue-second (#unreachable))
          (#let continue-ready Work::Poll
            (#call Work::poll ((task after-continue-second) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready continued) Work::Poll continue-ready (#unreachable))
          (#forget waker)
          (#return (#u64::add-wrap returned continued))\n  );\n}\n";
    build_and_run_graph(source, 18);

    let linear_source = source
        .replace(
            "#enum ConditionTask ()",
            "#struct Payload (#linear) ((value #u64))\n      \n#enum ConditionTask ()",
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
            "(#return (#u64::add-wrap returned continued))",
            "(#let returned-value #u64 (#get returned value))
  (#let continued-value #u64 (#get continued value))
  (#forget returned)
  (#forget continued)
  (#return (#u64::add-wrap returned-value continued-value))",
        );
    build_and_run_graph(&linear_source, 18);
    let reused = linear_source.replace(
        "(#forget returned)",
        "(#let duplicate Payload returned) (#forget returned) (#forget duplicate)",
    );
    assert_ne!(reused, linear_source);
    let error = graph_compile_error(&reused, "linear-while-return-reused");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(error.span.is_some());
}

#[test]
fn async_while_let_awaits_each_scrutinee_until_the_pattern_stops_matching() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ChildTask () ((ChildTask.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady Maybe))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting stage)
              (#if (#u64::eq stage 0u64)
                (ChildPoll.ChildPending (ChildTask.Waiting 1u64))
                (#if (#u64::eq stage 1u64)
                  (ChildPoll.ChildReady (Maybe.Some 10u64))
                  (ChildPoll.ChildReady Maybe.None))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#while-let (Maybe.Some payload)
              (#await Maybe ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                (ChildTask.Waiting (#if (#u64::eq iteration 0u64) 0u64 2u64)))
              (#set iteration payload))
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-frame) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-frame) (waker (#borrow waker)))))
          (#let value #u64 (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending-frame) (#block (#forget pending-frame) 0u64))))
          (#forget waker)
          (#return (#if (#u64::eq value 10u64) 42u64 0u64))\n  );\n}\n";
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
#enum Value () ((Value.Some #u64) Value.None)
#fn next-value {
  #params = ((counter (#ref-mut #u64)));
  #returns = Value;
  #body = (
          (#let index #u64 (#deref counter))
          (#deref-set counter (#u64::add-wrap index 1u64))
          (#return (#match index
            (#case 0u64 (Value.Some 20u64))
            (#case 1u64 (Value.Some 22u64))
            (#case _ Value.None)))
  );
}
#enum BodyTask (#linear) ((BodyTask.Start #u64) (BodyTask.Resume #u64))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.Start value) (BodyPoll.BodyPending (BodyTask.Resume value)))
            (#case (BodyTask.Resume value) (BodyPoll.BodyReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut counter #u64 0u64)
            (#let-mut total #u64 0u64)
            (#while-let (Value.Some amount) (#call next-value ((counter (#borrow-mut counter))))
              (#let result #u64 (#await BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.Start amount)))
              (#set total (#u64::add-wrap total result)))
            (#assert (#u64::eq counter 3u64))
            (#return total))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-task) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task second-task) (waker (#borrow waker)))))
          (#return (#match third
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#;
    build_and_run(source, 42);
    build_and_run(include_str!("../examples/async_while_let_body.lim"), 42);
    let prefix = source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap().0;
    let never_matches = format!(
        r#"{}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let value #u64 (#match first
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#assert (#u64::eq value 0u64))
          (#return 42u64)
  );
}}
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
#enum Value () ((Value.Some (#ref #u64)) Value.None)
#enum BodyTask (#linear) (BodyTask.Start BodyTask.Resume)

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady ()))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case BodyTask.Start (BodyPoll.BodyPending BodyTask.Resume))
            (#case BodyTask.Resume (BodyPoll.BodyReady ()))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((owner (#ref #u64))) #u64
            (#let current Value (Value.Some owner))
            (#let-mut result #u64 0u64)
            (#while-let (Value.Some reference) current
              (#let ready () (#await () BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll BodyTask.Start))
              (#set result (#deref reference))
              (#break))
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 42u64)
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((owner (#borrow owner))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#return (#match second
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#;
    build_and_run(source, 42);
    let invalid = source.replace(
        "(#let second Work::Poll",
        "(#set owner 43u64) (#let second Work::Poll",
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
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 42u64)
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((owner (#borrow owner))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#forget task)
          (#set owner 43u64)
          (#return owner)
  );
}}
    "#,
        source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap().0
    );
    build_and_run(&cancelled, 43);
}

#[test]
fn async_while_let_sequences_awaits_in_its_scrutinee_expression() {
    let source = "#enum ChildTask () ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while-let true
              (#bool::and
                (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 42u64))
                (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting 42u64)))
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-frame) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-frame) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task second-frame) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_condition_sequences_awaits_in_a_value_expression() {
    let source = "#enum ChildTask () ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for (#let-mut index #u64 0u64)
              (#bool::and
                (#u64::lt index 1u64)
                (#bool::and
                  (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting index))
                  (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting index))))
              (#set index (#u64::add-wrap index 1u64))
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-frame) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-frame) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task second-frame) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_rebuilds_a_partially_moved_struct_after_suspension() {
    let source = r#"
#struct Resource (#linear) ((value #u64))

#struct Pair () ((left Resource) (right Resource))
#enum Step (#linear) ((Step.Start #u64) (Step.Resume #u64))

#enum StepPoll () ((StepPoll.Pending Step) (StepPoll.Ready #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Start value) (StepPoll.Pending (Step.Resume value)))
            (#case (Step.Resume value) (StepPoll.Ready value))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64) (function
          (#fn work () #u64
            (#let-mut pair Pair (#struct-literal Pair
              ((left (#struct-literal Resource ((value 20u64))))
               (right (#struct-literal Resource ((value 22u64)))))))
            (#let moved Resource (#get pair left))
            (#let delta #u64 (#await #u64 Step StepPoll.Pending StepPoll.Ready step-poll (Step.Start 2u64)))
            (#let old #u64 (#get moved value))
            (#forget moved)
            (#set-field pair left (#struct-literal Resource ((value (#u64::add-wrap old delta)))))
            (#let result #u64 (#u64::add-wrap (#get (#get pair left) value) (#get (#get pair right) value)))
            (#forget pair)
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#return (#match (#call Work::poll ((task task) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#;
    let generated = build_and_run_partial_storage(source, 44);
    assert_single_poll(&generated, "Work::poll");
    let explicit = source.replace(
        "#struct Pair () ((left Resource) (right Resource))",
        "#struct Pair (#linear) ((left Resource) (right Resource))\n ",
    );
    build_and_run_partial_storage(&explicit, 44);

    let parameter = source
        .replace("(#fn work () #u64", "(#fn work ((#mut pair Pair)) #u64")
        .replace("(#let-mut pair Pair (#struct-literal Pair\n              ((left (#struct-literal Resource ((value 20u64))))\n               (right (#struct-literal Resource ((value 22u64)))))))", "")
        .replace("(#call work ())", "(#call work ((pair (#struct-literal Pair ((left (#struct-literal Resource ((value 20u64)))) (right (#struct-literal Resource ((value 22u64)))))))))");
    assert!(!parameter.contains("(#let-mut pair Pair"));
    build_and_run_partial_storage(&parameter, 44);

    let prefix = source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap().0;
    let cancelled = format!(
        r#"{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let (Work::Task::Cleanup moved right waiting) Work::Task::Cleanup
            (#call Work::Poll::cleanup ((task pending))))
          (#let-else (Work::Task::Cleanup::Moved.Full original) Work::Task::Cleanup::Moved moved (#unreachable))
          (#let-else (Work::Task::Cleanup::Pair-right.Full sibling) Work::Task::Cleanup::Pair-right right (#unreachable))
          (#forget waiting)
          (#let result #u64 (#u64::add-wrap (#get original value) (#get sibling value)))
          (#forget original) (#forget sibling)
          (#return result)
  );
}}
"#
    );
    let cleanup_source = build_and_run_partial_storage(&cancelled, 42);
    assert!(
        !cleanup_source.contains("Work::Task::Cleanup::Pair-left"),
        "a field always moved before StepPoll.Pending is not a cancellation obligation"
    );

    let explicit_cancel = cancelled
        .replace("#struct Pair () ((left Resource) (right Resource))", "#struct Pair (#linear) ((left Resource) (right Resource))\n ")
        .replace("Work::Task::Cleanup moved right waiting", "Work::Task::Cleanup moved right shell waiting")
        .replace("(#forget waiting)", "(#assert (#variant-is (#borrow shell) Work::Task::Cleanup::Pair-shell.Full)) (#forget shell) (#forget waiting)");
    build_and_run_partial_storage(&explicit_cancel, 42);

    let pinned = prefix
        .replace("#generate #async-fn ", "#generate #async-fn-pinned ")
        .replace(
            "(#let moved Resource",
            "(#let view (#ref Resource) (#borrow (#get pair right))) (#let moved Resource",
        )
        .replace("(#get (#get pair right) value)", "(#get view value)")
        .replace("(#forget pair)", "(#drop view) (#forget pair)");
    let pinned = format!(
        r#"{pinned}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut frame Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll
            ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let result #u64 (#match (#call Work::poll ((task pending) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame)
          (#return result)
  );
}}
"#
    );
    build_and_run_partial_storage(&pinned, 44);
    let cloned = source.replace(
        "(#forget pair)",
        "(#let duplicate Pair (#clone pair)) (#forget duplicate) (#forget pair)",
    );
    build_and_run_partial_storage(&cloned, 44);
    for (source, needle, replacement, expected) in [
        (
            source,
            "(#let delta #u64",
            "(#let stolen Resource (#get pair left)) (#forget stolen) (#let delta #u64",
            "more than once",
        ),
        (
            pinned.as_str(),
            "(#let delta #u64",
            "(#let overlap (#ref-mut Resource) (#borrow-mut (#get pair right))) (#drop overlap) (#let delta #u64",
            "borrow",
        ),
    ] {
        let invalid = source.replace(needle, replacement);
        let error = graph_compile_error(&invalid, "partial-storage-invalid");
        assert!(error.message.contains(expected), "{error:?}");
        assert!(error.span.is_some(), "{error:?}");
    }
}

#[test]
fn async_rebuilds_nested_partially_moved_structs() {
    let source = r#"
#struct Resource (#linear) ((value #u64))

#struct Pair () ((left Resource) (right Resource))
#struct Outer () ((inner Pair) (spare Resource))
#enum Step (#linear) ((Step.Start #u64) (Step.Resume #u64))

#enum StepPoll () ((StepPoll.Pending Step) (StepPoll.Ready #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Start value) (StepPoll.Pending (Step.Resume value)))
            (#case (Step.Resume value) (StepPoll.Ready value))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64) (function
          (#fn work () #u64
            (#let-mut owner Outer (#struct-literal Outer
              ((inner (#struct-literal Pair
                 ((left (#struct-literal Resource ((value 20u64))))
                  (right (#struct-literal Resource ((value 22u64)))))))
               (spare (#struct-literal Resource ((value 3u64)))))))
            (#let moved Resource (#get (#get owner inner) left))
            (#let delta #u64 (#await #u64 Step StepPoll.Pending StepPoll.Ready step-poll (Step.Start 2u64)))
            (#let old #u64 (#get moved value))
            (#forget moved)
            (#let sibling Resource (#get (#get owner inner) right))
            (#set-field owner inner (#struct-literal Pair
              ((left (#struct-literal Resource ((value (#u64::add-wrap old delta)))))
               (right sibling))))
            (#let cloned-inner Pair (#clone (#get owner inner)))
            (#assert (#u64::eq (#get (#get cloned-inner left) value) 22u64))
            (#forget cloned-inner)
            (#let result #u64 (#u64::add-wrap
              (#get (#get (#get owner inner) left) value)
              (#get (#get (#get owner inner) right) value)))
            (#forget owner)
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#return (#match (#call Work::poll ((task task) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#;
    let generated = build_and_run_partial_storage(source, 44);
    assert_single_poll(&generated, "Work::poll");
    let explicit = source.replace(
        "#struct Outer () ((inner Pair) (spare Resource))",
        "#struct Outer (#linear) ((inner Pair) (spare Resource))\n ",
    );
    build_and_run_partial_storage(&explicit, 44);

    let prefix = source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap().0;
    let pinned = prefix
        .replace("#generate #async-fn ", "#generate #async-fn-pinned ")
        .replace("(#let moved Resource", "(#let view (#ref Resource) (#borrow (#get (#get owner inner) right))) (#let moved Resource")
        .replace("(#let sibling Resource", "(#assert (#u64::eq (#get view value) 22u64)) (#drop view) (#let sibling Resource");
    let pinned = format!(
        r#"{pinned}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut frame Work::Frame (#call work ()))
          (#let first Work::Poll (#call Work::poll
            ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let result #u64 (#match (#call Work::poll ((task pending) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame)
          (#return result)
  );
}}
"#
    );
    build_and_run_partial_storage(&pinned, 44);

    let cancelled = format!(
        r#"{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let (Work::Task::Cleanup moved right spare waiting) Work::Task::Cleanup
            (#call Work::Poll::cleanup ((task pending))))
          (#let-else (Work::Task::Cleanup::Moved.Full original) Work::Task::Cleanup::Moved moved (#unreachable))
          (#let-else (Work::Task::Cleanup::Owner-inner-right.Full sibling) Work::Task::Cleanup::Owner-inner-right right (#unreachable))
          (#forget spare) (#forget waiting)
          (#let result #u64 (#u64::add-wrap (#get original value) (#get sibling value)))
          (#forget original) (#forget sibling)
          (#return result)
  );
}}
"#
    );
    build_and_run_partial_storage(&cancelled, 42);

    let nominal_prefix = prefix.split_once("(#let old #u64").unwrap().0.replace(
        "#struct Pair () ((left Resource) (right Resource))",
        "#struct Pair (#linear) ((left Resource) (right Resource))\n ",
    );
    let nominal_main = cancelled.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap().1
        .replace("Work::Task::Cleanup moved right spare waiting", "Work::Task::Cleanup moved right spare shell waiting")
        .replace("(#forget spare)", "(#assert (#variant-is (#borrow shell) Work::Task::Cleanup::Owner-inner-shell.Full)) (#forget shell) (#forget spare)");
    let nominal_cancel =
        format!("{nominal_prefix}(#return (#unreachable)))))\n#fn main {{\n  #params = ();\n  #returns = #u64;{nominal_main}");
    build_and_run_partial_storage(&nominal_cancel, 42);

    let parameter = source
        .replace("(#fn work () #u64", "(#fn work ((#mut owner Outer)) #u64")
        .replace("(#let-mut owner Outer (#struct-literal Outer\n              ((inner (#struct-literal Pair\n                 ((left (#struct-literal Resource ((value 20u64))))\n                  (right (#struct-literal Resource ((value 22u64)))))))\n               (spare (#struct-literal Resource ((value 3u64)))))))", "")
        .replace("(#call work ())", "(#call work ((owner (#struct-literal Outer ((inner (#struct-literal Pair ((left (#struct-literal Resource ((value 20u64)))) (right (#struct-literal Resource ((value 22u64))))))) (spare (#struct-literal Resource ((value 3u64)))))))))");
    assert!(!parameter.contains("(#let-mut owner Outer"));
    build_and_run_partial_storage(&parameter, 44);

    let deep = source
        .replace("#struct Pair () ((left Resource) (right Resource))", "#struct Box () ((resource Resource))\n#struct Pair () ((left Box) (right Resource))")
        .replace("(left (#struct-literal Resource ((value 20u64))))", "(left (#struct-literal Box ((resource (#struct-literal Resource ((value 20u64)))))))")
        .replace("(#let moved Resource (#get (#get owner inner) left))", "(#let moved Resource (#get (#get (#get owner inner) left) resource))")
        .replace("(left (#struct-literal Resource ((value (#u64::add-wrap old delta)))))", "(left (#struct-literal Box ((resource (#struct-literal Resource ((value (#u64::add-wrap old delta))))))))")
        .replace("(#get (#get (#get owner inner) left) value)", "(#get (#get (#get (#get owner inner) left) resource) value)")
        .replace("(#get (#get cloned-inner left) value)", "(#get (#get (#get cloned-inner left) resource) value)");
    assert_ne!(deep, source);
    build_and_run_partial_storage(&deep, 44);

    for (input, replacement, expected) in [
        (source, "(#let duplicate Resource (#get (#get owner inner) left)) (#forget duplicate) (#let delta #u64", "more than once"),
        (pinned.as_str(), "(#let overlap (#ref-mut Resource) (#borrow-mut (#get (#get owner inner) right))) (#drop overlap) (#let delta #u64", "borrow"),
    ] {
        let invalid = input.replace("(#let delta #u64", replacement);
        let error = graph_compile_error(&invalid, "nested-storage-invalid");
        assert!(error.message.contains(expected), "{error:?}");
        assert!(error.span.is_some(), "{error:?}");
    }
}

#[test]
fn async_clones_indexed_computed_reference_owners() {
    let source = r#"
#struct Holder (#linear) ((reference (#ref #u64)) (offset #u64))

#fn make-array {
  #params = ((owner (#ref #u64)));
  #returns = (#array Holder 2);
  #body = (
          (#return (#array-of (#array Holder 2)
            (#struct-literal Holder ((reference owner) (offset 0u64)))
            (#struct-literal Holder ((reference owner) (offset 1u64)))))
  );
}
#fn index-value {
  #params = ((calls (#ptr-mut #usize)) (result #usize));
  #returns = #usize;
  #body = (
          (#unsafe (#ptr-write calls (#usize::add-wrap (#ptr-read calls) 1usize)))
          (#return result)
  );
}
#enum Step (#linear) (Step.Start Step.Resume)

#enum StepPoll () ((StepPoll.Pending Step) (StepPoll.Ready ()))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case Step.Start (StepPoll.Pending Step.Resume)) (#case Step.Resume (StepPoll.Ready ()))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64) (function
          (#fn work ((owner (#ref #u64)) (index #usize) (calls (#ptr-mut #usize))) #u64
            (#let holder Holder (#clone (#index (#call make-array ((owner owner)))
              (#call index-value ((calls calls) (result index))))))
            (#let ready () (#await () Step StepPoll.Pending StepPoll.Ready step-poll Step.Start))
            (#let result #u64 (#u64::add-wrap
              (#deref (#get holder reference)) (#get holder offset)))
            (#forget holder) (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 42u64) (#let-mut index #usize 1usize)
          (#let-mut calls #usize 0usize) (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ((owner (#borrow owner)) (index index)
              (calls (#unsafe (#addr-of-mut calls)))))) (waker (#borrow waker)))))
          (#assert (#usize::eq calls 1usize))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#set index 0usize)
          (#let second Work::Poll (#call Work::poll
            ((task pending) (waker (#borrow waker)))))
          (#assert (#usize::eq calls 1usize))
          (#return (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#;
    build_and_run_partial_storage(source, 43);
    let pinned = format!(
        "{}#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let owner #u64 42u64) (#let-mut calls #usize 0usize)
            (#let waker #u64 0u64)
            (#let-mut frame Work::Frame (#call work
              ((owner (#borrow owner)) (index 1usize)
                (calls (#unsafe (#addr-of-mut calls))))))
            (#let first Work::Poll (#call Work::poll
              ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
            (#assert (#usize::eq calls 1usize))
            (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
            (#let second Work::Poll (#call Work::poll
              ((task pending) (waker (#borrow waker)))))
            (#assert (#usize::eq calls 1usize))
            (#let result #u64 (#match second
              (#case (Work::Poll.Ready ready) ready)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
            (#forget frame) (#return result)\n  );\n}}\n",
        source
            .split_once("#fn main")
            .unwrap()
            .0
            .replace("#generate #async-fn", "#generate #async-fn-pinned")
    );
    build_and_run_partial_storage(&pinned, 43);
    let index_await = source
        .replace(
            "#generate #async-fn",
            "#enum IndexTask (#linear) ((IndexTask.IndexStart #usize) (IndexTask.IndexResume #usize))
#enum IndexPoll () ((IndexPoll.IndexPending IndexTask) (IndexPoll.IndexReady #usize))
#fn index-poll {
  #params = ((task IndexTask) (waker (#ref #u64)));
  #returns = IndexPoll;
  #body = (
  (#return (#match task
    (#case (IndexTask.IndexStart start) (IndexPoll.IndexPending (IndexTask.IndexResume start)))
    (#case (IndexTask.IndexResume resumed) (IndexPoll.IndexReady resumed))))
  );
}
#generate #async-fn",
        )
        .replace(
            "(#call index-value ((calls calls) (result index)))",
            "(#await #usize IndexTask IndexPoll.IndexPending IndexPoll.IndexReady index-poll
              (IndexTask.IndexStart (#call index-value ((calls calls) (result index)))))",
        )
        .replace(
            "(#return (#match second",
            "(#let-else (Work::Poll.Pending again) Work::Poll second (#unreachable))
             (#let third Work::Poll (#call Work::poll
               ((task again) (waker (#borrow waker)))))
             (#assert (#usize::eq calls 1usize))
             (#return (#match third",
        );
    assert!(index_await.contains("(#await #usize IndexTask"));
    build_and_run_partial_storage(&index_await, 43);
    let old_factory = format!(
        "#fn make-array{}",
        source
            .split_once("#fn make-array")
            .unwrap()
            .1
            .split_once("#fn index-value")
            .unwrap()
            .0
    );
    let matrix = index_await
        .replace(&old_factory,
            "#fn make-array {\n  #params = ((owner (#ref #u64)));\n  #returns = (#array (#array Holder 2) 2);\n  #body = (\n                 (#return (#array-of (#array (#array Holder 2) 2)\n                   (#array-of (#array Holder 2)\n                     (#struct-literal Holder ((reference owner) (offset 0u64)))\n                     (#struct-literal Holder ((reference owner) (offset 1u64))))\n                   (#array-of (#array Holder 2)\n                     (#struct-literal Holder ((reference owner) (offset 2u64)))\n                     (#struct-literal Holder ((reference owner) (offset 3u64))))))\n  );\n}\n")
        .replace("(#call make-array ((owner owner)))",
            "(#index (#call make-array ((owner owner))) (#call index-value ((calls calls) (result index))))")
        .replace("(IndexTask.IndexStart (#call index-value ((calls calls) (result index))))",
            "(IndexTask.IndexStart (#call index-value ((calls calls) (result 0usize))))")
        .replace("(#usize::eq calls 1usize)", "(#usize::eq calls 2usize)");
    assert!(matrix.contains("(#array (#array Holder 2) 2)"));
    build_and_run_partial_storage(&matrix, 44);
    let invalid_outer = matrix
        .replace(
            "(#let-mut index #usize 1usize)",
            "(#let-mut index #usize 2usize)",
        )
        .replace(
            "(#return result)\n#enum Step (#linear)",
            "(#if (#unsafe (#usize::eq (#ptr-read calls) 2usize))
               (#block (#unsafe (#linux-syscall () 60u64 (87u64))) (#unreachable)) ())
             (#return result)
#enum Step (#linear)",
        );
    assert!(invalid_outer.contains("(#linux-syscall () 60u64 (87u64))"));
    // If the first bounds check is deferred until after the second index
    // starts, the second callback exits 87 instead of trapping with SIGILL.
    build_and_run_route_status(&invalid_outer, None, true);
    let returned = source
        .replace(
            "(#fn work ((owner (#ref #u64)) (index #usize) (calls (#ptr-mut #usize))) #u64",
            "(#fn work ((owner (#ref #u64)) (index #usize) (calls (#ptr-mut #usize))) Holder",
        )
        .replace(
            "(#let result #u64 (#u64::add-wrap\n              (#deref (#get holder reference)) (#get holder offset)))\n            (#forget holder) (#return result)",
            "(#return holder)",
        )
        .replace(
            "(#case (Work::Poll.Ready result) result)",
            "(#case (Work::Poll.Ready result) (#block
              (#let data #u64 (#u64::add-wrap
                (#deref (#get result reference)) (#get result offset)))
              (#forget result) data))",
        );
    assert!(returned.contains("(#return holder)"));
    build_and_run_partial_storage(&returned, 43);
    let returned_invalid = returned.replace(
        "(#return (#match second",
        "(#set owner 99u64) (#return (#match second",
    );
    let error = graph_compile_error(&returned_invalid, "returned-index-clone-retains-owner");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let write = returned_invalid.find("(#set owner 99u64)").unwrap();
    let span = error
        .span
        .expect("returned array clone keeps its source span");
    assert!(
        span.start >= write && span.end <= write + "(#set owner 99u64)".len(),
        "{error:?}"
    );
    let invalid = index_await.replace(
        "(#set index 0usize)",
        "(#set owner 99u64) (#set index 0usize)",
    );
    let error = graph_compile_error(&invalid, "computed-index-clone-retains-owner");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let write = invalid.find("(#set owner 99u64)").unwrap();
    let span = error.span.expect("array owner loan keeps its source span");
    assert!(
        span.start >= write && span.end <= write + "(#set owner 99u64)".len(),
        "{error:?}"
    );
}

#[test]
fn async_borrows_scalar_inside_a_partially_stored_field() {
    let source = include_str!("../examples/async_partial_clone.lim")
        .replace(
            "(#let view (#ref Part) (#borrow (#get original second)))",
            "(#let view (#ref #u64) (#borrow (#get (#get original second) value)))",
        )
        .replace("(#get view value)", "(#deref view)");
    build_and_run_partial_storage(&source, 45);
}

#[test]
fn async_deep_field_borrows_preserve_permissions_and_addresses() {
    for (data_type, data, projection) in [
        ("#u64", "22u64", "(#get (#get pair right) data)"),
        (
            "(#tuple #u64 #u64)",
            "(#tuple (#tuple #u64 #u64) 21u64 22u64)",
            "(#get (#get (#get pair right) data) 1)",
        ),
        (
            "(#array #u64 2)",
            "(#array-of (#array #u64 2) 21u64 22u64)",
            "(#index (#get (#get pair right) data) 1usize)",
        ),
        (
            "(#array #u64 2)",
            "(#array-of (#array #u64 2) 21u64 22u64)",
            "(#index (#get (#get pair right) data) selection)",
        ),
    ] {
        for mutable in [false, true] {
            for pinned in [false, true] {
                let reference = if pinned { "#pin-ref" } else { "#ref" };
                let borrow = if pinned { "#pin-borrow" } else { "#borrow" };
                let suffix = if mutable { "-mut" } else { "" };
                let write = if mutable && pinned {
                    "(#unsafe (#pin-write view 23u64))"
                } else if mutable {
                    "(#deref-set view 23u64)"
                } else {
                    ""
                };
                let source = format!(
                    r#"
#struct Resource (#linear) ((value #u64))
#struct Holder (#linear) ((data {data_type}))
#struct Pair (#linear) ((left Resource) (right Holder))
#enum Step (#linear) (Step.Start Step.Resume)
#enum StepPoll () ((StepPoll.Pending Step) (StepPoll.Ready ()))
#fn step-poll {{
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
                      (#return (#match task
                        (#case Step.Start (StepPoll.Pending Step.Resume)) (#case Step.Resume (StepPoll.Ready ()))))
  );
}}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64) (function
                      (#fn work () #u64
                        (#let-mut pair Pair (#struct-literal Pair
                          ((left (#struct-literal Resource ((value 20u64))))
                           (right (#struct-literal Holder ((data {data})))))))
                        (#let-mut selection #usize 1usize)
                        (#let view ({reference}{suffix} #u64) ({borrow}{suffix} {projection}))
                        (#set selection 0usize)
                        (#let moved Resource (#get pair left))
                        (#let ready () (#await () Step StepPoll.Pending StepPoll.Ready step-poll Step.Start))
                        (#forget moved)
                        (#set-field pair left (#struct-literal Resource ((value 23u64))))
                        {write}
                        (#let observed #u64 (#deref view))
                        (#drop view)
                        (#let result #u64 (#u64::add-wrap (#get (#get pair left) value) observed))
                        (#forget pair) (#return result))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                      (#let waker #u64 0u64)
                      (#let-mut frame Work::Frame (#call work ()))
                      (#let first Work::Poll (#call Work::poll
                        ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
                      (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
                      (#let result #u64 (#match (#call Work::poll
                        ((task pending) (waker (#borrow waker))))
                        (#case (Work::Poll.Ready value) value)
                        (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
                      (#forget frame) (#return result)
  );
}}
                "#
                );
                build_and_run_partial_storage(&source, if mutable { 46 } else { 45 });
                if !mutable && !pinned {
                    let retained = projection
                        .replace("(#get pair right)", "retained")
                        .replace(" selection)", " 1usize)");
                    let cancelled = format!(
                        "{}#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                            (#let waker #u64 0u64)
                            (#let-mut frame Work::Frame (#call work ()))
                            (#let first Work::Poll (#call Work::poll
                              ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
                            (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
                            (#let (Work::Frame::Cleanup moved right shell waiting) Work::Frame::Cleanup
                              (#call Work::Poll::cleanup ((task pending))))
                            (#forget frame)
                            (#let-else (Work::Frame::Cleanup::Pair-right.Full retained) Work::Frame::Cleanup::Pair-right right (#unreachable))
                            (#let result #u64 {retained})
                            (#forget moved) (#forget retained) (#forget shell) (#forget waiting)
                            (#return result)\n  );\n}}\n",
                        source.split_once("#fn main").unwrap().0
                    );
                    build_and_run_partial_storage(&cancelled, 22);
                }
                if !pinned {
                    // Movable tasks may form operation-local references, but
                    // they must not carry an internal address over Pending.
                    let view = format!(
                        "(#let view ({reference}{suffix} #u64) ({borrow}{suffix} {projection}))"
                    );
                    let continuation = source
                        .replace("#generate #async-fn-pinned", "#generate #async-fn")
                        .replace(&view, "")
                        .replace(
                            "(#set-field pair left (#struct-literal Resource ((value 23u64))))",
                            &format!("(#set-field pair left (#struct-literal Resource ((value 23u64)))) {view}"),
                        );
                    let movable = format!(
                        "{}#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                            (#let waker #u64 0u64)
                            (#let first Work::Poll (#call Work::poll
                              ((task (#call work ())) (waker (#borrow waker)))))
                            (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
                            (#return (#match (#call Work::poll
                              ((task pending) (waker (#borrow waker))))
                              (#case (Work::Poll.Ready value) value)
                              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}}\n",
                        continuation.split_once("#fn main").unwrap().0
                    );
                    let expected = if mutable {
                        46
                    } else if projection.contains("selection") {
                        44
                    } else {
                        45
                    };
                    build_and_run_partial_storage(&movable, expected);
                }
                let conflicting_projection = projection.replace(" selection)", " 1usize)");
                let overlap = format!(
                    "(#let overlap (#ref-mut #u64) (#borrow-mut {conflicting_projection})) (#deref-set overlap 99u64) (#drop overlap)"
                );
                let invalid = source.replace(
                    "(#let moved Resource",
                    &format!("{overlap} (#let moved Resource"),
                );
                let error = graph_compile_error(&invalid, "deep-field-overlap");
                assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
                let span = error
                    .span
                    .expect("conflicting deep borrow keeps its source span");
                let start = invalid.find(&overlap).unwrap();
                assert!(
                    span.start >= start && span.end <= start + overlap.len(),
                    "{error:?}"
                );
            }
        }
    }
}

#[test]
fn async_clones_rebuilt_whole_aggregates_without_relocating_borrowed_fields() {
    let source = r#"
#struct Resource (#linear) ((value #u64))

#fn Resource::clone {
  #params = ((original Resource));
  #returns = Resource;
  #body = (
          (#let value #u64 (#u64::add-wrap (#get original value) 100u64))
          (#forget original)
          (#return (#struct-literal Resource ((value value))))
  );
}
#struct Pair (#linear) ((left Resource) (right Resource) (reference (#ref #u64)))

#fn Pair::clone {
  #params = ((original Pair));
  #returns = Pair;
  #body = (
          (#let (Pair left right reference) Pair original)
          (#let value #u64 (#u64::add-wrap (#get left value) 1u64))
          (#forget left)
          (#return (#struct-literal Pair
            ((left (#struct-literal Resource ((value value)))) (right right) (reference reference))))
  );
}
#enum Step (#linear) (Step.Start Step.Resume)

#enum StepPoll () ((StepPoll.Pending Step) (StepPoll.Ready ()))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task (#case Step.Start (StepPoll.Pending Step.Resume)) (#case Step.Resume (StepPoll.Ready ()))))
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64) (function
          (#fn work ((owner (#ref #u64))) Pair
            (#let-mut pair Pair (#struct-literal Pair
              ((left (#struct-literal Resource ((value 0u64))))
               (right (#struct-literal Resource ((value 1u64)))) (reference owner))))
            (#let view (#ref Resource) (#borrow (#get pair right)))
            (#let moved Resource (#get pair left))
            (#let ready () (#await () Step StepPoll.Pending StepPoll.Ready step-poll Step.Start))
            (#set-field pair left (#struct-literal Resource ((value 2u64))))
            (#forget moved)
            (#let duplicate Pair (#clone pair))
            (#assert (#u64::eq (#get view value) 1u64))
            (#assert (#u64::eq (#get (#get pair left) value) 2u64))
            (#drop view) (#forget pair) (#return duplicate))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 42u64) (#let waker #u64 0u64)
          (#let-mut frame Work::Frame (#call work ((owner (#borrow owner)))))
          (#let first Work::Poll (#call Work::poll
            ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64 (#match second
            (#case (Work::Poll.Ready duplicate) (#block
              (#let answer #u64 (#u64::add-wrap
                (#deref (#get duplicate reference))
                (#u64::add-wrap (#get (#get duplicate left) value) (#get (#get duplicate right) value))))
              (#forget duplicate) answer))
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame) (#return result)
  );
}
    "#;
    build_and_run_partial_storage(source, 46);
    let hook = lim::parse_source_unit(source)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
                if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#fn")
                    && matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == "Pair::clone"))
        })
        .expect("the fixture defines an explicit Pair clone hook");
    let mut structural = source.to_owned();
    structural.replace_range(hook.span.start..hook.span.end, "");
    assert!(!structural.contains("#fn Pair::clone"));
    build_and_run_partial_storage(&structural, 45);

    let reference_leaf = source
        .replace("#struct Pair (#linear) ((left Resource) (right Resource) (reference (#ref #u64)))",
            "#struct Holder (#linear) ((reference (#ref #u64)) (value #u64))

#fn Holder::clone {
  #params = ((original Holder));
  #returns = Holder;
  #body = (
                 (#let reference (#ref #u64) (#get original reference))
                 (#let value #u64 (#u64::add-wrap (#get original value) 200u64))
                 (#forget original)
                 (#return (#struct-literal Holder ((reference reference) (value value))))
  );
}
#struct Pair (#linear) ((left Resource) (right Holder))")
        .replace("(Pair left right reference)", "(Pair left right)")
        .replace("(right right) (reference reference)", "(right right)")
        .replace("(right (#struct-literal Resource ((value 1u64)))) (reference owner)",
            "(right (#struct-literal Holder ((reference owner) (value 1u64))))")
        .replace("(#let view (#ref Resource) (#borrow (#get pair right)))", "")
        .replace("(#assert (#u64::eq (#get view value) 1u64))", "")
        .replace("(#drop view) ", "")
        .replace("(#deref (#get duplicate reference))", "(#deref (#get (#get duplicate right) reference))")
        .replace("(#case (Work::Poll.Ready duplicate) (#block",
            "(#case (Work::Poll.Ready duplicate) (#block (#forget frame)")
        .replace("(#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))",
            "(#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#forget frame) (#unreachable)))")
        .replace("(#forget frame) (#return result)", "(#return result)");
    assert!(reference_leaf.contains("(right Holder)"));
    let generated = build_and_run_partial_storage(&reference_leaf, 46);
    let movable = format!(
        "{}#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut owner #u64 42u64) (#let waker #u64 0u64)
            (#let first Work::Poll (#call Work::poll
              ((task (#call work ((owner (#borrow owner))))) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
            (#let second Work::Poll (#call Work::poll
              ((task pending) (waker (#borrow waker)))))
            (#return (#match second
              (#case (Work::Poll.Ready duplicate) (#block
                (#let result #u64 (#u64::add-wrap
                  (#deref (#get (#get duplicate right) reference))
                  (#u64::add-wrap (#get (#get duplicate left) value) (#get (#get duplicate right) value))))
                (#forget duplicate) result))
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}}\n",
        reference_leaf.split_once("#fn main").unwrap().0
            .replace("#generate #async-fn-pinned", "#generate #async-fn")
    );
    build_and_run_partial_storage(&movable, 46);
    let invalid = reference_leaf.replace(
        "(#block (#forget frame)\n",
        "(#block (#forget frame) (#set owner 99u64)\n",
    );
    assert!(invalid.contains("(#set owner 99u64)"));
    let error = graph_compile_error(&invalid, "rebuilt-clone-retains-reference-leaf");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let write = invalid.find("(#set owner 99u64)").unwrap();
    let span = error
        .span
        .expect("returned aggregate clone keeps caller span");
    assert!(
        span.start >= write && span.end <= write + "(#set owner 99u64)".len(),
        "{error:?}"
    );
    let invocation = lim::parse_source_unit(&invalid).unwrap().into_iter().find(|node|
        matches!(&node.expr, lim::Expr::List(items) if matches!(items.first(), Some(lim::Expr::Generate))))
        .unwrap();
    let ordinary = format!(
        "{}\n{generated}\n{}",
        &invalid[..invocation.span.start],
        &invalid[invocation.span.end..]
    );
    assert!(
        lim::check_types(&lim::parse_program(&ordinary_generated(&ordinary)).unwrap())
            .unwrap_err()
            .contains("borrow")
    );

    let premature = source.replace(
        "(#let ready () (#await",
        "(#let premature Pair (#clone pair)) (#forget premature) (#let ready () (#await",
    );
    let error = graph_compile_error(&premature, "rebuilt-clone-rejects-uninitialized-owner");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
}

#[test]
fn async_clones_computed_reference_bearing_owners() {
    let source = r#"
#struct Holder (#linear) ((reference (#ref #u64)))

#fn make-holder {
  #params = ((reference (#ref #u64)));
  #returns = Holder;
  #body = (
          (#return (#struct-literal Holder ((reference reference))))
  );
}
#enum Step (#linear) (Step.Start Step.Resume)

#enum StepPoll () ((StepPoll.Pending Step) (StepPoll.Ready ()))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case Step.Start (StepPoll.Pending Step.Resume))
            (#case Step.Resume (StepPoll.Ready ()))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64) (function
          (#fn work ((owner (#ref #u64))) #u64
            (#let holder Holder (#clone (#call make-holder ((reference owner)))))
            (#let ready () (#await () Step StepPoll.Pending StepPoll.Ready step-poll Step.Start))
            (#let result #u64 (#deref (#get holder reference)))
            (#forget holder)
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 42u64)
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((owner (#borrow owner))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#return (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#;
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    let invalid = source.replace(
        "(#let second Work::Poll",
        "(#set owner 43u64) (#let second Work::Poll",
    );
    let projected = source
        .replace(
            "#enum Step (#linear) (Step.Start Step.Resume)",
            "#struct Envelope () ((item Holder))
#fn make-envelope {
  #params = ((reference (#ref #u64)));
  #returns = Envelope;
  #body = (
                 (#return (#struct-literal Envelope
                   ((item (#call make-holder ((reference reference)))))))
  );
}
#enum Step (#linear) (Step.Start Step.Resume)",
        )
        .replace(
            "(#clone (#call make-holder ((reference owner))))",
            "(#clone (#get (#call make-envelope ((reference owner))) item))",
        );
    assert!(projected.contains("(#clone (#get (#call make-envelope"));
    build_and_run_partial_storage(&projected, 42);
    let projected_invalid = projected.replace(
        "(#let second Work::Poll",
        "(#set owner 43u64) (#let second Work::Poll",
    );
    let error = graph_compile_error(&projected_invalid, "projected-clone-retains-origin");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let write = projected_invalid.find("(#set owner 43u64)").unwrap();
    let span = error
        .span
        .expect("projected clone keeps original caller span");
    assert!(
        span.start >= write && span.end <= write + "(#set owner 43u64)".len(),
        "{error:?}"
    );
    let error = graph_compile_error(&invalid, "computed-clone-retains-origin");
    assert!(error.message.contains("borrow"), "{error:?}");
    let write = invalid.find("(#set owner 43u64)").unwrap();
    let span = error
        .span
        .expect("borrow violation needs an original source span");
    assert!(
        span.start >= write && span.end <= write + "(#set owner 43u64)".len(),
        "{error:?}"
    );
    let returned_projection = projected
        .replace(
            "(#fn work ((owner (#ref #u64))) #u64",
            "(#fn work ((owner (#ref #u64))) Holder",
        )
        .replace(
            "(#let result #u64 (#deref (#get holder reference)))\n            (#forget holder)\n            (#return result)",
            "(#return holder)",
        )
        .replace(
            "(#case (Work::Poll.Ready result) result)",
            "(#case (Work::Poll.Ready result) (#block
              (#let data #u64 (#deref (#get result reference))) (#forget result) data))",
        );
    assert!(returned_projection.contains("(#return holder)"));
    build_and_run_partial_storage(&returned_projection, 42);
    let returned_invalid = returned_projection.replace(
        "(#return (#match second",
        "(#set owner 43u64) (#return (#match second",
    );
    let error = graph_compile_error(&returned_invalid, "returned-projected-clone-retains-origin");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let exclusive = source
        .replace("(#ref #u64)", "(#ref-mut #u64)")
        .replace("waker (#ref-mut #u64)", "waker (#ref #u64)")
        .replace("owner (#borrow owner)", "owner (#borrow-mut owner)");
    let error = graph_compile_error(&exclusive, "computed-clone-exclusive-reference");
    assert!(
        error.message.contains("clone") || error.message.contains("Clone"),
        "{error:?}"
    );
    let reused = source
        .replace(
            "(#let holder Holder (#clone (#call make-holder ((reference owner)))))",
            "(#let original Holder (#call make-holder ((reference owner))))\n          (#let holder Holder (#clone original))",
        )
        .replace(
            "(#let result #u64 (#deref (#get holder reference)))",
            "(#let result #u64 (#u64::add-wrap (#deref (#get holder reference)) (#deref (#get original reference))))\n          (#forget original)",
        );
    assert_ne!(reused, source);
    build_and_run_graph(&reused, 84);
    let conflicting = reused.replace(
        "(#let second Work::Poll",
        "(#set owner 43u64) (#let second Work::Poll",
    );
    let error = graph_compile_error(&conflicting, "reused-clone-retains-origin");
    assert!(error.message.contains("borrow"), "{error:?}");
    let span = error
        .span
        .expect("retained owners need a source diagnostic");
    let write = conflicting.find("(#set owner 43u64)").unwrap();
    assert!(
        span.start >= write && span.end <= write + "(#set owner 43u64)".len(),
        "{error:?}"
    );
}

#[test]
fn async_while_let_body_can_suspend_multiple_times_after_matching() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ConditionTask (#linear) (ConditionTask.ConditionWaiting ConditionTask.ConditionResuming)

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady Maybe))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case ConditionTask.ConditionWaiting (ConditionPoll.ConditionPending ConditionTask.ConditionResuming))
            (#case ConditionTask.ConditionResuming (ConditionPoll.ConditionReady (Maybe.Some 42u64)))))
  );
}
#enum BodyTask (#linear) (BodyTask.BodyWaiting BodyTask.BodyResuming)

#fn start-body-task {
  #params = ();
  #returns = BodyTask;
  #body = ( (#return BodyTask.BodyWaiting)
  );
}
#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case BodyTask.BodyWaiting (BodyPoll.BodyPending BodyTask.BodyResuming))
            (#case BodyTask.BodyResuming (BodyPoll.BodyReady 7u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while-let (Maybe.Some payload)
              (#await Maybe ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                condition-poll ConditionTask.ConditionWaiting)
              (#let first #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll
                  (#call start-body-task ())))
              (#let second #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll
                  (#call start-body-task ())))
              (#assert (#u64::eq first second))
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending body-first-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll
            (#call Work::poll ((task body-first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending body-second-pending) Work::Poll third (#unreachable))
          (#let fourth Work::Poll
            (#call Work::poll ((task body-second-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match fourth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");

    let linear_source = source.replace(
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)",
        "#enum Maybe (#linear) ((Maybe.Some #u64) Maybe.None)\n      ",
    );
    let generated = build_and_run_graph(&linear_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let hooked = format!(
        "#fn Maybe::clone {{
  #params = ((value Maybe));
  #returns = Maybe;
  #body = (
  (#return (#match value
  (#case (Maybe.Some original) (Maybe.Some (#u64::add-wrap original 1u64)))
  (#case Maybe.None Maybe.None)))
  );
}}
{}",
        linear_source.replace(
            "(#let first #u64\n                (#await",
            "(#assert (#u64::eq payload 43u64))\n            (#let first #u64\n              (#await",
        ),
    );
    assert!(hooked.contains("(#assert (#u64::eq payload 43u64))"));
    let generated = build_and_run_graph(&hooked, 42);
    assert_single_poll(&generated, "Work::poll");

    let repeated = format!(
        "{}\n#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let-mut task Work::Task (#call work ()))
            (#for-range (attempt #u64) 0u64 8u64
              (#let outcome Work::Poll
                (#call Work::poll ((task task) (waker (#borrow waker)))))
              (#match outcome
                (#case (Work::Poll.Pending next) (#block (#set task next) ()))
                (#case (Work::Poll.Ready result) (#block (#return result)))))
            (#forget task)
            (#return (#unreachable))\n  );\n}}\n",
        hooked
            .split_once("#fn main {\n  #params = ();\n  #returns = #u64;")
            .unwrap()
            .0
            .replace(
                "(#fn work () #u64",
                "(#fn work () #u64 (#let-mut cycles #u64 0u64)"
            )
            .replace(
                "(#break)",
                "(#set cycles (#u64::add-wrap cycles 1u64)) (#if (#u64::eq cycles 2u64) (#break) ())"
            ),
    );
    let generated = build_and_run_graph(&repeated, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_let_suspends_in_a_nested_body_statement() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ConditionTask (#linear) (ConditionTask.ConditionWaiting)

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady Maybe))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#forget task)
          (#return (ConditionPoll.ConditionReady (Maybe.Some 42u64)))
  );
}
#enum BodyTask (#linear) (BodyTask.BodyWaiting BodyTask.BodyResuming)

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #bool))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case BodyTask.BodyWaiting (BodyPoll.BodyPending BodyTask.BodyResuming))
            (#case BodyTask.BodyResuming (BodyPoll.BodyReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while-let (Maybe.Some payload)
              (#await Maybe ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                condition-poll ConditionTask.ConditionWaiting)
              (#assert (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll BodyTask.BodyWaiting))
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-frame) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending-frame) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_let_does_not_poll_the_unselected_scrutinee_branch() {
    let source = "#enum Maybe () (Maybe.Some Maybe.None)
#enum ChildTask (#linear) (ChildTask.Waiting ChildTask.Resuming)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady Maybe))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#forget task)
          (#assert false)
          (#return (ChildPoll.ChildReady Maybe.None))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while-let Maybe.Some
              (#if false
                (#await Maybe ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting)
                Maybe.None)
              (#assert false))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let outcome Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Ready value) 42u64)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");

    let pending_source = source
        .replace(
            "          (#forget task)\n          (#assert false)\n          (#return (ChildPoll.ChildReady Maybe.None))",
            "        (#return (#match task\n          (#case ChildTask.Waiting (ChildPoll.ChildPending ChildTask.Resuming))\n          (#case ChildTask.Resuming (ChildPoll.ChildReady Maybe.None))))",
        )
        .replace("(#if false", "(#if true")
        .replace(
            "          (#let outcome Work::Poll\n            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))",
            "        (#let first Work::Poll\n          (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))\n        (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))\n        (#let outcome Work::Poll\n          (#call Work::poll ((task pending) (waker (#borrow waker)))))",
        );
    build_and_run_graph(&pending_source, 42);
}

#[test]
fn async_await_preserves_boolean_short_circuiting() {
    let source = format!(
        "#alias lim-gen-cell = \"{0}/library/cell.lim::#cell\"\n#generate lim-gen-cell #u64 CellU64 CellU64::create CellU64::get CellU64::set\n#enum ChildTask () ((ChildTask.Waiting (#ref CellU64)))\n#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))\n#fn child-poll {{\n  #params = ((task ChildTask) (waker (#ref #u64)));\n  #returns = ChildPoll;\n  #body = (\n             (#return (#match task\n               (#case (ChildTask.Waiting cell)\n                 (#block\n                   (#call CellU64::set ((cell cell) (value\n                     (#u64::add-wrap (#call CellU64::get ((cell cell))) 1u64))))\n                   (ChildPoll.ChildReady true)))))\n  );\n}}\n#generate #async-fn ((protocol work-await) (waker #u64) (function\n             (#fn work ((cell (#ref CellU64))) #u64\n               (#let ignored #bool\n                 (#bool::and false\n                   (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting cell))))\n               (#return (#call CellU64::get ((cell cell)))))))\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#let cell CellU64 (#call CellU64::create ((value 0u64))))\n             (#let waker #u64 0u64)\n             (#let result Work::Poll\n               (#call Work::poll ((task (#call work ((cell (#borrow cell))))) (waker (#borrow waker)))))\n             (#let value #u64 (#match result\n               (#case (Work::Poll.Ready ready) ready)\n               (#case (Work::Poll.Pending pending) (#block (#forget pending) 1u64))))\n             (#forget waker)\n             (#forget cell)\n             (#return (#if (#u64::eq value 0u64) 42u64 0u64))\n  );\n}}\n",
        env!("CARGO_MANIFEST_DIR")
    );
    build_and_run(&source, 42);
    let or_source = source.replace("#bool::and false", "#bool::or true");
    build_and_run(&or_source, 42);
}

#[test]
fn async_await_preserves_match_guard_selection() {
    let source = format!(
        "#alias lim-gen-cell = \"{0}/library/cell.lim::#cell\"\n#generate lim-gen-cell #u64 CellU64 CellU64::create CellU64::get CellU64::set\n#enum ChildTask () ((ChildTask.Waiting (#ref CellU64)))\n#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))\n#fn child-poll {{\n  #params = ((task ChildTask) (waker (#ref #u64)));\n  #returns = ChildPoll;\n  #body = (\n             (#return (#match task\n               (#case (ChildTask.Waiting cell)\n                 (#block\n                   (#call CellU64::set ((cell cell) (value\n                     (#u64::add-wrap (#call CellU64::get ((cell cell))) 1u64))))\n                   (ChildPoll.ChildReady true)))))\n  );\n}}\n#generate #async-fn ((protocol work-await) (waker #u64) (function\n             (#fn work ((cell (#ref CellU64))) #u64\n               (#let ignored #bool\n                 (#match true\n                   (#case true (#when false)\n                     (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting cell)))\n                   (#case _ false)))\n               (#return (#call CellU64::get ((cell cell)))))))\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#let cell CellU64 (#call CellU64::create ((value 0u64))))\n             (#let waker #u64 0u64)\n             (#let result Work::Poll\n               (#call Work::poll ((task (#call work ((cell (#borrow cell))))) (waker (#borrow waker)))))\n             (#let value #u64 (#match result\n               (#case (Work::Poll.Ready ready) ready)\n               (#case (Work::Poll.Pending pending) (#block (#forget pending) 1u64))))\n             (#forget waker)\n             (#forget cell)\n             (#return (#if (#u64::eq value 0u64) 42u64 0u64))\n  );\n}}\n",
        env!("CARGO_MANIFEST_DIR")
    );
    build_and_run(&source, 42);
    let selected_source = source.replace("(#when false)", "(#when true)");
    build_and_run(&selected_source, 0);
}

#[test]
fn async_await_preserves_if_let_branch_selection() {
    let source = format!(
        "#alias lim-gen-cell = \"{0}/library/cell.lim::#cell\"\n#generate lim-gen-cell #u64 CellU64 CellU64::create CellU64::get CellU64::set\n#enum Maybe () ((Maybe.Some #u64) Maybe.None)\n#enum ChildTask () ((ChildTask.Waiting (#ref CellU64)))\n#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))\n#fn child-poll {{\n  #params = ((task ChildTask) (waker (#ref #u64)));\n  #returns = ChildPoll;\n  #body = (\n             (#return (#match task\n               (#case (ChildTask.Waiting cell)\n                 (#block\n                   (#call CellU64::set ((cell cell) (value\n                     (#u64::add-wrap (#call CellU64::get ((cell cell))) 1u64))))\n                   (ChildPoll.ChildReady true)))))\n  );\n}}\n#generate #async-fn ((protocol work-await) (waker #u64) (function\n             (#fn work ((maybe Maybe) (cell (#ref CellU64))) #u64\n               (#let ignored #bool\n                 (#if-let (Maybe.Some payload) maybe\n                   (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting cell))\n                   false))\n               (#return (#call CellU64::get ((cell cell)))))))\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n             (#let cell CellU64 (#call CellU64::create ((value 0u64))))\n             (#let waker #u64 0u64)\n             (#let result Work::Poll\n               (#call Work::poll ((task (#call work ((maybe Maybe.None) (cell (#borrow cell))))) (waker (#borrow waker)))))\n             (#let value #u64 (#match result\n               (#case (Work::Poll.Ready ready) ready)\n               (#case (Work::Poll.Pending pending) (#block (#forget pending) 1u64))))\n             (#forget waker)\n             (#forget cell)\n             (#return (#if (#u64::eq value 0u64) 42u64 0u64))\n  );\n}}\n",
        env!("CARGO_MANIFEST_DIR")
    );
    build_and_run(&source, 42);
    let selected_source = source.replace("(maybe Maybe.None)", "(maybe (Maybe.Some 7u64))");
    build_and_run(&selected_source, 0);
}

#[test]
fn async_function_returns_linear_state_after_a_loop() {
    let source = "#struct State (#linear) ((value #u64))

#struct Token (#linear) ((limit #u64))

#enum ChildPoll () ((ChildPoll.ChildPending #u64) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task #u64) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#if (#u64::eq task 0u64)
            (ChildPoll.ChildPending 1u64)
            (ChildPoll.ChildReady task)))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut state State (#struct-literal State ((value 0u64))))
            (#let token Token (#struct-literal Token ((limit 3u64))))
            (#while (#u64::lt (#get state value) (#get token limit))
              (#let result #u64
                (#await #u64 ChildPoll.ChildPending ChildPoll.ChildReady child-poll (#get state value)))
              (#let next-value #u64 (#u64::add-wrap result 1u64))
              (#forget state)
              (#set state (#struct-literal State
                ((value next-value)))))
            (#return (#block
              (#let value #u64 (#get state value))
              (#forget state)
              (#forget token)
              value)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let cancel-frame Work::Task (#call work ()))
          (#let cancel-first Work::Poll (#call Work::poll ((task cancel-frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending cancelled-task) Work::Poll cancel-first (#unreachable))
          (#forget cancelled-task)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending-again)
                (#block (#forget pending-again) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 3);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_resumes_child_await_inside_a_for_range_loop() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady value)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for-range (iteration #u64) 0u64 2u64
              (#let result #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting iteration))))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending-again)
                (#block (#forget pending-again) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_range_suspends_in_a_non_binding_body_statement() {
    let source = "#enum BodyTask (#linear) (BodyTask.Waiting BodyTask.Resuming)

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #bool))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case BodyTask.Waiting (BodyPoll.BodyPending BodyTask.Resuming))
            (#case BodyTask.Resuming (BodyPoll.BodyReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for-range (iteration #u64) 0u64 2u64
              (#assert (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll BodyTask.Waiting))
              (#if (#u64::eq iteration 0u64)
                (#continue)
                (#break)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task second-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_range_awaits_bounds_in_source_order_before_iterating() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64) (Child.Resuming #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildPending (Child.Resuming value)))
            (#case (Child.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for-range (iteration #u64)
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 2u64))
              (#assert (#u64::lt iteration 3u64)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll
            (#call Work::poll ((task second-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert!(!generated.contains("(#await"), "{generated}");
}

#[test]
fn range_bounds_are_once_with_side_effects_and_labeled_continue() {
    build_and_run(include_str!("../examples/range_bounds_once.lim"), 42);
    let source = include_str!("../examples/async_range_bounds_once.lim");
    build_and_run(source, 42);
    build_and_run_graph(source, 42);
    let immediate = source.replace(
        "(ChildPoll.ChildPending (ChildTask.Resume value))",
        "(ChildPoll.ChildReady value)",
    );
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
    let source = "#enum Child (#linear) ((Child.BoundWaiting #u64) (Child.BoundResuming #u64) (Child.Body #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.BoundWaiting value) (ChildPoll.ChildPending (Child.BoundResuming value)))
            (#case (Child.BoundResuming value) (ChildPoll.ChildReady value))
            (#case (Child.Body value) (ChildPoll.ChildReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for-range (iteration #u64)
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.BoundWaiting 0u64))
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.BoundWaiting 2u64))
              (#let result #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Body iteration))))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll
            (#call Work::poll ((task second-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert!(generated.contains("Child.BoundWaiting"), "{generated}");
    assert!(generated.contains("Child.Body"), "{generated}");
}

#[test]
fn async_function_resumes_child_await_inside_for_with_existing_counter() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (Child.Waiting 1u64))
                (ChildPoll.ChildReady value)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for (#set iteration 0u64)
                  (#u64::lt iteration 2u64)
                  (#set iteration (#u64::add-wrap iteration 1u64))
              (#let result #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting iteration))))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending-again)
                (#block (#forget pending-again) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_condition_can_await_and_step_only_after_ready_true() {
    let source = "#enum ChildTask () ((ChildTask.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (ChildTask.Waiting 1u64))
                (ChildPoll.ChildReady (#u64::lt value 2u64))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for (#set iteration 0u64)
                  (#await ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting iteration))
                  (#set iteration (#u64::add-wrap iteration 1u64))
              (#assert true))
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let value #u64 (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending-again) (#block (#forget pending-again) 0u64))))
          (#forget waker)
          (#return (#if (#u64::eq value 2u64) 42u64 0u64))\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_condition_can_suspend_with_an_awaited_step() {
    let source = "#enum ConditionTask (#linear) ((ConditionTask.Waiting #u64) (ConditionTask.Resuming #u64))

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.Waiting iteration) (ConditionPoll.ConditionPending (ConditionTask.Resuming iteration)))
            (#case (ConditionTask.Resuming iteration)
              (ConditionPoll.ConditionReady (#u64::lt iteration 1u64)))))
  );
}
#enum BodyTask (#linear) ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #bool))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting iteration) (BodyPoll.BodyPending (BodyTask.BodyResuming iteration)))
            (#case (BodyTask.BodyResuming iteration) (BodyPoll.BodyReady true))))
  );
}
#enum StepTask (#linear) ((StepTask.StepWaiting (#tuple #u64 #bool)) (StepTask.StepResuming (#tuple #u64 #bool)))

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (StepTask.StepWaiting (#tuple iteration body-ran))
              (#block (#assert body-ran)
                (StepPoll.StepPending (StepTask.StepResuming (#tuple (#tuple #u64 #bool) iteration body-ran)))))
            (#case (StepTask.StepResuming (#tuple iteration body-ran))
              (#block (#assert body-ran)
                (StepPoll.StepReady (#u64::add-wrap iteration 1u64))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for (#set iteration 0u64)
                  (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                    condition-poll (ConditionTask.Waiting iteration))
                  (#set iteration
                    (#await #u64 StepTask StepPoll.StepPending StepPoll.StepReady step-poll
                      (StepTask.StepWaiting (#tuple (#tuple #u64 #bool) iteration body-ran))))
              (#let body-ran #bool true))
            (#return (#if (#u64::eq iteration 1u64) 42u64 0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending step-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task step-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending resumed-condition) Work::Poll third (#unreachable))
          (#let fourth Work::Poll (#call Work::poll ((task resumed-condition) (waker (#borrow waker)))))
          (#let result #u64
            (#match fourth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");

    let three_phase_source = source
        .replace(
            "(#let-mut iteration #u64 0u64)",
            "(#let-mut iteration #u64 0u64)\n          (#let-mut total #u64 0u64)",
        )
        .replace(
            "(#let body-ran #bool true)",
            "(#let body-ran #bool\n              (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll\n                (BodyTask.BodyWaiting iteration)))\n            (#set total (#u64::add-wrap total 1u64))",
        )
        .replace(
            "(#return (#if (#u64::eq iteration 1u64) 42u64 0u64))",
            "(#return (#if (#u64::eq iteration 1u64)\n            (#if (#u64::eq total 1u64) 42u64 0u64)\n            0u64))",
        );
    let (prefix, _) = three_phase_source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let three_phase_source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
            (#let second Work::Poll (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending body-pending) Work::Poll second (#unreachable))
            (#let third Work::Poll (#call Work::poll ((task body-pending) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending step-pending) Work::Poll third (#unreachable))
            (#let fourth Work::Poll (#call Work::poll ((task step-pending) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending resumed-condition) Work::Poll fourth (#unreachable))
            (#let fifth Work::Poll (#call Work::poll ((task resumed-condition) (waker (#borrow waker)))))
            (#let result #u64
              (#match fifth
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
            (#forget waker)
            (#return result)
  );\n}}\n"
    );
    let generated = build_and_run_graph(&three_phase_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let shared_reference_source = three_phase_source
        .replace(
            "(#fn work () #u64",
            "(#fn work ((view (#ref #u64))) #u64",
        )
        .replace(
            "(#set total (#u64::add-wrap total 1u64))",
            "(#assert (#u64::eq (#deref view) 41u64))\n            (#set total (#u64::add-wrap total 1u64))",
        )
        .replace(
            "(#return (#if (#u64::eq iteration 1u64)\n            (#if (#u64::eq total 1u64) 42u64 0u64)\n            0u64))",
            "(#return (#if (#u64::eq (#deref view) 41u64)\n            (#if (#u64::eq iteration 1u64)\n              (#if (#u64::eq total 1u64) 42u64 0u64)\n              0u64)\n            0u64))",
        );
    let (prefix, _) = shared_reference_source
        .split_once("#fn main {\n  #params = ();\n  #returns = #u64;")
        .unwrap();
    let shared_reference_source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut owner #u64 41u64)
            (#let waker #u64 0u64)
            (#let task Work::Task (#call work ((view (#borrow owner)))))
            (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
            (#let second Work::Poll (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending body-pending) Work::Poll second (#unreachable))
            (#let third Work::Poll (#call Work::poll ((task body-pending) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending step-pending) Work::Poll third (#unreachable))
            (#let fourth Work::Poll (#call Work::poll ((task step-pending) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending resumed-condition) Work::Poll fourth (#unreachable))
            (#let fifth Work::Poll (#call Work::poll ((task resumed-condition) (waker (#borrow waker)))))
            (#let result #u64
              (#match fifth
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
            (#set owner 43u64)
            (#forget waker)
            (#return (#if (#u64::eq result 42u64)
              (#if (#u64::eq owner 43u64) 42u64 0u64) 0u64))
  );\n}}\n"
    );
    let generated = build_and_run_graph(&shared_reference_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let mutation_before_poll = shared_reference_source.replace(
        "(#let task Work::Task (#call work ((view (#borrow owner)))))",
        "(#let task Work::Task (#call work ((view (#borrow owner)))))\n          (#set owner 42u64)",
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
        "(#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))",
        "(#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))\n          (#set owner 42u64)",
    );
    let error = graph_compile_error(
        &mutation_while_pending,
        "async-for-phase-mutation_while_pending",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the external shared loan must remain live while the composed task is Work::Pending: {error}"
    );

    let mutable_reference_source = shared_reference_source
        .replace(
            "(#fn work ((view (#ref #u64)))",
            "(#fn work ((view (#ref-mut #u64)))",
        )
        .replace(
            "(#assert (#u64::eq (#deref view) 41u64))",
            "(#deref-set view 42u64)",
        )
        .replace(
            "(#u64::eq (#deref view) 41u64)",
            "(#u64::eq (#deref view) 42u64)",
        )
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    let generated = build_and_run_graph(&mutable_reference_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let multi_await_source = mutable_reference_source.replace(
        "(#let body-ran #bool\n              (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll\n                (BodyTask.BodyWaiting iteration)))\n            (#deref-set view 42u64)\n            (#set total (#u64::add-wrap total 1u64))",
        "(#let body-ran #bool\n              (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll\n                (BodyTask.BodyWaiting iteration)))\n            (#let second-body-ran #bool\n              (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll\n                (BodyTask.BodyWaiting iteration)))\n            (#let third-body-ran #bool\n              (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll\n                (BodyTask.BodyWaiting iteration)))\n            (#deref-set view 42u64)\n            (#set total (#u64::add-wrap total 1u64))",
    );
    let (prefix, _) = multi_await_source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let mut poll_chain = "(#block (#forget pending-7) 0u64)".to_owned();
    for index in (0..7).rev() {
        let task = if index == 0 {
            "(#call work ((view (#borrow-mut owner))))".to_owned()
        } else {
            format!("pending-{index}")
        };
        let next = index + 1;
        poll_chain = format!(
            "(#match (#call Work::poll ((task {task}) (waker (#borrow waker))))\n\
               (#case (Work::Poll.Pending pending-{next}) {poll_chain})\n\
               (#case (Work::Poll.Ready ready-{index}) ready-{index}))"
        );
    }
    let multi_await_source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
  (#let-mut owner #u64 41u64)
  (#let waker #u64 0u64)
  (#let result #u64 {poll_chain})
  (#set owner 43u64)
  (#forget waker)
  (#return (#if (#u64::eq owner 43u64) result 0u64))
  );\n}}\n"
    );
    let generated = build_and_run_graph(&multi_await_source, 42);
    assert_single_poll(&generated, "Work::poll");
    let (prefix, _) = multi_await_source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let cancel_source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut owner #u64 41u64)
            (#let waker #u64 0u64)
            (#let task Work::Task (#call work ((view (#borrow-mut owner)))))
            (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
            (#let second Work::Poll
              (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending pending) Work::Poll second (#unreachable))
            (#forget pending)
            (#set owner 43u64)
            (#forget waker)
            (#return owner)
  );\n}}\n"
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
        "the multi-await body must retain the transferred exclusive loan while Work::Pending: {error}"
    );

    let (prefix, _) = mutable_reference_source
        .split_once("#fn main {\n  #params = ();\n  #returns = #u64;")
        .unwrap();
    let cancelled_mutable_reference = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut owner #u64 41u64)
            (#let waker #u64 0u64)
            (#let task Work::Task (#call work ((view (#borrow-mut owner)))))
            (#let first Work::Poll
              (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
            (#forget pending)
            (#set owner 42u64)
            (#forget waker)
            (#return (#if (#u64::eq owner 42u64) 42u64 0u64))
  );\n}}\n"
    );
    let generated = build_and_run_graph(&cancelled_mutable_reference, 42);
    assert_single_poll(&generated, "Work::poll");

    let pinned_reference_source = shared_reference_source
        .replace("(view (#ref #u64))", "(view (#pin-ref-mut #u64))")
        .replace("(#borrow owner)", "(#pin-borrow-mut owner)");
    let generated = build_and_run_graph(&pinned_reference_source, 42);
    assert_single_poll(&generated, "Work::poll");
    let (prefix, _) = pinned_reference_source
        .split_once("#fn main {\n  #params = ();\n  #returns = #u64;")
        .unwrap();
    let cancelled_pinned_reference = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let-mut owner #u64 41u64)
            (#let view (#pin-ref-mut #u64) (#pin-borrow-mut owner))
            (#let waker #u64 0u64)
            (#let task Work::Task (#call work ((view view))))
            (#let first Work::Poll
              (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
            (#forget pending)
            (#set owner 42u64)
            (#forget waker)
            (#return (#if (#u64::eq owner 42u64) 42u64 0u64))
  );\n}}\n"
    );
    let generated = build_and_run_graph(&cancelled_pinned_reference, 42);
    assert_single_poll(&generated, "Work::poll");

    let mutation_while_pending = mutable_reference_source.replace(
        "(#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))",
        "(#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))\n          (#set owner 42u64)",
    );
    let error = graph_compile_error(
        &mutation_while_pending,
        "async-for-phase-mutation_while_pending",
    );
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    let error = error.message;
    assert!(
        error.contains("borrow") || error.contains("access"),
        "the external exclusive loan must remain live while the composed task is Work::Pending: {error}"
    );
}

#[test]
fn async_for_three_phase_transfers_preserve_continue_break_and_return() {
    let source = "#enum ConditionTask (#linear) ((ConditionTask.Waiting #u64) (ConditionTask.Resuming #u64))

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.Waiting iteration) (ConditionPoll.ConditionPending (ConditionTask.Resuming iteration)))
            (#case (ConditionTask.Resuming iteration)
              (ConditionPoll.ConditionReady (#u64::lt iteration 2u64)))))
  );
}
#enum BodyTask (#linear) ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #bool))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting iteration) (BodyPoll.BodyPending (BodyTask.BodyResuming iteration)))
            (#case (BodyTask.BodyResuming iteration) (BodyPoll.BodyReady true))))
  );
}
#enum StepTask (#linear) ((StepTask.StepWaiting #u64) (StepTask.StepResuming #u64))

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (StepTask.StepWaiting iteration)
              (#block (#assert (#u64::eq iteration 0u64))
                (StepPoll.StepPending (StepTask.StepResuming iteration))))
            (#case (StepTask.StepResuming iteration)
              (#block (#assert (#u64::eq iteration 0u64))
                (StepPoll.StepReady (#u64::add-wrap iteration 1u64))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for (#set iteration 0u64)
                  (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                    condition-poll (ConditionTask.Waiting iteration))
                  (#set iteration
                    (#await #u64 StepTask StepPoll.StepPending StepPoll.StepReady step-poll
                      (StepTask.StepWaiting iteration)))
              (#let body-ran #bool
                (#await #bool BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll
                  (BodyTask.BodyWaiting iteration)))
              (#if (#u64::eq iteration 0u64) (#continue) (#break)))
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task second-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending third-pending) Work::Poll third (#unreachable))
          (#let fourth Work::Poll (#call Work::poll ((task third-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending fourth-pending) Work::Poll fourth (#unreachable))
          (#let fifth Work::Poll (#call Work::poll ((task fourth-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending fifth-pending) Work::Poll fifth (#unreachable))
          (#let sixth Work::Poll (#call Work::poll ((task fifth-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match sixth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending sixth-pending)
                (#block
                  (#let seventh Work::Poll
                    (#call Work::poll ((task sixth-pending) (waker (#borrow waker)))))
                  (#match seventh
                    (#case (Work::Poll.Ready value) value)
                    (#case (Work::Poll.Pending unexpected)
                      (#block (#forget unexpected) 77u64)))))))
          (#forget waker)
          (#return (#if (#u64::eq result 1u64) 42u64 0u64))\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");

    let return_source = source
        .replace(
            "(#if (#u64::eq iteration 0u64) (#continue) (#break))",
            "(#if true (#return 42u64) ())",
        )
        .replace("(#assert (#u64::eq iteration 0u64))", "(#assert false)")
        .replace(
            "(#return iteration))))",
            "(#assert false) (#return iteration))))",
        );
    let (prefix, _) = return_source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let mut poll_chain = "(#block (#forget pending-8) 0u64)".to_owned();
    for index in (0..8).rev() {
        let task = if index == 0 {
            "(#call work ())".to_owned()
        } else {
            format!("pending-{index}")
        };
        poll_chain = format!(
            "(#match (#call Work::poll ((task {task}) (waker (#borrow waker))))
              (#case (Work::Poll.Pending pending-{next}) {poll_chain})
              (#case (Work::Poll.Ready ready-{index}) ready-{index}))",
            next = index + 1,
        );
    }
    let return_source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let result #u64 {poll_chain})
            (#forget waker)
            (#return result)
  );\n}}\n"
    );
    let generated = build_and_run_graph(&return_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let linear_prefix = prefix
        .replace(
            "#enum ConditionTask (#linear)",
            "#struct Payload (#linear) ((value #u64))\n      \n#enum ConditionTask (#linear)",
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
            "(#call work ())".to_owned()
        } else {
            format!("pending-{index}")
        };
        linear_poll_chain = format!(
            "(#match (#call Work::poll ((task {task}) (waker (#borrow waker))))
              (#case (Work::Poll.Pending pending-{next}) {linear_poll_chain})
              (#case (Work::Poll.Ready ready-{index})
                (#block
                  (#let result #u64 (#get ready-{index} value))
                  (#forget ready-{index})
                  result)))",
            next = index + 1,
        );
    }
    let linear_return_source = format!(
        "{linear_prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let result #u64 {linear_poll_chain})
            (#forget waker)
            (#return result)
  );\n}}\n"
    );
    let generated = build_and_run_graph(&linear_return_source, 42);
    assert_single_poll(&generated, "Work::poll");
    assert_generated_type_names_are_capitalized(&generated);
}

#[test]
fn async_for_condition_awaits_only_the_selected_branch_each_iteration() {
    let source = "#enum ChildTask (#linear) (ChildTask.Waiting ChildTask.Resuming)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Waiting (ChildPoll.ChildPending ChildTask.Resuming))
            (#case ChildTask.Resuming (ChildPoll.ChildReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut should-await #bool true)
            (#for ()
                  (#bool::and should-await
                    (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                      ChildTask.Waiting))
                  (#set should-await false)
              (#assert true))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_loop_short_circuit_conditions_do_not_poll_unselected_awaits() {
    let source = "#enum ChildTask (#linear) (ChildTask.Waiting)

#enum ChildPoll (#linear) ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#forget task)
          (#assert false)
          (#return (ChildPoll.ChildReady true))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while
              (#bool::and false
                (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting))
              (#assert false))
            (#for ()
                  (#bool::or true
                    (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting))
                  ()
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let result Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let value #u64
            (#match result
              (#case (Work::Poll.Ready ready) ready)
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 0u64))))
          (#forget waker)
          (#return value)\n  );\n}\n";
    build_and_run(source, 42);
}

#[test]
fn async_while_let_resumes_a_body_await_only_after_the_pattern_matches() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ConditionTask (#linear) (ConditionTask.ConditionWaiting ConditionTask.ConditionResuming)

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady Maybe))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case ConditionTask.ConditionWaiting (ConditionPoll.ConditionPending ConditionTask.ConditionResuming))
            (#case ConditionTask.ConditionResuming (ConditionPoll.ConditionReady (Maybe.Some 42u64)))))
  );
}
#enum BodyTask (#linear) (BodyTask.BodyWaiting BodyTask.BodyResuming)

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case BodyTask.BodyWaiting (BodyPoll.BodyPending BodyTask.BodyResuming))
            (#case BodyTask.BodyResuming (BodyPoll.BodyReady 7u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#while-let (Maybe.Some payload)
              (#await Maybe ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll ConditionTask.ConditionWaiting)
              (#let result #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll BodyTask.BodyWaiting))
              (#assert (#u64::eq payload 42u64))
              (#assert (#u64::eq result 7u64))
              (#match payload
                (#case 42u64 (#break))
                (#case _ (#continue))))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending body-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task body-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");

    let conditional_source = source.replace(
        "(#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll BodyTask.BodyWaiting)",
        "(#if true\n                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll BodyTask.BodyWaiting)\n                7u64)",
    );
    let generated = build_and_run_graph(&conditional_source, 42);
    assert_single_poll(&generated, "Work::poll");

    let (prefix, _) = source.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let unmatched_source = format!(
        "{}{}",
        prefix
            .replace("(ConditionPoll.ConditionReady (Maybe.Some 42u64))", "(ConditionPoll.ConditionReady Maybe.None)")
            .replace(
                "#fn body-poll {\n  #params = ((task BodyTask) (waker (#ref #u64)));\n  #returns = BodyPoll;\n  #body = (\n          (#return (#match task\n            (#case BodyTask.BodyWaiting (BodyPoll.BodyPending BodyTask.BodyResuming))\n            (#case BodyTask.BodyResuming (BodyPoll.BodyReady 7u64))))\n  );\n}",
                "#fn body-poll {\n  #params = ((task BodyTask) (waker (#ref #u64)));\n  #returns = BodyPoll;\n  #body = (\n          (#forget task)\n          (#return (BodyPoll.BodyPending BodyTask.BodyWaiting))\n  );\n}",
            ),
        "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n"
    );
    build_and_run_graph(&unmatched_source, 42);
}

#[test]
fn async_while_let_carries_named_copy_aggregate_to_body_task() {
    let source = "#struct Captures () ((left #u64) (right #u64))
#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum ConditionTask (#linear) (ConditionTask.ConditionWaiting ConditionTask.ConditionResuming)

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady Maybe))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case ConditionTask.ConditionWaiting (ConditionPoll.ConditionPending ConditionTask.ConditionResuming))
            (#case ConditionTask.ConditionResuming (ConditionPoll.ConditionReady (Maybe.Some 1u64)))))
  );
}
#enum BodyTask (#linear) ((BodyTask.BodyWaiting Captures) (BodyTask.BodyResuming Captures))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting captures) (BodyPoll.BodyPending (BodyTask.BodyResuming captures)))
            (#case (BodyTask.BodyResuming captures)
              (BodyPoll.BodyReady (#u64::add-wrap
                (#get captures left) (#get captures right))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((captures Captures)) #u64
            (#let-mut total #u64 0u64)
            (#while-let (Maybe.Some payload)
              (#await Maybe ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll ConditionTask.ConditionWaiting)
              (#let result #u64
                (#await #u64 BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting captures)))
              (#set total (#u64::add-wrap payload result))
              (#break))
            (#return total))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let captures Captures
            (#struct-literal Captures ((left 20u64) (right 22u64))))
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((captures captures)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending condition-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll
            ((task condition-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending body-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task body-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 43);
    assert_single_poll(&generated, "Work::poll");

    let linear_source = source.replace(
        "#struct Captures () ((left #u64) (right #u64))",
        "#struct Captures (#linear) ((left #u64) (right #u64))\n ",
    );
    let error = graph_compile_error(&linear_source, "async-while-let-linear-captures");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(error.message.contains("captures"), "{error:?}");
    assert!(
        error.span.is_some(),
        "linear aggregate error must retain source location: {error:?}"
    );
}

#[test]
fn async_while_condition_composes_multiple_body_awaits_in_a_child_frame() {
    let source = "#struct Captures () ((left #u64) (right #u64))
#struct Counter (#linear) ((value (#atomic #u64)))

#fn counter-create {
  #params = ();
  #returns = Counter;
  #body = (
          (#return (#struct-literal Counter ((value (#atomic-init #u64 1u64)))))
  );
}
#fn counter-get {
  #params = ((counter (#ref Counter)));
  #returns = #u64;
  #body = (
          (#return (#atomic-load (#borrow (#get counter value)) #memory-relaxed))
  );
}
#fn counter-clear {
  #params = ((counter (#ref Counter)));
  #returns = ();
  #body = (
          (#atomic-store (#borrow (#get counter value)) 0u64 #memory-relaxed)
          (#return ())
  );
}
#enum ChildTask (#linear) ((ChildTask.Waiting #u64) (ChildTask.Resuming #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))

#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value) (ChildPoll.ChildPending (ChildTask.Resuming value)))
            (#case (ChildTask.Resuming value) (ChildPoll.ChildReady value))))
  );
}
#enum ConditionTask () ((ConditionTask.ConditionWaiting (#ref Counter)))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting counter)
              (#if (#u64::eq (#call counter-get ((counter counter))) 0u64)
                (ConditionPoll.ConditionReady false)
                (#block
                  (#call counter-clear ((counter counter)))
                  (ConditionPoll.ConditionReady true))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((counter (#ref Counter)) (captures Captures) (view (#ref #u64)) (#mut total #u64)) #u64
            (#while (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll
                      (ConditionTask.ConditionWaiting counter))
              (#let-mut subtotal #u64 0u64)
              (#let-mut inner-iterations #u64 0u64)
              (#while (#u64::eq inner-iterations 0u64)
                (#set inner-iterations 1u64)
                (#break))
              (#let first #u64
                (#await ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                  (ChildTask.Waiting (#u64::add-wrap (#get captures left) (#deref view)))))
              (#let second #u64
                (#await ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                  (ChildTask.Waiting (#u64::add-wrap (#get captures right) (#deref view)))))
              (#set subtotal (#u64::add-wrap first second))
              (#set total (#u64::add-wrap total subtotal)))
            (#return (#u64::add-wrap
              (#u64::add-wrap total (#get captures left))
              (#u64::add-wrap (#get captures right) (#deref view)))))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let counter Counter (#call counter-create ()))
          (#let captures Captures
            (#struct-literal Captures ((left 20u64) (right 22u64))))
          (#let-mut view-owner #u64 1u64)
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work
              ((counter (#borrow counter)) (captures captures) (view (#borrow view-owner)) (total 0u64))))
              (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-again) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task pending-again) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending task) (#block (#forget task) 0u64))))
          (#forget counter)
          (#set view-owner 0u64)
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 87);
    assert_single_poll(&generated, "Work::poll");

    let linear_capture_source = source.replace(
        "#struct Captures () ((left #u64) (right #u64))",
        "#struct Captures (#linear) ((left #u64) (right #u64))\n ",
    );
    let error = graph_compile_error(&linear_capture_source, "async-loop-linear-captures");
    assert_eq!(error.code, lim::DiagnosticCode::Linear, "{error:?}");
    assert!(error.message.contains("captures"), "{error:?}");
    assert!(
        error.span.is_some(),
        "linear aggregate error must retain source location: {error:?}"
    );

    let pending_mutation = source.replace(
        "(#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))",
        "(#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))\n        (#set view-owner 9u64)",
    );
    let error = graph_compile_error(&pending_mutation, "async-loop-pending-mutation");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error
        .span
        .expect("pending external loan mutation has a source span");
    assert_eq!(&pending_mutation[span.start..span.end], "#set");
    assert_eq!(
        span.start,
        pending_mutation.find("#set view-owner 9u64").unwrap()
    );

    let continue_source = source.replace(
        "(#set total (#u64::add-wrap total subtotal)))",
        "(#set total (#u64::add-wrap total subtotal))\n            (#continue))",
    );
    build_and_run_graph(&continue_source, 87);

    let break_source = source.replace(
        "(#set total (#u64::add-wrap total subtotal)))",
        "(#set total (#u64::add-wrap total subtotal))\n            (#break))",
    );
    build_and_run_graph(&break_source, 87);

    let branch_continue_source = source.replace(
        "(#set total (#u64::add-wrap total subtotal)))",
        "(#set total (#u64::add-wrap total subtotal))\n            (#if (#u64::eq first 21u64) (#continue) (#break)))",
    );
    build_and_run_graph(&branch_continue_source, 87);

    let branch_break_source = source.replace(
        "(#set total (#u64::add-wrap total subtotal)))",
        "(#set total (#u64::add-wrap total subtotal))\n            (#if (#u64::eq first 21u64) (#break) (#continue)))",
    );
    build_and_run_graph(&branch_break_source, 87);

    let match_continue_source = source.replace(
        "(#set total (#u64::add-wrap total subtotal)))",
        "(#set total (#u64::add-wrap total subtotal))\n            (#match first (#case 21u64 (#continue)) (#case _ (#break))))",
    );
    build_and_run_graph(&match_continue_source, 87);

    let conditional_await_source = source.replace(
        "(#await ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll\n                (ChildTask.Waiting (#get captures right)))",
        "(#if true\n                (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll\n                  (ChildTask.Waiting (#get captures right)))\n                0u64)",
    );
    build_and_run_graph(&conditional_await_source, 87);
}

#[test]
fn async_while_condition_awaits_only_the_selected_branch_each_iteration() {
    let source = "#enum ChildTask (#linear) (ChildTask.Waiting ChildTask.Resuming)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Waiting (ChildPoll.ChildPending ChildTask.Resuming))
            (#case ChildTask.Resuming (ChildPoll.ChildReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut should-await #bool true)
            (#while
              (#bool::and should-await
                (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting))
              (#set should-await false))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(&source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_while_body_binding_awaits_only_the_selected_branch() {
    let source = "#enum ChildTask (#linear) (ChildTask.Waiting ChildTask.Resuming)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Waiting (ChildPoll.ChildPending ChildTask.Resuming))
            (#case ChildTask.Resuming (ChildPoll.ChildReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut keep-going #bool true)
            (#while keep-going
              (#let result #bool
                (#if keep-going
                  (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting)
                  false))
              (#set keep-going false)
              (#assert result))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_loop_sequences_two_awaits_in_one_iteration() {
    let source = "#enum SecondTask (#linear) ((SecondTask.SecondWaiting #u64) (SecondTask.SecondResuming #u64))

#enum SecondPoll () ((SecondPoll.SecondPending SecondTask) (SecondPoll.SecondReady #u64))
#fn second-poll {
  #params = ((task SecondTask) (waker (#ref #u64)));
  #returns = SecondPoll;
  #body = (
          (#return (#match task
            (#case (SecondTask.SecondWaiting value) (SecondPoll.SecondPending (SecondTask.SecondResuming value)))
            (#case (SecondTask.SecondResuming value) (SecondPoll.SecondReady (#u64::add-wrap value 2u64)))))
  );
}
#enum FirstTask (#linear) (FirstTask.FirstWaiting FirstTask.FirstResuming)

#enum FirstPoll () ((FirstPoll.FirstPending FirstTask) (FirstPoll.FirstReady #u64))
#fn first-poll {
  #params = ((task FirstTask) (waker (#ref #u64)));
  #returns = FirstPoll;
  #body = (
          (#return (#match task
            (#case FirstTask.FirstWaiting (FirstPoll.FirstPending FirstTask.FirstResuming))
            (#case FirstTask.FirstResuming (FirstPoll.FirstReady 40u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut keep-going #bool true)
            (#while keep-going
              (#let next-value #u64
                (#await FirstTask FirstPoll.FirstPending FirstPoll.FirstReady first-poll FirstTask.FirstWaiting))
              (#assert (#u64::eq next-value 40u64))
              (#let result #u64
                (#await SecondTask SecondPoll.SecondPending SecondPoll.SecondReady second-poll (SecondTask.SecondWaiting next-value)))
              (#set keep-going false)
              (#assert (#u64::eq result 42u64)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll
            (#call Work::poll ((task second-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_loop_sequences_three_adjacent_awaits_in_one_iteration() {
    let source = "#enum ThirdTask (#linear) (ThirdTask.ThirdWaiting ThirdTask.ThirdResuming)

#enum ThirdPoll () ((ThirdPoll.ThirdPending ThirdTask) (ThirdPoll.ThirdReady #u64))
#fn third-poll {
  #params = ((task ThirdTask) (waker (#ref #u64)));
  #returns = ThirdPoll;
  #body = (
          (#return (#match task
            (#case ThirdTask.ThirdWaiting (ThirdPoll.ThirdPending ThirdTask.ThirdResuming))
            (#case ThirdTask.ThirdResuming (ThirdPoll.ThirdReady 42u64))))
  );
}
#enum SecondTask (#linear) (SecondTask.SecondWaiting SecondTask.SecondResuming)

#enum SecondPoll () ((SecondPoll.SecondPending SecondTask) (SecondPoll.SecondReady ThirdTask))
#fn second-poll {
  #params = ((task SecondTask) (waker (#ref #u64)));
  #returns = SecondPoll;
  #body = (
          (#return (#match task
            (#case SecondTask.SecondWaiting (SecondPoll.SecondPending SecondTask.SecondResuming))
            (#case SecondTask.SecondResuming (SecondPoll.SecondReady ThirdTask.ThirdWaiting))))
  );
}
#enum FirstTask (#linear) (FirstTask.FirstWaiting FirstTask.FirstResuming)

#enum FirstPoll () ((FirstPoll.FirstPending FirstTask) (FirstPoll.FirstReady SecondTask))
#fn first-poll {
  #params = ((task FirstTask) (waker (#ref #u64)));
  #returns = FirstPoll;
  #body = (
          (#return (#match task
            (#case FirstTask.FirstWaiting (FirstPoll.FirstPending FirstTask.FirstResuming))
            (#case FirstTask.FirstResuming (FirstPoll.FirstReady SecondTask.SecondWaiting))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut keep-going #bool true)
            (#while keep-going
              (#let second-task SecondTask
                (#await FirstTask FirstPoll.FirstPending FirstPoll.FirstReady first-poll FirstTask.FirstWaiting))
              (#let third-task ThirdTask
                (#await SecondTask SecondPoll.SecondPending SecondPoll.SecondReady second-poll second-task))
              (#let result #u64
                (#await ThirdTask ThirdPoll.ThirdPending ThirdPoll.ThirdReady third-poll third-task))
              (#set keep-going false)
              (#assert (#u64::eq result 42u64)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task first-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll
            (#call Work::poll ((task second-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending third-pending) Work::Poll third (#unreachable))
          (#let fourth Work::Poll
            (#call Work::poll ((task third-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match fourth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_initializer_awaits_once_before_entering_the_loop() {
    let source = "#enum InitTask (#linear) ((InitTask.Waiting #u64) (InitTask.Resuming #u64))

#enum InitPoll () ((InitPoll.InitPending InitTask) (InitPoll.InitReady #u64))
#fn init-poll {
  #params = ((task InitTask) (waker (#ref #u64)));
  #returns = InitPoll;
  #body = (
          (#return (#match task
            (#case (InitTask.Waiting count)
              (InitPoll.InitPending (InitTask.Resuming count)))
            (#case (InitTask.Resuming count)
              (InitPoll.InitReady (#u64::add-wrap count 2u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut total #u64 0u64)
            (#for (#let-mut iteration #u64
                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64)))
                  (#u64::lt iteration 3u64)
                  (#set iteration (#u64::add-wrap iteration 1u64))
              (#set total (#u64::add-wrap total iteration)))
            (#return (#if (#u64::eq total 2u64) 42u64 0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert!(generated.contains("InitPoll.InitPending"), "{generated}");

    let conditional_initializer = source
        .replace(
            "(#let-mut iteration #u64\n                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64)))",
            "(#let-mut iteration #u64\n                  (#if false\n                    (#await #u64 InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64))\n                    2u64))",
        )
        .replace(
            "(#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))\n          (#let second Work::Poll\n            (#call Work::poll ((task pending) (waker (#borrow waker)))))\n          (#let result #u64\n            (#match second\n              (#case (Work::Poll.Ready value) value)\n              (#case (Work::Poll.Pending unexpected)\n                (#block (#forget unexpected) 0u64))))",
            "(#let result #u64\n          (#match first\n            (#case (Work::Poll.Ready value) value)\n            (#case (Work::Poll.Pending unexpected)\n              (#block (#forget unexpected) 0u64))))",
    );
    assert_ne!(conditional_initializer, source);
    let generated = build_and_run_graph(&conditional_initializer, 42);
    assert!(
        generated_contains_form(&generated, "(#fn Work::poll)"),
        "{generated}"
    );

    let nested_initializer = source.replace(
        "(#let-mut iteration #u64\n                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64)))",
        "(#let-mut iteration #u64\n                  (#u64::add-wrap 0u64 (#await #u64 InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64))))",
    );
    let generated = build_and_run_graph(&nested_initializer, 42);
    assert!(generated.contains("InitPoll.InitPending"), "{generated}");

    let multiple_nested_initializers = source
        .replace("(#u64::lt iteration 3u64)", "(#u64::lt iteration 5u64)")
        .replace("(#u64::eq total 2u64)", "(#u64::eq total 4u64)")
        .replace(
            "(#let-mut iteration #u64\n                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64)))",
            "(#let-mut iteration #u64\n                  (#u64::add-wrap\n                    (#await #u64 InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64))\n                    (#await #u64 InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64))))",
        )
        .replace(
            "(#let result #u64\n            (#match second\n              (#case (Work::Poll.Ready value) value)\n              (#case (Work::Poll.Pending unexpected)\n                (#block (#forget unexpected) 0u64))))",
            "(#let-else (Work::Poll.Pending second-pending) Work::Poll second (#unreachable))\n          (#let third Work::Poll\n            (#call Work::poll ((task second-pending) (waker (#borrow waker)))))\n          (#let result #u64\n            (#match third\n              (#case (Work::Poll.Ready value) value)\n              (#case (Work::Poll.Pending unexpected)\n                (#block (#forget unexpected) 0u64))))",
        );
    assert_ne!(multiple_nested_initializers, source);
    let generated = build_and_run_graph(&multiple_nested_initializers, 42);
    assert!(generated.contains("InitPoll.InitPending"), "{generated}");

    let initializer_then_body_await = source
        .replace(
            "(#case (InitTask.Waiting count)\n              (InitPoll.InitPending (InitTask.Resuming count)))",
            "(#case (InitTask.Waiting count)\n            (#if (#u64::eq count 0u64)\n              (InitPoll.InitPending (InitTask.Resuming count))\n              (InitPoll.InitReady count)))",
        )
        .replace(
            "(#set total (#u64::add-wrap total iteration))",
            "(#let body-value #u64\n              (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting iteration)))\n            (#set total (#u64::add-wrap total body-value))",
        );
    let generated = build_and_run_graph(&initializer_then_body_await, 42);
    assert!(generated.contains("InitPoll.InitPending"), "{generated}");

    let initializer_then_condition_await = source
        .replace(
            "#generate #async-fn",
            "#enum ConditionTask (#linear) ((ConditionTask.ConditionStart #u64) (ConditionTask.ConditionResume #u64))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
  (#return (#match task
    (#case (ConditionTask.ConditionStart iteration) (ConditionPoll.ConditionPending (ConditionTask.ConditionResume iteration)))
    (#case (ConditionTask.ConditionResume iteration)
      (ConditionPoll.ConditionReady (#u64::lt iteration 3u64)))))
  );
}
#generate #async-fn",
        )
        .replace(
            "                  (#u64::lt iteration 3u64)\n                  (#set iteration",
            "                (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll (ConditionTask.ConditionStart iteration))\n                (#set iteration",
        )
        .replace("            (#let-mut total #u64 0u64)\n", "")
        .replace("            (#set total (#u64::add-wrap total iteration))", "            (#assert true)")
        .replace(
            "(#return (#if (#u64::eq total 2u64) 42u64 0u64))",
            "(#return 42u64)",
        )
        .replace(
            "(#let second Work::Poll\n            (#call Work::poll ((task pending) (waker (#borrow waker)))))\n          (#let result #u64\n            (#match second",
            "(#let second Work::Poll\n          (#call Work::poll ((task pending) (waker (#borrow waker)))))\n        (#let-else (Work::Poll.Pending condition-pending) Work::Poll second (#unreachable))\n        (#let third Work::Poll\n          (#call Work::poll ((task condition-pending) (waker (#borrow waker)))))\n        (#let-else (Work::Poll.Pending resumed-condition-pending) Work::Poll third (#unreachable))\n        (#let fourth Work::Poll\n          (#call Work::poll ((task resumed-condition-pending) (waker (#borrow waker)))))\n        (#let result #u64\n          (#match fourth",
        );
    assert_ne!(initializer_then_condition_await, source);
    assert!(initializer_then_condition_await.contains("#fn condition-poll"));
    assert!(initializer_then_condition_await.contains(
        "(#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll"
    ));
    let generated = build_and_run_graph(&initializer_then_condition_await, 42);
    assert!(
        generated.contains("ConditionPoll.ConditionPending"),
        "{generated}"
    );

    let protocol_typed_initializer = source.replace(
        "(#let-mut iteration #u64\n                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64)))",
        "(#let-mut iteration #u64\n                  (#u64::add-wrap 1u64 (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting 0u64))))",
    );
    // The child protocol supplies #u64 even inside the addition. Starting
    // at 1 + 2 means the loop is empty and total remains zero.
    let generated = build_and_run_graph(&protocol_typed_initializer, 0);
    assert_single_poll(&generated, "Work::poll");
    build_and_run_graph(
        &protocol_typed_initializer
            .replace("(#set total (#u64::add-wrap total iteration))", "(#panic)"),
        0,
    );

    let task_initializer = "#enum OuterTask (#linear) ((OuterTask.Waiting #u64) (OuterTask.Resuming #u64))

#enum OuterPoll () ((OuterPoll.OuterPending OuterTask) (OuterPoll.OuterReady #u64))
#fn outer-poll {
  #params = ((task OuterTask) (waker (#ref #u64)));
  #returns = OuterPoll;
  #body = (
          (#return (#match task
            (#case (OuterTask.Waiting value) (OuterPoll.OuterPending (OuterTask.Resuming value)))
            (#case (OuterTask.Resuming value) (OuterPoll.OuterReady value))))
  );
}
#enum InnerTask () (InnerTask.MakeOuter)
#enum InnerPoll () ((InnerPoll.InnerPending InnerTask) (InnerPoll.InnerReady OuterTask))
#fn inner-poll {
  #params = ((task InnerTask) (waker (#ref #u64)));
  #returns = InnerPoll;
  #body = (
          (#return (#match task
            (#case InnerTask.MakeOuter (InnerPoll.InnerReady (OuterTask.Waiting 42u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for (#let-mut initial #u64
                    (#await OuterTask OuterPoll.OuterPending OuterPoll.OuterReady outer-poll
                      (#await OuterTask InnerTask InnerPoll.InnerPending InnerPoll.InnerReady inner-poll InnerTask.MakeOuter)))
                  false
                  ()
              (#assert false))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(task_initializer, 42);
    assert!(!generated.contains("(#await"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_suspends_before_entering_the_loop() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum InitTask (#linear) (InitTask.Waiting InitTask.Resuming)

#enum InitPoll () ((InitPoll.InitPending InitTask) (InitPoll.InitReady Maybe))
#fn init-poll {
  #params = ((task InitTask) (waker (#ref #u64)));
  #returns = InitPoll;
  #body = (
          (#return (#match task
            (#case InitTask.Waiting (InitPoll.InitPending InitTask.Resuming))
            (#case InitTask.Resuming (InitPoll.InitReady (Maybe.Some 0u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for (#let-else (Maybe.Some index) Maybe
                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll InitTask.Waiting)
                    (#unreachable))
                  (#u64::lt index 1u64)
                  (#u64::add-wrap index 1u64)
              (#assert (#u64::eq index 0u64))
              (#break))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("InitPoll.InitPending"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_composes_with_a_suspending_body() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#type MaybeAlias Maybe
#enum InitTask (#linear) (InitTask.Waiting InitTask.Resuming)

#enum InitPoll () ((InitPoll.InitPending InitTask) (InitPoll.InitReady Maybe))
#fn init-poll {
  #params = ((task InitTask) (waker (#ref #u64)));
  #returns = InitPoll;
  #body = (
          (#return (#match task
            (#case InitTask.Waiting (InitPoll.InitPending InitTask.Resuming))
            (#case InitTask.Resuming (InitPoll.InitReady (Maybe.Some 9u64)))))
  );
}
#struct Resource (#linear) ((value #u64))

#fn Resource::destroy {
  #params = ((resource Resource));
  #returns = #u64;
  #body = (
          (#let result #u64 (#get resource value))
          (#forget resource)
          (#return result)
  );
}
#enum BodyTask (#linear) ((BodyTask.BodyWaiting #u64) (BodyTask.BodyResuming #u64))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady Resource))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.BodyWaiting value) (BodyPoll.BodyPending (BodyTask.BodyResuming value)))
            (#case (BodyTask.BodyResuming value)
              (#block (#forget value)
                (BodyPoll.BodyReady (#struct-literal Resource ((value 9u64))))))))
  );
}
#enum SecondBodyTask (#linear) (SecondBodyTask.SecondBodyWaiting SecondBodyTask.SecondBodyResuming)

#enum SecondBodyPoll () ((SecondBodyPoll.SecondBodyPending SecondBodyTask) (SecondBodyPoll.SecondBodyReady #u64))
#fn second-body-poll {
  #params = ((task SecondBodyTask) (waker (#ref #u64)));
  #returns = SecondBodyPoll;
  #body = (
          (#return (#match task
            (#case SecondBodyTask.SecondBodyWaiting (SecondBodyPoll.SecondBodyPending SecondBodyTask.SecondBodyResuming))
            (#case SecondBodyTask.SecondBodyResuming (SecondBodyPoll.SecondBodyReady 9u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64)
          (cancel (cancel-frame ((value cancel-resource)
            (await-0 cancel-initializer) (await-1 cancel-body-task)
            (await-2 cancel-second-body-task))))
          (function
          (#fn work () #u64
            (#let-mut done #bool false)
            (#for (#let-else (Maybe.Some index) MaybeAlias
                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll InitTask.Waiting)
                    (#unreachable))
                  (#bool::eq done false)
                  ()
              (#let value Resource
                (#await BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.BodyWaiting index)))
              (#let second-value #u64
                (#await SecondBodyTask SecondBodyPoll.SecondBodyPending SecondBodyPoll.SecondBodyReady
                  second-body-poll SecondBodyTask.SecondBodyWaiting))
              (#assert (#u64::eq second-value 9u64))
              (#let destroyed #u64 (#call Resource::destroy ((resource value))))
              (#assert (#u64::eq destroyed second-value))
              (#set done true))
            (#return 42u64))))
#fn cancel-initializer {
  #params = ((task InitTask));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#fn cancel-resource {
  #params = ((resource Resource));
  #returns = ();
  #body = (
          (#let destroyed #u64 (#call Resource::destroy ((resource resource))))
          (#assert (#u64::eq destroyed 9u64)) (#return ())
  );
}
#fn cancel-body-task {
  #params = ((task BodyTask));
  #returns = ();
  #body = (
          (#forget task)
          (#return ())
  );
}
#fn cancel-second-body-task {
  #params = ((task SecondBodyTask));
  #returns = ();
  #body = (
          (#forget task)
          (#return ())
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-init) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task after-init) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-body) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task after-body) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-second-body) Work::Poll third (#unreachable))
          (#let fourth Work::Poll (#call Work::poll ((task after-second-body) (waker (#borrow waker)))))
          (#let result #u64
            (#match fourth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#let cancel-task Work::Task (#call work ()))
          (#let cancel-first Work::Poll (#call Work::poll ((task cancel-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending cancel-after-init) Work::Poll cancel-first (#unreachable))
          (#let cancel-second Work::Poll
            (#call Work::poll ((task cancel-after-init) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending cancel-after-body) Work::Poll cancel-second (#unreachable))
          (#let cancel-third Work::Poll
            (#call Work::poll ((task cancel-after-body) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending cancel-after-second-body) Work::Poll cancel-third (#unreachable))
          (#call cancel-frame ((task (#call Work::Poll::cleanup ((task cancel-after-second-body))))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(&source, 42);
    assert!(generated.contains("BodyPoll.BodyPending"), "{generated}");
    let (prefix, _) = source.split_once("#fn main").unwrap();
    for polls in 0..=3 {
        let prefix = if polls < 3 {
            prefix.replace("(#assert (#u64::eq destroyed 9u64))", "(#assert false)")
        } else {
            prefix.to_owned()
        };
        let mut canceled = format!(
            "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let waker #u64 0u64)
              (#let state-0 Work::Task (#call work ()))\n"
        );
        for index in 0..polls {
            canceled.push_str(&format!(
                "
              (#let outcome-{index} Work::Poll
                (#call Work::poll ((task state-{index}) (waker (#borrow waker)))))
              (#let-else (Work::Poll.Pending state-{}) Work::Poll outcome-{index} (#unreachable))",
                index + 1
            ));
        }
        canceled.push_str(&format!(
            "
            (#call cancel-frame ((task (#call Work::Poll::cleanup ((task state-{polls}))))))
            (#forget waker) (#return 42u64)\n  );\n}}"
        ));
        build_and_run_graph(&canceled, 42);
    }
    let counted = prefix
        .replace(
            "#struct Resource (#linear) ((value #u64))",
            "#struct Resource (#linear) ((value #u64) (counter (#ref (#atomic #u64))))",
        )
        .replace("(#ref #u64)", "(#ref (#atomic #u64))")
        .replace("(waker #u64)", "(waker (#atomic #u64))")
        .replace(
            "(#struct-literal Resource ((value 9u64)))",
            "(#struct-literal Resource ((value 9u64) (counter waker)))",
        )
        .replace(
            "(#let result #u64 (#get resource value))",
            "(#atomic-store (#get resource counter)
          (#u64::add-wrap (#atomic-load (#get resource counter) #memory-relaxed) 1u64) #memory-relaxed)
          (#let result #u64 (#get resource value))",
        );
    for polls in 0..=3 {
        let mut canceled = format!(
            "{counted}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let waker (#atomic #u64) (#atomic-init #u64 0u64))
              (#let state-0 Work::Task (#call work ()))\n"
        );
        for index in 0..polls {
            canceled.push_str(&format!(
                "
              (#let outcome-{index} Work::Poll
                (#call Work::poll ((task state-{index}) (waker (#borrow waker)))))
              (#let-else (Work::Poll.Pending state-{}) Work::Poll outcome-{index} (#unreachable))",
                index + 1
            ));
        }
        let expected = u64::from(polls == 3);
        canceled.push_str(&format!(
            "
            (#call cancel-frame ((task (#call Work::Poll::cleanup ((task state-{polls}))))))
            (#assert (#u64::eq (#atomic-load (#borrow waker) #memory-relaxed) {expected}u64))
            (#forget waker) (#return 42u64)\n  );\n}}"
        ));
        build_and_run_graph(&canceled, 42);
        if polls == 3 {
            let conflicting = canceled
                .replace("(#forget waker) (#return 42u64)", "(#return 42u64)")
                .replace(
                    "(#assert (#u64::eq (#atomic-load (#borrow waker) #memory-relaxed) 1u64))",
                    "",
                )
                .replace("(#call cancel-frame", "(#forget waker) (#call cancel-frame");
            let error = graph_compile_error(&conflicting, "pending-resource-retains-poll-context");
            assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
            let span = error.span.unwrap();
            assert_eq!(&conflicting[span.start..span.end], "#forget");
        }
    }
}

#[test]
fn async_for_let_else_initializer_composes_with_an_awaited_step() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#type MaybeAlias Maybe
#enum InitTask (#linear) (InitTask.InitWaiting InitTask.InitResuming)

#enum InitPoll () ((InitPoll.InitPending InitTask) (InitPoll.InitReady Maybe))
#fn init-poll {
  #params = ((task InitTask) (waker (#ref #u64)));
  #returns = InitPoll;
  #body = (
          (#return (#match task
            (#case InitTask.InitWaiting (InitPoll.InitPending InitTask.InitResuming))
            (#case InitTask.InitResuming (InitPoll.InitReady (Maybe.Some 9u64)))))
  );
}
#enum StepTask (#linear) (StepTask.StepWaiting StepTask.StepResuming)

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #bool))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case StepTask.StepWaiting (StepPoll.StepPending StepTask.StepResuming))
            (#case StepTask.StepResuming (StepPoll.StepReady true))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut done #bool false)
            (#for (#let-else (Maybe.Some index) MaybeAlias
                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll InitTask.InitWaiting)
                    (#unreachable))
                  (#bool::eq done false)
                  (#set done
                    (#await #bool StepTask StepPoll.StepPending StepPoll.StepReady step-poll StepTask.StepWaiting))
              (#assert (#u64::eq index 9u64)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let task Work::Task (#call work ()))
          (#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-init) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task after-init) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending after-step) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task after-step) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPoll.StepPending"), "{generated}");
}

#[test]
fn async_for_let_else_initializer_returns_ready_on_mismatch() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum InitTask (#linear) ((InitTask.Waiting Maybe) (InitTask.Resuming Maybe))

#enum InitPoll () ((InitPoll.InitPending InitTask) (InitPoll.InitReady Maybe))
#fn init-poll {
  #params = ((task InitTask) (waker (#ref #u64)));
  #returns = InitPoll;
  #body = (
          (#return (#match task
            (#case (InitTask.Waiting value) (InitPoll.InitPending (InitTask.Resuming value)))
            (#case (InitTask.Resuming value) (InitPoll.InitReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe)) #u64
            (#for (#let-else (Maybe.Some index) Maybe
                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting input))
                    (#return 7u64))
                  false
                  ()
              ())
            (#return 35u64))))
#fn Work::poll-work {
  #params = ((input Maybe) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let task Work::Task (#call work ((input input))))
          (#let first Work::Poll (#call Work::poll ((task task) (waker waker))))
          (#return (#match first
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending pending) (#block
              (#let second Work::Poll (#call Work::poll ((task pending) (waker waker))))
              (#match second
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64)))))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let mismatch #u64 (#call Work::poll-work ((input Maybe.None) (waker (#borrow waker)))))
          (#let matched #u64 (#call Work::poll-work ((input (Maybe.Some 7u64)) (waker (#borrow waker)))))
          (#forget waker)
          (#return (#u64::add-wrap mismatch matched))\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_let_else_initializer_can_suspend_in_condition() {
    let source = "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#enum InitTask (#linear) ((InitTask.Waiting Maybe) (InitTask.Resuming Maybe))

#enum InitPoll () ((InitPoll.InitPending InitTask) (InitPoll.InitReady Maybe))
#fn init-poll {
  #params = ((task InitTask) (waker (#ref #u64)));
  #returns = InitPoll;
  #body = (
          (#return (#match task
            (#case (InitTask.Waiting value) (InitPoll.InitPending (InitTask.Resuming value)))
            (#case (InitTask.Resuming value) (InitPoll.InitReady value))))
  );
}
#enum ConditionTask (#linear) ((ConditionTask.ConditionWaiting #bool) (ConditionTask.ConditionResuming #bool))

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting value) (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming value)))
            (#case (ConditionTask.ConditionResuming value) (ConditionPoll.ConditionReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((input Maybe) (condition #bool)) #u64
            (#let-mut body-ran #bool false)
            (#for (#let-else (Maybe.Some index) Maybe
                    (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.Waiting input))
                    (#return 7u64))
                  (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                    condition-poll (ConditionTask.ConditionWaiting condition))
                  ()
              (#set body-ran true)
              (#break))
            (#return (#if body-ran 43u64 42u64)))))\n";
    let source = format!(
        "{source}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let mismatch-task Work::Task (#call work ((input Maybe.None) (condition false))))
            (#let mismatch-first Work::Poll (#call Work::poll ((task mismatch-task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending mismatch-after-init) Work::Poll mismatch-first (#unreachable))
            (#let mismatch-second Work::Poll
              (#call Work::poll ((task mismatch-after-init) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Ready mismatch) Work::Poll mismatch-second (#unreachable))
            (#let false-task Work::Task (#call work ((input (Maybe.Some 7u64)) (condition false))))
            (#let false-first Work::Poll (#call Work::poll ((task false-task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending false-after-init) Work::Poll false-first (#unreachable))
            (#let false-second Work::Poll
              (#call Work::poll ((task false-after-init) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending false-after-condition-start) Work::Poll false-second (#unreachable))
            (#let false-third Work::Poll
              (#call Work::poll ((task false-after-condition-start) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Ready matched-false) Work::Poll false-third (#unreachable))
            (#let true-task Work::Task (#call work ((input (Maybe.Some 7u64)) (condition true))))
            (#let true-first Work::Poll (#call Work::poll ((task true-task) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending true-after-init) Work::Poll true-first (#unreachable))
            (#let true-second Work::Poll
              (#call Work::poll ((task true-after-init) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending true-after-condition-start) Work::Poll true-second (#unreachable))
            (#let true-third Work::Poll
              (#call Work::poll ((task true-after-condition-start) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Ready matched-true) Work::Poll true-third (#unreachable))
            (#forget waker)
            (#return (#u64::add-wrap mismatch
              (#u64::add-wrap matched-false matched-true)))\n  );\n}}\n"
    );
    let generated = build_and_run(&source, 92);
    assert!(
        generated.contains("ConditionPoll.ConditionPending"),
        "{generated}"
    );
}

#[test]
fn async_for_condition_and_step_await_preserve_body_continue_and_break() {
    let source =
        "#enum ConditionTask (#linear) ((ConditionTask.ConditionWaiting #u64) (ConditionTask.ConditionResuming #u64))

#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task
            (#case (ConditionTask.ConditionWaiting iteration)
              (ConditionPoll.ConditionPending (ConditionTask.ConditionResuming iteration)))
            (#case (ConditionTask.ConditionResuming iteration) (ConditionPoll.ConditionReady true))))
  );
}
#enum StepTask (#linear) ((StepTask.StepWaiting #u64) (StepTask.StepResuming #u64))

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (StepTask.StepWaiting iteration)
              (StepPoll.StepPending (StepTask.StepResuming iteration)))
            (#case (StepTask.StepResuming iteration)
              (StepPoll.StepReady (#u64::add-wrap iteration 1u64)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for ()
              (#await ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady
                condition-poll (ConditionTask.ConditionWaiting iteration))
              (#set iteration
                (#await #u64 StepTask StepPoll.StepPending StepPoll.StepReady step-poll
                  (StepTask.StepWaiting iteration)))
              (#if (#u64::eq iteration 0u64) (#continue) (#break)))
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-1) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending-1) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-2) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task pending-2) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-3) Work::Poll third (#unreachable))
          (#let fourth Work::Poll (#call Work::poll ((task pending-3) (waker (#borrow waker)))))
          (#let result #u64
            (#match fourth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 1);
    assert_single_poll(&generated, "Work::poll");

    let (prefix, _) = source
        .split_once("#fn main {\n  #params = ();\n  #returns = #u64;")
        .expect("async main function");
    let return_prefix = prefix.replace(
        "(#if (#u64::eq iteration 0u64) (#continue) (#break))",
        "(#return 42u64)",
    );
    let return_source = format!(
        "{return_prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let first Work::Poll
              (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
            (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
            (#let second Work::Poll
              (#call Work::poll ((task pending) (waker (#borrow waker)))))
            (#let result #u64
              (#match second
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected)
                  (#block (#forget unexpected) 0u64))))
            (#forget waker)
            (#return result)\n  );\n}}\n"
    );
    let returned = build_and_run_graph(&return_source, 42);
    assert_single_poll(&returned, "Work::poll");
}

#[test]
fn async_for_step_can_suspend_after_the_loop_body() {
    let source = "#enum StepTask (#linear) ((StepTask.Waiting #u64) (StepTask.Resuming #u64))

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (StepTask.Waiting iteration)
              (#block
                (#assert (#u64::eq (#u64::rem-wrap iteration 2u64) 1u64))
                (#if (#u64::eq iteration 1u64)
                  (StepPoll.StepPending (StepTask.Resuming iteration))
                  (StepPoll.StepReady (#u64::add-wrap iteration 1u64)))))
            (#case (StepTask.Resuming iteration)
              (#block
                (#assert (#u64::eq (#u64::rem-wrap iteration 2u64) 1u64))
                (StepPoll.StepReady (#u64::add-wrap iteration 1u64))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for (#set iteration 0u64)
                  (#u64::lt iteration 6u64)
                  (#set iteration
                    (#await StepTask StepPoll.StepPending StepPoll.StepReady step-poll
                      (StepTask.Waiting iteration)))
              (#set iteration (#u64::add-wrap iteration 1u64)))
            (#return (#if (#u64::eq iteration 6u64) 42u64 0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPoll.StepPending"), "{generated}");
}

#[test]
fn async_for_step_can_suspend_after_a_suspending_body() {
    let source = "#enum BodyTask (#linear) ((BodyTask.Waiting #u64) (BodyTask.Resuming #u64))

#enum BodyPoll () ((BodyPoll.BodyPending BodyTask) (BodyPoll.BodyReady #u64))
#fn body-poll {
  #params = ((task BodyTask) (waker (#ref #u64)));
  #returns = BodyPoll;
  #body = (
          (#return (#match task
            (#case (BodyTask.Waiting value) (BodyPoll.BodyPending (BodyTask.Resuming value)))
            (#case (BodyTask.Resuming value) (BodyPoll.BodyReady value))))
  );
}
#enum StepTask (#linear) (StepTask.Start StepTask.Resume)

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case StepTask.Start (StepPoll.StepPending StepTask.Resume))
            (#case StepTask.Resume (StepPoll.StepReady 1u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for (#set iteration 0u64)
                  (#u64::lt iteration 1u64)
              (#set iteration
                    (#await StepTask StepPoll.StepPending StepPoll.StepReady step-poll StepTask.Start))
              (#let body-value #u64
                (#await BodyTask BodyPoll.BodyPending BodyPoll.BodyReady body-poll (BodyTask.Waiting 42u64)))
              (#assert (#u64::eq body-value 42u64)))
            (#return (#if (#u64::eq iteration 1u64) 42u64 0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending body-pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task body-pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending step-pending) Work::Poll second (#unreachable))
          (#let third Work::Poll
            (#call Work::poll ((task step-pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match third
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_for_step_can_suspend_inside_assignment_expression() {
    let source = "#enum StepTask (#linear) (StepTask.Waiting StepTask.Resuming)

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case StepTask.Waiting (StepPoll.StepPending StepTask.Resuming))
            (#case StepTask.Resuming (StepPoll.StepReady 1u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for ()
                  (#u64::lt iteration 1u64)
                  (#set iteration
                    (#u64::add-wrap iteration
                      (#await #u64 StepTask StepPoll.StepPending StepPoll.StepReady step-poll StepTask.Waiting)))
              (#assert true))
            (#return (#if (#u64::eq iteration 1u64) 42u64 0u64)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run(source, 42);
    assert!(generated.contains("StepPoll.StepPending"), "{generated}");
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
            "(#return (#u64::add-wrap (#u64::add-wrap (#as left #u64) second) bias))",
            "(#u64::add-wrap (#u64::add-wrap (#as left #u64) second) bias))) (#return result)",
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
        "#struct Token (#linear) ((value #u64))\n \n{}",
        include_str!("../examples/async_pattern_blocks.lim")
            .replace("(a #u64)", "(a Token)")
            .replace("(a 22u64)", "(a (#struct-literal Token ((value 22u64))))")
            .replace(
                "(#let first #u64",
                "(#let bias-value #u64 (#get bias value)) (#forget bias) (#let first #u64",
            )
            .replace("first second) bias)", "first second) bias-value)")
    );
    build_and_run(&consumed_prefix, 47);
    build_and_run_graph(&consumed_prefix, 47);
    build_and_run(
        &consumed_prefix.replace(
            "(StepPoll.StepPending (Step.Resume value))",
            "(StepPoll.StepReady value)",
        ),
        47,
    );
    build_and_run(
        &consumed_prefix
            .replace("(StepPoll.StepPending (Step.Resume value))", "(#panic)")
            .replace("(choose true) (waker", "(choose false) (waker"),
        10,
    );
    let destructor = format!(
        "#fn destroy-token {{
  #params = ((token Token));
  #returns = #u64;
  #body = (
            (#let value #u64 (#get token value)) (#forget token) (#return value)\n  );
}}
{}",
        consumed_prefix.replace(
            "(#let bias-value #u64 (#get bias value)) (#forget bias)",
            "(#let bias-value #u64 (#call destroy-token ((token bias))))",
        )
    );
    build_and_run(&destructor, 47);
    build_and_run(include_str!("../examples/async_prefix_cleanup.lim"), 47);
    let first_child_only = consumed_prefix
        .replace(
            "(Step.Start (#as left #u64))",
            "(Step.Start (#u64::add-wrap (#as left #u64) bias-value))",
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
            "(Step.Start (#as left #u64))",
            "(Step.Start (#u64::add-wrap (#as left #u64) offset))",
        )
        .replace(
            "(choose choose) (values",
            "(choose choose) (offset 3u64) (values",
        );
    build_and_run(&outer_child_only, 50);
    let scratch = support::Scratch::new("async-prefix-ownership");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let error_for = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &config,
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
    assert!(
        !scratch.path().join("cache").exists(),
        "source ownership errors must precede generated cache publication"
    );
    let reused = error_for(&consumed_prefix.replace(
        "first second) bias-value)",
        "first second) (#get bias value))",
    ));
    assert_eq!(reused.code, lim::DiagnosticCode::Linear, "{reused:?}");
    assert!(reused.message.contains("bias"), "{reused:?}");
    let span = reused.span.expect("consumed source read must have a span");
    let invalid = consumed_prefix.replace(
        "first second) bias-value)",
        "first second) (#get bias value))",
    );
    assert!(invalid[span.start..span.end].contains("bias"), "{reused:?}");
    assert!(
        reused
            .labels
            .iter()
            .any(|label| invalid[label.span.start..label.span.end].contains("bias")),
        "the diagnostic must identify the original consumption: {reused:?}"
    );
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
            "(#return (#u64::add-wrap (#u64::add-wrap first second) bias))",
            "(#u64::add-wrap (#u64::add-wrap first second) bias))) (#return result)",
        );
    build_and_run(&block, 42);
    let branch = include_str!("../examples/async_pattern_blocks.lim");
    build_and_run(branch, 47);
    let immediate = branch.replace(
        "(StepPoll.StepPending (Step.Resume value))",
        "(StepPoll.StepReady value)",
    );
    build_and_run(&immediate, 47);
    let skipped = branch
        .replace("(StepPoll.StepPending (Step.Resume value))", "(#panic)")
        .replace("(choose true) (waker", "(choose false) (waker");
    build_and_run(&skipped, 10);
    let mutable = branch
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64::add-wrap bias 2u64)) (#let second #u64",
        );
    build_and_run(&mutable, 49);
    let bool_tail = block
        .replace("(a #u64)", "(a #bool)")
        .replace("(a 22u64)", "(a true)")
        .replace(
            "(#fn work ((values Values)) #u64",
            "(#fn work ((values Values)) #bool",
        )
        .replace("(#let result #u64", "(#let result #bool")
        .replace(
            "(#u64::add-wrap (#u64::add-wrap first second) bias)",
            "bias",
        )
        .replace("(#return value)", "(#return (#if value 42u64 0u64))");
    build_and_run(&bool_tail, 42);
    let owned = format!("#struct Token (#linear) ((value #u64))\n \n{}", branch
        .replace("(a #u64)", "(a Token)")
        .replace("(a 22u64)", "(a (#struct-literal Token ((value 22u64))))")
        .replace("(#u64::add-wrap (#u64::add-wrap first second) bias))", "(#let total #u64 (#u64::add-wrap (#u64::add-wrap first second) (#get bias value))) (#forget bias) total)"));
    build_and_run(&owned, 47);
    let referenced = branch
        .replace("(#tuple #u16 #u16)", "(#tuple #u16 (#ref #u64))")
        .replace("(#as right #u64)", "(#deref right)")
        .replace(
            "(#let-mut task Work::Task",
            "(#let-mut owner #u64 11u64) (#let-mut task Work::Task",
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
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    let immediate = source.replace(
        "(InputPoll.InputPending (InputTask.InputResume values))",
        "(InputPoll.InputReady values)",
    );
    build_and_run_graph(&immediate, 42);
    let without_result_type = source.replace("(#await Values InputTask", "(#await InputTask");
    build_and_run_graph(&without_result_type, 42);
    let aliased = format!(
        "#type ValuesAlias Values\n{}",
        source
            .replace("(values Values)", "(values ValuesAlias)")
            .replace("bias) Values\n", "bias) ValuesAlias\n")
            .replace("(#await Values InputTask", "(#await ValuesAlias InputTask")
    );
    build_and_run_graph(&aliased, 42);
    let mutable = source
        .replace("(#let (Values", "(#let-mut (Values")
        .replace("(#let second #u64", "(#set bias (#u64::add-wrap bias 2u64)) (#set right (#u16::add-wrap right 1u16)) (#let second #u64");
    build_and_run_graph(&mutable, 45);
    let array = source
        .replace("(#tuple #u16 #u16)", "(#array #u16 2)")
        .replace("(#tuple left right)", "(#array left right)")
        .replace(
            "(#tuple (#array #u16 2) 9u16 11u16)",
            "(#array-of (#array #u16 2) 9u16 11u16)",
        );
    build_and_run_graph(&array, 42);
    let tuple = source
        .replace(
            "#struct Values () ((z (#tuple #u16 #u16)) (a #u64))",
            "#type Values (#tuple (#tuple #u16 #u16) #u64)",
        )
        .replace(
            "(Values (#tuple left right) bias)",
            "(#tuple (#tuple left right) bias)",
        )
        .replace(
            "(#struct-literal Values ((a 22u64) (z (#tuple (#tuple #u16 #u16) 9u16 11u16))))",
            "(#tuple (#tuple (#tuple #u16 #u16) #u64) (#tuple (#tuple #u16 #u16) 9u16 11u16) 22u64)",
        );
    build_and_run_graph(&tuple, 42);
    let single_variant = source
        .replace(
            "#struct Values () ((z (#tuple #u16 #u16)) (a #u64))",
            "#enum Values () ((Values.Only (#tuple (#tuple #u16 #u16) #u64)))",
        )
        .replace(
            "(Values (#tuple left right) bias)",
            "(Values.Only (#tuple (#tuple left right) bias))",
        )
        .replace("(#let (Values.Only", "(#let-else (Values.Only")
        .replace(
            "input-poll (InputTask.InputStart values)))",
            "input-poll (InputTask.InputStart values)) (#unreachable))",
        )
        .replace(
            "(#struct-literal Values ((a 22u64) (z (#tuple (#tuple #u16 #u16) 9u16 11u16))))",
            "(Values.Only (#tuple (#tuple (#tuple #u16 #u16) #u64) (#tuple (#tuple #u16 #u16) 9u16 11u16) 22u64))",
        );
    build_and_run_graph(&single_variant, 42);
    let enum_options = single_variant
        .replace(
            "#enum Values () ((Values.Only (#tuple (#tuple #u16 #u16) #u64)))",
            "#enum Values () ((Values.Only (#tuple (#tuple #u16 #u16) #u64)) Values.Missing)",
        )
        .replace(
            "input-poll (InputTask.InputStart values)) (#unreachable))",
            "input-poll (InputTask.InputStart values)) (#return 5u64))",
        );
    assert!(enum_options.contains("Values.Missing"));
    build_and_run_graph(&enum_options, 42);
    let mismatched = enum_options
        .replace(
            "(Values.Only (#tuple (#tuple (#tuple #u16 #u16) #u64) (#tuple (#tuple #u16 #u16) 9u16 11u16) 22u64))",
            "Values.Missing",
        )
        .replace("(StepPoll.StepPending (Step.Resume value))", "(#panic)");
    build_and_run_graph(&mismatched, 5);
    let owned = format!("#struct Token (#linear) ((value #u64))\n \n{}", source
        .replace("(a #u64)", "(a Token)")
        .replace("(a 22u64)", "(a (#struct-literal Token ((value 22u64))))")
        .replace("(#return (#u64::add-wrap (#u64::add-wrap (#as left #u64) second) bias))", "(#let total #u64 (#u64::add-wrap (#u64::add-wrap (#as left #u64) second) (#get bias value))) (#forget bias) (#return total)"));
    build_and_run_graph(&owned, 42);
    let effect = format!(
        "#fn make-input {{
  #params = ((values Values) (count (#ref-mut #u64)));
  #returns = InputTask;
  #body = (
        (#deref-set count (#u64::add-wrap (#deref count) 1u64))
        (#return (InputTask.InputStart values))\n  );
}}
{}",
        source
            .replace(
                "(#fn work ((values Values))",
                "(#fn work ((values Values) (counter (#ref-mut #u64)))"
            )
            .replace(
                "input-poll (InputTask.InputStart values)",
                "input-poll (#call make-input ((values values) (count counter)))"
            )
            .replace(
                "(#let waker #u64",
                "(#let-mut touches #u64 0u64) (#let waker #u64"
            )
            .replace(
                "(#call work ((values",
                "(#call work ((counter (#borrow-mut touches)) (values"
            )
            .replace(
                "(#block (#return value))",
                "(#block (#assert (#u64::eq touches 1u64)) (#return value))"
            )
    );
    build_and_run_graph(&effect, 42);
    let factory = format!("#enum Factory () ((Factory.FactoryStart Values) (Factory.FactoryResume Values))
#enum FactoryPoll () ((FactoryPoll.FactoryPending Factory) (FactoryPoll.FactoryReady InputTask))
#fn factory-poll {{
  #params = ((task Factory) (waker (#ref #u64)));
  #returns = FactoryPoll;
  #body = (
          (#return (#match task
            (#case (Factory.FactoryStart values) (FactoryPoll.FactoryPending (Factory.FactoryResume values)))
            (#case (Factory.FactoryResume values) (FactoryPoll.FactoryReady (InputTask.InputStart values)))))\n  );
}}
{}", source
        .replace("input-poll (InputTask.InputStart values)", "input-poll (#await InputTask Factory FactoryPoll.FactoryPending FactoryPoll.FactoryReady factory-poll (Factory.FactoryStart values))")
        .replace("0u64 4u64", "0u64 5u64"));
    build_and_run_graph(&factory, 42);
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
    let released = exclusive.replace(
        "(#case (Work::Poll.Ready value) (#block (#return value)))",
        "(#case (Work::Poll.Ready value) (#block (#set owner 99u64) (#return value)))",
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
    let error = graph_compile_error(&invalid, "async-awaited-pattern-borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(
        error.message.contains("owner") && error.message.contains("borrow"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("awaited pattern loan must retain its source span");
    assert_eq!(&invalid[span.start..span.end], "#set", "{error:?}");
    assert_eq!(span.start, invalid.find("#set owner 99u64").unwrap());
    let error_for = |source: &str| graph_compile_error(source, "async-awaited-pattern-errors");
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
    let invalid_type = source.replace("(#await Values InputTask", "(#await #u64 InputTask");
    let mismatch = error_for(&invalid_type);
    assert_eq!(mismatch.code, lim::DiagnosticCode::Type, "{mismatch:?}");
    assert!(
        mismatch
            .message
            .contains("#await result type does not match its Ready payload"),
        "{mismatch:?}"
    );
    let span = mismatch
        .span
        .expect("await type mismatch retains its source span");
    assert_eq!(&invalid_type[span.start..span.end], "#u64");
    assert_eq!(
        span.start,
        invalid_type.find("#await #u64 InputTask").unwrap() + "#await ".len()
    );
}

#[test]
fn async_nested_local_destructuring_retains_all_declared_bindings() {
    let source = include_str!("../examples/async_destructure.lim");
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    let aliased = format!(
        "#type ValuesAlias Values\n{}",
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
        "#struct Bits () ((first #u16) (second #u16))\n{}",
        source
            .replace("(z (#tuple #u16 #u16))", "(z Bits)")
            .replace("(#tuple left right)", "(Bits left right)")
            .replace(
                "(#tuple (#tuple #u16 #u16) 9u16 11u16)",
                "(#struct-literal Bits ((first 9u16) (second 11u16)))"
            )
    );
    build_and_run_graph(&nested_struct, 42);
    let mutable = source
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64::add-wrap bias 2u64)) (#let second #u64",
        );
    build_and_run_graph(&mutable, 44);
    let between = source
        .replace(
            "    (#let (Values (#tuple left right) bias) Values values)\n",
            "",
        )
        .replace("(Step.Start (#as left #u64))", "(Step.Start 9u64)")
        .replace(
            "(#let second #u64",
            "(#let (Values (#tuple left right) bias) Values values) (#let second #u64",
        );
    build_and_run_graph(&between, 42);
    let mutable_between = between
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64::add-wrap bias 2u64)) (#let second #u64",
        );
    build_and_run_graph(&mutable_between, 44);
    let both_updated = mutable_between.replace(
        "(#let second #u64",
        "(#set right (#u16::add-wrap right 1u16)) (#let second #u64",
    );
    build_and_run_graph(&both_updated, 45);
    let final_prefix = source
        .replace("    (#let (Values (#tuple left right) bias) Values values)\n", "")
        .replace("(Step.Start (#as left #u64))", "(Step.Start 9u64)")
        .replace("(Step.Start (#as right #u64))", "(Step.Start 11u64)")
        .replace("(#return (#u64::add-wrap", "(#let-mut (Values (#tuple left right) bias) Values values) (#set bias 24u64) (#return (#u64::add-wrap");
    build_and_run_graph(&final_prefix, 44);
    let immutable_update = mutable_between.replace("(#let-mut (Values", "(#let (Values");
    let error = graph_compile_error(&immutable_update, "async-resume-pattern-immutable");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error.message.contains("immutable variable 'bias'"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("immutable pattern update must be source-spanned");
    assert_eq!(&immutable_update[span.start..span.end], "bias");
    assert_eq!(
        span.start,
        immutable_update.find("#set bias").unwrap() + "#set ".len()
    );
    let owned = format!(
        "#struct Token (#linear) ((value #u64))\n \n{}",
        source
            .replace("(a #u64)", "(a Token)")
            .replace("(a 22u64)", "(a (#struct-literal Token ((value 22u64))))")
            .replace("(#return (#u64::add-wrap (#u64::add-wrap first second) bias))", "(#let total #u64 (#u64::add-wrap (#u64::add-wrap first second) (#get bias value))) (#forget bias) (#return total)")
    );
    build_and_run_graph(&owned, 42);
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
        .replace("(#ref #u64)", "(#ref-mut #u64)")
        .replace("(#borrow owner)", "(#borrow-mut owner)");
    // Keep the poller's waker shared; only the destructured data field is exclusive.
    let exclusive = exclusive.replace("(waker (#ref-mut #u64))", "(waker (#ref #u64))");
    build_and_run_graph(&exclusive, 42);
    let definitions = referenced.split_once("#fn main").unwrap().0;
    let cancelled = format!(
        "{definitions}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut owner #u64 11u64)
          (#let frame Work::Task (#call work ((values
            (#struct-literal Values ((a 22u64) (z
              (#tuple (#tuple #u16 (#ref #u64)) 9u16 (#borrow owner)))))))))
          (#let-else (Work::Poll.Pending pending) Work::Poll
            (#call Work::poll ((task frame) (waker (#borrow waker)))) (#unreachable))
          (#forget pending)
          (#set owner 42u64)
          (#return owner)\n  );\n}}\n"
    );
    build_and_run_graph(&cancelled, 42);
    let invalid = referenced.replace(
        "(#block (#set task next) ())",
        "(#block (#set owner 99u64) (#set task next) ())",
    );
    assert_ne!(invalid, referenced);
    let error = graph_compile_error(&invalid, "async-local-pattern-borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
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
        "#type ValuesAlias Values\n{}",
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
        "#struct Bits () ((first #u16) (second #u16))\n{}",
        source
            .replace("(z (#tuple #u16 #u16))", "(z Bits)")
            .replace("(#tuple left right)", "(Bits left right)")
            .replace(
                "(#tuple (#tuple #u16 #u16) 9u16 11u16)",
                "(#struct-literal Bits ((first 9u16) (second 11u16)))",
            )
    );
    build_and_run_graph(&nested_struct, 42);
    let row_literal =
        "(#struct-literal Row ((padding 0u128) (cells (#array-of (#array #u64 2) 41u64 17u64))))";
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
            "#struct Row () ((padding #u128) (cells (#array #u64 2)))",
            "#type Row (#tuple #u128 (#array #u64 2))",
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
        .replace("(Step.Start (#as left #u64))", "(Step.Start 9u64)")
        .replace(
            "(#let second #u64",
            "(#let (Values (#tuple left right) bias) Values values) (#let second #u64",
        );
    build_and_run_graph(&between, 42);
    let mutable = between
        .replace("(#let (Values", "(#let-mut (Values")
        .replace(
            "(#let second #u64",
            "(#set bias (#u64::add-wrap bias 2u64)) (#set right (#u16::add-wrap right 1u16)) (#let second #u64",
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
                    "(#let waker #u64 {}u64) (#let choose #bool (#u64::eq waker 0u64))",
                    if choice { 0 } else { 1 },
                ),
            )
            .replace(
                "9u16 (#borrow owner)",
                "9u16 (#if choose (#borrow owner) (#borrow other))",
            );
        build_and_run_graph(&selected, expected);
    }
    let definitions = referenced.split_once("#fn main").unwrap().0;
    let cancelled = format!(
        "{definitions}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
            (#let waker #u64 0u64)
            (#let-mut owner #u64 11u64)
            (#let frame Work::Task (#call work ((values
              (#struct-literal Values ((a 22u64) (z
                (#tuple (#tuple #u16 (#ref #u64)) 9u16 (#borrow owner)))))))))
            (#let-else (Work::Poll.Pending pending) Work::Poll
              (#call Work::poll ((task frame) (waker (#borrow waker)))) (#unreachable))
            (#forget pending)
            (#set owner 42u64)
            (#return owner)\n  );\n}}\n"
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
        "#type ValuesAlias Values\n{}",
        source.replace("(Choice.Chosen Values)", "(Choice.Chosen ValuesAlias)")
    );
    build_and_run(&aliased, 42);
    let nested = format!(
        "#struct Bias () ((only #u64))\n{}",
        source
            .replace("(a #u64)", "(a Bias)")
            .replace("(Values value bias)", "(Values value (Bias bias))")
            .replace("(a 22u64)", "(a (#struct-literal Bias ((only 22u64))))")
    );
    build_and_run(&nested, 42);
    let referenced = source
        .replace("(z #u16)", "(z (#ref #u64))")
        .replace("(#as value #u64)", "(#deref value)")
        .replace(
            "\n            bias))",
            "\n          (#u64::add-wrap bias (#deref value))))",
        )
        .replace(
            "(#let waker #u64",
            "(#let owner #u64 20u64) (#let waker #u64",
        )
        .replace("(z 20u16)", "(z (#borrow owner))");
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
    .expect("a struct pattern's shared field must stay borrowed through Work::Poll.Pending");
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
            "#enum Choice () ((Choice.Chosen #u64) Choice.Empty)",
            "#enum Choice () ((Choice.Chosen (#tuple #u64 #u64)) Choice.Empty)",
        )
        .replace(
            "(#while-let (Choice.Chosen value)",
            "(#while-let (Choice.Chosen (#tuple value bias))",
        )
        .replace(
            "(Step.Start value)))",
            "(Step.Start (#u64::add-wrap value bias))))",
        )
        .replace(
            "(Choice.Chosen 37u64)",
            "(Choice.Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))",
        );
    build_and_run_graph(&source, 40);
    let aliased = format!(
        "#type Pair (#tuple #u64 #u64)\n{}",
        source.replace("(Choice.Chosen (#tuple #u64 #u64))", "(Choice.Chosen Pair)")
    );
    build_and_run_graph(&aliased, 40);
    let array = source
        .replace(
            "(Choice.Chosen (#tuple #u64 #u64))",
            "(Choice.Chosen (#array #u64 2))",
        )
        .replace(
            "(Choice.Chosen (#tuple value bias))",
            "(Choice.Chosen (#array value bias))",
        )
        .replace(
            "(Choice.Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))",
            "(Choice.Chosen (#array-of (#array #u64 2) 37u64 0u64))",
        );
    build_and_run_graph(&array, 40);
    let alias_chain = format!(
        "#type PairAlias Pair\n{}",
        aliased.replace("(Choice.Chosen Pair)", "(Choice.Chosen PairAlias)")
    );
    build_and_run_graph(&alias_chain, 40);
    let referenced = source
        .replace(
            "(Choice.Chosen (#tuple #u64 #u64))",
            "(Choice.Chosen (#tuple (#ref #u64) #u64))",
        )
        .replace(
            "(#u64::add-wrap value bias)",
            "(#u64::add-wrap (#deref value) bias)",
        )
        .replace(
            "(#let chosen #u64",
            "(#let owner #u64 37u64) (#let chosen #u64",
        )
        .replace(
            "(Choice.Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))",
            "(Choice.Chosen (#tuple (#tuple (#ref #u64) #u64) (#borrow owner) 0u64))",
        );
    build_and_run_graph(&referenced, 40);
    let nested = source
        .replace("(Choice.Chosen (#tuple #u64 #u64))", "(Choice.Chosen (#tuple #u64 (#array #u64 2)))")
        .replace("(Choice.Chosen (#tuple value bias))", "(Choice.Chosen (#tuple value (#array bias padding)))")
        .replace("(Choice.Chosen (#tuple (#tuple #u64 #u64) 37u64 0u64))", "(Choice.Chosen (#tuple (#tuple #u64 (#array #u64 2)) 37u64 (#array-of (#array #u64 2) 0u64 0u64)))");
    build_and_run_graph(&nested, 40);
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
        .split_once("#fn run")
        .unwrap()
        .0;
    let factory = "#enum Factory (#linear) ((Factory.MakeChoice Choice) (Factory.ResumeChoice Choice))

#enum FactoryPoll () ((FactoryPoll.FactoryPending Factory) (FactoryPoll.FactoryReady ChoiceTask))
#fn factory-poll {
  #params = ((task Factory) (waker (#ref #u64)));
  #returns = FactoryPoll;
  #body = (
          (#return (#match task
            (#case (Factory.MakeChoice choice) (FactoryPoll.FactoryPending (Factory.ResumeChoice choice)))
            (#case (Factory.ResumeChoice choice) (FactoryPoll.FactoryReady (ChoiceTask.ChoiceStart choice)))))\n  );\n}\n";
    let source = format!("{factory}\n{}\n
#fn run {{
  #params = ((choice Choice) (waker (#ref #u64)));
  #returns = #u64;
  #body = (
          (#let-mut task Work::Task (#call work ((choice choice))))
          (#for-range (attempt #u64) 0u64 8u64
            (#let polled Work::Poll (#call Work::poll ((task task) (waker waker))))
            (#match polled
              (#case (Work::Poll.Pending next) (#block (#set task next) ()))
              (#case (Work::Poll.Ready result) (#block (#return result)))))
          (#forget task)
          (#return (#unreachable))
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let chosen #u64 (#call run ((choice (Choice.Chosen 37u64)) (waker (#borrow waker)))))
          (#let empty #u64 (#call run ((choice Choice.Empty) (waker (#borrow waker)))))
          (#return (#u64::add-wrap chosen empty))\n  );\n}}\n", definitions.replace(
        "choice-poll (ChoiceTask.ChoiceStart choice)",
        "choice-poll (#await ChoiceTask Factory FactoryPoll.FactoryPending FactoryPoll.FactoryReady factory-poll (Factory.MakeChoice choice))",
    ));
    build_and_run(&source, 42);
    let immediate = source.replace(
        "(FactoryPoll.FactoryPending (Factory.ResumeChoice choice))",
        "(FactoryPoll.FactoryReady (ChoiceTask.ChoiceStart choice))",
    );
    build_and_run(&immediate, 42);
    let guarded = source.replace(
        "(#case (Step.Start value) (StepPoll.StepPending (Step.Resume value)))",
        "(#case (Step.Start value) (#block (#assert (#u64::eq value 37u64)) (StepPoll.StepPending (Step.Resume value))))",
    );
    assert_ne!(guarded, source);
    build_and_run(&guarded, 42);
    let repeated = source
        .replace(
            "(#fn work ((choice Choice)) #u64",
            "(#fn work ((#mut choice Choice)) #u64\n      (#let-mut total #u64 0u64)",
        )
        .replace(
            "(#return second)",
            "(#set total (#u64::add-wrap total second)) (#set choice Choice.Empty)",
        )
        .replace("(#return 5u64)", "(#return total)");
    build_and_run(&repeated, 37);
    let effects = repeated.replace(
        "factory-poll (Factory.MakeChoice choice)",
        "factory-poll (#block (#set total (#u64::add-wrap total 1u64)) (Factory.MakeChoice choice))",
    );
    assert_ne!(effects, repeated);
    build_and_run(&effects, 40);
    let referenced = source
        .replace(
            "#enum Choice () ((Choice.Chosen #u64) Choice.Empty)",
            "#enum Choice () ((Choice.Chosen (#ref #u64)) Choice.Empty)",
        )
        .replace("(Step.Start value)", "(Step.Start (#deref value))")
        .replace(
            "(#let chosen #u64",
            "(#let owner #u64 37u64) (#let chosen #u64",
        )
        .replace("(Choice.Chosen 37u64)", "(Choice.Chosen (#borrow owner))");
    // Change only the async body's task input, not the poller's binding pattern.
    let referenced = referenced.replace(
        "(#case (Step.Start (#deref value))",
        "(#case (Step.Start value)",
    );
    build_and_run(&referenced, 42);
    let prefix = referenced.split_once("#fn main").unwrap().0;
    let cancelled = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut owner #u64 37u64) (#let waker #u64 0u64)
          (#let frame Work::Task (#call work ((choice (Choice.Chosen (#borrow owner))))))
          (#let first Work::Poll (#call Work::poll ((task frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#forget pending)
          (#set owner 42u64)
          (#return owner)\n  );\n}}\n"
    );
    build_and_run(&cancelled, 42);
    let borrowed_mutation = cancelled.replace(
        "(#forget pending)\n          (#set owner 42u64)",
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
    let definitions = source.split_once("#fn main").unwrap().0;
    let factory = "#enum Factory (#linear) ((Factory.MakeCondition #u64) (Factory.ResumeCondition #u64))

#enum FactoryPoll () ((FactoryPoll.FactoryPending Factory) (FactoryPoll.FactoryReady ConditionTask))
#fn factory-poll {
  #params = ((task Factory) (waker (#ref #u64)));
  #returns = FactoryPoll;
  #body = (
          (#return (#match task
            (#case (Factory.MakeCondition index) (FactoryPoll.FactoryPending (Factory.ResumeCondition index)))
            (#case (Factory.ResumeCondition index) (FactoryPoll.FactoryReady (ConditionTask.Check index)))))\n  );\n}\n";
    let source = format!("{factory}\n{}\n
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut task Work::Task (#call work ()))
          (#for-range (attempt #u64) 0u64 10u64
            (#let polled Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#match polled
              (#case (Work::Poll.Pending next) (#block (#set task next) ()))
              (#case (Work::Poll.Ready result) (#block (#return result)))))
          (#forget task)
          (#forget waker)
          (#return 0u64)\n  );\n}}\n", definitions.replace(
            "condition-poll (ConditionTask.Check index)",
            "condition-poll (#await ConditionTask Factory FactoryPoll.FactoryPending FactoryPoll.FactoryReady factory-poll (Factory.MakeCondition index))",
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
            "(#return (#u64::add-wrap value index))",
            "(#set total (#u64::add-wrap total value))",
        )
        .replacen("(#return 0u64)", "(#return total)", 1);
    build_and_run(&repeated, 40);
    let effects = repeated.replace(
        "factory-poll (Factory.MakeCondition index)",
        "factory-poll (#block (#set total (#u64::add-wrap total 1u64)) (Factory.MakeCondition index))",
    );
    build_and_run(&effects, 43);
}

#[test]
fn async_mutating_branches_restore_their_outputs() {
    let source = "#enum Step (#linear) ((Step.Start #u64) (Step.Resume #u64))
#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Start value) (StepPoll.StepPending (Step.Resume value)))
            (#case (Step.Resume value) (StepPoll.StepReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((selected #bool)) #u64
            (#let-mut total #u64 0u64)
            (#let value #u64 (#if selected
              (#block
                (#set total 1u64)
                (#let left #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start 20u64)))
                (#set total 22u64)
                left)
              (#block
                (#set total 2u64)
                (#let right #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start 30u64)))
                (#set total 12u64)
                right)))
            (#return (#u64::add-wrap total value)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut task Work::Task (#call work ((selected true))))
          (#for-range (attempt #u64) 0u64 5u64
            (#let polled Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#match polled
              (#case (Work::Poll.Pending next) (#block (#set task next) ()))
              (#case (Work::Poll.Ready result) (#block (#return result)))))
          (#forget task)
          (#return 0u64)\n  );\n}\n";
    build_and_run_graph(source, 42);
    build_and_run_graph(&source.replace("(selected true)", "(selected false)"), 42);
    let immediate = source.replace(
        "(StepPoll.StepPending (Step.Resume value))",
        "(StepPoll.StepReady value)",
    );
    build_and_run_graph(&immediate, 42);
    let matched = source
        .replace("(#if selected", "(#match selected (#case true")
        .replace(
            "left)\n              (#block",
            "left))\n            (#case false (#block",
        )
        .replace("right)))", "right))))");
    assert_ne!(matched, source);
    build_and_run_graph(&matched, 42);
    build_and_run_graph(&matched.replace("(selected true)", "(selected false)"), 42);
    let mixed = source.replace(
        "(#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start 30u64))",
        "30u64",
    );
    build_and_run_graph(&mixed, 42);
    build_and_run_graph(&mixed.replace("(selected true)", "(selected false)"), 42);
    let borrowed = format!(
        "#fn put {{
  #params = ((target (#ref-mut #u64)) (value #u64));
  #returns = ();
  #body = (
        (#deref-set target value) (#return ())\n  );
}}
{}",
        source
            .replace(
                "(#set total 22u64)",
                "(#call put ((target (#borrow-mut total)) (value 22u64)))"
            )
            .replace(
                "(#set total 12u64)",
                "(#call put ((target (#borrow-mut total)) (value 12u64)))"
            )
    );
    build_and_run_graph(&borrowed, 42);
    build_and_run_graph(&borrowed.replace("(selected true)", "(selected false)"), 42);
    let linear = format!("#struct Counter (#linear) ((value #u64))\n \n{}", source
        .replace("(#let-mut total #u64 0u64)", "(#let-mut total Counter (#struct-literal Counter ((value 0u64))))")
        .replace("(#set total", "(#set-field total value")
        .replace("(#return (#u64::add-wrap total value))", "(#let result #u64 (#u64::add-wrap (#get total value) value)) (#forget total) (#return result)"));
    build_and_run_graph(&linear, 42);
    build_and_run_graph(&linear.replace("(selected true)", "(selected false)"), 42);
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
    let source = "#struct Counter (#linear) ((value #u64))
#enum Step (#linear) ((Step.Start #u64) (Step.Resume #u64))
#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Start value) (StepPoll.StepPending (Step.Resume value)))
            (#case (Step.Resume value) (StepPoll.StepReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut total Counter (#struct-literal Counter ((value 0u64))))
            (#forget total)
            (#let value #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start 40u64)))
            (#set total (#struct-literal Counter ((value 2u64))))
            (#let result #u64 (#u64::add-wrap value (#get total value)))
            (#forget total)
            (#return result))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task next) (waker (#borrow waker)))))
          (#return (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}\n";
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
    let source = "#enum Step (#linear) ((Step.Start #u64) (Step.Resume #u64))
#enum StepPoll () ((StepPoll.StepPending Step) (StepPoll.StepReady #u64))
#fn step-poll {
  #params = ((task Step) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case (Step.Start value) (StepPoll.StepPending (Step.Resume value)))
            (#case (Step.Resume value) (StepPoll.StepReady value))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut total #u64 0u64)
            (#let left #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll
              (#block (#set total (#u64::add-wrap total 1u64)) (Step.Start 20u64))))
            (#let right #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll
              (#block (#set total (#u64::add-wrap total 1u64)) (Step.Start left))))
            (#return (#u64::add-wrap (#u64::add-wrap left right) total)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut task Work::Task (#call work ()))
          (#for-range (attempt #u64) 0u64 5u64
            (#let polled Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#match polled
              (#case (Work::Poll.Pending next) (#block (#set task next) ()))
              (#case (Work::Poll.Ready result) (#block (#return result)))))
          (#forget task)
          (#return 0u64)\n  );\n}\n";
    build_and_run(source, 42);
    let immediate = source.replace(
        "(StepPoll.StepPending (Step.Resume value))",
        "(StepPoll.StepReady value)",
    );
    build_and_run(&immediate, 42);
    // Explicit task temporaries and direct task expressions have identical
    // sequencing, including construction of the second stage after resume.
    let temporaries = source.replace(
        "(#let left #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll\n              (#block (#set total (#u64::add-wrap total 1u64)) (Step.Start 20u64))))",
        "(#let first Step (#block (#set total (#u64::add-wrap total 1u64)) (Step.Start 20u64)))\n          (#let left #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll first))",
    ).replace(
        "(#let right #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll\n              (#block (#set total (#u64::add-wrap total 1u64)) (Step.Start left))))",
        "(#let second Step (#block (#set total (#u64::add-wrap total 1u64)) (Step.Start left)))\n          (#let right #u64 (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll second))",
    );
    assert_ne!(temporaries, source);
    build_and_run(&temporaries, 42);
}

#[test]
fn async_early_continue_skips_the_rest_of_the_iteration() {
    let source = include_str!("../examples/async_early_continue.lim");
    build_and_run(source, 42);
    let matched = source.replace(
        "(#if (#u64::eq index 1u64) (#continue) ())",
        "(#match index (#case 1u64 (#continue)) (#case _ ()))",
    );
    assert_ne!(matched, source);
    build_and_run(&matched, 42);
    let guarded = format!("#enum Index () ((Index.Current #u64))\n{}", source.replace(
        "(#if (#u64::eq index 1u64) (#continue) ())",
        "(#match (Index.Current index) (#case (Index.Current amount) (#when (#u64::eq amount 1u64)) (#continue)) (#case _ ()))",
    ));
    assert_ne!(guarded, source);
    build_and_run(&guarded, 42);

    let scoped = source.replace(
        "(#if (#u64::eq index 1u64) (#continue) ())",
        "(#if (#u64::eq index 1u64) (#block (#let local #u64 1u64) (#assert (#u64::eq local 1u64)) (#continue)) ())",
    );
    assert_ne!(scoped, source);
    build_and_run(&scoped, 42);
    let reused_local = scoped
        .replace("(#let value #u64", "(#let local #u64")
        .replace(
            "(#u64::add-wrap value index)",
            "(#u64::add-wrap local index)",
        );
    build_and_run(&reused_local, 42);
    let nested = source.replace(
        "(#set index (#u64::add-wrap index 1u64))",
        "(#set index (#u64::add-wrap index 1u64)) (#for-range (inner #u64) 0u64 1u64 (#break))",
    );
    build_and_run(&nested, 42);
    let short_main = "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
        (#let waker #u64 0u64)
        (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
        (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
        (#let second Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
        (#return (#match second
          (#case (Work::Poll.Ready value) value)
          (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))\n  );\n}\n";
    let work = source.split_once("#fn main").unwrap().0;
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
        "(#while (#await #bool ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll (ConditionTask.Check index))\n        (#set index (#u64::add-wrap index 1u64))",
        "(#for () (#await #bool ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll (ConditionTask.Check index))\n      (#set index (#u64::add-wrap index 1u64))",
    ).replace("(#u64::eq index 1u64)", "(#u64::eq index 0u64)");
    assert_ne!(for_loop, source);
    build_and_run(&for_loop, 41);
}

#[test]
fn terminalized_async_branches_preserve_lexical_scope_and_shadowing_rules() {
    let source = include_str!("../examples/async_early_continue.lim");
    let scoped = source.replace(
        "(#if (#u64::eq index 1u64) (#continue) ())",
        "(#if (#u64::eq index 1u64) (#block (#let local #u64 1u64) (#continue)) ())",
    );
    let scratch = support::Scratch::new("async-terminal-scope");
    let input = scratch.path().join("scope.lim");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let leaked = scoped.replace(
        "(#u64::add-wrap value index)",
        "(#u64::add-wrap value local)",
    );
    let error = lim::compile_source_to_assembly(
        &leaked,
        &input,
        &config,
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
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("shadow"), "{error:?}");
    let span = error.span.expect("original shadowed declaration span");
    assert_eq!(&shadowed[span.start..span.end], "index");
    assert_eq!(
        span.start,
        shadowed.find("#let index").unwrap() + "#let ".len()
    );
    let global_shadow = format!("#const local #u64 9u64\n{scoped}");
    let error = lim::compile_source_to_assembly(
        &global_shadow,
        &input,
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("shadow"), "{error:?}");
    let span = error
        .span
        .expect("global shadow has an original binder span");
    assert_eq!(&global_shadow[span.start..span.end], "local");
    assert_eq!(
        span.start,
        global_shadow.find("#let local").unwrap() + "#let ".len()
    );
    let resource = format!(
        "#struct Resource (#linear) ((value #u64))\n \n{}",
        scoped.replace(
            "(#let local #u64 1u64)",
            "(#let local Resource (#struct-literal Resource ((value 1u64))))",
        )
    );
    let error = lim::compile_source_to_assembly(
        &resource,
        &input,
        &config,
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("local") && error.message.contains("consumed"),
        "{error:?}"
    );
    let consumed = resource.replace("(#continue)", "(#forget local) (#continue)");
    build_and_run_graph(&consumed, 42);
}

#[test]
fn async_for_effect_step_awaits_with_a_synchronous_condition() {
    let source = include_str!("../examples/async_for_effect_step.lim");
    build_and_run(source, 42);
    let returned = source.replace("(#break)", "(#return (#u64::add-wrap index 40u64))");
    build_and_run(&returned, 42);
    let matched = source.replace(
        "(#if (#u64::eq index 0u64)\n          (#continue)\n          (#if stop (#break) ()))",
        "(#match index (#case 0u64 (#continue)) (#case _ (#if stop (#break) ())))",
    );
    assert_ne!(matched, source);
    build_and_run(&matched, 42);
    let effects = source
        .replace("#fn advance", "#fn touch {\n  #params = ((counter (#ref-mut #u64)));\n  #returns = #u64;\n  #body = (\n  (#deref-set counter (#u64::add-wrap (#deref counter) 1u64))\n  (#return 1u64)\n  );\n}\n\n#fn advance")
        .replace("(#let-mut index #u64 0u64)", "(#let-mut index #u64 0u64) (#let-mut touches #u64 0u64)")
        .replace("((next (#await", "((next (#u64::add-wrap (#call touch ((counter (#borrow-mut touches)))) (#await")
        .replace("(StepTask.Start (#u64::add-wrap index 1u64)))", "(StepTask.Start index)))")
        .replace("(#return (#u64::add-wrap index 40u64))", "(#assert (#u64::eq touches index)) (#return (#u64::add-wrap index 40u64))");
    assert_ne!(effects, source);
    build_and_run(&effects, 42);
}

#[test]
fn async_for_effect_step_consumes_linear_operands_and_results() {
    let source = include_str!("../examples/async_for_effect_step.lim");
    let source = format!(
        "#struct Resource (#linear) ((value #u64))\n\n{}",
        source
            .replace(
                "((StepTask.Start #u64) (StepTask.Resume #u64))",
                "((StepTask.Start Resource) (StepTask.Resume Resource))"
            )
            .replace("(StepPoll.StepReady #u64)", "(StepPoll.StepReady Resource)")
            .replace("((next #u64) (counter", "((next Resource) (counter")
            .replace(
                "(#deref-set counter next)",
                "(#deref-set counter (#get next value))\n  (#forget next)"
            )
            .replace("(#await #u64 StepTask", "(#await Resource StepTask")
            .replace(
                "(StepTask.Start (#u64::add-wrap index 1u64))",
                "(StepTask.Start (#struct-literal Resource ((value (#u64::add-wrap index 1u64)))))"
            )
    );
    build_and_run(&source, 42);

    // Cancel after the child owns a Resource; explicitly consume that state.
    let continuation = source.find("(#let second Work::Poll").unwrap();
    let cancelled = format!(
        "{} (#forget first-task) (#return 42u64)\n  );\n}}",
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
        .split("#generate #async-fn")
        .next()
        .unwrap();
    let source = format!(
        r#"{definitions}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((counter (#ref-mut #u64))) #u64
            (#for () (#u64::lt (#deref counter) 2u64)
              (#call advance ((next (#await #u64 StepTask StepPoll.StepPending StepPoll.StepReady step-poll
                                        (StepTask.Start (#u64::add-wrap (#deref counter) 1u64))))
                              (counter counter))) ())
            (#return (#u64::add-wrap (#deref counter) 40u64)))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let-mut owner #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ((counter (#borrow-mut owner))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending last-task) Work::Poll second (#unreachable))
          (#let third Work::Poll (#call Work::poll ((task last-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Ready result) Work::Poll third (#unreachable))
          (#assert (#u64::eq owner 2u64))
          (#return result)
  );
}}
"#
    );
    build_and_run(&source, 42);
    let continuation = source.find("(#let second Work::Poll").unwrap();
    let cancelled = format!(
        "{} (#forget pending) (#set owner 42u64) (#return owner)\n  );\n}}",
        &source[..continuation]
    );
    build_and_run(&cancelled, 42);
    let invalid = source.replace(
        "(#let second Work::Poll",
        "(#set owner 9u64) (#let second Work::Poll",
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
        .replace("(#u64::lt index 2u64)", "(#u64::lt index 4u64)")
        .replace(
            "(#let body-ran #bool true))",
            "(#let body-ran #bool true) (#if (#u64::eq index 0u64) (#continue) (#break)))",
        );
    assert_ne!(transfers, source);
    build_and_run(&transfers, 42);
    let returned = transfers.replace("(#break)", "(#return (#u64::add-wrap index 40u64))");
    assert_ne!(returned, transfers);
    build_and_run(&returned, 42);
    for source in [&transfers, &returned] {
        let matched = source
            .replace(
                "(#if (#u64::eq index 0u64) (#continue)",
                "(#match index (#case 0u64 (#continue)) (#case _",
            )
            .replace("(#break)))", "(#break))))")
            .replace(
                "(#return (#u64::add-wrap index 40u64))))",
                "(#return (#u64::add-wrap index 40u64)))))",
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
#struct Counter () ((value #u64))
#enum ChildTask (#linear) (ChildTask.Start ChildTask.Resume)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {{
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
              (#return (#match task
                (#case ChildTask.Start (ChildPoll.ChildPending ChildTask.Resume))
                (#case ChildTask.Resume (ChildPoll.ChildReady true))))
  );
}}
#fn touch {{
  #params = ((value (#ref-mut #u64)));
  #returns = ();
  #body = (
              (#deref-set value (#u64::add-wrap (#deref value) 1u64))
              (#return ())
  );
}}
#generate #async-fn ((protocol work-await) (waker #u64) (function
              (#fn work () #u64
                (#let-mut counter {ty} {initial})
                (#let-mut keep #bool true)
                (#while keep
                  {prefix}
                  (#call touch ((value {argument})))
                  {suffix}
                  (#set keep (#bool::and
                    (#await #bool ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Start) false)))
                (#return (#u64::add-wrap {place} 41u64)))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
              (#let waker #u64 0u64)
              (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
              (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
              (#let second Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
              (#return (#match second
                (#case (Work::Poll.Ready value) value)
                (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}}
        "#
        );
        build_and_run_graph(&source, 42);
        if ty == "(#array #u64 1)" {
            let retained = source.replace(
                &format!("(#call touch ((value {argument})))"),
                &format!(
                    "(#let selected (#ref-mut #u64) {argument})
                     (#call touch ((value selected)))
                     (#call touch ((value selected)))
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
#fn lend {
  #params = ((holder (#pin-ref-mut (#slice-mut #u64))));
  #returns = (#slice-mut #u64);
  #body = (
          (#return (#slice-mut-range (#deref holder) 0usize (#slice-mut-len (#deref holder))))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 41u64))
          (#let-mut items (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
          (#let range (#slice-mut #u64) (#call lend ((holder (#pin items)))))
          (#deref-set (#slice-mut-idx range 0usize) 42u64)
          (#forget range)
          (#forget items)
          (#return (#index values 0usize))
  );
}
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
#enum ChildTask (#linear) (ChildTask.Start ChildTask.Resume)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady ()))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Start (ChildPoll.ChildPending ChildTask.Resume))
            (#case ChildTask.Resume (ChildPoll.ChildReady ()))))
  );
}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((items (#slice-mut #u64))) #u64
            (#let view (#ref-mut #u64) (#slice-mut-idx items 0usize))
            (#deref-set view (#u64::add-wrap (#deref view) 1u64))
            (#forget view)
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Start)
            (#let answer #u64 (#deref (#slice-mut-idx items 0usize)))
            (#forget items)
            (#return answer))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 41u64))
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((items (#slice-mut-of (#borrow-mut values)))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#assert (#u64::eq (#index values 0usize) 42u64))
          (#return answer)
  );
}
    "#
}

#[test]
fn graph_external_mutable_slice_indices_preserve_lending_and_pending() {
    let source = external_mutable_slice_source();
    let generated = build_and_run_graph(source, 42);
    let runtime = source.split_once("#generate #async-fn").unwrap().0;
    let main = source.split_once("#fn main").unwrap().1;
    let standalone = format!("{runtime}\n{generated}\n#fn main{main}");
    build_and_run_graph(&ordinary_generated(&standalone), 42);
    let aliased = format!(
        "#type Items (#slice-mut #u64)\n{}",
        source.replace("(items (#slice-mut #u64))", "(items Items)")
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
    let runtime = retained.split_once("#generate #async-fn").unwrap().0;
    let main = retained.split_once("#fn main").unwrap().1;
    build_and_run_graph(
        &ordinary_generated(&format!("{runtime}\n{generated}\n#fn main{main}")),
        42,
    );
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
        "#type Items (#slice-mut #u64)\n{}",
        indexed.replace("(items (#slice-mut #u64))", "(items Items)")
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
        .replace("(#deref-set view (#u64::add-wrap (#deref view) 1u64))", "")
        .replace("41u64", "42u64")
        .replace("#ref-mut", "#ref")
        .replace("#slice-mut", "#slice")
        .replace("#borrow-mut values", "#borrow values");
    build_and_run_graph(&shared, 42);

    let runtime = external_mutable_slice_source()
        .split_once("#generate #async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
#struct Empty () ()
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((items (#slice-mut Empty))) #u64
            (#let index #usize 2usize)
            (#let view (#ref-mut Empty) (#slice-mut-idx items index))
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Start)
            (#let observed Empty (#deref view)) (#forget observed)
            (#forget view) (#forget items) (#return 42u64))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut values (#array Empty 3) (#array-of (#array Empty 3)
            (#struct-literal Empty ()) (#struct-literal Empty ()) (#struct-literal Empty ())))
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((items (#slice-mut-of (#borrow-mut values)))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#return (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}}
"#
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
            "(items (#slice-mut #u64))",
            "(items (#slice-mut #u64)) (other (#slice-mut #u64)) (choose #bool)",
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
            "(items (#slice-mut-of (#borrow-mut values)))",
            "(items (#slice-mut-of (#borrow-mut values))) (other (#slice-mut-of (#borrow-mut second))) (choose true)",
        )
        .replace(
            "(#u64::eq (#index values 0usize) 42u64)",
            "(#u64::eq (#u64::add-wrap (#index values 0usize) (#index second 0usize)) 83u64)",
        );
    build_and_run_graph(&source, 42);
    build_and_run_graph(&source.replace("(choose true)", "(choose false)"), 42);
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
        .replace("(items (#slice-mut #u64))", "(items (#slice-mut (#array #u64 2))) (choose #bool)")
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
        .replace("(items (#slice-mut-of (#borrow-mut values)))", "(items (#slice-mut-of (#borrow-mut values))) (choose true)")
        .replace("(#index values 0usize)", "(#index (#index values 0usize) 0usize)");
    build_and_run_graph(&source, 42);
    let invalid_first = source
        .replace("(#index row 0usize)", "(#index row swap)")
        .replace("(#index row 2usize)", "(#index row 0usize)")
        .replace("(#index row swap)", "(#index row 2usize)")
        .replace("(choose true)", "(choose false)");
    build_and_run_graph(&invalid_first, 42);
    let nested_struct = format!(
        "#struct Row () ((padding #u128) (cells (#array #u64 2)))\n{}",
        invalid_first
            .replace("(#slice-mut (#array #u64 2))", "(#slice-mut Row)")
            .replace("(#ref-mut (#array #u64 2))", "(#ref-mut Row)")
            .replace("(#array (#array #u64 2) 1)", "(#array Row 1)")
            .replace("(#array-of (#array #u64 2) 41u64 17u64)",
                "(#struct-literal Row ((padding 0u128) (cells (#array-of (#array #u64 2) 41u64 17u64))))")
            .replace("(#index row ", "(#index (#get row cells) ")
            .replace("(#index (#index values 0usize) 0usize)",
                "(#index (#get (#index values 0usize) cells) 0usize)")
    );
    build_and_run_graph(&nested_struct, 42);
    // Skipping an impossible reconstruction candidate does not authorize the
    // original selection: the selected invalid source branch still traps.
    build_and_run_route_status(
        &invalid_first.replace("(choose false)", "(choose true)"),
        None,
        true,
    );
}

#[test]
fn graph_slice_nested_runtime_coordinates_survive_index_mutation() {
    let runtime = external_mutable_slice_source()
        .split_once("#generate #async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
#struct Row () ((padding #u128) (cells (#array #u64 2)))
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((items (#slice-mut Row))) #u64
            (#let-mut outer #usize 1usize) (#let-mut inner #usize 1usize)
            (#let row (#ref-mut Row) (#slice-mut-idx items outer))
            (#let view (#ref-mut #u64) (#borrow-mut (#index (#get row cells) inner)))
            (#deref-set view (#u64::add-wrap (#deref view) 1u64))
            (#set outer 0usize) (#set inner 0usize)
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Start)
            (#let answer #u64 (#deref view))
            (#forget view) (#forget row) (#forget items) (#return answer))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut values (#array Row 2) (#array-of (#array Row 2)
            (#struct-literal Row ((padding 0u128) (cells (#array-of (#array #u64 2) 3u64 4u64))))
            (#struct-literal Row ((padding 7u128) (cells (#array-of (#array #u64 2) 17u64 41u64))))))
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((items (#slice-mut-of (#borrow-mut values)))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#assert (#u64::eq (#index (#get (#index values 1usize) cells) 1usize) 42u64))
          (#assert (#u64::eq (#index (#get (#index values 0usize) cells) 1usize) 4u64))
          (#return answer)
  );
}}
"#
    );
    let generated = build_and_run_graph(&source, 42);
    let declarations = source.split_once("#generate #async-fn").unwrap().0;
    let main = source.split_once("#fn main").unwrap().1;
    build_and_run_graph(
        &ordinary_generated(&format!("{declarations}\n{generated}\n#fn main{main}")),
        42,
    );
    let shared = source
        .replace("(#deref-set view (#u64::add-wrap (#deref view) 1u64))", "")
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
            "(#struct-literal Row ((padding 0u128) (cells (#array-of (#array #u64 2) 3u64 4u64))))",
            "",
        )
        .replace(
            "(#assert (#u64::eq (#index (#get (#index values 0usize) cells) 1usize) 4u64))",
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
        "#struct Empty () ()\n{}",
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
            .replace("(#deref-set view (#u64::add-wrap (#deref view) 1u64))", "")
            .replace(
                "(#let answer #u64 (#deref view))",
                "(#let observed Empty (#deref view)) (#forget observed) (#let answer #u64 42u64)"
            )
            .replace(
                "(#assert (#u64::eq (#index (#get (#index values 1usize) cells) 1usize) 42u64))",
                ""
            )
            .replace(
                "(#assert (#u64::eq (#index (#get (#index values 0usize) cells) 1usize) 4u64))",
                ""
            )
    );
    build_and_run_graph(&zero_sized, 42);
    let branched = source
        .replace("(items (#slice-mut Row))", "(items (#slice-mut Row)) (choose #bool)")
        .replace("(#borrow-mut (#index (#get row cells) inner))", "(#if choose (#borrow-mut (#index (#get row cells) inner)) (#borrow-mut (#index (#get row cells) 0usize)))")
        .replace("(items (#slice-mut-of (#borrow-mut values)))", "(items (#slice-mut-of (#borrow-mut values))) (choose true)");
    build_and_run_graph(&branched, 42);
    let constant_branch = branched.replace("(choose true)", "(choose false)").replace(
        "(#index (#get (#index values 1usize) cells) 1usize) 42u64",
        "(#index (#get (#index values 1usize) cells) 0usize) 18u64",
    );
    build_and_run_graph(&constant_branch, 18);
    let conflicting = source.replace("(#let answer #u64 (#match", "(#set-index values 1usize (#struct-literal Row ((padding 0u128) (cells (#array-of (#array #u64 2) 0u64 0u64))))) (#let answer #u64 (#match");
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
        .replace("(items (#slice-mut #u64))", "(items (#slice-mut #u64)) (fallback (#ref-mut #u64)) (choose #bool)")
        .replace("(#slice-mut-idx items 0usize)", "(#if choose (#slice-mut-idx items 0usize) (#borrow-mut (#deref fallback)))")
        .replace("(#forget items)", "(#forget items) (#forget fallback)")
        .replace("(#let waker #u64 0u64)", "(#let-mut fallback #u64 41u64) (#let waker #u64 0u64)")
        .replace("(items (#slice-mut-of (#borrow-mut values)))", "(items (#slice-mut-of (#borrow-mut values))) (fallback (#borrow-mut fallback)) (choose true)")
        .replace("(#u64::eq (#index values 0usize) 42u64)", "(#u64::eq (#u64::add-wrap (#index values 0usize) fallback) 83u64)");
    build_and_run_graph(&source, 42);
    build_and_run_graph(&source.replace("(choose true)", "(choose false)"), 42);
    let aliased = format!(
        "#type Items (#slice-mut #u64)\n#type Fallback (#ref-mut #u64)\n{}",
        source
            .replace("(items (#slice-mut #u64))", "(items Items)")
            .replace("(fallback (#ref-mut #u64))", "(fallback Fallback)")
    );
    build_and_run_graph(&aliased, 42);
    let shared = source
        .replace("(#deref-set view (#u64::add-wrap (#deref view) 1u64))", "")
        .replace("41u64", "42u64")
        .replace("83u64", "84u64")
        .replace("#ref-mut", "#ref")
        .replace("#slice-mut", "#slice")
        .replace("#borrow-mut", "#borrow");
    build_and_run_graph(&shared, 42);
    build_and_run_graph(&shared.replace("(choose true)", "(choose false)"), 42);
    let field = format!(
        "#struct Data () ((padding #u128) (value #u64))\n{}",
        source
            .replace("(fallback (#ref-mut #u64))", "(fallback (#ref-mut Data))")
            .replace(
                "(#borrow-mut (#deref fallback))",
                "(#borrow-mut (#get fallback value))"
            )
            .replace(
                "(#let-mut fallback #u64 41u64)",
                "(#let-mut fallback Data (#struct-literal Data ((padding 0u128) (value 41u64))))"
            )
            .replace(
                "(#u64::add-wrap (#index values 0usize) fallback)",
                "(#u64::add-wrap (#index values 0usize) (#get fallback value))"
            )
    );
    build_and_run_graph(&field, 42);
    build_and_run_graph(&field.replace("(choose true)", "(choose false)"), 42);
    let array = source
        .replace(
            "(fallback (#ref-mut #u64))",
            "(fallback (#ref-mut (#array #u64 2)))",
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
            "(#u64::add-wrap (#index values 0usize) fallback)",
            "(#u64::add-wrap (#index values 0usize) (#index fallback 1usize))",
        );
    build_and_run_graph(&array, 42);
    build_and_run_graph(&array.replace("(choose true)", "(choose false)"), 42);
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
        "{source}\n#fn escape {{
  #params = ((items (#slice-mut #u64)));
  #returns = Work::Task;
  #body = (
        (#let-mut local #u64 41u64)
        (#return (#call work ((items items) (fallback (#borrow-mut local)) (choose false))))\n  );\n}}\n"
    );
    let error = graph_compile_error(&escaping, "mixed-target-local-reference-escape");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some());
    let overlapping = source.replace(
        "(fallback (#borrow-mut fallback))",
        "(fallback (#borrow-mut (#index values 0usize)))",
    );
    let error = graph_compile_error(&overlapping, "mixed-target-overlapping-inputs");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.message.contains("overlap"), "{error:?}");
    assert!(error.span.is_some());
}

#[test]
fn graph_pinned_reference_selects_local_or_external_storage() {
    let runtime = external_mutable_slice_source()
        .split_once("#generate #async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
#fn cancel-child {{
  #params = ((task ChildTask));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (cancel (cancel-frame ((await-0 cancel-child))))
          (function (#fn work ((other (#pin-ref-mut #u64)) (choose #bool)) #u64
            (#let-mut local #u64 42u64)
            (#let view (#pin-ref-mut #u64)
              (#if choose (#pin local) (#borrow-mut (#deref other))))
            (#assert (#u64::eq (#deref view) 42u64))
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Start)
            (#let answer #u64 (#deref view))
            (#forget view) (#forget other) (#forget local) (#return answer))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut other #u64 42u64) (#let waker #u64 0u64)
          (#let-mut frame Work::Frame (#call work ((other (#pin other)) (choose true))))
          (#let first Work::Poll
            (#call Work::poll ((task (#pin frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame) (#forget other) (#return answer)
  );
}}
"#
    );
    build_and_run_graph(&source, 42);
    build_and_run_graph(&source.replace("(choose true)", "(choose false)"), 42);
    let shared = source
        .replace("#pin-ref-mut", "#pin-ref")
        .replace("(#pin local)", "(#pin-shared local)")
        .replace("(#pin other)", "(#pin-shared other)")
        .replace("(#borrow-mut (#deref other))", "(#borrow (#deref other))");
    build_and_run_graph(&shared, 42);
    build_and_run_graph(&shared.replace("(choose true)", "(choose false)"), 42);
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
    build_and_run_graph(&projected.replace("(choose true)", "(choose false)"), 42);
    let second =
        "(#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))";
    let canceled = source.replace(
        second,
        "(#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task next))))
         (#call cancel-frame ((task cleanup))) (#let answer #u64 42u64)",
    );
    assert_ne!(canceled, source);
    build_and_run_graph(&canceled, 42);
    build_and_run_graph(&canceled.replace("(choose true)", "(choose false)"), 42);
    let conflicting = source.replace(
        second,
        &format!("(#unsafe (#pin-write (#pin-borrow-mut other) 0u64)) {second}"),
    );
    let error = graph_compile_error(&conflicting, "mixed-pinned-target-live-write");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some());
    let movable = source.replace("#generate #async-fn-pinned", "#generate #async-fn");
    let error = graph_compile_error(&movable, "movable-pinned-local-target");
    assert!(error.message.contains("pinned async frame"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&movable[span.start..span.end], "(#pin local)");
}

#[test]
fn graph_whole_pinned_reborrows_preserve_kind_before_and_after_pending() {
    let runtime = external_mutable_slice_source()
        .split_once("#generate #async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((parent (#pin-ref-mut #u64))) #u64
            (#let first (#pin-ref-mut #u64) (#borrow-mut (#deref parent)))
            (#assert (#u64::eq (#deref first) 42u64)) (#forget first)
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Start)
            (#let second (#pin-ref-mut #u64) (#borrow-mut (#deref parent)))
            (#let answer #u64 (#deref second))
            (#forget second) (#forget parent) (#return answer))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut value #u64 42u64) (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ((parent (#pin value))))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget value) (#return answer)
  );
}}
"#
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
        .split_once("#generate #async-fn")
        .unwrap()
        .0;
    let source = format!(
        r#"{runtime}
#fn cancel-container {{
  #params = ((view (#slice-mut #u64)));
  #returns = ();
  #body = ( (#forget view) (#return ())
  );
}}
#fn cancel-child {{
  #params = ((task ChildTask));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (cancel (cancel-frame ((container cancel-container) (await-0 cancel-child))))
          (function (#fn work () #u64
            (#let-mut counter (#array #u64 1) (#array-of (#array #u64 1) 41u64))
            (#let container (#slice-mut #u64) (#slice-mut-of (#borrow-mut counter)))
            (#let view (#ref-mut #u64) (#slice-mut-idx container 0usize))
            (#deref-set view (#u64::add-wrap (#deref view) 1u64)) (#forget view)
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Start)
            (#let answer #u64 (#deref (#slice-mut-idx container 0usize)))
            (#forget container) (#forget counter) (#return answer))))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut frame Work::Frame (#call work ())) (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#pin frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame) (#return answer)
  );
}}
"#
    );
    build_and_run_graph(&source, 42);
}

#[test]
fn graph_parent_cancels_a_slice_borrowing_child_before_its_lender() {
    let source = r#"
#enum ChildTask (#linear) ((ChildTask.Start (#slice-mut #u64)) (ChildTask.Resume (#slice-mut #u64)))

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady ()))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Start initial) (ChildPoll.ChildPending (ChildTask.Resume initial)))
            (#case (ChildTask.Resume final)
              (#block
                (#let element (#ref-mut #u64) (#slice-mut-idx final 0usize))
                (#deref-set element (#u64::add-wrap (#deref element) 1u64))
                (#forget element)
                (#forget final) (ChildPoll.ChildReady ())))))
  );
}
#fn cancel-child {
  #params = ((task ChildTask));
  #returns = ();
  #body = (
          (#match task
            (#case (ChildTask.Start initial)
              (#block (#deref-set (#slice-mut-idx initial 0usize) 42u64) (#forget initial)))
            (#case (ChildTask.Resume final)
              (#block (#deref-set (#slice-mut-idx final 0usize) 42u64) (#forget final))))
          (#return ())
  );
}
#fn cancel-container {
  #params = ((view (#slice-mut #u64)));
  #returns = ();
  #body = (
          (#assert (#u64::eq (#deref (#slice-mut-idx view 0usize)) 42u64))
          (#forget view) (#return ())
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (cancel (cancel-frame ((container cancel-container) (await-0 cancel-child))))
          (function (#fn work () #u64
            (#let-mut counter (#array #u64 1) (#array-of (#array #u64 1) 41u64))
            (#let container (#slice-mut #u64) (#slice-mut-of (#borrow-mut counter)))
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll
              (ChildTask.Start (#slice-mut-range container 0usize (#slice-mut-len container))))
            (#let answer #u64 (#deref (#slice-mut-idx container 0usize)))
            (#forget container) (#forget counter) (#return answer))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut frame Work::Frame (#call work ())) (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#pin frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task next))))
          (#call cancel-frame ((task cleanup)))
          (#forget frame) (#return 42u64)
  );
}
"#;
    build_and_run_graph(source, 42);
    // The same child must also release its loan on normal completion before
    // its parent reads and consumes the original lending slice.
    let resumed = source.replace(
        "(#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task next))))\n          (#call cancel-frame ((task cleanup)))\n          (#forget frame) (#return 42u64)",
        "(#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#forget frame) (#return answer)",
    );
    assert_ne!(resumed, source);
    build_and_run_graph(&resumed, 42);
    let overlapping = source.replace(
        "(#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll\n              (ChildTask.Start (#slice-mut-range container 0usize (#slice-mut-len container))))",
        "(#let child ChildTask (ChildTask.Start (#slice-mut-range container 0usize (#slice-mut-len container))))
          (#deref-set (#slice-mut-idx container 0usize) 0u64)
          (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll child)",
    );
    assert_ne!(overlapping, source);
    let error = graph_compile_error(&overlapping, "parent-access-with-live-slice-child");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.span.is_some(), "{error:?}");
}

#[test]
fn graph_child_cancellation_retains_a_shared_slice_descriptor() {
    let source = r#"
#enum ChildTask (#linear) ((ChildTask.Start (#ref (#slice #u64))) (ChildTask.Resume (#ref (#slice #u64))))

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady ()))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Start initial) (ChildPoll.ChildPending (ChildTask.Resume initial)))
            (#case (ChildTask.Resume final) (#block (#forget final) (ChildPoll.ChildReady ())))))
  );
}
#fn cancel-child {
  #params = ((task ChildTask));
  #returns = ();
  #body = (
          (#match task
            (#case (ChildTask.Start initial)
              (#assert (#u64::eq (#deref (#slice-idx (#deref initial) 0usize)) 42u64)))
            (#case (ChildTask.Resume final)
              (#assert (#u64::eq (#deref (#slice-idx (#deref final) 0usize)) 42u64))))
          (#return ())
  );
}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (cancel (cancel-frame ((await-0 cancel-child))))
          (function (#fn work () #u64
            (#let backing (#array #u64 1) (#array-of (#array #u64 1) 42u64))
            (#let container (#slice #u64) (#slice-of (#borrow backing)))
            (#await () ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Start (#borrow container)))
            (#let answer #u64 (#deref (#slice-idx container 0usize)))
            (#forget container) (#forget backing) (#return answer))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut frame Work::Frame (#call work ())) (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#pin frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let cleanup Work::Frame::Cleanup (#call Work::Poll::cleanup ((task next))))
          (#call cancel-frame ((task cleanup)))
          (#forget frame) (#return 42u64)
  );
}
"#;
    let generated = build_and_run_graph(source, 42);
    let cleanup = lim::parse_source_unit(&generated)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name.split_once(".lim::").map_or(name.as_str(), |(_, local)| local) == "Work::Poll::cleanup"))
        })
        .unwrap();
    let cleanup = &generated[cleanup.span.start..cleanup.span.end];
    assert!(
        cleanup.find("(#call cancel-child").unwrap()
            < cleanup
                .find("(#pin-borrow-mut (#get task binding-2))")
                .unwrap(),
        "the child's descriptor must not be cleared before its destructor"
    );
    // Exercise the opposite retained constructor too. Both destructor arms
    // read the descriptor; neither is rewritten into a dummy cleanup arm.
    let retained_start = source
        .replace(
            "(ChildPoll.ChildPending (ChildTask.Resume initial))",
            "(ChildPoll.ChildPending (ChildTask.Start initial))",
        )
        .replace(
            "(#block (#forget final) (ChildPoll.ChildReady ()))",
            "(ChildPoll.ChildPending (ChildTask.Start final))",
        )
        .replace(
            "(ChildTask.Start (#borrow container))",
            "(ChildTask.Resume (#borrow container))",
        );
    assert_ne!(retained_start, source);
    build_and_run_graph(&retained_start, 42);
}

#[test]
fn dereference_reborrows_keep_exclusivity_and_pin_kind() {
    let source = r#"#fn main {
  #params = ();
  #returns = #u64;
  #body = (
        (#let-mut value #u64 41u64)
        (#let parent (#ref-mut #u64) (#borrow-mut value))
        (#let shared (#ref #u64) (#borrow (#deref parent)))
        (#assert (#u64::eq (#deref shared) 41u64)) (#forget shared)
        (#let child (#ref-mut #u64) (#borrow-mut (#deref parent)))
        (#deref-set child 42u64) (#forget child) (#forget parent) (#return value)
  );
}
"#;
    build_and_run_graph(source, 42);
    let error = graph_compile_error(
        "#fn bad {\n  #params = ((view (#ref #u64)));\n  #returns = (#ref-mut #u64);\n  #body = ( (#return (#borrow-mut (#deref view)))\n  );\n}\n",
        "shared-dereference-reborrow",
    );
    assert!(error.message.contains("immutable"), "{error:?}");
    let error = graph_compile_error("#fn bad {\n  #params = ((view (#pin-ref-mut #u64)));\n  #returns = (#ref-mut #u64);\n  #body = ( (#return (#borrow-mut (#deref view)))\n  );\n}\n", "pinned-dereference-reborrow");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
}

#[test]
fn async_for_void_await_step_respects_continue_break_and_false_condition() {
    let source = r#"
#enum ConditionTask () ((ConditionTask.Check #bool))
#enum ConditionPoll () ((ConditionPoll.ConditionPending ConditionTask) (ConditionPoll.ConditionReady #bool))
#fn condition-poll {
  #params = ((task ConditionTask) (waker (#ref #u64)));
  #returns = ConditionPoll;
  #body = (
          (#return (#match task (#case (ConditionTask.Check run) (ConditionPoll.ConditionReady run))))
  );
}
#enum StepTask (#linear) (StepTask.Start StepTask.Resume)

#enum StepPoll () ((StepPoll.StepPending StepTask) (StepPoll.StepReady ()))
#fn step-poll {
  #params = ((task StepTask) (waker (#ref #u64)));
  #returns = StepPoll;
  #body = (
          (#return (#match task
            (#case StepTask.Start (StepPoll.StepPending StepTask.Resume))
            (#case StepTask.Resume (StepPoll.StepReady ()))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((run #bool) (stop #bool)) #u64
            (#let-mut keep #bool run)
            (#for ()
              (#await #bool ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll (ConditionTask.Check keep))
              (#await () StepTask StepPoll.StepPending StepPoll.StepReady step-poll StepTask.Start)
              (#set keep false)
              (#if stop (#break) (#continue)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((run true) (stop false)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending task) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#match second
            (#case (Work::Poll.Ready value) (#assert (#u64::eq value 42u64)))
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable))))
          (#let broken Work::Poll (#call Work::poll ((task (#call work ((run true) (stop true)))) (waker (#borrow waker)))))
          (#match broken
            (#case (Work::Poll.Ready value) (#assert (#u64::eq value 42u64)))
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable))))
          (#let skipped Work::Poll (#call Work::poll ((task (#call work ((run false) (stop false)))) (waker (#borrow waker)))))
          (#return (#match skipped
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
  );
}
    "#;
    build_and_run(source, 42);
    let synchronous_condition = source.replace(
        "(#await #bool ConditionTask ConditionPoll.ConditionPending ConditionPoll.ConditionReady condition-poll (ConditionTask.Check keep))",
        "keep",
    );
    assert_ne!(synchronous_condition, source);
    build_and_run(&synchronous_condition, 42);
    build_and_run(include_str!("../examples/async_for_unit_step.lim"), 42);
}

#[test]
fn awaited_for_condition_runs_step_after_continue_but_not_break() {
    let source = "#enum ChildTask () ((ChildTask.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #bool))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (ChildTask.Waiting value)
              (#if (#u64::eq value 0u64)
                (ChildPoll.ChildPending (ChildTask.Waiting 1u64))
                (ChildPoll.ChildReady (#u64::lt value 3u64))))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#for (#set iteration 0u64)
                  (#await ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll (ChildTask.Waiting iteration))
                  (#set iteration (#u64::add-wrap iteration 1u64))
              (#match iteration
                (#case 0u64 (#continue))
                (#case 1u64 ())
                (#case _ (#break))))
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let value #u64 (#match second
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending pending-again) (#block (#forget pending-again) 0u64))))
          (#forget waker)
          (#return (#if (#u64::eq value 2u64) 42u64 0u64))\n  );\n}\n";
    build_and_run(source, 42);
}

#[test]
fn explicit_await_contracts_are_checked_before_loop_lowering() {
    let source = include_str!("../examples/async_for_patterns.lim");
    let invalid = source.replace(
        "(#set iteration (#u64::add-wrap iteration 1u64))",
        "(#set iteration (#await #u32 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start (#u64::add-wrap iteration 1u64))))",
    );
    let error = graph_compile_error(&invalid, "async-explicit-result-contracts");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error
            .message
            .contains("#await result type does not match its Ready payload"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("an explicit await contract error has its own source span");
    assert_eq!(
        span.start,
        invalid.find("#await #u32").unwrap() + "#await ".len(),
        "{error:?}"
    );
    assert_eq!(&invalid[span.start..span.end], "#u32", "{error:?}");
    let with_condition = format!("#struct TestTask () ((decision #bool))
#enum TestPoll () ((TestPoll.TestPending TestTask) (TestPoll.TestReady #bool))
#fn test-poll {{
  #params = ((task TestTask) (waker (#ref #u64)));
  #returns = TestPoll;
  #body = (
          (#return (TestPoll.TestReady (#get task decision)))
  );
}}\n{}", source.replace(
        "(#u64::lt iteration limit)",
        "(#await #bool TestTask TestPoll.TestPending TestPoll.TestReady test-poll (#struct-literal TestTask ((decision (#u64::lt iteration limit)))))"));
    let body_error = with_condition.replace(
        "(#await Step StepPoll.StepPending",
        "(#await #u32 Step StepPoll.StepPending",
    );
    let error = graph_compile_error(&body_error, "async-explicit-body-result-contracts");
    assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
    assert!(
        error
            .message
            .contains("#await result type does not match its Ready payload"),
        "{error:?}"
    );
    let span = error.span.unwrap();
    assert_eq!(
        span.start,
        body_error.find("#await #u32").unwrap() + "#await ".len(),
        "{error:?}"
    );
    assert_eq!(&body_error[span.start..span.end], "#u32");
    let aliased = format!("#type Index #u64\n{}", source
        .replace("(z (#tuple #u64 #u64))", "(z (#tuple Index #u64))")
        .replace("(#set iteration (#u64::add-wrap iteration 1u64))", "(#set iteration (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start (#u64::add-wrap iteration 1u64))))")
        .replace("0u64 4u64", "0u64 8u64"));
    build_and_run_graph(&aliased, 42);
}

#[test]
fn async_for_initializers_register_every_declared_pattern_leaf() {
    let source = include_str!("../examples/async_for_patterns.lim");
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
    build_and_run_graph(
        &source.replace(
            "(StepPoll.StepPending (Step.Resume value))",
            "(StepPoll.StepReady value)",
        ),
        42,
    );
    build_and_run_graph(
        &source
            .replace("0u64 2u64", "0u64 0u64")
            .replace("(StepPoll.StepPending (Step.Resume value))", "(#panic)"),
        1,
    );
    let aliased = format!(
        "#type BoundsAlias Bounds\n{}",
        source
            .replace("(bounds Bounds)", "(bounds BoundsAlias)")
            .replace("bias) Bounds bounds", "bias) BoundsAlias bounds")
    );
    build_and_run_graph(&aliased, 42);
    let narrow = source
        .replace(
            "(z (#tuple #u64 #u64)) (a #u64)",
            "(z (#tuple #u8 #u16)) (a #u32)",
        )
        .replace(
            "(#u64::lt iteration limit)",
            "(#u8::lt iteration (#as limit #u8))",
        )
        .replace(
            "(#u64::add-wrap iteration 1u64)",
            "(#u8::add-wrap iteration 1u8)",
        )
        .replace(
            "(Step.Start iteration)",
            "(Step.Start (#as iteration #u64))",
        )
        .replace("value bias)", "value (#as bias #u64))")
        .replace(
            "(a 20u64) (z (#tuple (#tuple #u64 #u64) 0u64 2u64))",
            "(a 20u32) (z (#tuple (#tuple #u8 #u16) 0u8 2u16))",
        );
    build_and_run_graph(&narrow, 42);
    let awaited =
        format!("#enum InitTask () ((InitTask.InitStart Bounds) (InitTask.InitResume Bounds))
#enum InitPoll () ((InitPoll.InitPending InitTask) (InitPoll.InitReady Bounds))
#fn init-poll {{
  #params = ((task InitTask) (waker (#ref #u64)));
  #returns = InitPoll;
  #body = (
          (#return (#match task
            (#case (InitTask.InitStart bounds) (InitPoll.InitPending (InitTask.InitResume bounds)))
            (#case (InitTask.InitResume bounds) (InitPoll.InitReady bounds))))\n  );
}}
{}", source.replace(
            "bias) Bounds bounds)",
            "bias) Bounds (#await InitTask InitPoll.InitPending InitPoll.InitReady init-poll (InitTask.InitStart bounds)))"));
    build_and_run_graph(&awaited, 42);
    build_and_run_graph(
        &awaited.replace("(#await InitTask", "(#await Bounds InitTask"),
        42,
    );
    let condition = format!("#struct TestTask () ((decision #bool) (resume #bool))
#enum TestPoll () ((TestPoll.TestPending TestTask) (TestPoll.TestReady #bool))
#fn test-poll {{
  #params = ((task TestTask) (waker (#ref #u64)));
  #returns = TestPoll;
  #body = (
          (#return (#if (#get task resume) (TestPoll.TestReady (#get task decision))
            (TestPoll.TestPending (#struct-literal TestTask ((decision (#get task decision)) (resume true))))))
  );
}}\n{}", source
        .replace("(#u64::lt iteration limit)", "(#await #bool TestTask TestPoll.TestPending TestPoll.TestReady test-poll (#struct-literal TestTask ((decision (#u64::lt iteration limit)) (resume false))))")
        .replace("0u64 4u64", "0u64 12u64"));
    build_and_run_graph(&condition, 42);
    let step = source.replace(
        "(#set iteration (#u64::add-wrap iteration 1u64))",
        "(#set iteration (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start (#u64::add-wrap iteration 1u64))))",
    ).replace("0u64 4u64", "0u64 12u64");
    build_and_run_graph(&step, 42);
    let all_phases = condition.replace(
        "(#set iteration (#u64::add-wrap iteration 1u64))",
        "(#set iteration (#await #u64 Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Start (#u64::add-wrap iteration 1u64))))",
    );
    build_and_run_graph(&all_phases, 42);
    let referenced = source
        .replace("(a #u64)", "(a (#ref #u64))")
        .replace("value bias)", "value (#deref bias))")
        .replace(
            "(#let waker #u64",
            "(#let-mut owner #u64 20u64) (#let waker #u64",
        )
        .replace("(a 20u64)", "(a (#borrow owner))");
    build_and_run_graph(&referenced, 42);
    build_and_run_graph(
        &referenced
            .replace("(a (#ref #u64))", "(a (#ref-mut #u64))")
            .replace("(#borrow owner)", "(#borrow-mut owner)"),
        42,
    );
    build_and_run_graph(
        &referenced.replace(
            "(#block (#return value))",
            "(#block (#set owner 99u64) (#return value))",
        ),
        42,
    );
    build_and_run_graph(
        &referenced.replace(
            "(#block (#set task next) ())",
            "(#block (#forget next) (#set owner 99u64) (#return owner))",
        ),
        99,
    );
    let error_for = |source: &str| graph_compile_error(source, "async-for-pattern-errors");
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
        "(#return (#u64::add-wrap total",
        "(#let leaked #u64 limit) (#return (#u64::add-wrap total",
    ));
    assert!(
        leaked.message.contains("limit") && leaked.message.contains("unknown"),
        "{leaked:?}"
    );
    assert!(leaked.span.is_some(), "{leaked:?}");
    let invalid_type = condition.replace(
        "(#await Step StepPoll.StepPending",
        "(#await #u32 Step StepPoll.StepPending",
    );
    let mismatch = error_for(&invalid_type);
    assert_eq!(mismatch.code, lim::DiagnosticCode::Type, "{mismatch:?}");
    assert!(
        mismatch
            .message
            .contains("#await result type does not match its Ready payload"),
        "{mismatch:?}"
    );
    let span = mismatch
        .span
        .expect("loop await mismatch keeps its explicit type span");
    assert_eq!(&invalid_type[span.start..span.end], "#u32");
    assert_eq!(
        span.start,
        invalid_type.find("#await #u32 Step").unwrap() + "#await ".len()
    );
}

#[test]
fn async_function_resumes_child_await_inside_for_with_local_initializer() {
    let source = "#struct Child () ((iteration #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-value {
  #params = ((iteration #u64));
  #returns = #u64;
  #body = ( (#return iteration)
  );
}
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#let value #u64 (#get task iteration))
          (#return (#if (#u64::eq value 0u64)
            (ChildPoll.ChildPending (#struct-literal Child ((iteration 1u64))))
            (ChildPoll.ChildReady value)))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#for (#let-mut iteration #u64 0u64)
                  (#u64::lt iteration 2u64)
                  (#set iteration (#u64::add-wrap iteration 1u64))
              (#let result #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll
                  (#struct-literal Child ((iteration
                    (#call child-value ((iteration iteration)))))))))
            (#let iteration #u64 42u64)
            (#return iteration))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending-again)
                (#block (#forget pending-again) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_rejects_for_initializer_shadowing() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (ChildPoll.ChildReady 1u64))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 5u64)
            (#for (#let-mut iteration #u64 0u64)
                  (#u64::lt iteration 2u64)
                  (#set iteration (#u64::add-wrap iteration 1u64))
              (#let result #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting iteration))))
            (#return 42u64))))\n";
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
    let source = "#enum ChildPoll () ((ChildPoll.ChildPending #u64) (ChildPoll.ChildReady #u64))
#enum Decision () (Decision.Stop Decision.Continue)
#fn child-poll {
  #params = ((task #u64) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#if (#u64::eq task 0u64)
            (ChildPoll.ChildPending 1u64)
            (ChildPoll.ChildReady task)))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#loop
              (#let result #u64
                (#await #u64 ChildPoll.ChildPending ChildPoll.ChildReady child-poll iteration))
              (#set iteration result)
              (#set iteration (#u64::add-wrap iteration 1u64))
              (#let decision Decision
                (#if (#u64::eq iteration 2u64) (Decision.Stop) (Decision.Continue)))
              (#match decision
                (#case Decision.Stop (#break))
                (#case Decision.Continue (#continue))))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
          (#let result #u64
            (#match second
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending pending-again)
                (#block (#forget pending-again) (#unreachable)))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_does_not_hoist_awaits_out_of_loop_forms() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting value) (ChildPoll.ChildPending (Child.Waiting value)))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#loop
              (#let result #u64
                (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64))))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let outcome Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let result #u64
            (#match outcome
              (#case (Work::Poll.Pending pending) (#block (#forget pending) 42u64))
              (#case (Work::Poll.Ready value) value)))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_loop_body_supports_more_than_two_suspensions() {
    let source = "#enum ChildTask (#linear) (ChildTask.Waiting ChildTask.Resuming)

#enum ChildPoll () ((ChildPoll.ChildPending ChildTask) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task ChildTask) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case ChildTask.Waiting (ChildPoll.ChildPending ChildTask.Resuming))
            (#case ChildTask.Resuming (ChildPoll.ChildReady 2u64))))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut total #u64 0u64)
            (#loop
              (#let first #u64
                (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting))
              (#let second #u64
                (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting))
              (#let third #u64
                (#await #u64 ChildTask ChildPoll.ChildPending ChildPoll.ChildReady child-poll ChildTask.Waiting))
              (#set total
                (#u64::add-wrap total
                  (#u64::add-wrap first (#u64::add-wrap second third))))
              (#break))
            (#assert (#u64::eq total 6u64))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let first Work::Poll
            (#call Work::poll ((task (#call work ())) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending first-task) Work::Poll first (#unreachable))
          (#let second Work::Poll
            (#call Work::poll ((task first-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending second-task) Work::Poll second (#unreachable))
          (#let third Work::Poll
            (#call Work::poll ((task second-task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending third-task) Work::Poll third (#unreachable))
          (#let fourth Work::Poll
            (#call Work::poll ((task third-task) (waker (#borrow waker)))))
          (#let result #u64
            (#match fourth
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending unexpected)
                (#block (#forget unexpected) 0u64))))
          (#forget waker)
          (#return result)\n  );\n}\n";
    let generated = build_and_run_graph(source, 42);
    assert_single_poll(&generated, "Work::poll");
}

#[test]
fn async_function_preserves_loop_locals_used_after_suspension() {
    let source = "#enum Child () ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (ChildPoll.ChildReady 1u64))
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work () #u64
            (#let-mut iteration #u64 0u64)
            (#while (#u64::lt iteration 1u64)
              (#let-mut child-input #u64 iteration)
              (#let result #u64
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting child-input)))
              (#set child-input result)
              (#set iteration (#u64::add-wrap iteration 1u64)))
            (#return 42u64))))\n";
    let driver = "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64) (#let-mut task Work::Task (#call work ()))
          (#for-range (attempt #u64) 0u64 4u64
            (#let outcome Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
            (#match outcome
              (#case (Work::Poll.Pending next) (#block (#set task next) ()))
              (#case (Work::Poll.Ready value) (#block (#return value)))))
          (#forget task) (#return (#unreachable))\n  );\n}\n";
    build_and_run(&format!("{source}\n{driver}"), 42);
    let pending = source.replace(
        "(#return (ChildPoll.ChildReady 1u64))",
        "(#return (#match task (#case (Child.Waiting count)
          (#if (#u64::eq count 0u64) (ChildPoll.ChildPending (Child.Waiting 1u64)) (ChildPoll.ChildReady 1u64)))))",
    );
    build_and_run(&format!("{pending}\n{driver}"), 42);
}

#[test]
fn async_function_can_suspend_at_each_await() {
    let original = example_without_cancel_work();
    let (prefix, _) = original.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let prefix = prefix.replace(
        "(#return (#u64::add-wrap total offset))",
        "(#let second #u64
           (#await Step StepPoll.StepPending StepPoll.StepReady step-poll (Step.Waiting 1u64)))
         (#return (#u64::add-wrap total offset))",
    );
    let source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
             (#let executor Executor
               (#struct-literal Executor ((notifications
                 (#call CellU64::create ((value 0u64)))))))
             (#let waker LocalWaker
               (#call local-waker-create ((executor (#borrow executor)) (metadata (#struct-literal WakeMetadata ((amount 1u64)))))))
             (#let first Work::Poll
               (#call Work::poll ((task (#call work ((offset 1u64)))) (waker (#borrow waker)))))
             (#let-else (Work::Poll.Pending first-task) Work::Poll first (#unreachable))
             (#let second Work::Poll
               (#call Work::poll ((task first-task) (waker (#borrow waker)))))
             (#let-else (Work::Poll.Pending second-task) Work::Poll second (#unreachable))
             (#let third Work::Poll
               (#call Work::poll ((task second-task) (waker (#borrow waker)))))
             (#let value #u64
               (#match third
                 (#case (Work::Poll.Ready result) result)
                 (#case (Work::Poll.Pending task)
                   (#block (#forget task) (#unreachable)))))
             (#call local-waker-destroy ((waker waker)))
             (#let executor-ref (#ref Executor) (#borrow executor))
             (#let notifications #u64 (#call CellU64::get ((cell (#borrow (#get executor-ref notifications))))))
             (#drop executor-ref)
             (#forget executor)
             (#return (#u64::add-wrap value notifications))
  );\n}}\n"
    );
    build_and_run_graph(&source, 43);
}

#[test]
fn async_function_pending_state_can_be_cancelled_explicitly() {
    let original = example_source();
    let (prefix, _) = original.split_once("#fn main {\n  #params = ();\n  #returns = #u64;").unwrap();
    let source = format!(
        "{prefix}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
             (#let executor Executor
               (#struct-literal Executor ((notifications
                 (#call CellU64::create ((value 0u64)))))))
             (#let waker LocalWaker
               (#call local-waker-create ((executor (#borrow executor)) (metadata (#struct-literal WakeMetadata ((amount 1u64)))))))
             (#let first Work::Poll
               (#call Work::poll ((task (#call work ((offset 1u64)))) (waker (#borrow waker)))))
             (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))
             (#call cancel-work ((task (#call Work::Poll::cleanup ((task pending))))))
             (#call local-waker-destroy ((waker waker)))
             (#let executor-ref (#ref Executor) (#borrow executor))
             (#let notifications #u64 (#call CellU64::get ((cell (#borrow (#get executor-ref notifications))))))
             (#drop executor-ref)
             (#forget executor)
             (#return notifications)
  );\n}}\n"
    );
    build_and_run_graph(&source, 1);
}

#[test]
fn generated_async_frames_support_source_named_task_cancellation() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (#match task
            (#case (Child.Waiting remaining)
              (#if (#u64::eq remaining 0u64)
                (ChildPoll.ChildReady 42u64)
                (ChildPoll.ChildPending (Child.Waiting (#u64::sub-wrap remaining 1u64)))))))
  );
}
#fn child-cancel {
  #params = ((task Child));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((offset #u64)) #u64
            (#let value #u64
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 2u64)))
            (#return (#u64::add-wrap value offset)))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker #u64 0u64)
          (#let frame Work::Task (#call work ((offset 40u64))))
          (#let first Work::Poll (#call Work::poll ((task frame) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending pending-frame) Work::Poll first (#unreachable))
          (#call cancel-frame ((task (#call Work::Poll::cleanup ((task pending-frame))))))
          (#forget waker)
          (#return 42u64)\n  );\n}\n";
    let source = source.replace(
        "(waker #u64) (function",
        "(waker #u64) (cancel (cancel-frame ((await-0 child-cancel)))) (function",
    );
    build_and_run_graph(&source, 42);
}

#[test]
fn async_fn_generates_source_specific_cancel_dispatch() {
    let source = include_str!("../examples/async_fn_cancel_dispatch.lim");
    let generated = build_and_run_graph(source, 42);
    assert!(generated_contains_form(
        &generated,
        "(#fn cancel-work ((task Work::Task::Cleanup)) ())"
    ));
    assert!(generated.contains("Work::Task::Cleanup::Token.Full"));
    assert!(generated.contains("Work::Task::Cleanup::Await-0.Full"));
    assert!(generated.contains("child-cancel"));
}

#[test]
fn async_fn_cancel_mapping_must_cover_each_source_slot() {
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (ChildPoll.ChildReady 1u64))
  );
}
#generate #async-fn ((protocol work-await)
                    (waker #u64)
                    (cancel (cancel-frame ()))
                    (function
          (#fn work ((input #u64)) #u64
            (#let result #u64
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting input)))
            (#return result))))\n";
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
    let source = "#enum Child (#linear) ((Child.Waiting #u64))

#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll {
  #params = ((task Child) (waker (#ref #u64)));
  #returns = ChildPoll;
  #body = (
          (#return (ChildPoll.ChildPending task))
  );
}
#fn child-cancel {
  #params = ((task Child));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#enum Token (#linear) ((Token.TokenValue #u64))

#fn destroy-token {
  #params = ((task Token));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#generate #async-fn-pinned ((protocol work-await)
                    (waker #u64)
                    (cancel (cancel-frame
                      ((token destroy-token) (await-0 child-cancel))))
                    (function
          (#fn work ((token Token)) #u64
            (#let child-result #u64
              (#await #u64 Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Waiting 0u64)))
            (#call destroy-token ((task token)))
            (#return 42u64))))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut frame Work::Frame (#call work ((token (Token.TokenValue 1u64)))))
          (#let waker #u64 0u64)
          (#let outcome Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending cancel-pin) Work::Poll outcome (#unreachable))
          (#let state Work::Frame::Cleanup (#call Work::Poll::cleanup ((task cancel-pin))))
          (#call cancel-frame ((task state)))
          (#forget frame)
          (#forget waker)
          (#return 42u64)\n  );\n}\n";
    build_and_run_graph(source, 42);
}
