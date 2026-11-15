#[path = "support/generated_source.rs"]
mod generated_source;
mod support;

use std::{fs, process::Command, time::Duration};

const CONTEXT: &str = "
#enum Child (#linear) ((Child.Start #u64) (Child.Resume #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
      (#return (#match task
        (#case (Child.Start value) (ChildPoll.ChildPending (Child.Resume value)))
        (#case (Child.Resume value) (ChildPoll.ChildReady value))))
#fn cancel-child ((child Child)) () (#forget child) (#return ())\n";

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

fn checked_artifact(source: &str, label: &str) -> (support::Scratch, String, String) {
    let scratch = support::Scratch::new(label);
    let path = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let output = scratch.path().join("generated");
    for _ in 0..2 {
        let program =
            lim::parse_program_from_path_with_config_and_cache(source, &path, &config(), &cache)
                .unwrap_or_else(|error| panic!("{error}\n{source}"));
        lim::check_types(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
        lim::write_generated_sources_from_path_with_config_and_cache(
            source,
            &path,
            &output,
            &config(),
            &cache,
        )
        .unwrap();
    }
    let artifact = fs::read_dir(&output)
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .find(|text| generated_source::contains_function(text, "Work::poll"))
        .unwrap();
    assert!(artifact.starts_with("// Generated from:"));
    assert!(generated_source::contains_declaration(
        &artifact,
        "#syntax",
        "WorkAwait"
    ));
    assert!(!artifact.contains("#await") && !artifact.contains("#generate #async-fn"));
    let invocation = lim::parse_source_unit(source)
        .unwrap()
        .into_iter()
        .find(|node| {
            source[node.span.start..node.span.end]
                .strip_prefix("#generate ")
                .is_some_and(|rest| rest.trim_start().starts_with("#async-fn"))
        })
        .unwrap();
    let ordinary_artifact = generated_source::ordinary_source_in_file(&artifact, &path);
    let standalone = format!(
        "{}\n{ordinary_artifact}\n{}",
        &source[..invocation.span.start],
        &source[invocation.span.end..]
    );
    let ordinary = lim::parse_program_from_path(&standalone, &path)
        .unwrap_or_else(|error| panic!("{error}\n{standalone}"));
    lim::check_types(&ordinary).unwrap_or_else(|error| panic!("{error}\n{standalone}"));
    (scratch, artifact, standalone)
}

fn run(source: &str, label: &str) -> String {
    run_expected(source, label, 42)
}

fn run_expected(source: &str, label: &str, expected: i32) -> String {
    run_expected_output(source, label, expected, &[])
}

fn run_expected_output(source: &str, label: &str, expected: i32, expected_stdout: &[u8]) -> String {
    let (scratch, artifact, standalone) = checked_artifact(source, label);
    let ordinary =
        lim::parse_program_from_path(&standalone, &scratch.path().join("input.lim")).unwrap();
    let assembly = lim::generate_assembly(&ordinary).unwrap_or_else(|error| {
        let line = error
            .split(':')
            .next()
            .and_then(|line| line.parse::<usize>().ok())
            .unwrap_or(1);
        let excerpt = standalone
            .lines()
            .skip(line.saturating_sub(3))
            .take(6)
            .collect::<Vec<_>>()
            .join("\n");
        panic!("{error}\n{excerpt}")
    });
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
    assert_eq!(status.code(), Some(expected), "{stderr:?}");
    assert_eq!(stdout, expected_stdout);
    assert!(stderr.is_empty());
    artifact
}

#[test]
fn printing_between_pending_and_resume_needs_no_stored_slice_cells() {
    let source = include_str!("../examples/async_fn.lim").replace(
        "\"../library/",
        &format!("\"{}/library/", env!("CARGO_MANIFEST_DIR")),
    );
    let artifact = run_expected_output(
        &source,
        "async-printing-pending",
        42,
        include_bytes!("fixtures/async_fn.stdout"),
    );
    assert!(artifact.contains("#slice-of"));
    assert!(artifact.contains("#word-view"));
    assert!(
        !artifact.contains("(#slice #char)"),
        "synchronous slices must not inhabit the future frame"
    );
}

#[test]
fn public_cancellation_examples_use_cleanup_slots_not_legacy_state_variants() {
    for (source, label, expected) in [
        (
            include_str!("../examples/async_fn_cancel_dispatch.lim"),
            "async-cancel-slots",
            42,
        ),
        (
            include_str!("../examples/async_fn_pinned.lim"),
            "async-pinned-cleanup-slots",
            41,
        ),
        (
            include_str!("../examples/async_single_poll.lim"),
            "async-single-poll-cleanup-slots",
            42,
        ),
    ] {
        let source = source.replace(
            "\"../library/pin.lim\"",
            &format!("\"{}/library/pin.lim\"", env!("CARGO_MANIFEST_DIR")),
        );
        run_expected(&source, label, expected);
    }
}

#[test]
fn self_reference_example_uses_source_named_access_and_cleanup_on_the_same_frame() {
    let source = include_str!("../examples/async_fn_self_reference.lim")
        .replace("read-after-await", "work")
        .replace("Read::after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait");
    let artifact = run_expected(&source, "async-graph-self-reference-example", 58);
    assert!(artifact.contains("#fn work-owner-replace "));
    assert!(artifact.contains("#fn work-owner-read "));
    assert!(artifact.contains("#struct Work::Frame::Cleanup (#linear)"));
    assert!(!source.contains("Work::Poll::cancel"));
    assert!(!source.contains("work-frame-await-0"));
    assert!(!source.contains("(#set-field frame owner"));
    assert!(!source.contains("(#set-field cancelled owner"));
}

#[test]
fn self_reference_graph_pending_handle_blocks_frame_destruction() {
    let original = include_str!("../examples/async_fn_self_reference.lim");
    let prefix = original
        .split("  (#let second Read-after-await::Poll")
        .next()
        .unwrap();
    let source = format!("{prefix}
      (#forget frame)
      (#let second Read-after-await::Poll
        (#call Read-after-await::poll ((task pending-frame) (waker (#borrow waker)))))
      (#return (#match second (#case (Read-after-await::Poll.Ready value) value)
        (#case (Read-after-await::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable))))))");
    let scratch = support::Scratch::new("async-graph-self-reference-pending");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("the parent frame must remain alive through a live Pending handle");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    let start = source.find("(#forget frame)").unwrap();
    assert!(
        span.start >= start && span.end <= start + "(#forget frame)".len(),
        "{error:?}"
    );
}

#[test]
fn graph_allows_reading_copy_owner_data_while_shared_self_references_are_retained() {
    let source = include_str!("../examples/async_fn_self_reference.lim")
        .replace("read-after-await", "work")
        .replace("Read::after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait")
        .replace("(#u64::add-wrap (#u64::add-wrap (#deref view) (#deref right-view)) result)",
            "(#u64::add-wrap (#u64::add-wrap (#u64::add-wrap (#deref view) (#deref right-view)) result) (#get (#get owner payload) left))");
    run_expected(&source, "async-graph-self-reference-owner-read", 98);
}

#[test]
fn enum_self_reference_example_checks_and_runs_as_standalone_graph_code() {
    let source = include_str!("../examples/async_fn_enum_self_reference.lim")
        .replace("read-after-await", "work")
        .replace("Read::after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait");
    run_expected(&source, "async-enum-self-reference-graph", 42);
}

#[test]
fn enum_self_reference_graph_pending_handle_blocks_frame_destruction() {
    let source = include_str!("../examples/async_fn_enum_self_reference.lim")
        .replace("    (#forget frame)\n    (#forget waker)", "  (#forget waker)")
        .replace(
            "  (#let second Read-after-await::Poll",
            "  (#forget frame)\n  (#let second Read-after-await::Poll",
        );
    let scratch = support::Scratch::new("async-enum-self-reference-pending-conflict");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("a live Pending handle must keep its frame alive");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error
        .span
        .expect("caller conflict must retain its source span");
    let start = source.find("(#forget frame)").unwrap();
    assert!(
        span.start >= start && span.end <= start + "(#forget frame)".len(),
        "{error:?}"
    );
    assert!(error.message.contains("borrow"), "{error:?}");
}

#[test]
fn enum_self_reference_public_cleanup_handles_entry_pending_and_ready() {
    let counter = "#struct Counter (#linear) ((storage (#atomic #u64)))
#fn read-counter ((count (#ref Counter))) #u64
          (#return (#atomic-load (#borrow (#get count storage)) #memory-relaxed))
#fn bump-counter ((count (#ref Counter))) ()
          (#atomic-store (#borrow (#get count storage))
            (#u64::add-wrap (#call read-counter ((count count))) 1u64) #memory-relaxed)
          (#return ())\n";
    let prefix = include_str!("../examples/async_fn_enum_self_reference.lim")
        .split("#fn main")
        .next()
        .unwrap()
        .replace("read-after-await", "work")
        .replace("Read::after-await", "Work")
        .replace("ReadAfterAwaitAwait", "WorkAwait")
        .replace("(waker #u64)", "(waker #u64) (cancel (work-cancel ((await-0 cancel-child))))")
        .replace(
            "#enum Child (#linear) ((Child.Waiting #u64))",
            "#enum Child (#linear) ((Child.Waiting (#tuple (#ref Counter) #u64)))",
        )
        .replace("(Child.Waiting count)", "(Child.Waiting (#tuple counter count))")
        .replace("Child.Waiting 1u64", "Child.Waiting (#tuple counter 1u64)")
        .replace("Child.Waiting 0u64", "Child.Waiting (#tuple counter 0u64)")
        .replace("(#fn work ((owner Owner))", "(#fn work ((owner Owner) (counter (#ref Counter)))")
        .replace("(#forget task) (#return ())", "(#match task (#case (Child.Waiting (#tuple counter count)) (#block (#call bump-counter ((count counter))) (#drop counter) ()))) (#return ()))");
    let first = "(#let first Work::Poll (#call Work::poll ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
      (#let-else (Work::Poll.Pending pending) Work::Poll first (#unreachable))";
    let second =
        "(#let second Work::Poll (#call Work::poll ((task pending) (waker (#borrow waker)))))
      (#let answer #u64 (#match second (#case (Work::Poll.Ready value) value)
        (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
      (#assert (#u64::eq answer 42u64))";
    for (polls, handle, cancellations) in [
        (String::new(), "(#pin-borrow-mut task)", 0),
        (first.to_owned(), "pending", 1),
        (format!("{first}\n{second}"), "(#pin-borrow-mut task)", 0),
    ] {
        let source = format!(
            "{counter} {prefix}
#fn main () #u64 (#let waker #u64 0u64)
              (#let count Counter (#struct-literal Counter ((storage (#atomic-init #u64 0u64)))))
              (#let-mut task Work::Frame (#call work ((owner (#struct-literal Owner
                ((choice (Choice.Number (#struct-literal NumberPayload ((value 40u64)))))))) (counter (#borrow count)))))
              {polls}
              (#call work-cancel ((task (#call Work::Poll::cleanup ((task {handle}))))))
              (#call work-cancel ((task (#call Work::Poll::cleanup ((task (#pin-borrow-mut task)))))))
              (#assert (#u64::eq (#call read-counter ((count (#borrow count)))) {cancellations}u64))
              (#forget count) (#forget task) (#return 42u64)\n"
        );
        run_expected(&source, "async-enum-self-reference-public-cleanup", 42);
    }
}

#[test]
fn source_named_cleanup_runs_at_entry_pending_ready_and_repeated_cancel() {
    let first = "(#let first Work::Poll (#call Work::poll ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
      (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))";
    let second = "(#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
      (#case (Work::Poll.Ready value) value) (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
      (#assert (#u64::eq answer 42u64))";
    for (polls, handle) in [
        (String::new(), "(#pin-borrow-mut task)"),
        (first.into(), "next"),
        (format!("{first}\n{second}"), "(#pin-borrow-mut task)"),
    ] {
        let source = format!(
            "{CONTEXT}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
              (cancel (work-cancel ((await-0 cancel-child))))
              (function (#fn work ((seed #u64)) #u64
                (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed))))))
#fn main () #u64 (#let waker #u64 0u64)
              (#let-mut task Work::Frame (#call work ((seed 42u64)))) {polls}
              (#call work-cancel ((task (#call Work::Poll::cleanup ((task {handle}))))))
              (#call work-cancel ((task (#call Work::Poll::cleanup ((task (#pin-borrow-mut task)))))))
              (#forget task) (#return 42u64)\n"
        );
        let artifact = run(&source, "async-graph-cancel");
        assert!(artifact.contains(
            "#struct Work::Frame::Cleanup (#linear) ((await-0 Work::Frame::Cleanup::Await-0))"
        ));
    }
}

#[test]
fn movable_cleanup_consumes_the_frame_at_entry_and_pending() {
    for (polls, task) in [
        ("", "task"),
        (
            "(#let first Work::Poll (#call Work::poll ((task task) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))",
            "next",
        ),
    ] {
        let source = format!(
            "{CONTEXT}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
              (cancel (work-cancel ((await-0 cancel-child))))
              (function (#fn work ((seed #u64)) #u64
                (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed))))))
#fn main () #u64 (#let waker #u64 0u64)
              (#let task Work::Task (#call work ((seed 42u64)))) {polls}
              (#call work-cancel ((task (#call Work::Poll::cleanup ((task {task}))))))
              (#return 42u64)\n"
        );
        run(&source, "async-graph-movable-cleanup");
        let invalid = source.replace("(#return 42u64)", "(#forget task) (#return 42u64)");
        assert!(lim::parse_program_with_config(&invalid, &config()).is_err());
    }
}

#[test]
fn movable_dynamic_store_preserves_selection_in_cached_and_standalone_code() {
    let source = format!(
        "{CONTEXT}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (cancel (work-cancel ((await-0 cancel-child))))
          (function (#fn work ((seed #u64)) #u64
            (#let-mut index #usize 1usize)
            (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 0u64 9u64))
            (#set-index values index (#block (#set index 0usize)
              (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed))))
            (#assert (#u64::eq (#index values 0usize) 0u64))
            (#return (#index values 1usize)))))
#fn main () #u64
          (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll
            ((task (#call work ((seed 42u64)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
          (#let cancelled Work::Poll (#call Work::poll
            ((task (#call work ((seed 90u64)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending cancel-task) Work::Poll cancelled (#unreachable))
          (#call work-cancel ((task (#call Work::Poll::cleanup ((task cancel-task))))))
          (#return answer)\n"
    );
    let artifact = run(&source, "async-movable-dynamic-store");
    assert!(artifact.contains("index."));
    assert!(!artifact.contains("select-address"));
    assert!(artifact.contains("(#usize::lt"));
}

#[test]
fn guard_preview_keeps_linear_scrutinee_through_rejection_and_resumption() {
    let source = format!("{CONTEXT}
#generate #async-fn ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((seed #u64)) #u64
            (#let child Child (Child.Start seed))
            (#return (#match child
              (#case (Child.Start amount)
                (#when (#u64::eq (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)) 1u64))
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 99u64)))
              (#case (Child.Start amount) (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start amount)))
              (#case (Child.Resume amount) amount))))))
#fn main () #u64 (#let waker #u64 0u64)
          (#let first Work::Poll (#call Work::poll ((task (#call work ((seed 42u64)))) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let second Work::Poll (#call Work::poll ((task next) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending last) Work::Poll second (#unreachable))
          (#return (#match (#call Work::poll ((task last) (waker (#borrow waker))))
            (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))\n");
    run(&source, "async-graph-guard");
}

fn shared_reference_guard_source() -> String {
    include_str!("fixtures/async_reference_guard.lim").to_owned()
}

#[test]
fn shared_reference_guard_preview_keeps_the_referent_through_rejected_awaits() {
    run(
        &shared_reference_guard_source(),
        "async-graph-reference-guard",
    );
}

fn aggregate_reference_guard_source() -> String {
    shared_reference_guard_source()
        .replace(
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)))",
            "#struct View () ((value (#ref #u64)))\n#enum Holder (#linear) ((Holder.Holding View))",
        )
        .replace(
            "(Holder.Holding source)",
            "(Holder.Holding (#struct-literal View ((value source))))",
        )
        .replace("(#deref view)", "(#deref (#get view value))")
}

#[test]
fn copy_reference_aggregate_guard_retains_nested_referents_across_rejection() {
    run(
        &aggregate_reference_guard_source(),
        "async-graph-aggregate-reference-guard",
    );
}

#[test]
fn linear_reference_aggregate_guard_lends_stationary_preview_aliases() {
    run(
        &linear_reference_guard_source(),
        "async-graph-linear-reference-guard",
    );
}

#[test]
fn linear_exclusive_reference_aggregate_guard_lends_without_copying_the_handle() {
    let source = exclusive_reference_guard_source(&linear_reference_guard_source())
        .replace(
            "View (#linear) ((value (#ref #u64)))",
            "View (#linear) ((value (#ref-mut #u64)))",
        )
        .replace(
            "(#deref (#get (#borrow view) value))",
            "(#call read-view ((view (#borrow view))))",
        );
    let source = format!(
        "{source}\n#fn read-view ((view (#ref View))) #u64
        (#return (#deref (#get view value)))\n"
    );
    run(&source, "async-linear-exclusive-guard");
}

#[test]
fn linear_exclusive_reference_fields_are_read_directly_without_moving_the_handle() {
    let source = exclusive_reference_guard_source(&linear_reference_guard_source()).replace(
        "View (#linear) ((value (#ref #u64)))",
        "View (#linear) ((value (#ref-mut #u64)))",
    );
    run(&source, "async-direct-exclusive-field-guard");
}

#[test]
fn direct_pinned_exclusive_reference_fields_are_lent_for_scalar_reads() {
    let source = exclusive_reference_guard_source(&linear_reference_guard_source())
        .replace(
            "View (#linear) ((value (#ref #u64)))",
            "View (#linear) ((value (#ref-mut #u64)))",
        )
        .replace("(#ref-mut #u64)", "(#pin-ref-mut #u64)")
        .replace("(#borrow-mut owner)", "(#pin-borrow-mut owner)");
    run(&source, "async-direct-pinned-exclusive-field");
}

#[test]
fn direct_exclusive_field_reads_do_not_release_the_callers_unique_loan() {
    let source = exclusive_reference_guard_source(&linear_reference_guard_source())
        .replace(
            "View (#linear) ((value (#ref #u64)))",
            "View (#linear) ((value (#ref-mut #u64)))",
        )
        .replace("(#let second Work::Poll", "(#let conflicting (#ref #u64) (#borrow owner))\n  (#forget conflicting)\n  (#let second Work::Poll");
    let scratch = support::Scratch::new("async-direct-field-caller-conflict");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("Pending must retain the caller's unique borrow");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#borrow");
    assert_eq!(span.start, source.find("#borrow owner").unwrap());
    assert!(!scratch.path().join("cache").exists());
}

#[test]
fn direct_exclusive_field_reads_keep_nested_struct_and_tuple_projections() {
    let source = exclusive_reference_guard_source(&linear_reference_guard_source())
        .replace(
            "View (#linear) ((value (#ref #u64)))",
            "View (#linear) ((value (#ref-mut #u64)))",
        )
        .replace("(#ref-mut #u64)", "(#ref-mut Point)")
        .replace(
            "(#let-mut owner #u64 42u64)",
            "(#let-mut owner Point (#struct-literal Point ((amount 42u64) (other 0u64))))",
        )
        .replace(
            "(#deref (#get (#borrow view) value))",
            "(#get (#get (#borrow view) value) amount)",
        );
    let source = format!("#struct Point () ((amount #u64) (other #u64))\n{source}");
    run(&source, "async-direct-nested-exclusive-field");
    let tuple = source
        .replace(
            "#struct Point () ((amount #u64) (other #u64))",
            "#type Point (#tuple #u64 #u64)",
        )
        .replace(
            "(#struct-literal Point ((amount 42u64) (other 0u64)))",
            "(#tuple (#tuple #u64 #u64) 42u64 0u64)",
        )
        .replace(
            "(#get (#get (#borrow view) value) amount)",
            "(#get (#get (#borrow view) value) 0)",
        );
    run(&tuple, "async-direct-tuple-exclusive-field");
}

#[test]
fn repeated_direct_field_reads_lend_a_unique_parent_before_and_after_pending() {
    let source = format!(
        "{CONTEXT}
#struct View (#linear) ((field (#ref-mut #u64)))
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
          (function (#fn work ((view (#ref-mut View))) #u64
            (#let first #u64 (#deref (#get view field)))
            (#let extra #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)))
            (#let second #u64 (#deref (#get view field)))
            (#return (#u64::add-wrap (#u64::add-wrap first second) extra)))))
#fn main () #u64
          (#let waker #u64 0u64) (#let-mut owner #u64 21u64)
          (#let-mut view View (#struct-literal View ((field (#borrow-mut owner)))))
          (#let-mut frame Work::Frame (#call work ((view (#borrow-mut view)))))
          (#let-else (Work::Poll.Pending next) Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))) (#unreachable))
          (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget frame) (#forget view) (#set owner 42u64) (#return answer)\n"
    );
    run(&source, "async-direct-unique-parent");
}

fn linear_reference_guard_source() -> String {
    aggregate_reference_guard_source()
        .replace(
            "#struct View () ((value (#ref #u64)))",
            "#struct View (#linear) ((value (#ref #u64)))\n ",
        )
        .replace(
            "\n          (#deref (#get view value)))",
            "\n        (#block (#let answer #u64 (#deref (#get view value)))\n\
             (#forget view) answer))",
        )
        .replace(
            "(#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start (#deref (#get view value))))",
            "(#block (#let amount #u64 (#deref (#get view value)))
  (#forget view)
  (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start amount)))",
        )
        .replace("(#get view value)", "(#get (#borrow view) value)")
}

#[test]
fn linear_reference_guard_acceptance_consumes_only_the_selected_payload() {
    let source = linear_reference_guard_source();
    let main = source.find("#fn main").unwrap();
    let source = format!(
        "{}\n#fn main () #u64
        (#let waker #u64 0u64) (#let owner #u64 0u64)
        (#let-mut frame Work::Frame (#call work ((source (#borrow owner)))))
        (#let-else (Work::Poll.Pending next) Work::Poll
          (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker))))
          (#unreachable))
        (#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
          (#case (Work::Poll.Ready value) value)
          (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
        (#forget frame) (#return answer)\n",
        &source[..main]
    );
    run_expected(&source, "async-linear-guard-accept", 0);
}

#[test]
fn linear_guard_whole_payload_borrow_survives_suspension_before_preview_read() {
    let source = linear_reference_guard_source().replace(
        "(#when (#u64::eq\n          (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64))\n          (#deref (#get (#borrow view) value))))",
        "(#when (#block
          (#let guard-view (#ref View) (#borrow view))
          (#let decision #bool (#u64::eq
            (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64))
            (#deref (#get guard-view value))))
          (#forget guard-view) decision))",
    );
    assert!(source.contains("(#let guard-view"));
    run(&source, "async-linear-whole-preview-borrow");
}

#[test]
fn movable_linear_guard_borrows_the_retained_payload_only_during_poll() {
    for source in [
        linear_reference_guard_source(),
        linear_reference_guard_source().replace("(#get (#borrow view) value)", "(#get view value)"),
    ] {
        let declarations = source[..source.find("#fn main").unwrap()]
            .replace("#generate #async-fn-pinned", "#generate #async-fn");
        let source = format!(
            "{declarations}
#fn main () #u64
          (#let waker #u64 0u64) (#let owner #u64 42u64)
          (#let-else (Work::Poll.Pending next) Work::Poll
            (#call Work::poll ((task (#call work ((source (#borrow owner)))))
              (waker (#borrow waker)))) (#unreachable))
          (#let-else (Work::Poll.Pending last) Work::Poll
            (#call Work::poll ((task next) (waker (#borrow waker)))) (#unreachable))
          (#return (#match (#call Work::poll ((task last) (waker (#borrow waker))))
            (#case (Work::Poll.Ready answer) answer)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))\n"
        );
        run(&source, "async-movable-linear-guard");
    }
}

#[test]
fn suspended_linear_reference_guard_keeps_the_callers_referent_borrowed() {
    let source = linear_reference_guard_source()
        .replace("(#let owner #u64", "(#let-mut owner #u64")
        .replace(
            "(#let second Work::Poll",
            "(#set owner 99u64)\n  (#let second Work::Poll",
        );
    let scratch = support::Scratch::new("async-linear-guard-conflict");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("the retained linear preview cannot release its external loan");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#set");
    assert_eq!(span.start, source.find("#set owner").unwrap());
    assert!(!scratch.path().join("cache").exists());
}

#[test]
fn linear_reference_guard_cancellation_reads_and_releases_the_retained_owner() {
    let source = linear_reference_guard_source();
    let declarations = format!(
        "{}\n
#fn cancel-holder ((holder Holder)) ()
          (#match holder (#case (Holder.Holding held)
            (#block (#assert (#u64::eq (#deref (#get (#borrow held) value)) 42u64))
              (#forget held) ())))
          (#return ())\n",
        &source[..source.find("#fn main").unwrap()]
    )
    .replace(
        "(function (#fn work",
        "(cancel (work-cancel ((source-expression-17 cancel-holder)
               (await-0 cancel-child) (await-1 cancel-child))))\n(function (#fn work",
    );
    run_guard_cancellation_matrix(&declarations, "async-linear-guard-cancel");
}

#[test]
fn copy_reference_tuple_guard_retains_nested_referents_across_rejection() {
    let source = aggregate_reference_guard_source()
        .replace(
            "#struct View () ((value (#ref #u64)))",
            "#type View (#tuple #u64 (#ref #u64))",
        )
        .replace(
            "(#struct-literal View ((value source)))",
            "(#tuple 0u64 source)",
        )
        .replace("(#get view value)", "(#get view 1)");
    run(&source, "async-graph-tuple-reference-guard");
}

#[test]
fn alternative_reference_guards_do_not_preview_payloads() {
    let source = shared_reference_guard_source()
        .replace(
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)))",
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)) (Holder.Other (#ref #u64)))",
        )
        .replace(
            "(#case (Holder.Holding view)",
            "(#case (#or (Holder.Holding _) (Holder.Other _))",
        )
        .replace("(#deref view)", "(#deref source)");
    for source in [
        source.clone(),
        source.replace("(Holder.Holding source)", "(Holder.Other source)"),
    ] {
        run(&source, "async-graph-alternative-reference-guard");
    }
}

#[test]
fn alternative_reference_guards_reject_payload_bindings_before_publication() {
    let source = shared_reference_guard_source()
        .replace(
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)))",
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)) (Holder.Other (#ref #u64)))",
        )
        .replace(
            "(#case (Holder.Holding view)",
            "(#case (#or (Holder.Holding view) (Holder.Other view))",
        );
    for source in [
        source.clone(),
        source.replace("(Holder.Holding source)", "(Holder.Other source)"),
    ] {
        let scratch = support::Scratch::new("async-graph-bound-alternative-reference-guard");
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("input.lim"),
            &config(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .expect_err("or-pattern payload bindings are forbidden in the source language");
        assert!(error
            .message
            .contains("or-pattern alternatives cannot bind values"));
        assert!(error.span.is_some(), "{error:?}");
        assert!(!scratch.path().join("cache").exists());
    }
}

#[test]
fn suspended_aggregate_guard_keeps_the_callers_loan_alive() {
    let source = aggregate_reference_guard_source()
        .replace("(#let owner #u64", "(#let-mut owner #u64")
        .replace(
            "(#let second Work::Poll",
            "(#set owner 99u64)\n  (#let second Work::Poll",
        );
    let scratch = support::Scratch::new("async-graph-aggregate-guard-conflict");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#set");
    assert_eq!(span.start, source.find("#set owner").unwrap());
    assert!(!scratch.path().join("cache").exists());
}

fn guard_cancellation_declarations() -> String {
    let source = shared_reference_guard_source();
    let declarations = source[..source.find("#fn main").unwrap()]
        .replace(
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)))",
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)))
#fn cancel-holder ((holder Holder)) () (#forget holder) (#return ())",
        )
        .replace(
            "(function (#fn work",
            "(cancel (work-cancel ((source-expression-11 cancel-holder)
               (await-0 cancel-child) (await-1 cancel-child))))
             (function (#fn work",
        );
    assert!(declarations.contains("#fn cancel-holder"));
    declarations
}

fn cancelled_guard_source(declarations: &str, polls: &str, handle: &str) -> String {
    format!(
        "{declarations}
#fn main () #u64 (#let waker #u64 0u64) (#let-mut owner #u64 42u64)
          (#let-mut frame Work::Frame (#call work ((source (#borrow owner)))))
          {polls}
          (#call work-cancel ((task (#call Work::Poll::cleanup ((task {handle}))))))
          (#call work-cancel ((task (#call Work::Poll::cleanup ((task (#pin-borrow-mut frame)))))))
          (#forget frame) (#set owner 42u64) (#return owner)\n"
    )
}

#[test]
fn reference_guard_cancellation_releases_entry_preview_and_committed_loans() {
    run_guard_cancellation_matrix(
        &guard_cancellation_declarations(),
        "async-graph-reference-guard-cancel",
    );
}

fn run_guard_cancellation_matrix(declarations: &str, label: &str) {
    run_guard_cancellation_matrix_with_borrow(declarations, label, "#borrow");
}

fn run_guard_cancellation_matrix_with_borrow(declarations: &str, label: &str, borrow: &str) {
    let poll_first = "(#let first Work::Poll
      (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
      (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))";
    let poll_second = "(#let second Work::Poll
      (#call Work::poll ((task next) (waker (#borrow waker)))))
      (#let-else (Work::Poll.Pending last) Work::Poll second (#unreachable))";
    for (polls, handle) in [
        (String::new(), "(#pin-borrow-mut frame)"),
        (poll_first.into(), "next"),
        (format!("{poll_first}\n{poll_second}"), "last"),
    ] {
        let source = cancelled_guard_source(declarations, &polls, handle)
            .replace("(#borrow owner)", &format!("({borrow} owner)"));
        run(&source, label);
    }
}

#[test]
fn reading_guard_cleanup_resolves_conditional_call_input_provenance() {
    let declarations = guard_cancellation_declarations().replace(
        "#fn cancel-holder ((holder Holder)) () (#forget holder) (#return ())",
        "#fn cancel-holder ((holder Holder)) ()
            (#match holder (#case (Holder.Holding held)
              (#block (#assert (#u64::eq (#deref held) 42u64)) (#drop held) ())))
            (#return ())",
    );
    run_guard_cancellation_matrix(&declarations, "async-graph-reading-guard-cleanup");
}

#[test]
fn reading_aggregate_guard_cleanup_preserves_and_releases_nested_loans() {
    let declarations = guard_cancellation_declarations()
        .replace(
            "#enum Holder (#linear) ((Holder.Holding (#ref #u64)))",
            "#struct View () ((value (#ref #u64)))\n#enum Holder (#linear) ((Holder.Holding View))",
        )
        .replace(
            "(Holder.Holding source)",
            "(Holder.Holding (#struct-literal View ((value source))))",
        )
        .replace("(#deref view)", "(#deref (#get view value))")
        .replace("source-expression-11", "source-expression-17")
        .replace(
            "#fn cancel-holder ((holder Holder)) () (#forget holder) (#return ())",
            "#fn cancel-holder ((holder Holder)) ()
                (#match holder (#case (Holder.Holding held)
                  (#assert (#u64::eq (#deref (#get held value)) 42u64))))
                (#return ())",
        );
    run_guard_cancellation_matrix(&declarations, "async-graph-reading-aggregate-guard-cleanup");
}

#[test]
fn suspended_reference_guard_does_not_allow_mutating_the_callers_referent() {
    let source = shared_reference_guard_source()
        .replace("(#let owner #u64", "(#let-mut owner #u64")
        .replace(
            "(#let second Work::Poll",
            "(#set owner 99u64)\n  (#let second Work::Poll",
        );
    let scratch = support::Scratch::new("async-graph-reference-guard-conflict");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("a retained reference guard must keep the caller's loan alive");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.expect("caller conflict has an exact span");
    assert_eq!(&source[span.start..span.end], "#set", "{error:?}");
    assert_eq!(span.start, source.find("#set owner").unwrap(), "{error:?}");
    assert!(!scratch.path().join("cache").exists());
}

#[test]
fn exclusive_reference_guard_reborrows_without_duplicating_the_owner() {
    run(
        &exclusive_reference_guard_source(&shared_reference_guard_source()),
        "async-graph-exclusive-guard",
    );
}

#[test]
fn pinned_exclusive_reference_guard_reborrows_without_losing_pinning() {
    let source = exclusive_reference_guard_source(&shared_reference_guard_source())
        .replace("(#ref-mut #u64)", "(#pin-ref-mut #u64)")
        .replace("(#borrow-mut owner)", "(#pin-borrow-mut owner)");
    run(&source, "async-graph-pinned-exclusive-guard");
}

fn exclusive_reference_guard_source(source: &str) -> String {
    source
        .replace(
            "Holder (#linear) ((Holder.Holding (#ref #u64)))",
            "Holder (#linear) ((Holder.Holding (#ref-mut #u64)))",
        )
        .replace(
            "work ((source (#ref #u64)))",
            "work ((source (#ref-mut #u64)))",
        )
        .replace("(#let owner #u64", "(#let-mut owner #u64")
        .replace(
            "((source (#borrow owner)))",
            "((source (#borrow-mut owner)))",
        )
}

#[test]
fn exclusive_guard_commit_releases_the_preview_before_mutating_the_payload() {
    let source = exclusive_reference_guard_source(&shared_reference_guard_source());
    let declarations = source[..source.find("#fn main").unwrap()]
        .replace("(Child.Start 0u64)", "(Child.Start 42u64)")
        .replace(
            "(#deref view))\n        (#case",
            "(#block (#deref-set view 43u64) (#deref view)))\n      (#case",
        );
    assert!(
        declarations.contains("(#deref-set view 43u64)"),
        "the commit mutation must be present in the transformed fixture"
    );
    let source = format!(
        "{declarations}
#fn main () #u64 (#let waker #u64 0u64) (#let-mut owner #u64 42u64)
          (#let-mut frame Work::Frame (#call work ((source (#borrow-mut owner)))))
          (#let first Work::Poll
            (#call Work::poll ((task (#pin-borrow-mut frame)) (waker (#borrow waker)))))
          (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
          (#let answer #u64 (#match
            (#call Work::poll ((task next) (waker (#borrow waker))))
            (#case (Work::Poll.Ready result) result)
            (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
          (#forget frame) (#assert (#u64::eq owner 43u64)) (#return answer)\n"
    );
    run_expected(&source, "async-graph-exclusive-guard-commit", 43);
}

#[test]
fn nested_guard_previews_lend_only_exclusive_fields_regardless_of_order() {
    for swapped in [false, true] {
        let source = exclusive_reference_guard_source(&shared_reference_guard_source());
        let (fields, pattern) = if swapped {
            (
                "((exclusive (#ref-mut #u64)) (shared (#ref #u64)))",
                "(View view shared)",
            )
        } else {
            (
                "((shared (#ref #u64)) (exclusive (#ref-mut #u64)))",
                "(View shared view)",
            )
        };
        let source = source
            .replace(
                "(#enum Holder (#linear) ((Holder.Holding (#ref-mut #u64))))",
                &format!(
                    "#struct View () {fields}\n#enum Holder (#linear) ((Holder.Holding View))"
                ),
            )
            .replace(
                "work ((source (#ref-mut #u64)))",
                "work ((source (#ref-mut #u64)) (other (#ref #u64)))",
            )
            .replace(
                "(Holder.Holding source)",
                "(Holder.Holding (#struct-literal View ((shared other) (exclusive source))))",
            )
            .replace(
                "(Holder.Holding view)",
                &format!("(Holder.Holding {pattern})"),
            )
            .replace(
                "(#deref view)",
                "(#u64::add-wrap (#deref shared) (#deref view))",
            )
            .replace(
                "((source (#borrow-mut owner)))",
                "((source (#borrow-mut owner)) (other (#borrow waker)))",
            );
        run(&source, "async-graph-mixed-guard");
    }
}

#[test]
fn suspended_exclusive_guard_rejects_shared_and_exclusive_caller_aliases() {
    for borrow in ["#borrow", "#borrow-mut"] {
        let source = exclusive_reference_guard_source(&shared_reference_guard_source()).replace(
            "(#let second Work::Poll",
            &format!(
                "(#let alias ({} #u64) ({borrow} owner))\n  (#drop alias)\n  (#let second Work::Poll",
                if borrow == "#borrow" {
                    "#ref"
                } else {
                    "#ref-mut"
                }
            ),
        );
        let scratch = support::Scratch::new("async-graph-exclusive-guard-conflict");
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("input.lim"),
            &config(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .expect_err("the suspended exclusive guard must retain its caller's loan");
        assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
        let span = error.span.expect("caller alias conflict has an exact span");
        assert_eq!(&source[span.start..span.end], borrow, "{error:?}");
        assert!(!scratch.path().join("cache").exists());
    }
}

#[test]
fn reading_exclusive_guard_cleanup_releases_preview_before_consuming_holder() {
    let declarations = exclusive_reference_guard_source(&guard_cancellation_declarations())
        .replace(
            "#fn cancel-holder ((holder Holder)) () (#forget holder) (#return ())",
            "#fn cancel-holder ((holder Holder)) ()
            (#match holder (#case (Holder.Holding held)
              (#block (#assert (#u64::eq (#deref held) 42u64)) (#drop held) ())))
            (#return ())",
        );
    run_guard_cancellation_matrix_with_borrow(
        &declarations,
        "async-graph-exclusive-guard-cancel",
        "#borrow-mut",
    );
}

#[test]
fn graph_route_rejects_missing_wrong_and_private_cleanup_contracts() {
    for (handlers, expected) in [
        (
            "()",
            "missing graph cleanup handler for source slot 'await-0'",
        ),
        (
            "((work-frame-await-0 cancel-child))",
            "missing graph cleanup handler for source slot 'await-0'",
        ),
        (
            "((await-0 wrong))",
            "must safely consume one Child and return ()",
        ),
        (
            "((await-0 cancel-child) (unused cancel-child))",
            "unknown graph cleanup source slot 'unused'",
        ),
    ] {
        let source = format!("{CONTEXT}
#fn wrong ((value #u64)) () (#return ())
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64) (cancel (work-cancel {handlers}))
              (function (#fn work ((seed #u64)) #u64 (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed))))))
");
        let error = lim::parse_program_with_config(&source, &config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
    }
}

#[test]
fn scoped_local_borrows_use_inspectable_pointer_storage() {
    let source = format!("{CONTEXT}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
        (function (#fn work ((seed #u64)) #u64 (#let owner #u64 seed)
          (#return (#borrow owner (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64)))))))
");
    let scratch = support::Scratch::new("async-graph-fail-closed");
    let cache = scratch.path().join("cache");
    lim::parse_program_from_path_with_config_and_cache(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &cache,
    )
    .unwrap();
    let artifacts = fs::read_dir(scratch.path().join("generated"))
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .collect::<Vec<_>>();
    let source = &artifacts[0];
    assert!(source.contains("(#ptr #u64)"));
    assert!(source.contains("#ref-ptr"));
    assert!(scratch.path().join("generated").exists());
}

#[test]
fn invalid_scoped_borrows_fail_before_cache_publication() {
    let source = format!(
        "{CONTEXT}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
        (function (#fn work ((seed #u64)) #u64 (#let-mut owner #u64 seed)
          (#return (#borrow owner (#block (#set owner 1u64)
            (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64))))))))
"
    );
    let scratch = support::Scratch::new("async-graph-invalid-scope");
    let error = lim::parse_program_from_path_with_config_and_cache(
        &source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
    )
    .err()
    .expect("mutation inside a shared borrow must fail");
    assert!(error.contains("borrow"), "{error}");
    assert!(!scratch.path().join("generated").exists());
}

#[test]
fn delayed_owner_initialization_and_configured_destruction_are_exactly_once() {
    let declarations = "#struct Counter (#linear) ((storage (#atomic #u64)))
#fn read-counter ((count (#ref Counter))) #u64
          (#return (#atomic-load (#borrow (#get count storage)) #memory-relaxed))
#fn bump-counter ((count (#ref Counter))) ()
          (#atomic-store (#borrow (#get count storage))
            (#u64::add-wrap (#call read-counter ((count count))) 1u64) #memory-relaxed)
          (#return ())
#struct Source (#linear) ((amount #u64) (destroyed (#ref Counter)))
#fn make-owner ((created (#ref Counter)) (destroyed (#ref Counter))) Source
          (#call bump-counter ((count created)))
          (#return (#struct-literal Source ((amount 40u64) (destroyed destroyed))))
#fn destroy-owner ((owner Source)) ()
          (#assert (#u64::eq (#get owner amount) 40u64))
          (#call bump-counter ((count (#get owner destroyed))))
          (#forget owner) (#return ())\n";
    let first = "(#let first Work::Poll (#call Work::poll ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
      (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))";
    let second = "(#let second Work::Poll (#call Work::poll ((task next) (waker (#borrow waker)))))
      (#let-else (Work::Poll.Pending last) Work::Poll second (#unreachable))";
    let ready = "(#let answer #u64 (#match (#call Work::poll ((task last) (waker (#borrow waker))))
      (#case (Work::Poll.Ready value) value) (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
      (#assert (#u64::eq answer 42u64))";
    for (polls, handle, created, destroyed) in [
        (String::new(), "(#pin-borrow-mut task)", 0, 0),
        (first.into(), "next", 0, 0),
        (format!("{first}\n{second}"), "last", 1, 0),
        (
            format!("{first}\n{second}\n{ready}"),
            "(#pin-borrow-mut task)",
            1,
            1,
        ),
    ] {
        let source = format!("{CONTEXT}\n{declarations}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
              (cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child) (await-1 cancel-child))))
              (function (#fn work ((created (#ref Counter)) (destroyed (#ref Counter))) #u64
                (#let ignored #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 5u64)))
                (#let owner Source (#call make-owner ((created created) (destroyed destroyed))))
                (#let view (#pin-ref #u64) (#pin-borrow (#get owner amount)))
                (#let amount #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 2u64)))
                (#let answer #u64 (#u64::add-wrap (#deref view) amount)) (#drop view)
                (#call destroy-owner ((owner owner))) (#return answer))))
#fn main () #u64 (#let waker #u64 0u64)
              (#let created Counter (#struct-literal Counter ((storage (#atomic-init #u64 0u64)))))
              (#let destroyed Counter (#struct-literal Counter ((storage (#atomic-init #u64 0u64)))))
              (#let-mut task Work::Frame (#call work ((created (#borrow created)) (destroyed (#borrow destroyed)))))
              (#assert (#u64::eq (#call read-counter ((count (#borrow created)))) 0u64)) {polls}
              (#assert (#u64::eq (#call read-counter ((count (#borrow created)))) {created}u64))
              (#assert (#u64::eq (#call read-counter ((count (#borrow destroyed)))) {destroyed}u64))
              (#call work-cancel ((task (#call Work::Poll::cleanup ((task {handle}))))))
              (#assert (#u64::eq (#call read-counter ((count (#borrow destroyed)))) {created}u64))
              (#call work-cancel ((task (#call Work::Poll::cleanup ((task (#pin-borrow-mut task)))))))
              (#assert (#u64::eq (#call read-counter ((count (#borrow destroyed)))) {created}u64))
              (#forget task) (#forget created) (#forget destroyed) (#return 42u64)\n");
        run(&source, "async-graph-delayed-cleanup");
    }
}

#[test]
fn scoped_external_tokens_survive_pending_and_release_on_exit_or_cleanup() {
    for (ty, borrow) in [
        ("(#ref (#tuple #u64 #u64))", "#borrow"),
        ("(#ref-mut (#tuple #u64 #u64))", "#borrow-mut"),
        ("(#pin-ref (#tuple #u64 #u64))", "#pin-borrow"),
        ("(#pin-ref-mut (#tuple #u64 #u64))", "#pin-borrow-mut"),
    ] {
        // Explicit pin-borrow's scoped spelling is not part of the language;
        // ordinary scoped borrow inherits the receiver's checked pinning.
        let scoped = if borrow.ends_with("mut") {
            "#borrow-mut"
        } else {
            "#borrow"
        };
        for cancel in [false, true] {
            let finish = if cancel {
                "(#call work-cancel ((task (#call Work::Poll::cleanup ((task next))))))"
            } else {
                "(#let answer #u64 (#match (#call Work::poll ((task next) (waker (#borrow waker))))
                  (#case (Work::Poll.Ready value) value)
                  (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable)))))
                 (#assert (#u64::eq answer 42u64))"
            };
            let source = format!("{CONTEXT}
#generate #async-fn-pinned ((protocol WorkAwait) (waker #u64)
                  (cancel (work-cancel ((await-0 cancel-child))))
                  (function (#fn work ((owner {ty})) #u64
                    (#let answer #u64 ({scoped} (#get owner 0)
                      (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 42u64))))
                    (#return answer))))
#fn main () #u64 (#let waker #u64 0u64)
                  (#let-mut owner (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) 1u64 2u64))
                  (#let-mut task Work::Frame (#call work ((owner ({borrow} owner)))))
                  (#let first Work::Poll (#call Work::poll ((task (#pin-borrow-mut task)) (waker (#borrow waker)))))
                  (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
                  {finish} (#forget task)
                  (#set owner (#tuple (#tuple #u64 #u64) 40u64 2u64))
                  (#return (#u64::add-wrap (#get owner 0) (#get owner 1)))\n");
            run(&source, "async-graph-scoped-external");
            let misuse = source.replace(
                finish,
                "(#set owner (#tuple (#tuple #u64 #u64) 40u64 2u64))",
            );
            assert!(lim::parse_program_with_config(&misuse, &config()).is_err());
        }
    }
}
