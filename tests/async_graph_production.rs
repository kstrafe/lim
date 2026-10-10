mod support;

use std::{fs, process::Command, time::Duration};

const CONTEXT: &str = "
  (#enum Child ((Start #u64) (Resume #u64))) (#linear Child)
  (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
  (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
    (#return (#match task
      (#case (Start value) (ChildPending (Resume value)))
      (#case (Resume value) (ChildReady value)))))
  (#fn cancel-child (: child Child) () (#forget child) (#return ()))";

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
        .find(|text| text.contains("(#fn work-poll "))
        .unwrap();
    assert!(artifact.starts_with("; Generated from:"));
    assert!(artifact.contains("(#syntax WorkAwait"));
    assert!(!artifact.contains("#await") && !artifact.contains("@#async-fn"));
    let invocation = lim::parse(source)
        .unwrap()
        .into_iter()
        .find(|node| source[node.span.start..node.span.end].starts_with("(@#async-fn"))
        .unwrap();
    let standalone = format!(
        "{}\n{artifact}\n{}",
        &source[..invocation.span.start],
        &source[invocation.span.end..]
    );
    let ordinary =
        lim::parse_program(&standalone).unwrap_or_else(|error| panic!("{error}\n{standalone}"));
    lim::check_types(&ordinary).unwrap_or_else(|error| panic!("{error}\n{standalone}"));
    (scratch, artifact, standalone)
}

fn run(source: &str, label: &str) -> String {
    let (scratch, artifact, standalone) = checked_artifact(source, label);
    let ordinary = lim::parse_program(&standalone).unwrap();
    let assembly = lim::generate_assembly(&ordinary).unwrap();
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
    artifact
}

#[test]
fn source_named_cleanup_runs_at_entry_pending_ready_and_repeated_cancel() {
    let first = "(#let first work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
      (#let-else (work-pending next) work-poll-result first (#unreachable))";
    let second = "(#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
      (#case (work-ready value) value) (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
      (#assert (#u64.== answer 42u64))";
    for (polls, handle) in [
        (String::new(), "(#pin-borrow-mut task)"),
        (first.into(), "next"),
        (format!("{first}\n{second}"), "(#pin-borrow-mut task)"),
    ] {
        let source = format!(
            "{CONTEXT}
          (@#async-fn-pinned (: protocol WorkAwait : waker #u64
            : cancel (work-cancel ((await-0 cancel-child)))
            : function (#fn work (: seed #u64) #u64
              (#return (#await Child ChildPending ChildReady child-poll (Start seed))))))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let-mut task work-frame (#call work (: seed 42u64))) {polls}
            (#call work-cancel (: task (#call work-poll-cleanup (: task {handle}))))
            (#call work-cancel (: task (#call work-poll-cleanup (: task (#pin-borrow-mut task)))))
            (#forget task) (#return 42u64))"
        );
        let artifact = run(&source, "async-graph-cancel");
        assert!(artifact
            .contains("(#struct work-frame-cleanup ((await-0 work-frame-cleanup-await-0)))"));
    }
}

#[test]
fn movable_cleanup_consumes_the_frame_at_entry_and_pending() {
    for (polls, task) in [
        ("", "task"),
        (
            "(#let first work-poll-result (#call work-poll (: task task : waker (#borrow waker))))
          (#let-else (work-pending next) work-poll-result first (#unreachable))",
            "next",
        ),
    ] {
        let source = format!(
            "{CONTEXT}
          (@#async-fn (: protocol WorkAwait : waker #u64
            : cancel (work-cancel ((await-0 cancel-child)))
            : function (#fn work (: seed #u64) #u64
              (#return (#await Child ChildPending ChildReady child-poll (Start seed))))))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let task work-task (#call work (: seed 42u64))) {polls}
            (#call work-cancel (: task (#call work-poll-cleanup (: task {task}))))
            (#return 42u64))"
        );
        run(&source, "async-graph-movable-cleanup");
        let invalid = source.replace("(#return 42u64))", "(#forget task) (#return 42u64))");
        assert!(lim::parse_program_with_config(&invalid, &config()).is_err());
    }
}

#[test]
fn guard_preview_keeps_linear_scrutinee_through_rejection_and_resumption() {
    let source = format!("{CONTEXT}
      (@#async-fn (: protocol WorkAwait : waker #u64
        : function (#fn work (: seed #u64) #u64
          (#let child Child (Start seed))
          (#return (#match child
            (#case (Start amount)
              (#when (#u64.== (#await Child ChildPending ChildReady child-poll (Start 0u64)) 1u64))
              (#await Child ChildPending ChildReady child-poll (Start 99u64)))
            (#case (Start amount) (#await Child ChildPending ChildReady child-poll (Start amount)))
            (#case (Resume amount) amount))))))
      (#fn main () #u64 (#let waker #u64 0u64)
        (#let first work-poll-result (#call work-poll (: task (#call work (: seed 42u64)) : waker (#borrow waker))))
        (#let-else (work-pending next) work-poll-result first (#unreachable))
        (#let second work-poll-result (#call work-poll (: task next : waker (#borrow waker))))
        (#let-else (work-pending last) work-poll-result second (#unreachable))
        (#return (#match (#call work-poll (: task last : waker (#borrow waker)))
          (#case (work-ready answer) answer)
          (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))");
    run(&source, "async-graph-guard");
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
        let source = format!("{CONTEXT} (#fn wrong (: value #u64) () (#return ()))
          (@#async-fn-pinned (: protocol WorkAwait : waker #u64 : cancel (work-cancel {handlers})
            : function (#fn work (: seed #u64) #u64 (#return (#await Child ChildPending ChildReady child-poll (Start seed))))))");
        let error = lim::parse_program_with_config(&source, &config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
    }
}

#[test]
fn scoped_local_borrows_use_inspectable_pointer_storage() {
    let source = format!("{CONTEXT} (@#async-fn-pinned (: protocol WorkAwait : waker #u64
      : function (#fn work (: seed #u64) #u64 (#let owner #u64 seed)
        (#return (#borrow owner (#await Child ChildPending ChildReady child-poll (Start 0u64)))))))");
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
        "{CONTEXT} (@#async-fn-pinned (: protocol WorkAwait : waker #u64
      : function (#fn work (: seed #u64) #u64 (#let-mut owner #u64 seed)
        (#return (#borrow owner (#block (#set owner 1u64)
          (#await Child ChildPending ChildReady child-poll (Start 0u64))))))))"
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
    let declarations = "(#struct Counter (: storage (#atomic #u64))) (#linear Counter)
      (#fn read-counter (: count (#ref Counter)) #u64
        (#return (#atomic-load (#borrow (#get count storage)) #memory-relaxed)))
      (#fn bump-counter (: count (#ref Counter)) ()
        (#atomic-store (#borrow (#get count storage))
          (#u64.+.wrap (#call read-counter (: count count)) 1u64) #memory-relaxed)
        (#return ()))
      (#struct Source (: amount #u64 : destroyed (#ref Counter))) (#linear Source)
      (#fn make-owner (: created (#ref Counter) : destroyed (#ref Counter)) Source
        (#call bump-counter (: count created))
        (#return (#struct-literal Source (: amount 40u64 : destroyed destroyed))))
      (#fn destroy-owner (: owner Source) ()
        (#assert (#u64.== (#get owner amount) 40u64))
        (#call bump-counter (: count (#get owner destroyed)))
        (#forget owner) (#return ()))";
    let first = "(#let first work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
      (#let-else (work-pending next) work-poll-result first (#unreachable))";
    let second =
        "(#let second work-poll-result (#call work-poll (: task next : waker (#borrow waker))))
      (#let-else (work-pending last) work-poll-result second (#unreachable))";
    let ready = "(#let answer #u64 (#match (#call work-poll (: task last : waker (#borrow waker)))
      (#case (work-ready value) value) (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
      (#assert (#u64.== answer 42u64))";
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
          (@#async-fn-pinned (: protocol WorkAwait : waker #u64
            : cancel (work-cancel ((owner destroy-owner) (await-0 cancel-child) (await-1 cancel-child)))
            : function (#fn work (: created (#ref Counter) : destroyed (#ref Counter)) #u64
              (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Start 5u64)))
              (#let owner Source (#call make-owner (: created created : destroyed destroyed)))
              (#let view (#pin-ref #u64) (#pin-borrow (#get owner amount)))
              (#let amount #u64 (#await Child ChildPending ChildReady child-poll (Start 2u64)))
              (#let answer #u64 (#u64.+.wrap (#deref view) amount)) (#drop view)
              (#call destroy-owner (: owner owner)) (#return answer))))
          (#fn main () #u64 (#let waker #u64 0u64)
            (#let created Counter (#struct-literal Counter (: storage (#atomic-init #u64 0u64))))
            (#let destroyed Counter (#struct-literal Counter (: storage (#atomic-init #u64 0u64))))
            (#let-mut task work-frame (#call work (: created (#borrow created) : destroyed (#borrow destroyed))))
            (#assert (#u64.== (#call read-counter (: count (#borrow created))) 0u64)) {polls}
            (#assert (#u64.== (#call read-counter (: count (#borrow created))) {created}u64))
            (#assert (#u64.== (#call read-counter (: count (#borrow destroyed))) {destroyed}u64))
            (#call work-cancel (: task (#call work-poll-cleanup (: task {handle}))))
            (#assert (#u64.== (#call read-counter (: count (#borrow destroyed))) {created}u64))
            (#call work-cancel (: task (#call work-poll-cleanup (: task (#pin-borrow-mut task)))))
            (#assert (#u64.== (#call read-counter (: count (#borrow destroyed))) {created}u64))
            (#forget task) (#forget created) (#forget destroyed) (#return 42u64))");
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
                "(#call work-cancel (: task (#call work-poll-cleanup (: task next))))"
            } else {
                "(#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
                  (#case (work-ready value) value)
                  (#case (work-pending bad) (#block (#forget bad) (#unreachable)))))
                 (#assert (#u64.== answer 42u64))"
            };
            let source = format!("{CONTEXT}
              (@#async-fn-pinned (: protocol WorkAwait : waker #u64
                : cancel (work-cancel ((await-0 cancel-child)))
                : function (#fn work (: owner {ty}) #u64
                  (#let answer #u64 ({scoped} (#get owner 0)
                    (#await Child ChildPending ChildReady child-poll (Start 42u64))))
                  (#return answer))))
              (#fn main () #u64 (#let waker #u64 0u64)
                (#let-mut owner (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) 1u64 2u64))
                (#let-mut task work-frame (#call work (: owner ({borrow} owner))))
                (#let first work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
                (#let-else (work-pending next) work-poll-result first (#unreachable))
                {finish} (#forget task)
                (#set owner (#tuple (#tuple #u64 #u64) 40u64 2u64))
                (#return (#u64.+.wrap (#get owner 0) (#get owner 1))))");
            run(&source, "async-graph-scoped-external");
            let misuse = source.replace(
                finish,
                "(#set owner (#tuple (#tuple #u64 #u64) 40u64 2u64))",
            );
            assert!(lim::parse_program_with_config(&misuse, &config()).is_err());
        }
    }
}
