mod support;

use std::{fs, process::Command, time::Duration};

fn generated_standalone(
    source: &str,
    marker: &str,
    poll: &str,
    label: &str,
) -> (support::Scratch, String) {
    generated_standalone_with_config(source, marker, poll, label, &lim::CompileConfig::default())
}

fn generated_standalone_with_config(
    source: &str,
    marker: &str,
    poll: &str,
    label: &str,
    config: &lim::CompileConfig,
) -> (support::Scratch, String) {
    let scratch = support::Scratch::new(label);
    let source_path = scratch.path().join("input.lim");
    let generated_dir = scratch.path().join("generated");
    let cache_dir = scratch.path().join("cache");
    lim::write_generated_sources_from_path_with_config_and_cache(
        source,
        &source_path,
        &generated_dir,
        config,
        &cache_dir,
    )
    .unwrap();

    let artifact_dir = generated_dir.clone();
    let artifact = fs::read_dir(&artifact_dir)
        .unwrap_or_else(|error| panic!("read {}: {error}", artifact_dir.display()))
        .filter_map(Result::ok)
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .find(|artifact| artifact.contains(&format!("(#fn {poll} ")))
        .unwrap_or_else(|| panic!("no generated artifact contains poll function {poll}"))
        .replace("Lim.async.", "Ordinary.frame.")
        .replace(".graph.", ".ordinary.")
        .replace("lim.async.", "ordinary.frame.");
    assert!(!artifact.contains("@#async-fn"), "{artifact}");
    assert!(!artifact.contains("#await"), "{artifact}");
    assert!(!artifact.contains("lim.async."), "{artifact}");
    assert!(!artifact.contains("Lim.async."), "{artifact}");
    assert!(!artifact.contains("generator_validation"), "{artifact}");

    let form = lim::parse(source)
        .unwrap()
        .into_iter()
        .find(|form| {
            form.span.start < source.len()
                && source[form.span.start..form.span.end].starts_with(marker)
        })
        .unwrap_or_else(|| panic!("could not find generator form {marker}"));
    let standalone = format!(
        "{}\n{}\n{}",
        &source[..form.span.start],
        artifact,
        &source[form.span.end..]
    );
    assert!(!standalone.contains("@#async-fn"), "{standalone}");
    assert!(!standalone.contains("#await"), "{standalone}");
    assert!(!standalone.contains("lim.async."), "{standalone}");
    assert!(!standalone.contains("Lim.async."), "{standalone}");
    (scratch, standalone)
}

#[test]
fn graph_selected_internal_references_compile_as_independent_ordinary_code() {
    let source = "(#enum Child (#linear) ((Waiting #u64)))
      (#enum ChildPoll () ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
        (#return (#match task (#case (Waiting count)
          (#if (#u64.== count 0u64) (ChildPending (Waiting 1u64)) (ChildReady count))))))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work (: choose #bool) #u64
          (#let left #u64 41u64) (#let right #u64 51u64)
          (#let view (#ref #u64) (#if choose (#borrow left) (#borrow right)))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#let answer #u64 (#u64.+.wrap (#deref view) extra))
          (#drop view) (#return answer))))
      (#fn main () #u64
        (#let waker #u64 0u64) (#let-mut task Work-frame (#call work (: choose true)))
        (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending bad) (#block (#drop bad) (#unreachable)))))
        (#forget task) (#return answer))";
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let (scratch, standalone) = generated_standalone_with_config(
        source,
        "(@#async-fn-pinned",
        "work-poll",
        "async-generator-selected-graph",
        &config,
    );
    assert!(!standalone.contains(".graph."));
    assert!(standalone.contains("#ptr-address"));
    check_build_and_run(&scratch, &standalone, 42);

    // There is no runtime Empty tag for primitive bindings. Change the
    // unselected left buffer after Pending, then poll the right loan: address
    // selection must retain the original branch instead of rebuilding it.
    let declarations = lim::parse(&standalone).unwrap();
    let frame = declarations.iter().find_map(|node| {
        let lim::Expr::List(items) = &node.expr else { return None; };
        matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#struct")
            .then_some(items)
            .filter(|items| matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == "Work-frame"))
    }).unwrap();
    let lim::Expr::List(fields) = &frame[3] else {
        panic!("frame fields");
    };
    let left_buffer = fields
        .iter()
        .find_map(|field| {
            let lim::Expr::List(pair) = field else {
                return None;
            };
            match pair.as_slice() {
                [lim::Expr::Symbol(field), lim::Expr::List(ty)]
                    if field.ends_with(".binding.2-words") => {
                    assert!(matches!(ty.as_slice(), [lim::Expr::Symbol(array), lim::Expr::Symbol(element), lim::Expr::Integer(1)]
                        if array == "#array" && element == "#u64"));
                    Some(field)
                }
                _ => None,
            }
        })
        .unwrap_or_else(|| panic!("missing left buffer: {fields:?}"));
    let changed_left = standalone
        .replace("(: choose true)", "(: choose false)")
        .replace(
            "(#let answer #u64 (#match",
            &format!(
                "(#drop next)
          (#block
            (#let buffer-anchor (#pin-ref-mut (#array #u64 1))
              (#pin-borrow-mut (#get task {left_buffer})))
            (#let writable (#ref-mut (#array #u64 1))
              (#unsafe (#ptr-borrow-mut buffer-anchor (#ref-ptr buffer-anchor))))
            (#unsafe (#word-write #u64 (#borrow-slice-mut (#deref writable)) 99u64)))
          (#let answer #u64 (#match"
            ),
        )
        .replace(
            "(: task next : waker",
            "(: task (#pin-borrow-mut task) : waker",
        );
    check_build_and_run(&scratch, &changed_left, 52);
}

#[test]
fn graph_mixed_external_references_retain_lifetimes_in_independent_ordinary_code() {
    let source = "(#struct Outside () (: other #u64 : selected #u64))
      (#enum Child (#linear) ((Waiting #u64)))
      (#enum ChildPoll () ((ChildPending Child) (ChildReady #u64)))
      (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
        (#return (#match task (#case (Waiting count)
          (#if (#u64.== count 0u64) (ChildPending (Waiting 1u64)) (ChildReady count))))))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work (: external (#ref-mut #u64) : choose #bool) #u64
          (#let-mut owner #u64 40u64)
          (#let view (#ref-mut #u64) (#if choose (#borrow-mut owner) external))
          (#let extra #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#forget extra) (#deref-set view 42u64)
          (#let answer #u64 (#deref view)) (#drop view) (#return answer))))
      (#fn main () #u64
        (#let-mut external Outside (#struct-literal Outside (: other 90u64 : selected 50u64)))
        (#let waker #u64 0u64)
        (#let-mut task Work-frame (#call work (: external (#borrow-mut (#get external selected)) : choose false)))
        (#let first Work-poll-result (#call work-poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (work-pending next) Work-poll-result first (#unreachable))
        (#let answer #u64 (#match (#call work-poll (: task next : waker (#borrow waker)))
          (#case (work-ready value) value)
          (#case (work-pending bad) (#block (#drop bad) (#unreachable)))))
        (#forget task) (#assert (#u64.== (#get external other) 90u64))
        (#assert (#u64.== (#get external selected) 42u64)) (#return answer))";
    for mutable in [false, true] {
        let source = if mutable {
            source.to_owned()
        } else {
            source
                .replace("#ref-mut", "#ref")
                .replace("#borrow-mut", "#borrow")
                .replace("(#forget extra) (#deref-set view 42u64)", "(#forget extra)")
                .replace(
                    "(#get external selected) 42u64",
                    "(#get external selected) 50u64",
                )
        };
        let mut config = lim::CompileConfig::default();
        config.set("async-lowering", "graph");
        let (scratch, standalone) = generated_standalone_with_config(
            &source,
            "(@#async-fn-pinned",
            "work-poll",
            "async-generator-mixed-external",
            &config,
        );
        if !mutable {
            assert!(standalone.contains("external.0"), "{standalone}");
        }
        assert!(standalone.contains(if mutable {
            "(#ref-mut #u64)"
        } else {
            "(#ref #u64)"
        }));
        check_build_and_run(&scratch, &standalone, if mutable { 42 } else { 50 });
        let invalid = standalone.replace(
            "(#let answer #u64 (#match",
            "(#set-field external selected 99u64) (#let answer #u64 (#match",
        );
        let error = lim::check_types(&lim::parse_program(&invalid).unwrap()).unwrap_err();
        assert!(error.contains("borrow"), "{error}");
    }
}

fn check_build_and_run(scratch: &support::Scratch, source: &str, expected: i32) {
    let path = scratch.path().join("standalone.lim");
    let cache = scratch.path().join("standalone-cache");
    let program = lim::parse_program_from_path_with_config_and_cache(
        source,
        &path,
        &lim::CompileConfig::default(),
        &cache,
    )
    .unwrap_or_else(|error| panic!("{error}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("standalone");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(expected), "{stderr:?}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

#[test]
fn movable_async_artifact_is_checked_and_run_as_ordinary_lim() {
    let source = "(#enum Child (#linear) ((Waiting #u64)))

      (#enum ChildPoll () ((ChildPending Child) (ChildReady #u64)))
      (#syntax ChildAwait (#u64 Child ChildPending ChildReady child-poll))
      (#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Waiting amount) (ChildReady amount)))))
      (@#async-fn (: protocol WorkAwait : waker #u64 : function
        (#fn work ((seed #u64)) #u64
          (#let answer #u64 (#await ChildAwait (Waiting seed)))
          (#return (#u64.+.wrap answer 2u64)))))
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let result Work-poll-result
          (#call work-poll (: task (#call work (: seed 40u64)) : waker (#borrow waker))))
        (#return (#match result
          (#case (work-ready value) value)
          (#case (work-pending pending) (#block (#forget pending) (#unreachable))))))";
    let (scratch, standalone) = generated_standalone(
        source,
        "(@#async-fn",
        "work-poll",
        "async-generator-movable",
    );
    check_build_and_run(&scratch, &standalone, 42);

    let misuse = format!(
        "{standalone}\n(#fn illegal () ()
          (#let-mut owner #u64 1u64)
          (#let view (#ref #u64) (#borrow owner))
          (#set owner 2u64) (#drop view) (#return ()))"
    );
    let program = lim::parse_program(&misuse).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}

#[test]
fn pinned_local_self_reference_artifact_is_checked_and_run_as_ordinary_lim() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim");
    let (scratch, standalone) = generated_standalone(
        source,
        "(@#async-fn-pinned",
        "local-self-ref-poll",
        "async-generator-pinned",
    );
    check_build_and_run(&scratch, &standalone, 42);
}

#[test]
fn mutable_self_reference_artifact_uses_ordinary_loan_identities_and_local_pins() {
    let source = include_str!("../examples/async_fn_local_self_reference.lim")
        .replace("(#pin-ref #u64)", "(#pin-ref-mut #u64)")
        .replace("(#pin-borrow (#get (#get owner payload) left))",
            "(#pin-borrow-mut (#get (#get owner payload) left))")
        .replace("    (#return (#u64.+.wrap (#deref view) result))",
            "    (#unsafe (#pin-write view 41u64))\n    (#return (#u64.+.wrap (#deref view) result))")
        .replace("(#pin-borrow-mut frame)", "(#pin frame)");
    // Changing the reference kind must not silently make its owner mutable.
    // Validate the original source before asking for ordinary generated code.
    let rejected = support::Scratch::new("async-generator-immutable-pin");
    let error = lim::compile_source_to_assembly(
        &source,
        &rejected.path().join("input.lim"),
        &lim::CompileConfig::default(),
        &rejected.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .expect_err("exclusive self-reference requires an explicitly mutable owner");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    assert!(error.message.contains("immutable reference"), "{error:?}");
    let span = error
        .span
        .expect("immutable pinned projection has a source span");
    assert!(
        source[span.start..span.end].contains("#pin-borrow-mut"),
        "{error:?}"
    );
    let source = source.replace("(#let owner LocalOwner", "(#let-mut owner LocalOwner");
    let (scratch, standalone) = generated_standalone(
        &source,
        "(@#async-fn-pinned",
        "local-self-ref-poll",
        "async-generator-mutable-pin",
    );
    check_build_and_run(&scratch, &standalone, 43);
}
