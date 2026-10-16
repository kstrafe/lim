mod support;

use lim::{Diagnostic, DiagnosticCode};
use std::{process::Command, time::Duration};

const CHILD: &str = "(#enum Child (#linear) ((Waiting #u64)))
  (#enum ChildPoll () ((ChildPending Child) (ChildReady #u64)))
  (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
    (#return (#match task
      (#case (Waiting count)
        (#if (#u64.< count 2u64)
          (ChildPending (Waiting (#u64.+.wrap count 1u64)))
          (ChildReady count))))))
  (#fn cancel-child (: child Child) () (#forget child) (#return ()))";

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

fn compile_error(source: &str, label: &str) -> Diagnostic {
    let scratch = support::Scratch::new(label);
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("input.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

fn run_native(source: &str, label: &str, expected: i32) {
    let scratch = support::Scratch::new(label);
    let input = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &input,
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
    };
    let cold = compile().unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let warm = compile().unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    assert_eq!(cold, warm, "cold and warm compilation differ");
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
    assert_eq!(
        status.code(),
        Some(expected),
        "status={status:?}; {stderr:?}"
    );
    assert!(stdout.is_empty() && stderr.is_empty());
}

fn assert_independent_generated_source(source: &str) {
    let scratch = support::Scratch::new("async-static-independent-source");
    let input = scratch.path().join("input.lim");
    let generated = scratch.path().join("generated");
    let cache = scratch.path().join("cache");
    lim::write_generated_sources_from_path_with_config_and_cache(
        source,
        &input,
        &generated,
        &config(),
        &cache,
    )
    .unwrap();
    let artifact = std::fs::read_dir(&generated)
        .unwrap()
        .filter_map(Result::ok)
        .map(|entry| std::fs::read_to_string(entry.path()).unwrap())
        .find(|artifact| artifact.contains("(#fn Work::poll "))
        .expect("generated artifact containing Work::poll")
        .replace("Lim.async.", "Ordinary.frame.")
        .replace(".graph.", ".ordinary.")
        .replace("lim.async.", "ordinary.frame.");
    assert!(!artifact.contains("@#async-fn"), "{artifact}");
    assert!(!artifact.contains("#await"), "{artifact}");
    let form = lim::parse(source)
        .unwrap()
        .into_iter()
        .find(|form| source[form.span.start..form.span.end].starts_with("(@#async-fn-pinned"))
        .expect("pinned async form");
    let standalone = format!(
        "{}\n{}\n{}",
        &source[..form.span.start],
        artifact,
        &source[form.span.end..]
    );
    assert!(!standalone.contains("@#async-fn"), "{standalone}");
    assert!(!standalone.contains("#await"), "{standalone}");
    let path = scratch.path().join("standalone.lim");
    let cache = scratch.path().join("standalone-cache");
    let program =
        lim::parse_program_from_path_with_config_and_cache(&standalone, &path, &config(), &cache)
            .unwrap_or_else(|error| panic!("{error}\n{standalone}"));
    lim::check_types(&program).unwrap_or_else(|error| panic!("{error:?}\n{standalone}"));
    lim::generate_assembly(&program).unwrap_or_else(|error| panic!("{error:?}\n{standalone}"));
}

fn generated_source_error(source: &str, label: &str) -> String {
    let scratch = support::Scratch::new(label);
    lim::write_generated_sources_from_path_with_config_and_cache(
        source,
        &scratch.path().join("input.lim"),
        &scratch.path().join("generated"),
        &config(),
        &scratch.path().join("cache"),
    )
    .unwrap_err()
}

fn anchor_source(mutable: bool) -> String {
    let ref_ty = if mutable {
        "(#ref-mut #u64)"
    } else {
        "(#ref #u64)"
    };
    let borrow = if mutable { "#borrow-mut" } else { "#borrow" };
    let selected = if mutable {
        format!("({borrow} local)")
    } else {
        format!("(#if choose ({borrow} local) external)")
    };
    let external_arg = if mutable {
        "(#borrow-mut external)"
    } else {
        "(#unsafe (#borrow Global))"
    };
    let update = if mutable {
        "(#deref-set view 41u64)"
    } else {
        ""
    };
    let expect = if mutable { 43 } else { 42 };
    format!("{CHILD}
      (#static Global #u64 40u64)
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64
        : cancel (work-cancel ((await-0 cancel-child)))
        : function (#fn work (: choose #bool : external {ref_ty}) #u64
          (#let-mut local #u64 40u64)
          (#let-mut view {ref_ty} {selected})
          (#let result #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          {update}
          (#let answer #u64 (#u64.+.wrap (#deref view) result))
          (#drop view) (#forget local) (#return answer))))
      (#fn cancel-current (: task (#pin-ref-mut Work::Frame)) ()
        (#call work-cancel (: task (#call Work::poll::cleanup (: task task))))
        (#call work-cancel (: task (#call Work::poll::cleanup (: task task))))
        (#return ()))
      (#fn run (: choose #bool : cancel-at #u64) #u64
        (#let-mut external #u64 40u64)
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (: choose choose : external {external_arg})))
        (#if (#u64.== cancel-at 0u64) (#block
          (#call cancel-current (: task (#pin-borrow-mut task)))
          (#forget task) (#return 42u64)) ())
        (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (Work::Pending pending) Work::Poll first (#unreachable))
        (#if (#u64.== cancel-at 1u64) (#block
          (#call work-cancel (: task (#call Work::poll::cleanup (: task pending))))
          (#call work-cancel (: task (#call Work::poll::cleanup (: task (#pin-borrow-mut task)))))
          (#forget task) (#return 42u64)) ())
        (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
        (#let-else (Work::Pending pending-again) Work::Poll second (#unreachable))
        (#if (#u64.== cancel-at 2u64) (#block
          (#call work-cancel (: task (#call Work::poll::cleanup (: task pending-again))))
          (#call work-cancel (: task (#call Work::poll::cleanup (: task (#pin-borrow-mut task)))))
          (#forget task) (#return 42u64)) ())
        (#let third Work::Poll (#call Work::poll (: task pending-again : waker (#borrow waker))))
        (#let result #u64 (#match third
          (#case (Work::Ready value) value)
          (#case (Work::Pending bad) (#block (#forget bad) (#unreachable)))))
        (#if (#u64.== cancel-at 3u64) (#block
          (#call cancel-current (: task (#pin-borrow-mut task)))
          (#forget task) (#return 42u64)) ())
        (#forget task) (#return result))
      (#fn main () #u64
        (#assert (#u64.== (#call run (: choose true : cancel-at 4u64)) {expect}u64))
        (#assert (#u64.== (#call run (: choose false : cancel-at 4u64)) {expect}u64))
        (#assert (#u64.== (#call run (: choose false : cancel-at 0u64)) 42u64))
        (#assert (#u64.== (#call run (: choose false : cancel-at 1u64)) 42u64))
        (#assert (#u64.== (#call run (: choose false : cancel-at 2u64)) 42u64))
        (#assert (#u64.== (#call run (: choose false : cancel-at 3u64)) 42u64))
        (#return 42u64))")
}

#[test]
fn pinned_static_and_local_shared_references_survive_repeated_pending() {
    let source = anchor_source(false);
    assert_independent_generated_source(&source);
    run_native(&source, "async-static-anchor-shared", 42);
}

#[test]
fn pinned_local_exclusive_reference_survives_repeated_pending() {
    let source = anchor_source(true);
    assert_independent_generated_source(&source);
    run_native(&source, "async-static-anchor-exclusive", 42);
}

#[test]
fn direct_local_and_static_anchor_mix_is_rejected_without_checked_parameter() {
    let direct = anchor_source(false)
        .replace(" : external (#ref #u64)", "")
        .replace(
            "(#if choose (#borrow local) external)",
            "(#if choose (#borrow local) (#unsafe (#borrow Global)))",
        )
        .replace(" : external (#unsafe (#borrow Global))", "");
    let error = generated_source_error(&direct, "async-static-direct-mix-rejected");
    assert!(
        error.contains("selected external async anchors require a checked reference parameter"),
        "{error}"
    );
}

#[test]
fn native_layout_scalar_and_struct_field_static_references_match_cold_and_warm() {
    let source = format!("{CHILD}
      (#struct Record () (: tag #u8 : value #u64))
      (#static Global Record (#struct-literal Record (: tag 1u8 : value 40u64)))
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64 : cancel (work-cancel ((await-0 cancel-child)))
        : function (#fn work (: scalar-view (#ref #u64) : field-view (#ref #u64)) #u64
          (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#let result #u64 (#u64.+.wrap (#u64.+.wrap (#deref scalar-view) (#deref field-view)) ignored))
          (#drop field-view) (#drop scalar-view) (#return result))))
      (#fn main () #u64
        (#let scalar #u64 2u64)
        (#let waker #u64 0u64)
        (#let-mut task Work::Frame (#call work (: scalar-view (#borrow scalar) : field-view (#unsafe (#borrow (#get Global value))))))
        (#let first Work::Poll (#call Work::poll (: task (#pin-borrow-mut task) : waker (#borrow waker))))
        (#let-else (Work::Pending pending) Work::Poll first (#unreachable))
        (#let second Work::Poll (#call Work::poll (: task pending : waker (#borrow waker))))
        (#let-else (Work::Pending pending-again) Work::Poll second (#unreachable))
        (#let third Work::Poll (#call Work::poll (: task pending-again : waker (#borrow waker))))
        (#let result #u64 (#match third (#case (Work::Ready value) value) (#case (Work::Pending bad) (#block (#forget bad) (#unreachable)))))
        (#forget task) (#drop scalar) (#return (#if (#u64.== result 44u64) 42u64 0u64)))");
    assert_independent_generated_source(&source);
    run_native(&source, "async-static-anchor-layout", 42);
}

#[test]
fn static_access_requires_unsafe_and_alias_conflict_is_a_borrow_error() {
    let unsafe_error = compile_error(
        "(#static Global #u64 40u64) (#fn main () #u64 (#return Global))",
        "async-static-requires-unsafe",
    );
    assert_eq!(
        unsafe_error.code,
        DiagnosticCode::Unsafe,
        "{unsafe_error:?}"
    );

    let source = format!("{CHILD}
      (#static Global #u64 40u64)
      (@#async-fn-pinned (: protocol WorkAwait : waker #u64 : cancel (work-cancel ((await-0 cancel-child)))
        : function (#fn work () #u64
          (#let-mut owner #u64 40u64)
          (#let-mut view (#ref-mut #u64) (#borrow-mut owner))
          (#let ignored #u64 (#await Child ChildPending ChildReady child-poll (Waiting 0u64)))
          (#let alias (#ref #u64) (#borrow owner))
          (#drop alias) (#drop view) (#forget owner) (#forget ignored) (#return 0u64))))");
    let error = compile_error(&source, "async-static-alias-conflict");
    assert_eq!(error.code, DiagnosticCode::Borrow, "{error:?}");
    let span = error
        .span
        .expect("borrow diagnostic should identify conflict");
    let expected = source.rfind("(#borrow owner)").unwrap() + 1;
    assert_eq!(span.start, expected, "{error:?}");
    assert_eq!(&source[span.start..span.end], "#borrow", "{error:?}");
}

#[test]
fn atomic_static_literal_initializer_has_native_cold_warm_parity() {
    let source = "(#static Counter (#atomic #u64) (#atomic-init #u64 0u64))
      (#fn main () #u64
        (#unsafe (#atomic-fetch-add (#borrow Counter) 42u64 #memory-relaxed))
        (#return (#unsafe (#atomic-load (#borrow Counter) #memory-acquire))))";
    run_native(source, "async-static-atomic-literal-init", 42);
}
