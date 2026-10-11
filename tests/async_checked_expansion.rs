//! Checked graph expansion must remain tied to its exact source program.
mod support;

use std::{fs, process::Command, time::Duration};

const SOURCE: &str = "
  (#enum Child ((Start #u64) (Resume #u64))) (#linear Child)
  (#enum ChildPoll ((Pending Child) (Ready #u64)))
  (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
    (#return (#match task
      (#case (Start value) (Pending (Resume value)))
      (#case (Resume value) (Ready value)))))
  (@#async-fn (: protocol WorkAwait : waker #u64
    : function (#fn work (: seed #u64) #u64
      (#return (#await Child Pending Ready child-poll (Start seed))))))
  (#fn main () #u64
    (#let waker #u64 0u64)
    (#let first Work-poll-result (#call work-poll
      (: task (#call work (: seed 42u64)) : waker (#borrow waker))))
    (#let-else (work-pending next) Work-poll-result first (#unreachable))
    (#return (#match (#call work-poll (: task next : waker (#borrow waker)))
      (#case (work-ready value) value)
      (#case (work-pending bad) (#block (#forget bad) (#unreachable))))))";

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

#[test]
fn checked_expansion_compiles_and_materializes_cold_and_warm() {
    let scratch = support::Scratch::new("checked-expansion");
    let path = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let generated = scratch.path().join("generated");
    let mut previous = None;
    for _ in 0..2 {
        lim::check_source_with_generated_sources(SOURCE, &path, &config(), &cache, &generated)
            .unwrap();
        let assembly = lim::compile_source_with_generated_sources(
            SOURCE,
            &path,
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
            None,
            &generated,
        )
        .unwrap();
        if let Some(previous) = previous.as_ref() {
            assert_eq!(&assembly, previous);
        }
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
        previous = Some(assembly);
    }
    assert!(fs::read_dir(generated).unwrap().next().is_some());
}

#[test]
fn cached_generator_output_never_certifies_changed_user_code() {
    let scratch = support::Scratch::new("checked-expansion-negative");
    let path = scratch.path().join("input.lim");
    let cache = scratch.path().join("cache");
    let compile = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &path,
            &config(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
    };
    compile(SOURCE).unwrap();
    let invalid = SOURCE.replace(": seed 42u64", ": seed true");
    for _ in 0..2 {
        let diagnostic = compile(&invalid).unwrap_err();
        assert_eq!(diagnostic.source_text.as_deref(), Some(invalid.as_str()));
        let span = diagnostic.span.expect("source-spanned type mismatch");
        assert!(invalid[span.start..span.end].contains("true"));
    }
}
