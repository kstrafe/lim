mod support;

use std::{fs, process::Command, time::Duration};

fn config() -> lim::CompileConfig {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    config
}

#[test]
fn external_graph_source_uses_prefixed_aliases_and_parameter_names() {
    let scratch = support::Scratch::new("async-external-source-alias");
    fs::write(
        scratch.path().join("module.lim"),
        "(#type Amount #u64)
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work (: amount Amount) Amount (#return amount))))",
    )
    .unwrap();
    let source = "(#import-external \"module.lim\" Ext)
      (#fn main () #u64
        (#let waker #u64 0u64)
        (#let-mut frame Ext@Work::Frame (#call Ext::work (: Ext::amount 42u64)))
        (#let result #u64 (#match (#call Ext@Work::poll
          (: task (#pin-borrow-mut frame) : waker (#borrow waker)))
          (#case (Ext@Work::Poll.Ready value) value)
          (#case (Ext@Work::Poll.Pending unexpected) (#block (#forget unexpected) (#unreachable)))))
        (#forget frame) (#return result))";
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
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
    assert_eq!(status.code(), Some(42), "{status:?} {stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn external_graph_source_preserves_the_original_borrow_violation_span() {
    let scratch = support::Scratch::new("async-external-source-invalid");
    let module = "(#type Amount #u64)
      (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64
        : function (#fn work (: amount Amount) Amount
          (#let-mut local Amount amount)
          (#let alias (#ref Amount) (#borrow local))
          (#set local 99u64)
          (#return (#deref alias)))))";
    fs::write(scratch.path().join("module.lim"), module).unwrap();
    let source = "(#import-external \"module.lim\" Ext) (#fn main () #u64 (#return 0u64))";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &config(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(span.source_id, 1, "{error:?}");
    assert_eq!(&module[span.start..span.end], "#set", "{error:?}");
    assert!(error.message.contains("Ext::local"), "{error:?}");
    assert!(
        error.labels.iter().any(|label| label.span.source_id == 1
            && &module[label.span.start..label.span.end] == "#borrow"),
        "{error:?}"
    );
    assert!(
        error.source_name.as_ref().unwrap().ends_with("module.lim"),
        "{error:?}"
    );
}
