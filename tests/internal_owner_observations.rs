use std::{process::Command, time::Duration};
mod support;

const SOURCE: &str = r#"
  (#struct Link () (: value #u64 : state #u32 : view (#pin-ref #u64)))
  (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
    (#let view (#pin-ref #u64) (#pin-borrow (#get target value)))
    (#pin-set-field target view view) (#return target))
  (#fn tick (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
    (#let observed #u64 (#get target value)) (#assert (#u64::eq observed 42u64))
    (#return target))
  (#fn driver (: outside (#pin-ref #u64)) #u64
    (#let-mut link Link (#struct-literal Link (: value 42u64 : state 0u32 : view outside)))
    (#let running (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))
    (#let updated (#pin-ref-mut Link) (#call tick (: target running)))
    (#let answer #u64 (#deref (#get updated view)))
    (#pin-set-field updated view outside) (#drop updated) (#forget link)
    (#return answer))
  (#fn main () #u64 (#let outside #u64 0u64)
    (#return (#call driver (: outside (#pin-borrow outside)))))
"#;

fn compile(source: &str, scratch: &support::Scratch) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn ordinary_owner_shared_reads_and_child_reads_run_natively() {
    let scratch = support::Scratch::new("internal-owner-observation");
    let assembly = compile(SOURCE, &scratch).unwrap_or_else(|e| panic!("{}", e.message));
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
}

#[test]
fn loaded_internal_child_survives_disjoint_owner_call_natively() {
    let source = SOURCE
        .replace(
            "(#let observed #u64 (#get target value)) (#assert (#u64::eq observed 42u64))",
            "(#pin-set-field target state 2u32)",
        )
        .replace(
            "(#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
            "(#let held (#pin-ref #u64) (#get running view))\n    (#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
        )
        .replace(
            "(#let running (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))",
            "(#let-mut running (#pin-ref-mut Link) (#pin-borrow-mut link))\n    (#let installed (#pin-ref-mut Link) (#call install (: target running)))\n    (#set running installed)",
        )
        .replace(
            "(#let answer #u64 (#deref (#get updated view)))",
            "(#let answer #u64 (#deref held))",
        )
        .replace(
            "(#pin-set-field updated view outside) (#drop updated) (#forget link)",
            "(#pin-set-field updated view outside) (#drop held) (#drop updated) (#forget link)",
        );
    let scratch = support::Scratch::new("loaded-internal-child-disjoint-call");
    let assembly = compile(&source, &scratch).unwrap_or_else(|e| panic!("{e:?}\n{source}"));
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
}

#[test]
fn a_shared_internal_child_blocks_an_exclusive_borrow_at_the_actual_call_argument() {
    let source = SOURCE.replace(
        "(#let observed #u64 (#get target value)) (#assert (#u64::eq observed 42u64))",
        "(#let another (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value))) (#drop another)",
    );
    let scratch = support::Scratch::new("internal-owner-exclusive-borrow");
    let error = compile(&source, &scratch)
        .expect_err("a stored shared child must block an exclusive owner borrow");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored conflicting reference"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "running");
    assert!(error
        .labels
        .iter()
        .any(|label| &source[label.span.start..label.span.end]
            == "(#pin-borrow-mut (#get target value))"));
}

const EXCLUSIVE_SOURCE: &str = r#"
  (#struct Link () (: value #u64 : state #u32 : view (#pin-ref-mut #u64)))
  (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
    (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value)))
    (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) view))
    (#return target))
  (#fn tick (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
    (#let observed #u64 (#get target value)) (#assert (#u64::eq observed 42u64))
    (#return target))
  (#fn finish (: target (#pin-ref-mut Link) : outside (#pin-ref-mut #u64)) #u64
    (#let answer #u64 (#deref (#get target view)))
    (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) outside))
    (#drop target) (#return answer))
  (#fn main () #u64
    (#let-mut outside #u64 0u64)
    (#let-mut link Link (#struct-literal Link (: value 42u64 : state 0u32
      : view (#pin-borrow-mut outside))))
    (#let running (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))
    (#let updated (#pin-ref-mut Link) (#call tick (: target running)))
    (#let answer #u64 (#call finish (: target updated : outside (#pin-borrow-mut outside))))
    (#forget link)
    (#return answer))
"#;

#[test]
fn an_exclusive_internal_child_blocks_owner_reads_but_preserves_child_access() {
    let source = EXCLUSIVE_SOURCE
        .replace(
            "(#let observed #u64 (#get target value)) (#assert (#u64::eq observed 42u64))",
            "(#let observed #u32 (#get target state)) (#assert (#u32::eq observed 0u32))
         (#unsafe (#pin-write (#get target view) 42u64))",
        )
        .replace(": value 42u64", ": value 10u64");
    let scratch = support::Scratch::new("internal-owner-exclusive-child-valid");
    let assembly = compile(&source, &scratch).unwrap_or_else(|e| panic!("{e:?}"));
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

    let error = compile(
        EXCLUSIVE_SOURCE,
        &support::Scratch::new("internal-owner-exclusive-child-error"),
    )
    .expect_err("a stored exclusive child must block an owner read");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored conflicting reference"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert_eq!(&EXCLUSIVE_SOURCE[span.start..span.end], "running");
    assert!(error
        .labels
        .iter()
        .any(|label| &EXCLUSIVE_SOURCE[label.span.start..label.span.end] == "(#get target value)"));
}
