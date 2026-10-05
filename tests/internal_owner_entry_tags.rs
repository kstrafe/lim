use std::{process::Command, time::Duration};
mod support;

const SOURCE: &str = r#"
  (#enum Value (Empty (Full u64)))
  (#struct Link (: value Value : view (#pin-ref u64)))
  (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
    (#let view (#pin-ref u64)
      (#pin-get-payload (#pin-borrow (#get target value)) Full 0))
    (#pin-set-field target view view) (#return target))
  (#fn initialize-or-touch (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
    (#if (#variant-is (#pin-borrow (#get target value)) Empty)
      (#block
        (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Full 40u64)))
        (#let payload (#pin-ref-mut u64)
          (#pin-get-payload-mut (#pin-borrow-mut (#get target value)) Full 0))
        (#unsafe (#pin-write payload 42u64))) ())
    (#return target))
  (#fn full_owner () u64
    (#let outside u64 0u64)
    (#let-mut link Link (#struct-literal Link
      (: value (Full 42u64) : view (#pin-borrow outside))))
    (#let installed (#pin-ref-mut Link)
      (#call install (: target (#pin-borrow-mut link))))
    (#let updated (#pin-ref-mut Link)
      (#call initialize-or-touch (: target installed)))
    (#let answer u64 (#deref (#get updated view)))
    (#pin-set-field updated view (#pin-borrow outside))
    (#drop updated) (#forget link) (#return answer))
  (#fn main () u64 (#return (#call full_owner ())))
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
fn initialization_before_installing_an_internal_reference_runs_natively() {
    let source = SOURCE
        .replace("value (Full 42u64)", "value Empty")
        .replace(
            "(#call install (: target (#pin-borrow-mut link))))",
            "(#call initialize-or-touch (: target (#pin-borrow-mut link))))",
        )
        .replace(
            "(#call initialize-or-touch (: target installed)))",
            "(#call install (: target installed)))",
        );
    let scratch = support::Scratch::new("internal-owner-entry-tags-positive");
    let assembly = compile(&source, &scratch).unwrap_or_else(|error| panic!("{error:?}"));
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
fn conditional_owner_access_stays_fail_closed_until_pinned_permissions_are_proved() {
    let scratch = support::Scratch::new("internal-owner-entry-tags-staged");
    let error =
        compile(SOURCE, &scratch).expect_err("entry constraints alone do not grant parent access");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("callee accesses a pinned pointee"),
        "{}",
        error.message
    );
}

#[test]
fn changed_entry_tag_cannot_make_incoming_payload_alias_safe() {
    let source = SOURCE.replace("value)) Empty)", "value)) Full)");
    let scratch = support::Scratch::new("internal-owner-entry-tags-negative");
    let error = compile(&source, &scratch)
        .expect_err("initializing on Full must retain the incoming self-loan");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("initialize-or-touch"),
        "{}",
        error.message
    );
    let span = error
        .span
        .expect("diagnostic should identify the caller argument");
    assert_eq!(&source[span.start..span.end], "installed");
    assert!(
        error
            .labels
            .iter()
            .any(|label| &source[label.span.start..label.span.end] == "(#pin-write payload 42u64)"),
        "{} {:?}",
        error.message,
        error
            .labels
            .iter()
            .map(|label| &source[label.span.start..label.span.end])
            .collect::<Vec<_>>()
    );
}

#[test]
fn an_initializer_guard_does_not_authorize_writes_after_the_branch_join() {
    let source = SOURCE.replace(
        "(#unsafe (#pin-write payload 42u64))) ())",
        "(#unsafe (#pin-write payload 42u64))) ())
         (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Full 99u64)))",
    );
    let error = compile(
        &source,
        &support::Scratch::new("internal-owner-entry-tags-join"),
    )
    .expect_err("an Empty-only arm does not prove Empty on the other arm");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored internal reference"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "installed");
    assert!(error
        .labels
        .iter()
        .any(|label| &source[label.span.start..label.span.end]
            == "(#pin-write (#pin-borrow-mut (#get target value)) (Full 99u64))"));
}
