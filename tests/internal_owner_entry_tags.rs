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

#[test]
fn mutable_reference_in_enum_payload_blocks_owner_reads_through_callees() {
    let source = r#"
      (#enum View (NoView (HasView (#pin-ref-mut u64))))
      (#struct Link (: value u64 : view View))
      (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#let view (#pin-ref-mut u64) (#pin-borrow-mut (#get target value)))
        (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) (HasView view)))
        (#return target))
      (#fn observe (: target (#pin-ref-mut Link)) u64
        (#return (#get target value)))
      (#fn driver () u64
        (#let-mut link Link (#struct-literal Link (: value 42u64 : view NoView)))
        (#let installed (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))
        (#let value u64 (#call observe (: target installed)))
        (#unsafe (#pin-write (#pin-borrow-mut (#get installed view)) NoView))
        (#drop installed) (#forget link) (#return value))
      (#fn main () u64 (#return (#call driver ())))
    "#;
    let error = compile(
        source,
        &support::Scratch::new("internal-owner-payload-observation"),
    )
    .expect_err("reading the owner must conflict with its retained exclusive child");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored conflicting reference"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "installed");
    assert!(error
        .labels
        .iter()
        .any(|label| { &source[label.span.start..label.span.end] == "(#get target value)" }));
}

#[test]
fn inactive_conditional_child_allows_guarded_owner_reads_but_active_child_does_not() {
    let source = r#"
      (#enum View (NoView (HasView (#pin-ref-mut u64))))
      (#struct Link (: value u64 : view View))
      (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#let view (#pin-ref-mut u64) (#pin-borrow-mut (#get target value)))
        (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) (HasView view)))
        (#return target))
      (#fn observe (: target (#pin-ref-mut Link)) ()
        (#if (#variant-is (#pin-borrow (#get target view)) NoView)
          (#block (#let observed u64 (#get target value)) (#forget observed) ()) ())
        (#return ()))
      (#fn driver () u64
        (#let-mut link Link (#struct-literal Link (: value 42u64 : view NoView)))
        (#let installed (#pin-ref-mut Link)
          (#call install (: target (#pin-borrow-mut link))))
        (#call observe (: target installed))
        (#unsafe (#pin-write (#pin-borrow-mut (#get installed view)) NoView))
        (#drop installed) (#forget link) (#return 42u64))
      (#fn main () u64 (#return (#call driver ())))
    "#;
    let scratch = support::Scratch::new("internal-owner-conditional-observation-positive");
    let assembly = compile(source, &scratch).unwrap_or_else(|error| panic!("{error:?}"));
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

    let active_read = source.replace("view)) NoView", "view)) HasView");
    assert_ne!(
        active_read, source,
        "the active-variant negative must change its guard"
    );
    let error = compile(
        &active_read,
        &support::Scratch::new("internal-owner-conditional-observation-negative"),
    )
    .expect_err("the active child must continue to block an overlapping owner read");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored conflicting reference"),
        "{}",
        error.message
    );
}

#[test]
fn shared_reference_in_enum_payload_blocks_owner_mut_borrows_through_callees() {
    let source = r#"
      (#enum View (NoView (HasView (#pin-ref u64))))
      (#struct Link (: value u64 : view View))
      (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#let view (#pin-ref u64) (#pin-borrow (#get target value)))
        (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) (HasView view)))
        (#return target))
      (#fn mutate (: target (#pin-ref-mut Link)) ()
        (#let writer (#pin-ref-mut u64) (#pin-borrow-mut (#get target value)))
        (#unsafe (#pin-write writer 99u64))
        (#drop writer) (#return ()))
      (#fn driver () ()
        (#let-mut link Link (#struct-literal Link (: value 42u64 : view NoView)))
        (#let installed (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))
        (#call mutate (: target installed))
        (#unsafe (#pin-write (#pin-borrow-mut (#get installed view)) NoView))
        (#drop installed) (#forget link) (#return ()))
      (#fn main () () (#call driver ()) (#return ()))
    "#;
    let error = compile(
        source,
        &support::Scratch::new("internal-owner-shared-payload-mutation"),
    )
    .expect_err("a shared payload loan forbids an exclusive owner reborrow");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored internal reference"),
        "{}",
        error.message
    );
    assert!(error.message.contains("'mutate'"), "{}", error.message);
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "installed");
}

#[test]
fn mutable_reference_to_enum_payload_blocks_owner_access_through_callees() {
    let source = r#"
      (#enum Value (Empty (Full u64)))
      (#enum View (NoView (Self (#pin-ref-mut u64))))
      (#struct Link (: value Value : view View))
      (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#let view (#pin-ref-mut u64)
          (#pin-get-payload-mut (#pin-borrow-mut (#get target value)) Full 0))
        (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) (Self view))) (#return target))
      (#fn mutate (: target (#pin-ref-mut Link)) ()
        (#let writer (#pin-ref-mut u64)
          (#pin-get-payload-mut (#pin-borrow-mut (#get target value)) Full 0))
        (#unsafe (#pin-write writer 99u64))
        (#drop writer) (#return ()))
      (#fn driver () ()
        (#let-mut link Link (#struct-literal Link (: value (Full 42u64) : view NoView)))
        (#let installed (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))
        (#call mutate (: target installed))
        (#unsafe (#pin-write (#pin-borrow-mut (#get installed view)) NoView))
        (#drop installed) (#forget link) (#return ()))
      (#fn main () () (#call driver ()) (#return ()))
    "#;
    let error = compile(
        source,
        &support::Scratch::new("internal-owner-payload-referent-mutation"),
    )
    .expect_err("mutating a payload cannot bypass its retained reference loan");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored internal reference"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "installed");
}

#[test]
fn owner_checks_follow_mutable_references_stored_in_nested_owners() {
    let source = r#"
      (#enum View (Empty (Full (#ref-mut u64))))
      (#struct Inner (: value u64 : view View))
      (#struct Outer (: inner (#ref-mut Inner)))
      (#fn install (: target (#ref-mut Outer)) (#ref-mut Outer)
        (#let inner (#ref-mut Inner) (#get target inner))
        (#let child (#ref-mut u64) (#borrow-mut (#get inner value)))
        (#deref-set (#borrow-mut (#get inner view)) (Full child))
        (#return target))
      (#fn mutate (: target (#ref-mut Outer)) ()
        (#let inner (#ref-mut Inner) (#get target inner))
        (#deref-set (#borrow-mut (#get inner value)) 99u64)
        (#return ()))
      (#fn main () ()
        (#let-mut inner Inner (#struct-literal Inner (: value 42u64 : view Empty)))
        (#let inner-ref (#ref-mut Inner) (#borrow-mut inner))
        (#let-mut outer Outer (#struct-literal Outer (: inner inner-ref)))
        (#let outer-ref (#ref-mut Outer) (#borrow-mut outer))
        (#let installed (#ref-mut Outer) (#call install (: target outer-ref)))
        (#call mutate (: target installed))
        (#return ()))
    "#;
    let error = compile(
        source,
        &support::Scratch::new("internal-owner-nested-pointer-mutation"),
    )
    .expect_err("an outer borrow must carry child loans through nested owners");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn unknown_direct_payload_slot_does_not_hide_a_mutable_owner_alias() {
    let source = r#"
      (#enum View (Empty (Full (#ref-mut u64))))
      (#struct Link (: value u64 : view View))
      (#fn install (: target (#ref-mut Link)) (#ref-mut Link)
        (#let child (#ref-mut u64) (#borrow-mut (#get target value)))
        (#deref-set (#borrow-mut (#get target view)) (Full child))
        (#return target))
      (#fn mutate (: target (#ref-mut Link)) ()
        (#deref-set (#borrow-mut (#get target value)) 99u64)
        (#return ()))
      (#fn driver (: choose bool) ()
        (#let-mut link Link (#struct-literal Link (: value 42u64 : view Empty)))
        (#if choose
          (#block
            (#let installed (#ref-mut Link)
              (#call install (: target (#borrow-mut link))))
            (#drop installed) ())
          ())
        (#call mutate (: target (#borrow-mut link)))
        (#forget link) (#return ()))
      (#fn main () () (#call driver (: choose true)) (#return ()))
    "#;
    let error = compile(
        source,
        &support::Scratch::new("internal-owner-unknown-direct-payload-slot"),
    )
    .expect_err("a join cannot discard a possible mutable alias in an enum payload");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("stored internal reference"),
        "{}",
        error.message
    );
}
