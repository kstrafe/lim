mod support;

use lim::{check_types, parse_program};
use std::{fs, process::Command, time::Duration};

fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}

#[test]
fn all_borrow_modes_project_or_take_the_explicit_failure_path() {
    for (keyword, reference, borrow) in [
        ("ref", "ref", "borrow"),
        ("ref-mut", "ref-mut", "borrow-mut"),
        ("pin", "pin-ref", "pin-borrow"),
        ("pin-mut", "pin-ref-mut", "pin-borrow-mut"),
    ] {
        for (value, answer) in [("(Full 42u64)", 42), ("Empty", 7)] {
            let source = format!(
                "(#enum Choice () ((Full #u64) Empty))
              (#fn main () #u64
                (#let-mut owner Choice {value})
                (#let-else-{keyword} (Full payload) (#{reference} Choice) (#{borrow} owner)
                  (#return 7u64))
                (#return (#deref payload)))"
            );
            check(&source).unwrap();
            let scratch = support::Scratch::new("borrowed-let-else");
            let input = scratch.path().join("main.lim");
            let binary = scratch.path().join("program");
            fs::write(&input, &source).unwrap();
            let (status, _, stderr) = support::run(
                Command::new(env!("CARGO_BIN_EXE_lim"))
                    .arg(&input)
                    .arg("-o")
                    .arg(&binary),
                Duration::from_secs(20),
                64 * 1024,
            )
            .unwrap();
            assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
            let (status, _, stderr) =
                support::run(&mut Command::new(&binary), Duration::from_secs(5), 1024).unwrap();
            assert_eq!(status.code(), Some(answer), "{source}: {stderr:?}");
        }
    }
}

#[test]
fn borrowed_payloads_retain_the_owner_loan_and_mutability() {
    for (keyword, reference, borrow) in [
        ("ref", "ref", "borrow"),
        ("ref-mut", "ref-mut", "borrow-mut"),
        ("pin", "pin-ref", "pin-borrow"),
        ("pin-mut", "pin-ref-mut", "pin-borrow-mut"),
    ] {
        let source = format!("(#enum Choice () ((Full #u64) Empty))
          (#fn main () #u64
            (#let-mut owner Choice (Full 42u64))
            (#let-else-{keyword} (Full payload) (#{reference} Choice) (#{borrow} owner) (#return 0u64))
            (#set owner Empty)
            (#return (#deref payload)))");
        let error = check(&source).unwrap_err();
        assert!(
            error.contains("borrow") || error.contains("pinned"),
            "{keyword}: {error}"
        );
        let forgotten = source.replace("(#set owner Empty)", "(#forget owner)");
        assert!(
            check(&forgotten).is_err(),
            "{keyword} must retain its referent"
        );
    }
}

#[test]
fn failure_bindings_are_borrowed_and_fieldless_or_ignored_successes_work() {
    for (keyword, reference, borrow) in [
        ("ref", "ref", "borrow"),
        ("ref-mut", "ref-mut", "borrow-mut"),
        ("pin", "pin-ref", "pin-borrow"),
        ("pin-mut", "pin-ref-mut", "pin-borrow-mut"),
    ] {
        let source = format!(
            "(#enum Choice () ((Full #u64) Empty))
          (#fn main () #u64
            (#let-mut owner Choice (Full 42u64))
            (#let-else-{keyword} Empty (#{reference} Choice) (#{borrow} owner)
              (#else (Full payload) (#return (#deref payload))))
            (#return 0u64))"
        );
        check(&source).unwrap();
        let ignored = source.replace("Empty (", "(Full _) (").replace(
            "(#else (Full payload) (#return (#deref payload)))",
            "(#return 0u64)",
        );
        check(&ignored).unwrap();
    }
}

#[test]
fn invalid_modes_patterns_fallbacks_and_removed_projections_are_rejected() {
    let valid = "(#enum Choice () ((Full #u64) Empty))
      (#fn main () #u64 (#let-mut owner Choice (Full 42u64))
        (#let-else-pin-mut (Full payload) (#pin-ref-mut Choice) (#pin-borrow-mut owner) (#return 0u64))
        (#return (#deref payload)))";
    for source in [
        valid.replace("(#return 0u64)", "(#forget owner)"),
        valid.replace("(#pin-ref-mut Choice)", "(#pin-ref Choice)"),
        valid.replace("#let-else-pin-mut", "#let-else-ref-mut"),
        valid.replace("(Full payload)", "(Missing payload)"),
        valid.replace("(Full payload)", "(Empty payload)"),
        valid.replace("(Full payload)", "(Full (#tuple x y))"),
    ] {
        assert!(check(&source).is_err(), "{source}");
    }
    for removed in ["#pin-get-payload", "#pin-get-payload-mut"] {
        let source = format!(
            "(#enum Choice () ((Full #u64) Empty))
          (#fn main () #u64 (#let-mut owner Choice (Full 42u64))
            (#let view (#pin-ref-mut #u64) ({removed} (#pin-borrow-mut owner) Full))
            (#return (#deref view)))"
        );
        assert!(
            check(&source).is_err(),
            "removed asserting projection remained available"
        );
    }
}

#[test]
fn returned_payload_references_keep_the_callers_origin_and_reject_local_escape() {
    for (mode, reference) in [
        ("ref", "ref"),
        ("ref-mut", "ref-mut"),
        ("pin", "pin-ref"),
        ("pin-mut", "pin-ref-mut"),
    ] {
        let source = format!("(#enum Choice () ((Full #u64) Empty))
          (#fn project (: source (#{reference} Choice) : fallback (#{reference} #u64)) (#{reference} #u64)
            (#let-else-{mode} (Full payload) (#{reference} Choice) source (#return fallback))
            (#return payload))");
        check(&source).unwrap();
        let borrow = match mode {
            "ref" => "borrow",
            "ref-mut" => "borrow-mut",
            "pin" => "pin-borrow",
            _ => "pin-borrow-mut",
        };
        let local = source
            .replace(
                "source (#return fallback)",
                &format!("(#{borrow} local) (#return fallback)"),
            )
            .replace(
                "(#let-else-",
                "(#let-mut local Choice (Full 42u64)) (#let-else-",
            );
        assert!(check(&local).is_err(), "{mode}: local referent escaped");
    }
}

#[test]
fn a_bound_failure_can_release_its_view_and_destroy_the_linear_owner() {
    let source = "(#struct Resource (#linear) (: value #u64))
      (#enum Choice () ((Full Resource) (Other Resource)))
      (#fn main () #u64
        (#let-mut owner Choice (Other (#struct-literal Resource (: value 42u64))))
        (#let-else-pin-mut (Full payload) (#pin-ref-mut Choice) (#pin-borrow-mut owner)
          (#else (Other failure)
            (#let answer #u64 (#get failure value))
            (#drop failure) (#forget owner) (#return answer)))
        (#drop payload) (#forget owner) (#return 0u64))";
    check(source).unwrap();
}

#[test]
fn generated_declarations_aliases_and_external_prefixes_share_the_same_rules() {
    let scratch = support::Scratch::new("borrowed-let-import");
    fs::write(
        scratch.path().join("library.lim"),
        "
      (#gn declare () `((#enum Choice () ((Full #u64) Empty))
        (#type View (#pin-ref Choice))))
      (@declare)
      (#fn read (: input View) #u64
        (#let-else-pin (Full value) View input (#return 0u64))
        (#return (#deref value)))",
    )
    .unwrap();
    let source = "(#import-external \"library.lim\" ext-)
      (#fn main () #u64
        (#let owner ext-Choice (ext-Full 42u64))
        (#return (#call ext-read (: ext-input (#pin-borrow owner)))))";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    check_types(&program).unwrap();
}

#[test]
fn generated_async_protocol_enums_can_be_borrowed_before_their_layout_is_emitted() {
    check(
        "(@#async-fn-pinned (: protocol WorkAwait : waker #u64
      : function (#fn work () #u64 (#return 42u64))))
      (#fn read (: input (#ref Work::Poll)) #u64
        (#let-else-ref (Work::Ready value) (#ref Work::Poll) input (#return 0u64))
        (#return (#deref value)))
      (#fn main () #u64 (#return 0u64))",
    )
    .unwrap();
}
