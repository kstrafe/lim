mod support;

use lim::{CompileConfig, DiagnosticCode, TargetDescription};

struct Violation {
    name: &'static str,
    source: &'static str,
    conflict: &'static str,
    conflict_occurrence: usize,
    origin: Option<(&'static str, usize)>,
}

fn compile(source: &str, name: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new(name);
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("case.lim"),
        &CompileConfig::default(),
        &scratch.path().join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
}

fn assert_native_42(source: &str, name: &str) {
    let assembly = compile(source, name).unwrap();
    let scratch = support::Scratch::new(name);
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        &mut std::process::Command::new(binary),
        std::time::Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

#[test]
fn pending_cannot_export_a_handle_to_consumed_storage() {
    let source = include_str!("fixtures/pinned_empty_handle_pending.lim");
    let diagnostic = compile(source, "pinned-empty-handle-pending").unwrap_err();
    assert_eq!(diagnostic.code, DiagnosticCode::Linear);
    assert_eq!(
        diagnostic.message,
        "returned reference may point to a consumed linear referent"
    );
    let span = diagnostic.span.unwrap();
    assert_eq!(&source[span.start..span.end], "(#return (Pending item))");
    let consumed = source.find("(#pin-read item)").unwrap();
    assert!(diagnostic
        .labels
        .iter()
        .any(|label| label.span.start == consumed
            && &source[label.span.start..label.span.end] == "(#pin-read item)"));

    // Restoring the same stationary referent before returning permits the
    // handle to escape. This must not ban all reference-bearing results.
    let restored = source.replace("(#return (Pending item))",
        "(#unsafe (#pin-write item (#struct-literal Token (: value 2u64)))) (#return (Pending item))");
    compile(&restored, "pinned-restored-handle-pending").unwrap();
}

#[test]
fn retained_pinned_field_restores_across_calls_without_relocation() {
    let source = include_str!("fixtures/pinned_partial_field_calls.lim");
    assert_native_42(source, "pinned-partial-field-calls");
    for (name, replacement, offending) in [
        (
            "reborrow-empty-pinned-field",
            "(#call restore-item (: item (#pin-borrow-mut (#get owner item))))",
            "(#pin-borrow-mut (#get owner item))",
        ),
        (
            "read-unrestored-pinned-owner",
            "()",
            "(#call inspect (: target whole))",
        ),
    ] {
        let mut invalid = source.replace("(#call restore-item (: item item))", replacement);
        if name == "reborrow-empty-pinned-field" {
            // End the first call-duration field borrow before trying the new
            // one, so this tests initialization rather than overlapping loans.
            invalid = invalid
                .replace(
                    "(#let item (#pin-ref-mut Token) (#pin-borrow-mut (#get owner item)))",
                    "",
                )
                .replace(
                    "(#call consume-item (: item item))",
                    "(#call consume-item (: item (#pin-borrow-mut (#get owner item))))",
                )
                .replace("(#forget item)", "");
        }
        let diagnostic = compile(&invalid, name).unwrap_err();
        assert_eq!(diagnostic.code, DiagnosticCode::Linear, "{diagnostic:?}");
        let span = diagnostic.span.unwrap();
        assert_eq!(
            span.start,
            invalid.rfind(offending).unwrap(),
            "{diagnostic:?}"
        );
        assert_eq!(&invalid[span.start..span.end], offending, "{diagnostic:?}");
        let consumed = invalid.find("(#pin-read item)").unwrap();
        assert!(
            diagnostic
                .labels
                .iter()
                .any(|label| label.span.start == consumed),
            "{diagnostic:?}"
        );
    }
    let invalid = source.replace("(#call consume-item (: item item))",
        "(#let excluded (#pin-ref-mut #u64) (#pin-borrow-mut (#get owner kept))) (#forget excluded) (#call consume-item (: item item))");
    let diagnostic = compile(&invalid, "mutate-pinned-shared-sibling").unwrap_err();
    assert_eq!(diagnostic.code, DiagnosticCode::Borrow, "{diagnostic:?}");
    let span = diagnostic.span.unwrap();
    assert_eq!(
        &invalid[span.start..span.end],
        "#pin-borrow-mut",
        "{diagnostic:?}"
    );
    let origin = invalid.find("#borrow (#get owner kept)").unwrap();
    assert!(
        diagnostic
            .labels
            .iter()
            .any(|label| label.span.start == origin),
        "{diagnostic:?}"
    );
}

#[test]
fn restored_whole_borrow_preserves_live_sibling_address_and_alias_rules() {
    let source = include_str!("fixtures/partial_aggregate_whole_borrow.lim");
    assert_native_42(source, "restored-whole-borrow-native");

    // Restoration permits a shared whole borrow, not an overlapping exclusive
    // borrow. Borrowing the already-shared sibling exclusively is also invalid.
    for (name, replacement, conflict) in [
        (
            "exclusive-restored-whole",
            "(#let exclusive (#ref-mut Owner) (#borrow-mut owner)) (#forget exclusive) (#let whole (#ref Owner) (#borrow owner))",
            "#borrow-mut",
        ),
        (
            "exclusive-restored-sibling",
            "(#let exclusive (#ref-mut #u64) (#borrow-mut (#get owner kept))) (#forget exclusive) (#let whole (#ref Owner) (#borrow owner))",
            "#borrow-mut",
        ),
    ] {
        let invalid = source.replace("(#let whole (#ref Owner) (#borrow owner))", replacement);
        let diagnostic = compile(&invalid, name).unwrap_err();
        assert_eq!(diagnostic.code, DiagnosticCode::Borrow, "{diagnostic:?}");
        let span = diagnostic.span.unwrap();
        assert_eq!(&invalid[span.start..span.end], conflict, "{diagnostic:?}");
        let origin = invalid.find("#borrow (#get owner kept)").unwrap();
        assert!(diagnostic.labels.iter().any(|label| label.span.start == origin));
    }
}

fn assert_violation(case: Violation) {
    let diagnostic = match compile(case.source, case.name) {
        Err(diagnostic) => diagnostic,
        Ok(_) => panic!("{} unexpectedly compiled", case.name),
    };
    assert_eq!(
        diagnostic.code,
        DiagnosticCode::Borrow,
        "{}: {}",
        case.name,
        diagnostic.message
    );
    let primary = diagnostic.span.expect("borrow error needs a primary span");
    let primary_start = case
        .source
        .match_indices(case.conflict)
        .nth(case.conflict_occurrence)
        .unwrap_or_else(|| panic!("{}: missing conflict text {:?}", case.name, case.conflict))
        .0;
    assert_eq!(
        primary.start,
        primary_start,
        "{}: primary span {:?} should identify intended occurrence {:?}",
        case.name,
        &case.source[primary.start..primary.end],
        case.conflict
    );
    assert_eq!(
        &case.source[primary.start..primary.end],
        case.conflict,
        "{}: primary span should identify the conflicting operation",
        case.name
    );
    if let Some((origin, occurrence)) = case.origin {
        let origin_start = case
            .source
            .match_indices(origin)
            .nth(occurrence)
            .unwrap_or_else(|| panic!("{}: missing origin text {origin:?}", case.name));
        assert!(
            diagnostic
                .labels
                .iter()
                .any(|label| label.span.start == origin_start.0),
            "{}: expected a secondary label at {origin:?}: {:?}",
            case.name,
            diagnostic.labels
        );
    }
}

#[test]
fn rejects_adversarial_borrow_violations_at_the_conflicting_operation() {
    let cases = [
        Violation {
            name: "shared-then-write",
            source: "(#fn main () #u64
              (#let-mut owner #u64 1u64)
              (#let view (#ref #u64) (#borrow owner))
              (#set owner 2u64)
              (#drop view) (#return 0u64))",
            conflict: "#set",
            conflict_occurrence: 0,
            origin: Some(("#borrow owner", 0)),
        },
        Violation {
            name: "two-overlapping-call-arguments",
            source: "(#fn inspect (: left (#ref-mut #u64) : right (#ref #u64)) ()
                (#forget left) (#drop right) (#return ()))
              (#fn main () ()
                (#let-mut owner #u64 1u64)
                (#call inspect (: left (#borrow-mut owner) : right (#borrow owner)))
                (#return ()))",
            conflict: "(#borrow owner)",
            conflict_occurrence: 0,
            origin: Some(("#borrow-mut owner", 0)),
        },
        Violation {
            name: "parent-access-during-child-reborrow",
            source: "(#struct Pair (: left #u64 : right #u64))
              (#fn main () #u64
                (#let-mut pair Pair (#struct-literal Pair (: left 1u64 : right 2u64)))
                (#let parent (#ref-mut Pair) (#borrow-mut pair))
                (#let child (#ref-mut #u64) (#borrow-mut (#get parent left)))
                (#let bad #u64 (#get parent left))
                (#drop child) (#drop parent) (#forget pair) (#return bad))",
            conflict: "#get",
            conflict_occurrence: 1,
            origin: Some(("#borrow-mut (#get parent left)", 0)),
        },
        Violation {
            name: "dynamic-slice-indices-may-alias",
            source: "(#fn main () ()
              (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 1u64 2u64))
              (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
              (#let index #usize 0usize)
              (#let first (#ref-mut #u64) (#slice-mut-idx view index))
              (#let second (#ref-mut #u64) (#slice-mut-idx view index))
              (#deref-set first 10u64)
              (#deref-set second 20u64)
              (#forget first) (#forget second) (#forget view) (#forget values) (#return ()))",
            conflict: "#slice-mut-idx",
            conflict_occurrence: 1,
            origin: Some(("#borrow-mut values", 0)),
        },
        Violation {
            name: "block-local-reference-escape",
            source: "(#fn main () #u64
              (#let escaped (#ref #u64)
                (#block (#let local #u64 7u64) (#borrow local)))
              (#return (#deref escaped)))",
            conflict: "(#block (#let local #u64 7u64) (#borrow local))",
            conflict_occurrence: 0,
            origin: None,
        },
        Violation {
            name: "aggregate-reference-escape",
            source: "(#struct Holder (: view (#ref #u64)))
              (#fn bad () Holder
                (#let local #u64 7u64)
                (#return (#struct-literal Holder (: view (#borrow local)))))
              (#fn main () #u64
                (#let holder Holder (#call bad ()))
                (#return (#deref (#get holder view))))",
            conflict: "(#return (#struct-literal Holder (: view (#borrow local))))",
            conflict_occurrence: 0,
            origin: Some(("(#borrow local)", 0)),
        },
        Violation {
            name: "callee-stored-reference-retains-source-loan",
            source: include_str!("ui/callee-store-retained-borrow.lim"),
            conflict: "#set",
            conflict_occurrence: 0,
            origin: Some(("#borrow value", 0)),
        },
        Violation {
            name: "owner-move-while-borrowed",
            source: "(#struct Token (: value #u64)) (#linear Token)
              (#fn consume (: token Token) () (#forget token) (#return ()))
              (#fn main () ()
                (#let token Token (#struct-literal Token (: value 1u64)))
                (#let view (#ref Token) (#borrow token))
                (#call consume (: token token))
                (#drop view) (#return ()))",
            conflict: "token",
            conflict_occurrence: 5,
            origin: Some(("#borrow token", 0)),
        },
        Violation {
            name: "exclusive-internal-reference-blocks-owner-access",
            source: include_str!("ui/call-self-loan-owner-borrow.lim"),
            conflict: "running",
            conflict_occurrence: 1,
            origin: None,
        },
    ];

    for case in cases {
        assert_violation(case);
    }
}

#[test]
fn accepts_adversarial_non_aliasing_controls() {
    let accepted = [
        (
            "shared-shared",
            "(#fn main () #u64
               (#let owner #u64 9u64)
               (#let first (#ref #u64) (#borrow owner))
               (#let second (#ref #u64) (#borrow owner))
               (#let result #u64 (#u64.+.wrap (#deref first) (#deref second)))
               (#drop first) (#drop second) (#return result))",
        ),
        (
            "disjoint-fields",
            "(#struct Pair (: left #u64 : right #u64))
             (#fn main () #u64
               (#let-mut pair Pair (#struct-literal Pair (: left 1u64 : right 2u64)))
               (#let left (#ref-mut #u64) (#borrow-mut (#get pair left)))
               (#let right (#ref-mut #u64) (#borrow-mut (#get pair right)))
               (#deref-set left 40u64) (#deref-set right 2u64)
               (#drop left) (#drop right)
               (#return (#u64.+.wrap (#get pair left) (#get pair right))))",
        ),
    ];

    for (name, source) in accepted {
        compile(source, name).unwrap_or_else(|error| panic!("{name}: {error:?}"));
    }
}
