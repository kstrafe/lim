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
