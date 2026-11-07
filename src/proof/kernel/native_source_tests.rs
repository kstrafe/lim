use super::{DeclarationSource, Source};

fn theorem(name: &str, body: &str) -> String {
    format!(
        "(#theorem {name} (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof {body}))"
    )
}

#[test]
fn eager_and_source_check_accept_pure_definitions_and_theorems() {
    let source = format!(
        "(#math-definition zero () #pt-nat #pt-zero) {}",
        theorem("zero-reflexive", "(#pt-refl #pt-nat #pt-zero)")
    );
    let program = crate::parse_program(&source).unwrap();
    crate::check_types(&program).unwrap();
    Source::new(&source)
        .unwrap()
        .check(crate::ProofBudget::default())
        .unwrap();
}

#[test]
fn forward_references_and_mutual_inductives_follow_the_existing_schedule() {
    let forward = r#"
      (#math-definition use-later () #pt-nat (#pt-use later ()))
      (#math-definition later () #pt-nat #pt-zero)
      (#theorem early-proof (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-use later-proof ())))
      (#theorem later-proof (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#;
    Source::new(forward)
        .unwrap()
        .check(crate::ProofBudget::default())
        .unwrap();

    let mutual = r#"
      (#math-inductive left () () (#mutual left right) (#pt-type 0)
        ((wrap ((children (#pt-recur right ()))))))
      (#math-inductive right () () (#mutual left right) (#pt-type 0)
        ((back ((children (#pt-recur left ()))))))
    "#;
    Source::new(mutual)
        .unwrap()
        .check(crate::ProofBudget::default())
        .unwrap();
}

#[test]
fn ordinary_definition_cycles_are_rejected() {
    let source = r#"
      (#math-definition left () #pt-nat (#pt-use right ()))
      (#math-definition right () #pt-nat (#pt-use left ()))
    "#;
    assert!(Source::new(source)
        .unwrap()
        .check(crate::ProofBudget::default())
        .is_err());
}

#[test]
fn malformed_trailing_source_is_not_ignored_after_a_valid_theorem() {
    let source = format!(
        "{} (#theorem incomplete",
        theorem("valid", "(#pt-refl #pt-nat #pt-zero)")
    );
    assert!(Source::new(&source).is_err());
}

#[test]
fn source_rejects_non_mathematical_forms_instead_of_skipping_them() {
    let forms = [
        "(#fn main () #u64 (#return 0u64))",
        "(#import \"module\")",
        "(#generator generated () #u64)",
        "(#generate arbitrary (:))",
        "(#theorem procedural #pt-zero)",
        "(#alias x = ./other.lim::x)",
        "(#cfg linux (#math-definition x () #pt-nat #pt-zero))",
        "(#theorem t (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)) extra)",
    ];
    for form in forms {
        assert!(Source::new(form).is_err(), "accepted: {form}");
    }
}

#[test]
fn names_duplicates_spans_comments_and_unicode_are_preserved() {
    let source = "; λ comment\n(#math-definition café () #pt-nat #pt-zero)\n";
    let parsed = Source::new(source).unwrap();
    assert_eq!(parsed.len(), 1);
    assert_eq!(parsed.name(0), "café");
    assert_eq!(parsed.len(), 1);
    assert!(parsed.declaration(0).is_ok());
    let span = parsed.span(0);
    assert_eq!(span.start, source.find("(#math-definition").unwrap());
    assert_eq!(
        &source[span.start..span.end],
        "(#math-definition café () #pt-nat #pt-zero)"
    );
    assert!(parsed.item(0).is_ok());

    let duplicate =
        "(#math-definition same () #pt-nat #pt-zero) (#math-definition same () #pt-nat #pt-zero)";
    assert!(Source::new(duplicate).is_err());
}

#[test]
fn tiny_work_and_cumulative_budgets_fail_closed() {
    let source = theorem("refl", "(#pt-refl #pt-nat #pt-zero)");
    for budget in [
        crate::ProofBudget::new(1, 64 << 20, 256 << 20).unwrap(),
        crate::ProofBudget::new(100_000, 64 << 20, 1).unwrap(),
    ] {
        assert!(Source::new(&source).unwrap().check(budget).is_err());
    }
}

#[test]
fn selected_source_limits_reject_bytes_declarations_and_directory() {
    let source = theorem("a", "(#pt-refl #pt-nat #pt-zero)");
    let limits = crate::NativeProofLimits {
        max_bytes: source.len() - 1,
        ..Default::default()
    };
    assert!(Source::with_limits(&source, limits).is_err());
    let two = format!(
        "{} {}",
        theorem("a", "(#pt-refl #pt-nat #pt-zero)"),
        theorem("b", "(#pt-refl #pt-nat #pt-zero)")
    );
    let limits = crate::NativeProofLimits {
        max_declarations: 1,
        ..Default::default()
    };
    assert!(Source::with_limits(&two, limits).is_err());
    let limits = crate::NativeProofLimits {
        max_directory_bytes: 1,
        ..Default::default()
    };
    assert!(Source::with_limits(&source, limits).is_err());
    let late_bad = format!(
        "{} (#invalid)",
        theorem("first", "(#pt-refl #pt-nat #pt-zero)")
    );
    assert!(Source::with_limits(&late_bad, crate::NativeProofLimits::default()).is_err());
}

#[test]
fn actual_target_role_and_foundation_audit_match_eager_audit() {
    let source = r#"
      (#theorem actual-target (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#;
    let parsed = Source::new(source).unwrap();
    assert!(parsed.is_theorem("actual-target"));
    assert!(!parsed.is_theorem("missing"));

    let full = include_str!("../../../examples/proof_foundations.lim");
    let math = full.split("(#fn main").next().unwrap();
    let program = crate::parse_program(&math).unwrap();
    let expected =
        super::super::foundation_dependencies(&program, "proposition-extensionality").unwrap();
    let actual = Source::new(&math)
        .unwrap()
        .foundation_dependencies("proposition-extensionality")
        .unwrap();
    assert_eq!(actual, expected);
}
