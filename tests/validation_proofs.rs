//! Storage-sensitive validation claims, independent of the implementation.
//! Every fixture first passes ordinary checking without its theorem.

const USER: &str = r#"
    (#struct User () (: ready #bool : data #u8))
    (#fn validate (: user (#ref User)) #bool (#return (#get user ready)))
    (#fn perform (: user (#ref User)) () (#return ()))
"#;
const CLAIM: &str = "(#proof-requires-validation entry (validate user) (perform user))";
const VALID_USER: &str = "(#struct-literal User (: ready true : data 0u8))";

fn ordinary(program: &str) {
    let parsed = lim::parse_program(program)
        .unwrap_or_else(|error| panic!("ordinary fixture must parse: {error}\n{program}"));
    lim::check_types(&parsed)
        .unwrap_or_else(|error| panic!("ordinary fixture must be safe: {error}\n{program}"));
}

fn check_claim(program: &str, claim: &str) -> Result<(), String> {
    ordinary(program);
    let source = format!("{program}\n(#theorem storage-validation {claim})");
    let parsed = lim::parse_program(&source)?;
    lim::check_types(&parsed)
}

fn proved(program: &str) {
    check_claim(program, CLAIM)
        .unwrap_or_else(|error| panic!("validation claim must hold: {error}\n{program}"));
}

fn disproved(program: &str) {
    let error = check_claim(program, CLAIM).expect_err("unsafe validation order was certified");
    assert!(
        error.starts_with("theorem '"),
        "not a theorem diagnostic: {error}"
    );
    assert!(
        error.contains("disproved"),
        "expected a semantic counterexample: {error}"
    );
}

fn with_entry(body: &str) -> String {
    format!("{USER}\n(#fn entry (: user (#ref User)) () {body} (#return ()))")
}

fn with_local(body: &str) -> String {
    format!(
        "{USER}\n(#fn entry () ()
      (#let-mut user User {VALID_USER})
      {body}
      (#forget user)
      (#return ()))"
    )
}

#[test]
fn true_guard_validates_the_exact_entry_input() {
    proved(&with_entry(
        "(#if (#call validate (: user user)) (#call perform (: user user)))",
    ));
}

#[test]
fn bypassing_the_validation_branch_is_disproved_even_if_validation_always_succeeds() {
    // User contents cannot rescue the unchecked flag=false path: this validator
    // returns true for every object, but must still actually complete first.
    let program = r#"
      (#struct User () (: ready #bool : data #u8))
      (#fn validate (: user (#ref User)) #bool (#return true))
      (#fn perform (: user (#ref User)) () (#return ()))
      (#fn entry (: user (#ref User) : flag #bool) ()
        (#if flag (#block
          (#let ignored #bool (#call validate (: user user)))
          ()))
        (#call perform (: user user))
        (#return ()))
    "#;
    disproved(program);
}

#[test]
fn zero_iteration_bypass_is_disproved_and_nontermination_exhausts_closed() {
    let program = format!(
        r#"{USER}
      (#fn entry (: user (#ref User) : flag #bool) ()
        (#while flag
          (#let ignored #bool (#call validate (: user user)))
          (#break))
        (#call perform (: user user))
        (#return ()))
    "#
    );
    // flag=false bypasses the only validation; flag=true runs the loop once.
    disproved(&program);

    let nonterminating = with_entry("(#loop (#continue))");
    let bounded = format!("(#proof-loop-limit 2 {CLAIM})");
    for claim in [bounded.clone(), format!("(#proof-not {bounded})")] {
        let error = check_claim(&nonterminating, &claim)
            .expect_err("nontermination must not become a proof or its negation");
        assert!(error.starts_with("theorem '"), "{error}");
        assert!(
            error.contains("unproved") && error.contains("loop"),
            "{error}"
        );
    }
}

#[test]
fn action_on_the_false_validation_branch_is_disproved() {
    disproved(&with_entry(
        "(#if (#bool::not (#call validate (: user user))) (#call perform (: user user)))",
    ));
}

#[test]
fn missing_validation_is_disproved() {
    disproved(&with_entry("(#call perform (: user user))"));
}

#[test]
fn later_validation_cannot_authorize_an_earlier_action() {
    disproved(&with_entry(
        r#"
      (#call perform (: user user))
      (#let valid #bool (#call validate (: user user)))
    "#,
    ));
}

#[test]
fn returning_early_on_failed_validation_protects_the_remaining_path() {
    proved(&with_entry(
        r#"
      (#if (#bool::not (#call validate (: user user))) (#block (#return ())))
      (#call perform (: user user))
    "#,
    ));
}

#[test]
fn unreachable_actions_do_not_require_a_validation() {
    proved(&with_entry("(#if false (#call perform (: user user)))"));
}

#[test]
fn validation_is_not_completed_while_its_body_calls_the_action() {
    let program = r#"
      (#struct User () (: ready #bool : data #u8))
      (#fn perform (: user (#ref User)) () (#return ()))
      (#fn validate (: user (#ref User)) #bool
        (#call perform (: user user))
        (#return (#get user ready)))
      (#fn entry (: user (#ref User)) ()
        (#let valid #bool (#call validate (: user user)))
        (#return ()))
    "#;
    disproved(program);
}

#[test]
fn validating_one_input_does_not_validate_another_input() {
    let program = format!(
        r#"{USER}
      (#fn entry (: first (#ref User) : second (#ref User)) ()
        (#if (#call validate (: user first)) (#call perform (: user second)))
        (#return ()))
    "#
    );
    disproved(&program);
}

#[test]
fn equal_values_in_distinct_objects_are_not_storage_identity() {
    let program = format!(
        r#"{USER}
      (#fn entry () ()
        (#let first User {VALID_USER})
        (#let second User {VALID_USER})
        (#if (#call validate (: user (#borrow first)))
          (#call perform (: user (#borrow second))))
        (#forget first)
        (#forget second)
        (#return ()))
    "#
    );
    disproved(&program);
}

#[test]
fn reborrowing_an_alias_preserves_the_validated_storage_identity() {
    proved(&with_entry(
        r#"
      (#let alias (#ref User) (#borrow (#deref user)))
      (#if (#call validate (: user alias)) (#call perform (: user user)))
      (#drop alias)
    "#,
    ));
}

#[test]
fn repeated_projection_borrows_identify_the_same_subobject() {
    let program = format!(
        r#"{USER}
      (#struct Envelope () (: child User : unrelated #u8))
      (#fn entry (: envelope (#ref Envelope)) ()
        (#if (#call validate (: user (#borrow (#get envelope child))))
          (#call perform (: user (#borrow (#get envelope child)))))
        (#return ()))
    "#
    );
    proved(&program);
}

#[test]
fn nested_helpers_preserve_completed_validation_and_action_identity() {
    let program = format!(
        r#"{USER}
      (#fn check-user (: candidate (#ref User)) #bool
        (#return (#call validate (: user candidate))))
      (#fn act-user (: candidate (#ref User)) ()
        (#call perform (: user candidate))
        (#return ()))
      (#fn entry (: user (#ref User)) ()
        (#if (#call check-user (: candidate user)) (#call act-user (: candidate user)))
        (#return ()))
    "#
    );
    proved(&program);
}

#[test]
fn overlapping_writes_invalidate_even_when_the_value_is_unchanged_or_restored() {
    for writes in [
        "(#set-field user data 1u8)",
        "(#set-field user data 0u8)",
        "(#set-field user data 1u8) (#set-field user data 0u8)",
    ] {
        let body = format!(
            r#"
          (#if (#call validate (: user (#borrow user)))
            (#block {writes} (#call perform (: user (#borrow user)))))
        "#
        );
        disproved(&with_local(&body));
    }
    let program = format!(
        r#"{}
      (#fn mutate (: target (#ref-mut User)) ()
        (#deref-set (#borrow-mut (#get target data)) 1u8)
        (#return ()))
    "#,
        with_local(
            r#"
      (#if (#call validate (: user (#borrow user)))
        (#block
          (#call mutate (: target (#borrow-mut user)))
          (#call perform (: user (#borrow user)))))
    "#
        )
    );
    disproved(&program);
}

#[test]
fn a_new_completed_true_validation_restores_authorization_after_a_write() {
    proved(&with_local(
        r#"
      (#let first-valid #bool (#call validate (: user (#borrow user))))
      (#set-field user data 1u8)
      (#if (#call validate (: user (#borrow user)))
        (#call perform (: user (#borrow user))))
    "#,
    ));
}

#[test]
fn a_disjoint_sibling_write_preserves_validation_of_the_child() {
    let program = format!(
        r#"{USER}
      (#struct Envelope () (: child User : unrelated #u8))
      (#fn entry () ()
        (#let-mut envelope Envelope
          (#struct-literal Envelope (: child {VALID_USER} : unrelated 0u8)))
        (#if (#call validate (: user (#borrow (#get envelope child))))
          (#block
            (#set-field envelope unrelated 1u8)
            (#call perform (: user (#borrow (#get envelope child))))))
        (#forget envelope)
        (#return ()))
    "#
    );
    proved(&program);
}

#[test]
fn writing_a_referenced_dependency_invalidates_the_containing_object() {
    let program = r#"
      (#struct View () (: dependency (#ref-mut #u8)))
      (#fn validate (: user (#ref View)) #bool
        (#return (#u8::eq (#deref (#get user dependency)) 0u8)))
      (#fn perform (: user (#ref View)) () (#return ()))
      (#fn entry () ()
        (#let-mut byte #u8 0u8)
        (#let-mut user View (#struct-literal View (: dependency (#borrow-mut byte))))
        (#if (#call validate (: user (#borrow user)))
          (#block
            (#deref-set (#get user dependency) 1u8)
            (#call perform (: user (#borrow user)))))
        (#forget user)
        (#return ()))
    "#;
    disproved(program);
}

#[test]
fn two_successful_validations_authorize_both_objects_independently() {
    let program = format!(
        r#"{USER}
      (#fn entry () ()
        (#let first User {VALID_USER})
        (#let second User {VALID_USER})
        (#let first-valid #bool (#call validate (: user (#borrow first))))
        (#let second-valid #bool (#call validate (: user (#borrow second))))
        (#if (#bool::and first-valid second-valid)
          (#block
            (#call perform (: user (#borrow first)))
            (#call perform (: user (#borrow second)))))
        (#forget first)
        (#forget second)
        (#return ()))
    "#
    );
    proved(&program);
}

fn false_second_validation(action: &str) -> String {
    format!(
        r#"{USER}
      (#fn entry () ()
        (#let first User {VALID_USER})
        (#let second User (#struct-literal User (: ready false : data 0u8)))
        (#let first-valid #bool (#call validate (: user (#borrow first))))
        (#let second-valid #bool (#call validate (: user (#borrow second))))
        (#call perform (: user (#borrow {action})))
        (#forget first)
        (#forget second)
        (#return ()))
    "#
    )
}

#[test]
fn a_false_second_validation_cannot_authorize_its_object() {
    disproved(&false_second_validation("second"));
    // A false result also revokes an earlier success on the same unchanged
    // storage. The validator's extra argument makes both results deterministic.
    let same_object = format!(
        r#"
      (#struct User () (: ready #bool : data #u8))
      (#fn validate (: user (#ref User) : accept #bool) #bool
        (#return (#bool::and accept (#get user ready))))
      (#fn perform (: user (#ref User)) () (#return ()))
      (#fn entry () ()
        (#let user User {VALID_USER})
        (#let first-valid #bool (#call validate (: user (#borrow user) : accept true)))
        (#let second-valid #bool (#call validate (: user (#borrow user) : accept false)))
        (#call perform (: user (#borrow user)))
        (#forget user)
        (#return ()))
    "#
    );
    disproved(&same_object);
}

#[test]
fn a_false_check_of_another_object_does_not_erase_the_first_validation() {
    proved(&false_second_validation("first"));
}

#[test]
fn ordinary_and_pinned_references_can_designate_the_same_storage() {
    let program = format!(
        r#"
      (#struct User () (: ready #bool : data #u8))
      (#fn validate (: user (#ref User)) #bool (#return (#get user ready)))
      (#fn perform (: user (#pin-ref User)) () (#return ()))
      (#fn entry () ()
        (#let user User {VALID_USER})
        (#if (#call validate (: user (#borrow user)))
          (#call perform (: user (#pin-borrow user))))
        (#forget user)
        (#return ()))
    "#
    );
    proved(&program);
}

#[test]
fn malformed_descriptors_and_unknown_labels_are_rejected() {
    let program = with_entry("()");
    for claim in [
        "(#proof-requires-validation entry (validate user))",
        "(#proof-requires-validation entry (validate user) (perform user) extra)",
        "(#proof-requires-validation entry validate (perform user))",
        "(#proof-requires-validation entry (validate) (perform user))",
        "(#proof-requires-validation entry (validate user extra) (perform user))",
        "(#proof-requires-validation entry (validate user) (perform))",
        "(#proof-requires-validation entry (validate missing) (perform user))",
        "(#proof-requires-validation entry (validate user) (perform missing))",
        "(#proof-requires-validation missing (validate user) (perform user))",
        "(#proof-requires-validation entry (missing user) (perform user))",
        "(#proof-requires-validation entry (validate user) (missing user))",
    ] {
        assert!(
            check_claim(&program, claim).is_err(),
            "accepted malformed claim: {claim}"
        );
    }
}

#[test]
fn descriptor_parameter_types_and_validator_result_are_checked() {
    // The action is unreachable in each fixture: descriptor typing is mandatory
    // independently of whether a counterexample path reaches that action.
    for program in [
        r#"
          (#fn validate (: user #bool) #bool (#return user))
          (#fn perform (: user #bool) () (#return ()))
          (#fn entry () () (#return ()))
        "#,
        r#"
          (#fn validate (: user (#ref #u8)) #u8 (#return (#deref user)))
          (#fn perform (: user (#ref #u8)) () (#return ()))
          (#fn entry () () (#return ()))
        "#,
        r#"
          (#fn validate (: user (#ref #u8)) #bool (#return true))
          (#fn perform (: user (#ref #u64)) () (#return ()))
          (#fn entry () () (#return ()))
        "#,
        r#"
          (#fn validate (: user (#ref #u8)) #bool (#return true))
          (#fn perform (: user #u8) () (#return ()))
          (#fn entry () () (#return ()))
        "#,
    ] {
        assert!(
            check_claim(program, CLAIM).is_err(),
            "accepted invalid descriptor types: {program}"
        );
    }
}

#[test]
fn negation_applies_to_the_completed_universal_validation_claim() {
    let negated = format!("(#proof-not {CLAIM})");
    // The unsafe program has an invalidating execution, so the negation of the
    // completed universal safety proposition holds.
    let unsafe_program = with_entry("(#call perform (: user user))");
    check_claim(&unsafe_program, &negated).unwrap();
    // The safe program satisfies the universal proposition; its negation fails.
    let safe_program =
        with_entry("(#if (#call validate (: user user)) (#call perform (: user user)))");
    let error = check_claim(&safe_program, &negated)
        .expect_err("negated true validation claim was accepted");
    assert!(error.starts_with("theorem '"), "{error}");
    assert!(error.contains("disproved"), "{error}");
}
