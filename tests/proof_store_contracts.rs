use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("store-contracts.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn rejected(source: &str, theorem: &str) -> Diagnostic {
    check(source, theorem).expect_err("the stored-reference contract claim must fail closed")
}

#[test]
fn shared_reference_store_replaces_the_caller_visible_reference() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slot (#ref-mut Slot) : replacement (#ref #u8)) ()
        (#deref-set slot (#struct-literal Slot (: reference replacement))) (#return ()))
      (#theorem replace-contract (#proof-contract replace true true))
      (#fn caller (: old-input #u8 : replacement-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old-input))))
        (#call replace (: slot (#borrow-mut slot) : replacement (#borrow replacement-input)))
        (#return (#deref (#get slot reference))))
      (#theorem caller-contract
        (#proof-using (replace-contract)
          (#proof-contract caller true (#proof-eq (#proof-result) replacement-input))))
    "#,
        "caller-contract",
    );
}

#[test]
fn mutable_reference_store_updates_the_original_referent_by_alias() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref-mut #u8)))
      (#fn replace (: slot (#ref-mut Slot) : replacement (#ref-mut #u8)) ()
        (#deref-set slot (#struct-literal Slot (: reference replacement))) (#return ()))
      (#theorem replace-contract (#proof-contract replace true true))
      (#fn caller (: old-input #u8 : replacement-input #u8) #u8
        (#let-mut old-value #u8 old-input)
        (#let-mut replacement-value #u8 replacement-input)
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow-mut old-value))))
        (#call replace (: slot (#borrow-mut slot) : replacement (#borrow-mut replacement-value)))
        (#deref-set (#get slot reference) 9u8)
        (#forget slot)
        (#return replacement-value))
      (#theorem caller-contract
        (#proof-using (replace-contract)
          (#proof-contract caller true (#proof-eq (#proof-result) 9u8))))
    "#,
        "caller-contract",
    );
}

#[test]
fn stored_reference_replacement_flows_through_a_helper_contract() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slot (#ref-mut Slot) : replacement (#ref #u8)) ()
        (#deref-set slot (#struct-literal Slot (: reference replacement))) (#return ()))
      (#theorem replace-contract (#proof-contract replace true true))
      (#fn forward (: slot (#ref-mut Slot) : replacement (#ref #u8)) ()
        (#call replace (: slot slot : replacement replacement)) (#return ()))
      (#theorem forward-contract
        (#proof-using (replace-contract)
          (#proof-contract forward true true)))
      (#fn caller (: old-input #u8 : replacement-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old-input))))
        (#call forward (: slot (#borrow-mut slot) : replacement (#borrow replacement-input)))
        (#return (#deref (#get slot reference))))
      (#theorem caller-contract
        (#proof-using (forward-contract)
          (#proof-contract caller true (#proof-eq (#proof-result) replacement-input))))
    "#,
        "caller-contract",
    );
}

#[test]
fn whole_struct_replacement_preserves_an_explicit_readonly_sibling() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8) : tag #u8))
      (#fn replace (: slot (#ref-mut Slot) : replacement (#ref #u8)) ()
        (#deref-set slot (#struct-literal Slot
          (: reference replacement : tag (#get slot tag)))) (#return ()))
      (#theorem replace-contract
        (#proof-contract replace true
          (#proof-eq (#get slot tag) (#proof-old (#get slot tag)))))
      (#fn caller (: old-input #u8 : replacement-input #u8 : tag-input #u8) #u8
        (#let-mut slot Slot
          (#struct-literal Slot (: reference (#borrow old-input) : tag tag-input)))
        (#call replace (: slot (#borrow-mut slot) : replacement (#borrow replacement-input)))
        (#return (#get slot tag)))
      (#theorem caller-contract
        (#proof-using (replace-contract)
          (#proof-contract caller true (#proof-eq (#proof-result) tag-input))))
    "#,
        "caller-contract",
    );
}

#[test]
fn weak_conditional_store_does_not_choose_a_reference_target() {
    let source = r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slot (#ref-mut Slot) : condition #bool
          : left (#ref #u8) : right (#ref #u8)) ()
        (#deref-set slot (#struct-literal Slot
          (: reference (#if condition left right)))) (#return ()))
      (#theorem replace-contract (#proof-contract replace true true))
      (#fn caller (: condition #bool : old-input #u8 : replacement-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old-input))))
        (#call replace (: slot (#borrow-mut slot) : condition condition
          : left (#borrow old-input) : right (#borrow replacement-input)))
        (#return (#deref (#get slot reference))))
      (#theorem caller-contract
        (#proof-using (replace-contract)
          (#proof-contract caller true
            (#proof-eq (#proof-result) replacement-input))))
    "#;
    let error = rejected(source, "caller-contract");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::ContractFailure),
        "{error:?}"
    );
}

#[test]
fn a_swap_reads_both_reference_sources_from_call_entry() {
    proved(
        r#"
      (#struct Pair () (: first (#ref #u8) : second (#ref #u8)))
      (#fn swap (: pair (#ref-mut Pair)) ()
        (#let first (#ref #u8) (#get pair first))
        (#let second (#ref #u8) (#get pair second))
        (#deref-set pair (#struct-literal Pair (: first second : second first)))
        (#return ()))
      (#theorem swap-contract (#proof-contract swap true true))
      (#fn caller (: left #u8 : right #u8) (#tuple #u8 #u8)
        (#let-mut pair Pair (#struct-literal Pair (: first (#borrow left) : second (#borrow right))))
        (#call swap (: pair (#borrow-mut pair)))
        (#return (#tuple (#tuple #u8 #u8) (#deref (#get pair first)) (#deref (#get pair second)))))
      (#theorem selected (#proof-using (swap-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) (#tuple (#tuple #u8 #u8) right left)))))"#,
        "selected",
    );
}

#[test]
fn replacing_a_field_keeps_the_other_reference_identity() {
    proved(
        r#"
      (#struct Pair () (: first (#ref #u8) : second (#ref #u8)))
      (#fn replace (: pair (#ref-mut Pair) : replacement (#ref #u8)) ()
        (#deref-set (#borrow-mut (#get (#deref pair) first)) replacement)
        (#return ()))
      (#theorem replace-contract (#proof-contract replace true true))
      (#fn caller (: left #u8 : right #u8 : next #u8) (#tuple #u8 #u8)
        (#let-mut pair Pair (#struct-literal Pair (: first (#borrow left) : second (#borrow right))))
        (#call replace (: pair (#borrow-mut pair) : replacement (#borrow next)))
        (#return (#tuple (#tuple #u8 #u8) (#deref (#get pair first)) (#deref (#get pair second)))))
      (#theorem selected (#proof-using (replace-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) (#tuple (#tuple #u8 #u8) next right)))))"#,
        "selected",
    );
}

#[test]
fn a_replacement_can_return_the_retired_reference() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slot (#ref-mut Slot) : next (#ref #u8)) (#ref #u8)
        (#let previous (#ref #u8) (#get slot reference))
        (#deref-set slot (#struct-literal Slot (: reference next)))
        (#return previous))
      (#theorem replace-contract (#proof-contract replace true true))
      (#fn caller (: old #u8 : next #u8) (#tuple #u8 #u8)
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old))))
        (#let previous (#ref #u8) (#call replace (: slot (#borrow-mut slot) : next (#borrow next))))
        (#return (#tuple (#tuple #u8 #u8) (#deref previous) (#deref (#get slot reference)))))
      (#theorem selected (#proof-using (replace-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) (#tuple (#tuple #u8 #u8) old next)))))"#,
        "selected",
    );
}

#[test]
fn enum_reference_slots_can_be_cleared_and_populated() {
    proved(
        r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn clear (: slot (#ref-mut Maybe)) () (#deref-set slot (#enum-literal Maybe.None)) (#return ()))
      (#fn set (: slot (#ref-mut Maybe) : source (#ref #u8)) () (#deref-set slot (#enum-literal Maybe.Some source)) (#return ()))
      (#theorem clear-contract (#proof-contract clear true true))
      (#theorem set-contract (#proof-contract set true true))
      (#fn caller (: input #u8) #u8
        (#let-mut slot Maybe (#enum-literal Maybe.Some (#borrow input)))
        (#call clear (: slot (#borrow-mut slot)))
        (#call set (: slot (#borrow-mut slot) : source (#borrow input)))
        (#return (#match slot (#case Maybe.None 0u8) (#case (Maybe.Some source) (#deref source)))))
      (#theorem selected (#proof-using (clear-contract set-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) input))))"#,
        "selected",
    );
}

#[test]
fn a_conditional_store_retains_the_old_reference_alternative() {
    let prefix = r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slot (#ref-mut Slot) : condition #bool : replacement (#ref #u8)) ()
        (#if condition (#deref-set slot (#struct-literal Slot (: reference replacement))) ())
        (#return ()))
      (#theorem replace-contract (#proof-contract replace true true))
      (#fn caller (: condition #bool : old #u8 : next #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old))))
        (#call replace (: slot (#borrow-mut slot) : condition condition : replacement (#borrow next)))
        (#return (#deref (#get slot reference))))"#;
    proved(
        &format!(
            r#"{prefix}
      (#theorem selected (#proof-using (replace-contract) (#proof-contract caller true
        (#proof-or (#proof-eq (#proof-result) old) (#proof-eq (#proof-result) next)))))"#
        ),
        "selected",
    );
    for claim in [
        "(#proof-contract caller true (#proof-eq (#proof-result) next))",
        "(#proof-not (#proof-contract caller true (#proof-eq (#proof-result) next)))",
    ] {
        let source =
            format!("{prefix} (#theorem selected (#proof-using (replace-contract) {claim}))");
        assert_eq!(
            rejected(&source, "selected").proof_outcome(),
            Some(ProofOutcome::ContractFailure)
        );
    }
}
