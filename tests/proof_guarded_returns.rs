use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("guarded-returns.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn contract_failure(source: &str, theorem: &str) {
    let error = check(source, theorem).expect_err("the guarded return claim must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::ContractFailure),
        "{error:?}"
    );
}

#[test]
fn boolean_selector_correlates_the_returned_reference_with_the_write_target() {
    proved(
        r#"
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#ref-mut #u8)
        (#return (#if condition left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let selected (#ref-mut #u8)
          (#call choose (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set selected 9u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-and
            (#proof-implies condition
              (#proof-eq (#get (#proof-result) 0) 9u8))
            (#proof-implies (#bool::not condition)
              (#proof-eq (#get (#proof-result) 1) 9u8))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn numeric_selector_correlates_branch_origin_without_assuming_numeric_outputs() {
    proved(
        r#"
      (#fn choose (: selector #u8 : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#ref-mut #u8)
        (#return (#if (#u8::eq selector 0u8) left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: selector #u8 : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let selected (#ref-mut #u8)
          (#call choose (: selector selector
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set selected 7u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-and
            (#proof-implies (#u8::eq selector 0u8)
              (#proof-eq (#get (#proof-result) 0) 7u8))
            (#proof-implies (#u8::ne selector 0u8)
              (#proof-eq (#get (#proof-result) 1) 7u8))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn selected_reference_inside_a_struct_keeps_its_branch_guard() {
    proved(
        r#"
      (#struct BorrowedPair () (: selected (#ref-mut #u8) : tag #u8))
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          BorrowedPair
        (#return (#struct-literal BorrowedPair
          (: selected (#if condition left right) : tag 3u8))))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let result BorrowedPair
          (#call choose (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set (#get result selected) 5u8)
        (#forget result)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-and
            (#proof-implies condition (#proof-eq (#get (#proof-result) 0) 5u8))
            (#proof-implies (#bool::not condition)
              (#proof-eq (#get (#proof-result) 1) 5u8))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn tuple_payload_keeps_each_conditional_reference_origin() {
    proved(
        r#"
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#tuple (#ref-mut #u8) (#ref-mut #u8))
        (#return (#if condition
          (#tuple (#tuple (#ref-mut #u8) (#ref-mut #u8)) left right)
          (#tuple (#tuple (#ref-mut #u8) (#ref-mut #u8)) right left))))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let pair (#tuple (#ref-mut #u8) (#ref-mut #u8))
          (#call choose (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set (#get pair 0) 4u8)
        (#deref-set (#get pair 1) 6u8)
        (#forget pair)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-implies condition
            (#proof-eq (#get (#proof-result) 0) 4u8)))))
    "#,
        "selected-contract",
    );
}

#[test]
fn array_payload_tracks_branch_selected_reference_slots() {
    proved(
        r#"
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#array (#ref-mut #u8) 2)
        (#return (#if condition
          (#array-of (#array (#ref-mut #u8) 2) left right)
          (#array-of (#array (#ref-mut #u8) 2) right left))))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let selected (#array (#ref-mut #u8) 2)
          (#call choose (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set (#index selected 0usize) 8u8)
        (#deref-set (#index selected 1usize) 2u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-implies condition
            (#proof-eq (#get (#proof-result) 0) 8u8)))))
    "#,
        "selected-contract",
    );
}

#[test]
fn enum_variant_and_payload_origin_remain_correlated() {
    proved(
        r#"
      (#enum Selection () (: Selection.None : Selection.Left (#ref-mut #u8)
        : Selection.Right (#ref-mut #u8)))
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          Selection
        (#return (#if condition
          (#enum-literal Selection.Left left)
          (#enum-literal Selection.Right right))))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#match (#call choose (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right)))
          (#case (Selection.Left target) (#deref-set target 3u8))
          (#case (Selection.Right target) (#deref-set target 6u8))
          (#case Selection.None ()))
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-and
            (#proof-implies condition (#proof-eq (#get (#proof-result) 0) 3u8))
            (#proof-implies (#bool::not condition)
              (#proof-eq (#get (#proof-result) 1) 6u8))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn input_enum_uses_only_the_active_reference_payload() {
    proved(
        r#"
      (#enum Source () (: Source.None : Source.Some (#ref-mut #u8)))
      (#fn unwrap (: source Source : fallback (#ref-mut #u8)) (#ref-mut #u8)
        (#return (#match source
          (#case Source.None fallback)
          (#case (Source.Some selected) selected))))
      (#theorem unwrap-contract (#proof-contract unwrap true true))
      (#fn caller (: present #bool : payload-input #u8 : fallback-input #u8)
          (#tuple #u8 #u8)
        (#let-mut payload #u8 payload-input)
        (#let-mut fallback #u8 fallback-input)
        (#let source Source
          (#if present
            (#enum-literal Source.Some (#borrow-mut payload))
            (#enum-literal Source.None)))
        (#let selected (#ref-mut #u8)
          (#call unwrap (: source source : fallback (#borrow-mut fallback))))
        (#deref-set selected 7u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) payload fallback)))
      (#theorem selected-contract (#proof-using (unwrap-contract)
        (#proof-contract caller true
          (#proof-and
            (#proof-implies present
              (#proof-eq (#get (#proof-result) 0) 7u8))
            (#proof-implies (#bool::not present)
              (#proof-eq (#get (#proof-result) 1) 7u8))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn transitive_checked_wrapper_preserves_the_selected_helper_origin() {
    proved(
        r#"
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#ref-mut #u8)
        (#return (#if condition left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn forward (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#ref-mut #u8)
        (#return (#call choose (: condition condition : left left : right right))))
      (#theorem forward-contract
        (#proof-using (choose-contract)
          (#proof-contract forward true true)))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let selected (#ref-mut #u8)
          (#call forward (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set selected 5u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (forward-contract)
        (#proof-contract caller true
          (#proof-implies condition
            (#proof-eq (#get (#proof-result) 0) 5u8)))))
    "#,
        "selected-contract",
    );
}

#[test]
fn mutable_return_changes_only_the_guard_selected_alias() {
    proved(
        r#"
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#ref-mut #u8)
        (#return (#if condition left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8)
          (#tuple #u8 #u8)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let selected (#ref-mut #u8)
          (#call choose (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set selected 11u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-and
            (#proof-implies condition
              (#proof-eq (#get (#proof-result) 1) (#proof-old right-input)))
            (#proof-implies (#bool::not condition)
              (#proof-eq (#get (#proof-result) 0) (#proof-old left-input)))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn identical_caller_arguments_may_share_the_selected_origin() {
    proved(
        r#"
      (#fn choose (: condition #bool : left (#ref #u8) : right (#ref #u8)) (#ref #u8)
        (#return (#if condition left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : input #u8) #u8
        (#let selected (#ref #u8)
          (#call choose (: condition condition : left (#borrow input) : right (#borrow input))))
        (#return (#deref selected)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) input))))
    "#,
        "selected-contract",
    );
}

#[test]
fn wrong_target_claim_and_its_negation_remain_unproved() {
    let source = r#"
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#ref-mut #u8)
        (#return (#if condition left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8) #u8
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let selected (#ref-mut #u8)
          (#call choose (: condition condition
            : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set selected 9u8)
        (#forget selected)
        (#return left))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-implies condition (#proof-eq (#proof-result) 8u8)))))
    "#;
    contract_failure(source, "selected-contract");

    let negated = source.replace(
        "(#proof-implies condition (#proof-eq (#proof-result) 8u8))",
        "(#proof-not (#proof-implies condition (#proof-eq (#proof-result) 9u8)))",
    );
    contract_failure(&negated, "selected-contract");
}

#[test]
fn shared_abstract_selector_choices_keep_complementary_results_correlated() {
    proved(
        r#"
      (#fn select-flag (: value #bool) #bool (#return value))
      (#theorem flag-contract (#proof-contract select-flag true true))
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#tuple (#ref-mut #u8) (#ref-mut #u8))
        (#let selected #bool (#call select-flag (: value condition)))
        (#return (#if selected
          (#tuple (#tuple (#ref-mut #u8) (#ref-mut #u8)) left right)
          (#tuple (#tuple (#ref-mut #u8) (#ref-mut #u8)) right left))))
      (#theorem choose-contract (#proof-using (flag-contract) (#proof-contract choose true true)))
      (#fn caller (: condition #bool) (#tuple #u8 #u8)
        (#let-mut left #u8 0u8)
        (#let-mut right #u8 0u8)
        (#let pair (#tuple (#ref-mut #u8) (#ref-mut #u8))
          (#call choose (: condition condition : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set (#get pair 0) 4u8)
        (#deref-set (#get pair 1) 6u8)
        (#forget pair)
        (#return (#tuple (#tuple #u8 #u8) left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-or
            (#proof-eq (#proof-result) (#tuple (#tuple #u8 #u8) 4u8 6u8))
            (#proof-eq (#proof-result) (#tuple (#tuple #u8 #u8) 6u8 4u8))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn repeated_calls_bind_their_own_computed_selector_values() {
    proved(
        r#"
      (#fn choose (: condition #bool : left (#ref #u8) : right (#ref #u8)) (#ref #u8)
        (#return (#if condition left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left #u8 : right #u8) (#tuple #u8 #u8)
        (#let first (#ref #u8) (#call choose (: condition condition : left (#borrow left) : right (#borrow right))))
        (#let second (#ref #u8) (#call choose (: condition (#bool::not condition) : left (#borrow left) : right (#borrow right))))
        (#return (#tuple (#tuple #u8 #u8) (#deref first) (#deref second))))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true (#proof-eq (#proof-result)
          (#tuple (#tuple #u8 #u8) (#if condition left right) (#if condition right left))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn inactive_nested_input_payloads_do_not_constrain_another_constructor() {
    proved(
        r#"
      (#struct Config () (: flag #bool))
      (#enum Source () (: Source.None : Source.Some Config))
      (#fn choose (: source Source : left (#ref #u8) : right (#ref #u8)) (#ref #u8)
        (#return (#match source
          (#case Source.None left)
          (#case (Source.Some config) (#if (#get config flag) left right)))))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: present #bool : flag #bool : left #u8 : right #u8) #u8
        (#let source Source (#if present
          (#enum-literal Source.Some (#struct-literal Config (: flag flag)))
          (#enum-literal Source.None)))
        (#let selected (#ref #u8) (#call choose (: source source : left (#borrow left) : right (#borrow right))))
        (#return (#deref selected)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true (#proof-eq (#proof-result)
          (#if (#bool::or (#bool::not present) flag) left right)))))
    "#,
        "selected-contract",
    );
}

#[test]
fn numeric_output_fields_still_require_an_explicit_contract_postcondition() {
    let source = r#"
      (#struct Selected () (: reference (#ref #u8) : tag #u8))
      (#fn choose (: source (#ref #u8)) Selected
        (#return (#struct-literal Selected (: reference source : tag 3u8))))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: input #u8) #u8
        (#let selected Selected (#call choose (: source (#borrow input))))
        (#let tag #u8 (#get selected tag))
        (#forget selected)
        (#return tag))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) 3u8))))
    "#;
    contract_failure(source, "selected-contract");
    proved(
        &source.replace("(#proof-using (choose-contract)", "(#proof-using ()"),
        "selected-contract",
    );
}

#[test]
fn mutating_reference_bearing_parents_keep_the_conservative_origin_model() {
    let source = r#"
      (#struct Holder () (: flag #bool : retained (#ref #u8)))
      (#fn choose (: holder (#ref-mut Holder) : condition #bool : left (#ref #u8) : right (#ref #u8)) (#ref #u8)
        (#deref-set (#borrow-mut (#get (#deref holder) flag)) false)
        (#return (#if condition left right)))
      (#theorem choose-contract (#proof-contract choose true true))
      (#fn caller (: condition #bool : left #u8 : right #u8) #u8
        (#let-mut holder Holder (#struct-literal Holder (: flag true : retained (#borrow left))))
        (#let selected (#ref #u8) (#call choose (: holder (#borrow-mut holder) : condition condition : left (#borrow left) : right (#borrow right))))
        (#let answer #u8 (#deref selected))
        (#forget selected)
        (#forget holder)
        (#return answer))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) (#if condition left right)))))
    "#;
    contract_failure(source, "selected-contract");
    proved(
        &source.replace("(#proof-using (choose-contract)", "(#proof-using ()"),
        "selected-contract",
    );
}

#[test]
fn mutable_scalar_selectors_are_bound_before_the_caller_frame_is_freshened() {
    proved(
        r#"
      (#fn choose (: flag (#ref-mut #bool) : left (#ref-mut #u8) : right (#ref-mut #u8)) (#ref-mut #u8)
        (#let before #bool (#deref flag))
        (#deref-set flag (#bool::not before))
        (#return (#if before left right)))
      (#theorem choose-contract (#proof-contract choose true
        (#proof-and
          (#proof-eq (#deref flag) (#bool::not (#proof-old (#deref flag))))
          (#proof-eq (#deref left) (#proof-old (#deref left)))
          (#proof-eq (#deref right) (#proof-old (#deref right))))))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8) (#tuple #bool #u8 #u8)
        (#let-mut flag #bool condition)
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let selected (#ref-mut #u8) (#call choose (: flag (#borrow-mut flag) : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set selected 9u8)
        (#forget selected)
        (#return (#tuple (#tuple #bool #u8 #u8) flag left right)))
      (#theorem selected-contract (#proof-using (choose-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#tuple (#tuple #bool #u8 #u8)
            (#bool::not condition) (#if condition 9u8 left-input) (#if condition right-input 9u8))))))
    "#,
        "selected-contract",
    );
}

#[test]
fn equal_array_contents_do_not_determine_a_dynamic_subobject_origin() {
    let source = r#"
      (#fn at (: values (#ref-mut (#array #u8 2)) : index #usize) (#ref-mut #u8)
        (#return (#borrow-mut (#index (#deref values) index))))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize)
        (#proof-eq (#deref (#proof-result)) (#index values index))))
      (#fn caller (: values (#ref-mut (#array #u8 2)) : index #usize) ()
        (#let selected (#ref-mut #u8) (#call at (: values values : index index)))
        (#deref-set selected 9u8)
        (#forget selected)
        (#return ()))
      (#theorem selected-contract (#proof-using (at-contract)
        (#proof-contract caller
          (#bool::and (#usize::lt index 2usize) (#u8::eq (#index values 0usize) (#index values 1usize)))
          (#proof-eq (#index values index) 9u8))))
    "#;
    contract_failure(source, "selected-contract");
    proved(
        &source.replace("(#proof-using (at-contract)", "(#proof-using ()"),
        "selected-contract",
    );
}

#[test]
fn guarded_selector_example_matches_native_for_every_byte_pair_and_both_selectors() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-guarded-return-native");
    let mut source = include_str!("../examples/proof_guarded_returns.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(r#"
      (#fn main () #u64
        (#let-mut left-index #u16 0u16)
        (#while (#u16::lt left-index 256u16)
          (#let-mut right-index #u16 0u16)
          (#while (#u16::lt right-index 256u16)
            (#let-mut selector #u8 0u8)
            (#while (#u8::lt selector 2u8)
              (#let condition #bool (#u8::eq selector 1u8))
              (#let-mut left #u8 (#as left-index #u8))
              (#let-mut right #u8 (#as right-index #u8))
              (#call update-choice (: condition condition : left (#borrow-mut left) : right (#borrow-mut right) : value 9u8))
              (#let expected-left #u8 (#if condition 9u8 (#as left-index #u8)))
              (#let expected-right #u8 (#if condition (#as right-index #u8) 9u8))
              (#if (#u8::ne left expected-left) (#block (#return 1u64)))
              (#if (#u8::ne right expected-right) (#block (#return 2u64)))
              (#set selector (#u8::add-wrap selector 1u8)))
            (#set right-index (#u16::add-wrap right-index 1u16)))
          (#set left-index (#u16::add-wrap left-index 1u16)))
        (#return 42u64))
    "#);
    let path = scratch.path().join("main.lim");
    let binary = scratch.path().join("main");
    fs::write(&path, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&path)
            .arg("-o")
            .arg(&binary)
            .env("PATH", ""),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) = support::run(
        Command::new(&binary).env("PATH", ""),
        Duration::from_secs(5),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}
