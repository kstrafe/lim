use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("guarded-stores.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn contract_failure(source: &str, theorem: &str) {
    let error = check(source, theorem).expect_err("the stored-reference claim must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::ContractFailure),
        "{error:?}"
    );
}

#[test]
fn conditional_slot_store_proves_the_selected_reference_value() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : condition #bool : left (#ref #u8) : right (#ref #u8)) ()
        (#if condition
          (#deref-set slot (#struct-literal Slot (: reference left)))
          (#deref-set slot (#struct-literal Slot (: reference right))))
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow left-input))))
        (#call update (: slot (#borrow-mut slot) : condition condition
          : left (#borrow left-input) : right (#borrow right-input)))
        (#return (#deref (#get slot reference))))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#if condition left-input right-input)))))
    "#,
        "selected",
    );
}

#[test]
fn no_write_branch_preserves_the_old_reference_origin() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : condition #bool : next (#ref #u8)) ()
        (#if condition
          (#deref-set slot (#struct-literal Slot (: reference next)))
          ())
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: condition #bool : old-input #u8 : next-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old-input))))
        (#call update (: slot (#borrow-mut slot) : condition condition : next (#borrow next-input)))
        (#return (#deref (#get slot reference))))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#if condition next-input old-input)))))
    "#,
        "selected",
    );
}

#[test]
fn conditional_pair_swap_keeps_both_field_origins_correlated() {
    proved(
        r#"
      (#struct Pair () (: first (#ref #u8) : second (#ref #u8)))
      (#fn update (: pair (#ref-mut Pair) : condition #bool) ()
        (#let first (#ref #u8) (#get pair first))
        (#let second (#ref #u8) (#get pair second))
        (#if condition
          (#deref-set pair (#struct-literal Pair (: first second : second first)))
          ())
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: condition #bool : left #u8 : right #u8) (#tuple #u8 #u8)
        (#let-mut pair Pair (#struct-literal Pair
          (: first (#borrow left) : second (#borrow right))))
        (#call update (: pair (#borrow-mut pair) : condition condition))
        (#return (#tuple (#tuple #u8 #u8)
          (#deref (#get pair first)) (#deref (#get pair second)))))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result)
            (#if condition
              (#tuple (#tuple #u8 #u8) right left)
              (#tuple (#tuple #u8 #u8) left right))))))
    "#,
        "selected",
    );
}

#[test]
fn enum_constructor_and_reference_payload_follow_the_same_condition() {
    proved(
        r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn update (: slot (#ref-mut Maybe) : condition #bool : next (#ref #u8)) ()
        (#if condition
          (#deref-set slot (#enum-literal Maybe.Some next))
          (#deref-set slot (#enum-literal Maybe.None)))
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: condition #bool : old-input #u8 : next-input #u8) #u8
        (#let-mut slot Maybe (#enum-literal Maybe.Some (#borrow old-input)))
        (#call update (: slot (#borrow-mut slot) : condition condition : next (#borrow next-input)))
        (#return (#match slot
          (#case Maybe.None 0u8)
          (#case (Maybe.Some selected) (#deref selected)))))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#if condition next-input 0u8)))))
    "#,
        "selected",
    );
}

#[test]
fn transitive_summary_preserves_the_conditional_store_guard() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : condition #bool : next (#ref #u8)) ()
        (#if condition
          (#deref-set slot (#struct-literal Slot (: reference next)))
          ())
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn forward (: slot (#ref-mut Slot) : condition #bool : next (#ref #u8)) ()
        (#call update (: slot slot : condition condition : next next))
        (#return ()))
      (#theorem forward-contract
        (#proof-using (update-contract) (#proof-contract forward true true)))
      (#fn caller (: condition #bool : old-input #u8 : next-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old-input))))
        (#call forward (: slot (#borrow-mut slot) : condition condition : next (#borrow next-input)))
        (#return (#deref (#get slot reference))))
      (#theorem selected (#proof-using (forward-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#if condition next-input old-input)))))
    "#,
        "selected",
    );
}

#[test]
fn replacing_a_slot_returns_its_retired_reference_with_matching_state() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : condition #bool : next (#ref #u8)) (#ref #u8)
        (#let previous (#ref #u8) (#get slot reference))
        (#if condition
          (#deref-set slot (#struct-literal Slot (: reference next)))
          ())
        (#return previous))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: condition #bool : old-input #u8 : next-input #u8)
          (#tuple #u8 #u8)
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old-input))))
        (#let previous (#ref #u8)
          (#call update (: slot (#borrow-mut slot) : condition condition : next (#borrow next-input))))
        (#return (#tuple (#tuple #u8 #u8)
          (#deref previous) (#deref (#get slot reference)))))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result)
            (#if condition
              (#tuple (#tuple #u8 #u8) old-input next-input)
              (#tuple (#tuple #u8 #u8) old-input old-input))))))
    "#,
        "selected",
    );
}

#[test]
fn constant_array_element_store_preserves_the_other_element() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : next (#ref #u8)) ()
        (#deref-set slot (#struct-literal Slot (: reference next)))
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : next (#ref #u8)) ()
        (#call update (: slot (#borrow-mut (#index (#deref slots) 0usize)) : next next))
        (#return ()))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true
          (#proof-and
            (#proof-eq (#deref (#get (#index (#deref slots) 0usize) reference)) (#deref next))
            (#proof-eq (#deref (#get (#index (#deref slots) 1usize) reference))
              (#proof-old (#deref (#get (#index (#deref slots) 1usize) reference))))))))
    "#,
        "selected",
    );
}

#[test]
fn symbolic_array_element_store_respects_bounds_and_preserves_siblings() {
    let source = r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : next (#ref #u8)) ()
        (#deref-set slot (#struct-literal Slot (: reference next)))
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : index #usize : next (#ref #u8)) ()
        (#call update (: slot (#borrow-mut (#index (#deref slots) index)) : next next))
        (#return ()))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-and
            (#proof-eq (#deref (#get (#index (#deref slots) index) reference)) (#deref next))
            (#proof-implies (#usize::ne index 0usize)
              (#proof-eq (#deref (#get (#index (#deref slots) 0usize) reference))
                (#proof-old (#deref (#get (#index (#deref slots) 0usize) reference)))))
            (#proof-implies (#usize::ne index 1usize)
              (#proof-eq (#deref (#get (#index (#deref slots) 1usize) reference))
                (#proof-old (#deref (#get (#index (#deref slots) 1usize) reference)))))))))
    "#;
    proved(source, "selected");
    let mut negated = source.replace(
        "(#proof-contract caller (#usize::lt index 2usize)",
        "(#proof-not (#proof-contract caller (#usize::lt index 2usize)",
    );
    let end = negated.rfind(')').unwrap();
    negated.insert(end, ')');
    contract_failure(&negated, "selected");
}

#[test]
fn incorrect_conditional_store_claim_and_its_negation_fail_closed() {
    let source = r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : condition #bool : next (#ref #u8)) ()
        (#if condition
          (#deref-set slot (#struct-literal Slot (: reference next)))
          ())
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: condition #bool : old-input #u8 : next-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow old-input))))
        (#call update (: slot (#borrow-mut slot) : condition condition : next (#borrow next-input)))
        (#return (#deref (#get slot reference))))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true
          (#proof-implies condition (#proof-eq (#proof-result) old-input)))))
    "#;
    contract_failure(source, "selected");

    let negated = source.replace(
        "(#proof-implies condition (#proof-eq (#proof-result) old-input))",
        "(#proof-not (#proof-eq (#proof-result) (#if condition next-input old-input)))",
    );
    contract_failure(&negated, "selected");
}

#[test]
fn numeric_fields_stay_unconstrained_until_the_provider_contract_names_them() {
    let unconstrained = r#"
      (#struct Slot () (: reference (#ref #u8) : tag #u8))
      (#fn update (: slot (#ref-mut Slot) : next (#ref #u8) : tag #u8) ()
        (#deref-set slot (#struct-literal Slot (: reference next : tag tag)))
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: old-input #u8 : next-input #u8 : tag-input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot
          (: reference (#borrow old-input) : tag tag-input)))
        (#call update (: slot (#borrow-mut slot) : next (#borrow next-input) : tag 9u8))
        (#return (#get slot tag)))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) 9u8))))
    "#;
    contract_failure(unconstrained, "selected");

    let constrained = unconstrained.replace(
        "(#proof-contract update true true)",
        "(#proof-contract update true (#proof-eq (#get slot tag) tag))",
    );
    proved(&constrained, "selected");
}

#[test]
fn aliased_reference_inputs_remain_sound_under_a_conditional_store() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn update (: slot (#ref-mut Slot) : condition #bool : left (#ref #u8) : right (#ref #u8)) ()
        (#if condition
          (#deref-set slot (#struct-literal Slot (: reference left)))
          (#deref-set slot (#struct-literal Slot (: reference right))))
        (#return ()))
      (#theorem update-contract (#proof-contract update true true))
      (#fn caller (: condition #bool : input #u8) #u8
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow input))))
        (#call update (: slot (#borrow-mut slot) : condition condition
          : left (#borrow input) : right (#borrow input)))
        (#return (#deref (#get slot reference))))
      (#theorem selected (#proof-using (update-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) input))))
    "#,
        "selected",
    );
}

#[test]
fn conditional_store_example_matches_native_for_every_byte_pair_and_both_branches() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-guarded-store-native");
    let mut source = include_str!("../examples/proof_guarded_stores.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(r#"
      (#fn main () #u64
        (#let-mut old-index #u16 0u16)
        (#while (#u16::lt old-index 256u16)
          (#let-mut next-index #u16 0u16)
          (#while (#u16::lt next-index 256u16)
            (#let-mut selector #u8 0u8)
            (#while (#u8::lt selector 2u8)
              (#let replace #bool (#u8::eq selector 1u8))
              (#let previous #u8 (#as old-index #u8))
              (#let next #u8 (#as next-index #u8))
              (#let actual #u8 (#call read-updated (: replace replace : previous previous : next next)))
              (#let expected #u8 (#if replace next previous))
              (#if (#u8::ne actual expected) (#block (#return 1u64)))
              (#set selector (#u8::add-wrap selector 1u8)))
            (#set next-index (#u16::add-wrap next-index 1u16)))
          (#set old-index (#u16::add-wrap old-index 1u16)))
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
