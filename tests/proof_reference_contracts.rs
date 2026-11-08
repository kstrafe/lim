use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("reference-contracts.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn rejected(source: &str, theorem: &str) -> Diagnostic {
    check(source, theorem).expect_err("the reference contract claim must fail closed")
}

#[test]
fn mutable_identity_return_preserves_the_caller_alias() {
    proved(
        r#"
      (#fn identity (: source (#ref-mut #u8)) (#ref-mut #u8)
        (#return source))
      (#theorem identity-contract (#proof-contract identity true true))
      (#fn caller (: input #u8) #u8
        (#let-mut original #u8 input)
        (#let result (#ref-mut #u8)
          (#call identity (: source (#borrow-mut original))))
        (#deref-set result 9u8)
        (#forget result)
        (#return original))
      (#theorem caller-contract
        (#proof-using (identity-contract)
          (#proof-contract caller true
            (#proof-eq (#proof-result) 9u8))))
    "#,
        "caller-contract",
    );
}

#[test]
fn mutable_projected_reference_return_preserves_sibling_field() {
    proved(
        r#"
      (#struct Pair () (: first #u8 : second #u8))
      (#fn first-ref (: pair (#ref-mut Pair)) (#ref-mut #u8)
        (#return (#borrow-mut (#get (#deref pair) first))))
      (#theorem first-ref-contract (#proof-contract first-ref true true))
      (#fn caller (: input (#ref-mut Pair)) #u8
        (#let selected (#ref-mut #u8)
          (#call first-ref (: pair input)))
        (#deref-set selected 9u8)
        (#forget selected)
        (#return (#get input first)))
      (#theorem caller-contract
        (#proof-using (first-ref-contract)
          (#proof-contract caller true
            (#proof-and
              (#proof-eq (#proof-result) 9u8)
              (#proof-eq (#get input second) (#proof-old (#get input second)))))))
    "#,
        "caller-contract",
    );
}

#[test]
fn returned_reference_origin_flows_through_a_checked_caller() {
    proved(
        r#"
      (#fn identity (: source (#ref-mut #u8)) (#ref-mut #u8)
        (#return source))
      (#theorem identity-contract (#proof-contract identity true true))
      (#fn pass-through (: source (#ref-mut #u8)) (#ref-mut #u8)
        (#return (#call identity (: source source))))
      (#theorem pass-through-contract
        (#proof-using (identity-contract)
          (#proof-contract pass-through true true)))
      (#fn caller (: input #u8) #u8
        (#let-mut original #u8 input)
        (#let result (#ref-mut #u8)
          (#call pass-through (: source (#borrow-mut original))))
        (#deref-set result 9u8)
        (#forget result)
        (#return original))
      (#theorem caller-contract
        (#proof-using (pass-through-contract)
          (#proof-contract caller true (#proof-eq (#proof-result) 9u8))))
    "#,
        "caller-contract",
    );
}

#[test]
fn returned_shared_reference_reads_the_caller_referent() {
    proved(
        r#"
      (#fn identity (: source (#ref #u8)) (#ref #u8)
        (#return source))
      (#theorem identity-contract (#proof-contract identity true true))
      (#fn caller (: input #u8) #u8
        (#let result (#ref #u8) (#call identity (: source (#borrow input))))
        (#return (#deref result)))
      (#theorem caller-contract
        (#proof-using (identity-contract)
          (#proof-contract caller true (#proof-eq (#proof-result) input))))
    "#,
        "caller-contract",
    );
}

#[test]
fn pinned_reference_results_keep_the_stationary_caller_location() {
    proved(
        r#"
      (#struct Pair () (: first #u8 : second #u8))
      (#fn identity (: source (#pin-ref Pair)) (#pin-ref Pair) (#return source))
      (#theorem identity-contract (#proof-contract identity true true))
      (#fn caller (: input #u8) #u8
        (#let pair Pair (#struct-literal Pair (: first input : second 7u8)))
        (#let result (#pin-ref Pair) (#call identity (: source (#pin-borrow pair))))
        (#return (#get result first)))
      (#theorem selected (#proof-using (identity-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) input))))"#,
        "selected",
    );
}

#[test]
fn conditional_reference_summary_keeps_the_checked_selector_relation() {
    let source = r#"
      (#fn choose (: condition #bool : left (#ref-mut #u8) : right (#ref-mut #u8))
          (#ref-mut #u8)
        (#return (#if condition left right)))
      (#theorem weak (#proof-contract choose
        (#u8::eq (#deref left) (#deref right))
        (#proof-eq (#deref (#proof-result)) (#deref left))))
      (#fn caller (: condition #bool : left-input #u8 : right-input #u8) #u8
        (#let-mut left #u8 left-input)
        (#let-mut right #u8 right-input)
        (#let result (#ref-mut #u8)
          (#call choose
            (: condition condition : left (#borrow-mut left) : right (#borrow-mut right))))
        (#deref-set result 9u8)
        (#forget result)
        (#return left))
      (#theorem caller-contract
        (#proof-using (weak)
          (#proof-contract caller (#bool::and condition (#u8::eq left-input right-input))
            (#proof-eq (#proof-result) 9u8))))
    "#;
    proved(source, "caller-contract");
    proved(
        &source.replace("(#proof-using (weak)", "(#proof-using ()"),
        "caller-contract",
    );
    let mut negated = source.replace("(#proof-using (weak)", "(#proof-not (#proof-using (weak)");
    negated.push(')');
    assert_eq!(
        rejected(&negated, "caller-contract").proof_outcome(),
        Some(ProofOutcome::ContractFailure)
    );
}

#[test]
fn dynamic_array_origins_keep_every_possible_location_without_new_roots() {
    proved(
        r#"
      (#fn at (: values (#ref-mut (#array #u8 2)) : index #usize) (#ref-mut #u8)
        (#return (#borrow-mut (#index (#deref values) index))))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize)
        (#proof-eq (#deref (#proof-result)) (#index values index))))
      (#fn caller (: values (#ref-mut (#array #u8 2)) : index #usize) ()
        (#let result (#ref-mut #u8) (#call at (: values values : index index)))
        (#deref-set result 9u8) (#forget result) (#return ()))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller
          (#bool::and (#usize::lt index 2usize)
            (#u8::ne (#index values 0usize) (#index values 1usize)))
          (#proof-and
            (#proof-eq (#index values index) 9u8)
            (#proof-implies (#usize::ne index 0usize)
              (#proof-eq (#index values 0usize) (#proof-old (#index values 0usize))))
            (#proof-implies (#usize::ne index 1usize)
              (#proof-eq (#index values 1usize) (#proof-old (#index values 1usize))))))))"#,
        "selected",
    );
}

#[test]
fn reference_result_alternative_limits_cannot_be_negated_into_a_proof() {
    let ty = format!("(#tuple {})", vec!["(#ref #u8)"; 9].join(" "));
    for claim in [
        "(#proof-contract many true true)",
        "(#proof-not (#proof-contract many true true))",
    ] {
        let source = format!(
            r#"
          (#fn many ({parameters} : left (#ref #u8) : right (#ref #u8)) {ty}
            {selections}
            (#return (#tuple {ty} {values})))
          (#theorem many-contract (#proof-contract many true true))
          (#theorem selected (#proof-using (many-contract) {claim}))"#,
            parameters = (0..9)
                .map(|i| format!(": condition{i} #bool"))
                .collect::<Vec<_>>()
                .join(" "),
            selections = (0..9)
                .map(|i| format!("(#let selected{i} (#ref #u8) (#if condition{i} left right))"))
                .collect::<Vec<_>>()
                .join(" "),
            values = (0..9)
                .map(|i| format!("selected{i}"))
                .collect::<Vec<_>>()
                .join(" "),
        );
        let error = rejected(&source, "selected");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::ResourceLimit),
            "{error:?}"
        );
        assert!(
            error.message.contains("budget") || error.message.contains("alternatives"),
            "{}",
            error.message
        );
    }
}

#[test]
fn correlated_repeated_reference_slots_do_not_create_impossible_combinations() {
    let ty = format!("(#tuple {})", vec!["(#ref #u8)"; 9].join(" "));
    let source = format!(
        r#"
      (#fn many (: condition #bool : left (#ref #u8) : right (#ref #u8)) {ty}
        (#let selected (#ref #u8) (#if condition left right))
        (#return (#tuple {ty} {values})))
      (#theorem many-contract (#proof-contract many true true))
      (#theorem selected (#proof-using (many-contract) (#proof-contract many true true)))
    "#,
        values = vec!["selected"; 9].join(" ")
    );
    proved(&source, "selected");
}

#[test]
fn readonly_reference_bearing_pointees_keep_the_stored_reference_origin() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn load (: slot (#ref Slot)) (#ref #u8) (#return (#get slot reference)))
      (#theorem load-contract (#proof-contract load true true))
      (#fn caller (: input #u8) #u8
        (#let source Slot (#struct-literal Slot (: reference (#borrow input))))
        (#let result (#ref #u8) (#call load (: slot (#borrow source))))
        (#return (#deref result)))
      (#theorem selected (#proof-using (load-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) input))))"#,
        "selected",
    );
}

#[test]
fn a_mutating_callee_can_return_the_original_mutable_target() {
    proved(
        r#"
      (#fn increment (: value (#ref-mut #u8)) (#ref-mut #u8)
        (#deref-set value (#u8::add-wrap (#deref value) 1u8))
        (#return value))
      (#theorem increment-contract (#proof-contract increment true
        (#proof-eq (#deref value) (#u8::add-wrap (#proof-old (#deref value)) 1u8))))
      (#fn caller (: input #u8) #u8
        (#let-mut value #u8 input)
        (#let result (#ref-mut #u8) (#call increment (: value (#borrow-mut value))))
        (#deref-set result (#u8::add-wrap (#deref result) 1u8))
        (#forget result) (#return value))
      (#theorem selected (#proof-using (increment-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#u8::add-wrap input 2u8)))))"#,
        "selected",
    );
}

#[test]
fn returned_record_reference_and_char_fields_are_modeled_separately() {
    proved(
        r#"
      (#struct Borrowed () (: target (#ref-mut #u8) : marker #char))
      (#fn wrap (: source (#ref-mut #u8)) Borrowed
        (#return (#struct-literal Borrowed (: target source : marker #\x))))
      (#theorem wrap-contract (#proof-contract wrap true
        (#proof-eq (#get (#proof-result) marker) #\x)))
      (#fn caller (: input #u8) #u8
        (#let-mut value #u8 input)
        (#let wrapped Borrowed (#call wrap (: source (#borrow-mut value))))
        (#deref-set (#get wrapped target) 9u8)
        (#forget wrapped) (#return value))
      (#theorem selected (#proof-using (wrap-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) 9u8))))"#,
        "selected",
    );
}

#[test]
fn checked_discriminants_keep_an_always_absent_reference_absent() {
    proved(
        r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn none () Maybe (#return (#enum-literal Maybe.None)))
      (#theorem none-contract (#proof-contract none true true))
      (#fn caller () #u8
        (#return (#match (#call none ())
          (#case Maybe.None 9u8)
          (#case (Maybe.Some value) (#deref value)))))
      (#theorem selected (#proof-using (none-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) 9u8))))"#,
        "selected",
    );
}

#[test]
fn returned_enum_payload_references_alias_the_caller() {
    proved(
        r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref-mut #u8)))
      (#fn wrap (: source (#ref-mut #u8)) Maybe
        (#return (#enum-literal Maybe.Some source)))
      (#theorem wrap-contract (#proof-contract wrap true true))
      (#fn caller (: input #u8) #u8
        (#let-mut value #u8 input)
        (#match (#call wrap (: source (#borrow-mut value)))
          (#case Maybe.None ())
          (#case (Maybe.Some target) (#deref-set target 9u8)))
        (#return value))
      (#theorem selected (#proof-using (wrap-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) 9u8))))"#,
        "selected",
    );
}

#[test]
fn returned_reference_arrays_preserve_input_slot_correspondence() {
    proved(
        r#"
      (#fn identity (: sources (#array (#ref #u8) 2)) (#array (#ref #u8) 2)
        (#return sources))
      (#theorem identity-contract (#proof-contract identity true true))
      (#fn caller (: left #u8 : right #u8) (#tuple #u8 #u8)
        (#let sources (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let result (#array (#ref #u8) 2) (#call identity (: sources sources)))
        (#return (#tuple (#tuple #u8 #u8)
          (#deref (#index result 0usize)) (#deref (#index result 1usize)))))
      (#theorem selected (#proof-using (identity-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#tuple (#tuple #u8 #u8) left right)))))"#,
        "selected",
    );
}

#[test]
fn private_projected_origins_work_through_exported_facade_aliases() {
    use std::fs;
    let scratch = support::Scratch::new("proof-reference-private");
    let library = scratch.path().join("library");
    fs::create_dir(&library).unwrap();
    fs::write(
        library.join("impl.lim"),
        r#"
      (#struct Counter () (: current #u8 : private #u8))
      (#fn make (: initial #u8) Counter
        (#return (#struct-literal Counter (: current initial : private 7u8))))
      (#fn current (: counter (#ref Counter)) #u8 (#return (#get counter current)))
      (#fn current-ref (: counter (#ref-mut Counter)) (#ref-mut #u8)
        (#return (#borrow-mut (#get (#deref counter) current))))
      (#theorem current-ref-contract (#proof-contract current-ref true true))"#,
    )
    .unwrap();
    fs::write(
        library.join("lib.lim"),
        r#"
      (#export Counter make current current-ref current-ref-contract)
      (#alias Counter = ./impl.lim::Counter)
      (#alias make = ./impl.lim::make)
      (#alias current = ./impl.lim::current)
      (#alias current-ref = ./impl.lim::current-ref)
      (#alias current-ref-contract = ./impl.lim::current-ref-contract)"#,
    )
    .unwrap();
    let source = r#"
      (#alias Counter = ./library/lib.lim::Counter)
      (#alias make = ./library/lib.lim::make)
      (#alias current = ./library/lib.lim::current)
      (#alias current-ref = ./library/lib.lim::current-ref)
      (#alias current-ref-contract = ./library/lib.lim::current-ref-contract)
      (#fn caller (: input #u8) #u8
        (#let-mut counter Counter (#call make (: initial input)))
        (#let reference (#ref-mut #u8) (#call current-ref (: counter (#borrow-mut counter))))
        (#deref-set reference 9u8) (#forget reference)
        (#return (#call current (: counter (#borrow counter)))))
      (#theorem selected (#proof-using (current-ref-contract)
        (#proof-contract caller true (#proof-eq (#proof-result) 9u8))))"#;
    lim::check_theorem_details_from_path_with_config(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        "selected",
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
}

#[test]
fn reference_example_matches_native_for_every_byte() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-reference-native");
    let mut source = fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/proof_reference_contracts.lim"),
    )
    .unwrap();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(
        r#"
      (#fn main () #u64
        (#let-mut index #u16 0u16)
        (#while (#u16::lt index 256u16)
          (#let initial #u8 (#as index #u8))
          (#let-mut pair Pair (#struct-literal Pair (: current initial : untouched 7u8)))
          (#let actual #u8 (#call update (: pair (#borrow-mut pair))))
          (#if (#u8::ne actual (#u8::add-wrap initial 1u8)) (#block (#return 1u64)))
          (#if (#u8::ne (#get pair untouched) 7u8) (#block (#return 2u64)))
          (#set index (#u16::add-wrap index 1u16)))
        (#return 42u64))"#,
    );
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
