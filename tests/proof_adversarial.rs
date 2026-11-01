fn check(source: &str) -> Result<(), String> {
    let program = lim::parse_program(source)?;
    lim::check_types(&program)
}

fn reject(source: &str, expected: &str) {
    let error = check(source).expect_err("the claim must not be certified");
    assert!(error.contains(expected), "{error}");
}

#[test]
fn literals_must_fit_their_explicit_type() {
    for literal in ["256u8", "-1u8", "128i8", "-129i8"] {
        reject(
            &format!("(#theorem bad (#proof-eq {literal} 0u8))"),
            "out of range",
        );
    }
}

#[test]
fn equality_cannot_coerce_scalar_types() {
    reject("(#theorem bad (#proof-eq 1u8 1u64))", "incompatible types");
}

#[test]
fn native_arithmetic_spelling_rules_apply_in_proofs() {
    reject(
        "(#theorem bad (#proof-eq (#u8::add 1u8 2u8) 3u8))",
        "explicit",
    );
    reject(
        "(#theorem bad (#proof-eq (#u8::bit-and-wrap 1u8 2u8) 0u8))",
        "overflow mode",
    );
}

#[test]
fn a_statement_block_cannot_change_a_specification() {
    reject(
        "(#theorem bad (#proof-eq (#block (#let x #u8 0u8) x) 0u8))",
        "statement blocks",
    );
}

#[test]
fn self_is_not_a_transitive_call() {
    check(
        "(#fn main () #u64 (#return 0u64))
      (#theorem no-recursion (#proof-not (#proof-calls-transitively main main)))",
    )
    .unwrap();
}

#[test]
fn false_branch_guards_do_not_hide_a_counterexample() {
    reject(
        "(#theorem bad (#proof-for-all (: flag #bool)
        (#proof-implies true (#if flag false true))))",
        "disproved",
    );
}

#[test]
fn negated_vacuity_is_not_a_proof() {
    reject(
        "(#fn identity (: value #u8) #u8 (#return value))
      (#theorem bad (#proof-not (#proof-contract identity false false)))",
        "disproved",
    );
}

#[test]
fn signed_saturation_and_division_match_machine_semantics() {
    check(
        "(#theorem signed
      (#proof-and
        (#proof-eq (#i8::add-saturate 127i8 1i8) 127i8)
        (#proof-eq (#i8::sub-saturate -128i8 1i8) -128i8)
        (#proof-eq (#i8::div-wrap -128i8 -1i8) -128i8)
        (#proof-eq (#i8::div-saturate -128i8 -1i8) 127i8)))",
    )
    .unwrap();
    reject(
        "(#theorem bad (#proof-eq (#u8::div-wrap 1u8 0u8) 0u8))",
        "trap",
    );
}

#[test]
fn bounded_indexing_proves_every_valid_index() {
    check(
        "(#fn select (: index #usize) #u8
        (#let values (#array #u8 2) (#array-of (#array #u8 2) 7u8 7u8))
        (#return (#index values index)))
      (#theorem select-contract
        (#proof-contract select (#usize::lt index 2usize)
          (#proof-eq (#proof-result) 7u8)))",
    )
    .unwrap();
    reject(
        "(#fn select (: index #usize) #u8
        (#let values (#array #u8 2) (#array-of (#array #u8 2) 7u8 7u8))
        (#return (#index values index)))
      (#theorem invalid-index
        (#proof-contract select true (#proof-eq (#proof-result) 7u8)))",
        "bounds",
    );
}

#[test]
fn a_comparator_has_a_universal_strict_order_law() {
    check(
        "(#fn less (: left #u8 : right #u8) #bool
        (#return (#u8::lt left right)))
      (#theorem irreflexive (#proof-for-all (: value #u8)
        (#bool::not (#call less (: left value : right value)))))
      (#theorem asymmetric (#proof-for-all (: left #u8 : right #u8)
        (#proof-implies (#call less (: left left : right right))
          (#bool::not (#call less (: left right : right left))))))",
    )
    .unwrap();
}

#[test]
fn generated_result_of_a_sort_function_is_sorted_and_a_permutation() {
    check(
        "(#fn less (: left #u8 : right #u8) #bool
        (#return (#u8::lt left right)))
      (#fn sort-pair (: values (#array #u8 2)) (#array #u8 2)
        (#let first #u8 (#index values 0usize))
        (#let second #u8 (#index values 1usize))
        (#return (#if (#u8::lt second first)
          (#array-of (#array #u8 2) second first)
          (#array-of (#array #u8 2) first second))))
      (#theorem sort-correct
        (#proof-contract sort-pair true
          (#proof-and
            (#proof-sorted (#proof-result) less)
            (#proof-permutation (#proof-result) (#proof-old values)))))",
    )
    .unwrap();
}

#[test]
fn unknown_allowlist_members_cannot_be_trusted_silently() {
    reject(
        "(#fn identity () #u8 (#return 1u8))
      (#theorem bad (#proof-only-unsafe identity (#nonexistent)))",
        "unknown unsafe builtin",
    );
}

#[test]
fn empty_arrays_still_check_element_and_comparator_types() {
    reject(
        "(#fn less (: left #u64 : right #u64) #bool (#return (#u64::lt left right)))
      (#theorem bad (#proof-sorted (#array-of (#array #u8 0)) less))",
        "parameter types",
    );
    reject(
        "(#theorem bad (#proof-permutation (#array-of (#array #u8 0))
      (#array-of (#array #u64 0))))",
        "same element type",
    );
}

#[test]
fn cardinality_counters_cannot_wrap_for_large_explicit_arrays() {
    let left = std::iter::repeat_n("1u8", 256)
        .collect::<Vec<_>>()
        .join(" ");
    let right = std::iter::repeat_n("2u8", 256)
        .collect::<Vec<_>>()
        .join(" ");
    reject(
        &format!(
            "(#theorem bad (#proof-permutation
      (#array-of (#array #u8 256) {left})
      (#array-of (#array #u8 256) {right})))"
        ),
        "at most 64",
    );
}

#[test]
fn static_writes_are_unsafe_even_without_a_static_read() {
    reject(
        "(#static counter (#atomic #u8) (#atomic-init #u8 0u8))
      (#fn write () () (#unsafe (#atomic-store (#borrow counter) 1u8 #memory-relaxed)) (#return ()))
      (#theorem bad (#proof-no-effects write (#proof-unsafe)))",
        "disproved",
    );
    check(
        "(#static counter (#atomic #u8) (#atomic-init #u8 0u8))
      (#fn write () () (#unsafe (#atomic-store (#borrow counter) 1u8 #memory-relaxed)) (#return ()))
      (#theorem allowed (#proof-only-unsafe write (#static)))",
    )
    .unwrap();
}

#[test]
fn a_false_guard_cannot_lose_its_mutations() {
    reject(
        "(#fn changed (: input #bool) #u8
        (#let-mut value #u8 0u8)
        (#return (#match input
          (#case true (#when (#block (#set value 1u8) false)) 0u8)
          (#case _ value))))
      (#theorem bad (#proof-contract changed true (#proof-eq (#proof-result) 0u8)))",
        "match guards require pure",
    );
}

#[test]
fn a_pure_numeric_match_guard_is_modeled() {
    check(
        "(#fn choose (: input #u8) #u8
        (#return (#match input
          (#case 0u8 (#when (#u8::eq input 0u8)) 1u8)
          (#case _ 2u8))))
      (#theorem choose-contract (#proof-contract choose true
        (#proof-eq (#proof-result) (#if (#u8::eq input 0u8) 1u8 2u8))))",
    )
    .unwrap();
}

#[test]
fn initializing_an_owning_pin_writes_but_does_not_allocate() {
    let source = "(#unsafe-fn initialize (: pointer (#ptr-mut #u8) : value #u8) (#pin-own #u8)
      (#return (#unsafe (#pin-own-of pointer value))))";
    check(&format!(
        "{source} (#theorem no-allocation
      (#proof-no-effects initialize (#proof-allocation)))"
    ))
    .unwrap();
    for effect in ["#proof-mutation", "#proof-global-write"] {
        reject(
            &format!("{source} (#theorem bad (#proof-no-effects initialize ({effect})))"),
            "disproved",
        );
    }
}

#[test]
fn a_misspelled_invariant_label_is_not_silently_ignored() {
    reject(
        "(#fn identity (: value #u8) #u8 (#return value))
      (#theorem bad (#proof-with-invariants ((identity nonexistent false 0u8))
        (#proof-contract identity true true)))",
        "exactly one loop",
    );
}

#[test]
fn hidden_assembly_calls_cannot_establish_call_absence() {
    reject(
        "(#fn action () () (#return ()))
      (#fn opaque () #u8 (#return (#unsafe (#asm #u8 () \"mov rax, 0\"))))
      (#theorem bad (#proof-not (#proof-calls-transitively opaque action)))",
        "opaque execution",
    );
}

#[test]
fn deep_symbolic_evaluation_fails_with_a_budget_error() {
    for expression in [
        format!("{}true{}", "(#bool::not ".repeat(48), ")".repeat(48)),
        format!("{}true{}", "(#if true ".repeat(48), " false)".repeat(48)),
        format!("{}true{}", "(#proof-not ".repeat(48), ")".repeat(48)),
    ] {
        reject(
            &format!("(#theorem deep {expression})"),
            "evaluation nesting exceeds 32",
        );
    }
}

#[test]
fn proofs_do_not_accept_internal_unprefixed_operator_spellings() {
    reject(
        "(#theorem bad (#proof-eq (u8.+.wrap 1u8 2u8) 3u8))",
        "canonical # prefixed",
    );
}

#[test]
fn character_arithmetic_is_not_an_integer_operation() {
    reject(
        r"(#theorem bad (#proof-eq (#char::add-wrap #\a #\a) #\b))",
        "character operators",
    );
}

#[test]
fn proof_types_use_the_same_explicit_keyword_spelling_as_native_types() {
    reject(
        "(#theorem bad (#proof-for-all (: value u8) true))",
        "must use its '#' prefix",
    );
}

#[test]
fn aliases_remain_transparent_inside_reference_types() {
    check(
        "(#type Byte #u8)
      (#fn read (: value (#ref Byte)) Byte (#return (#deref value)))
      (#theorem read-contract (#proof-for-all (: input Byte)
        (#proof-eq (#call read (: value (#borrow input))) input)))",
    )
    .unwrap();
}
