fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}
const SCALAR: &str = r#"
#fn below-100 ((value #u64)) #bool (#return (#u64::lt value 100u64))
#fn consume ((value #u64)) ()
    (#requires (#call below-100 ((value value))))
    (#return ())
"#;

const PROVEN_READ: &str = r#"
#fn read ((values (#ref (#array #u64 4))) (index #usize)) #u64
    (#requires (#usize::lt index 4usize))
    (#return (#index-proven values index))
"#;

#[test]
fn explicit_index_proof_helper_satisfies_assignment_and_access() {
    check(include_str!("../examples/index_contracts.lim")).unwrap();
    let missing = include_str!("../examples/index_contracts.lim")
        .replace("          (#call widen-to-four ((index index)))\n", "");
    assert!(check(&missing).unwrap_err().contains("missing evidence"));
}

#[test]
fn proven_index_requires_evidence_even_without_other_contract_forms() {
    let source = "#fn read ((values (#ref (#array #u64 4))) (index #usize)) #u64 (#return (#index-proven values index))\n";
    assert!(check(source).unwrap_err().contains("missing evidence"));
}

#[test]
fn proven_index_keeps_linear_element_and_exclusive_borrow_rules() {
    let moved = r#"#struct Resource (#linear) ((value #u64))
#fn take ((values (#ref (#array Resource 4))) (index #usize)) Resource
          (#requires (#usize::lt index 4usize)) (#return (#index-proven values index))
"#;
    assert!(check(moved).is_err());
    let aliased = r#"#fn edit ((values (#ref-mut (#array #u64 4))) (index #usize)) ()
        (#requires (#usize::lt index 4usize))
        (#let first (#ref-mut #u64) (#borrow-mut (#index-proven values index)))
        (#let second (#ref-mut #u64) (#borrow-mut (#index-proven values index)))
        (#deref-set first 1u64) (#deref-set second 2u64) (#return ())
"#;
    let error = check(aliased).unwrap_err();
    assert!(!error.contains("missing evidence"), "{error}");
}

#[test]
fn direct_comparison_validation_can_supply_exact_index_bound() {
    let source = format!("{PROVEN_READ}\n#fn use ((values (#ref (#array #u64 4))) (index #usize)) #u64 (#return (#if-valid (#usize::lt index 4usize) (#call read ((values values) (index index))) 0u64))\n");
    check(&source).unwrap();
    for weaker in [
        "(#usize::lt index 2usize)",
        "(#usize::lt index 8usize)",
        "(#usize::le index 4usize)",
    ] {
        let bad = source.replace(
            "#if-valid (#usize::lt index 4usize)",
            &format!("#if-valid {weaker}"),
        );
        assert!(
            check(&bad).unwrap_err().contains("missing evidence"),
            "{bad}"
        );
    }
    assert!(check(&source.replace("#if-valid", "#if"))
        .unwrap_err()
        .contains("missing evidence"));
}

#[test]
fn proven_index_does_not_translate_a_named_predicate_body() {
    let source = format!("{PROVEN_READ}\n#fn within ((index #usize)) #bool (#return (#usize::lt index 4usize))\n#fn use ((values (#ref (#array #u64 4))) (index #usize)) #u64 (#return (#if-valid (#call within ((index index))) (#call read ((values values) (index index))) 0u64))\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}

#[test]
fn comparison_evidence_is_bound_to_the_checked_index() {
    let source = format!("{PROVEN_READ}\n#fn use ((values (#ref (#array #u64 4))) (index #usize) (other #usize)) #u64 (#return (#if-valid (#usize::lt index 4usize) (#call read ((values values) (index other))) 0u64))\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}

#[test]
fn primitive_claims_require_explicit_implication_helpers() {
    let source = r#"
#fn consume ((value #u64)) () (#requires (#u64::gt value 0u64)) (#return ())
#fn weaken ((value #u64)) () (#requires (#u64::gt value 1u64)) (#ensures (#u64::gt value 0u64)) (#return ())
#fn use ((value #u64)) ()
          (#if-valid (#u64::gt value 1u64) (#block (#call weaken ((value value))) (#call consume ((value value)))))
          (#return ())
"#;
    check(source).unwrap();
    assert!(check(&source.replace("(#call weaken ((value value)))", ""))
        .unwrap_err()
        .contains("missing evidence"));
}

#[test]
fn primitive_contracts_can_relate_two_runtime_inputs() {
    let source = r#"
#fn consume ((value #usize) (bound #usize)) () (#requires (#usize::lt value bound)) (#return ())
#fn use ((value #usize) (bound #usize) (other #usize)) ()
          (#if-valid (#usize::lt value bound) (#call consume ((value value) (bound bound))))
          (#return ())
"#;
    check(source).unwrap();
    assert!(check(&source.replace("(bound bound)", "(bound other)"))
        .unwrap_err()
        .contains("missing evidence"));
}

#[test]
fn changing_an_index_revokes_its_bounds_evidence() {
    let source = format!("{PROVEN_READ}\n#fn use ((values (#ref (#array #u64 4))) (input #usize)) #u64 (#let-mut index #usize input) (#return (#if-valid (#usize::lt index 4usize) (#block (#set index 99usize) (#call read ((values values) (index index)))) 0u64))\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
    let saved = format!("{PROVEN_READ}\n#fn use ((values (#ref (#array #u64 4))) (input #usize)) #u64 (#let-mut index #usize input) (#let valid #bool (#usize::lt index 4usize)) (#set index 99usize) (#return (#if-valid valid (#call read ((values values) (index index))) 0u64))\n");
    assert!(check(&saved).unwrap_err().contains("missing evidence"));
}

#[test]
fn explicit_assumptions_can_supply_primitive_bounds() {
    check("#fn read ((values (#ref (#array #u64 4))) (index #usize)) #u64 (#assume (#usize::lt index 4usize)) (#return (#index-proven values index))\n").unwrap();
}

#[test]
fn comparison_contract_arity_and_types_are_checked_even_in_assumptions() {
    for expression in ["(#usize::lt value)", "(#usize::lt value false)"] {
        let source = format!("#fn use ((value #usize)) () (#assume {expression}) (#return ())\n");
        assert!(check(&source).is_err());
    }
}

#[test]
fn adding_proven_index_to_an_unannotated_ast_cannot_bypass_checking() {
    let mut program = lim::parse_program("#fn read ((values (#ref (#array #u64 4))) (index #usize)) #u64 (#return (#index values index))\n").unwrap();
    let lim::Item::Function(function) = &mut program.items[0] else {
        panic!()
    };
    let lim::Statement::Return(Some(lim::Expr::List(parts))) = &mut function.body[0] else {
        panic!()
    };
    parts[0] = lim::Expr::Symbol("index-proven".into());
    assert!(lim::check_types(&program).unwrap_err().contains("metadata"));
}
#[test]
fn required_evidence_is_mandatory() {
    let error = check(&format!(
        "{SCALAR}\n#fn use ((input #u64)) () (#call consume ((value input))) (#return ())\n"
    ))
    .unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}
#[test]
fn validation_branch_supplies_evidence() {
    check(&format!("{SCALAR}\n#fn use ((input #u64)) () (#if-valid (#call below-100 ((value input))) (#call consume ((value input)))) (#return ())\n")).unwrap();
}
#[test]
fn ordinary_branch_does_not_implicitly_validate() {
    assert!(check(&format!("{SCALAR}\n#fn use ((input #u64)) () (#if (#call below-100 ((value input))) (#call consume ((value input)))) (#return ())\n")).is_err());
}
#[test]
fn assumed_evidence_satisfies_requirement() {
    check(&format!("{SCALAR}\n#fn use ((input #u64)) () (#assume (#call below-100 ((value input)))) (#call consume ((value input))) (#return ())\n")).unwrap();
}
#[test]
fn evidence_does_not_cross_subjects() {
    assert!(check(&format!("{SCALAR}\n#fn use ((input #u64) (other #u64)) () (#if-valid (#call below-100 ((value input))) (#call consume ((value other)))) (#return ())\n")).is_err());
}
#[test]
fn intermediary_explicitly_forwards_requirement() {
    check(&format!("{SCALAR}\n#fn use ((input #u64)) () (#requires (#call below-100 ((value input)))) (#call consume ((value input))) (#return ())\n")).unwrap();
}
#[test]
fn unconditional_postcondition_establishes_result() {
    check(&format!("{SCALAR}\n#fn produce () #u64 (#ensures (#call below-100 ((value (#result))))) (#return 42u64)\n#fn use () () (#let value #u64 (#call produce ())) (#call consume ((value value))) (#return ())\n")).unwrap();
}
#[test]
fn forgotten_branch_evidence_is_not_available_after_join() {
    assert!(check(&format!("{SCALAR}\n#fn use ((input #u64)) () (#if-valid (#call below-100 ((value input))) ()) (#call consume ((value input))) (#return ())\n")).is_err());
}
#[test]
fn malformed_predicate_rejected_even_in_assume() {
    let error=check("#fn number () #u64 (#return 1u64)\n#fn use () () (#assume (#call number ())) (#return ())\n").unwrap_err();
    assert!(error.contains("#bool"), "{error}");
}
#[test]
fn assumptions_reject_transitively_mutating_predicates_and_observations() {
    let declarations = r#"
#fn write ((value (#ref-mut #u64))) #u64 (#deref-set value 200u64) (#return 0u64)
#fn hidden-write ((value (#ref-mut #u64))) #bool (#let ignored #u64 (#call write ((value value)))) (#return true)
#fn positive ((value #u64)) #bool (#return (#u64::gt value 0u64))
    "#;
    for predicate in [
        "(#call hidden-write ((value value)))",
        "(#call positive ((value (#call write ((value value))))))",
    ] {
        let error = check(&format!("{declarations}\n#fn use ((value (#ref-mut #u64))) () (#assume {predicate}) (#return ())\n")).unwrap_err();
        assert!(error.contains("pure"), "{error}");
    }
}
#[test]
fn retired_theorem_syntax_is_rejected() {
    let error = lim::parse_program("#theorem retired true").unwrap_err();
    assert!(error.contains("removed"), "{error}");
}
const REFERENT: &str = r#"
#struct Packet () ((body #u64) (tag #u64))
#fn acceptable ((packet (#ref Packet))) #bool (#return (#u64::lt (#get packet body) 100u64))
#fn send ((packet (#ref Packet))) () (#requires (#call acceptable ((packet packet)))) (#return ())
#fn relabel ((packet (#ref-mut Packet))) () (#deref-set (#borrow-mut (#get packet tag)) 7u64) (#return ())
#fn replace ((packet (#ref-mut Packet))) () (#deref-set (#borrow-mut (#get packet body)) 200u64) (#return ())
#fn shrink ((packet (#ref-mut Packet))) () (#preserves (#call acceptable ((packet packet)))) (#deref-set (#borrow-mut (#get packet body)) 1u64) (#return ())
"#;
#[test]
fn unrelated_field_write_preserves_evidence() {
    check(&format!("{REFERENT}\n#fn use () () (#let-mut packet Packet (#struct-literal Packet ((body 2u64) (tag 0u64)))) (#if-valid (#call acceptable ((packet (#borrow packet)))) (#block (#call relabel ((packet (#borrow-mut packet)))) (#call send ((packet (#borrow packet)))))) (#forget packet) (#return ())\n")).unwrap();
}
#[test]
fn dependency_write_revokes_evidence() {
    assert!(check(&format!("{REFERENT}\n#fn use () () (#let-mut packet Packet (#struct-literal Packet ((body 2u64) (tag 0u64)))) (#if-valid (#call acceptable ((packet (#borrow packet)))) (#block (#call replace ((packet (#borrow-mut packet)))) (#call send ((packet (#borrow packet)))))) (#forget packet) (#return ())\n")).is_err());
}
#[test]
fn declared_preservation_renews_evidence() {
    check(&format!("{REFERENT}\n#fn use () () (#let-mut packet Packet (#struct-literal Packet ((body 2u64) (tag 0u64)))) (#if-valid (#call acceptable ((packet (#borrow packet)))) (#block (#call shrink ((packet (#borrow-mut packet)))) (#call send ((packet (#borrow packet)))))) (#forget packet) (#return ())\n")).unwrap();
}
#[test]
fn preservation_does_not_impose_a_requirement() {
    check(&format!("{REFERENT}\n#fn use ((packet (#ref-mut Packet))) () (#call shrink ((packet packet))) (#return ())\n")).unwrap();
}
#[test]
fn intermediary_does_not_implicitly_export_preservation() {
    assert!(check(&format!("{REFERENT}\n#fn middle ((packet (#ref-mut Packet))) () (#call shrink ((packet packet))) (#return ())\n#fn use ((packet (#ref-mut Packet))) () (#requires (#call acceptable ((packet packet)))) (#call middle ((packet packet))) (#call send ((packet packet))) (#return ())\n")).is_err());
}
#[test]
fn constrained_scalar_binding_needs_evidence() {
    check(&format!("{SCALAR}#type Small (#where (value #u64) (#call below-100 ((value value))))\n#fn use ((input #u64)) () (#if-valid (#call below-100 ((value input))) (#block (#let small Small input) (#call consume ((value small))))) (#return ())\n")).unwrap();
}
#[test]
fn constrained_scalar_cannot_be_forged() {
    assert!(check(&format!("{SCALAR}#type Small (#where (value #u64) (#call below-100 ((value value))))\n#fn use ((input #u64)) () (#let small Small input) (#return ())\n")).is_err());
}
#[test]
fn explicit_constrained_parameter_is_an_entry_contract() {
    check(&format!("{SCALAR}#type Small (#where (value #u64) (#call below-100 ((value value))))\n#fn forward ((value Small)) () (#call consume ((value value))) (#return ())\n")).unwrap();
}
const CONSTRAINED: &str = r#"
#fn small ((value (#ref #u64))) #bool (#return (#u64::lt (#deref value) 100u64))
#type Small (#where (value #u64) (#call small ((value (#borrow value)))))
#struct Holder () ((number Small) (tag #u64))
"#;
#[test]
fn fixed_field_must_be_valid_on_construction() {
    let source=format!("{CONSTRAINED}\n#fn use ((input #u64)) () (#let holder Holder (#struct-literal Holder ((number input) (tag 0u64)))) (#forget holder) (#return ())\n");
    let error = check(&source).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}
#[test]
fn fixed_field_restoration_after_mutable_element_borrow() {
    let source=format!("{CONSTRAINED}\n#fn edit ((holder (#ref-mut Holder))) () (#let slot (#ref-mut #u64) (#borrow-mut (#get holder number))) (#deref-set slot 42u64) (#assume (#call small ((value slot)))) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn fixed_field_borrow_cannot_end_with_missing_evidence() {
    let source=format!("{CONSTRAINED}\n#fn edit ((holder (#ref-mut Holder))) () (#let slot (#ref-mut #u64) (#borrow-mut (#get holder number))) (#deref-set slot 200u64) (#return ())\n");
    let error = check(&source).unwrap_err();
    assert!(error.contains("restored"), "{error}");
}
#[test]
fn saved_boolean_does_not_validate_mutated_storage() {
    let source=format!("{REFERENT}\n#fn use () () (#let-mut packet Packet (#struct-literal Packet ((body 2u64) (tag 0u64)))) (#let ok #bool (#call acceptable ((packet (#borrow packet))))) (#call replace ((packet (#borrow-mut packet)))) (#if-valid ok (#call send ((packet (#borrow packet))))) (#forget packet) (#return ())\n");
    let error = check(&source).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}
#[test]
fn requirements_nested_in_builtin_arguments_are_checked() {
    let source=format!("{SCALAR}\n#fn computed ((value #u64)) #u64 (#requires (#call below-100 ((value value)))) (#return value)\n#fn use ((input #u64)) #u64 (#return (#u64::add-wrap (#call computed ((value input))) 1u64))\n");
    assert!(check(&source).is_err());
}

#[test]
fn every_requirement_in_a_conjunction_is_needed() {
    let source=format!("{SCALAR}\n#fn nonzero ((value #u64)) #bool (#return (#u64::ne value 0u64))\n#fn target ((value #u64)) () (#requires (#bool::and (#call below-100 ((value value))) (#call nonzero ((value value))))) (#return ())\n#fn use ((input #u64)) () (#if-valid (#bool::and (#call below-100 ((value input))) (#call nonzero ((value input)))) (#call target ((value input)))) (#return ())\n");
    check(&source).unwrap();
    let bad = source.replace(
        "(#bool::and (#call below-100 ((value input))) (#call nonzero ((value input))))",
        "(#call below-100 ((value input)))",
    );
    assert!(check(&bad).unwrap_err().contains("missing evidence"));
}
#[test]
fn disjunction_does_not_supply_either_operand() {
    let source=format!("{SCALAR}\n#fn use ((input #u64)) () (#if-valid (#bool::or (#call below-100 ((value input))) true) (#call consume ((value input)))) (#return ())\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}
#[test]
fn saved_pure_scalar_observation_matches_specification() {
    let source=format!("{SCALAR}\n#fn observed ((value (#ref #u64))) #u64 (#return (#deref value))\n#fn use ((input (#ref #u64))) () (#let value #u64 (#call observed ((value input)))) (#assume (#call below-100 ((value (#call observed ((value input))))))) (#call consume ((value value))) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn scalar_snapshot_does_not_equal_a_new_observation_after_write() {
    let source=format!("{SCALAR}\n#fn observed ((value (#ref #u64))) #u64 (#return (#deref value))\n#fn use ((input (#ref-mut #u64))) () (#let value #u64 (#call observed ((value (#borrow (#deref input)))))) (#deref-set input 200u64) (#assume (#call below-100 ((value (#call observed ((value input))))))) (#call consume ((value value))) (#return ())\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}
#[test]
fn unused_refinement_predicate_is_still_checked() {
    let error=check("#fn wrong ((value #u64)) #u64 (#return value)\n#type Bad (#where (value #u64) (#call wrong ((value value))))\n").unwrap_err();
    assert!(error.contains("#bool"), "{error}");
}
#[test]
fn old_is_restricted_to_postconditions() {
    assert!(lim::parse_program(&format!("{SCALAR}\n#fn bad ((value #u64)) () (#requires (#call below-100 ((value (#old value))))) (#return ())\n")).unwrap_err().contains("#ensures"));
}
#[test]
fn stale_contract_metadata_cannot_certify_a_modified_ast() {
    let mut program=lim::parse_program(&format!("{SCALAR}\n#fn use ((input #u64)) () (#assume (#call below-100 ((value input)))) (#call consume ((value input))) (#return ())\n")).unwrap();
    let function = program
        .items
        .iter_mut()
        .find_map(|item| match item {
            lim::Item::Function(f) if f.name == "use" => Some(f),
            _ => None,
        })
        .unwrap();
    function.body.remove(0);
    assert!(lim::check_types(&program).unwrap_err().contains("metadata"));
}
#[test]
fn indirect_reference_field_write_invalidates_referent_evidence() {
    let source = r#"
#struct Link () ((target (#ref-mut #u64)))
#fn small ((value (#ref #u64))) #bool (#return (#u64::lt (#deref value) 100u64))
#fn consume ((value (#ref #u64))) () (#requires (#call small ((value value)))) (#return ())
#fn mutate ((link (#ref-mut Link))) () (#deref-set (#get link target) 200u64) (#return ())
#fn use ((link (#ref-mut Link))) ()
        (#let before (#ref-mut #u64) (#get link target))
        (#let ok #bool (#call small ((value (#borrow (#deref before))))))
        (#call mutate ((link link)))
        (#let after (#ref-mut #u64) (#get link target))
        (#if-valid ok (#call consume ((value (#borrow (#deref after))))))
        (#return ())
"#;
    let error = check(source).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}
#[test]
fn mutable_reference_return_keeps_fixed_owner_obligation() {
    let source=format!("{CONSTRAINED}\n#fn slot ((holder (#ref-mut Holder))) (#ref-mut #u64) (#return (#borrow-mut (#get holder number)))\n#fn edit ((holder (#ref-mut Holder))) () (#let item (#ref-mut #u64) (#call slot ((holder holder)))) (#deref-set item 200u64) (#return ())\n");
    let error = check(&source).unwrap_err();
    assert!(error.contains("restored"), "{error}");
}
#[test]
fn constrained_result_requires_evidence_even_without_an_ensures() {
    let source=format!("{SCALAR}#type Small (#where (value #u64) (#call below-100 ((value value))))\n#fn create ((input #u64)) Small (#return input)\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
    check(&source.replace(
        "(#return input)",
        "(#assume (#call below-100 ((value input)))) (#return input)",
    ))
    .unwrap();
}
#[test]
fn constrained_field_can_be_constructed_from_validated_value() {
    let source=format!("{CONSTRAINED}\n#fn use ((input #u64)) () (#if-valid (#call small ((value (#borrow input)))) (#block (#let holder Holder (#struct-literal Holder ((number input) (tag 0u64)))) (#forget holder))) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn constrained_slice_elements_are_rejected_instead_of_dropped() {
    let source=format!("{SCALAR}#type Small (#where (value #u64) (#call below-100 ((value value))))\n#type Unsupported (#slice Small)\n");
    assert!(lim::parse_program(&source)
        .unwrap_err()
        .contains("enclosing type"));
}

#[test]
fn builtin_named_user_functions_do_not_become_contract_forms() {
    check("#fn requires ((value #u64)) #u64 (#return value)\n#fn use () #u64 (#return (#call requires ((value 42u64))))\n").unwrap();
}
#[test]
fn refinement_substitution_keeps_field_selectors_literal() {
    check("#struct Boxed () ((value #u64))\n#fn below ((value #u64)) #bool (#return (#u64::lt value 100u64))\n#type SmallBox (#where (value Boxed) (#call below ((value (#get value value)))))\n#fn use ((value SmallBox)) () (#return ())\n").unwrap();
}
#[test]
fn float_literals_are_distinct_evidence_subjects() {
    let error=check("#fn positive ((value #f64)) #bool (#return (#f64::gt value 0.0f64))\n#fn consume ((value #f64)) () (#requires (#call positive ((value value)))) (#return ())\n#fn use () () (#if-valid (#call positive ((value 1.0f64))) (#call consume ((value -1.0f64)))) (#return ())\n").unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}
#[test]
fn old_snapshot_and_current_observation_have_distinct_versions() {
    let source = r#"#fn changed ((before #u64) (after #u64)) #bool (#return (#u64::ne before after))
#fn update ((value (#ref-mut #u64))) () (#ensures (#call changed ((before (#old (#deref value))) (after (#deref value))))) (#deref-set value 2u64) (#return ())
#fn consume ((before #u64) (after #u64)) () (#requires (#call changed ((before before) (after after)))) (#return ())
#fn use ((value (#ref-mut #u64))) () (#let before #u64 (#deref value)) (#call update ((value value))) (#call consume ((before before) (after (#deref value)))) (#return ())
"#;
    check(source).unwrap();
    let bad = source.replacen(
        "(#call consume ((before before) (after (#deref value))))",
        "(#call consume ((before before) (after before)))",
        1,
    );
    assert!(check(&bad).unwrap_err().contains("missing evidence"));
}
#[test]
fn conjunction_cannot_regrant_evidence_revoked_by_its_second_operand() {
    let source=format!("{REFERENT}\n#fn overwrite-and-true ((packet (#ref-mut Packet))) #bool (#call replace ((packet packet))) (#return true)\n#fn use ((packet (#ref-mut Packet))) () (#if-valid (#bool::and (#call acceptable ((packet (#borrow (#deref packet))))) (#call overwrite-and-true ((packet packet)))) (#call send ((packet (#borrow (#deref packet)))))) (#return ())\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}
#[test]
fn loop_conditions_cannot_reuse_pre_loop_evidence_after_mutation() {
    let source=format!("{REFERENT}\n#fn repeat ((packet (#ref Packet))) #bool (#requires (#call acceptable ((packet packet)))) (#return false)\n#fn use ((packet (#ref-mut Packet))) () (#requires (#call acceptable ((packet packet)))) (#while (#call repeat ((packet (#borrow (#deref packet))))) (#call replace ((packet packet)))) (#return ())\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}

#[test]
fn a_generated_vector_can_have_sorted_and_element_bound_requirements() {
    let source = r#"
#struct Allocator () ()
#generate #vec ((element #u64) (allocator Allocator) (name VecU64))
#fn sorted ((values (#ref VecU64))) #bool
        (#let length #usize (#call VecU64::len ((vector values))))
        (#let pointer (#ptr-mut #u64) (#clone (#get values pointer)))
        (#let-mut index #usize 1usize)
        (#while (#usize::lt index length)
          (#let left #u64 (#unsafe (#ptr-read (#ptr-offset (#clone pointer) (#usize::sub-wrap index 1usize)))))
          (#let right #u64 (#unsafe (#ptr-read (#ptr-offset (#clone pointer) index))))
          (#if (#u64::gt left right) (#block (#forget pointer) (#return false)))
          (#set index (#usize::add-wrap index 1usize)))
        (#forget pointer) (#return true)
#fn all-below-100 ((values (#ref VecU64))) #bool
        (#let length #usize (#call VecU64::len ((vector values))))
        (#let pointer (#ptr-mut #u64) (#clone (#get values pointer)))
        (#let-mut index #usize 0usize)
        (#while (#usize::lt index length)
          (#let element #u64 (#unsafe (#ptr-read (#ptr-offset (#clone pointer) index))))
          (#if (#u64::ge element 100u64) (#block (#forget pointer) (#return false)))
          (#set index (#usize::add-wrap index 1usize)))
        (#forget pointer) (#return true)
#type SortedSmallVec (#where (value VecU64)
        (#call sorted ((values (#borrow value))))
        (#call all-below-100 ((values (#borrow value)))))
#struct Store () ((values SortedSmallVec))
#fn accepts ((values (#ref SortedSmallVec))) () (#return ())
#fn validate-and-call ((values (#ref VecU64))) ()
        (#if-valid (#bool::and (#call sorted ((values values))) (#call all-below-100 ((values values))))
          (#call accepts ((values values))))
        (#return ())
"#;
    check(source).unwrap();
}

#[test]
fn casts_cannot_conflate_different_runtime_values() {
    let source=format!("{SCALAR}\n#fn use () () (#if-valid (#call below-100 ((value (#as (#as 256u64 #u8) #u64)))) (#call consume ((value 256u64)))) (#return ())\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}
#[test]
fn unsuffixed_literals_use_the_declared_context() {
    let source=format!("{SCALAR}\n#fn use () () (#let input #u64 42) (#if-valid (#call below-100 ((value input))) (#call consume ((value input)))) (#if-valid (#call below-100 ((value 42))) (#call consume ((value 42)))) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn constrained_array_elements_require_individual_evidence() {
    let source=format!("{SCALAR}#type Small (#where (value #u64) (#call below-100 ((value value))))\n#fn use ((a #u64) (b #u64)) () (#if-valid (#bool::and (#call below-100 ((value a))) (#call below-100 ((value b)))) (#block (#let values (#array Small 2) (#array (#array Small 2) a b)) (#forget values))) (#return ())\n");
    check(&source).unwrap();
    assert!(check(&source.replace(
        "(#bool::and (#call below-100 ((value a))) (#call below-100 ((value b))))",
        "(#call below-100 ((value a)))"
    ))
    .unwrap_err()
    .contains("missing evidence"));
}
#[test]
fn raw_memory_writes_inside_loops_cannot_preserve_old_evidence() {
    let source=format!("{REFERENT}\n#fn use ((packet (#ref-mut Packet)) (pointer (#ptr-mut #u64)) (again #bool)) () (#requires (#call acceptable ((packet packet)))) (#while again (#unsafe (#ptr-write (#clone pointer) 200u64))) (#call send ((packet (#borrow (#deref packet))))) (#forget pointer) (#return ())\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}
#[test]
fn nested_reference_writes_revoke_evidence_about_the_final_referent() {
    let source = r#"#struct Slot () ((pointer (#ref-mut #u64)))
#fn small ((value (#ref #u64))) #bool (#return (#u64::lt (#deref value) 100u64))
#fn consume ((value (#ref #u64))) () (#requires (#call small ((value value)))) (#return ())
#fn mutate ((slot (#ref-mut (#ref-mut #u64)))) () (#deref-set (#deref slot) 200u64) (#return ())
#fn use ((holder (#ref-mut Slot))) ()
          (#let reference (#ref-mut #u64) (#get holder pointer))
          (#let ok #bool (#call small ((value (#borrow (#deref reference))))))
          (#call mutate ((slot (#borrow-mut (#get holder pointer)))))
          (#let after (#ref-mut #u64) (#get holder pointer))
          (#if-valid ok (#call consume ((value (#borrow (#deref after))))))
          (#return ())
"#;
    let error = check(source).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}
#[test]
fn moving_an_owner_transfers_its_constrained_field_evidence() {
    let source=format!("{CONSTRAINED}\n#fn use ((holder Holder)) () (#let moved Holder holder) (#forget moved) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn constrained_structs_can_be_constructed_inline_and_returned() {
    let source=format!("{CONSTRAINED}\n#fn identity ((holder Holder)) Holder (#return holder)\n#fn create ((input #u64)) Holder (#requires (#call small ((value (#borrow input))))) (#return (#call identity ((holder (#struct-literal Holder ((number input) (tag 0u64)))))))\n#fn use ((input #u64)) () (#requires (#call small ((value (#borrow input))))) (#let holder Holder (#call create ((input input)))) (#forget holder) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn malformed_ghost_observations_are_errors_not_compiler_panics() {
    for observation in ["(#borrow)", "(#deref)", "(#get value)", "(#as value)"] {
        let source=format!("{SCALAR}\n#fn use ((value #u64)) () (#assume (#call below-100 ((value {observation})))) (#return ())\n");
        assert!(check(&source).unwrap_err().contains("argument count"));
    }
}
#[test]
fn guarantees_cannot_confuse_a_mutable_value_parameter_with_the_callers_copy() {
    let source=format!("{SCALAR}\n#fn update ((#mut value #u64)) () (#ensures (#call below-100 ((value value)))) (#set value 0u64) (#return ())\n");
    assert!(lim::parse_program(&source)
        .unwrap_err()
        .contains("mutable parameter"));
}
#[test]
fn assumed_argument_observations_do_not_grant_callee_postconditions() {
    let source=format!("{SCALAR}\n#fn observation ((value #u64)) #u64 (#ensures (#call below-100 ((value value)))) (#return 0u64)\n#fn ignored ((value #u64)) #bool (#return true)\n#fn use ((input #u64)) () (#assume (#call ignored ((value (#as (#call observation ((value input))) #u64))))) (#call consume ((value input))) (#return ())\n");
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}
#[test]
fn aliases_of_constrained_mutable_references_export_restoration() {
    let source=format!("{CONSTRAINED}#type Pointer (#ref-mut Small)\n#fn edit ((value Pointer)) () (#deref-set value 42u64) (#assume (#call small ((value value)))) (#return ())\n#fn use ((value Pointer)) () (#let slot Pointer (#borrow-mut (#deref value))) (#call edit ((value slot))) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn consuming_a_linear_owner_ends_its_storage_obligations() {
    let source=format!("{SCALAR}#type Small (#where (value #u64) (#call below-100 ((value value))))\n#struct Resource (#linear) ((value Small))\n#extern-fn #abi-c opaque () ()\n#fn destroy ((resource Resource)) () (#forget resource) (#unsafe (#unsafe-call opaque ())) (#return ())\n#fn use ((resource Resource)) () (#call destroy ((resource resource))) (#return ())\n");
    check(&source).unwrap();
}
#[test]
fn lending_an_invalid_element_does_not_claim_the_owner_is_already_restored() {
    let source=format!("{CONSTRAINED}\n#fn open ((holder (#ref-mut Holder))) (#ref-mut #u64) (#let item (#ref-mut #u64) (#borrow-mut (#get holder number))) (#deref-set item 200u64) (#return item)\n#fn use ((holder (#ref-mut Holder))) () (#let item (#ref-mut #u64) (#call open ((holder holder)))) (#drop item) (#return ())\n");
    let error = check(&source).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}
#[test]
fn growing_expression_identities_fail_with_a_bounded_diagnostic() {
    let mut body =
        String::from("(#assume (#call below-100 ((value input)))) (#let-mut value #u64 input)");
    for _ in 0..50 {
        body.push_str(" (#set value (#u64::add-wrap value value))");
    }
    let source = format!("{SCALAR}\n#fn use ((input #u64)) #u64 {body} (#return value)\n");
    assert!(check(&source).unwrap_err().contains("identity"));
}
#[test]
fn repeated_large_branch_snapshots_have_a_work_limit() {
    let mut body =
        String::from("(#assume (#call below-100 ((value input)))) (#let-mut current #u64 input)");
    for _ in 0..250 {
        body.push_str(" (#set current (#call grow ((value current))))");
    }
    for index in 0..2500 {
        body.push_str(&format!(" (#let value{index} #u64 current)"));
    }
    let mut nested = String::from("()");
    for _ in 0..3 {
        nested = format!("(#if true (#block {nested}) ())");
    }
    let source=format!("{SCALAR}\n#fn grow ((value #u64)) #u64 (#return value)\n#fn use ((input #u64)) () {body} {nested} (#return ())\n");
    let error = check(&source).unwrap_err();
    assert!(error.contains("snapshot work budget"), "{error}");
}
