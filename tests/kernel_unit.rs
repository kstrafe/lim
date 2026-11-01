//! Source-level conformance tests for definitional equality of values of
//! nonrecursive, single-constructor, zero-field data types.

fn accepts(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("unit-conversion fixture must parse: {error}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|error| {
        panic!("unit-conversion fixture must typecheck: {error}\n{source}")
    });
}

fn rejects(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("negative unit fixture must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("kernel accepted an invalid unit conversion");
    assert!(
        error.starts_with("theorem '"),
        "not a theorem diagnostic: {error}\n{source}"
    );
    assert!(
        !error.contains("resource limit"),
        "resource error masked rejection: {error}\n{source}"
    );
}

const UNIT: &str = r#"
  (#math-inductive unit-data () () (#pt-type 0)
    ((only ())))
"#;

#[test]
fn arbitrary_variables_of_a_fieldless_singleton_are_equal() {
    accepts(&format!(
        r#"{UNIT}
      (#theorem variables-equal
        (#universes) (#parameters
          (#parameter left (#pt-use unit-data ()))
          (#parameter right (#pt-use unit-data ())))
        (#statement (#pt-eq (#pt-use unit-data ()) left right))
        (#proof (#pt-refl (#pt-use unit-data ()) left)))"#
    ));
}

#[test]
fn a_variable_equals_the_only_constructor_in_both_orientations() {
    accepts(&format!(
        r#"{UNIT}
      (#theorem variable-equals-constructor
        (#universes) (#parameters (#parameter value (#pt-use unit-data ())))
        (#statement (#pt-eq (#pt-use unit-data ()) value
          (#pt-construct unit-data () () only ())))
        (#proof (#pt-refl (#pt-use unit-data ()) value)))
      (#theorem constructor-equals-variable
        (#universes) (#parameters (#parameter value (#pt-use unit-data ())))
        (#statement (#pt-eq (#pt-use unit-data ())
          (#pt-construct unit-data () () only ()) value))
        (#proof (#pt-refl (#pt-use unit-data ())
          (#pt-construct unit-data () () only ()))) )"#
    ));
}

#[test]
fn constructor_and_application_results_are_equal_at_the_same_type() {
    accepts(&format!(
        r#"{UNIT}
      (#math-definition pass-unit ()
        (#pt-pi ((value (#pt-use unit-data ()))) (#pt-use unit-data ()))
        (#pt-lambda ((value (#pt-use unit-data ()))) value))
      (#theorem application-results
        (#universes) (#parameters
          (#parameter left (#pt-use unit-data ()))
          (#parameter right (#pt-use unit-data ())))
        (#statement (#pt-eq (#pt-use unit-data ())
          (#pt-app (#pt-use pass-unit ()) left)
          (#pt-app (#pt-use pass-unit ()) right)))
        (#proof (#pt-refl (#pt-use unit-data ())
          (#pt-app (#pt-use pass-unit ()) left))))"#
    ));
}

#[test]
fn neutral_and_constructor_unit_recursors_both_reduce_to_the_sole_branch() {
    accepts(&format!(
        r#"{UNIT}
      (#theorem neutral-unit-recursion
        (#universes) (#parameters
          (#parameter value (#pt-use unit-data ())))
        (#statement (#pt-eq #pt-nat
          (#pt-induct unit-data () ()
            (#pt-lambda ((subject (#pt-use unit-data ()))) #pt-nat)
            (#pt-zero) value)
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
      (#theorem constructor-unit-recursion
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-induct unit-data () ()
            (#pt-lambda ((subject (#pt-use unit-data ()))) #pt-nat)
            (#pt-zero) (#pt-construct unit-data () () only ()))
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
}

#[test]
fn parameterized_singleton_values_convert_at_the_same_parameter() {
    accepts(
        r#"
      (#math-inductive tagged-unit () ((tag #pt-nat)) (#pt-type 0)
        ((only ())))
      (#theorem same-parameter
        (#universes) (#parameters (#parameter left
          (#pt-app (#pt-use tagged-unit ()) #pt-zero))
          (#parameter right (#pt-app (#pt-use tagged-unit ()) #pt-zero)))
        (#statement (#pt-eq (#pt-app (#pt-use tagged-unit ()) #pt-zero) left right))
        (#proof (#pt-refl (#pt-app (#pt-use tagged-unit ()) #pt-zero) left)))
    "#,
    );
}

#[test]
fn universe_polymorphic_singleton_values_convert_for_an_arbitrary_level() {
    accepts(
        r#"
      (#math-inductive unit-at (u) () (#pt-sort u)
        ((only ())))
      (#theorem same-universe
        (#universes u) (#parameters
          (#parameter left (#pt-use unit-at (u)))
          (#parameter right (#pt-use unit-at (u))))
        (#statement (#pt-eq (#pt-use unit-at (u)) left right))
        (#proof (#pt-refl (#pt-use unit-at (u)) left)))
    "#,
    );
}

#[test]
fn dependent_family_indices_are_preserved_while_values_convert() {
    accepts(
        r#"
      (#math-inductive indexed-unit ()
        ((A (#pt-type 0)) (index A)) (#pt-type 0)
        ((only ())))
      (#theorem same-dependent-index
        (#universes) (#parameters
          (#parameter A (#pt-type 0)) (#parameter index A)
          (#parameter left (#pt-app (#pt-use indexed-unit ()) A index))
          (#parameter right (#pt-app (#pt-use indexed-unit ()) A index)))
        (#statement (#pt-eq (#pt-app (#pt-use indexed-unit ()) A index) left right))
        (#proof (#pt-refl (#pt-app (#pt-use indexed-unit ()) A index) left)))
    "#,
    );
}

#[test]
fn different_parameters_of_a_singleton_family_remain_distinct() {
    rejects(
        r#"
      (#math-inductive tagged-unit () ((tag #pt-nat)) (#pt-type 0)
        ((only ())))
      (#theorem different-parameters
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-type 0)
          (#pt-app (#pt-use tagged-unit ()) #pt-zero)
          (#pt-app (#pt-use tagged-unit ()) (#pt-succ #pt-zero))))
        (#proof (#pt-refl (#pt-type 0)
          (#pt-app (#pt-use tagged-unit ()) #pt-zero))))
    "#,
    );
}

#[test]
fn distinct_singleton_family_names_remain_nominally_distinct() {
    rejects(
        r#"
      (#math-inductive first-unit () () (#pt-type 0) ((only ())))
      (#math-inductive second-unit () () (#pt-type 0) ((only ())))
      (#theorem family-names-remain-distinct
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-type 0)
          (#pt-use first-unit ()) (#pt-use second-unit ())))
        (#proof (#pt-refl (#pt-type 0) (#pt-use first-unit ()))) )
    "#,
    );
}

#[test]
fn one_constructor_with_data_fields_is_not_a_unit_type() {
    rejects(
        r#"
      (#math-inductive fielded () () (#pt-type 0)
        ((pack ((value #pt-nat)))))
      (#theorem distinct-fields
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-use fielded ())
          (#pt-construct fielded () () pack (#pt-zero))
          (#pt-construct fielded () () pack ((#pt-succ #pt-zero)))))
        (#proof (#pt-refl (#pt-use fielded ())
          (#pt-construct fielded () () pack (#pt-zero)))))
    "#,
    );
}

#[test]
fn recursive_single_constructor_types_are_not_collapsed() {
    rejects(
        r#"
      (#math-inductive recursive-data () () (#pt-type 0)
        ((roll ((next #pt-self)))))
      (#theorem recursive-values-remain-distinct
        (#universes) (#parameters
          (#parameter left (#pt-use recursive-data ()))
          (#parameter right (#pt-use recursive-data ())))
        (#statement (#pt-eq (#pt-use recursive-data ()) left right))
        (#proof (#pt-refl (#pt-use recursive-data ()) left)))
    "#,
    );
}

#[test]
fn values_at_a_different_universe_instantiation_cannot_be_substituted() {
    rejects(
        r#"
      (#math-inductive unit-at (u) () (#pt-sort u)
        ((only ())))
      (#theorem wrong-universe
        (#universes u) (#parameters
          (#parameter value (#pt-use unit-at (u))))
        (#statement (#pt-eq (#pt-use unit-at (u)) value
          (#pt-construct unit-at ((#pt-level-succ u)) () only ())))
        (#proof (#pt-refl (#pt-use unit-at (u)) value)))
    "#,
    );
}

#[test]
fn the_fieldless_singleton_rule_does_not_collapse_nat_constructors() {
    rejects(
        r#"
      (#theorem nat-zero-is-successor
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn the_fieldless_singleton_rule_does_not_inhabit_false() {
    rejects(&format!(
        r#"{UNIT}
      (#theorem unit-is-not-false
        (#universes) (#parameters)
        (#statement #pt-false)
        (#proof (#pt-construct unit-data () () only ())))"#
    ));
}

#[test]
fn beta_reduction_cannot_hide_an_ill_typed_erased_value() {
    rejects(&format!(
        r#"{UNIT}
      (#theorem erased-argument-is-checked
        (#universes) (#parameters (#parameter value (#pt-use unit-data ())))
        (#statement (#pt-eq (#pt-use unit-data ()) value value))
        (#proof (#pt-app
          (#pt-lambda ((ignored #pt-nat))
            (#pt-refl (#pt-use unit-data ()) value))
          (#pt-refl #pt-nat #pt-zero))))"#
    ));
}

#[test]
fn unit_recursion_does_not_erase_invalid_subjects_parameters_or_branches() {
    for recursion in [
        "(#pt-induct unit-data () () (#pt-lambda ((subject (#pt-use unit-data ()))) #pt-nat) (#pt-zero) #pt-zero)",
        "(#pt-induct unit-data () (#pt-zero) (#pt-lambda ((subject (#pt-use unit-data ()))) #pt-nat) (#pt-zero) (#pt-construct unit-data () () only ()))",
        "(#pt-induct unit-data () () (#pt-lambda ((subject (#pt-use unit-data ()))) #pt-nat) (#pt-zero #pt-zero) (#pt-construct unit-data () () only ()))",
        "(#pt-induct unit-data () () (#pt-lambda ((subject (#pt-use unit-data ()))) #pt-nat) ((#pt-refl #pt-nat #pt-zero)) (#pt-construct unit-data () () only ()))",
    ] {
        rejects(&format!(
            "{UNIT}\n(#theorem invalid-unit-recursion (#universes) (#parameters)\n (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))\n (#proof (#pt-refl #pt-nat {recursion})))"
        ));
    }
}
