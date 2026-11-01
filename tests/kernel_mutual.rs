//! Source-level conformance tests for mutually defined mathematical inductives.

fn accepts(source: &str) {
    lim::parse(source).unwrap_or_else(|error| {
        panic!("fixture must have balanced S-expressions: {error}\n{source}")
    });
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("fixture must parse as a program: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str) {
    lim::parse(source).unwrap_or_else(|error| {
        panic!("semantic negative must have balanced S-expressions: {error}\n{source}")
    });
    let program = lim::parse_program(source).unwrap_or_else(|error| {
        panic!("semantic negative must parse as a program: {error}\n{source}")
    });
    let error =
        lim::check_types(&program).expect_err("kernel accepted an invalid mutual inductive");
    let message = error.to_string();
    assert!(
        !message.contains("resource limit"),
        "resource failure masked rejection: {message}\n{source}"
    );
}

#[test]
fn mutual_tree_and_forest_recursion_checks_all_members_and_ihs() {
    accepts(include_str!("../examples/proof_mutual.lim"));
}

#[test]
fn indexed_function_child_gets_a_pointwise_sibling_ih() {
    accepts(include_str!("../examples/proof_mutual_function.lim"));
}

#[test]
fn mutual_group_rejects_inconsistent_members_and_elimination_bundles() {
    for fixture in [
        // The member list must be identical and include the declaration itself.
        "(#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ((x (#pt-recur left ())))))) (#math-inductive right () () (#mutual right left) (#pt-type 0) ((end ())))",
        "(#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ()))) (#math-inductive right () () (#mutual left missing) (#pt-type 0) ((end ())))",
        // Parameters and result sorts are shared by the group.
        "(#math-inductive left (u) ((A (#pt-type u))) (#mutual left right) (#pt-type u) ((wrap ()))) (#math-inductive right (u) ((A (#pt-type (#pt-level-succ u)))) (#mutual left right) (#pt-type u) ((end ())))",
        // A mutual eliminator needs a motive and a complete branch list for every member.
        "(#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ()))) (#math-inductive right () () (#mutual left right) (#pt-type 0) ((end ()))) (#math-definition bad () #pt-nat (#pt-mutual-induct left () () (#indices) ((left (#pt-lambda ((x (#pt-use left ()))) #pt-nat) ((#pt-lambda ((x (#pt-use left ()))) #pt-zero)))) (#pt-construct left () () wrap ())))",
        // Ordinary induction is not available for a member of a mutual group.
        "(#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ()))) (#math-inductive right () () (#mutual left right) (#pt-type 0) ((end ()))) (#math-definition bad () #pt-nat (#pt-induct left () () (#pt-lambda ((x (#pt-use left ()))) #pt-nat) (#pt-zero) (#pt-construct left () () wrap ())))",
        // Mutual propositions cannot eliminate into data.
        "(#math-inductive even () () (#mutual even odd) (#indices (#parameter n #pt-nat)) #pt-prop ((zero () (#pt-zero)))) (#math-inductive odd () () (#mutual even odd) (#indices (#parameter n #pt-nat)) #pt-prop ((zero () (#pt-zero)))) (#math-definition bad () #pt-nat (#pt-mutual-induct even () () (#indices #pt-zero) ((even (#pt-lambda ((n #pt-nat) (p (#pt-app (#pt-use even ()) n))) #pt-nat) (#pt-zero)) (odd (#pt-lambda ((n #pt-nat) (p (#pt-app (#pt-use odd ()) n))) #pt-nat) (#pt-zero))) (#pt-construct even () () zero ())))",
    ] {
        rejects(fixture);
    }
}

#[test]
fn recursive_markers_reject_wrong_members_and_negative_occurrences() {
    for fixture in [
        "(#math-inductive outside () () (#pt-type 0) ((make ()))) (#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ((x (#pt-recur outside ())))))) (#math-inductive right () () (#mutual left right) (#pt-type 0) ((end ())))",
        "(#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ((f (#pt-pi ((x (#pt-recur right ()))) #pt-nat)))))) (#math-inductive right () () (#mutual left right) (#pt-type 0) ((end ())))",
    ] {
        rejects(fixture);
    }
}

#[test]
fn explicit_family_applications_check_uniform_parameters_before_accepting_recursion() {
    let source = r#"
      (#math-inductive left () ((A (#pt-type 0))) (#mutual left right) (#pt-type 0)
        ((make ((child (#pt-app (#pt-use right ()) A))))))
      (#math-inductive right () ((A (#pt-type 0))) (#mutual left right) (#pt-type 0)
        ((end ())))
    "#;
    accepts(source);
    let changed = source.replace("(#pt-use right ()) A", "(#pt-use right ()) #pt-nat");
    let program = lim::parse_program(&changed).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(error.contains("uniform"), "{error}");
    assert!(!error.contains("resource limit"), "{error}");
}

#[test]
fn a_bad_later_member_diagnostic_identifies_its_own_declaration() {
    let source = r#"
      (#math-inductive left () () (#mutual left right) (#pt-type 0) ((make ())))
      (#math-inductive right () () (#mutual left right) (#pt-type 0)
        ((bad ((function (#pt-pi ((value (#pt-recur left ()))) #pt-false))))))
    "#;
    let program = lim::parse_program(source).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(error.starts_with("theorem 'right':"), "{error}");
    assert!(error.contains("strict positivity"), "{error}");
}

#[test]
fn count_equations_reject_a_type_correct_branch_that_discards_a_recursive_ih() {
    fn branch_body(node: &lim::SpannedExpr) -> Option<lim::Span> {
        if matches!(&node.expr, lim::Expr::List(parts)
            if parts.len() == 4
                && matches!(&parts[0], lim::Expr::Symbol(name) if name == "#pt-app")
                && matches!(&parts[2], lim::Expr::Symbol(name) if name == "first-count")
                && matches!(&parts[3], lim::Expr::Symbol(name) if name == "rest-count"))
        {
            return Some(node.span);
        }
        node.children.iter().find_map(branch_body)
    }
    let source = include_str!("../examples/proof_mutual.lim");
    let span = lim::parse(source)
        .unwrap()
        .iter()
        .find_map(branch_body)
        .expect("the forest branch adds both recursive hypotheses");
    let changed = format!(
        "{}first-count{}",
        &source[..span.start],
        &source[span.end..]
    );
    let program = lim::parse_program(&changed).unwrap();
    let error = lim::check_types(&program)
        .expect_err("discarding the forest IH invalidates the count equation");
    assert!(error.contains("kernel type mismatch"), "{error}");
    assert!(!error.contains("resource limit"), "{error}");
}
