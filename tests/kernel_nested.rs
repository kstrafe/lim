//! Native syntax must check every nested case before computing with it.
mod support;

const EXAMPLE: &str = include_str!("../examples/proof_nested.lim");

fn accepts(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}

fn rejects(source: &str, expected: &str) {
    lim::parse(source).unwrap_or_else(|why| panic!("unbalanced negative fixture: {why}\n{source}"));
    let program = lim::parse_program(source).unwrap();
    let error = lim::check_types(&program).expect_err("invalid nested proof accepted");
    assert!(
        error.contains(expected),
        "expected {expected:?}, got {error}\n{source}"
    );
    assert!(!error.contains("resource limit"), "{error}");
}

fn replace(source: &str, before: &str, after: &str) -> String {
    assert!(source.contains(before), "missing mutation target: {before}");
    source.replacen(before, after, 1)
}

#[test]
fn nonempty_nested_tree_fold_computes_through_both_cases() {
    accepts(EXAMPLE);
}

#[test]
fn selectors_must_match_the_checked_group_in_derivation_order() {
    for selector in ["#pt-nat", "(#pt-use seq ())", "(#pt-use tree ())"] {
        let source = replace(
            EXAMPLE,
            "(#pt-case (#pt-app (#pt-use seq ()) (#pt-use tree ()))",
            &format!("(#pt-case {selector}"),
        );
        rejects(&source, "selector must name");
    }
    rejects(
        &replace(
            EXAMPLE,
            "(#pt-case (#pt-use tree ())",
            "(#pt-case (#pt-app (#pt-use seq ()) (#pt-use tree ()))",
        ),
        "selector must name",
    );
}

#[test]
fn selector_conversion_cannot_erase_an_ill_typed_argument() {
    let source = replace(
        EXAMPLE,
        "(#pt-case (#pt-use tree ())",
        "(#pt-case (#pt-app (#pt-lambda ((ignored #pt-nat)) (#pt-use tree ())) (#pt-type 0))",
    );
    rejects(&source, "type mismatch");
}

#[test]
fn all_motives_branches_and_recursive_hypotheses_are_checked() {
    for (before, after, expected) in [
        ("(#pt-case (#pt-use tree ())\n         (#pt-lambda ((subject (#pt-use tree ()))) #pt-nat)",
         "(#pt-case (#pt-use tree ())\n         (#pt-lambda ((subject #pt-nat)) #pt-nat)", "motive"),
        ("(first-count #pt-nat)", "(first-count (#pt-use tree ()))", "type mismatch"),
        ("(rest-count #pt-nat)", "(rest-count (#pt-use tree ()))", "type mismatch"),
        ("(#pt-app (#pt-use add ()) first-count rest-count)", "(#pt-type 0)", "type mismatch"),
        ("(#pt-succ #pt-zero)\n          (#pt-lambda", "(#pt-type 0)\n          (#pt-lambda", "type mismatch"),
    ] {
        rejects(&replace(EXAMPLE, before, after), expected);
    }
}

#[test]
fn nested_case_tags_are_not_standalone_terms() {
    rejects(
        "(#math-definition bad () #pt-nat (#pt-case #pt-nat #pt-nat (#pt-zero)))",
        "unknown proof-term form",
    );
    rejects(
        &replace(
            EXAMPLE,
            "(#pt-case (#pt-use tree ())",
            "(tree (#pt-use tree ())",
        ),
        "nested cases require",
    );
    rejects(
        &replace(
            EXAMPLE,
            "(#indices)\n      ((#pt-case",
            "()\n      ((#pt-case",
        ),
        "explicit #indices",
    );
}

#[test]
fn a_plain_family_cannot_request_scoped_nested_cases() {
    rejects(
        r#"
      (#math-inductive plain () () (#pt-type 0) ((make ())))
      (#math-definition bad () #pt-nat
        (#pt-nested-induct plain () () 0 (#indices)
          ((#pt-case (#pt-use plain ()) (#pt-lambda ((x (#pt-use plain ()))) #pt-nat) (#pt-zero))
           (#pt-case (#pt-use plain ()) (#pt-lambda ((x (#pt-use plain ()))) #pt-nat) (#pt-zero)))
          (#pt-construct plain () () make ())))
    "#,
        "requires a family with nested recursion cases",
    );
}

#[test]
fn imported_families_selectors_and_absolute_names_resolve() {
    let scratch = support::Scratch::new("kernel-nested-import");
    let (families, rest) = EXAMPLE.split_once("(#math-definition add").unwrap();
    std::fs::write(scratch.path().join("families.lim"), families).unwrap();
    let source = format!(
        "(#alias seq = ./families.lim::seq)\n(#alias tree = ./families.lim::tree)\n(#math-definition add{rest}"
    ).replace("#pt-nested-induct tree", "#pt-nested-induct @tree")
        .replace("#pt-use tree ()", "#pt-use @tree ()")
        .replace("#pt-construct tree ", "#pt-construct @tree ");
    let program = lim::parse_program_from_path(&source, &scratch.path().join("main.lim"))
        .unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap();
}

#[test]
fn generated_declarations_and_nested_eliminators_are_checked_together() {
    let scratch = support::Scratch::new("kernel-nested-generated");
    let source = format!("(#gn emit () `({EXAMPLE}))\n(#generate emit)");
    let program = lim::parse_program_from_path(&source, &scratch.path().join("main.lim"))
        .unwrap_or_else(|why| panic!("{why}"));
    lim::check_types(&program).unwrap();
}

#[test]
fn duplicate_cases_and_extra_subject_indices_cannot_change_the_group() {
    fn find(node: &lim::SpannedExpr) -> Option<&lim::SpannedExpr> {
        if matches!(&node.expr, lim::Expr::List(parts)
            if matches!(parts.first(), Some(lim::Expr::Symbol(head)) if head == "#pt-nested-induct"))
        {
            return Some(node);
        }
        node.children.iter().find_map(find)
    }
    let nodes = lim::parse(EXAMPLE).unwrap();
    let induction = nodes.iter().find_map(find).unwrap();
    let span = induction.children[6].children[0].span;
    let duplicate = format!(
        "{}{} {}",
        &EXAMPLE[..span.start],
        &EXAMPLE[span.start..span.end],
        &EXAMPLE[span.start..]
    );
    rejects(&duplicate, "cover every root and container");
    rejects(
        &replace(EXAMPLE, "(#indices)", "(#indices #pt-zero)"),
        "count mismatch",
    );
    let one_case = replace(
        EXAMPLE,
        &EXAMPLE[induction.children[6].children[1].span.start
            ..induction.children[6].children[1].span.end],
        "",
    );
    rejects(&one_case, "between 2 and 16 family cases");
}

#[test]
fn polymorphic_nested_cases_preserve_explicit_uniform_parameters() {
    accepts(
        r#"
      (#math-inductive seq (u) ((A (#pt-type u))) (#pt-type u)
        ((nil ()) (cons ((head A) (tail #pt-self)))))
      (#math-inductive tree (u) ((A (#pt-type u))) (#pt-type u)
        ((leaf ((value A)))
         (node ((children (#pt-app (#pt-use seq (u)) (#pt-app (#pt-use tree (u)) A)))))))
      (#math-definition fold (u)
        (#pt-pi ((A (#pt-type u)) (value (#pt-app (#pt-use tree (u)) A))) #pt-nat)
        (#pt-lambda ((A (#pt-type u)) (value (#pt-app (#pt-use tree (u)) A)))
          (#pt-nested-induct tree (u) (A) 0 (#indices)
            ((#pt-case (#pt-app (#pt-use tree (u)) A)
               (#pt-lambda ((subject (#pt-app (#pt-use tree (u)) A))) #pt-nat)
               ((#pt-lambda ((element A)) (#pt-succ #pt-zero))
                (#pt-lambda ((children (#pt-app (#pt-use seq (u)) (#pt-app (#pt-use tree (u)) A)))
                  (ih #pt-nat)) (#pt-succ ih))))
             (#pt-case (#pt-app (#pt-use seq (u)) (#pt-app (#pt-use tree (u)) A))
               (#pt-lambda ((subject (#pt-app (#pt-use seq (u)) (#pt-app (#pt-use tree (u)) A)))) #pt-nat)
               (#pt-zero (#pt-lambda ((head (#pt-app (#pt-use tree (u)) A))
                 (head-ih #pt-nat) (tail (#pt-app (#pt-use seq (u)) (#pt-app (#pt-use tree (u)) A)))
                 (tail-ih #pt-nat)) (#pt-succ tail-ih))))) value)))
      (#theorem polymorphic-nested-computation (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use fold (0)) #pt-nat
            (#pt-construct tree (0) (#pt-nat) node
              ((#pt-construct seq (0) ((#pt-app (#pt-use tree (0)) #pt-nat)) nil ()))))
          (#pt-succ #pt-zero)))
        (#proof (#pt-refl #pt-nat (#pt-succ #pt-zero))))
    "#,
    );
}

const INDEXED: &str = r#"
  (#math-inductive vector () ((A (#pt-type 0)))
    (#indices (#parameter length #pt-nat)) (#pt-type 0)
    ((nil () (#pt-zero))
     (cons ((size #pt-nat) (head A) (tail (#pt-self-at (size)))) ((#pt-succ size)))))
  (#math-inductive indexed-tree () () (#pt-type 0)
    ((node ((size #pt-nat)
      (children (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()) size))))))
  (#math-definition indexed-count ()
    (#pt-pi ((value (#pt-use indexed-tree ()))) #pt-nat)
    (#pt-lambda ((value (#pt-use indexed-tree ())))
      (#pt-nested-induct indexed-tree () () 0 (#indices)
        ((#pt-case (#pt-use indexed-tree ())
           (#pt-lambda ((subject (#pt-use indexed-tree ()))) #pt-nat)
           ((#pt-lambda ((size #pt-nat)
             (children (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()) size))
             (ih #pt-nat)) (#pt-succ ih))))
         (#pt-case (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()))
           (#pt-lambda ((size #pt-nat)
             (subject (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()) size))) #pt-nat)
           (#pt-zero (#pt-lambda ((size #pt-nat)
             (head (#pt-use indexed-tree ())) (head-ih #pt-nat)
             (tail (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()) size))
             (tail-ih #pt-nat)) (#pt-succ tail-ih))))) value)))
  (#theorem indexed-nested-computes (#universes) (#parameters)
    (#statement (#pt-eq #pt-nat
      (#pt-app (#pt-use indexed-count ())
        (#pt-construct indexed-tree () () node ((#pt-succ #pt-zero)
          (#pt-construct vector () ((#pt-use indexed-tree ())) cons
            (#pt-zero
             (#pt-construct indexed-tree () () node
               (#pt-zero (#pt-construct vector () ((#pt-use indexed-tree ())) nil ())))
             (#pt-construct vector () ((#pt-use indexed-tree ())) nil ()))))))
      (#pt-numeral 2)))
    (#proof (#pt-refl #pt-nat (#pt-numeral 2))))
"#;

#[test]
fn indexed_container_cases_take_partial_types_and_generic_index_motives() {
    accepts(INDEXED);
    rejects(
        &replace(
            INDEXED,
            "(#pt-case (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()))",
            "(#pt-case (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()) #pt-zero)",
        ),
        "selector must name",
    );
    rejects(
        &replace(
            INDEXED,
            "(subject (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()) size))",
            "(subject (#pt-app (#pt-use vector ()) (#pt-use indexed-tree ()) #pt-zero))",
        ),
        "motive",
    );
}

#[test]
fn native_nested_declarations_reject_negative_containers() {
    rejects(
        r#"
      (#math-inductive consumer () ((A (#pt-type 0))) (#pt-type 0)
        ((make ((consume (#pt-pi ((item A)) #pt-nat))))))
      (#math-inductive bad () () (#pt-type 0)
        ((make ((child (#pt-app (#pt-use consumer ()) (#pt-use bad ())))))))
    "#,
        "strict positivity",
    );
}

#[test]
fn selectors_support_typed_aliases_and_beta_conversion() {
    accepts(&replace(
        EXAMPLE,
        "(#pt-case (#pt-use tree ())",
        "(#pt-case (#pt-app (#pt-lambda ((A (#pt-type 0))) A) (#pt-use tree ()))",
    ));
    accepts(&replace(
        EXAMPLE,
        "(#pt-case (#pt-use tree ())",
        "(#pt-case (#pt-let (#parameter View (#pt-type 0)) (#pt-use tree ()) View)",
    ));
}

#[test]
fn selected_case_is_an_explicit_checked_ordinal() {
    rejects(
        &replace(
            EXAMPLE,
            "#pt-nested-induct tree () () 0",
            "#pt-nested-induct tree () () 2",
        ),
        "case index is out of range",
    );
    for index in ["-1", "0u64", "tree-count"] {
        rejects(
            &replace(
                EXAMPLE,
                "#pt-nested-induct tree () () 0",
                &format!("#pt-nested-induct tree () () {index}"),
            ),
            "untyped nonnegative integer",
        );
    }
    // Selecting a physical container case also checks the subject's type.
    rejects(
        &replace(
            EXAMPLE,
            "#pt-nested-induct tree () () 0",
            "#pt-nested-induct tree () () 1",
        ),
        "type mismatch",
    );
}

#[test]
fn nested_propositions_cannot_eliminate_into_data() {
    rejects(
        r#"
      (#math-inductive seqp () ((P #pt-prop)) #pt-prop
        ((nil ()) (cons ((head P) (tail #pt-self)))))
      (#math-inductive treep () () #pt-prop
        ((leaf ()) (node ((children (#pt-app (#pt-use seqp ()) (#pt-use treep ())))))))
      (#math-definition bad () #pt-nat
        (#pt-nested-induct treep () () 0 (#indices)
          ((#pt-case (#pt-use treep ())
             (#pt-lambda ((subject (#pt-use treep ()))) #pt-nat)
             (#pt-zero (#pt-lambda ((children (#pt-app (#pt-use seqp ()) (#pt-use treep ()))) (ih #pt-nat)) ih)))
           (#pt-case (#pt-app (#pt-use seqp ()) (#pt-use treep ()))
             (#pt-lambda ((subject (#pt-app (#pt-use seqp ()) (#pt-use treep ())))) #pt-nat)
             (#pt-zero (#pt-lambda ((head (#pt-use treep ())) (head-ih #pt-nat)
               (tail (#pt-app (#pt-use seqp ()) (#pt-use treep ()))) (tail-ih #pt-nat)) tail-ih))))
          (#pt-construct treep () () leaf ())))
    "#,
        "large elimination",
    );
}

#[test]
fn a_checked_dependent_pair_container_can_hold_recursive_children() {
    accepts(
        r#"
      (#math-inductive dependent-pair ()
        ((A (#pt-type 0)) (B (#pt-pi ((a A)) (#pt-type 0)))) (#pt-type 0)
        ((make ((first A) (second (#pt-app B first))))))
      (#math-inductive pair-tree () () (#pt-type 0)
        ((leaf ()) (node ((pair (#pt-app (#pt-use dependent-pair ()) #pt-nat
          (#pt-lambda ((index #pt-nat)) (#pt-use pair-tree ()))))))))
      (#math-definition pair-count ()
        (#pt-pi ((value (#pt-use pair-tree ()))) #pt-nat)
        (#pt-lambda ((value (#pt-use pair-tree ())))
          (#pt-nested-induct pair-tree () () 0 (#indices)
            ((#pt-case (#pt-use pair-tree ())
               (#pt-lambda ((subject (#pt-use pair-tree ()))) #pt-nat)
               ((#pt-succ #pt-zero)
                (#pt-lambda ((pair (#pt-app (#pt-use dependent-pair ()) #pt-nat
                  (#pt-lambda ((index #pt-nat)) (#pt-use pair-tree ())))) (ih #pt-nat)) (#pt-succ ih))))
             (#pt-case (#pt-app (#pt-use dependent-pair ()) #pt-nat
                 (#pt-lambda ((index #pt-nat)) (#pt-use pair-tree ())))
               (#pt-lambda ((subject (#pt-app (#pt-use dependent-pair ()) #pt-nat
                 (#pt-lambda ((index #pt-nat)) (#pt-use pair-tree ()))))) #pt-nat)
               ((#pt-lambda ((first #pt-nat) (second (#pt-use pair-tree ())) (ih #pt-nat)) ih)))) value)))
      (#theorem dependent-nested-computes (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use pair-count ()) (#pt-construct pair-tree () () node
            ((#pt-construct dependent-pair ()
              (#pt-nat (#pt-lambda ((index #pt-nat)) (#pt-use pair-tree ()))) make
              (#pt-zero (#pt-construct pair-tree () () leaf ()))))))
          (#pt-numeral 2)))
        (#proof (#pt-refl #pt-nat (#pt-numeral 2))))
    "#,
    );
}

#[test]
fn nested_parameters_cannot_capture_an_earlier_constructor_field() {
    rejects(
        r#"
      (#math-inductive identity (u) ((A (#pt-type u)) (left A))
        (#indices (#parameter right A)) #pt-prop ((refl () (left))))
      (#math-inductive bad () () (#pt-type 0)
        ((make ((child #pt-self)
          (proof (#pt-app (#pt-use identity (0)) (#pt-use bad ()) child child))))))
    "#,
        "cannot capture constructor-local variables",
    );
}
