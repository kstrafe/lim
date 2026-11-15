use lim::Expr;

#[test]
fn parsed_nested_list_payload_is_shared_with_its_source_child() {
    let forms = lim::parse("(root (branch leaf))").unwrap();
    let root = &forms[0];
    let branch = &root.children[1];

    let Expr::List(root_items) = &root.expr else {
        panic!("root expression should be a list");
    };
    let Expr::List(branch_items) = &branch.expr else {
        panic!("branch expression should be a list");
    };
    let Expr::List(raw_branch_items) = &root_items[1] else {
        panic!("raw root child should be a list");
    };

    assert!(!branch_items.is_empty());
    assert_eq!(branch_items.as_ptr(), raw_branch_items.as_ptr());
    assert_eq!(
        branch.expr,
        Expr::List(vec![Expr::Symbol("branch".into()), Expr::Symbol("leaf".into()),].into())
    );
}

#[test]
fn mutating_a_cloned_nested_list_detaches_and_keeps_the_parent_snapshot() {
    let parsed = lim::parse("(root (branch leaf))").unwrap();
    let original = parsed[0].clone();
    let mut cloned = original.clone();

    let Expr::List(original_items) = &original.children[1].expr else {
        panic!("parsed child expression should be a list");
    };
    let original_ptr = original_items.as_ptr();

    let Expr::List(mutated_items) = &mut cloned.children[1].expr else {
        panic!("cloned child expression should be a list");
    };
    mutated_items.push(Expr::Symbol("added".into()));

    let Expr::List(cloned_items) = &cloned.children[1].expr else {
        unreachable!();
    };
    let Expr::List(original_items_after) = &original.children[1].expr else {
        unreachable!();
    };
    assert_ne!(cloned_items.as_ptr(), original_ptr);
    assert_eq!(original_items_after.as_ptr(), original_ptr);
    assert_eq!(
        original.children[1].expr,
        Expr::List(vec![Expr::Symbol("branch".into()), Expr::Symbol("leaf".into()),].into())
    );
    assert_eq!(
        cloned.children[1].expr,
        Expr::List(
            vec![
                Expr::Symbol("branch".into()),
                Expr::Symbol("leaf".into()),
                Expr::Symbol("added".into()),
            ]
            .into()
        )
    );

    // The parent's raw Expr is an independent parsed snapshot and stays intact.
    assert_eq!(cloned.expr, original.expr);
}

#[test]
fn editing_a_raw_parent_does_not_change_its_source_children_or_other_clones() {
    let parsed = lim::parse("(root (branch leaf))").unwrap();
    let original = &parsed[0];
    let mut edited = original.clone();
    let Expr::List(parent) = &mut edited.expr else {
        unreachable!();
    };
    let Expr::List(branch) = &mut parent[1] else {
        unreachable!();
    };
    assert_eq!(branch.remove(0), Expr::Symbol("branch".into()));
    branch.extend([Expr::Symbol("extra".into()), Expr::Symbol("tail".into())]);
    let removed: Vec<_> = branch.drain(1..).collect();
    assert_eq!(
        removed,
        vec![Expr::Symbol("extra".into()), Expr::Symbol("tail".into())]
    );
    assert_eq!(
        branch.clone().into_iter().collect::<Vec<_>>(),
        vec![Expr::Symbol("leaf".into())]
    );
    assert_eq!(edited.children, original.children);
    assert_eq!(parsed[0].expr, original.expr);
    assert_ne!(edited.expr, original.expr);
}

#[test]
fn cloned_assertion_statements_validate_and_emit_as_distinct_occurrences() {
    let mut program =
        lim::parse_program("#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#assert true) (#return 42u64)\n  );\n}\n").unwrap();
    let lim::Item::Function(main) = &mut program.items[0] else {
        panic!("expected the main function");
    };
    let assertion = main.body[0].clone();
    let lim::Statement::Expr(Expr::List(original_items)) = &main.body[0] else {
        panic!("expected an assertion expression");
    };
    let lim::Statement::Expr(Expr::List(cloned_items)) = &assertion else {
        panic!("expected the cloned assertion expression");
    };
    assert!(!original_items.is_empty());
    assert_eq!(original_items.as_ptr(), cloned_items.as_ptr());
    main.body.insert(1, assertion);

    let checked = lim::CheckedProgram::validate(&program)
        .expect("cloned assertions must have separate executable identities");
    checked
        .generate_assembly(lim::TargetDescription::X86_64_SYSTEM_V)
        .expect("both assertion occurrences must emit successfully");
}

#[test]
fn cloned_function_bodies_keep_their_distinct_type_contexts() {
    let mut program = lim::parse_program(
        "#fn copy-word {
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return (#clone value))
  );
}
#fn copy-flag {
  #params = ((value #bool));
  #returns = #bool;
  #body = ( (#return (#clone value))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#assert (#call copy-flag ((value true))))
             (#return (#call copy-word ((value 42u64))))\n  );\n}\n",
    )
    .unwrap();
    let lim::Item::Function(original) = &program.items[0] else {
        panic!("expected the word function");
    };
    let mut cloned = original.clone();
    cloned.name = "copy-flag".into();
    cloned.parameters[0].ty = lim::Type::Bool;
    cloned.return_type = lim::Type::Bool;

    let lim::Statement::Return(Some(Expr::List(original_items))) = &original.body[0] else {
        panic!("expected the word function to return a clone expression");
    };
    let lim::Statement::Return(Some(Expr::List(cloned_items))) = &cloned.body[0] else {
        panic!("expected the boolean function to return a clone expression");
    };
    assert!(!original_items.is_empty());
    assert_eq!(original_items.as_ptr(), cloned_items.as_ptr());
    program.items[1] = lim::Item::Function(cloned);

    let checked = lim::CheckedProgram::validate(&program)
        .expect("shared clone syntax must validate in both U64 and Bool contexts");
    checked
        .generate_assembly(lim::TargetDescription::X86_64_SYSTEM_V)
        .expect("both typed function bodies must emit successfully");
}

#[test]
fn repeated_shared_call_syntax_still_rejects_a_second_linear_consumption() {
    let mut program = lim::parse_program(
        "#struct Owned (#linear) ((value #u64))
#fn consume {
  #params = ((value Owned));
  #returns = ();
  #body = ( (#forget value) (#return ())
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let item Owned (#struct-literal Owned ((value 42u64))))
             (#call consume ((value item)))
             (#return 0u64)\n  );\n}\n",
    )
    .unwrap();
    let function = program
        .items
        .iter_mut()
        .find_map(|item| match item {
            lim::Item::Function(function) if function.name == "main" => Some(function),
            _ => None,
        })
        .unwrap();
    function.body.insert(2, function.body[1].clone());
    let error = lim::CheckedProgram::validate(&program)
        .err()
        .expect("sharing syntax must not merge two consumptions");
    assert!(
        error.starts_with("linear value 'item' was used more than once"),
        "{error}"
    );
}
