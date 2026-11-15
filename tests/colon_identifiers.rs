#[test]
fn qualified_colon_names_stay_identifiers() {
    let tokens = lim::lex("Pipeline::Poll.Pending left:right :leading trailing: :: :").unwrap();
    for (token, expected) in tokens.iter().zip([
        "Pipeline::Poll.Pending",
        "left:right",
        ":leading",
        "trailing:",
        "::",
    ]) {
        assert_eq!(token.kind, lim::TokenKind::Symbol(expected.into()));
    }
    assert_eq!(tokens.last().unwrap().kind, lim::TokenKind::Colon);
    assert_eq!(
        lim::parse(": (task Pipeline::Poll.Pending) (tag left:right)").unwrap()[0].expr,
        lim::parse("((task Pipeline::Poll.Pending) (tag left:right))").unwrap()[0].expr,
    );
}

#[test]
fn colon_names_are_flat_identifiers_in_declarations_and_calls() {
    let source = "#enum Pipeline::Poll () ((Pipeline::Poll.Ready #u64))
#fn Pipeline::poll {
  #params = ((task #u64));
  #returns = Pipeline::Poll;
  #body = (
            (#return (#enum-literal Pipeline::Poll.Ready task))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
            (#return (#match (#call Pipeline::poll ((task 42u64)))
              (#case (Pipeline::Poll.Ready answer) answer)))\n  );\n}\n";
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn formatting_distinguishes_colon_names_from_grouping() {
    let source = "#fn Pipeline::identity {
  #params = ((value #u64));
  #returns = #u64;
  #body = ( (#return value)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return (#call Pipeline::identity ((value 42u64))))\n  );\n}\n";
    let formatted = lim::format_source(source).unwrap();
    let before = lim::parse_source_unit(source)
        .unwrap()
        .into_iter()
        .map(|form| form.expr)
        .collect::<Vec<_>>();
    let after = lim::parse_source_unit(&formatted)
        .unwrap()
        .into_iter()
        .map(|form| form.expr)
        .collect::<Vec<_>>();
    assert_eq!(before, after);
    lim::check_types(&lim::parse_program(&formatted).unwrap()).unwrap();
}

#[test]
fn invalid_colon_declaration_names_are_rejected() {
    for source in [
        "#fn :identity {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}\n",
        "#fn identity:fn {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}\n",
        "#fn Pipeline:identity {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}\n",
        "#fn Pipeline::identity {\n  #params = ((task:value #u64));\n  #returns = #u64;\n  #body = ( (#return task:value)\n  );\n}\n",
        "#fn Pipeline::identity {\n  #params = ((::value #u64));\n  #returns = #u64;\n  #body = ( (#return ::value)\n  );\n}\n",
    ] {
        let error = lim::parse_program(source).unwrap_err();
        assert!(error.contains("violates value naming"), "{source}: {error}");
    }
}
