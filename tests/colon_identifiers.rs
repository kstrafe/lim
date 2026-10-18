#[test]
fn only_a_standalone_colon_groups_arguments() {
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
        lim::parse("(: task Pipeline::Poll.Pending : tag left:right)").unwrap()[0].expr,
        lim::parse("((task Pipeline::Poll.Pending) (tag left:right))").unwrap()[0].expr,
    );
}

#[test]
fn colon_names_are_flat_identifiers_in_declarations_and_calls() {
    let source = "(#enum Pipeline::Poll () ((Pipeline::Poll.Ready #u64)))
        (#fn Pipeline::poll (: task:value #u64) Pipeline::Poll
          (#return (Pipeline::Poll.Ready task:value)))
        (#fn main () #u64
          (#return (#match (#call Pipeline::poll (: task:value 42u64))
            (#case (Pipeline::Poll.Ready answer) answer))))";
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn formatting_distinguishes_colon_names_from_grouping() {
    let source = "(#fn :identity (: ::value #u64) #u64 (#return ::value))
      (#fn main () #u64 (#return (#call :identity (: ::value 42u64))))";
    let formatted = lim::format_source(source).unwrap();
    let before = lim::parse(source)
        .unwrap()
        .into_iter()
        .map(|form| form.expr)
        .collect::<Vec<_>>();
    let after = lim::parse(&formatted)
        .unwrap()
        .into_iter()
        .map(|form| form.expr)
        .collect::<Vec<_>>();
    assert_eq!(before, after);
    lim::check_types(&lim::parse_program(&formatted).unwrap()).unwrap();
}
