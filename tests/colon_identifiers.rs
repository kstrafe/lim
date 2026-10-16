#[test]
fn only_a_standalone_colon_groups_arguments() {
    let tokens = lim::lex("Pipeline::Pending left:right :leading trailing: :: :").unwrap();
    for (token, expected) in tokens.iter().zip([
        "Pipeline::Pending",
        "left:right",
        ":leading",
        "trailing:",
        "::",
    ]) {
        assert_eq!(token.kind, lim::TokenKind::Symbol(expected.into()));
    }
    assert_eq!(tokens.last().unwrap().kind, lim::TokenKind::Colon);
    assert_eq!(
        lim::parse("(: task Pipeline::Pending : tag left:right)").unwrap()[0].expr,
        lim::parse("((task Pipeline::Pending) (tag left:right))").unwrap()[0].expr,
    );
}

#[test]
fn colon_names_are_flat_identifiers_in_declarations_and_calls() {
    let source = "(#enum Pipeline::Poll () ((Pipeline::Ready #u64)))
        (#fn Pipeline::poll (: task:value #u64) Pipeline::Poll
          (#return (Pipeline::Ready task:value)))
        (#fn main () #u64
          (#return (#match (#call Pipeline::poll (: task:value 42u64))
            (#case (Pipeline::Ready answer) answer))))";
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap();
}
