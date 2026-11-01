//! Check the complete indexed-family examples in the kernel guide.
#[test]
fn native_nested_group_guide_declarations_are_checked() {
    let guide = include_str!("../docs/kernel.md");
    let source = guide
        .split("## Nested inductive groups")
        .nth(1)
        .unwrap()
        .split("```lisp\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap();
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn indexed_vector_and_proposition_guide_examples_are_checked() {
    let guide = include_str!("../docs/kernel.md");
    let section = guide
        .split("An indexed vector family")
        .nth(1)
        .unwrap()
        .split("## Falsehood and elimination")
        .next()
        .unwrap();
    let examples = section
        .split("```lisp\n")
        .skip(1)
        .map(|block| block.split("```").next().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        examples.len(),
        2,
        "expected the vector and proposition examples"
    );
    let source = examples.join("\n");
    let program = lim::parse_program(&source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::CheckedProgram::validate(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}

#[test]
fn indexed_vector_count_is_proved_for_every_natural_length() {
    let source = include_str!("../examples/proof_indexed.lim");
    let program = lim::parse_program(source).unwrap();
    lim::CheckedProgram::validate(&program).unwrap();
}

#[test]
fn vector_count_proof_requires_the_recursive_induction_hypothesis() {
    fn evidence(node: &lim::SpannedExpr) -> Option<lim::Span> {
        if matches!(&node.expr, lim::Expr::List(parts)
            if matches!(parts.first(), Some(lim::Expr::Symbol(name)) if name == "#pt-eq-elim"))
        {
            assert_eq!(node.children.len(), 7);
            return Some(node.children[6].span);
        }
        node.children.iter().find_map(evidence)
    }
    let source = include_str!("../examples/proof_indexed.lim");
    let nodes = lim::parse(source).unwrap();
    let span = nodes
        .iter()
        .find_map(evidence)
        .expect("J must use the recursive IH");
    let mutant = format!(
        "{}(#pt-refl #pt-nat counted){}",
        &source[..span.start],
        &source[span.end..]
    );
    let program = lim::parse_program(&mutant).unwrap();
    let error = match lim::CheckedProgram::validate(&program) {
        Ok(_) => panic!("reflexivity cannot replace the recursive IH"),
        Err(error) => error,
    };
    assert!(!error.to_string().contains("resource limit"), "{error}");
}
