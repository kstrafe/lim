mod support;

use lim::{Diagnostic, Expr, Item, Statement, Type, check_types, parse_program};

fn function(body: &str) -> String {
    format!("#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = (\n{body}\n  );\n}}\n")
}

fn diagnostic(source: &str) -> Diagnostic {
    let scratch = support::Scratch::new("let-delimiters");
    lim::check_source_with_generated_sources(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        &scratch.path().join("generated"),
    )
    .unwrap_err()
}

fn assert_span(source: &str, error: &Diagnostic, text: &str, start: usize) {
    let span = error.span.expect("diagnostic must retain its source span");
    assert_eq!(span.start, start, "{error:?}");
    assert_eq!(&source[span.start..span.end], text, "{error:?}");
}

#[test]
fn both_mutabilities_lower_to_the_existing_let_statement() {
    for (head, mutable) in [("#let", false), ("#let-mut", true)] {
        let delimited = function(&format!(
            "    {head} count : #u64 = 42u64;\n    #return count;"
        ));
        let canonical = function(&format!(
            "    ({head} count #u64 42u64)\n    (#return count)"
        ));
        let program = parse_program(&delimited).unwrap();
        check_types(&program).unwrap();
        assert_eq!(program.items, parse_program(&canonical).unwrap().items);
        let Item::Function(main) = &program.items[0] else {
            panic!("expected function");
        };
        assert!(
            matches!(&main.body[0], Statement::Let { name, ty: Type::U64, mutable: actual, .. }
            if name == "count" && *actual == mutable)
        );
    }
    let source =
        function("    #let-mut count : #u64 = 0u64;\n    #set count 42u64;\n    #return count;");
    check_types(&parse_program(&source).unwrap()).unwrap();
}

#[test]
fn root_bindings_preserve_existing_mutability_rules() {
    let source = "#let answer : #u64 = 42u64;\n#let-mut counter : #u64 = 0u64;\n";
    let program = parse_program(source).unwrap();
    assert!(
        check_types(&program)
            .unwrap_err()
            .contains("top-level binding 'counter' cannot be mutable")
    );
    check_types(&parse_program("#let answer : #u64 = 42u64;\n").unwrap()).unwrap();
    assert!(matches!(
        &program.items[0],
        Item::Let { mutable: false, .. }
    ));
    assert!(matches!(&program.items[1], Item::Let { mutable: true, .. }));
    assert_eq!(
        program.items,
        parse_program("#let answer #u64 42u64\n#let-mut counter #u64 0u64\n")
            .unwrap()
            .items
    );
}

#[test]
fn reader_keeps_nested_specification_and_exact_operand_spans() {
    let source = "#let count : #u64 = 42u64;";
    let forms = lim::parse_source_unit(source).unwrap();
    let binding = &forms[0];
    assert_eq!(binding.children.len(), 3);
    let specification = &binding.children[2];
    assert_eq!(specification.children.len(), 3);
    assert_eq!(specification.children[1].expr, Expr::Symbol("=".into()));
    for (child, spelling) in specification.children.iter().zip(["#u64", "=", "42u64"]) {
        assert_eq!(&source[child.span.start..child.span.end], spelling);
    }
    assert_eq!(
        binding.expr,
        lim::parse("(#let count (#u64 = 42u64))").unwrap()[0].expr
    );
}

#[test]
fn compound_types_calls_and_colon_initializers_work() {
    let source = format!(
        "#fn add {{ #params = ((left #u64) (right #u64)); #returns = #u64; #body = ((#return (#u64::add-wrap left right))); }}\n{}",
        function(
            r#"    #let pair : (#tuple #u64 #u64) = (#tuple 20u64 22u64);
    #let-mut values : (#array #u64 2) = (#array (#array #u64 2) (#get pair 0) (#get pair 1));
    #let answer : #u64 = : #call add ((left (#index values 0usize)) (right (#index values 1usize)));
    #return answer;"#
        )
    );
    check_types(&parse_program(&source).unwrap()).unwrap();
}

#[test]
fn indented_initializers_and_grouped_multiline_values_work() {
    for head in ["#let", "#let-mut"] {
        let source = function(&format!(
            "    ({head} answer : #u64 = :\n      #u64::add-wrap 20u64 22u64\n    );\n    #return answer;"
        ));
        check_types(&parse_program(&source).unwrap()).unwrap();
        let grouped = function(&format!(
            "    {head} answer : #u64 = (#u64::add-wrap\n      20u64\n      22u64);\n    #return answer;"
        ));
        check_types(&parse_program(&grouped).unwrap()).unwrap();
    }
    let source = function(
        r#"    #let pair (
      (#tuple #u64 #u64) =
      (#tuple 20u64 22u64)
    );
    #return (#u64::add-wrap (#get pair 0) (#get pair 1));"#,
    );
    check_types(&parse_program(&source).unwrap()).unwrap();
}

#[test]
fn delimiters_have_exact_diagnostics_for_both_mutabilities() {
    for head in ["#let", "#let-mut"] {
        for (specification, message) in [
            (
                "#u64 42u64",
                "delimited let binding requires literal '=' after the type",
            ),
            (
                "#u64",
                "delimited let binding requires literal '=' after the type",
            ),
            (
                "#u64 == 42u64",
                "delimited let binding requires literal '=' after the type",
            ),
            (
                "#u64 #= 42u64",
                "delimited let binding requires literal '=' after the type",
            ),
            (
                "#u64 \"=\" 42u64",
                "delimited let binding requires literal '=' after the type",
            ),
            (
                "#u64 (=) 42u64",
                "delimited let binding requires literal '=' after the type",
            ),
            (
                "#u64 '= 42u64",
                "delimited let binding requires literal '=' after the type",
            ),
            (
                "#u64 =",
                "delimited let binding requires an initializer after '='",
            ),
            (
                "#u64 = = 42u64",
                "delimited let binding has duplicate '=' delimiter",
            ),
            (
                "#u64 = 42u64 =",
                "delimited let binding has duplicate '=' delimiter",
            ),
            (
                "#u64 = 20u64 22u64",
                "delimited let binding requires exactly one initializer after '='",
            ),
        ] {
            let source = function(&format!(
                "    {head} count : {specification};\n    #return 0u64;"
            ));
            assert_eq!(diagnostic(&source).message, message, "{source}");
        }
    }
}

#[test]
fn delimiter_errors_point_at_the_malformed_or_missing_operand() {
    for (specification, token) in [
        ("#u64 #= 42u64", "#="),
        ("#u64 == 42u64", "=="),
        ("#u64 =", "="),
        ("#u64 = 42u64 =", "="),
        ("#u64 = 20u64 22u64", "22u64"),
    ] {
        let source = function(&format!(
            "    #let count : {specification};\n    #return 0u64;"
        ));
        let error = diagnostic(&source);
        // rfind distinguishes a duplicate delimiter from the valid first one.
        assert_span(&source, &error, token, source.rfind(token).unwrap());
    }
}

#[test]
fn type_errors_point_at_nested_initializer_in_functions_and_roots() {
    for head in ["#let", "#let-mut"] {
        let mut sources = vec![function(&format!(
            "    {head} count : #bool = 42u64;\n    #return 0u64;"
        ))];
        if head == "#let" {
            sources.push(format!("{head} count : #bool = 42u64;\n"));
        }
        for source in sources {
            let error = diagnostic(&source);
            assert!(
                error.message.contains("has type U64, expected Bool"),
                "{error:?}"
            );
            assert_span(&source, &error, "42u64", source.find("42u64").unwrap());
        }
    }
}

#[test]
fn shadowing_still_rejects_the_new_declaration_and_underlines_its_name() {
    let source = function(
        "    #let count : #u64 = 1u64;\n    #let-mut count : #u64 = count;\n    #return count;",
    );
    let error = diagnostic(&source);
    assert_eq!(
        error.message,
        "binding 'count' shadows an existing binding; shadowing is not allowed"
    );
    assert_span(
        &source,
        &error,
        "count",
        source.find("count : #u64 = count").unwrap(),
    );

    // A declaration inside the initializer precedes the enclosing declaration.
    let source = function(
        "    #let count : #u64 = (#block (#let count #u64 1u64) count);\n    #let count : #u64 = 2u64;\n    #return count;",
    );
    let error = diagnostic(&source);
    assert_span(
        &source,
        &error,
        "count",
        source.find("count : #u64 = 2u64").unwrap(),
    );
}

#[test]
fn borrowing_and_ownership_rules_apply_to_delimited_bindings() {
    let valid = function(
        r#"    #let-mut value : #u64 = 40u64;
    #let reference : (#ref-mut #u64) = (#borrow-mut value);
    #deref-set reference 42u64;
    #return (#deref reference);"#,
    );
    check_types(&parse_program(&valid).unwrap()).unwrap();

    let immutable =
        function("    #let value : #u64 = 40u64;\n    #set value 42u64;\n    #return value;");
    assert_eq!(
        diagnostic(&immutable).message,
        "cannot assign to immutable variable 'value'"
    );

    let conflict = function(
        r#"    #let-mut value : #u64 = 40u64;
    #let reference : (#ref #u64) = (#borrow value);
    #set value 42u64;
    #return (#deref reference);"#,
    );
    let error = diagnostic(&conflict);
    assert!(
        error
            .message
            .contains("cannot mutate 'value' while it is immutably borrowed"),
        "{error:?}"
    );

    let linear = format!(
        "#struct Resource (#linear) ((value #u64))\n{}",
        function(
            "    #let resource : Resource = (#struct-literal Resource ((value 1u64)));\n    #return 0u64;"
        )
    );
    let error = diagnostic(&linear);
    assert!(error.message.contains("linear"), "{error:?}");
}

#[test]
fn other_binding_forms_keep_their_existing_representation() {
    let source = "#const answer #u64 42u64\n#static counter #u64 0u64\n#enum Choice () ((Choice.Some #u64) Choice.None)\n#fn main { #params = (); #returns = #u64; #body = ((#let (#tuple left right) (#tuple #u64 #u64) (#tuple 20u64 22u64)) (#let choice Choice (Choice.Some left)) (#let-else (Choice.Some value) choice (#else (#return 0u64))) (#return (#u64::add-wrap value right))); }\n";
    check_types(&parse_program(source).unwrap()).unwrap();
    for head in ["#const", "#static"] {
        assert!(parse_program(&format!("{head} count : #u64 = 42u64;\n")).is_err());
    }
    let destructure = function(
        "    #let (#tuple left right) : (#tuple #u64 #u64) = (#tuple 20u64 22u64);\n    #return left;",
    );
    assert!(parse_program(&destructure).is_err());
}

#[test]
fn syntax_formatter_preserves_nested_binding_shape_and_comments() {
    let source = "(#let count (#u64 = (#block\n  // initializer stays nested\n  (#let inner #u64 42u64) inner)))";
    let formatted = lim::format_syntax(source).unwrap();
    assert!(formatted.contains("// initializer stays nested"));
    assert_eq!(
        lim::parse(source).unwrap()[0].expr,
        lim::parse(&formatted).unwrap()[0].expr
    );
    assert_eq!(lim::format_syntax(&formatted).unwrap(), formatted);
}
