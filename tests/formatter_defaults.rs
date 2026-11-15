use lim::{format_source, format_syntax, parse, parse_source_unit, Expr};

fn source_trees(source: &str) -> Vec<Expr> {
    parse_source_unit(source).unwrap().into_iter()
        .map(|node| node.expr)
        .collect()
}

fn formatted(source: &str) -> String {
    let output = format_source(source).unwrap();
    assert_eq!(source_trees(source), source_trees(&output), "{output}");
    assert_eq!(format_source(&output).unwrap(), output);
    output
}

fn syntax(source: &str) -> String {
    let output = format_syntax(source).unwrap();
    let trees = |source: &str| {
        parse(source).unwrap().into_iter().map(|node| node.expr).collect::<Vec<_>>()
    };
    assert_eq!(trees(source), trees(&output), "{output}");
    assert_eq!(format_syntax(&output).unwrap(), output);
    output
}

#[test]
fn function_records_use_two_space_sections_by_default() {
    let output = formatted("#fn main {#params=();#returns=#u64;#body=((#return 42u64));}\n");
    assert_eq!(output, "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ((#return 42u64));\n}\n");
}

#[test]
fn simple_records_calls_and_infix_expressions_stay_compact() {
    assert_eq!(syntax("{value=42u64;}"), "{ value = 42u64; }\n");
    assert_eq!(syntax("read {value=42u64;}"), "read { value = 42u64; }\n");
    assert_eq!(syntax("[#u64 #wrap ; 20u64   + 22u64]"), "[#u64 #wrap; 20u64 + 22u64]\n");
    assert_eq!(syntax("{left=20u64;right=22u64;}"), "{ left = 20u64; right = 22u64; }\n");
}

#[test]
fn colon_bodies_and_nested_loops_normalize_indentation_without_rewriting_layout() {
    let source = "#fn main {\n        #params=();\n        #returns=#u64;\n        #body:\n                #let-mut count : #u64 = 0u64;\n                #while [#u64; count < 3u64]:\n                        #set count [#u64 #wrap; count + 1u64];\n                #return count;\n}\n";
    let output = formatted(source);
    assert_eq!(output, "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body:\n    #let-mut count : #u64 = 0u64;\n    #while [#u64; count < 3u64]:\n      #set count [#u64 #wrap; count + 1u64];\n    #return count;\n}\n");
}

#[test]
fn compound_loops_have_clear_body_lines_and_keep_explicit_returns() {
    let source = "#fn main {#params=();#returns=#u64;#body=((#let-mut count #u64 0u64) (#while (#u64::lt count 3u64) (#set count (#u64::add-wrap count 1u64)) (#println count)) (#return count));}\n";
    let output = formatted(source);
    assert!(output.contains("\n    (#while (#u64::lt count 3u64)\n"), "{output}");
    assert!(output.contains("\n      (#set count (#u64::add-wrap count 1u64))\n"), "{output}");
    assert!(output.contains("(#return count)"), "{output}");
    assert!(output.lines().all(|line| line.chars().count() <= 100), "{output}");
}

#[test]
fn long_infix_expressions_wrap_near_one_hundred_columns() {
    let terms = (1..=30).map(|value| format!("{value}u64")).collect::<Vec<_>>().join(" + ");
    let source = format!("#fn main {{ #params = (); #returns = #u64; #body = ((#return [#u64 #wrap; {terms}])); }}\n");
    let output = formatted(&source);
    assert!(output.lines().all(|line| line.chars().count() <= 100), "{output}");
    assert!(output.lines().any(|line| line.chars().count() >= 75), "{output}");
    assert!(output.lines().count() < 15, "operands should fill lines: {output}");
}

#[test]
fn delimited_bindings_keep_their_nested_specifications() {
    let source = "#fn main {#params=();#returns=#u64;#body=(#let count : #u64 = 42u64; #let-mut copy : #u64 = (#u64::add-wrap count 0u64); #return copy;);}\n";
    let output = formatted(source);
    assert!(output.contains("#let count : #u64 = 42u64;"), "{output}");
    assert!(output.contains("#let-mut copy : #u64 = (#u64::add-wrap count 0u64);"), "{output}");
    assert!(output.contains("#return copy;"), "{output}");
}

#[test]
fn multiline_grouped_initializers_keep_their_semantic_boundaries() {
    formatted("#fn main {\n      #params = ();\n      #returns = #u64;\n      #body = (\n        #let count : #u64 = (#u64::add-wrap\n            20u64\n            22u64);\n        #return count;\n      );\n}\n");
}

#[test]
fn comments_and_interior_blank_lines_survive_default_layout() {
    let source = "#fn main {\n      // inputs stay empty\n      #params=();\n\n      #returns=#u64; // explicit result type\n      #body=(\n          // keep this before the return\n          (#return 42u64)\n      );\n}\n// final note\n";
    let output = formatted(source);
    for comment in [
        "// inputs stay empty",
        "// explicit result type",
        "// keep this before the return",
        "// final note",
    ] {
        assert_eq!(output.matches(comment).count(), 1, "{output}");
    }
    assert!(output.contains("\n\n"), "{output}");
    assert!(output.find("// keep this before the return").unwrap() < output.find("#return").unwrap());
}

#[test]
fn multiline_literals_keep_every_byte_including_trailing_spaces() {
    let literal = "\"first line  \n        second line\n  final line  \"";
    let source = format!("#fn main {{ #params=(); #returns=(); #body=((#println {literal}) (#return ())); }}\n");
    let output = formatted(&source);
    assert!(output.contains(literal), "{output:?}");
}

#[test]
fn generator_quoted_data_keeps_authored_spelling_and_layout() {
    let template = "`((#type ,name #u64)\n          // template comment\n          (#fn helper () #u64 (#return 0x2au64)))";
    let source = format!("#gn make (name) {template}\n");
    let output = formatted(&source);
    assert!(output.contains(template), "{output}");
    assert!(syntax(&format!("'{template}")).contains(template));
}

#[test]
fn numeric_character_and_string_spellings_are_not_rewritten() {
    let source = r#"#fn main { #params=(); #returns=(); #body=((#println "not // a comment; : [ ]") (#println #\😀) (#println 0x2au64) (#return ())); }
"#;
    let output = formatted(source);
    for literal in [r#""not // a comment; : [ ]""#, "#\\😀", "0x2au64"] {
        assert!(output.contains(literal), "{output}");
    }
}

#[test]
fn canonical_lisp_forms_still_use_the_existing_formatter() {
    assert_eq!(syntax("(#let   count #u64   42u64)"), "(#let count #u64 42u64)\n");
    let source = "(#loop (#let-mut value #u64 0u64) (#set value 42u64) (#break))";
    assert!(syntax(source).contains("(#set value 42u64)"));
}

#[test]
fn blank_lines_between_root_forms_are_preserved() {
    let source = "#type First #u64\n\n\n#type Second #u64\n";
    assert_eq!(formatted(source), source);
}

#[test]
fn long_simple_parameter_lists_fill_lines_instead_of_expanding_each_item() {
    let parameters = (0..12).map(|index| format!("(value{index} #u64)"))
        .collect::<Vec<_>>().join(" ");
    let source = format!("#fn many {{ #params = ({parameters}); #returns = #u64; #body = ((#return value0)); }}\n");
    let output = formatted(&source);
    assert!(output.lines().all(|line| line.chars().count() <= 100), "{output}");
    assert!(output.lines().count() < 12, "{output}");
    assert!(output.lines().any(|line| line.matches("#u64)").count() > 2), "{output}");
}

#[test]
fn single_body_canonical_loops_put_the_body_below_the_header() {
    for (statement, header) in [
        ("(#while false (#break))", "(#while false"),
        ("(#for () false () (#break))", "(#for () false ()"),
        ("(#loop (#break))", "(#loop"),
        (
            "(#for-range (index #u64) 0u64 3u64 (#break))",
            "(#for-range (index #u64) 0u64 3u64",
        ),
    ] {
        // The function record selects surface formatting while the loop itself
        // retains canonical Lisp syntax and has exactly one body operand.
        let source = format!(
            "#fn main {{ #params = (); #returns = #u64; #body = ({statement} (#return 0u64)); }}\n"
        );
        let output = formatted(&source);
        let expected = format!("    {header}\n      (#break)\n    )");
        assert!(output.contains(&expected), "{statement}: {output}");
    }
}
