mod support;

fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}

const INCREMENT: &str = "#fn increment {
  #params = #u64;
  #returns = #u64;
  #body: #return [#u64 #wrap; #arg + 1u64];
}\n";

fn main(body: &str) -> String {
    format!("#fn main {{ #params = {{}}; #returns = #u64; #body = ({body}); }}")
}

#[test]
fn implicit_and_explicit_positional_calls_have_the_declared_type() {
    for call in [
        "(increment 41u64)",
        "(#call increment 41u64)",
        "(increment (#u64::add-wrap 20u64 21u64))",
    ] {
        check(&(INCREMENT.to_owned() + &main(&format!("(#return {call})")))).unwrap();
    }
    let error = check(&(INCREMENT.to_owned() + &main("(#return (increment false))"))).unwrap_err();
    assert!(
        error.contains("expected") && error.contains("U64"),
        "{error}"
    );
}

#[test]
fn copy_parameters_can_be_read_more_than_once() {
    check(
        "#fn double { #params = #u64; #returns = #u64; #body: #return [#u64 #wrap; #arg + #arg]; }",
    )
    .unwrap();
}

#[test]
fn named_functions_still_require_named_arguments() {
    let source =
        "#fn named { #params = { value = #u64; }; #returns = #u64; #body: #return value; }\n";
    assert!(check(&(source.to_owned() + &main("(#return (named 42u64))"))).is_err());
    check(&(source.to_owned() + &main("(#return (named { value = 42u64; }))"))).unwrap();
    assert!(
        check(&(INCREMENT.to_owned() + &main("(#return (increment { value = 41u64; }))"))).is_err()
    );
}

#[test]
fn arg_is_bare_and_only_in_plain_type_parameter_functions() {
    for params in ["{}", "()", "{ value = #u64; }"] {
        let source =
            format!("#fn invalid {{ #params = {params}; #returns = #u64; #body: #return #arg; }}");
        let error = check(&source).unwrap_err();
        assert!(error.contains("#arg"), "{error}");
    }
    for expression in ["(#arg)", "(#arg 1u64)"] {
        let error = check(&INCREMENT.replace("[#u64 #wrap; #arg + 1u64]", expression)).unwrap_err();
        assert!(error.contains("bare #arg"), "{error}");
    }
    assert!(check("#const value #u64 #arg").is_err());
    let error = check("#fn invalid { #params = #u64; #returns = #u64; #body = ((#let #arg #u64 0u64) (#return #arg)); }").unwrap_err();
    assert!(
        error.contains("#arg") && error.contains("reserved"),
        "{error}"
    );
}

#[test]
fn linear_parameters_must_be_consumed_once() {
    let prefix = "#struct Owned (#linear) ((value #u64))\n";
    let valid = "#fn take { #params = Owned; #returns = #u64; #body = ((#let result #u64 (#get #arg value)) (#forget #arg) (#return result)); }";
    check(&(prefix.to_owned() + valid)).unwrap();
    assert!(check(&(prefix.to_owned() + &valid.replace("(#forget #arg)", ""))).is_err());
    assert!(
        check(
            &(prefix.to_owned()
                + &valid.replace("(#forget #arg)", "(#forget #arg) (#forget #arg)"))
        )
        .is_err()
    );
}

#[test]
fn references_retain_borrow_origins_across_positional_calls() {
    let prefix =
        "#fn identity { #params = (#ref #u64); #returns = (#ref #u64); #body: #return #arg; }\n";
    let body = "(#let-mut value #u64 42u64) (#let reference (#ref #u64) (identity (#borrow value))) (#return (#deref reference))";
    check(&(prefix.to_owned() + &main(body))).unwrap();
    let invalid = body.replace("(#return", "(#set value 0u64) (#return");
    assert!(check(&(prefix.to_owned() + &main(&invalid))).is_err());
    check("#fn view { #params = (#ref-mut #u64); #returns = (#ref #u64); #body: #return (#borrow (#deref #arg)); }").unwrap();
    assert!(
        check(
            "#fn invalid { #params = #u64; #returns = (#ref #u64); #body: #return (#borrow #arg); }"
        )
        .is_err()
    );
}

#[test]
fn positional_arguments_do_not_erase_unsafe_call_requirements() {
    let source = INCREMENT.replace("#fn increment", "#unsafe-fn increment");
    check(&(source.clone() + &main("(#return (#unsafe (#unsafe-call increment 41u64)))"))).unwrap();
    assert!(check(&(source.clone() + &main("(#return (#unsafe-call increment 41u64))"))).is_err());
    assert!(check(&(source + &main("(#return (#unsafe (increment 41u64)))"))).is_err());
}

#[test]
fn generators_can_emit_positional_functions() {
    let source =
        "#gn make (name) `((#fn ,name #u64 #u64 (#return #arg)))\n#generate make identity\n";
    check(&(source.to_owned() + &main("(#return (identity 42u64))"))).unwrap();
}

#[test]
fn aliased_positional_functions_keep_file_local_types() {
    let scratch = support::Scratch::new("positional-alias");
    std::fs::write(scratch.path().join("value.lim"), "#type Number #u64\n#fn identity { #params = Number; #returns = Number; #body: #return #arg; }").unwrap();
    let source = "#alias identity = ./value.lim::identity\n".to_owned()
        + &main("(#return (identity 42u64))");
    let program = lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn positional_syntax_formats_without_changing_semantics() {
    let source = INCREMENT.to_owned() + &main("(#return (increment 41u64))");
    let formatted = lim::format_source(&source).unwrap();
    assert_eq!(formatted, lim::format_source(&formatted).unwrap());
    let trees = |s: &str| {
        lim::parse_source_unit(s)
            .unwrap()
            .into_iter()
            .map(|n| n.expr)
            .collect::<Vec<_>>()
    };
    assert_eq!(trees(&source), trees(&formatted));
}

#[test]
fn positional_calls_execute_once_with_normal_native_lowering() {
    use std::{process::Command, time::Duration};
    let scratch = support::Scratch::new("positional-native");
    let next = "#fn next { #params = (#ref-mut #u64); #returns = #u64; #body = ((#deref-set #arg (#u64::add-wrap (#deref #arg) 1u64)) (#return 41u64)); }\n";
    let source = INCREMENT.to_owned()
        + next
        + &main(
            "(#let-mut count #u64 0u64) (#let answer #u64 (increment (next (#borrow-mut count)))) (#assert (#u64::eq count 1u64)) (#return answer)",
        );
    let assembly = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(3), 1024).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}

#[test]
fn positional_type_errors_underline_the_argument() {
    let scratch = support::Scratch::new("positional-diagnostic");
    for call in ["(increment false)", "(#call increment false)"] {
        let source = INCREMENT.to_owned() + &main(&format!("(#return {call})"));
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "false", "{error:?}");
    }
}

#[test]
fn positional_predicates_preserve_contract_and_refinement_obligations() {
    let predicate =
        "#fn positive { #params = #u64; #returns = #bool; #body: #return [#u64; #arg > 0u64]; }\n";
    let consume = "#fn consume { #params = #u64; #returns = #u64; #requires: (positive #arg); #body: #return #arg; }\n";
    let body =
        "(#let input #u64 42u64) (#return (#if-valid (positive input) (consume input) 0u64))";
    check(&(predicate.to_owned() + consume + &main(body))).unwrap();
    assert!(check(&(predicate.to_owned() + consume + &main("(#return (consume 42u64))"))).is_err());
    let refined = "#fn consume { #params = (#where (item #u64) (positive item)); #returns = #u64; #body: #return #arg; }\n";
    check(&(predicate.to_owned() + refined + &main(body))).unwrap();
    assert!(check(&(predicate.to_owned() + refined + &main("(#return (consume 42u64))"))).is_err());
}
