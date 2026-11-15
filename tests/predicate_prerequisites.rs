mod support;
use std::{os::unix::process::ExitStatusExt, process::Command, time::Duration};

fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}
fn function(name: &str, params: &str, ret: &str, body: &str) -> String {
    format!("#fn {name} {{\n  #params = ({params});\n  #returns = {ret};\n  #body = ( {body}\n  );\n}}\n")
}
fn call(name: &str, parameter: &str, value: &str) -> String {
    format!("(#call {name} (({parameter} {value})))")
}
fn requires(name: &str, parameter: &str, value: &str) -> String {
    format!("(#requires {})", call(name, parameter, value))
}
fn chain() -> String {
    function("base", "(original #u64)", "#bool", "(#return (#u64::ne original 0u64))")
        + &function("middle", "(renamed #u64)", "#bool", &format!("{} (#return true)", requires("base", "original", "renamed")))
        + &function("outer", "(subject #u64)", "#bool", &format!("{} (#return true)", requires("middle", "renamed", "subject")))
        + &function("consume", "(input #u64)", "()", &format!("{} (#return ())", requires("outer", "subject", "input")))
}

#[test]
fn transitive_requirements_substitute_renamed_parameters() {
    let source = chain() + &function("forward", "(item #u64)", "()", &format!("{} {} {} (#return ())", requires("outer", "subject", "item"), call("base-user", "value", "item"), call("consume", "input", "item")))
        + &function("base-user", "(value #u64)", "()", &format!("{} (#return ())", requires("base", "original", "value")));
    check(&source).unwrap();
    let wrong = source.replace("(input item)", "(input 9u64)");
    assert!(check(&wrong).unwrap_err().contains("missing evidence"));
}

#[test]
fn direct_partial_predicate_calls_check_prerequisites_locally() {
    let source = chain() + &function("caller", "(item #u64)", "()", &format!("{} (#return ())", call("middle", "renamed", "item")));
    let error = check(&source).unwrap_err();
    assert!(error.contains("missing evidence") && error.contains("base"), "{error}");
    let valid = source.replace("#body = ( (#call middle", "#body = ( (#requires (#call base ((original item)))) (#call middle");
    check(&valid).unwrap();
}

#[test]
fn successful_validation_establishes_the_partial_predicate() {
    let source = chain() + &function("caller", "(item #u64)", "()", &format!("(#if-valid {} (#if-valid {} (#if-valid {} {}))) (#return ())", call("base", "original", "item"), call("middle", "renamed", "item"), call("outer", "subject", "item"), call("consume", "input", "item")));
    check(&source).unwrap();
    assert!(check(&source.replace("#if-valid", "#if")).unwrap_err().contains("missing evidence"));
    // The final validation cannot evaluate a partial predicate before its
    // prerequisite has been established, even when its body returns true.
    let missing = chain() + &function("caller", "(item #u64)", "()", &format!("(#if-valid {} ()) (#return ())", call("outer", "subject", "item")));
    assert!(check(&missing).unwrap_err().contains("missing evidence"));
}

#[test]
fn predicate_body_calls_do_not_widen_the_callers_interface() {
    let source = chain() + &function("hidden", "(item #u64)", "#bool", &format!("(#return {})", call("middle", "renamed", "item")));
    let error = check(&source).unwrap_err();
    assert!(error.contains("contract in 'hidden'") && error.contains("missing evidence"), "{error}");
}

#[test]
fn predicate_bodies_do_not_supply_comparison_facts() {
    let source = chain() + &function("numeric-user", "(item #u64)", "()", "(#requires (#u64::ne item 0u64)) (#return ())")
        + &function("caller", "(item #u64)", "()", &format!("{} {} (#return ())", requires("outer", "subject", "item"), call("numeric-user", "item", "item")));
    assert!(check(&source).unwrap_err().contains("missing evidence"));
}

#[test]
fn removing_roots_preserves_only_explicit_or_shared_prerequisites() {
    let declarations = chain()
        + &function("sibling", "(value #u64)", "#bool", &format!("{} (#return true)", requires("base", "original", "value")))
        + &function("base-user", "(value #u64)", "()", &format!("{} (#return ())", requires("base", "original", "value")));
    let root = requires("outer", "subject", "item");
    let explicit = requires("base", "original", "item");
    let shared = requires("sibling", "value", "item");
    for remaining in [&explicit, &shared] {
        let source = declarations.clone() + &function("caller", "(item #u64)", "()", &format!("{root} {remaining} {} (#return ())", call("base-user", "value", "item")));
        check(&source).unwrap();
        check(&source.replace(&root, "")).unwrap();
    }
    let source = declarations + &function("caller", "(item #u64)", "()", &format!("{root} {} (#return ())", call("base-user", "value", "item")));
    check(&source).unwrap();
    assert!(check(&source.replace(&root, "")).unwrap_err().contains("missing evidence"));
}

#[test]
fn missing_fact_diagnostic_retains_call_root_and_prerequisite_spans() {
    let source = chain() + &function("caller", "(item #u64)", "()", &format!("{} (#return ())", call("consume", "input", "item")));
    let scratch = support::Scratch::new("prerequisite-diagnostic");
    let error = lim::compile_source_to_assembly(&source, &scratch.path().join("input.lim"), &lim::CompileConfig::default(), &scratch.path().join("cache"), lim::TargetDescription::X86_64_SYSTEM_V).unwrap_err();
    assert!(error.message.contains("missing evidence") && error.message.contains("base"), "{error:?}");
    let primary = error.span.unwrap();
    assert_eq!(&source[primary.start..primary.end], call("consume", "input", "item"));
    let labels = error.labels.iter().map(|label| (&source[label.span.start..label.span.end], label.message.as_str())).collect::<Vec<_>>();
    assert_eq!(labels.len(), 3, "{error:?}");
    assert_eq!(labels[0].0, call("outer", "subject", "input"));
    assert!(labels[0].1.contains("root requirement"));
    assert_eq!(labels[1].0, call("middle", "renamed", "subject"));
    assert_eq!(labels[2].0, call("base", "original", "renamed"));
}

#[test]
fn prerequisite_cycles_are_rejected_even_when_unused() {
    for cycle in [
        function("cycle", "(item #u64)", "#bool", &format!("{} (#return true)", requires("cycle", "item", "item"))),
        function("left", "(first #u64)", "#bool", &format!("{} (#return true)", requires("right", "second", "first")))
            + &function("right", "(second #u64)", "#bool", &format!("{} (#return true)", requires("left", "first", "second"))),
    ] {
        let error = check(&cycle).unwrap_err();
        assert!(error.contains("cyclic predicate prerequisites"), "{error}");
    }
}

#[test]
fn prerequisite_depth_and_syntax_growth_exhaust_bounded_work() {
    let mut depth = function("predicate-0", "(item #u64)", "#bool", "(#return true)");
    for level in 1..70 {
        depth += &function(&format!("predicate-{level}"), "(item #u64)", "#bool", &format!("{} (#return true)", requires(&format!("predicate-{}", level - 1), "item", "item")));
    }
    assert!(check(&depth).unwrap_err().contains("prerequisite expansion budget"));
    let mut growth = function("predicate-0", "(item #u64)", "#bool", "(#return true)");
    for level in 1..18 {
        growth += &function(&format!("predicate-{level}"), "(item #u64)", "#bool", &format!("{} (#return true)", requires(&format!("predicate-{}", level - 1), "item", "(#u64::add-wrap item item)")));
    }
    assert!(check(&growth).unwrap_err().contains("prerequisite expansion budget"));
}

#[test]
fn shared_diamonds_do_not_enumerate_exponential_paths() {
    let mut source = function("left-0", "(item #u64)", "#bool", "(#return true)")
        + &function("right-0", "(item #u64)", "#bool", "(#return true)");
    for level in 1..12 {
        for side in ["left", "right"] {
            source += &function(&format!("{side}-{level}"), "(item #u64)", "#bool", &format!("{} {} (#return true)", requires(&format!("left-{}", level - 1), "item", "item"), requires(&format!("right-{}", level - 1), "item", "item")));
        }
    }
    source += &function("caller", "(item #u64)", "()", &format!("{} {} (#return ())", requires("left-11", "item", "item"), call("right-0", "item", "item")));
    check(&source).unwrap();
}

#[test]
fn mutation_invalidates_prerequisites_and_dependent_predicate_facts() {
    let source = function("base", "(value (#ref #u64))", "#bool", "(#return (#u64::ne (#deref value) 0u64))")
        + &function("partial", "(value (#ref #u64))", "#bool", &format!("{} (#return true)", requires("base", "value", "value")))
        + &function("consume", "(value (#ref #u64))", "()", &format!("{} (#return ())", requires("partial", "value", "value")))
        + &function("caller", "(value (#ref-mut #u64))", "()", &format!("{} (#deref-set value 0u64) {} (#return ())", requires("partial", "value", "value"), call("consume", "value", "value")));
    assert!(check(&source).unwrap_err().contains("missing evidence"));
    check(&source.replace("(#deref-set value 0u64)", "")).unwrap();
    // Re-establishing base alone must not resurrect partial's old evidence,
    // whose prerequisite read was invalidated even though its own body is true.
    let revalidated = source.replace("(#deref-set value 0u64)", "(#deref-set value 0u64) (#assume (#call base ((value value))))");
    let error = check(&revalidated).unwrap_err();
    assert!(error.contains("missing evidence") && error.contains("partial"), "{error}");
}

fn run(source: &str, instrumented: bool) -> std::process::ExitStatus {
    let scratch = support::Scratch::new("prerequisite-runtime");
    let mut config = lim::CompileConfig::default();
    if instrumented { config.set("contracts", "check"); }
    let assembly = lim::compile_source_to_assembly(source, &scratch.path().join("main.lim"), &config, &scratch.path().join("cache"), lim::TargetDescription::X86_64_SYSTEM_V).unwrap_or_else(|error| panic!("{}", error.message));
    let executable = scratch.path().join("program");
    lim::link_native_binary(&assembly, &executable, &[], &[], lim::TargetDescription::X86_64_SYSTEM_V).unwrap();
    support::run(&mut Command::new(executable), Duration::from_secs(5), 4096).unwrap().0
}

#[test]
fn checked_contracts_assert_prerequisites_before_partial_predicates() {
    let source = function("partial", "(item #u64)", "#bool", "(#requires (#u64::ne item 0u64)) (#return (#u64::eq (#u64::div-wrap 42u64 item) 42u64))")
        + &function("consume", "(item #u64)", "()", &format!("{} (#return ())", requires("partial", "item", "item")))
        + &function("main", "", "#u64", &format!("(#let item #u64 0u64) (#assume (#u64::ne item 0u64)) (#assume {}) {} (#return 42u64)", call("partial", "item", "item"), call("consume", "item", "item")));
    assert_eq!(run(&source, false).code(), Some(42));
    // A failed prerequisite assertion traps with SIGILL before division by zero
    // in the partial predicate could raise SIGFPE.
    assert_eq!(run(&source, true).signal(), Some(4));
    assert_eq!(run(&source.replace("#let item #u64 0u64", "#let item #u64 1u64"), true).code(), Some(42));
}

#[test]
fn partial_predicate_promises_remain_promises_and_do_not_imply_prerequisites() {
    let promised = chain() + &function("promise", "(item #u64)", "()", &format!("(#ensures {}) (#return ())", call("outer", "subject", "item")));
    check(&promised).unwrap();
    let caller = function("caller", "(item #u64)", "()", &format!("{} {} (#return ())", call("promise", "item", "item"), call("consume", "input", "item")));
    let error = check(&(promised + &caller)).unwrap_err();
    assert!(error.contains("missing evidence") && error.contains("base"), "{error}");
}

#[test]
fn partial_predicate_requirements_keep_purity_and_boolean_guards() {
    let base = function("base", "(item #u64)", "#bool", "(#return true)");
    let not_boolean = base.clone() + &function("partial", "(item #u64)", "#u64", &format!("{} (#return item)", requires("base", "item", "item")))
        + &function("consume", "(item #u64)", "()", &format!("{} (#return ())", requires("partial", "item", "item")));
    assert!(check(&not_boolean).unwrap_err().contains("#bool"));
    let impure = base + &function("partial", "(item #u64) (value (#ref-mut #u64))", "#bool", &format!("{} (#deref-set value item) (#return true)", requires("base", "item", "item")))
        + &function("consume", "(item #u64) (value (#ref-mut #u64))", "()", "(#requires (#call partial ((item item) (value value)))) (#return ())");
    let error = check(&impure).unwrap_err();
    assert!(error.contains("impure") || error.contains("must be pure"), "{error}");
}

#[test]
fn substitution_preserves_relational_argument_positions_and_named_call_order() {
    let source = function("before", "(first #u64) (second #u64)", "#bool", "(#return (#u64::lt first second))")
        + &function("partial", "(low #u64) (high #u64)", "#bool", "(#requires (#call before ((second low) (first high)))) (#return true)")
        + &function("consume", "(x #u64) (y #u64)", "()", "(#requires (#call partial ((high x) (low y)))) (#return ())")
        + &function("caller", "(a #u64) (b #u64)", "()", "(#requires (#call before ((first a) (second b)))) (#assume (#call partial ((high a) (low b)))) (#call consume ((y b) (x a))) (#return ())");
    check(&source).unwrap();
    let error = check(&source.replace("(first a) (second b)", "(first b) (second a)")).unwrap_err();
    assert!(error.contains("missing evidence") && error.contains("before"), "{error}");
}

#[test]
fn constrained_partial_predicates_require_domain_evidence_at_checked_boundaries() {
    // Both predicates always return true: these are honest promises and
    // assumptions. Their bodies cannot supply the separately required evidence.
    let declarations = function("domain", "(value #u64)", "#bool", "(#return true)")
        + &function("partial", "(subject #u64)", "#bool", "(#requires (#call domain ((value subject)))) (#return true)")
        + "#type Accepted (#where (value #u64) (#call partial ((subject value))))\n"
        + &function("promise", "(item #u64)", "()", "(#ensures (#call partial ((subject item)))) (#return ())")
        + &function("domain-user", "(value #u64)", "()", "(#requires (#call domain ((value value)))) (#return ())");
    check(&declarations).unwrap();
    for evidence in [
        "(#call promise ((item item)))",
        "(#assume (#call partial ((subject item))))",
    ] {
        // Establishing only P remains permitted. It neither establishes Q nor
        // creates a new caller obligation until a checked boundary consumes it.
        check(&(declarations.clone() + &function("caller", "(item #u64)", "()", &format!("{evidence} (#return ())")))).unwrap();
        let binding = format!("{evidence} (#let accepted Accepted item) (#forget accepted) (#return ())");
        let error = check(&(declarations.clone() + &function("caller", "(item #u64)", "()", &binding))).unwrap_err();
        assert!(error.contains("missing evidence") && error.contains("domain"), "{error}");
        let valid = format!("(#requires (#call domain ((value item)))) {binding}");
        check(&(declarations.clone() + &function("caller", "(item #u64)", "()", &valid))).unwrap();
    }

    // A parameter constraint already supplies Q at entry and checks Q at calls.
    let forward = function("forward", "(item Accepted)", "()", "(#call domain-user ((value item))) (#return ())");
    check(&(declarations.clone() + &forward)).unwrap();
    let error = check(&(declarations.clone() + &forward + &function("caller", "(item #u64)", "()", "(#call promise ((item item))) (#call forward ((item item))) (#return ())"))).unwrap_err();
    assert!(error.contains("missing evidence") && error.contains("domain"), "{error}");

    // An explicit promise of P still cannot discharge a constrained return's Q.
    let promised_result = function("create", "(item #u64)", "Accepted", "(#ensures (#call partial ((subject (#result))))) (#return item)");
    let error = check(&(declarations.clone() + &promised_result)).unwrap_err();
    assert!(error.contains("missing evidence") && error.contains("domain"), "{error}");

    // Checked constrained results export their complete verified type contract.
    let checked_result = function("create", "(item #u64)", "Accepted", "(#assume (#call domain ((value item)))) (#assume (#call partial ((subject item)))) (#return item)");
    let use_result = function("caller", "(item #u64)", "()", "(#let accepted Accepted (#call create ((item item)))) (#call domain-user ((value accepted))) (#return ())");
    check(&(declarations.clone() + &checked_result + &use_result)).unwrap();

    // Restoration checks and exports the same closure after a real write.
    let edit = function("edit", "(value (#ref-mut Accepted))", "()", "(#deref-set value 7u64) (#assume (#call domain ((value (#deref value))))) (#assume (#call partial ((subject (#deref value))))) (#return ())");
    let use_edit = function("caller", "(value (#ref-mut Accepted))", "()", "(#call edit ((value value))) (#return ())");
    check(&(declarations.clone() + &edit + &use_edit)).unwrap();
    let missing_restore = edit.replace("(#assume (#call domain ((value (#deref value)))))", "");
    let error = check(&(declarations + &missing_restore)).unwrap_err();
    assert!(error.contains("missing evidence") && error.contains("domain"), "{error}");
}
