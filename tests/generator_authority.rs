mod support;
use std::{fs, path::Path};

fn write(base: &Path, path: &str, source: &str) {
    let path = base.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

fn check_modes(base: &Path, source: &str, error: Option<&str>) {
    for mode in 0..3 {
        let (program, report) = lim::with_cache_report(|| {
            if mode == 0 {
                lim::parse_program_from_path(source, &base.join("main.lim"))
            } else {
                lim::parse_program_from_path_with_config_and_cache(
                    source,
                    &base.join("main.lim"),
                    &lim::CompileConfig::default(),
                    &base.join(".lim/cache"),
                )
            }
        });
        let result = program.and_then(|program| lim::check_types(&program));
        if let Some(expected) = error {
            let message = result.expect_err("caller syntax acquired library authority");
            assert!(message.contains(expected), "mode {mode}: {message}");
        } else {
            result.unwrap_or_else(|message| panic!("mode {mode}: {message}"));
            if mode == 2 {
                let report = lim::lsp::json::parse(&report).unwrap();
                assert!(
                    report
                        .get("events")
                        .unwrap()
                        .array()
                        .unwrap()
                        .iter()
                        .any(
                            |event| event.get("kind").and_then(lim::lsp::json::Json::string)
                                == Some("syntax")
                                && event.get("decision").and_then(lim::lsp::json::Json::string)
                                    == Some("hit")
                        ),
                    "expected a real generator cache hit: {report:?}"
                );
            }
        }
    }
}

const HELPERS: &str = r#"
(#export make dynamic splice field forwarded)
(#fn secret () #u64 (#return 42u64))
(#struct Value (#linear) (: capacity #u64))
(#gn-fn echo (body) body)
(#gn make (name) `((#fn ,name () #u64 (#return (#call secret ())))))
(#gn dynamic (name text) `((#fn ,name () #u64 (#return (#call ,(#gn-symbol text) ())))))
(#gn splice (name parameter body) `((#fn ,name (: ,parameter (#ref Value)) #u64 (#return ,body))))
(#gn field (name member) `((#fn ,name (: value (#ref Value)) #u64 (#return (#get value ,member)))))
(#gn forwarded (name bodies) `((#fn ,name () #u64 (#return ,(#gn-call echo (#gn-first (#gn-rest bodies)))))))
"#;

#[test]
fn template_references_can_call_private_runtime_helpers_and_run() {
    let scratch = support::Scratch::new("generator-template-authority");
    write(scratch.path(), "library/lib.lim", HELPERS);
    let source = "(#import-external \"library/lib.lim\" lib) (#generate lib@make read-generated) (#fn main () #u64 (#return (#call read-generated ())))";
    check_modes(scratch.path(), source, None);
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::host().unwrap(),
    )
    .unwrap();
    assert_eq!(
        std::process::Command::new(binary).status().unwrap().code(),
        Some(42)
    );
}

#[test]
fn generator_can_deliberately_construct_a_private_runtime_reference() {
    let scratch = support::Scratch::new("generator-manufactured-callee");
    write(scratch.path(), "library/lib.lim", HELPERS);
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@dynamic read-generated \"lib@secret\") (#fn main () #u64 (#return 0u64))", None);
}

#[test]
fn literal_selectors_are_data_but_private_function_references_are_checked_early() {
    let scratch = support::Scratch::new("generator-spliced-authority");
    write(scratch.path(), "library/lib.lim", HELPERS);
    for invocation in [
        "(#generate lib@splice read-generated value (#get value lib@capacity))",
        "(#generate lib@field read-generated lib@capacity)",
    ] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) {invocation} (#fn main () #u64 (#return 0u64))"), None);
    }
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@forwarded read-generated (() (#call @lib@secret ()))) (#fn main () #u64 (#return 0u64))", Some("private"));
}

#[test]
fn library_authored_projection_can_access_its_private_representation() {
    let scratch = support::Scratch::new("generator-template-fields");
    write(scratch.path(), "library/lib.lim", "(#export make) (#struct Value (#linear) (: capacity #u64)) (#gn make (name) `((#fn ,name (: value (#ref Value)) #u64 (#return (#get value capacity)))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make read-generated) (#fn main () #u64 (#return 0u64))", None);
}

#[test]
fn generator_can_interpret_literal_field_names_in_its_own_representation() {
    let scratch = support::Scratch::new("generator-untrusted-constructor-fields");
    write(scratch.path(), "library/lib.lim", "(#export make) (#struct Value (#linear) (: capacity #u64)) (#gn make (name fields) `((#fn ,name () #u64 (#let value Value (#struct-literal Value ,fields)) (#forget value) (#return 0u64))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read ((lib@capacity 42u64))) (#fn main () #u64 (#return 0u64))", None);
}

#[test]
fn helper_authorship_is_preserved_without_granting_transitive_private_access() {
    let scratch = support::Scratch::new("generator-transitive-authority");
    write(scratch.path(), "leaf/lib.lim", "(#export make public) (#fn secret () #u64 (#return 42u64)) (#fn public () #u64 (#return 1u64)) (#gn-fn implementation (name) `((#fn ,name () #u64 (#return (#call secret ()))))) (#gn make (name) (#gn-call implementation name))");
    write(scratch.path(), "middle/lib.lim", "(#export make public-call forbidden) (#import-external \"../leaf/lib.lim\" leaf) (#gn make (name) `((#generate leaf@make ,name))) (#gn public-call (name) `((#fn ,name () #u64 (#return (#call leaf@public ()))))) (#gn forbidden (name) `((#fn ,name () #u64 (#return (#call leaf@secret ())))))");
    for generator in ["make", "public-call"] {
        check_modes(scratch.path(), &format!("(#import-external \"middle/lib.lim\" lib) (#generate lib@{generator} generated-read) (#fn main () #u64 (#return (#call generated-read ())))"), None);
    }
    check_modes(scratch.path(), "(#import-external \"middle/lib.lim\" lib) (#generate lib@forbidden generated-read) (#fn main () #u64 (#return 0u64))", Some("private"));
}

#[test]
fn copied_generated_headers_cannot_grant_authority() {
    let scratch = support::Scratch::new("generator-authority-not-source");
    write(scratch.path(), "library/lib.lim", HELPERS);
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read) (#fn main () #u64 (#return 0u64))", None);
    let artifact = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .find(|source| source.contains("#generated-context"))
        .unwrap();
    check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib)\n{artifact}\n(#fn main () #u64 (#return 0u64))"), Some("compiler-owned"));
}

#[test]
fn authored_construction_and_enum_patterns_keep_representation_authority() {
    let scratch = support::Scratch::new("generator-authority-constructors");
    write(scratch.path(), "library/lib.lim", "(#export make) (#struct Value (#linear) (: capacity #u64)) (#enum Choice () (Choice.Ready)) (#gn make (name) `((#fn ,name () #u64 (#let value Value (#struct-literal Value (: capacity 42u64))) (#let answer #u64 (#get (#borrow value) capacity)) (#forget value) (#let choice Choice (#enum-literal Choice.Ready)) (#return (#match choice (#case Choice.Ready answer))))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read) (#fn main () #u64 (#return (#call generated-read ())))", None);
}

#[test]
fn generated_code_can_use_deliberately_derived_names_and_literal_statement_lists() {
    let scratch = support::Scratch::new("generator-derived-authority");
    write(scratch.path(), "library/lib.lim", "(#export append splice) (#fn Secret::read () #u64 (#return 42u64)) (#struct Value (#linear) (: capacity #u64)) (#gn append (name base) `((#fn ,name () #u64 (#return (#call ,(#gn-symbol-append base \"read\") ()))))) (#gn splice (name parameter body) `((#fn ,name (: ,parameter (#ref Value)) #u64 ,@body)))");
    for invocation in [
        "(#generate lib@append generated-read lib@Secret)",
        "(#generate lib@splice generated-read value ((#return (#get value lib@capacity))))",
    ] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) {invocation} (#fn main () #u64 (#return 0u64))"), None);
    }
}

#[test]
fn identical_literals_from_one_definition_module_deduplicate() {
    let scratch = support::Scratch::new("generator-authority-dedup");
    write(scratch.path(), "library/lib.lim", "(#export trusted forged) (#fn secret () #u64 (#return 42u64)) (#gn relay (name target) `((#fn ,name () #u64 (#return (#call ,target ()))))) (#gn trusted (name) `((#generate relay ,name secret))) (#gn forged (name) `((#generate relay ,name ,(#gn-symbol \"secret\"))))");
    for (first, second) in [("trusted", "forged"), ("forged", "trusted")] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) (#generate lib@{first} generated-read) (#generate lib@{second} generated-read) (#fn main () #u64 (#return 0u64))"), None);
    }
}

#[test]
fn equivalent_authority_from_two_templates_still_deduplicates() {
    let scratch = support::Scratch::new("generator-equivalent-authority");
    write(scratch.path(), "library/lib.lim", "(#export first second) (#fn secret () #u64 (#return 42u64)) (#gn relay (name target) `((#fn ,name () #u64 (#return (#call ,target ()))))) (#gn first (name) `((#generate relay ,name secret))) (#gn second (name) `((#generate relay ,name secret)))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@first generated-read) (#generate lib@second generated-read) (#fn main () #u64 (#return (#call generated-read ())))", None);
}

#[test]
fn builtin_output_preserves_authored_private_worker_references() {
    let scratch = support::Scratch::new("generator-authority-builtin");
    write(scratch.path(), "library/lib.lim", "(#export make) (#fn worker () #u64 (#return 42u64)) (#gn make (name) `((#generate #thread-spawn (: task ,name : worker worker))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make Task) (#fn main () #u64 (#return 0u64))", None);
}

#[test]
fn builtin_deduplication_uses_the_producing_module_not_symbol_construction() {
    let scratch = support::Scratch::new("generator-authority-builtin-dedup");
    write(scratch.path(), "library/lib.lim", "(#export trusted forged) (#fn worker () #u64 (#return 42u64)) (#gn trusted (name) `((#generate #thread-spawn (: task ,name : worker worker)))) (#gn forged (name) `((#generate #thread-spawn (: task ,name : worker ,(#gn-symbol \"worker\")))))");
    for (first, second) in [("trusted", "forged"), ("forged", "trusted")] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) (#generate lib@{first} Task) (#generate lib@{second} Task) (#fn main () #u64 (#return 0u64))"), None);
    }
}

#[test]
fn syntax_bundle_splices_preserve_references_without_laundering_their_contents() {
    let scratch = support::Scratch::new("generator-authority-bundle-splice");
    write(scratch.path(), "library/lib.lim", "(#export wrap wrap-any) (#fn secret () #u64 (#return 42u64)) (#gn prepare () `((#syntax Hidden ((#return (#call secret ())))))) (#generate prepare) (#gn wrap (name) `((#fn ,name () #u64 (#syntax-splice Hidden)))) (#gn wrap-any (name body) `((#fn ,name () #u64 (#syntax-splice ,body))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@wrap generated-read) (#fn main () #u64 (#return (#call generated-read ())))", None);
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#gn forge () `((#syntax Body ((#return (#call ,(#gn-symbol \"lib@secret\") ())))))) (#generate forge) (#generate lib@wrap-any generated-read Body) (#fn main () #u64 (#return 0u64))", Some("private"));
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#gn forge () `((#fn generated-read () #u64 (#syntax-splice lib@Hidden)))) (#generate forge) (#fn main () #u64 (#return 0u64))", Some("private"));
}

#[test]
fn call_graph_lowering_retains_private_reference_authority() {
    let scratch = support::Scratch::new("generator-authority-call-graph");
    write(scratch.path(), "library/lib.lim", "(#export make) (#fn secret () #u64 (#let trace (#slice #char) (#call-graph)) (#forget trace) (#return 42u64)) (#gn make (name) `((#fn ,name () #u64 (#return (#call secret ())))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read) (#fn main () #u64 (#return (#call generated-read ())))", None);
}

#[test]
fn async_lowering_retains_generated_file_context_for_constructed_callees() {
    let scratch = support::Scratch::new("generator-authority-async");
    write(scratch.path(), "library/lib.lim", "(#export make forged) (#fn secret () #u64 (#return 42u64)) (#gn make () `((#generate #async-fn (: protocol WorkAwait : waker #u64 : function (#fn work () #u64 (#return (#call secret ()))))))) (#gn forged (target) `((#generate #async-fn (: protocol WorkAwait : waker #u64 : function (#fn work () #u64 (#return (#call ,(#gn-symbol target) ())))))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make) (#fn main () #u64 (#return 0u64))", None);
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@forged \"lib@secret\") (#fn main () #u64 (#return 0u64))", None);
}

#[test]
fn caller_library_authority_is_retained_alongside_template_authority() {
    let scratch = support::Scratch::new("generator-caller-library-authority");
    write(scratch.path(), "generator/lib.lim", "(#export relay) (#gn relay (name target) `((#fn ,name () #u64 (#return (#call ,target ())))))");
    write(scratch.path(), "caller/lib.lim", "(#export read) (#import-external \"../generator/lib.lim\" gen) (#fn secret () #u64 (#return 42u64)) (#generate gen@relay read secret)");
    check_modes(scratch.path(), "(#import-external \"caller/lib.lim\" caller) (#fn main () #u64 (#return (#call caller@read ())))", None);
}

#[test]
fn private_reference_authority_does_not_remove_unsafe_call_requirements() {
    let scratch = support::Scratch::new("generator-authority-not-unsafe");
    write(scratch.path(), "library/lib.lim", "(#export make) (#unsafe-fn secret () #u64 (#return 42u64)) (#gn make (name) `((#fn ,name () #u64 (#return (#call secret ())))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read) (#fn main () #u64 (#return 0u64))", Some("unsafe"));
}

#[test]
fn qualified_definition_and_invocation_names_survive_two_external_prefixes() {
    let scratch = support::Scratch::new("qualified-generator-contexts");
    write(scratch.path(), "producer/lib.lim", "(#export make) (#fn helper () #u64 (#return 2u64)) (#gn make (name callback) `((#fn ,name () #u64 (#let base #u64 (#call @helper ())) (#let input #u64 (#call ,callback ())) (#return (#u64::add-wrap base input)))))");
    write(scratch.path(), "consumer/lib.lim", "(#export read) (#import-external \"../producer/lib.lim\" producer) (#fn callback () #u64 (#return 40u64)) (#generate producer@make read @callback)");
    let source = "(#import-external \"consumer/lib.lim\" first) (#import-external \"consumer/lib.lim\" second) (#fn main () #u64 (#return (#u64::add-wrap (#call first@read ()) (#call second@read ()))))";
    check_modes(scratch.path(), source, None);
    let artifacts = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(artifacts.len(), 2);
    for prefix in ["first", "second"] {
        let artifact = artifacts
            .iter()
            .find(|text| text.contains(&format!("{prefix}@producer@helper")))
            .unwrap();
        assert!(artifact.contains("#generated-context"));
        assert!(artifact.contains("definition-module"));
        assert!(artifact.contains("producer/lib.lim"));
        assert!(artifact.contains("invocation-module"));
        assert!(artifact.contains("consumer/lib.lim"));
        assert!(artifact.contains(&format!("{prefix}@callback")));
        assert!(!artifact.contains("lim-reference-authority"));
    }
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &lim::generate_assembly(&program).unwrap(),
        &binary,
        &[],
        &[],
        lim::TargetDescription::host().unwrap(),
    )
    .unwrap();
    assert_eq!(
        std::process::Command::new(binary).status().unwrap().code(),
        Some(84)
    );
}

#[test]
fn private_invocation_references_fail_before_the_generator_executes() {
    let scratch = support::Scratch::new("early-generator-input-privacy");
    write(scratch.path(), "library/lib.lim", "(#export reject) (#fn secret () #u64 (#return 42u64)) (#gn reject (input) (#gn-error \"interpreter was executed\"))");
    for argument in [
        "@lib@secret",
        "lib@secret",
        "(#fn local () #u64 (#return (#call lib@secret ())))",
    ] {
        let source = format!("(#import-external \"library/lib.lim\" lib) (#generate lib@reject {argument}) (#fn main () #u64 (#return 0u64))");
        for cache in [false, true] {
            let result = if cache {
                lim::parse_program_from_path_with_config_and_cache(
                    &source,
                    &scratch.path().join("main.lim"),
                    &lim::CompileConfig::default(),
                    &scratch.path().join(".lim/cache"),
                )
            } else {
                lim::parse_program_from_path(&source, &scratch.path().join("main.lim"))
            };
            let error = result.err().expect("private argument must be rejected");
            assert!(error.contains("private"), "{error}");
            assert!(!error.contains("interpreter was executed"), "{error}");
        }
    }
}

#[test]
fn nested_generator_does_not_inherit_an_ancestor_definition_modules_privileges() {
    let scratch = support::Scratch::new("non-transitive-generated-context");
    write(scratch.path(), "inner/lib.lim", "(#export relay) (#gn relay (name target) `((#fn ,name () #u64 (#return (#call ,target ())))))");
    write(scratch.path(), "outer/lib.lim", "(#export make) (#import-external \"../inner/lib.lim\" inner) (#fn secret () #u64 (#return 42u64)) (#gn make (name) `((#generate inner@relay ,name @secret)))");
    check_modes(scratch.path(), "(#import-external \"outer/lib.lim\" outer) (#generate outer@make generated-read) (#fn main () #u64 (#return 0u64))", Some("private"));
}

#[test]
fn literal_function_locals_and_strings_are_not_qualified() {
    let scratch = support::Scratch::new("qualified-literal-function");
    let source = "(#gn identity (function) (#gn-list function)) (#generate identity (#fn main (: ) #u64 (#let input #u64 42u64) (#let text (#array #char 16) \"@not-a-reference\") (#forget text) (#return input)))";
    check_modes(scratch.path(), source, None);
    let artifact = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let text = fs::read_to_string(artifact).unwrap();
    assert!(text.contains("@not-a-reference"));
    assert!(text.contains("#let input"));
    assert!(text.contains("#return input"));
}

#[test]
fn generators_cannot_manufacture_headers_or_late_qualification() {
    let scratch = support::Scratch::new("generated-context-forgery");
    for (body, expected) in [
        (
            "(#gn-list (#gn-list (#gn-symbol \"#generated-context\")))",
            "compiler-owned",
        ),
        (
            "(#gn-list (#gn-symbol \"@secret\"))",
            "before generator execution",
        ),
    ] {
        check_modes(
            scratch.path(),
            &format!("(#gn forge () {body}) (#generate forge) (#fn main () #u64 (#return 0u64))"),
            Some(expected),
        );
    }
}

#[test]
fn qualification_in_generator_expressions_cannot_capture_a_parameter() {
    let scratch = support::Scratch::new("qualified-generator-parameter-capture");
    let source = "(#fn callback () #u64 (#return 42u64)) (#gn make (callback) (#gn-list (#gn-list (#gn-symbol \"#fn\") (#gn-symbol \"generated-read\") () #u64 (#gn-list (#gn-symbol \"#return\") (#gn-list (#gn-symbol \"#call\") @callback ()))))) (#generate make unrelated-literal) (#fn main () #u64 (#return (#call generated-read ())))";
    check_modes(scratch.path(), source, None);
}

#[test]
fn unknown_private_generated_names_are_checked_from_import_exports_before_execution() {
    let scratch = support::Scratch::new("qualified-forward-private");
    write(scratch.path(), "library/lib.lim", "(#export reject PublicFuture) (#gn reject (input) (#gn-error \"interpreter was executed\"))");
    let source = "(#import-external \"library/lib.lim\" lib) (#generate lib@reject @lib@PrivateFuture) (#fn main () #u64 (#return 0u64))";
    let error = lim::parse_program_from_path(source, &scratch.path().join("main.lim"))
        .err()
        .unwrap();
    assert!(error.contains("private"), "{error}");
    assert!(!error.contains("interpreter was executed"), "{error}");
}

#[test]
fn qualified_global_cannot_capture_a_local_in_a_literal_function() {
    let scratch = support::Scratch::new("qualified-runtime-local-capture");
    let source = "(#gn identity (function) (#gn-list function)) (#generate identity (#fn main () #u64 (#let local #u64 42u64) (#return @local)))";
    check_modes(scratch.path(), source, Some("never refers to a local"));
}

#[test]
fn qualification_supports_exported_generated_targets_and_handwritten_forward_declarations() {
    let scratch = support::Scratch::new("qualified-forward-exports");
    write(
        scratch.path(),
        "library/lib.lim",
        "(#export Future) (#gn make () `((#type Future #u64))) (#generate make)",
    );
    let source = "(#import-external \"library/lib.lim\" lib) (#gn alias (target) `((#type Alias ,target))) (#generate alias @lib@Future) (#gn reader (target) `((#fn read () #u64 (#return (#call ,target ()))))) (#generate reader @later) (#fn later () #u64 (#return 42u64)) (#fn main () #u64 (#let answer Alias (#call read ())) (#return answer))";
    check_modes(scratch.path(), source, None);
}
