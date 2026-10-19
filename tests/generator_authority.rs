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
fn manufactured_runtime_callee_does_not_inherit_its_call_operators_authority() {
    let scratch = support::Scratch::new("generator-manufactured-callee");
    write(scratch.path(), "library/lib.lim", HELPERS);
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@dynamic read-generated \"lib@secret\") (#fn main () #u64 (#return 0u64))", Some("private"));
}

#[test]
fn spliced_field_projection_and_forwarded_input_remain_unprivileged() {
    let scratch = support::Scratch::new("generator-spliced-authority");
    write(scratch.path(), "library/lib.lim", HELPERS);
    for invocation in [
        "(#generate lib@splice read-generated value (#get value lib@capacity))",
        "(#generate lib@field read-generated lib@capacity)",
        "(#generate lib@forwarded read-generated (() (#call lib@secret ())))",
    ] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) {invocation} (#fn main () #u64 (#return 0u64))"), Some("private"));
    }
}

#[test]
fn library_authored_projection_can_access_its_private_representation() {
    let scratch = support::Scratch::new("generator-template-fields");
    write(scratch.path(), "library/lib.lim", "(#export make) (#struct Value (#linear) (: capacity #u64)) (#gn make (name) `((#fn ,name (: value (#ref Value)) #u64 (#return (#get value capacity)))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make read-generated) (#fn main () #u64 (#return 0u64))", None);
}

#[test]
fn caller_supplied_constructor_field_names_do_not_gain_private_access() {
    let scratch = support::Scratch::new("generator-untrusted-constructor-fields");
    write(scratch.path(), "library/lib.lim", "(#export make) (#struct Value (#linear) (: capacity #u64)) (#gn make (name fields) `((#fn ,name () #u64 (#let value Value (#struct-literal Value ,fields)) (#forget value) (#return 0u64))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read ((lib@capacity 42u64))) (#fn main () #u64 (#return 0u64))", Some("private"));
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
fn copied_generated_source_comments_do_not_grant_authority() {
    let scratch = support::Scratch::new("generator-authority-not-source");
    write(scratch.path(), "library/lib.lim", HELPERS);
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read) (#fn main () #u64 (#return 0u64))", None);
    let artifact = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
        .find(|source| source.contains("lim-reference-authority-v1"))
        .unwrap();
    check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib)\n{artifact}\n(#fn main () #u64 (#return 0u64))"), Some("private"));
}

#[test]
fn authored_construction_and_enum_patterns_keep_representation_authority() {
    let scratch = support::Scratch::new("generator-authority-constructors");
    write(scratch.path(), "library/lib.lim", "(#export make) (#struct Value (#linear) (: capacity #u64)) (#enum Choice () (Choice.Ready)) (#gn make (name) `((#fn ,name () #u64 (#let value Value (#struct-literal Value (: capacity 42u64))) (#let answer #u64 (#get (#borrow value) capacity)) (#forget value) (#let choice Choice (#enum-literal Choice.Ready)) (#return (#match choice (#case Choice.Ready answer))))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make generated-read) (#fn main () #u64 (#return (#call generated-read ())))", None);
}

#[test]
fn synthesized_names_and_spliced_statement_lists_remain_unprivileged() {
    let scratch = support::Scratch::new("generator-derived-authority");
    write(scratch.path(), "library/lib.lim", "(#export append splice) (#fn Secret::read () #u64 (#return 42u64)) (#struct Value (#linear) (: capacity #u64)) (#gn append (name base) `((#fn ,name () #u64 (#return (#call ,(#gn-symbol-append base \"read\") ()))))) (#gn splice (name parameter body) `((#fn ,name (: ,parameter (#ref Value)) #u64 ,@body)))");
    for invocation in [
        "(#generate lib@append generated-read lib@Secret)",
        "(#generate lib@splice generated-read value ((#return (#get value lib@capacity))))",
    ] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) {invocation} (#fn main () #u64 (#return 0u64))"), Some("private"));
    }
}

#[test]
fn identical_literals_with_different_authorities_do_not_deduplicate() {
    let scratch = support::Scratch::new("generator-authority-dedup");
    write(scratch.path(), "library/lib.lim", "(#export trusted forged) (#fn secret () #u64 (#return 42u64)) (#gn relay (name target) `((#fn ,name () #u64 (#return (#call ,target ()))))) (#gn trusted (name) `((#generate relay ,name secret))) (#gn forged (name) `((#generate relay ,name ,(#gn-symbol \"secret\"))))");
    for (first, second) in [("trusted", "forged"), ("forged", "trusted")] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) (#generate lib@{first} generated-read) (#generate lib@{second} generated-read) (#fn main () #u64 (#return 0u64))"), Some("duplicate"));
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
fn builtin_deduplication_cannot_hide_a_forged_worker_reference() {
    let scratch = support::Scratch::new("generator-authority-builtin-dedup");
    write(scratch.path(), "library/lib.lim", "(#export trusted forged) (#fn worker () #u64 (#return 42u64)) (#gn trusted (name) `((#generate #thread-spawn (: task ,name : worker worker)))) (#gn forged (name) `((#generate #thread-spawn (: task ,name : worker ,(#gn-symbol \"worker\")))))");
    for (first, second) in [("trusted", "forged"), ("forged", "trusted")] {
        check_modes(scratch.path(), &format!("(#import-external \"library/lib.lim\" lib) (#generate lib@{first} Task) (#generate lib@{second} Task) (#fn main () #u64 (#return 0u64))"), Some("duplicate"));
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
fn async_lowering_retains_authority_without_trusting_unquoted_callees() {
    let scratch = support::Scratch::new("generator-authority-async");
    write(scratch.path(), "library/lib.lim", "(#export make forged) (#fn secret () #u64 (#return 42u64)) (#gn make () `((#generate #async-fn (: protocol WorkAwait : waker #u64 : function (#fn work () #u64 (#return (#call secret ()))))))) (#gn forged (target) `((#generate #async-fn (: protocol WorkAwait : waker #u64 : function (#fn work () #u64 (#return (#call ,(#gn-symbol target) ())))))))");
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@make) (#fn main () #u64 (#return 0u64))", None);
    check_modes(scratch.path(), "(#import-external \"library/lib.lim\" lib) (#generate lib@forged \"lib@secret\") (#fn main () #u64 (#return 0u64))", Some("private"));
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
