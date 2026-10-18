mod support;
use std::{fs, path::Path};

fn write(base: &Path, path: &str, source: &str) {
    let path = base.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

fn library(base: &Path) {
    write(base, "collection/lib.lim", "(#export Collection collection-new collection-read collection-destroy) (#import \"storage.lim\")");
    write(
        base,
        "collection/storage.lim",
        "
      (#struct Collection (#linear) ((capacity #u64)))
      (#fn private-capacity () #u64 (#return 42u64))
      (#fn collection-new () Collection
        (#return (#struct-literal Collection ((capacity (#call private-capacity ()))))))
      (#fn collection-read ((value (#ref Collection))) #u64 (#return (#get value capacity)))
      (#fn collection-destroy ((value Collection)) () (#forget value) (#return ()))",
    );
}

fn check(base: &Path, path: &str, source: &str) -> Result<(), String> {
    let program = lim::parse_program_from_path(source, &base.join(path))?;
    lim::check_types(&program)
}

#[test]
fn public_api_runs_with_agglutinated_names_and_no_public_representation() {
    let scratch = support::Scratch::new("library-api");
    library(scratch.path());
    let source = "(#import-external \"collection/lib.lim\" collections)
      (#fn main () #u64
        (#let value collections@Collection (#call collections@collection-new ()))
        (#let answer #u64 (#call collections@collection-read (: collections@value (#borrow value))))
        (#call collections@collection-destroy (: collections@value value))
        (#return answer))";
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
fn internal_and_external_paths_cannot_bypass_the_entry_point() {
    let scratch = support::Scratch::new("library-imports");
    library(scratch.path());
    for source in [
        "(#import \"collection/lib.lim\")",
        "(#import \"collection/storage.lim\")",
        "(#import-external \"collection/storage.lim\" collections)",
    ] {
        let error = check(scratch.path(), "main.lim", source).unwrap_err();
        assert!(
            error.contains("library") || error.contains("lib.lim"),
            "{error}"
        );
    }
}

#[test]
fn guessed_private_function_and_fields_are_rejected() {
    let scratch = support::Scratch::new("library-private");
    library(scratch.path());
    for body in [
        "(#return (#call collections@private-capacity ()))",
        "(#let value collections@Collection (#struct-literal collections@Collection ((collections@capacity 42u64)))) (#forget value) (#return 0u64)",
        "(#let value collections@Collection (#call collections@collection-new ())) (#let answer #u64 (#get value collections@capacity)) (#call collections@collection-destroy (: collections@value value)) (#return answer)",
        "(#let-mut value collections@Collection (#call collections@collection-new ())) (#set (#get value collections@capacity) 0u64) (#call collections@collection-destroy (: collections@value value)) (#return 0u64)",
        "(#let-mut value collections@Collection (#call collections@collection-new ())) (#let field (#ref-mut #u64) (#borrow-mut (#get value collections@capacity))) (#deref-set field 0u64) (#call collections@collection-destroy (: collections@value value)) (#return 0u64)",
        "(#let value collections@Collection (#call collections@collection-new ())) (#let answer #u64 (#if-let (collections@Collection capacity) value capacity 0u64)) (#return answer)",
    ] {
        let source = format!("(#import-external \"collection/lib.lim\" collections) (#fn main () #u64 {body})");
        let error = check(scratch.path(), "main.lim", &source).unwrap_err();
        assert!(error.contains("private"), "{error}\n{source}");
    }
}

#[test]
fn white_box_test_entry_can_import_only_the_needed_implementation() {
    let scratch = support::Scratch::new("library-white-box");
    library(scratch.path());
    check(
        scratch.path(),
        "collection/test.lim",
        "(#import \"storage.lim\") (#fn main () #u64 (#return (#call private-capacity ())))",
    )
    .unwrap();
}

#[test]
fn nested_libraries_are_isolated_in_both_directions() {
    let scratch = support::Scratch::new("nested-library");
    library(scratch.path());
    write(
        scratch.path(),
        "collection/utility/lib.lim",
        "(#export utility-read) (#import \"implementation.lim\")",
    );
    write(
        scratch.path(),
        "collection/utility/implementation.lim",
        "(#fn utility-read () #u64 (#return 7u64))",
    );
    assert!(check(
        scratch.path(),
        "collection/test.lim",
        "(#import \"utility/implementation.lim\")"
    )
    .is_err());
    assert!(check(
        scratch.path(),
        "collection/utility/test.lim",
        "(#import \"../storage.lim\")"
    )
    .is_err());
    check(scratch.path(), "collection/test.lim", "(#import-external \"utility/lib.lim\" util) (#fn main () #u64 (#return (#call util@utility-read ())))").unwrap();
}

#[test]
fn symlinks_do_not_bypass_library_ownership() {
    let scratch = support::Scratch::new("library-symlink");
    library(scratch.path());
    std::os::unix::fs::symlink(
        scratch.path().join("collection/storage.lim"),
        scratch.path().join("storage.lim"),
    )
    .unwrap();
    assert!(check(scratch.path(), "main.lim", "(#import \"storage.lim\")").is_err());
}

#[test]
fn generated_caller_code_has_no_private_library_privileges() {
    let scratch = support::Scratch::new("library-generated-access");
    library(scratch.path());
    let source = "(#import-external \"collection/lib.lim\" collections)
      (#gn forge () `((#fn main () #u64 (#return (#call collections@private-capacity ())))))
      (#generate forge)";
    let error = check(scratch.path(), "main.lim", source).unwrap_err();
    assert!(error.contains("private"), "{error}");
}

#[test]
fn external_prefix_is_required_and_at_is_an_identifier_separator() {
    let scratch = support::Scratch::new("library-prefix");
    library(scratch.path());
    for prefix in ["", "()", "\"\"", "a@b", "#u64"] {
        let source = format!("(#import-external \"collection/lib.lim\" {prefix})");
        assert!(
            check(scratch.path(), "main.lim", &source).is_err(),
            "{source}"
        );
    }
    let expressions = lim::parse("collections@Collection collections@collection-new").unwrap();
    assert_eq!(expressions.len(), 2);
    assert!(lim::parse_program("(@#optional (: type #u64 : name Number))").is_err());
    check(
        scratch.path(),
        "main.lim",
        "(#generate #optional (: type #u64 : name Number)) (#fn main () #u64 (#return 0u64))",
    )
    .unwrap();
}

#[test]
fn aliases_and_global_initializers_cannot_expose_or_construct_private_storage() {
    let scratch = support::Scratch::new("library-global-privacy");
    write(scratch.path(), "numbers/lib.lim", "(#export Number number) (#struct Number () ((value #u64))) (#const number Number (#struct-literal Number (: value 42u64)))");
    for body in [
        "(#const forged nums@Number (#struct-literal nums@Number (: nums@value 0u64)))",
        "(#type Alias nums@Number) (#const copied Alias nums@number) (#const exposed #u64 (#get copied nums@value))",
        "(#const exposed #u64 (#get nums@number nums@value))",
        "(#let exposed #u64 (#get nums@number nums@value))",
    ] {
        let source = format!("(#import-external \"numbers/lib.lim\" nums) {body} (#fn main () #u64 (#return 0u64))");
        let error = check(scratch.path(), "main.lim", &source).unwrap_err();
        assert!(error.contains("private"), "{error}");
    }
}

#[test]
fn exported_signatures_must_not_leak_private_types() {
    let scratch = support::Scratch::new("library-signature");
    write(scratch.path(), "numbers/lib.lim", "(#export read) (#struct Secret () ((value #u64))) (#fn read () Secret (#return (#struct-literal Secret (: value 42u64))))");
    let error = check(
        scratch.path(),
        "main.lim",
        "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#return 0u64))",
    )
    .unwrap_err();
    assert!(error.contains("exposes private type"), "{error}");
    write(scratch.path(), "numbers/lib.lim", "(#export Value Value.Public) (#struct Secret () ((value #u64))) (#enum Value () ((Value.Public Secret)))");
    let error = check(
        scratch.path(),
        "main.lim",
        "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#return 0u64))",
    )
    .unwrap_err();
    assert!(error.contains("exposes private type"), "{error}");
}

#[test]
fn enum_variants_require_explicit_exports_and_contributions_stay_internal() {
    let scratch = support::Scratch::new("library-enums");
    write(scratch.path(), "numbers/lib.lim", "(#export Number Number.Public) (#enum Number () ((Number.Public #u64) Number.Private)) (#export Events) (#distributed-enum Events ()) (#enum-contribute Events (Events.Internal #u64))");
    check(scratch.path(), "main.lim", "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#let value nums@Number (#enum-literal nums@Number.Public 42u64)) (#forget value) (#return 0u64))").unwrap();
    for body in [
        "(#fn main () #u64 (#let value nums@Number nums@Number.Private) (#forget value) (#return 0u64))",
        "(#enum-contribute nums@Events (nums@Events.Forged #u64)) (#fn main () #u64 (#return 0u64))",
        "(#gn forge () `((#enum-contribute nums@Events (nums@Events.Forged #u64)))) (#generate forge) (#fn main () #u64 (#return 0u64))",
    ] {
        let source = format!("(#import-external \"numbers/lib.lim\" nums) {body}");
        let error = check(scratch.path(), "main.lim", &source).unwrap_err();
        assert!(error.contains("private"), "{error}");
    }
}

#[test]
fn generator_helpers_are_private_even_when_called_inside_unquotes() {
    let scratch = support::Scratch::new("library-generator-privacy");
    write(scratch.path(), "numbers/lib.lim", "(#export public) (#gn-fn helper () `((#type Number #u64))) (#gn public () (#gn-call helper)) (#gn private () (#gn-call helper))");
    check(scratch.path(), "main.lim", "(#import-external \"numbers/lib.lim\" nums) (#generate nums@public) (#fn main () #u64 (#return 0u64))").unwrap();
    for body in [
        "(#generate nums@private)",
        "(#gn forge () (#gn-call nums@helper)) (#generate forge)",
        "(#gn forge () `((#type Number ,(#gn-first (#gn-call nums@helper))))) (#generate forge)",
        "(#gn forge () `((#generate nums@private))) (#generate forge)",
    ] {
        let source = format!(
            "(#import-external \"numbers/lib.lim\" nums) {body} (#fn main () #u64 (#return 0u64))"
        );
        let error = check(scratch.path(), "main.lim", &source).unwrap_err();
        assert!(error.contains("private"), "{error}");
    }
}

#[test]
fn export_metadata_is_literal_and_confined_to_lib_entries() {
    let scratch = support::Scratch::new("library-export-placement");
    assert!(check(
        scratch.path(),
        "main.lim",
        "(#export main) (#fn main () #u64 (#return 0u64))"
    )
    .is_err());
    write(
        scratch.path(),
        "numbers/lib.lim",
        "(#export) (#gn forge () `((#export main))) (#generate forge)",
    );
    let error = check(
        scratch.path(),
        "main.lim",
        "(#import-external \"numbers/lib.lim\" nums)",
    )
    .unwrap_err();
    assert!(error.contains("literal source"), "{error}");
}

#[test]
fn standard_library_is_available_inside_a_library_boundary() {
    let scratch = support::Scratch::new("library-standard");
    library(scratch.path());
    check(
        scratch.path(),
        "collection/test.lim",
        "(#std) (#fn main () #u64 (#return 0u64))",
    )
    .unwrap();
}

#[test]
fn nested_dependency_exports_are_not_automatically_reexported() {
    let scratch = support::Scratch::new("library-reexports");
    write(scratch.path(), "outer/lib.lim", "(#export read) (#import-external \"utility/lib.lim\" util) (#fn read () #u64 (#return (#call util@read ())))");
    write(
        scratch.path(),
        "outer/utility/lib.lim",
        "(#export read) (#fn read () #u64 (#return 42u64))",
    );
    check(scratch.path(), "main.lim", "(#import-external \"outer/lib.lim\" outer) (#fn main () #u64 (#return (#call outer@read ())))").unwrap();
    let error = check(scratch.path(), "main.lim", "(#import-external \"outer/lib.lim\" outer) (#fn main () #u64 (#return (#call outer@util@read ())))").unwrap_err();
    assert!(error.contains("not automatically re-exported"), "{error}");
}

#[test]
fn externally_imported_assembly_preserves_physical_register_names() {
    let scratch = support::Scratch::new("library-assembly");
    write(scratch.path(), "assembly.lim", "(#fn identity (: value #u64) #u64 (#return (#unsafe (#asm #u64 (: rdi value) \"mov rax, rdi\"))))");
    check(scratch.path(), "main.lim", "(#import-external \"assembly.lim\" machine) (#fn main () #u64 (#return (#call machine@identity (: machine@value 42u64))))").unwrap();
    write(scratch.path(), "standard.lim", "(#std)");
    let source = "(#import-external \"standard.lim\" standard) (#fn main () #u64 (#return 0u64))";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    lim::generate_assembly(&program).unwrap();
}

#[test]
fn private_field_diagnostics_underline_the_exact_source_token() {
    let scratch = support::Scratch::new("library-diagnostic");
    library(scratch.path());
    let source = "(#import-external \"collection/lib.lim\" collections)\n(#fn main () #u64\n  (#let value collections@Collection (#call collections@collection-new ()))\n  (#let result #u64 (#get value collections@capacity))\n  (#call collections@collection-destroy (: collections@value value))\n  (#return result))\n";
    let path = scratch.path().join("main.lim");
    let error = lim::compile_source_to_assembly(
        source,
        &path,
        &lim::CompileConfig::default(),
        &scratch.path().join(".lim/cache"),
        lim::TargetDescription::host().unwrap(),
    )
    .unwrap_err();
    let span = error.span.unwrap();
    assert_eq!(span.line, 4);
    assert_eq!(&source[span.start..span.end], "collections@capacity");
    let rendered = lim::render_diagnostic(&error, source, path.to_str().unwrap());
    assert!(rendered.contains("collections@capacity"));
    assert!(
        rendered.contains(&"^".repeat("collections@capacity".len())),
        "{rendered}"
    );
}

#[test]
fn native_thread_entry_points_are_private_unless_exported() {
    let scratch = support::Scratch::new("library-native-privacy");
    let implementation = "(#export Task Task::join Task::SpawnResult Task::SpawnResult.Ok Task::SpawnResult.Error Task::SpawnError Task::JoinResult Task::JoinResult.Ok Task::JoinResult.Error) (#fn worker () #u64 (#return 42u64)) (#generate #thread-spawn (: task Task : worker worker))";
    write(scratch.path(), "workers/lib.lim", implementation);
    let source = "(#import-external \"workers/lib.lim\" workers)
      (#fn main () #u64 (#return
        (#match (#call workers@Task::spawn ())
          (#case (workers@Task::SpawnResult.Ok task)
            (#match (#call workers@Task::join (: task task))
              (#case (workers@Task::JoinResult.Ok result) result)
              (#case (workers@Task::JoinResult.Error (#tuple retry-task error-code)) (#panic))))
          (#case (workers@Task::SpawnResult.Error error) (#panic)))))";
    // Public result types do not make the native spawn entry point public.
    let error = check(scratch.path(), "main.lim", source).unwrap_err();
    assert!(error.contains("private"), "{error}");
    assert!(error.contains("workers@Task::spawn"), "{error}");
    write(
        scratch.path(),
        "workers/lib.lim",
        &implementation.replace("(#export Task ", "(#export Task Task::spawn "),
    );
    check(scratch.path(), "main.lim", source).unwrap();
    write(scratch.path(), "workers/lib.lim", "(#export Task Task::spawn) (#fn worker () #u64 (#return 42u64)) (#generate #thread-spawn (: task Task : worker worker))");
    let error = check(
        scratch.path(),
        "main.lim",
        "(#import-external \"workers/lib.lim\" workers) (#fn main () #u64 (#return 0u64))",
    )
    .unwrap_err();
    assert!(error.contains("exposes private type"), "{error}");
}
