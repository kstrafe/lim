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

// Exercise ownership independently of whether expansions came from the
// interpreter or persistent cache, and repeat to cover warm-cache paths.
fn check_cache_modes(base: &Path, source: &str, expected_error: Option<&str>) {
    for mode in 0..3 {
        let parsed = if mode == 0 {
            lim::parse_program_from_path(source, &base.join("main.lim"))
        } else {
            lim::parse_program_from_path_with_config_and_cache(
                source,
                &base.join("main.lim"),
                &lim::CompileConfig::default(),
                &base.join(".lim/cache"),
            )
        };
        let result = parsed.and_then(|program| lim::check_types(&program));
        if let Some(message) = expected_error {
            let error = result.expect_err("cross-boundary declarations silently merged");
            assert!(error.contains(message), "mode {mode}: {error}");
        } else {
            result.unwrap_or_else(|error| panic!("mode {mode}: {error}"));
        }
    }
}

#[test]
fn identical_expansions_in_different_libraries_do_not_merge_ownership() {
    let scratch = support::Scratch::new("generator-instance-ownership");
    // Strings intentionally survive prefixing: these really are identical
    // invocations, unlike invocations whose symbol arguments get prefixed.
    write(scratch.path(), "numbers/lib.lim", "(#export make) (#gn make (name) `((#type ,(#gn-symbol name) #u64))) (#generate make \"Hidden\")");
    for imports in [
        "(#import-external \"numbers/lib.lim\" nums) (#generate nums@make \"Hidden\")",
        "(#generate nums@make \"Hidden\") (#import-external \"numbers/lib.lim\" nums)",
    ] {
        let source = format!("{imports} (#fn main () #u64 (#return 0u64))");
        check_cache_modes(scratch.path(), &source, Some("duplicate"));
    }
}

#[test]
fn external_instances_retain_their_own_internal_imports() {
    let scratch = support::Scratch::new("library-instance-internal-imports");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "(#export read) (#import \"implementation.lim\")",
    );
    write(
        scratch.path(),
        "numbers/implementation.lim",
        "(#generate #optional (: type #u64 : name Number)) (#fn read () #u64 (#return 42u64))",
    );
    check_cache_modes(scratch.path(), "(#import-external \"numbers/lib.lim\" first) (#import-external \"numbers/lib.lim\" second) (#fn main () #u64 (#return (#u64::add-wrap (#call first@read ()) (#call second@read ()))))", None);
}

#[test]
fn transitive_instances_retain_their_own_dependencies() {
    let scratch = support::Scratch::new("library-instance-transitive-imports");
    write(
        scratch.path(),
        "leaf/lib.lim",
        "(#export read) (#fn read () #u64 (#return 42u64))",
    );
    write(scratch.path(), "middle/lib.lim", "(#export read) (#import-external \"../leaf/lib.lim\" leaf) (#fn read () #u64 (#return (#call leaf@read ())))");
    check_cache_modes(scratch.path(), "(#import-external \"middle/lib.lim\" first) (#import-external \"middle/lib.lim\" second) (#fn main () #u64 (#return (#u64::add-wrap (#call first@read ()) (#call second@read ()))))", None);
}

#[test]
fn nested_builtin_expansions_do_not_merge_across_boundaries() {
    let scratch = support::Scratch::new("library-builtin-expansion-ownership");
    write(scratch.path(), "numbers/lib.lim", "(#export make) (#gn make (name) `((#generate #optional (: type #u64 : name ,(#gn-symbol name))))) (#generate make \"Hidden\")");
    for imports in [
        "(#import-external \"numbers/lib.lim\" nums) (#generate nums@make \"Hidden\")",
        "(#generate nums@make \"Hidden\") (#import-external \"numbers/lib.lim\" nums)",
    ] {
        check_cache_modes(
            scratch.path(),
            &format!("{imports} (#fn main () #u64 (#return 0u64))"),
            Some("duplicate"),
        );
    }
}

#[test]
fn identical_expansions_still_deduplicate_inside_one_library_instance() {
    let scratch = support::Scratch::new("library-local-expansion-dedup");
    write(scratch.path(), "numbers/lib.lim", "(#export read) (#gn make (name) `((#type ,(#gn-symbol name) #u64))) (#import \"first.lim\") (#import \"second.lim\") (#fn read () #u64 (#return 42u64))");
    write(
        scratch.path(),
        "numbers/first.lim",
        "(#generate make \"Hidden\")",
    );
    write(
        scratch.path(),
        "numbers/second.lim",
        "(#generate make \"Hidden\")",
    );
    check_cache_modes(scratch.path(), "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#return (#call nums@read ())))", None);
}

#[test]
fn one_instance_cannot_access_another_instances_private_declarations() {
    let scratch = support::Scratch::new("library-instance-private-access");
    write(scratch.path(), "numbers/lib.lim", "(#export read) (#fn secret () #u64 (#return 42u64)) (#gn forge (target) `((#fn read () #u64 (#return (#call ,(#gn-symbol target) ()))))) (#generate forge \"second@secret\")");
    check_cache_modes(scratch.path(), "(#import-external \"numbers/lib.lim\" first) (#import-external \"numbers/lib.lim\" second) (#fn main () #u64 (#return 0u64))", Some("private"));
}

#[test]
fn standard_imports_are_shared_between_library_instances() {
    let scratch = support::Scratch::new("library-standard-instance-dedup");
    write(scratch.path(), "numbers/lib.lim", "(#export read) (#std) (#fn read () #u64 (#let text String (#call String::new ())) (#call String::free (: string text)) (#return 42u64))");
    check_cache_modes(scratch.path(), "(#std) (#import-external \"numbers/lib.lim\" first) (#import-external \"numbers/lib.lim\" second) (#fn main () #u64 (#return 0u64))", None);
    // Also reach std first through a library: it must not capture that
    // instance's prefix on its types or named parameter labels.
    check_cache_modes(scratch.path(), "(#import-external \"numbers/lib.lim\" first) (#import-external \"numbers/lib.lim\" second) (#std) (#fn main () #u64 (#let text String (#call String::new ())) (#call String::free (: string text)) (#return 0u64))", None);
}

#[test]
fn exported_generators_can_use_private_nested_generators_transitively() {
    let scratch = support::Scratch::new("library-nested-generator-implementation");
    write(scratch.path(), "leaf/lib.lim", "(#export make) (#gn implementation (name) `((#type ,(#gn-symbol name) #u64))) (#gn make (name) `((#generate implementation ,name)))");
    write(scratch.path(), "middle/lib.lim", "(#export build) (#import-external \"../leaf/lib.lim\" leaf) (#gn build (name) `((#generate leaf@make ,name)))");
    check_cache_modes(scratch.path(), "(#import-external \"middle/lib.lim\" middle) (#generate middle@build \"ApplicationNumber\") (#fn main () #u64 (#let number ApplicationNumber 42u64) (#return number))", None);
    check_cache_modes(scratch.path(), "(#import-external \"middle/lib.lim\" middle) (#generate middle@leaf@make \"ApplicationNumber\") (#fn main () #u64 (#return 0u64))", Some("not automatically re-exported"));
    check_cache_modes(scratch.path(), "(#import-external \"middle/lib.lim\" middle) (#generate middle@leaf@implementation \"ApplicationNumber\") (#fn main () #u64 (#return 0u64))", Some("private"));
    write(scratch.path(), "middle/lib.lim", "(#export build) (#import-external \"../leaf/lib.lim\" leaf) (#gn build (name) `((#generate leaf@make ,name))) (#generate build \"Hidden\")");
    for imports in [
        "(#import-external \"middle/lib.lim\" middle) (#generate middle@build \"Hidden\")",
        "(#generate middle@build \"Hidden\") (#import-external \"middle/lib.lim\" middle)",
    ] {
        check_cache_modes(
            scratch.path(),
            &format!("{imports} (#fn main () #u64 (#return 0u64))"),
            Some("duplicate"),
        );
    }
}

#[test]
fn hygienic_names_are_fresh_per_expansion_instance_on_cache_hits() {
    let scratch = support::Scratch::new("library-instance-gensym");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "(#export make) (#gn make () `((#type ,(#gn-gensym \"hidden\") #u64))) (#generate make)",
    );
    for imports in [
        "(#import-external \"numbers/lib.lim\" nums) (#generate nums@make)",
        "(#generate nums@make) (#import-external \"numbers/lib.lim\" nums)",
    ] {
        check_cache_modes(
            scratch.path(),
            &format!("{imports} (#fn main () #u64 (#return 0u64))"),
            None,
        );
    }
}

#[test]
fn generated_only_libraries_retain_their_import_ancestry() {
    let scratch = support::Scratch::new("generated-only-library-ancestry");
    write(
        scratch.path(),
        "leaf/lib.lim",
        "(#export make) (#gn make (name) `((#type ,name #u64)))",
    );
    write(
        scratch.path(),
        "middle/lib.lim",
        "(#export Number) (#import-external \"../leaf/lib.lim\" leaf) (#generate leaf@make Number)",
    );
    check_cache_modes(
        scratch.path(),
        "(#import-external \"middle/lib.lim\" middle) (#fn main () middle@Number (#return 42u64))",
        None,
    );
}

#[test]
fn import_identity_delimiters_cannot_alias_other_paths_and_prefixes() {
    let scratch = support::Scratch::new("import-identity-delimiters");
    write(
        scratch.path(),
        "first:external:second",
        "(#fn read () #u64 (#return 1u64))",
    );
    write(scratch.path(), "first", "(#fn read () #u64 (#return 2u64))");
    check_cache_modes(scratch.path(), "(#import-external \"first:external:second\" p) (#import-external \"first\" second:external:p) (#fn main () #u64 (#return (#u64::add-wrap (#call p@read ()) (#call second:external:p@read ()))))", None);
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
    write(scratch.path(), "numbers/lib.lim", "(#export Value) (#struct Secret () ((value #u64))) (#enum Value () ((Value.Public Secret)))");
    let error = check(
        scratch.path(),
        "main.lim",
        "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#return 0u64))",
    )
    .unwrap_err();
    assert!(error.contains("exposes private type"), "{error}");
}

#[test]
fn exported_enums_expose_every_variant_but_contributions_stay_internal() {
    let scratch = support::Scratch::new("library-enums");
    write(scratch.path(), "numbers/lib.lim", "(#export Number Events) (#enum Number () ((Number.Value #u64) Number.Empty)) (#distributed-enum Events ()) (#enum-contribute Events (Events.Added #u64))");
    for body in [
        "(#fn main () #u64 (#let value nums@Number (#enum-literal nums@Number.Value 42u64)) (#return (#match value (#case (nums@Number.Value payload) payload) (#case nums@Number.Empty 0u64))))",
        "(#fn main () #u64 (#let value nums@Number (#enum-literal nums@Number.Empty)) (#return (#match value (#case (nums@Number.Value payload) payload) (#case nums@Number.Empty 42u64))))",
        "(#fn main () #u64 (#let value nums@Events (#enum-literal nums@Events.Added 42u64)) (#return (#match value (#case (nums@Events.Added payload) payload))))",
    ] {
        let source = format!("(#import-external \"numbers/lib.lim\" nums) {body}");
        check_cache_modes(scratch.path(), &source, None);
    }
    for body in [
        "(#enum-contribute nums@Events (nums@Events.Forged #u64)) (#fn main () #u64 (#return 0u64))",
        "(#gn forge () `((#enum-contribute nums@Events (nums@Events.Forged #u64)))) (#generate forge) (#fn main () #u64 (#return 0u64))",
    ] {
        let source = format!("(#import-external \"numbers/lib.lim\" nums) {body}");
        let error = check(scratch.path(), "main.lim", &source).unwrap_err();
        assert!(error.contains("private"), "{error}");
    }
    check_cache_modes(scratch.path(), "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#let value nums@Number (#enum-literal nums@Number.Value 42u64)) (#return (#match value (#case (nums@Number.Value payload) payload))))", Some("not exhaustive"));
}

#[test]
fn individual_variant_exports_are_rejected() {
    let scratch = support::Scratch::new("library-variant-export");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "(#export Number Number.Value) (#enum Number () ((Number.Value #u64)))",
    );
    check_cache_modes(
        scratch.path(),
        "(#import-external \"numbers/lib.lim\" nums)",
        Some("not individual variants"),
    );
}

#[test]
fn every_public_enum_payload_must_be_public_even_when_unused_or_generated() {
    let scratch = support::Scratch::new("library-enum-payloads");
    for declaration in [
        "(#enum Value () (Value.Empty (Value.Hidden Secret)))",
        "(#enum Value () (Value.Empty (Value.Hidden (#ref Secret))))",
        "(#enum Value () (Value.Empty (Value.Hidden (#tuple #u64 Secret))))",
        "(#type Alias Secret) (#enum Value () (Value.Empty (Value.Hidden Alias)))",
        "(#generate #optional (: type Secret : name Value))",
        "(#distributed-enum Value ()) (#enum-contribute Value (Value.Hidden Secret))",
    ] {
        write(
            scratch.path(),
            "numbers/lib.lim",
            &format!("(#export Value) (#struct Secret () (: value #u64)) {declaration}"),
        );
        check_cache_modes(
            scratch.path(),
            "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#return 0u64))",
            Some("exposes private type"),
        );
    }
}

#[test]
fn opaque_structs_can_wrap_private_enums_and_be_public_enum_payloads() {
    let scratch = support::Scratch::new("library-opaque-enum-wrapper");
    let library = include_str!("../examples/opaque_handle/lib.lim");
    write(scratch.path(), "opaque_handle/lib.lim", library);
    check_cache_modes(
        scratch.path(),
        include_str!("../examples/opaque_handle.lim"),
        None,
    );
    write(scratch.path(), "opaque_handle/lib.lim", &format!("{library}\n(#export Container) (#enum Container (#linear) (: Container.Handle Handle))"));
    check_cache_modes(scratch.path(), "(#import-external \"opaque_handle/lib.lim\" api) (#fn main () #u64 (#let value api@Container (#enum-literal api@Container.Handle (#call api@handle-create (: api@value 42u64)))) (#match value (#case (api@Container.Handle handle) (#call api@handle-close (: api@handle handle)))) (#return 42u64))", None);
    for body in [
        "(#let value api@InternalState (#enum-literal api@InternalState.Closed))",
        "(#match (#enum-literal api@InternalState.Closed) (#case api@InternalState.Closed ()) (#case (api@InternalState.Open value) ()))",
        "(#let value api@Handle (#call api@handle-create (: api@value 42u64))) (#if-let (api@Handle state) value (#forget state) ())",
        "(#let value api@Container (#enum-literal api@Container.Handle (#call api@handle-create (: api@value 42u64)))) (#match value (#case (api@Container.Handle handle) (#if-let (api@Handle state) handle (#forget state) ())))",
        "(#let value api@Handle (#struct-literal api@Handle (: api@state (#enum-literal api@InternalState.Closed))))",
        "(#let value api@Handle (#call api@handle-create (: api@value 42u64))) (#let field (#ref api@InternalState) (#borrow (#get value api@state))) (#forget value)",
        "(#let value api@Handle (#call api@handle-create (: api@value 42u64))) (#let field #u64 (#match (#get value api@state) (#case api@InternalState.Closed 0u64) (#case (api@InternalState.Open payload) payload))) (#forget value)",
    ] {
        check_cache_modes(scratch.path(), &format!("(#import-external \"opaque_handle/lib.lim\" api) (#fn main () #u64 {body} (#return 0u64))"), Some("private"));
    }
}

#[test]
fn exported_generated_enums_support_borrowed_variant_matches() {
    let scratch = support::Scratch::new("library-generated-public-enum");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "(#export Value) (#generate #optional (: type #u64 : name Value))",
    );
    check_cache_modes(scratch.path(), "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#let value nums@Value (#enum-literal nums@Value.Some 42u64)) (#let view (#ref nums@Value) (#borrow value)) (#return (#match view (#case-ref (nums@Value.Some payload) (#deref payload)) (#case-ref nums@Value.None 0u64))))", None);
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
fn private_enum_payload_diagnostics_underline_the_type() {
    let scratch = support::Scratch::new("library-enum-payload-diagnostic");
    let library = "(#export Value)\n(#struct Secret () (: value #u64))\n(#enum Value () (: Value.Visible #u64 : Value.Hidden Secret))\n";
    write(scratch.path(), "numbers/lib.lim", library);
    let source = "(#import-external \"numbers/lib.lim\" nums) (#fn main () #u64 (#return 0u64))";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join(".lim/cache"),
        lim::TargetDescription::host().unwrap(),
    )
    .unwrap_err();
    assert!(
        error.message.contains("exposes private type"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert_eq!(span.line, 3);
    assert_eq!(&library[span.start..span.end], "Secret");
}

#[test]
fn native_thread_entry_points_are_private_unless_exported() {
    let scratch = support::Scratch::new("library-native-privacy");
    let implementation = "(#export Task Task::join Task::SpawnResult Task::SpawnError Task::JoinResult) (#fn worker () #u64 (#return 42u64)) (#generate #thread-spawn (: task Task : worker worker))";
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
