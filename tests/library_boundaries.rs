mod support;
use std::{fs, path::Path};

fn write(base: &Path, path: &str, source: &str) {
    let path = base.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

fn library(base: &Path) {
    write(base, "collection/lib.lim", "#export Collection collection-new collection-read collection-destroy\n#alias Collection = ./storage.lim::Collection\n#alias collection-new = ./storage.lim::collection-new\n#alias collection-read = ./storage.lim::collection-read\n#alias collection-destroy = ./storage.lim::collection-destroy\n");
    write(
        base,
        "collection/storage.lim",
        "
#struct Collection (#linear) ((capacity #u64))
#fn private-capacity {
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)
  );
}
#fn collection-new {
  #params = ();
  #returns = Collection;
  #body = (
          (#return (#struct-literal Collection ((capacity (#call private-capacity ())))))
  );
}
#fn collection-read {
  #params = ((value (#ref Collection)));
  #returns = #u64;
  #body = ( (#return (#get value capacity))
  );
}
#fn collection-destroy {
  #params = ((value Collection));
  #returns = ();
  #body = ( (#forget value) (#return ())\n  );\n}\n",
    );
}

fn check(base: &Path, path: &str, source: &str) -> Result<(), String> {
    let program = lim::parse_program_from_path(source, &base.join(path))?;
    lim::check_types(&program)
}

// Exercise ownership independently of whether expansions came from the
// interpreter or persistent cache, and repeat to cover warm-cache paths.
fn check_cache_modes(base: &Path, source: &str, expected_error: Option<&str>) {
    check_cache_modes_with_identities(base, source, expected_error, &[]);
}

fn check_cache_modes_with_identities(
    base: &Path,
    source: &str,
    expected_error: Option<&str>,
    identities: &[(&str, &str)],
) {
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
        let result = parsed.and_then(|program| {
            lim::check_types(&program)?;
            for (path, name) in identities {
                let expected = format!(
                    "{}::{name}",
                    fs::canonicalize(base.join(path)).unwrap().display()
                );
                let count = program
                    .items
                    .iter()
                    .filter(|item| match item {
                        lim::Item::TypeAlias { name, .. }
                        | lim::Item::Enum { name, .. }
                        | lim::Item::Struct { name, .. } => name == &expected,
                        lim::Item::Function(function) => function.name == expected,
                        _ => false,
                    })
                    .count();
                assert_eq!(
                    count, 1,
                    "mode {mode}: expected one canonical declaration {expected}"
                );
            }
            Ok(())
        });
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
    // Identical inputs expand in their invocation files. Their canonical
    // identities must remain distinct on cold and warm cache paths.
    write(scratch.path(), "numbers/lib.lim", "#export make\n#gn make (name) `((#type ,(#gn-symbol name) #u64))\n#generate make \"Hidden\"\n");
    write(scratch.path(), "main.lim", "");
    for imports in [
        "#alias nums@make = ./numbers/lib.lim::make\n#generate nums@make \"Hidden\"\n",
        "#generate nums@make \"Hidden\"\n#alias nums@make = ./numbers/lib.lim::make\n",
    ] {
        let source = format!("{imports}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n");
        check_cache_modes_with_identities(
            scratch.path(),
            &source,
            None,
            &[("numbers/lib.lim", "Hidden"), ("main.lim", "Hidden")],
        );
    }
}

#[test]
fn repeated_aliases_share_their_internal_dependencies() {
    let scratch = support::Scratch::new("library-instance-internal-imports");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "#export read\n#alias read = ./implementation.lim::read\n",
    );
    write(
        scratch.path(),
        "numbers/implementation.lim",
        "#generate #optional ((type #u64) (name Number))\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n",
    );
    check_cache_modes_with_identities(scratch.path(), "#alias first@read = ./numbers/lib.lim::read\n#alias second@read = ./numbers/lib.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#u64::add-wrap (#call first@read ()) (#call second@read ())))\n  );\n}\n", None, &[("numbers/implementation.lim", "read")]);
}

#[test]
fn repeated_aliases_share_transitive_dependencies() {
    let scratch = support::Scratch::new("library-instance-transitive-imports");
    write(
        scratch.path(),
        "leaf/lib.lim",
        "#export read\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n",
    );
    write(scratch.path(), "middle/lib.lim", "#export read\n#alias leaf@read = ../leaf/lib.lim::read\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call leaf@read ()))\n  );\n}\n");
    check_cache_modes_with_identities(scratch.path(), "#alias first@read = ./middle/lib.lim::read\n#alias second@read = ./middle/lib.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#u64::add-wrap (#call first@read ()) (#call second@read ())))\n  );\n}\n", None, &[("middle/lib.lim", "read"), ("leaf/lib.lim", "read")]);
}

#[test]
fn nested_builtin_expansions_do_not_merge_across_boundaries() {
    let scratch = support::Scratch::new("library-builtin-expansion-ownership");
    write(scratch.path(), "numbers/lib.lim", "#export make\n#gn make (name) `((#generate #optional ((type #u64) (name ,(#gn-symbol name)))))\n#generate make \"Hidden\"\n");
    write(scratch.path(), "main.lim", "");
    for imports in [
        "#alias nums@make = ./numbers/lib.lim::make\n#generate nums@make \"Hidden\"\n",
        "#generate nums@make \"Hidden\"\n#alias nums@make = ./numbers/lib.lim::make\n",
    ] {
        check_cache_modes_with_identities(
            scratch.path(),
            &format!("{imports}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n"),
            None,
            &[("numbers/lib.lim", "Hidden"), ("main.lim", "Hidden")],
        );
    }
}

#[test]
fn identical_expansions_still_deduplicate_inside_one_source_file() {
    let scratch = support::Scratch::new("library-local-expansion-dedup");
    write(scratch.path(), "numbers/lib.lim", "#export read\n#gn make (name) `((#type ,(#gn-symbol name) #u64))\n#generate make \"Hidden\"\n#generate make \"Hidden\"\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value Hidden 42u64) (#return value)\n  );\n}\n");
    check_cache_modes_with_identities(
        scratch.path(),
        "#alias read = ./numbers/lib.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call read ()))\n  );\n}\n",
        None,
        &[("numbers/lib.lim", "Hidden")],
    );
}

#[test]
fn generated_references_cannot_guess_another_librarys_private_declarations() {
    let scratch = support::Scratch::new("library-generated-private-access");
    write(scratch.path(), "numbers/lib.lim", "#export read\n#fn secret {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call secret ()))\n  );\n}\n");
    let secret = format!(
        "{}::secret",
        scratch.path().join("numbers/lib.lim").display()
    );
    let source = format!("#alias first = ./numbers/lib.lim::read\n#alias second = ./numbers/lib.lim::read\n#gn forge (target) `((#fn stolen () #u64 (#return (#call ,(#gn-symbol target) ()))))\n#generate forge {secret:?}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n");
    check_cache_modes(scratch.path(), &source, Some("private"));
}

#[test]
fn standard_declarations_are_shared_through_multiple_aliases() {
    let scratch = support::Scratch::new("library-standard-instance-dedup");
    write(scratch.path(), "numbers/lib.lim", "#export read\n#std\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #effects = ((#effects-of String::free)); #body = ( (#let text String (#call String::new ())) (#call String::free ((string text))) (#return 42u64)\n  );\n}\n");
    check_cache_modes(scratch.path(), "#std\n#alias first@read = ./numbers/lib.lim::read\n#alias second@read = ./numbers/lib.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n", None);
    // Loading std through a library first preserves its identities and labels.
    check_cache_modes(scratch.path(), "#alias first@read = ./numbers/lib.lim::read\n#alias second@read = ./numbers/lib.lim::read\n#std\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #effects = ((#effects-of String::free)); #body = ( (#let text String (#call String::new ())) (#call String::free ((string text))) (#return 0u64)\n  );\n}\n", None);
}

#[test]
fn exported_generators_can_use_private_nested_generators_transitively() {
    let scratch = support::Scratch::new("library-nested-generator-implementation");
    write(scratch.path(), "leaf/lib.lim", "#export make\n#gn implementation (name) `((#type ,(#gn-symbol name) #u64))\n#gn make (name) `((#generate implementation ,name))\n");
    write(scratch.path(), "middle/lib.lim", "#export build\n#alias leaf@make = ../leaf/lib.lim::make\n#gn build (name) `((#generate leaf@make ,name))\n");
    check_cache_modes(scratch.path(), "#alias middle@build = ./middle/lib.lim::build\n#generate middle@build \"ApplicationNumber\"\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let number ApplicationNumber 42u64) (#return number)\n  );\n}\n", None);
    check_cache_modes(scratch.path(), "#alias middle@leaf@make = ./middle/lib.lim::leaf@make\n#generate middle@leaf@make \"ApplicationNumber\"\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n", Some("not exported"));
    check_cache_modes(scratch.path(), "#alias middle@leaf@implementation = ./middle/lib.lim::leaf@implementation\n#generate middle@leaf@implementation \"ApplicationNumber\"\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n", Some("private"));
    write(scratch.path(), "middle/lib.lim", "#export build\n#alias leaf@make = ../leaf/lib.lim::make\n#gn build (name) `((#generate leaf@make ,name))\n#generate build \"Hidden\"\n");
    for imports in [
        "#alias middle@build = ./middle/lib.lim::build\n#generate middle@build \"Hidden\"\n",
        "#generate middle@build \"Hidden\"\n#alias middle@build = ./middle/lib.lim::build\n",
    ] {
        check_cache_modes(
            scratch.path(),
            &format!("{imports}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n"),
            None,
        );
    }
}

#[test]
fn hygienic_names_are_fresh_per_expansion_instance_on_cache_hits() {
    let scratch = support::Scratch::new("library-instance-gensym");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "#export make\n#gn make () `((#type ,(#gn-gensym \"hidden\") #u64))\n#generate make\n",
    );
    for imports in [
        "#alias nums@make = ./numbers/lib.lim::make\n#generate nums@make\n",
        "#generate nums@make\n#alias nums@make = ./numbers/lib.lim::make\n",
    ] {
        check_cache_modes(
            scratch.path(),
            &format!("{imports}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n"),
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
        "#export make\n#gn make (name) `((#type ,name #u64))\n",
    );
    write(
        scratch.path(),
        "middle/lib.lim",
        "#export Number\n#alias leaf@make = ../leaf/lib.lim::make\n#generate leaf@make Number\n",
    );
    check_cache_modes(
        scratch.path(),
        "#alias middle@Number = ./middle/lib.lim::Number\n#fn main {\n  #params = ();\n  #returns = middle@Number;\n  #body = ( (#return 42u64)\n  );\n}\n",
        None,
    );
}

#[test]
fn canonical_path_delimiters_cannot_alias_other_files() {
    let scratch = support::Scratch::new("import-identity-delimiters");
    write(
        scratch.path(),
        "first:external:second.lim",
        "#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 1u64)\n  );\n}\n",
    );
    write(
        scratch.path(),
        "first.lim",
        "#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 2u64)\n  );\n}\n",
    );
    check_cache_modes(scratch.path(), "#alias p@read = ./first:external:second.lim::read\n#alias second:external:p@read = ./first.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#u64::add-wrap (#call p@read ()) (#call second:external:p@read ())))\n  );\n}\n", None);
}

#[test]
fn public_api_runs_with_explicit_aliases_and_no_public_representation() {
    let scratch = support::Scratch::new("library-api");
    library(scratch.path());
    let source = "#alias collections@Collection = ./collection/lib.lim::Collection
#alias collections@collection-destroy = ./collection/lib.lim::collection-destroy
#alias collections@collection-new = ./collection/lib.lim::collection-new
#alias collections@collection-read = ./collection/lib.lim::collection-read
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let value collections@Collection (#call collections@collection-new ()))
          (#let answer #u64 (#call collections@collection-read ((value (#borrow value)))))
          (#call collections@collection-destroy ((value value)))
          (#return answer)\n  );\n}\n";
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
        "#alias hidden = ./collection/lib.lim::private-capacity\n",
        "#alias Collection = ./collection/storage.lim::Collection\n",
        "#alias hidden = ./collection/storage.lim::private-capacity\n",
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
        "(#return (#call ./collection/lib.lim::private-capacity ()))",
        "(#let value collections@Collection (#struct-literal collections@Collection ((capacity 42u64)))) (#forget value) (#return 0u64)",
        "(#let value collections@Collection (#call collections@collection-new ())) (#let answer #u64 (#get value capacity)) (#call collections@collection-destroy ((value value))) (#return answer)",
        "(#let-mut value collections@Collection (#call collections@collection-new ())) (#set (#get value capacity) 0u64) (#call collections@collection-destroy ((value value))) (#return 0u64)",
        "(#let-mut value collections@Collection (#call collections@collection-new ())) (#let field (#ref-mut #u64) (#borrow-mut (#get value capacity))) (#deref-set field 0u64) (#call collections@collection-destroy ((value value))) (#return 0u64)",
        "(#let value collections@Collection (#call collections@collection-new ())) (#let answer #u64 (#if-let (collections@Collection capacity) value capacity 0u64)) (#return answer)",
    ] {
        let source = format!("#alias collections@Collection = ./collection/lib.lim::Collection\n#alias collections@collection-destroy = ./collection/lib.lim::collection-destroy\n#alias collections@collection-new = ./collection/lib.lim::collection-new\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( {body}\n  );\n}}\n");
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
        "#alias private-capacity = ./storage.lim::private-capacity\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call private-capacity ()))\n  );\n}\n",
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
        "#export utility-read\n#alias utility-read = ./implementation.lim::utility-read\n",
    );
    write(
        scratch.path(),
        "collection/utility/implementation.lim",
        "#fn utility-read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 7u64)\n  );\n}\n",
    );
    assert!(check(
        scratch.path(),
        "collection/test.lim",
        "#alias utility-read = ./utility/implementation.lim::utility-read\n"
    )
    .is_err());
    assert!(check(
        scratch.path(),
        "collection/utility/test.lim",
        "#alias Collection = ../storage.lim::Collection\n"
    )
    .is_err());
    check(scratch.path(), "collection/test.lim", "#alias util@utility-read = ./utility/lib.lim::utility-read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call util@utility-read ()))\n  );\n}\n").unwrap();
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
    assert!(check(scratch.path(), "main.lim", "#alias Collection = ./storage.lim::Collection\n#alias collection-new = ./storage.lim::collection-new\n#alias collection-read = ./storage.lim::collection-read\n#alias collection-destroy = ./storage.lim::collection-destroy\n").is_err());
}

#[test]
fn generated_caller_code_has_no_private_library_privileges() {
    let scratch = support::Scratch::new("library-generated-access");
    library(scratch.path());
    let source = "#alias Collection = ./collection/lib.lim::Collection
#gn forge () `((#fn main () #u64 (#return (#call ./collection/lib.lim::private-capacity ()))))
#generate forge\n";
    let error = check(scratch.path(), "main.lim", source).unwrap_err();
    assert!(error.contains("private"), "{error}");
}

#[test]
fn explicit_aliases_require_a_declaration_and_preserve_type_identity() {
    let scratch = support::Scratch::new("library-explicit-alias");
    library(scratch.path());
    for source in [
        "#alias Collection ./collection/lib.lim::Collection\n",
        "#alias #u64 = ./collection/lib.lim::Collection\n",
        "#alias Collection = ./collection/lib.lim\n",
        "#alias Collection = ./collection/lib.lim::missing\n",
        "#alias Collection = ./collection/lib.lim::Collection\n#alias Collection = ./collection/lib.lim::Collection\n",
    ] {
        assert!(check(scratch.path(), "main.lim", source).is_err(), "{source}");
    }
    check_cache_modes(scratch.path(), "#alias First = ./collection/lib.lim::Collection\n#alias Second = ./collection/lib.lim::Collection\n#alias create = ./collection/lib.lim::collection-new\n#alias destroy = ./collection/lib.lim::collection-destroy\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value First (#call create ())) (#let same Second value) (#call destroy ((value same))) (#return 42u64)\n  );\n}\n", None);
    let expressions = lim::parse("collections@Collection collections@collection-new").unwrap();
    assert_eq!(expressions.len(), 2);
    assert!(lim::parse_program("(@#optional ((type #u64) (name Number)))").is_err());
    check_cache_modes(
        scratch.path(),
        "#generate #optional ((type #u64) (name Number))\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
        None,
    );
}

#[test]
fn aliases_and_global_initializers_cannot_expose_or_construct_private_storage() {
    let scratch = support::Scratch::new("library-global-privacy");
    write(scratch.path(), "numbers/lib.lim", "#export Number number\n#struct Number () ((value #u64))\n#const number Number (#struct-literal Number ((value 42u64)))\n");
    for body in [
        "#const forged nums@Number (#struct-literal nums@Number ((value 0u64)))\n",
        "#type Alias nums@Number\n#const copied Alias nums@number\n#const exposed #u64 (#get copied value)\n",
        "#const exposed #u64 (#get nums@number value)\n",
        "#let exposed #u64 (#get nums@number value)\n",
    ] {
        let source = format!("#alias nums@Number = ./numbers/lib.lim::Number\n#alias nums@number = ./numbers/lib.lim::number\n{body}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n");
        let error = check(scratch.path(), "main.lim", &source).unwrap_err();
        assert!(error.contains("private"), "{error}");
    }
}

#[test]
fn exported_signatures_must_not_leak_private_types() {
    let scratch = support::Scratch::new("library-signature");
    write(scratch.path(), "numbers/lib.lim", "#export read\n#struct Secret () ((value #u64))\n#fn read {\n  #params = ();\n  #returns = Secret;\n  #body = ( (#return (#struct-literal Secret ((value 42u64))))\n  );\n}\n");
    let error = check(
        scratch.path(),
        "main.lim",
        "#alias nums@read = ./numbers/lib.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
    )
    .unwrap_err();
    assert!(error.contains("exposes private type"), "{error}");
    write(scratch.path(), "numbers/lib.lim", "#export Value\n#struct Secret () ((value #u64))\n#enum Value () ((Value.Public Secret))\n");
    let error = check(
        scratch.path(),
        "main.lim",
        "#alias nums@Value = ./numbers/lib.lim::Value\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
    )
    .unwrap_err();
    assert!(error.contains("exposes private type"), "{error}");
}

#[test]
fn exported_enums_expose_every_variant_but_contributions_stay_internal() {
    let scratch = support::Scratch::new("library-enums");
    write(scratch.path(), "numbers/lib.lim", "#export Number Events\n#enum Number () ((Number.Value #u64) Number.Empty)\n#distributed-enum Events ()\n#enum-contribute Events (Events.Added #u64)\n");
    for body in [
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value nums@Number (#enum-literal nums@Number.Value 42u64)) (#return (#match value (#case (nums@Number.Value payload) payload) (#case nums@Number.Empty 0u64)))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value nums@Number (#enum-literal nums@Number.Empty)) (#return (#match value (#case (nums@Number.Value payload) payload) (#case nums@Number.Empty 42u64)))\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value nums@Events (#enum-literal nums@Events.Added 42u64)) (#return (#match value (#case (nums@Events.Added payload) payload)))\n  );\n}\n",
    ] {
        let source = format!("#alias nums@Events = ./numbers/lib.lim::Events\n#alias nums@Number = ./numbers/lib.lim::Number\n{body}");
        check_cache_modes(scratch.path(), &source, None);
    }
    for body in [
        "#enum-contribute nums@Events (nums@Events.Forged #u64)\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
        "#gn forge () `((#enum-contribute nums@Events (nums@Events.Forged #u64)))\n#generate forge\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
    ] {
        let source = format!("#alias nums@Events = ./numbers/lib.lim::Events\n#alias nums@Number = ./numbers/lib.lim::Number\n{body}");
        let error = check(scratch.path(), "main.lim", &source).unwrap_err();
        assert!(error.contains("private"), "{error}");
    }
    check_cache_modes(scratch.path(), "#alias nums@Number = ./numbers/lib.lim::Number\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value nums@Number (#enum-literal nums@Number.Value 42u64)) (#return (#match value (#case (nums@Number.Value payload) payload)))\n  );\n}\n", Some("not exhaustive"));
}

#[test]
fn individual_variant_exports_are_rejected() {
    let scratch = support::Scratch::new("library-variant-export");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "#export Number Number.Value\n#enum Number () ((Number.Value #u64))\n",
    );
    check_cache_modes(
        scratch.path(),
        "#alias nums@Number = ./numbers/lib.lim::Number\n",
        Some("not individual variants"),
    );
}

#[test]
fn every_public_enum_payload_must_be_public_even_when_unused_or_generated() {
    let scratch = support::Scratch::new("library-enum-payloads");
    for declaration in [
        "#enum Value () (Value.Empty (Value.Hidden Secret))\n",
        "#enum Value () (Value.Empty (Value.Hidden (#ref Secret)))\n",
        "#enum Value () (Value.Empty (Value.Hidden (#tuple #u64 Secret)))\n",
        "#type Alias Secret\n#enum Value () (Value.Empty (Value.Hidden Alias))\n",
        "#generate #optional ((type Secret) (name Value))\n",
        "#distributed-enum Value ()\n#enum-contribute Value (Value.Hidden Secret)\n",
    ] {
        write(
            scratch.path(),
            "numbers/lib.lim",
            &format!("#export Value\n#struct Secret () ((value #u64))\n{declaration}"),
        );
        check_cache_modes(
            scratch.path(),
            "#alias nums@Value = ./numbers/lib.lim::Value\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
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
    write(scratch.path(), "opaque_handle/lib.lim", &format!("{library}\n#export Container\n#enum Container (#linear) ((Container.Handle Handle))\n"));
    check_cache_modes(scratch.path(), "#alias api@handle-create = ./opaque_handle/lib.lim::handle-create\n#alias api@handle-close = ./opaque_handle/lib.lim::handle-close\n#alias api@Container = ./opaque_handle/lib.lim::Container\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value api@Container (#enum-literal api@Container.Handle (#call api@handle-create ((value 42u64))))) (#match value (#case (api@Container.Handle handle) (#call api@handle-close ((handle handle))))) (#return 42u64)\n  );\n}\n", None);
    for body in [
        "(#let value ./opaque_handle/lib.lim::InternalState (#enum-literal ./opaque_handle/lib.lim::InternalState.Closed))",
        "(#match (#enum-literal ./opaque_handle/lib.lim::InternalState.Closed) (#case ./opaque_handle/lib.lim::InternalState.Closed ()) (#case (./opaque_handle/lib.lim::InternalState.Open value) ()))",
        "(#let value api@Handle (#call api@handle-create ((value 42u64)))) (#if-let (api@Handle state) value (#forget state) ())",
        "(#let value api@Container (#enum-literal api@Container.Handle (#call api@handle-create ((value 42u64))))) (#match value (#case (api@Container.Handle handle) (#if-let (api@Handle state) handle (#forget state) ())))",
        "(#let value api@Handle (#struct-literal api@Handle ((state (#enum-literal ./opaque_handle/lib.lim::InternalState.Closed)))))",
        "(#let value api@Handle (#call api@handle-create ((value 42u64)))) (#let field (#ref ./opaque_handle/lib.lim::InternalState) (#borrow (#get value state))) (#forget value)",
        "(#let value api@Handle (#call api@handle-create ((value 42u64)))) (#let field #u64 (#match (#get value state) (#case ./opaque_handle/lib.lim::InternalState.Closed 0u64) (#case (./opaque_handle/lib.lim::InternalState.Open payload) payload))) (#forget value)",
    ] {
        check_cache_modes(scratch.path(), &format!("#alias api@handle-create = ./opaque_handle/lib.lim::handle-create\n#alias api@handle-close = ./opaque_handle/lib.lim::handle-close\n#alias api@Container = ./opaque_handle/lib.lim::Container\n#alias api@Handle = ./opaque_handle/lib.lim::Handle\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( {body} (#return 0u64)\n  );\n}}\n"), Some("private"));
    }
}

#[test]
fn exported_generated_enums_support_borrowed_variant_matches() {
    let scratch = support::Scratch::new("library-generated-public-enum");
    write(
        scratch.path(),
        "numbers/lib.lim",
        "#export Value\n#generate #optional ((type #u64) (name Value))\n",
    );
    check_cache_modes(scratch.path(), "#alias nums@Value = ./numbers/lib.lim::Value\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value nums@Value (#enum-literal nums@Value.Some 42u64)) (#let view (#ref nums@Value) (#borrow value)) (#return (#match view (#case-ref (nums@Value.Some payload) (#deref payload)) (#case-ref nums@Value.None 0u64)))\n  );\n}\n", None);
}

#[test]
fn generator_helpers_are_private_even_when_called_inside_unquotes() {
    let scratch = support::Scratch::new("library-generator-privacy");
    write(scratch.path(), "numbers/lib.lim", "#export public\n#gn-fn helper () `((#type Number #u64))\n#gn public () (#gn-call helper)\n#gn private () (#gn-call helper)\n");
    check(scratch.path(), "main.lim", "#alias nums@public = ./numbers/lib.lim::public\n#generate nums@public\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n").unwrap();
    for body in [
        "#generate ./numbers/lib.lim::private\n",
        "#gn forge () (#gn-call ./numbers/lib.lim::helper)\n#generate forge\n",
        "#gn forge () `((#type Number ,(#gn-first (#gn-call ./numbers/lib.lim::helper))))\n#generate forge\n",
        "#gn forge () `((#generate ./numbers/lib.lim::private))\n#generate forge\n",
    ] {
        let source = format!(
            "#alias nums@public = ./numbers/lib.lim::public\n{body}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n"
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
        "#export main\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n"
    )
    .is_err());
    write(
        scratch.path(),
        "numbers/lib.lim",
        "#export read\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n#gn forge () `((#export main))\n#generate forge\n",
    );
    let error = check(
        scratch.path(),
        "main.lim",
        "#alias read = ./numbers/lib.lim::read\n",
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
        "#std\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
    )
    .unwrap();
}

#[test]
fn nested_dependency_exports_are_not_automatically_reexported() {
    let scratch = support::Scratch::new("library-reexports");
    write(scratch.path(), "outer/lib.lim", "#export read\n#alias util@read = ./utility/lib.lim::read\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call util@read ()))\n  );\n}\n");
    write(
        scratch.path(),
        "outer/utility/lib.lim",
        "#export read\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n",
    );
    check(scratch.path(), "main.lim", "#alias outer@read = ./outer/lib.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call outer@read ()))\n  );\n}\n").unwrap();
    let error = check(scratch.path(), "main.lim", "#alias outer@util@read = ./outer/lib.lim::util@read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call outer@util@read ()))\n  );\n}\n").unwrap_err();
    assert!(error.contains("not exported"), "{error}");
}

#[test]
fn externally_imported_assembly_preserves_physical_register_names() {
    let scratch = support::Scratch::new("library-assembly");
    write(scratch.path(), "assembly.lim", "#fn identity {\n  #params = ((value #u64));\n  #returns = #u64;\n  #effects = (#global-access #io); #body = ( (#return (#unsafe (#asm #u64 ((rdi value)) \"mov rax, rdi\")))\n  );\n}\n");
    check(scratch.path(), "main.lim", "#alias machine@identity = ./assembly.lim::identity\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call machine@identity ((value 42u64))))\n  );\n}\n").unwrap();
    write(
        scratch.path(),
        "standard.lim",
        "#std\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
    );
    let source = "#alias standard@read = ./standard.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    lim::generate_assembly(&program).unwrap();
}

#[test]
fn private_field_diagnostics_underline_the_exact_source_token() {
    let scratch = support::Scratch::new("library-diagnostic");
    library(scratch.path());
    let source = "#alias collections@Collection = ./collection/lib.lim::Collection\n#alias collections@collection-destroy = ./collection/lib.lim::collection-destroy\n#alias collections@collection-new = ./collection/lib.lim::collection-new\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n    (#let value collections@Collection (#call collections@collection-new ()))\n    (#let result #u64 (#get value capacity))\n    (#call collections@collection-destroy ((value value)))\n    (#return result)\n  );\n}\n";
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
    assert_eq!(span.line, 9);
    assert_eq!(&source[span.start..span.end], "capacity");
    let rendered = lim::render_diagnostic(&error, source, path.to_str().unwrap());
    assert!(rendered.contains("capacity"));
    assert!(
        rendered.contains(&"^".repeat("capacity".len())),
        "{rendered}"
    );
}

#[test]
fn private_enum_payload_diagnostics_underline_the_type() {
    let scratch = support::Scratch::new("library-enum-payload-diagnostic");
    let library = "#export Value\n#struct Secret () ((value #u64))\n#enum Value () ((Value.Visible #u64) (Value.Hidden Secret))\n";
    write(scratch.path(), "numbers/lib.lim", library);
    let source = "#alias nums@Value = ./numbers/lib.lim::Value\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n";
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
    let implementation = "#export Task Task::join Task::SpawnResult Task::SpawnError Task::JoinResult\n#fn worker {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#generate #thread-spawn ((task Task) (worker worker))\n";
    write(scratch.path(), "workers/lib.lim", implementation);
    let source = "#alias workers@Task::JoinResult = ./workers/lib.lim::Task::JoinResult
#alias workers@Task::SpawnResult = ./workers/lib.lim::Task::SpawnResult
#alias workers@Task::join = ./workers/lib.lim::Task::join
#alias workers@Task::spawn = ./workers/lib.lim::Task::spawn
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return
          (#match (#call workers@Task::spawn ())
            (#case (workers@Task::SpawnResult.Ok task)
              (#match (#call workers@Task::join ((task task)))
                (#case (workers@Task::JoinResult.Ok result) result)
                (#case (workers@Task::JoinResult.Error (#tuple retry-task error-code)) (#panic))))
            (#case (workers@Task::SpawnResult.Error error) (#panic))))\n  );\n}\n";
    // Public result types do not make the native spawn entry point public.
    // Keep explicit aliases for native functions: exported generated signatures
    // must be valid alias targets, just like ordinary function declarations.
    let error = check(scratch.path(), "main.lim", source).unwrap_err();
    assert!(error.contains("private"), "{error}");
    assert!(error.contains("Task::spawn"), "{error}");
    write(
        scratch.path(),
        "workers/lib.lim",
        &implementation.replace("#export Task ", "#export Task Task::spawn "),
    );
    check(scratch.path(), "main.lim", source).unwrap();
    write(scratch.path(), "workers/lib.lim", "#export Task Task::spawn\n#fn worker {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#generate #thread-spawn ((task Task) (worker worker))\n");
    let error = check(
        scratch.path(),
        "main.lim",
        "#alias workers@Task = ./workers/lib.lim::Task\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n",
    )
    .unwrap_err();
    assert!(error.contains("exposes private type"), "{error}");
}

#[test]
fn unstable_aliases_do_not_grant_library_or_representation_permissions() {
    let scratch = support::Scratch::new("library-unstable-permissions");
    library(scratch.path());
    // The nearest lib.lim owns implementation files. External callers normally
    // use its exported aliases; #unstable opts into one implementation target.
    check_cache_modes(scratch.path(), "#alias capacity = (#unstable ./collection/storage.lim::private-capacity)\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call capacity ()))\n  );\n}\n", None);
    check_cache_modes(scratch.path(), "#alias capacity = (#unstable ./collection/storage.lim::private-capacity)\n#alias create = ./collection/storage.lim::collection-new\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call capacity ()))\n  );\n}\n", Some("private library implementation"));
    // Even opting into a type leaves its representation private.
    check_cache_modes(scratch.path(), "#alias Collection = (#unstable ./collection/storage.lim::Collection)\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value Collection (#struct-literal Collection ((capacity 42u64)))) (#forget value) (#return 0u64)\n  );\n}\n", Some("private"));
}
