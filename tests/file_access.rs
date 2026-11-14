mod support;
use std::{fs, path::Path};

fn write(base: &Path, path: &str, source: &str) {
    let path = base.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

fn check(base: &Path, source: &str) -> Result<(), String> {
    let program = lim::parse_program_from_path(source, &base.join("main.lim"))?;
    lim::check_types(&program)
}

#[test]
fn direct_calls_and_aliases_keep_source_parameter_labels() {
    let scratch = support::Scratch::new("file-alias-call");
    write(
        scratch.path(),
        "math.lim",
        "(#fn add ((value #u64)) #u64 (#return (#u64::add-wrap value 1u64)))",
    );
    for source in [
        "(#alias increment = ./math.lim::add) (#fn main () #u64 (#return (#call increment ((value 41u64)))))",
        "(#fn main () #u64 (#return (#call ./math.lim::add ((value 41u64)))))",
    ] { check(scratch.path(), source).unwrap(); }
}

#[test]
fn identical_names_in_distinct_files_do_not_collide() {
    let scratch = support::Scratch::new("file-alias-versions");
    write(
        scratch.path(),
        "v1/value.lim",
        "(#fn read () #u64 (#return 20u64))",
    );
    write(
        scratch.path(),
        "v2/value.lim",
        "(#fn read () #u64 (#return 22u64))",
    );
    check(scratch.path(), "(#alias first = ./v1/value.lim::read) (#alias second = ./v2/value.lim::read) (#fn main () #u64 (#return (#u64::add-wrap (#call first ()) (#call second ()))))").unwrap();
}

#[test]
fn facade_aliases_export_declarations_without_exporting_struct_fields() {
    let scratch = support::Scratch::new("file-alias-facade");
    write(scratch.path(), "value/lib.lim", "(#export Number create destroy) (#alias Number = ./impl.lim::Number) (#alias create = ./impl.lim::create) (#alias destroy = ./impl.lim::destroy)");
    write(scratch.path(), "value/impl.lim", "(#struct Number (#linear) ((value #u64))) (#fn create () Number (#return (#struct-literal Number ((value 42u64))))) (#fn destroy ((number Number)) () (#forget number) (#return ()))");
    let imports = "(#alias Number = ./value/lib.lim::Number) (#alias create = ./value/lib.lim::create) (#alias destroy = ./value/lib.lim::destroy)";
    check(scratch.path(), &format!("{imports} (#fn main () #u64 (#let number Number (#call create ())) (#call destroy ((number number))) (#return 42u64))")).unwrap();
    let error = check(scratch.path(), &format!("{imports} (#fn main () #u64 (#let number Number (#call create ())) (#let answer #u64 (#get number value)) (#call destroy ((number number))) (#return answer))")).unwrap_err();
    assert!(error.contains("private"), "{error}");
}

#[test]
fn unstable_is_explicit_and_target_specific() {
    let scratch = support::Scratch::new("file-alias-unstable");
    write(scratch.path(), "value/lib.lim", "(#export)");
    write(
        scratch.path(),
        "value/private.lim",
        "(#fn read () #u64 (#return 42u64)) (#fn secret () #u64 (#return 0u64))",
    );
    let error = check(
        scratch.path(),
        "(#alias read = ./value/private.lim::read) (#fn main () #u64 (#return (#call read ())))",
    )
    .unwrap_err();
    assert!(error.contains("private library implementation"), "{error}");
    check(scratch.path(), "(#alias read = (#unstable ./value/private.lim::read)) (#fn main () #u64 (#return (#call read ())))").unwrap();
    let error = check(scratch.path(), "(#alias read = (#unstable ./value/private.lim::read)) (#alias secret = ./value/private.lim::secret) (#fn main () #u64 (#return (#call read ())))").unwrap_err();
    assert!(error.contains("private"), "{error}");
}

#[test]
fn aliases_do_not_create_new_types() {
    let scratch = support::Scratch::new("file-alias-type-identity");
    write(scratch.path(), "value.lim", "(#struct Number () ((value #u64))) (#fn read ((value Number)) #u64 (#return (#get value value)))");
    check(scratch.path(), "(#alias First = ./value.lim::Number) (#alias Second = ./value.lim::Number) (#alias read = ./value.lim::read) (#fn main () #u64 (#let value First (#struct-literal Second ((value 42u64)))) (#return (#call read ((value value)))))").unwrap();
}

#[test]
fn generators_keep_definition_and_invocation_references() {
    let scratch = support::Scratch::new("file-alias-generator");
    write(scratch.path(), "generator/lib.lim", "(#export make) (#fn helper () #u64 (#return 2u64)) (#gn make (name callback) `((#fn ,name () #u64 (#return (#u64::add-wrap (#call helper ()) (#call ,callback ()))))))");
    let source = "(#alias make = ./generator/lib.lim::make) (#fn input () #u64 (#return 40u64)) (#generate make output @input) (#fn main () #u64 (#return (#call output ())))";
    for _ in 0..2 {
        let program = lim::parse_program_from_path_with_config_and_cache(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join(".lim/cache"),
        )
        .unwrap();
        lim::check_types(&program).unwrap();
    }
}

#[test]
fn malformed_duplicate_and_cyclic_aliases_are_rejected() {
    let scratch = support::Scratch::new("file-alias-errors");
    write(
        scratch.path(),
        "value.lim",
        "(#fn read () #u64 (#return 42u64))",
    );
    for source in [
        "(#alias read ./value.lim::read)",
        "(#alias read = ./value.lim::read) (#alias read = ./value.lim::read)",
        "(#alias main = ./value.lim::read) (#fn main () #u64 (#return 0u64))",
        "(#alias read = (#unstable))",
        "(#fn ./value.lim::forged () #u64 (#return 42u64))",
        "(#alias missing = ./value.lim::missing)",
        "(#alias read = ./value.lim::read) (#fn main ((read #u64)) #u64 (#return read))",
    ] {
        assert!(check(scratch.path(), source).is_err(), "{source}");
    }
    write(scratch.path(), "a.lim", "(#alias read = ./b.lim::read)");
    write(scratch.path(), "b.lim", "(#alias read = ./a.lim::read)");
    let error = check(scratch.path(), "(#alias read = ./a.lim::read)").unwrap_err();
    assert!(error.contains("cyclic"), "{error}");
}

#[test]
fn generated_aliases_resolve_definition_paths_and_cold_warm_outputs() {
    let scratch = support::Scratch::new("file-generated-alias");
    write(
        scratch.path(),
        "generator/lib.lim",
        "(#export make) (#gn make (name) `((#alias ,name = ./helper.lim::read)))",
    );
    write(
        scratch.path(),
        "generator/helper.lim",
        "(#fn read () #u64 (#return 42u64))",
    );
    let source = "(#alias make = ./generator/lib.lim::make) (#generate make read) (#fn main () #u64 (#return (#call read ())))";
    for _ in 0..2 {
        let program = lim::parse_program_from_path_with_config_and_cache(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join(".lim/cache"),
        )
        .unwrap();
        lim::check_types(&program).unwrap();
    }
}

#[test]
fn exported_array_api_keeps_explicit_claims_across_aliases_and_cache_hits() {
    let scratch = support::Scratch::new("file-array-contracts");
    write(
        scratch.path(),
        "values/lib.lim",
        "(#export Values Values::in-bounds Values::prove-in-bounds Values::get) (#generate #array ((element #u64) (length 4) (name Values)))",
    );
    let source = "(#alias Quad = ./values/lib.lim::Values)
      (#alias valid = ./values/lib.lim::Values::in-bounds)
      (#alias prove = ./values/lib.lim::Values::prove-in-bounds)
      (#alias get = ./values/lib.lim::Values::get)
      (#fn main () #u64
        (#let values Quad (#array-of 1 42 3 4)) (#let index #usize 1usize)
        (#return (#if-valid (#call valid ((index index)))
          (#block (#call prove ((index index)))
            (#call get ((values (#borrow values)) (index index)))) 0u64)))";
    for _ in 0..2 {
        check(scratch.path(), source).unwrap();
        let error = check(
            scratch.path(),
            &source.replace("(#call prove ((index index)))", ""),
        )
        .unwrap_err();
        assert!(error.contains("missing evidence"), "{error}");
    }
}

#[test]
fn builtin_generated_types_and_variants_have_file_identity() {
    let scratch = support::Scratch::new("file-builtin-alias");
    write(
        scratch.path(),
        "value/lib.lim",
        "(#export Value) (#generate #optional ((type #u64) (name Value)))",
    );
    check(scratch.path(), "(#alias Maybe = ./value/lib.lim::Value) (#fn main () #u64 (#let value Maybe (#enum-literal Maybe.Some 42u64)) (#return (#match value (#case (Maybe.Some answer) answer) (#case Maybe.None 0u64))))").unwrap();
}

#[test]
fn exported_names_still_require_exports_and_unstable_does_not_open_fields() {
    let scratch = support::Scratch::new("file-unstable-representation");
    write(scratch.path(), "value/lib.lim", "(#export read) (#struct Secret () ((value #u64))) (#fn read () #u64 (#return 42u64)) (#fn private () #u64 (#return 0u64))");
    let error = check(scratch.path(), "(#alias hidden = ./value/lib.lim::private)").unwrap_err();
    assert!(error.contains("not exported"), "{error}");
    let error = check(scratch.path(), "(#alias Secret = (#unstable ./value/lib.lim::Secret)) (#fn main () #u64 (#let value Secret (#struct-literal Secret ((value 42u64)))) (#return (#get value value)))").unwrap_err();
    assert!(error.contains("private representation"), "{error}");
    write(
        scratch.path(),
        "value/lib.lim",
        "(#export) (#enum State () ((State.Ready #u64) (State.Empty)))",
    );
    check(scratch.path(), "(#alias State = (#unstable ./value/lib.lim::State)) (#fn main () #u64 (#let value State (#enum-literal State.Ready 42u64)) (#return (#match value (#case (State.Ready answer) answer) (#case State.Empty 0u64))))").unwrap();
}

#[test]
fn transitive_aliases_do_not_acquire_unrelated_private_permissions() {
    let scratch = support::Scratch::new("file-alias-transitive-privacy");
    write(
        scratch.path(),
        "third/lib.lim",
        "(#export read) (#fn read () #u64 (#return 42u64)) (#fn secret () #u64 (#return 0u64))",
    );
    write(
        scratch.path(),
        "middle/lib.lim",
        "(#export read) (#alias read = ../third/lib.lim::read)",
    );
    check(
        scratch.path(),
        "(#alias read = ./middle/lib.lim::read) (#fn main () #u64 (#return (#call read ())))",
    )
    .unwrap();
    write(
        scratch.path(),
        "middle/lib.lim",
        "(#export read) (#alias read = ../third/lib.lim::secret)",
    );
    let error = check(scratch.path(), "(#alias read = ./middle/lib.lim::read)").unwrap_err();
    assert!(error.contains("not exported"), "{error}");
}

#[test]
fn direct_references_are_part_of_cfg_collection_and_internal_formatting() {
    let scratch = support::Scratch::new("file-alias-tools");
    write(
        scratch.path(),
        "lib.lim",
        "(#export read) (#alias read = ./inner.lim::read)",
    );
    write(scratch.path(), "inner.lim", "(#cfg-if (#cfg-is #my-mode enabled) (#type Enabled #u64))\n(#fn read () #u64 (#return 42u64))");
    let source = "(#alias read = ./inner.lim::read)\n(#fn main () #u64 (#return (#call read ())))";
    write(scratch.path(), "main.lim", source);
    let keys = lim::collect_cfg_keys_from_path(&scratch.path().join("main.lim")).unwrap();
    assert!(keys.iter().any(|key| key == "#my-mode"));
    let paths = lim::format_project_from_path(&scratch.path().join("main.lim")).unwrap();
    assert_eq!(paths.len(), 2);
}

#[test]
fn same_spelled_types_in_different_files_remain_distinct() {
    let scratch = support::Scratch::new("file-distinct-types");
    for path in ["first.lim", "second.lim"] {
        write(scratch.path(), path, "(#struct Number () ((value #u64)))");
    }
    let error = check(scratch.path(), "(#alias First = ./first.lim::Number) (#alias Second = ./second.lim::Number) (#fn main () #u64 (#let value First (#struct-literal Second ((value 42u64)))) (#return 0u64))").unwrap_err();
    assert!(
        error.contains("expected") || error.contains("mismatch"),
        "{error}"
    );
}

#[test]
fn aliasing_unsafe_functions_does_not_remove_call_requirements() {
    let scratch = support::Scratch::new("file-unsafe-functions");
    write(
        scratch.path(),
        "value.lim",
        "(#unsafe-fn read () #u64 (#return 42u64))",
    );
    check(scratch.path(), "(#alias read = ./value.lim::read) (#fn main () #u64 (#return (#unsafe (#unsafe-call read ()))))").unwrap();
    assert!(check(
        scratch.path(),
        "(#alias read = ./value.lim::read) (#fn main () #u64 (#return (#call read ())))"
    )
    .is_err());
}

#[test]
fn aliasing_foreign_functions_preserves_the_linker_symbol() {
    let scratch = support::Scratch::new("file-foreign-symbols");
    write(
        scratch.path(),
        "foreign.lim",
        "(#extern-fn #abi-c c_value () #u64)",
    );
    let program = lim::parse_program_from_path("(#alias read = ./foreign.lim::c_value) (#fn main () #u64 (#return (#unsafe (#unsafe-call read ()))))", &scratch.path().join("main.lim")).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    assert!(assembly.contains(".extern c_value\n"), "{assembly}");
}

#[test]
fn quoted_paths_and_symlinks_preserve_canonical_identity() {
    let scratch = support::Scratch::new("file-quoted-path");
    write(
        scratch.path(),
        "space dir/value.lim",
        "(#struct Number () ((value #u64)))",
    );
    std::os::unix::fs::symlink(
        scratch.path().join("space dir/value.lim"),
        scratch.path().join("alias.lim"),
    )
    .unwrap();
    check(scratch.path(), "(#alias First = \"./space dir/value.lim::Number\") (#alias Second = ./alias.lim::Number) (#fn main () #u64 (#let value First (#struct-literal Second ((value 42u64)))) (#return (#get value value)))").unwrap();
}

#[test]
fn async_generator_outputs_are_distinct_between_source_files() {
    let scratch = support::Scratch::new("file-async-identity");
    let source = "(#generate #async-fn ((protocol WorkAwait) (waker #u64) (cancel (cancel-work ())) (function (#fn work ((value #u64)) #u64 (#return value)))))
      (#fn run () #u64 (#let waker #u64 0u64) (#let result Work::Poll (#call Work::poll ((task (#call work ((value 21u64)))) (waker (#borrow waker))))) (#return (#match result (#case (Work::Poll.Ready answer) answer) (#case (Work::Poll.Pending task) (#block (#forget task) (#unreachable))))))";
    write(scratch.path(), "first.lim", source);
    write(scratch.path(), "second.lim", source);
    check(scratch.path(), "(#alias first = ./first.lim::run) (#alias second = ./second.lim::run) (#fn main () #u64 (#return (#u64::add-wrap (#call first ()) (#call second ()))))").unwrap();
}

#[test]
fn identical_generator_inputs_do_not_merge_distinct_file_declarations() {
    let scratch = support::Scratch::new("file-generated-local-identity");
    write(
        scratch.path(),
        "generator.lim",
        "(#gn make () `((#type Number #u64)))",
    );
    for path in ["first.lim", "second.lim"] {
        write(scratch.path(), path, "(#alias make = ./generator.lim::make) (#generate make) (#fn read () Number (#return 21u64))");
    }
    let source = "(#alias first = ./first.lim::read) (#alias second = ./second.lim::read) (#fn main () #u64 (#return (#u64::add-wrap (#call first ()) (#call second ()))))";
    for _ in 0..2 {
        let program = lim::parse_program_from_path_with_config_and_cache(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join(".lim/cache"),
        )
        .unwrap();
        lim::check_types(&program).unwrap();
    }
}

#[test]
fn generated_aliases_cannot_publish_unrelated_private_targets_even_when_unused() {
    let scratch = support::Scratch::new("file-alias-forged-authority");
    write(
        scratch.path(),
        "library/lib.lim",
        "(#export public) (#fn public () #u64 (#return 0u64)) (#fn secret () #u64 (#return 42u64))",
    );
    let private = format!(
        "{}::secret",
        scratch.path().join("library/lib.lim").display()
    );
    let source = format!("(#alias public = ./library/lib.lim::public) (#gn forge () `((#alias stolen = ,(#gn-symbol {private:?})))) (#generate forge) (#fn main () #u64 (#return 0u64))");
    let error = check(scratch.path(), &source).unwrap_err();
    assert!(error.contains("private"), "{error}");
}

#[test]
fn file_looking_strings_remain_literal_data() {
    let scratch = support::Scratch::new("file-looking-literal");
    write(
        scratch.path(),
        "value.lim",
        "(#fn read () #u64 (#return 42u64))",
    );
    let text = "./does-not-exist.lim::not-a-reference";
    for imports in ["", "(#alias read = ./value.lim::read)"] {
        check(scratch.path(), &format!("{imports} (#fn main () #u64 (#let text (#array #char {}) {text:?}) (#return 42u64))", text.chars().count())).unwrap();
    }
    check(scratch.path(), "(#gn ignore (value) `()) (#generate ignore ./does-not-exist.lim::literal) (#fn main () #u64 (#return 42u64))").unwrap();
}

#[test]
fn project_root_paths_are_shared_across_nested_sources() {
    let scratch = support::Scratch::new("project-root-references");
    write(
        scratch.path(),
        "lim.project",
        "schema-version = 1\nname = Root\n",
    );
    write(
        scratch.path(),
        "shared/value.lim",
        "(#fn read () #u64 (#return 42u64))",
    );
    write(
        scratch.path(),
        "src/helper.lim",
        "(#alias read = project::shared/value.lim::read) (#fn run () #u64 (#return (#call read ())))",
    );
    let program = lim::parse_program_from_path(
        "(#alias run = project::src/helper.lim::run) (#fn main () #u64 (#return (#call run ())))",
        &scratch.path().join("src/bin/main.lim"),
    )
    .unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn standalone_root_paths_use_the_principal_sources_directory() {
    let scratch = support::Scratch::new("standalone-root-references");
    write(
        scratch.path(),
        "value.lim",
        "(#fn read () #u64 (#return 42u64))",
    );
    write(
        scratch.path(),
        "nested/helper.lim",
        "(#alias read = project::value.lim::read) (#fn run () #u64 (#return (#call read ())))",
    );
    check(
        scratch.path(),
        "(#alias run = project::nested/helper.lim::run) (#fn main () #u64 (#return (#call run ())))",
    )
    .unwrap();
}

#[test]
fn project_root_references_reject_parent_escape() {
    let scratch = support::Scratch::new("project-root-parent-escape");
    let error = check(
        scratch.path(),
        "(#alias read = project::../value.lim::read)",
    )
    .unwrap_err();
    assert!(error.contains("cannot contain"), "{error}");
}

#[test]
fn removed_import_forms_have_no_compatibility_path() {
    let scratch = support::Scratch::new("removed-imports");
    write(
        scratch.path(),
        "value.lim",
        "(#fn read () #u64 (#return 42u64))",
    );
    for source in [
        "(#import \"value.lim\")",
        "(#import-external \"value.lim\" old)",
    ] {
        let error = check(scratch.path(), source).unwrap_err();
        assert!(error.contains("unknown"), "{error}");
    }
}

#[test]
fn definition_references_survive_nested_generator_signature_templates() {
    let scratch = support::Scratch::new("file-generator-signature-helper");
    write(scratch.path(), "generator.lim", "(#gn-fn parameter () `(value #u64)) (#gn declare (name) `((#fn ,name (,(#gn-call @parameter)) #u64 (#return value))))");
    check(scratch.path(), "(#alias declare = ./generator.lim::declare) (#generate declare answer) (#fn main () #u64 (#return (#call answer ((value 42u64)))))").unwrap();
}

#[test]
fn generation_requirements_use_the_actual_files_declaration() {
    let scratch = support::Scratch::new("file-generation-proof");
    for file in ["first.lim", "second.lim"] {
        write(
            scratch.path(),
            file,
            "(#gn make (name) `((#struct ,name () ()))) (#generate make Thing)",
        );
    }
    let aliases = "(#alias First = ./first.lim::Thing) (#alias Second = ./second.lim::Thing) (#alias make-first = ./first.lim::make)";
    check(
        scratch.path(),
        &format!(
            "{aliases} (#require-generated First make-first) (#fn main () #u64 (#return 0u64))"
        ),
    )
    .unwrap();
    for name in ["Second", "Thing"] {
        let error = check(scratch.path(), &format!("{aliases} (#require-generated {name} make-first) (#fn main () #u64 (#return 0u64))")).unwrap_err();
        assert!(error.contains("was not generated"), "{error}");
    }
}
