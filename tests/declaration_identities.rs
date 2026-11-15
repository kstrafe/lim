mod support;

use std::process::Command;
use std::time::Duration;

fn checked_dump(source: &str) -> String {
    let parsed = lim::parse_program(source).expect("valid Lim source");
    lim::CheckedProgram::validate(&parsed)
        .expect("source typechecks")
        .dump_typed_ir()
}

#[test]
fn declaration_ids_are_stable_across_independent_parses() {
    let source = "#struct Zebra () ((shared #u64))
#struct Alpha () ((shared #u32))
#enum Choice () ((Choice.Item #u64) Choice.Empty)
#static tOTAL #u64 40u64
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let value Alpha (#struct-literal Alpha ((shared 2u32))))
          (#let other Zebra (#struct-literal Zebra ((shared 3u64))))
          (#return (#u64::add-wrap
            (#u64::add-wrap (#as (#get value shared) #u64) (#get other shared))
            (#unsafe tOTAL)))\n  );\n}\n";
    let first = checked_dump(source);
    let second = checked_dump(source);
    assert_eq!(first, second);

    // IDs include sorted aggregates; only declarations used by this body are dumped.
    assert!(
        first.contains("Declaration(Aggregate(AggregateId(0)))"),
        "{first}"
    );
    assert!(
        first.contains("Declaration(Aggregate(AggregateId(2)))"),
        "{first}"
    );
    assert!(
        first.contains("Declaration(Field(FieldId { owner: AggregateId(0), index: 0 }))"),
        "{first}"
    );
    assert!(
        first.contains("Declaration(Field(FieldId { owner: AggregateId(2), index: 0 }))"),
        "{first}"
    );
}

#[test]
fn aliases_and_references_resolve_field_identity_to_its_owner() {
    let source = "#struct Left () ((value #u64))
#struct Right () ((value #u64))
#type LeftAlias Left
#fn read {
  #params = ((item (#ref LeftAlias)));
  #returns = #u64;
  #body = ( (#return (#get item value))
  );
}
#fn read-right {
  #params = ((item (#ref Right)));
  #returns = #u64;
  #body = ( (#return (#get item value))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let item LeftAlias (#struct-literal Left ((value 42u64))))
          (#let right Right (#struct-literal Right ((value 1u64))))
          (#return (#u64::add-wrap
            (#call read ((item (#borrow item))))
            (#call read-right ((item (#borrow right))))))\n  );\n}\n";
    let dump = checked_dump(source);
    assert!(
        dump.contains("Declaration(Field(FieldId { owner: AggregateId(0), index: 0 }))"),
        "{dump}"
    );
    assert!(
        dump.contains("Declaration(Field(FieldId { owner: AggregateId(1), index: 0 }))"),
        "the same-spelled Right field must have its own identity: {dump}"
    );
}

#[test]
fn enum_constructor_match_and_payload_projection_share_variant_identity() {
    let source = "#enum Result () ((Result.Value #u64) Result.Empty)
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut result Result (Result.Value 40u64))
          (#set-payload result Result.Value 0 41u64)
          (#let reference (#ref Result) (#borrow result))
          (#let payload #u64 (#get-payload reference Result.Value 0))
          (#return (#match result
            (#case (Result.Value matched) (#u64::add-wrap payload 1u64))
            (#case Result.Empty 0u64)))\n  );\n}\n";
    let dump = checked_dump(source);
    let variant = "Declaration(Variant(VariantId { owner: AggregateId(0), index: 0 }))";
    assert!(dump.contains(variant), "{dump}");
    assert!(
        dump.matches(variant).count() >= 3,
        "constructor, match, and payload access should carry the same variant ID: {dump}"
    );
}

#[test]
fn global_and_local_references_have_distinct_declaration_kinds() {
    let source = "#static tOTAL #u64 40u64
#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#fn parameter {
  #params = ((argument #u64));
  #returns = #u64;
  #body = ( (#return argument)
  );
}
#fn local {
  #params = ();
  #returns = #u64;
  #body = (
          (#let local-total #u64 42u64)
          (#return local-total)
  );
}
#fn pattern {
  #params = ((value Maybe));
  #returns = #u64;
  #body = (
          (#return (#match value
            (#case (Maybe.Some matched) matched)
            (#case Maybe.None 0u64)))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#return (#unsafe tOTAL))\n  );\n}\n";
    let dump = checked_dump(source);
    let parameter_dump = dump
        .split_once("function parameter\n")
        .unwrap()
        .1
        .split("\nfunction ")
        .next()
        .unwrap();
    assert!(
        parameter_dump.contains("Symbol { name: \"argument\", binding: Some(BindingId("),
        "parameter should resolve as a local binding: {parameter_dump}"
    );
    assert!(
        !parameter_dump.contains("Declaration(Global("),
        "parameter must not resolve to a global: {parameter_dump}"
    );
    for function in ["local", "pattern"] {
        let body = dump
            .split_once(&format!("function {function}\n"))
            .unwrap()
            .1;
        let body = body.split("\nfunction ").next().unwrap();
        assert!(body.contains("binding: Some(BindingId("), "{body}");
        assert!(!body.contains("Declaration(Global("), "{body}");
    }
    let main_dump = dump.split_once("function main\n").unwrap().1;
    assert!(
        main_dump.contains("Declaration(Global(GlobalId(0)))"),
        "main's unshadowed reference must resolve to the global: {main_dump}"
    );
}

#[test]
fn local_bindings_may_not_shadow_visible_names() {
    for source in [
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value #u64 1u64) (#let value #u64 2u64) (#return value)\n  );\n}\n",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#let value #u64 1u64) (#return (#block (#let value #u64 2u64) value))\n  );\n}\n",
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)\n#fn main {\n  #params = ((value Maybe));\n  #returns = #u64;\n  #body = ( (#return (#match value (#case (Maybe.Some value) value) (#case Maybe.None 0u64)))\n  );\n}\n",
        "#static value #u64 1u64\n#fn read {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}\n",
        "#fn main {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#let (#tuple value) (#tuple #u64) (#tuple 2u64)) (#return value)\n  );\n}\n",
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)\n#fn main {\n  #params = ((value #u64) (maybe Maybe));\n  #returns = #u64;\n  #body = ( (#return (#if-let (Maybe.Some value) maybe value value))\n  );\n}\n",
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)\n#fn main {\n  #params = ((value #u64) (maybe Maybe));\n  #returns = #u64;\n  #body = ( (#let-else (Maybe.Some value) Maybe maybe (#return 0u64)) (#return value)\n  );\n}\n",
        "#fn main {\n  #params = ((counter #u64));\n  #returns = #u64;\n  #body = ( (#for (#let counter #u64 0u64) true () (#break)) (#return counter)\n  );\n}\n",
        "#fn main {\n  #params = ((offset #u64));\n  #returns = #u64;\n  #body = ( (#for-range (offset #u64) 0u64 2u64 ()) (#return offset)\n  );\n}\n",
    ] {
        let error = lim::parse_program(source).unwrap_err();
        assert!(
            error.contains("shadowing is not allowed"),
            "source: {source}\nerror: {error}"
        );
    }
}

#[test]
fn sibling_scopes_may_reuse_local_names() {
    let source = "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
        (#let first #u64 (#block (#let value #u64 1u64) value))
        (#let second #u64 (#block (#let value #u64 2u64) value))
        (#return (#u64::add-wrap first second))\n  );\n}\n";
    let program = lim::parse_program(source).unwrap();
    assert!(lim::check_types(&program).is_ok());
}

#[test]
fn sibling_enum_patterns_with_the_same_name_have_distinct_typed_storage() {
    let scratch = support::Scratch::new("pattern-binding-storage");
    let source = scratch.path().join("main.lim");
    let executable = scratch.path().join("program");
    std::fs::write(
        &source,
        "#enum Small () ((Small.Number #u64) Small.Zero)
#enum Wide () ((Wide.Words (#tuple #u64 #u64 #u64 #u64)) Wide.Absent)
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let small Small (Small.Number 20u64))
          (#let wide Wide (Wide.Words (#tuple (#tuple #u64 #u64 #u64 #u64) 22u64 3u64 4u64 5u64)))
          (#let first #u64 (#match small (#case (Small.Number value) value) (#case Small.Zero 0u64)))
          (#let second #u64 (#match wide (#case (Wide.Words value) (#get value 0)) (#case Wide.Absent 0u64)))
          (#return (#u64::add-wrap first second))\n  );\n}\n",
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source)
            .arg("-o")
            .arg(&executable),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) = support::run(
        &mut Command::new(&executable),
        Duration::from_secs(2),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn scoped_statement_destinations_do_not_alias_same_spelled_initializer_patterns() {
    let scratch = support::Scratch::new("scoped-statement-destinations");
    let executable = scratch.path().join("program");
    for (index, source) in [
        "#enum Maybe () ((Maybe.Some #u64) Maybe.None)
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
              (#let answer #u64 (#match (Maybe.Some 41u64)
                (#case (Maybe.Some answer) answer) (#case Maybe.None 0u64)))
              (#return (#u64::add-wrap answer 1u64))\n  );\n}\n",
        "#fn main {
  #params = ();
  #returns = #u64;
  #body = (
            (#let first #u64 (#block (#let-mut value #u64 20u64) (#set value 21u64) value))
            (#let second #u64 (#block (#let-mut value (#tuple #u64 #u64)
              (#tuple (#tuple #u64 #u64) 20u64 9u64)) (#set-field value 0 21u64) (#get value 0)))
            (#return (#u64::add-wrap first second))\n  );\n}\n",
        "#struct Pair () ((first #u64) (second #u64))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
              (#let first #u64 (#block (#let-mut value Pair
                (#struct-literal Pair ((first 20u64) (second 9u64))))
                (#set-field value first 21u64) (#get value first)))
              (#let second #u64 (#block (#let-mut value #u128 20u128) (#set value 21u128) (#as value #u64)))
              (#return (#u64::add-wrap first second))\n  );\n}\n",
    ].iter().enumerate() {
        let path = scratch.path().join(format!("main-{index}.lim"));
        std::fs::write(&path, source).unwrap();
        let (status, _, stderr) = support::run(
            Command::new(env!("CARGO_BIN_EXE_lim")).arg(&path).arg("-o").arg(&executable),
            Duration::from_secs(20), 1024 * 1024,
        ).unwrap();
        assert!(status.success(), "case {index}: {}", String::from_utf8_lossy(&stderr));
        let (status, _, stderr) = support::run(
            &mut Command::new(&executable), Duration::from_secs(2), 1024 * 1024,
        ).unwrap();
        assert_eq!(status.code(), Some(42), "case {index}: {}", String::from_utf8_lossy(&stderr));
    }
}

#[test]
fn actual_static_access_still_requires_unsafe_and_points_at_its_name() {
    let scratch = support::Scratch::new("static-unsafe");
    let source = "#static tOTAL #u64 40u64\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return tOTAL)\n  );\n}\n";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("static-unsafe.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("access to static 'tOTAL' requires"));
    let span = error.span.expect("static diagnostic source span");
    assert_eq!(&source[span.start..span.end], "tOTAL");
}

#[test]
fn imported_static_access_retains_its_imported_source_location() {
    let scratch = support::Scratch::new("imported-static-unsafe");
    let module = "#static tOTAL #u64 40u64\n#fn read {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return tOTAL)\n  );\n}\n";
    std::fs::write(scratch.path().join("module.lim"), module).unwrap();
    let root = "#alias read = ./module.lim::read\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call read ()))\n  );\n}\n";
    let error = lim::compile_source_to_assembly(
        root,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    let canonical = format!("{}::tOTAL", scratch.path().join("module.lim").display());
    assert!(
        error
            .message
            .contains(&format!("access to static '{canonical}' requires")),
        "{error:?}"
    );
    let span = error.span.expect("imported static diagnostic source span");
    assert_eq!(span.source_id, 1);
    assert_eq!(&module[span.start..span.end], "tOTAL");
    assert_eq!(
        error.source_name.as_deref(),
        Some(scratch.path().join("module.lim").to_str().unwrap())
    );
}

#[test]
fn generated_static_access_still_requires_unsafe() {
    let scratch = support::Scratch::new("generated-static-unsafe");
    let source =
        "#gn make (name) `((#static tOTAL #u64 1u64) (#fn ,name () #u64 (#return tOTAL)))\n\
      #generate make read\n\
      #fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return (#call read ()))\n  );\n}\n";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("generated-static.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("access to static 'tOTAL' requires"));
    let generated_span = error.span.expect("generated diagnostic source span");
    let generated_text = error
        .source_text
        .as_deref()
        .expect("generated diagnostic source text");
    assert!(generated_span.source_id > 0);
    assert!(generated_text.contains("#fn read") && generated_text.contains("tOTAL"));
    let invocation = error
        .expansion_provenance
        .first()
        .expect("generated diagnostic invocation provenance");
    assert_eq!(
        &invocation.source_text.as_deref().unwrap()[invocation.span.start..invocation.span.end],
        "#generate make read"
    );
}

#[test]
fn imported_declaration_nodes_retain_source_spans_and_deterministic_ids() {
    let scratch = support::Scratch::new("declaration-import-spans");
    let module = "#struct Record () ((value #u64))
#static bASE #u64 1u64
#fn imported {
  #params = ();
  #returns = #u64;
  #body = (
  (#return (#u64::add-wrap (#get (#struct-literal Record ((value 40u64))) value) (#unsafe bASE)))
  );\n}\n";
    std::fs::write(scratch.path().join("module.lim"), module).unwrap();
    let root = "#alias imported = ./module.lim::imported\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call imported ()))\n  );\n}\n";
    let path = scratch.path().join("main.lim");
    let parse_dump = || {
        let program = lim::parse_program_from_path(root, &path).expect("parse imported source");
        lim::CheckedProgram::validate(&program)
            .expect("imported source typechecks")
            .dump_typed_ir()
    };
    let first = parse_dump();
    assert_eq!(first, parse_dump());

    let field_start = module.rfind(" value)").unwrap() + 1;
    let global_start = module.rfind("bASE").unwrap();
    assert!(
        first.lines().any(|line| {
            line.contains("Declaration(Field(FieldId { owner: AggregateId(0), index: 0 }))")
                && line.contains(&format!("start: {field_start},"))
        }),
        "imported field identity should retain its source span at {field_start}: {first}"
    );
    assert!(
        first.lines().any(|line| {
            line.contains("Declaration(Global(GlobalId(0)))")
                && line.contains(&format!("start: {global_start},"))
        }),
        "imported global identity should retain its source span at {global_start}: {first}"
    );
}

#[test]
fn resolved_field_mutation_and_reference_projection_execute_correctly() {
    let scratch = support::Scratch::new("declaration-identities");
    let source = scratch.path().join("main.lim");
    let executable = scratch.path().join("program");
    std::fs::write(
        &source,
        "#struct First () ((value #u64))
#struct Second () ((value #u64))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
             (#let-mut first First (#struct-literal First ((value 1u64))))
             (#let-mut second Second (#struct-literal Second ((value 2u64))))
             (#set-field second value 7u64)
             (#let-mut first-ref (#ref-mut First) (#borrow-mut first))
             (#let-mut value-ref (#ref-mut #u64) (#borrow-mut (#get first-ref value)))
             (#deref-set value-ref 42u64)
             (#drop value-ref)
             (#drop first-ref)
             (#return (#u64::add-wrap (#get first value) (#get second value)))\n  );\n}\n",
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source)
            .arg("-o")
            .arg(&executable),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(
        status.success(),
        "compiler failed: {}",
        String::from_utf8_lossy(&stderr)
    );
    let (status, _, stderr) = support::run(
        &mut Command::new(&executable),
        Duration::from_secs(2),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(49),
        "runtime failed: {}",
        String::from_utf8_lossy(&stderr)
    );
}
