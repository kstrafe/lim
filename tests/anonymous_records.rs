mod support;

use lim::{check_types, parse_program, Item, Type};
use std::{fs, process::Command, time::Duration};

const MAKE: &str = r#"
#fn parse {
  #params = ();
  #returns = { value = #u64; consumed = #usize; };
  #effects = ();
  #body = ((#return (#record-literal
    { value = #u64; consumed = #usize; }
    { value = 42u64; consumed = 2usize; })));
}
"#;
const BIND: &str =
    "(#let { value = (#bind parsed #u64); consumed = (#ignore #usize); } = (parse {}))";

fn main_with(body: &str) -> String {
    format!("{MAKE}\n#fn main {{ #params = (); #returns = #u64; #effects = (); #body = ({body} (#return parsed)); }}")
}
fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}
fn rejects(source: &str, needle: &str) {
    let error = check(source).expect_err("invalid anonymous record was accepted");
    assert!(
        error.contains(needle),
        "expected {needle:?}: {error}\n{source}"
    );
}
fn return_type(program: &lim::Program, local: &str) -> Type {
    program
        .items
        .iter()
        .find_map(|item| match item {
            Item::Function(f) if f.name == local || f.name.ends_with(&format!("::{local}")) => {
                Some(f.return_type.clone())
            }
            _ => None,
        })
        .unwrap()
}

#[test]
fn explicit_construction_exhaustive_binding_and_field_renaming() {
    check(&main_with(BIND)).unwrap();
    check(&main_with(
        &BIND.replace("(#ignore #usize)", "(#bind count #usize)"),
    ))
    .unwrap();
    let program = parse_program(&main_with(BIND)).unwrap();
    let ty = return_type(&program, "parse");
    let Type::Named(name) = &ty else {
        panic!("expected an ordinary struct: {ty:?}");
    };
    let fields = program
        .items
        .iter()
        .find_map(|item| match item {
            Item::Struct {
                name: owner,
                fields,
                ..
            } if owner == name => Some(fields),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(),
        ["consumed", "value"]
    );
    assert_eq!(fields[0].ty, Type::Usize);
    assert_eq!(fields[1].ty, Type::U64);
}

#[test]
fn type_identity_uses_resolved_field_types_and_canonical_field_order() {
    let source = format!(
        r#"
#type Number #u64
{MAKE}
#fn alternate {{ #params = (); #returns = {{ consumed = #usize; value = Number; }};
  #effects = (); #body = ((#return (#record-literal
    {{ consumed = #usize; value = #u64; }} {{ consumed = 2usize; value = 42u64; }}))); }}
#fn main {{ #params = (); #returns = #u64; #effects = (); #body = (
  (#let {{ consumed = (#ignore #usize); value = (#bind parsed Number); }} = (alternate {{}}))
  (#return parsed)); }}
"#
    );
    let program = parse_program(&source).unwrap();
    check_types(&program).unwrap();
    assert_eq!(
        return_type(&program, "parse"),
        return_type(&program, "alternate")
    );
    assert_eq!(
        program
            .items
            .iter()
            .filter(|item| matches!(item, Item::Struct { .. }))
            .count(),
        1
    );
}

#[test]
fn every_pattern_field_requires_an_explicit_type_and_bind_or_ignore() {
    for pattern in [
        "{ value = parsed; consumed = (#ignore #usize); }",
        "{ value = (#bind parsed); consumed = (#ignore #usize); }",
        "{ value = (#bind parsed #u64); consumed = (#ignore); }",
        "{ value = (#bind parsed #u64); consumed = _; }",
        "{ value = (#bind parsed #u64); rest = (#ignore #usize); }",
    ] {
        let source = main_with(&format!("(#let {pattern} = (parse {{}}))"));
        assert!(check(&source).is_err(), "{source}");
    }
    rejects(
        &main_with(&BIND.replace("(#bind parsed #u64)", "(#bind _ #u64)")),
        "use #ignore",
    );
}

#[test]
fn missing_extra_duplicate_and_mistyped_fields_are_rejected() {
    rejects(
        &main_with(&BIND.replace("consumed = (#ignore #usize);", "")),
        "missing field 'consumed'",
    );
    rejects(
        &main_with(&BIND.replace(
            "consumed = (#ignore #usize);",
            "consumed = (#ignore #usize); extra = (#ignore #bool);",
        )),
        "unknown record pattern field 'extra'",
    );
    rejects(
        &main_with(&BIND.replace(
            "consumed = (#ignore #usize);",
            "consumed = (#ignore #usize); consumed = (#ignore #usize);",
        )),
        "duplicate record field 'consumed'",
    );
    rejects(
        &main_with(&BIND.replace("(#ignore #usize)", "(#bind parsed #usize)")),
        "duplicate record binding 'parsed'",
    );
    assert!(check(&main_with(
        &BIND.replace("#bind parsed #u64", "#bind parsed #bool")
    ))
    .is_err());
    for (old, new, error) in [
        ("value = 42u64;", "", "missing field 'value'"),
        (
            "value = 42u64;",
            "value = 42u64; other = true;",
            "unknown record literal field 'other'",
        ),
        (
            "value = 42u64;",
            "value = 42u64; value = 0u64;",
            "duplicate record field 'value'",
        ),
        (
            "value = #u64; consumed = #usize;",
            "value = #u64; value = #bool; consumed = #usize;",
            "duplicate record field 'value'",
        ),
    ] {
        rejects(&main_with(BIND).replace(old, new), error);
    }
}

#[test]
fn construction_requires_a_separate_explicit_shape() {
    let source = main_with(BIND);
    rejects(
        &source.replace(
            "{ value = #u64; consumed = #usize; }\n    { value =",
            "{ value =",
        ),
        "explicit field-type record",
    );
    assert!(check(&source.replace("#record-literal", "#tuple")).is_err());
    assert!(check(&source.replace("value = 42u64;", "value = false;")).is_err());
}

#[test]
fn record_return_calls_cannot_discard_or_bind_the_whole_result() {
    rejects(
        &main_with("(parse {}) (#let parsed #u64 42u64)"),
        "exhaustive typed record binding",
    );
    rejects(
        &format!(
            r#"
#type Result {{ value = #u64; consumed = #usize; }}
{MAKE}
#fn main {{ #params = (); #returns = #u64; #effects = (); #body = (
 (#let result Result (parse {{}})) (#return 42u64)); }}"#
        ),
        "exhaustive typed record binding",
    );
    rejects(
        &main_with("(#let parsed #u64 (#get (parse {}) value))"),
        "exhaustive typed record binding",
    );
}

#[test]
fn bindings_obey_existing_lexical_scopes() {
    check(&main_with(&format!(
        "(#block {BIND} (#forget parsed)) {BIND}"
    )))
    .unwrap();
    rejects(
        &main_with(&format!("(#block {BIND} (#forget parsed))")),
        "parsed",
    );
    check(&main_with(&format!(
        "(#let parsed #u64 (#block {BIND} parsed))"
    )))
    .unwrap();
}

fn linear_program(pattern: &str, cleanup: &str) -> String {
    format!(
        r#"
#struct Token (#linear) ((number #u64))
#type Owned Token
#fn make {{ #params = (); #returns = {{ token = Owned; count = #usize; }}; #effects = ();
 #body = ((#return (#record-literal {{ token = Token; count = #usize; }}
   {{ count = 1usize; token = (#struct-literal Token {{ number = 42u64; }}); }}))); }}
#fn main {{ #params = (); #returns = #u64; #effects = (); #body = (
 (#let {pattern} = (make {{}})) {cleanup} (#return 42u64)); }}
"#
    )
}

#[test]
fn linear_fields_must_be_bound_and_explicitly_consumed_even_through_aliases() {
    rejects(
        &linear_program("{ token = (#ignore Token); count = (#ignore #usize); }", ""),
        "cannot ignore linear record field 'token'",
    );
    rejects(
        &linear_program("{ token = (#ignore Owned); count = (#ignore #usize); }", ""),
        "cannot ignore linear record field 'token'",
    );
    let pattern = "{ token = (#bind owned Token); count = (#ignore #usize); }";
    check(&linear_program(pattern, "(#forget owned)")).unwrap();
    rejects(&linear_program(pattern, ""), "linear");
    rejects(
        &linear_program(pattern, "(#forget owned) (#forget owned)"),
        "owned",
    );
}

const REFS: &str = r#"
#fn views { #params = ((left (#ref #u64)) (right (#ref-mut #u64)));
 #returns = { shared = (#ref #u64); exclusive = (#ref-mut #u64); }; #effects = ();
 #body = ((#return (#record-literal
   { shared = (#ref #u64); exclusive = (#ref-mut #u64); }
   { shared = left; exclusive = right; }))); }
#fn main { #params = (); #returns = #u64; #effects = (); #body = (
 (#let-mut left #u64 20u64) (#let-mut right #u64 22u64)
 (#let { shared = (#bind shared (#ref #u64)); exclusive = (#bind exclusive (#ref-mut #u64)); }
   = (views { left = (#borrow left); right = (#borrow-mut right); }))
 (#deref-set exclusive 22u64)
 (#let result #u64 (#u64::add-wrap (#deref shared) (#deref exclusive)))
 (#drop shared) (#drop exclusive)
 (#set left 0u64) (#set right 0u64)
 (#return result)); }
"#;

#[test]
fn reference_fields_retain_their_separate_borrow_origins() {
    check(REFS).unwrap();
    rejects(
        &REFS.replace(
            "(#deref-set exclusive 22u64)",
            "(#set left 0u64) (#deref-set exclusive 22u64)",
        ),
        "borrow",
    );
    rejects(
        &REFS.replace(
            "(#deref-set exclusive 22u64)",
            "(#set right 0u64) (#deref-set exclusive 22u64)",
        ),
        "borrow",
    );
    rejects(
        &REFS.replace("right = (#borrow-mut right)", "right = (#borrow-mut left)"),
        "borrow",
    );
    rejects(
        &REFS.replace(
            "(#drop shared)",
            "(#let copied (#ref-mut #u64) exclusive) (#drop copied) (#drop shared)",
        ),
        "exclusive",
    );
}

#[test]
fn references_to_local_or_expired_scopes_cannot_escape_in_records() {
    rejects(
        r#"
#fn bad { #params = (); #returns = { view = (#ref #u64); }; #effects = ();
 #body = ((#let local #u64 42u64)
 (#return (#record-literal { view = (#ref #u64); } { view = (#borrow local); }))); }
"#,
        "local",
    );
    rejects(
        r#"
#fn bad { #params = (); #returns = { view = (#ref-mut #u64); }; #effects = ();
 #body = ((#return (#block (#let-mut local #u64 42u64)
   (#record-literal { view = (#ref-mut #u64); } { view = (#borrow-mut local); })))); }
"#,
        "local",
    );
}

#[test]
fn public_record_shapes_cross_file_aliases_without_exposing_private_types() {
    let scratch = support::Scratch::new("anonymous-record-aliases");
    fs::create_dir_all(scratch.path().join("parser")).unwrap();
    fs::write(
        scratch.path().join("parser/lib.lim"),
        format!("#export parse\n{MAKE}"),
    )
    .unwrap();
    let source = main_with(BIND).replace(MAKE, "#alias parse = ./parser/lib.lim::parse");
    let program = lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
    check_types(&program).unwrap();
    let private = r#"
#export make
#struct Hidden () ((number #u64))
#fn make { #params = (); #returns = { hidden = Hidden; }; #effects = ();
 #body = ((#return (#record-literal { hidden = Hidden; }
   { hidden = (#struct-literal Hidden { number = 42u64; }); }))); }
"#;
    fs::write(scratch.path().join("parser/lib.lim"), private).unwrap();
    let source = "#alias make = ./parser/lib.lim::make\n#fn main { #params = (); #returns = #u64; #effects = (); #body = ((#return 42u64)); }";
    let error = lim::parse_program_from_path(source, &scratch.path().join("main.lim"))
        .and_then(|program| check_types(&program))
        .unwrap_err();
    assert!(error.contains("private type"), "{error}");
    let source = "#alias Hidden = ./parser/lib.lim::Hidden\n#fn main { #params = (); #returns = #u64; #effects = (); #body = ((#return 42u64)); }";
    assert!(lim::parse_program_from_path(source, &scratch.path().join("main.lim")).is_err());
}

const ORDER: &str = r#"
#fn tick { #params = ((counter (#ref-mut #u64))); #returns = #u64; #effects = ();
 #body = ((#deref-set counter (#u64::add-wrap (#deref counter) 1u64)) (#return (#deref counter))); }
#fn pair { #params = ((counter (#ref-mut #u64)));
 #returns = { a = #u64; z = #u64; }; #effects = ();
 #body = ((#return (#record-literal { a = #u64; z = #u64; }
   { z = (tick { counter = counter; }); a = (tick { counter = counter; }); }))); }
#fn main { #params = (); #returns = #u64; #effects = (); #body = (
 (#let-mut counter #u64 0u64)
 (#let { z = (#bind first #u64); a = (#bind second #u64); } = (pair { counter = (#borrow-mut counter); }))
 (#assert (#u64::eq counter 2u64)) (#assert (#u64::eq first 1u64)) (#assert (#u64::eq second 2u64))
 (#return 42u64)); }
"#;

fn run_on(source: &str, target: lim::TargetDescription) {
    let program = parse_program(source).unwrap();
    check_types(&program).unwrap();
    let assembly = lim::generate_assembly_for_target(&program, target).unwrap();
    let scratch = support::Scratch::new("anonymous-record-native");
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    let mut command = if target == lim::TargetDescription::AARCH64_LINUX {
        let mut command = Command::new("qemu-aarch64");
        command.arg(&binary);
        command
    } else {
        Command::new(&binary)
    };
    let (status, out, err) = support::run(&mut command, Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{target:?}: {err:?}\n{source}");
    assert!(out.is_empty(), "{out:?}");
}

#[test]
fn calls_execute_once_and_construction_fields_execute_in_written_order() {
    for target in [
        lim::TargetDescription::X86_64_SYSTEM_V,
        lim::TargetDescription::AARCH64_LINUX,
    ] {
        run_on(ORDER, target);
        run_on(REFS, target);
    }
}

#[test]
fn both_native_targets_use_static_layouts_including_large_returns() {
    let source = r#"
#struct Layout () ((a #u8) (b #u64) (c #u16))
#fn large { #params = ();
 #returns = { g = #u64; f = #u64; e = #u64; d = #u64; c = #u64; b = #u64; a = #u64; }; #effects = ();
 #body = ((#return (#record-literal
   { a = #u64; b = #u64; c = #u64; d = #u64; e = #u64; f = #u64; g = #u64; }
   { g = 21u64; f = 0u64; e = 0u64; d = 0u64; c = 0u64; b = 0u64; a = 21u64; }))); }
#fn main { #params = (); #returns = #u64; #effects = (); #body = (
 (#assert (#usize::eq (#size-of { c = #u16; a = #u8; b = #u64; }) (#size-of Layout)))
 (#assert (#usize::eq (#align-of { c = #u16; a = #u8; b = #u64; }) (#align-of Layout)))
 (#let { a = (#bind left #u64); b = (#ignore #u64); c = (#ignore #u64); d = (#ignore #u64);
   e = (#ignore #u64); f = (#ignore #u64); g = (#bind right #u64); } = (large {}))
 (#return (#u64::add-wrap left right))); }
"#;
    for target in [
        lim::TargetDescription::X86_64_SYSTEM_V,
        lim::TargetDescription::AARCH64_LINUX,
    ] {
        run_on(source, target);
    }
}

#[test]
fn empty_records_are_unit_without_hiding_nonempty_record_fields() {
    let source = r#"
#fn empty { #params = (); #returns = {}; #effects = (); #body = ((#return (#record-literal {} {}))); }
#fn main { #params = (); #returns = #u64; #effects = (); #body = ((#let {} = (empty {})) (#return 42u64)); }
"#;
    check(source).unwrap();
    assert_eq!(
        return_type(&parse_program(source).unwrap(), "empty"),
        Type::Unit
    );
    check(&source.replace("(#let {} = (empty {}))", "(empty {})")).unwrap();
    let nonempty = source
        .replace("#returns = {};", "#returns = { value = #u64; };")
        .replace(
            "#record-literal {} {}",
            "#record-literal { value = #u64; } { value = 42u64; }",
        );
    rejects(&nonempty, "exhaustive typed record binding");
}

#[test]
fn record_field_evaluation_keeps_explicit_effect_requirements() {
    let source = r#"
#static counter #u64 42u64
#fn read { #params = (); #returns = { value = #u64; };
 #effects = ((#read-global counter));
 #body = ((#return (#record-literal { value = #u64; }
   { value = (#unsafe counter); }))); }
#fn main { #params = (); #returns = #u64; #effects = ((#effects-of read));
 #body = ((#let { value = (#bind answer #u64); } = (read {})) (#return answer)); }
"#;
    check(source).unwrap();
    assert!(
        check(&source.replace("#effects = ((#read-global counter));", "#effects = ();")).is_err()
    );
    assert!(check(&source.replace("#effects = ((#effects-of read));", "#effects = ();")).is_err());
}

#[test]
fn source_cannot_forge_internal_record_identities() {
    rejects(
        "#struct LimAnonymousRecordPendingFake () ((value #u64))",
        "compiler-owned",
    );
    assert!(parse_program("#struct lim.gensym.record.fake () ((value #u64))").is_err());
}

#[test]
fn borrow_diagnostics_keep_the_original_statement_span() {
    let source = REFS.replace(
        "(#deref-set exclusive 22u64)",
        "(#set left 0u64) (#deref-set exclusive 22u64)",
    );
    let scratch = support::Scratch::new("anonymous-record-span");
    let input = scratch.path().join("main.lim");
    fs::write(&input, &source).unwrap();
    let diagnostic = lim::compile_source_to_assembly(
        &source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(
        diagnostic.code,
        lim::DiagnosticCode::Borrow,
        "{diagnostic:?}"
    );
    let span = diagnostic.span.expect("borrow error lost its source span");
    assert!(
        source[span.start..span.end].contains("#set"),
        "{diagnostic:?}"
    );
}

#[test]
fn exported_opaque_linear_fields_keep_their_library_and_ownership_rules() {
    let scratch = support::Scratch::new("anonymous-record-opaque");
    fs::create_dir_all(scratch.path().join("owners")).unwrap();
    fs::write(
        scratch.path().join("owners/lib.lim"),
        r#"
#export Token make destroy
#struct Token (#linear) ((number #u64))
#opaque Token
#fn make { #params = (); #returns = { token = Token; count = #usize; }; #effects = ();
 #body = ((#return (#record-literal { token = Token; count = #usize; }
   { token = (#struct-literal Token { number = 42u64; }); count = 1usize; }))); }
#fn destroy { #params = ((value Token)); #returns = #u64; #effects = ();
 #body = ((#let output #u64 (#get value number)) (#forget value) (#return output)); }
"#,
    )
    .unwrap();
    let source = r#"
#alias Token = ./owners/lib.lim::Token
#alias make = ./owners/lib.lim::make
#alias destroy = ./owners/lib.lim::destroy
#fn main { #params = (); #returns = #u64; #effects = (); #body = (
 (#let { token = (#bind owned Token); count = (#ignore #usize); } = (make {}))
 (#let output #u64 (destroy { value = owned; })) (#return output)); }
"#;
    let check_file = |source: &str| {
        lim::parse_program_from_path(source, &scratch.path().join("main.lim"))
            .and_then(|program| check_types(&program))
    };
    check_file(source).unwrap();
    let ignored = source.replace("(#bind owned Token)", "(#ignore Token)");
    let error = check_file(&ignored).unwrap_err();
    assert!(
        error.contains("cannot ignore linear record field"),
        "{error}"
    );
    let access = source.replace(
        "(#let output #u64 (destroy",
        "(#let exposed #u64 (#get owned number)) (#let output #u64 (destroy",
    );
    let error = check_file(&access).unwrap_err();
    assert!(error.contains("private representation"), "{error}");
}

#[test]
fn positional_reference_and_tuple_parameters_lower_nested_record_types() {
    let source = r#"
#type Number #u64
#fn read { #params = (#ref { value = Number; consumed = #usize; });
 #returns = #u64; #effects = (); #body = ((#return (#get #arg value))); }
#fn second { #params = (#tuple (#ref { value = Number; }) #u64);
 #returns = #u64; #effects = (); #body = ((#return (#get #arg 1))); }
#fn main { #params = (); #returns = #u64; #effects = (); #body = ((#return 42u64)); }
"#;
    let program = parse_program(source).unwrap();
    check_types(&program).unwrap();
    for function in program.items.iter().filter_map(|item| match item {
        Item::Function(function)
            if function.name.ends_with("read") || function.name.ends_with("second") =>
        {
            Some(function)
        }
        _ => None,
    }) {
        assert_eq!(function.parameters.len(), 1);
        assert_eq!(function.parameters[0].name, "#arg");
        let record = match &function.parameters[0].ty {
            Type::Reference { target, .. } => target.as_ref(),
            Type::Tuple(fields) => match &fields[0] {
                Type::Reference { target, .. } => target.as_ref(),
                other => panic!("expected reference field: {other:?}"),
            },
            other => panic!("expected an explicit positional constructor: {other:?}"),
        };
        assert!(matches!(record, Type::Named(name) if name.starts_with("lim.gensym.record.")));
    }
}

fn record_diagnostic(source: &str) -> lim::Diagnostic {
    let scratch = support::Scratch::new("anonymous-record-diagnostic");
    let input = scratch.path().join("main.lim");
    fs::write(&input, source).unwrap();
    lim::compile_source_to_assembly(
        source,
        &input,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err()
}

#[test]
fn record_semantic_diagnostics_select_exact_authored_tokens_and_records() {
    let cases = [
        (
            main_with(&BIND.replace("#bind parsed #u64", "#bind parsed #bool")),
            "declares #bool",
            "#bool",
            lim::DiagnosticCode::Type,
        ),
        (
            main_with(&BIND.replace(
                "consumed = (#ignore #usize);",
                "consumed = (#ignore #usize); extra = (#ignore #bool);",
            )),
            "unknown record pattern field 'extra'",
            "extra",
            lim::DiagnosticCode::Type,
        ),
        (
            main_with(&BIND.replace("consumed = (#ignore #usize);", "")),
            "missing field 'consumed'",
            "{ value = (#bind parsed #u64);  }",
            lim::DiagnosticCode::Type,
        ),
        (
            main_with(BIND).replace("value = 42u64;", "value = 42u64; other = true;"),
            "unknown record literal field 'other'",
            "other",
            lim::DiagnosticCode::Type,
        ),
        (
            main_with(BIND).replace(
                "{ value = 42u64; consumed = 2usize; }",
                "{ value = 42u64; }",
            ),
            "missing field 'consumed'",
            "{ value = 42u64; }",
            lim::DiagnosticCode::Type,
        ),
        (
            linear_program("{ token = (#ignore Owned); count = (#ignore #usize); }", ""),
            "cannot ignore linear record field 'token'",
            "#ignore",
            lim::DiagnosticCode::Linear,
        ),
    ];
    for (source, message, expected, code) in cases {
        let diagnostic = record_diagnostic(&source);
        assert_eq!(diagnostic.code, code, "{diagnostic:?}");
        assert!(diagnostic.message.contains(message), "{diagnostic:?}");
        let span = diagnostic.span.expect("record error lost its source range");
        assert_eq!(&source[span.start..span.end], expected, "{diagnostic:?}");
    }
    let source = main_with(&BIND.replace(
        "consumed = (#ignore #usize);",
        "consumed = (#ignore #usize); consumed = (#ignore #usize);",
    ));
    let diagnostic = record_diagnostic(&source);
    let span = diagnostic.span.unwrap();
    assert_eq!(&source[span.start..span.end], "consumed");
    assert_eq!(span.start, source.rfind("consumed =").unwrap());
    let source = main_with(BIND).replace("value = 42u64;", "value = false;");
    let diagnostic = record_diagnostic(&source);
    let span = diagnostic.span.unwrap();
    assert_eq!(&source[span.start..span.end], "false", "{diagnostic:?}");
}

#[test]
fn named_generators_can_emit_explicit_anonymous_record_signatures() {
    let source = r#"
#gn emit { name; }
 `((#fn ,name { #params = (); #returns = { value = #u64; consumed = #usize; };
   #effects = (); #body = ((#return (#record-literal
     { value = #u64; consumed = #usize; } { value = 42u64; consumed = 2usize; }))); }))
#generate emit { name = make; }
#fn main { #params = (); #returns = #u64; #effects = (); #body = (
 (#let { value = (#bind answer #u64); consumed = (#ignore #usize); } = (make {}))
 (#return answer)); }
"#;
    check(source).unwrap();
}

const NAMED_RETURN_ORDER: &str = r#"
#struct Pair () ((a #u64) (z #u64))
#fn tick { #params = ((counter (#ref-mut #u64))); #returns = #u64; #effects = ();
 #body = ((#deref-set counter (#u64::add-wrap (#deref counter) 1u64)) (#return (#deref counter))); }
#fn pair { #params = ((counter (#ref-mut #u64))); #returns = Pair; #effects = ();
 #body = ((#return (#struct-literal Pair
   { z = (tick { counter = counter; }); a = (tick { counter = counter; }); }))); }
#fn main { #params = (); #returns = #u64; #effects = (); #body = (
 (#let-mut counter #u64 0u64)
 (#let (Pair second first) Pair (pair { counter = (#borrow-mut counter); }))
 (#assert (#u64::eq counter 2u64)) (#assert (#u64::eq first 1u64)) (#assert (#u64::eq second 2u64))
 (#return 42u64)); }
"#;

#[test]
fn ordinary_named_struct_direct_returns_preserve_written_effects() {
    for target in [
        lim::TargetDescription::X86_64_SYSTEM_V,
        lim::TargetDescription::AARCH64_LINUX,
    ] {
        run_on(NAMED_RETURN_ORDER, target);
    }
}

#[test]
fn layout_queries_fold_wide_float_unit_and_empty_array_types() {
    let source = r#"
#type Wide #u128
#type Real #f64
#struct Values () ((wide Wide) (real Real))
#enum Choice () ((Choice.Empty) (Choice.Full Wide))
#fn main { #params = (); #returns = #u64; #effects = (); #body = (
 (#assert (#usize::eq (#size-of ()) 0usize)) (#assert (#usize::eq (#align-of ()) 1usize))
 (#assert (#usize::eq (#size-of #u8) 8usize)) (#assert (#usize::eq (#align-of #u8) 8usize))
 (#assert (#usize::eq (#size-of Wide) 16usize)) (#assert (#usize::eq (#align-of Wide) 8usize))
 (#assert (#usize::eq (#size-of Real) 8usize)) (#assert (#usize::eq (#align-of Real) 8usize))
 (#assert (#usize::eq (#size-of #f32) 8usize)) (#assert (#usize::eq (#align-of #f32) 8usize))
 (#assert (#usize::eq (#size-of Values) 24usize)) (#assert (#usize::eq (#align-of Values) 8usize))
 (#assert (#usize::eq (#size-of Choice) 24usize)) (#assert (#usize::eq (#align-of Choice) 8usize))
 (#assert (#usize::eq (#size-of (#array #u64 0)) 0usize))
 (#assert (#usize::eq (#align-of (#array #u64 0)) 8usize))
 (#return 42u64)); }
"#;
    for target in [
        lim::TargetDescription::X86_64_SYSTEM_V,
        lim::TargetDescription::AARCH64_LINUX,
    ] {
        run_on(source, target);
    }
}

#[test]
fn array_repeat_keeps_its_value_operand_and_linear_diagnostic() {
    let source = include_str!("ui/array-repeat-linear.lim");
    let diagnostic = record_diagnostic(source);
    assert_eq!(
        diagnostic.code,
        lim::DiagnosticCode::Linear,
        "{diagnostic:?}"
    );
    let span = diagnostic
        .span
        .expect("linear repetition lost its value range");
    assert_eq!(
        &source[span.start..span.end],
        "(#array-repeat (#struct-literal Token ((value 1u64))))"
    );
}
