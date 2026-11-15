mod support;

use std::{fs, path::Path, process::Command, time::Duration};

const BASE: &str = r#"
#distributed-enum Choice ()
#enum-contribute Choice (Choice.Full #u64)
#enum-contribute Choice (Choice.Empty)
#dispatch-fn evaluate {
  #params = { value = Choice; extra = #u64; };
  #returns = #u64;
  #dispatch-on = value;
}
#dispatch-case evaluate Choice.Full full
#dispatch-case evaluate Choice.Empty empty
#fn full { #params = { extra = #u64; value = #u64; }; #returns = #u64;
  #body = ((#return (#u64::add-wrap value extra))); }
#fn empty { #params = { extra = #u64; }; #returns = #u64; #body = ((#return extra)); }
#fn main { #params = {}; #returns = #u64;
  #body = ((#return (evaluate { value = (Choice.Full 40u64); extra = 2u64; }))); }
"#;

fn compile_at(source: &str, root: &Path) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &root.join("main.lim"),
        &lim::CompileConfig::default(),
        &root.join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}
fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("distributed-dispatch");
    compile_at(source, scratch.path())
}
fn reject(source: &str, text: &str) -> lim::Diagnostic {
    let error = compile(source).expect_err("dispatch fixture must fail");
    assert!(
        error.message.contains(text),
        "expected {text}: {error:?}\n{source}"
    );
    error
}
fn artifacts(root: &Path) -> Vec<std::path::PathBuf> {
    let mut paths = fs::read_dir(root.join("generated"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "lim"))
        .filter(|path| {
            fs::read_to_string(path)
                .unwrap()
                .contains("producer \"#dispatch-fn\"")
        })
        .collect::<Vec<_>>();
    paths.sort();
    paths
}

#[test]
fn ordinary_exhaustive_dispatch_executes_and_forwards_named_arguments() {
    let scratch = support::Scratch::new("distributed-dispatch-native");
    let source = include_str!("../examples/distributed_dispatch.lim");
    let assembly = compile_at(source, scratch.path()).unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(3), 1024).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
    let text = fs::read_to_string(&artifacts(scratch.path())[0]).unwrap();
    assert!(text.contains("#match"));
    assert!(text.contains("#call"));
    assert!(!text.contains("#dispatch-case"));
}

#[test]
fn missing_coverage_points_to_dispatcher_and_variant() {
    let source = BASE.replace("#dispatch-case evaluate Choice.Empty empty", "");
    let error = reject(&source, "missing a handler");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "evaluate");
    assert!(error
        .labels
        .iter()
        .any(|label| source[label.span.start..label.span.end].contains("Choice.Empty")));
}

#[test]
fn identical_registrations_and_aliases_deduplicate() {
    let scratch = support::Scratch::new("dispatch-identical");
    let start = BASE.find("#fn full").unwrap();
    let end = BASE.find("#fn empty").unwrap();
    fs::write(scratch.path().join("handlers.lim"), &BASE[start..end]).unwrap();
    let base = format!("{}{}", &BASE[..start], &BASE[end..]);
    let source = format!("#alias full = ./handlers.lim::full\n#alias same = ./handlers.lim::full\n{base}\n#dispatch-case evaluate Choice.Full same\n#dispatch-case evaluate Choice.Full full\n");
    compile_at(&source, scratch.path()).unwrap();
    assert_eq!(artifacts(scratch.path()).len(), 1);
    let generated = fs::read_to_string(&artifacts(scratch.path())[0]).unwrap();
    assert_eq!(generated.matches("Choice.Full").count(), 1);
}

#[test]
fn conflicting_registrations_report_both_sources() {
    let source = format!("{BASE}\n#fn other {{ #params = {{ value = #u64; extra = #u64; }}; #returns = #u64; #body = ((#return value)); }}\n#dispatch-case evaluate Choice.Full other\n");
    let error = reject(&source, "conflicting handlers");
    assert_eq!(
        &source[error.span.unwrap().start..error.span.unwrap().end],
        "other"
    );
    assert!(error
        .labels
        .iter()
        .any(|label| source[label.span.start..label.span.end].contains("Choice.Full full")));
}

#[test]
fn bad_registration_targets_and_wrong_enum_variants_are_rejected() {
    reject(
        &BASE.replace(
            "#dispatch-case evaluate Choice.Full full",
            "#dispatch-case missing Choice.Full full",
        ),
        "unknown dispatch function",
    );
    reject(
        &BASE.replace(
            "#dispatch-case evaluate Choice.Full full",
            "#dispatch-case evaluate Other.Full full",
        ),
        "not in dispatch enum",
    );
    reject(
        &BASE.replace(
            "#dispatch-case evaluate Choice.Full full",
            "#dispatch-case evaluate Choice.Full missing",
        ),
        "unknown dispatch handler",
    );
}

#[test]
fn dispatch_parameter_must_name_a_supported_enum_input() {
    reject(
        &BASE.replace("#dispatch-on = value", "#dispatch-on = missing"),
        "not declared in #params",
    );
    reject(
        &BASE.replace("value = Choice", "value = #u64"),
        "must be an enum",
    );
    reject(
        &BASE.replace("value = Choice", "value = (#ptr Choice)"),
        "must be an enum",
    );
}

#[test]
fn all_projection_modes_emit_the_normal_case_form() {
    for (selected, projected, case) in [
        ("Choice", "Payload", "#case"),
        ("(#ref Choice)", "(#ref Payload)", "#case-ref"),
        ("(#ref-mut Choice)", "(#ref-mut Payload)", "#case-ref-mut"),
        ("(#pin-ref Choice)", "(#pin-ref Payload)", "#case-pin"),
        (
            "(#pin-ref-mut Choice)",
            "(#pin-ref-mut Payload)",
            "#case-pin-mut",
        ),
    ] {
        let scratch = support::Scratch::new("dispatch-projection");
        let source = format!(
            r#"
#struct Payload () ((number #u64))
#enum Choice () ((Choice.Full Payload) Choice.Empty)
#dispatch-fn inspect {{ #params = {{ value = {selected}; }}; #returns = #u64; #dispatch-on = value; }}
#dispatch-case inspect Choice.Full full
#dispatch-case inspect Choice.Empty empty
#fn full {{ #params = {{ value = {projected}; }}; #returns = #u64; #body = ((#return (#get value number))); }}
#fn empty {{ #params = {{}}; #returns = #u64; #body = ((#return 0u64)); }}
#fn main {{ #params = {{}}; #returns = #u64; #body = ((#return 42u64)); }}
"#
        );
        compile_at(&source, scratch.path()).unwrap();
        let generated = fs::read_to_string(&artifacts(scratch.path())[0]).unwrap();
        assert!(generated.contains(case), "{generated}");
    }
}

#[test]
fn handlers_need_exact_named_payload_forwarding_and_return_types() {
    reject(
        &BASE.replace("value = #u64; }; #returns", "value = #u32; }; #returns"),
        "incompatible payload or forwarding type",
    );
    reject(
        &BASE.replace("extra = #u64; value = #u64", "wrong = #u64; value = #u64"),
        "unexpected parameter",
    );
    reject(
        &BASE.replace(
            "#fn empty { #params = { extra = #u64; }; #returns = #u64",
            "#fn empty { #params = { extra = #u64; }; #returns = #u32",
        ),
        "incompatible return type",
    );
}

#[test]
fn missing_fieldless_omission_and_unsafe_targets_are_rejected() {
    reject(
        &BASE.replace(
            "#fn empty { #params = { extra = #u64; }",
            "#fn empty { #params = { extra = #u64; value = Choice; }",
        ),
        "incompatible named parameters",
    );
    reject(
        &BASE.replace("#fn full", "#unsafe-fn full"),
        "ordinary safe function",
    );
}

#[test]
fn ordinary_function_collisions_and_duplicate_dispatch_declarations_fail() {
    reject(
        &format!(
            "{BASE}\n#fn evaluate {{ #params = {{}}; #returns = (); #body = ((#return ())); }}\n"
        ),
        "conflicts with an ordinary function",
    );
    reject(&format!("{BASE}\n#dispatch-fn evaluate {{ #params = {{ value = Choice; }}; #returns = #u64; #dispatch-on = value; }}\n"), "duplicate dispatch declaration");
}

#[test]
fn authored_effect_interface_is_checked_without_widening() {
    let source = BASE.replace("#body = ((#return (#u64::add-wrap value extra)));", "#effects = (#io-output); #body = ((#let written #i64 (#io-output-byte 1i64 65u8)) (#return (#u64::add-wrap value extra)));");
    reject(&source, "explicit effect qualification");
    let source = source
        .replace(
            "#dispatch-on = value;",
            "#dispatch-on = value; #effects = (#io-output);",
        )
        .replace(
            "#fn main { #params = {}; #returns = #u64;",
            "#fn main { #params = {}; #returns = #u64; #effects = ((#effects-of evaluate));",
        );
    compile(&source).unwrap();
    reject(
        &source.replace("#effects = (#io-output);\n}", "#effects = (#io-input);\n}"),
        "explicit effect qualification",
    );
}

#[test]
fn owned_linear_payload_and_passthrough_values_use_normal_linearity() {
    let source = r#"
#struct Resource (#linear) ((number #u64))
#distributed-enum Choice (#linear)
#enum-contribute Choice (Choice.Full Resource)
#enum-contribute Choice (Choice.Empty)
#dispatch-fn consume { #params = { value = Choice; context = Resource; }; #returns = #u64; #dispatch-on = value; }
#dispatch-case consume Choice.Full full
#dispatch-case consume Choice.Empty empty
#fn full { #params = { value = Resource; context = Resource; }; #returns = #u64;
  #body = ((#let answer #u64 (#u64::add-wrap (#get value number) (#get context number))) (#forget value) (#forget context) (#return answer)); }
#fn empty { #params = { context = Resource; }; #returns = #u64; #body = ((#let answer #u64 (#get context number)) (#forget context) (#return answer)); }
#fn main { #params = {}; #returns = #u64; #body = ((#return 42u64)); }
"#;
    compile(source).unwrap();
    let repeated = source.replace("(#forget value)", "(#forget value) (#forget value)");
    let error = reject(&repeated, "was already consumed");
    assert_eq!(error.code, lim::DiagnosticCode::Linear);
    let span = error
        .span
        .expect("the repeated consume must retain its span");
    assert_eq!(&repeated[span.start..span.end], "value");
    assert_eq!(
        span.start,
        repeated.find("(#forget value) (#forget value)").unwrap()
            + "(#forget value) (#forget ".len()
    );
    assert!(error
        .labels
        .iter()
        .any(|label| label.message.contains("first consumed")));
}

#[test]
fn borrowed_payload_returns_keep_the_callers_real_dependency() {
    let source = r#"
#struct Payload () ((number #u64))
#enum Choice () ((Choice.Full Payload) Choice.Empty)
#dispatch-fn select { #params = { value = (#ref Choice); fallback = (#ref #u64); }; #returns = (#ref #u64); #dispatch-on = value; }
#dispatch-case select Choice.Full full
#dispatch-case select Choice.Empty empty
#fn full { #params = { value = (#ref Payload); fallback = (#ref #u64); }; #returns = (#ref #u64); #body = ((#return (#borrow (#get value number)))); }
#fn empty { #params = { fallback = (#ref #u64); }; #returns = (#ref #u64); #body = ((#return fallback)); }
#fn main { #params = {}; #returns = #u64; #body = (
  (#let-mut item Choice (Choice.Full (#struct-literal Payload ((number 42u64)))))
  (#let fallback #u64 0u64)
  (#let result (#ref #u64) (select { value = (#borrow item); fallback = (#borrow fallback); }))
  (#return (#deref result))
); }
"#;
    compile(source).unwrap();
    let error = compile(&source.replace(
        "(#return (#deref result))",
        "(#set item Choice.Empty) (#return (#deref result))",
    ))
    .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Borrow, "{error:?}");
}

#[test]
fn normal_recursion_checks_include_generated_dispatch_calls() {
    let source = BASE.replace(
        "(#return (#u64::add-wrap value extra))",
        "(#return (evaluate { value = (Choice.Full value); extra = extra; }))",
    );
    reject(&source, "recursive");
}

#[test]
fn nested_generators_contribute_before_enum_and_dispatch_freeze() {
    let source = BASE
        .replace("#enum-contribute Choice (Choice.Full #u64)", "")
        .replace("#dispatch-case evaluate Choice.Full full", "");
    let source = format!(
        r#"{source}
#gn inner {{ enum; dispatcher; variant; handler; }}
  `((#enum-contribute ,enum (,variant #u64)) (#dispatch-case ,dispatcher ,variant ,handler))
#gn outer {{}} `((#generate inner {{ enum = Choice; dispatcher = evaluate; variant = Choice.Full; handler = full; }}))
#generate outer {{}}
"#
    );
    let scratch = support::Scratch::new("dispatch-nested-generators");
    for _ in 0..2 {
        compile_at(&source, scratch.path()).unwrap();
    }
}

#[test]
fn cached_and_fresh_dispatch_use_the_same_artifact_without_rewriting_headers() {
    let scratch = support::Scratch::new("dispatch-warm-cache");
    let first = compile_at(BASE, scratch.path()).unwrap();
    let paths = artifacts(scratch.path());
    assert_eq!(paths.len(), 1);
    let before = fs::read_to_string(&paths[0]).unwrap();
    let timestamp = std::time::SystemTime::UNIX_EPOCH + Duration::from_secs(1_000_000);
    fs::OpenOptions::new()
        .write(true)
        .open(&paths[0])
        .unwrap()
        .set_times(fs::FileTimes::new().set_modified(timestamp))
        .unwrap();
    let (second, report) = lim::with_cache_report(|| compile_at(BASE, scratch.path()));
    assert_eq!(first, second.unwrap());
    assert_eq!(artifacts(scratch.path()), paths);
    assert_eq!(fs::read_to_string(&paths[0]).unwrap(), before);
    assert_eq!(
        fs::metadata(&paths[0]).unwrap().modified().unwrap(),
        timestamp
    );
    assert!(report.contains("\"decision\":\"hit\""), "{report}");
}

#[test]
fn declaration_and_registration_locate_the_real_compiled_file() {
    let scratch = support::Scratch::new("dispatch-navigation");
    let entry = scratch.path().join("main.lim");
    let positions = [
        BASE.find("#dispatch-fn").unwrap(),
        BASE.find("#dispatch-case").unwrap(),
    ];
    let mut expected = None;
    for position in positions {
        let paths = lim::locate_generated(
            BASE,
            &entry,
            &lim::CompileConfig::default(),
            &entry,
            position,
            position,
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert!(fs::read_to_string(&paths[0]).unwrap().contains("#match"));
        if let Some(previous) = &expected {
            assert_eq!(previous, &paths);
        }
        expected = Some(paths);
    }
}

fn write_library(root: &Path, public_handler: bool) -> String {
    fs::create_dir_all(root.join("api")).unwrap();
    fs::create_dir_all(root.join("provider")).unwrap();
    fs::write(
        root.join("api/lib.lim"),
        r#"
#export Choice evaluate
#distributed-enum Choice ()
#enum-contribute Choice (Choice.Full #u64)
#dispatch-fn evaluate { #params = { value = Choice; }; #returns = #u64; #dispatch-on = value; }
"#,
    )
    .unwrap();
    let exports = if public_handler {
        "#export marker handler"
    } else {
        "#export marker"
    };
    fs::write(
        root.join("provider/lib.lim"),
        format!(
            r#"{exports}
#alias api@Choice = ../api/lib.lim::Choice
#alias api@evaluate = ../api/lib.lim::evaluate
#dispatch-case api@evaluate api@Choice.Full handler
#fn handler {{ #params = {{ value = #u64; }}; #returns = #u64; #body = ((#return value)); }}
#fn marker {{ #params = {{}}; #returns = #u64; #body = ((#return 0u64)); }}
"#
        ),
    )
    .unwrap();
    "#alias marker = ./provider/lib.lim::marker\n#fn main { #params = {}; #returns = #u64; #body = ((#return 42u64)); }\n".into()
}

#[test]
fn registration_does_not_grant_its_modules_private_handler_authority() {
    let scratch = support::Scratch::new("dispatch-private-handler");
    let source = write_library(scratch.path(), false);
    let error = compile_at(&source, scratch.path()).unwrap_err();
    assert!(error.message.contains("private"), "{error:?}");
    assert!(
        error.labels.iter().any(|label| label
            .message
            .contains("registration grants no additional authority")),
        "{error:?}"
    );
}

#[test]
fn exported_adapter_can_cross_the_same_registration_boundary() {
    let scratch = support::Scratch::new("dispatch-public-adapter");
    let source = write_library(scratch.path(), true);
    for _ in 0..2 {
        compile_at(&source, scratch.path()).unwrap();
    }
}

#[test]
fn callbacks_and_registrations_do_not_grant_private_representation_access() {
    let scratch = support::Scratch::new("dispatch-private-memory");
    let source = write_library(scratch.path(), true);
    fs::create_dir(scratch.path().join("data")).unwrap();
    fs::write(
        scratch.path().join("data/lib.lim"),
        "#export Payload\n#struct Payload () ((secret #u64))\n#opaque Payload\n",
    )
    .unwrap();
    let api = fs::read_to_string(scratch.path().join("api/lib.lim")).unwrap();
    fs::write(
        scratch.path().join("api/lib.lim"),
        format!(
            "#alias Payload = ../data/lib.lim::Payload\n{}",
            api.replace("(Choice.Full #u64)", "(Choice.Full Payload)")
        ),
    )
    .unwrap();
    let provider = fs::read_to_string(scratch.path().join("provider/lib.lim")).unwrap();
    fs::write(
        scratch.path().join("provider/lib.lim"),
        format!(
            "#alias Payload = ../data/lib.lim::Payload\n{}",
            provider
                .replace("value = #u64", "value = Payload")
                .replace("(#return value)", "(#return (#get value secret))")
        ),
    )
    .unwrap();
    let error = compile_at(&source, scratch.path()).unwrap_err();
    assert!(
        error.message.contains("private") || error.message.contains("opaque"),
        "{error:?}"
    );
}

#[test]
fn multiple_dispatchers_share_one_frozen_enum_without_sharing_cases() {
    let source = format!("{BASE}\n#dispatch-fn another {{ #params = {{ value = Choice; extra = #u64; }}; #returns = #u64; #dispatch-on = value; }}\n#dispatch-case another Choice.Full full\n#dispatch-case another Choice.Empty empty\n");
    let scratch = support::Scratch::new("dispatch-independent");
    compile_at(&source, scratch.path()).unwrap();
    assert_eq!(artifacts(scratch.path()).len(), 2);
    reject(
        &source.replace("#dispatch-case another Choice.Empty empty", ""),
        "missing a handler",
    );
}

#[test]
fn registrations_can_precede_declarations_and_handlers() {
    let registrations =
        "#dispatch-case evaluate Choice.Full full\n#dispatch-case evaluate Choice.Empty empty\n";
    let source = format!(
        "{registrations}{}",
        BASE.replace("#dispatch-case evaluate Choice.Full full", "")
            .replace("#dispatch-case evaluate Choice.Empty empty", "")
    );
    compile(&source).unwrap();
}

#[test]
fn warm_cache_does_not_hide_changed_handler_effect_requirements() {
    let scratch = support::Scratch::new("dispatch-cached-permissions");
    compile_at(BASE, scratch.path()).unwrap();
    let paths = artifacts(scratch.path());
    let source = BASE.replace("#body = ((#return (#u64::add-wrap value extra)));", "#effects = (#io-output); #body = ((#let written #i64 (#io-output-byte 1i64 65u8)) (#return (#u64::add-wrap value extra)));");
    let error = compile_at(&source, scratch.path()).unwrap_err();
    assert!(
        error.message.contains("explicit effect qualification"),
        "{error:?}"
    );
    assert_eq!(artifacts(scratch.path()), paths);
}

#[test]
fn warm_cache_does_not_retain_revoked_handler_visibility() {
    let scratch = support::Scratch::new("dispatch-cached-visibility");
    let source = write_library(scratch.path(), true);
    compile_at(&source, scratch.path()).unwrap();
    write_library(scratch.path(), false);
    let error = compile_at(&source, scratch.path()).unwrap_err();
    assert!(error.message.contains("private"), "{error:?}");
}

#[test]
fn registered_handler_identity_survives_same_spelled_functions_elsewhere() {
    let scratch = support::Scratch::new("dispatch-handler-identity");
    let source = format!("{}\n#fn handler {{ #params = {{ value = #u64; }}; #returns = #u64; #body = ((#return 0u64)); }}\n", write_library(scratch.path(), true));
    compile_at(&source, scratch.path()).unwrap();
    let source = fs::read_to_string(&artifacts(scratch.path())[0]).unwrap();
    assert!(source.contains("provider/lib.lim::handler"), "{source}");
}

#[test]
fn parser_backed_enum_generators_and_safe_helpers_are_concrete_dispatch_inputs() {
    let source = r#"
#generate #optional { type = #u64; name = Maybe?; }
#enum Outer () ((Outer.Full Maybe?) Outer.Empty)
#dispatch-fn unwrap { #params = { value = Outer; fallback = #u64; }; #returns = #u64; #dispatch-on = value; }
#dispatch-case unwrap Outer.Full Maybe?::unwrap-or
#dispatch-case unwrap Outer.Empty empty
#fn empty { #params = { fallback = #u64; }; #returns = #u64; #body = ((#return fallback)); }
#fn main { #params = {}; #returns = #u64; #body = ((#return 42u64)); }
"#;
    compile(source).unwrap();
    let source = r#"
#generate #optional { type = #u64; name = Maybe?; }
#dispatch-fn inspect { #params = { value = Maybe?; }; #returns = #u64; #dispatch-on = value; }
#dispatch-case inspect Maybe?.Some some
#dispatch-case inspect Maybe?.None none
#fn some { #params = { value = #u64; }; #returns = #u64; #body = ((#return value)); }
#fn none { #params = {}; #returns = #u64; #body = ((#return 0u64)); }
#fn main { #params = {}; #returns = #u64; #body = ((#return 42u64)); }
"#;
    compile(source).unwrap();
}

#[test]
fn compiler_owned_dispatch_provenance_cannot_be_claimed_by_a_handler() {
    compile(&format!(
        "{BASE}\n#require-generated evaluate #dispatch-fn\n"
    ))
    .unwrap();
    let source = format!("{BASE}\n#require-generated full #dispatch-fn\n");
    let error = compile(&source).unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Generator);
    assert!(
        error
            .message
            .contains("was not generated by '#generate #dispatch-fn'"),
        "{error:?}"
    );
    let span = error
        .span
        .expect("provenance failures must identify the claimed name");
    assert_eq!(&source[span.start..span.end], "full");
}

#[test]
fn manifest_records_exact_cases_and_handlers_on_fresh_and_cached_parses() {
    let scratch = support::Scratch::new("dispatch-manifest");
    for _ in 0..2 {
        let (result, maps) = lim::with_dispatch_manifest(|| compile_at(BASE, scratch.path()));
        result.unwrap();
        assert_eq!(maps.len(), 1);
        let map = &maps[0];
        assert!(map.name.ends_with("evaluate"));
        assert_eq!(map.registrations.len(), 2);
        let generated = fs::read_to_string(&map.generated_path).unwrap();
        for registration in &map.registrations {
            let case = registration.generated_case.unwrap();
            let variant = registration.generated_variant.unwrap();
            let handler = registration.generated_handler.unwrap();
            assert_eq!(case.source_id, map.source_id);
            assert!(generated[case.start..case.end].contains("#case"));
            assert_eq!(&generated[variant.start..variant.end], registration.variant);
            assert_eq!(&generated[handler.start..handler.end], registration.handler);
        }
    }
}

#[test]
fn dispatch_syntax_and_emitted_source_roundtrip_through_the_formatter() {
    fn syntax(source: &str) -> Vec<lim::Expr> {
        lim::parse_source_unit(source)
            .unwrap()
            .into_iter()
            .map(|form| form.expr)
            .collect()
    }
    let scratch = support::Scratch::new("dispatch-source-roundtrip");
    let formatted = lim::format_source(BASE).unwrap();
    assert_eq!(syntax(BASE), syntax(&formatted));
    compile_at(&formatted, scratch.path()).unwrap();
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
    let generated = fs::read_to_string(&artifacts(scratch.path())[0]).unwrap();
    let formatted_generated = lim::format_source(&generated).unwrap();
    assert_eq!(syntax(&generated), syntax(&formatted_generated));
    assert_eq!(
        lim::format_source(&formatted_generated).unwrap(),
        formatted_generated
    );
}

#[test]
fn dispatch_producer_operand_does_not_hide_unseparated_root_declarations() {
    let source = "#require-generated evaluate #dispatch-fn #fn other { #params = {}; #returns = (); #body: #return (); }\n";
    let error = compile(source).unwrap_err();
    assert!(error.message.contains("separator"), "{error:?}");
    let span = error.span.expect("separator errors retain their authored token");
    assert_eq!(&source[span.start..span.end], "#fn");
}
