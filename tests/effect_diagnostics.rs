mod support;

use lim::{lsp::json::{self, Json}, CompileConfig, Diagnostic, DiagnosticCode};
use std::{fs, path::Path};

fn check(source: &str, path: &Path, root: &Path) -> Result<(), Diagnostic> {
    lim::check_source_with_generated_sources(
        source, path, &CompileConfig::default(), &root.join("cache"), &root.join("generated"),
    )
}
fn assert_range(error: &Diagnostic, path: &Path, source: &str, start: usize, token: &str) {
    assert_eq!(error.source_name.as_deref(), path.to_str(), "{error:?}");
    assert_eq!(error.source_text.as_deref(), Some(source), "{error:?}");
    let span = error.span.expect("effect diagnostics must retain their source span");
    assert_eq!((span.start, span.end), (start, start + token.len()), "{error:?}");
    assert_eq!(&source[span.start..span.end], token, "{error:?}");
    let prefix = &source[..start];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let column = prefix.rsplit('\n').next().unwrap().chars().count() + 1;
    assert_eq!((span.line, span.column), (line, column));

    // Imported source metadata must override deliberately unrelated fallbacks.
    let rendered = lim::render_diagnostic(error, "wrong fallback source", "wrong-file.lim");
    assert!(rendered.contains(&format!("{}:{line}:{column}", path.display())), "{rendered}");
    assert!(rendered.contains(token), "{rendered}");
    assert!(rendered.contains('^'), "{rendered}");
    assert!(!rendered.contains("wrong fallback source"), "{rendered}");
    assert!(!error.message.contains("source span"), "{error:?}");

    let rendered = lim::render_diagnostic_json(error, "wrong-file.lim");
    let value = json::parse(&rendered).unwrap();
    let location = value.get("location").unwrap();
    assert_eq!(location.get("path").and_then(Json::string), path.to_str());
    for (field, expected) in [
        ("byte_start", start), ("byte_end", start + token.len()),
        ("line", line), ("column", column),
    ] {
        assert_eq!(location.get(field).and_then(Json::integer), Some(expected as i64), "{rendered}");
    }
    assert_eq!(value.get("labels").unwrap().array().unwrap()[0].get("primary"), Some(&Json::Bool(true)));
}

#[test]
fn missing_byte_io_permissions_point_to_the_operation_inside_the_statement() {
    let scratch = support::Scratch::new("effect-use-diagnostic");
    let path = scratch.path().join("main.lim");
    for (result, operation, permission) in [
        ("(#tuple #i64 #u8)", "(#io-input-byte 0i64)", "#io-input"),
        ("#i64", "(#io-output-byte 1i64 65u8)", "#io-output"),
    ] {
        let source = format!("// λ exercises source offsets\n#fn main {{\n  #params = ();\n  #returns = {result};\n  #body = (\n    (#return {operation})\n  );\n}}\n");
        let error = check(&source, &path, scratch.path()).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Contract);
        assert!(error.message.contains("explicit effect qualification"), "{error:?}");
        assert!(error.message.contains(permission), "{error:?}");
        assert_range(&error, &path, &source, source.find(operation).unwrap(), operation);
        let qualified = source.replace("  #body =", &format!("  #effects = ({permission});\n  #body ="));
        check(&qualified, &path, scratch.path()).unwrap();
    }
}

#[test]
fn missing_call_permission_underlines_the_imported_alias_at_its_use() {
    let scratch = support::Scratch::new("effect-call-diagnostic");
    fs::write(scratch.path().join("output.lim"), "#fn output { #params = (); #returns = (); #effects = (#io-output); #body = ( (#return ()) ); }\n").unwrap();
    fs::write(scratch.path().join("facade.lim"), "#alias send = ./output.lim::output\n").unwrap();
    let source = "#alias renamed = ./facade.lim::send\n#fn main {\n  #params = (); #returns = ();\n  #body = (\n    (#let unrelated #u64 42u64)\n    (#call renamed ())\n    (#return ())\n  );\n}\n";
    let path = scratch.path().join("main.lim");
    let error = check(source, &path, scratch.path()).unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Contract);
    assert!(error.message.contains("#io-output") && error.message.contains("call to"), "{error:?}");
    assert_range(&error, &path, source, source.find("(#call renamed ())").unwrap(), "(#call renamed ())");
    let qualified = source.replace("  #body =", "  #effects = ((#effects-of @renamed));\n  #body =");
    check(&qualified, &path, scratch.path()).unwrap();
}

#[test]
fn malformed_effect_qualifications_underline_the_offending_form_or_token() {
    let scratch = support::Scratch::new("effect-malformed-diagnostic");
    let path = scratch.path().join("main.lim");
    for (effects, token, message) in [
        ("(#invented)", "#invented", "expected #io"),
        ("((#read-global))", "(#read-global)", "exactly one declaration name"),
        ("((#read-global 7u64))", "7u64", "effect targets must be declaration names"),
        ("(#io #io)", "#io", "duplicate effect qualification"),
    ] {
        let source = format!("#fn main {{\n  #params = ();\n  #returns = ();\n  #effects = {effects};\n  #body = ( (#return ()) );\n}}\n");
        let error = check(&source, &path, scratch.path()).unwrap_err();
        assert!(error.message.contains(message), "{error:?}");
        // Duplicate qualifications must select the second occurrence.
        assert_range(&error, &path, &source, source.rfind(token).unwrap(), token);
    }
}

#[test]
fn wrong_effect_target_kinds_underline_the_target_reference() {
    let scratch = support::Scratch::new("effect-target-diagnostic");
    let path = scratch.path().join("main.lim");
    let declarations = "#static counter (#atomic #u64) (#atomic-init #u64 0u64)\n#fn helper { #params = (); #returns = (); #body = ( (#return ()) ); }\n";
    for (qualification, target, message) in [
        ("(#read-global helper)", "helper", "not a global declaration"),
        ("(#write-global helper)", "helper", "not a global declaration"),
        ("(#effects-of @counter)", "@counter", "not a function declaration"),
    ] {
        let source = format!("{declarations}#fn main {{\n  #params = ();\n  #returns = ();\n  #effects = ({qualification});\n  #body = ( (#return ()) );\n}}\n");
        let error = check(&source, &path, scratch.path()).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Contract);
        assert!(error.message.contains(message), "{error:?}");
        assert_range(&error, &path, &source, source.rfind(target).unwrap(), target);
    }
}

#[test]
fn imported_alias_target_errors_keep_the_authored_reference_and_source_file() {
    let scratch = support::Scratch::new("effect-target-alias-diagnostic");
    let types = "#static counter (#atomic #u64) (#atomic-init #u64 0u64)\n#fn helper { #params = (); #returns = (); #body = ( (#return ()) ); }\n";
    fs::write(scratch.path().join("types.lim"), types).unwrap();
    let path = scratch.path().join("main.lim");
    let imported = scratch.path().join("module.lim");
    let root = "#alias operation = ./module.lim::broken\n";
    for (target, qualification, token, message) in [
        ("helper", "(#read-global target)", "target", "not a global declaration"),
        ("helper", "(#write-global target)", "target", "not a global declaration"),
        ("counter", "(#effects-of @target)", "@target", "not a function declaration"),
    ] {
        let module = format!("#alias target = ./types.lim::{target}\n#fn broken {{\n  #params = ();\n  #returns = ();\n  #effects = ({qualification});\n  #body = ( (#return ()) );\n}}\n");
        fs::write(&imported, &module).unwrap();
        let error = check(root, &path, scratch.path()).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Contract);
        assert!(error.message.contains(message), "{error:?}");
        assert_range(&error, &imported, &module, module.rfind(token).unwrap(), token);
        assert_ne!(error.span.unwrap().source_id, 0);
        assert!(error.expansion_provenance.is_empty(), "plain imports are not generated expansions: {error:?}");
    }
}

#[test]
fn malformed_effects_in_imports_do_not_point_at_the_root_alias() {
    let scratch = support::Scratch::new("effect-import-malformed-diagnostic");
    let path = scratch.path().join("main.lim");
    let imported = scratch.path().join("module.lim");
    let module = "// imported malformed declaration\n#fn broken {\n  #params = ();\n  #returns = ();\n  #effects = (#invented);\n  #body = ( (#return ()) );\n}\n";
    fs::write(&imported, module).unwrap();
    let root = "#alias operation = ./module.lim::broken\n";
    let error = check(root, &path, scratch.path()).unwrap_err();
    assert!(error.message.contains("expected #io"), "{error:?}");
    assert_range(&error, &imported, module, module.find("#invented").unwrap(), "#invented");
}

#[test]
fn missing_global_read_and_write_permissions_point_to_the_access() {
    let scratch = support::Scratch::new("effect-global-use-diagnostic");
    let path = scratch.path().join("main.lim");
    let read = "#let answer #u64 42u64\n#fn main {\n  #params = (); #returns = #u64;\n  #body = ( (#return (#u64::add-wrap 0u64 answer)) );\n}\n";
    let operation = "(#atomic-store (#borrow counter) 1u64 #memory-relaxed)";
    let write = format!("#static counter (#atomic #u64) (#atomic-init #u64 0u64)\n#fn main {{\n  #params = (); #returns = ();\n  #effects = ((#read-global counter));\n  #body = ( (#unsafe {operation}) (#return ()) );\n}}\n");
    for (source, token, permission) in [
        (read, "answer", "(#read-global answer)"),
        (write.as_str(), operation, "(#write-global counter)"),
    ] {
        let error = check(source, &path, scratch.path()).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Contract);
        assert!(error.message.contains(permission), "{error:?}");
        assert_range(&error, &path, source, source.rfind(token).unwrap(), token);
        let qualified = if source == read {
            source.replace("  #body =", "  #effects = ((#read-global answer));\n  #body =")
        } else {
            source.replace("(#read-global counter)", "(#write-global counter)")
        };
        check(&qualified, &path, scratch.path()).unwrap();
    }
}
