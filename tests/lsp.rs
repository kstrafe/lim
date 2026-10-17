pub use lim::{Diagnostic, DiagnosticCode, Span};
#[path = "../src/diagnostic_json.rs"]
mod diagnostic_json;
use lim::{format_source, lsp, CompileConfig};

use lsp::json::{self, Json};
use std::{io::Cursor, path::Path};

fn request(id: i64, method: &str, params: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":{},\"params\":{params}}}",
        diagnostic_json::quoted(method)
    )
}
fn notify(method: &str, params: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":{},\"params\":{params}}}",
        diagnostic_json::quoted(method)
    )
}
fn start() -> Vec<String> {
    vec![request(1, "initialize", "{}"), notify("initialized", "{}")]
}
fn open(uri: &str, version: i64, text: &str) -> String {
    notify("textDocument/didOpen", &format!("{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lim\",\"version\":{version},\"text\":{}}}}}", diagnostic_json::quoted(uri), diagnostic_json::quoted(text)))
}
fn change(uri: &str, version: i64, text: &str) -> String {
    notify("textDocument/didChange", &format!("{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}", diagnostic_json::quoted(uri), diagnostic_json::quoted(text)))
}
fn document(uri: &str) -> String {
    format!(
        "{{\"textDocument\":{{\"uri\":{}}}}}",
        diagnostic_json::quoted(uri)
    )
}
fn session(messages: Vec<String>) -> (i32, Vec<Json>) {
    let mut input = Vec::new();
    for message in messages {
        json::write_frame(&mut input, &message).unwrap();
    }
    let mut output = Vec::new();
    let code = lsp::serve(Cursor::new(input), &mut output, &CompileConfig::default()).unwrap();
    let mut cursor = Cursor::new(output);
    let mut responses = Vec::new();
    while let Some(body) = json::read_frame(&mut cursor).unwrap() {
        responses.push(json::parse(&body).unwrap());
    }
    (code, responses)
}
fn reply(messages: &[Json], id: i64) -> &Json {
    messages
        .iter()
        .find(|m| m.get("id").and_then(Json::integer) == Some(id))
        .unwrap()
}
fn publications(messages: &[Json]) -> Vec<&Json> {
    messages
        .iter()
        .filter(|m| {
            m.get("method").and_then(Json::string) == Some("textDocument/publishDiagnostics")
        })
        .map(|m| m.get("params").unwrap())
        .collect()
}
fn finish(messages: &mut Vec<String>) {
    messages.push(request(99, "shutdown", "null"));
    messages.push(notify("exit", "null"));
}

fn definition(id: i64, uri: &str, text: &str, needle: &str) -> String {
    let byte = text.find(needle).unwrap();
    let (line, character) = lsp::byte_position(text, byte);
    request(id, "textDocument/definition", &format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}",
        diagnostic_json::quoted(uri)
    ))
}

fn artifact_paths(messages: &[Json], id: i64) -> Vec<std::path::PathBuf> {
    let result = reply(messages, id).get("result").unwrap();
    let locations = result.array().unwrap_or_else(|| panic!("{id}: {result:?}"));
    assert!(!locations.is_empty(), "{id}: no artifacts");
    locations
        .iter()
        .map(|location| {
            let path = lsp::uri_to_path(location.get("uri").unwrap().string().unwrap()).unwrap();
            assert!(path.is_file(), "{}", path.display());
            assert!(path
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .starts_with("generated-"));
            path
        })
        .collect()
}

fn context(entry: &Path, config: CompileConfig) -> lim::lsp_context::LspContext {
    lim::lsp_context::LspContext {
        entry: entry.to_owned(),
        target: lim::TargetDescription::X86_64_SYSTEM_V,
        config,
    }
}

fn definition_locations(messages: &[Json], id: i64) -> Vec<&Json> {
    let result = reply(messages, id).get("result").unwrap();
    match result {
        Json::Array(locations) => locations.iter().collect(),
        Json::Null => vec![],
        location => vec![location],
    }
}

#[test]
fn shared_library_navigation_returns_definitions_from_each_including_entry_only() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-entries-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let app = base.join("app.lim");
    let test = base.join("test.lim");
    let bench = base.join("bench.lim");
    let unrelated = base.join("unrelated.lim");
    let library_text = "(#fn read-value () Value (#return (#call provide ())))";
    let app_text = "(#import \"library.lim\")\n(#type Value #u64)\n(#fn provide () Value (#return 10u64))\n(#fn main () #u64 (#return (#call read-value ())))";
    let test_text = app_text.replace("10u64", "20u64");
    let bench_text = app_text.replace("10u64", "30u64");
    for (path, text) in [
        (&library, library_text),
        (&app, app_text),
        (&test, &test_text),
        (&bench, &bench_text),
        (&unrelated, "(#fn provide () #u64 (#return 99u64))"),
    ] {
        std::fs::write(path, text).unwrap();
    }
    lim::lsp_context::LspContext::write_all(
        &[
            context(&app, CompileConfig::default()),
            context(&test, CompileConfig::default()),
            context(&bench, CompileConfig::default()),
            context(&unrelated, CompileConfig::default()),
        ],
        &base.join("lim.lsp"),
    )
    .unwrap();
    let library_uri = lsp::path_to_uri(&library).unwrap();
    let app_uri = lsp::path_to_uri(&app).unwrap();
    let mut messages = start();
    messages.push(open(&library_uri, 1, library_text));
    messages.push(open(&app_uri, 1, app_text));
    messages.push(definition(2, &library_uri, library_text, "provide"));
    messages.push(definition(3, &library_uri, library_text, "Value"));
    messages.push(definition(4, &app_uri, app_text, "read-value"));
    messages.push(definition(5, &library_uri, library_text, "read-value"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    for id in [2, 3] {
        let locations = definition_locations(&replies, id);
        assert_eq!(locations.len(), 3, "{locations:?}");
        let uris = locations
            .iter()
            .map(|location| location.get("uri").unwrap().string().unwrap())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            uris,
            [
                lsp::path_to_uri(&app).unwrap(),
                lsp::path_to_uri(&test).unwrap(),
                lsp::path_to_uri(&bench).unwrap(),
            ]
            .iter()
            .map(String::as_str)
            .collect()
        );
        for location in locations {
            let start = location.get("range").unwrap().get("start").unwrap();
            assert_eq!(
                start.get("line").and_then(Json::integer),
                Some(if id == 2 { 2 } else { 1 })
            );
            assert_eq!(
                start.get("character").and_then(Json::integer),
                Some(if id == 2 { 5 } else { 7 })
            );
        }
    }
    for id in [4, 5] {
        let locations = definition_locations(&replies, id);
        assert_eq!(locations.len(), 1);
        assert_eq!(
            locations[0].get("uri").unwrap().string(),
            Some(library_uri.as_str())
        );
    }
    assert!(!base.join(".lim").exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn multi_context_cfg_and_unsaved_buffers_select_distinct_definitions_in_one_entry() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-cfg-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let entry = base.join("main.lim");
    let library = base.join("library.lim");
    let library_text = "(#fn read-value () #u64 (#return (#call provide ())))";
    let entry_text = "(#import \"library.lim\")\n(#cfg-if (#cfg-is #mode app)\n (#fn provide () #u64 (#return 10u64))\n (#cfg-else (#fn provide () #u64 (#return 20u64))))\n(#fn main () #u64 (#return (#call read-value ())))";
    std::fs::write(&entry, ")").unwrap();
    std::fs::write(&library, ")").unwrap();
    let mut app = CompileConfig::default();
    app.set("mode", "app");
    let mut test = CompileConfig::default();
    test.set("mode", "test");
    lim::lsp_context::LspContext::write_all(
        &[context(&entry, app), context(&entry, test)],
        &base.join("lim.lsp"),
    )
    .unwrap();
    let entry_uri = lsp::path_to_uri(&entry).unwrap();
    let library_uri = lsp::path_to_uri(&library).unwrap();
    let mut messages = start();
    messages.push(open(&entry_uri, 1, entry_text));
    messages.push(open(&library_uri, 1, library_text));
    messages.push(definition(2, &library_uri, library_text, "provide"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let locations = definition_locations(&replies, 2);
    assert_eq!(locations.len(), 2, "{locations:?}");
    let lines = locations
        .iter()
        .map(|location| {
            assert_eq!(
                location.get("uri").unwrap().string(),
                Some(entry_uri.as_str())
            );
            location
                .get("range")
                .unwrap()
                .get("start")
                .unwrap()
                .get("line")
                .unwrap()
                .integer()
                .unwrap()
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(lines, [2, 3].into_iter().collect());
    assert_eq!(std::fs::read_to_string(&entry).unwrap(), ")");
    assert!(!base.join(".lim").exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn multi_context_generated_calls_macro_names_and_artifacts_keep_both_producers() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-generated-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let library_text = "(@emit)\n(#fn read-value () #u64 (#return (#call provide ())))";
    std::fs::write(&library, library_text).unwrap();
    let mut contexts = Vec::new();
    for (name, value) in [("app", 10), ("test", 20)] {
        let entry = base.join(format!("{name}.lim"));
        let text = format!("(#import \"library.lim\")\n(#gn emit () `((#fn provide () #u64 (#return {value}u64))))\n(#fn main () #u64 (#return (#call read-value ())))");
        std::fs::write(&entry, text).unwrap();
        contexts.push(context(&entry, CompileConfig::default()));
    }
    lim::lsp_context::LspContext::write_all(&contexts, &base.join("lim.lsp")).unwrap();
    let uri = lsp::path_to_uri(&library).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, library_text));
    messages.push(definition(2, &uri, library_text, "provide"));
    messages.push(definition(3, &uri, library_text, "emit"));
    messages.push(definition(4, &uri, library_text, "@"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(definition_locations(&replies, 2).len(), 2);
    let producers = definition_locations(&replies, 3);
    assert_eq!(producers.len(), 2);
    for location in producers {
        assert!(
            location
                .get("uri")
                .unwrap()
                .string()
                .unwrap()
                .ends_with("app.lim")
                || location
                    .get("uri")
                    .unwrap()
                    .string()
                    .unwrap()
                    .ends_with("test.lim")
        );
    }
    let artifacts = artifact_paths(&replies, 4);
    assert_eq!(artifacts.len(), 2);
    let sources = artifacts
        .iter()
        .map(|path| std::fs::read_to_string(path).unwrap())
        .collect::<Vec<_>>();
    assert!(
        sources
            .iter()
            .any(|source| source.contains("#literal #u64 10")),
        "{sources:?}"
    );
    assert!(
        sources
            .iter()
            .any(|source| source.contains("#literal #u64 20")),
        "{sources:?}"
    );
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn multi_context_import_paths_and_external_names_follow_each_entries_module_paths() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-modules-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let text =
        "(#import \"dependency.lim\")\n(#fn read-value () #u64 (#return (#call provide ())))";
    std::fs::write(&library, text).unwrap();
    let mut contexts = Vec::new();
    let mut expected = std::collections::BTreeSet::new();
    for (name, prefix) in [("app", ""), ("test", "Ext-")] {
        let modules = base.join(format!("{name}-modules"));
        std::fs::create_dir(&modules).unwrap();
        let dependency = modules.join("dependency.lim");
        std::fs::write(&dependency, "(#fn provide () #u64 (#return 42u64))").unwrap();
        expected.insert(lsp::path_to_uri(&dependency).unwrap());
        let entry = base.join(format!("{name}.lim"));
        let import = if prefix.is_empty() {
            "(#import \"library.lim\")"
        } else {
            "(#import-external \"library.lim\" Ext-)"
        };
        std::fs::write(
            &entry,
            format!("{import}\n(#fn main () #u64 (#return (#call {prefix}read-value ())))"),
        )
        .unwrap();
        let mut config = CompileConfig::default();
        config.add_module_path(modules);
        contexts.push(context(&entry, config));
    }
    lim::lsp_context::LspContext::write_all(&contexts, &base.join("lim.lsp")).unwrap();
    let uri = lsp::path_to_uri(&library).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, text));
    messages.push(definition(2, &uri, text, "provide"));
    messages.push(definition(3, &uri, text, "dependency.lim"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    for id in [2, 3] {
        let locations = definition_locations(&replies, id);
        let actual = locations
            .iter()
            .map(|location| location.get("uri").unwrap().string().unwrap().to_owned())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(actual, expected, "{id}: {locations:?}");
    }
    assert!(!base.join(".lim").exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn multi_context_diagnostics_identify_failing_entry_and_do_not_block_other_definitions() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-errors-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let text = "(#fn read-value () #u64 (#return (#call provide ())))";
    std::fs::write(&library, text).unwrap();
    let app = base.join("app.lim");
    let test = base.join("test.lim");
    let broken = base.join("broken.lim");
    std::fs::write(
        &app,
        "(#import \"library.lim\") (#fn provide () #u64 (#return 42u64))",
    )
    .unwrap();
    std::fs::write(
        &test,
        "(#import \"library.lim\") (#fn provide () #bool (#return false))",
    )
    .unwrap();
    std::fs::write(&broken, ")").unwrap();
    lim::lsp_context::LspContext::write_all(
        &[
            context(&app, CompileConfig::default()),
            context(&test, CompileConfig::default()),
            context(&broken, CompileConfig::default()),
        ],
        &base.join("lim.lsp"),
    )
    .unwrap();
    let uri = lsp::path_to_uri(&library).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, text));
    messages.push(definition(2, &uri, text, "provide"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(definition_locations(&replies, 2).len(), 2);
    let reports = publications(&replies);
    let report = reports
        .iter()
        .find(|report| report.get("uri").unwrap().string() == Some(uri.as_str()))
        .unwrap();
    let diagnostics = report.get("diagnostics").unwrap().array().unwrap();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let message = diagnostics[0].get("message").unwrap().string().unwrap();
    assert!(message.contains(test.to_str().unwrap()), "{message}");
    assert!(!message.contains(app.to_str().unwrap()), "{message}");
    assert!(reports
        .iter()
        .all(|report| report.get("uri").unwrap().string()
            != Some(lsp::path_to_uri(&broken).unwrap().as_str())));
    assert!(!base.join(".lim").exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn cfg_excluded_calls_do_not_add_another_entries_matching_name() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-inactive-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let text =
        "(#cfg-if (#cfg-is #mode app) (#fn read-value () #u64 (#return (#call provide ()))))";
    std::fs::write(&library, text).unwrap();
    let mut contexts = Vec::new();
    let mut app_uri = String::new();
    for mode in ["app", "test"] {
        let entry = base.join(format!("{mode}.lim"));
        std::fs::write(
            &entry,
            "(#import \"library.lim\") (#fn provide () #u64 (#return 42u64))",
        )
        .unwrap();
        let mut config = CompileConfig::default();
        config.set("mode", mode);
        if mode == "app" {
            app_uri = lsp::path_to_uri(&entry).unwrap();
        }
        contexts.push(context(&entry, config));
    }
    lim::lsp_context::LspContext::write_all(&contexts, &base.join("lim.lsp")).unwrap();
    let uri = lsp::path_to_uri(&library).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, text));
    messages.push(definition(2, &uri, text, "provide"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let locations = definition_locations(&replies, 2);
    assert_eq!(locations.len(), 1, "{locations:?}");
    assert_eq!(
        locations[0].get("uri").unwrap().string(),
        Some(app_uri.as_str())
    );
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn unused_type_warnings_have_warning_severity_and_clear_when_used() {
    let uri = "file:///tmp/lim-lsp-unused-types.lim";
    let source = "(#enum Unused () (Only))";
    let updated =
        format!("{source}\n(#fn consume (: value Unused) () (#forget value) (#return ()))");
    let mut messages = start();
    messages.push(open(uri, 1, source));
    messages.push(change(uri, 2, &updated));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let reports = publications(&replies);
    assert_eq!(reports.len(), 2);
    let diagnostics = reports[0].get("diagnostics").unwrap().array().unwrap();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].get("severity").and_then(Json::integer),
        Some(2)
    );
    assert_eq!(
        diagnostics[0].get("code").and_then(Json::string),
        Some("W8000")
    );
    assert_eq!(
        diagnostics[0]
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("character")
            .and_then(Json::integer),
        Some(7)
    );
    assert!(reports[1]
        .get("diagnostics")
        .unwrap()
        .array()
        .unwrap()
        .is_empty());
}

#[test]
fn macro_at_uses_current_artifacts_across_multiline_positions_and_warm_cache() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-at-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let path = base.join("main.lim");
    let uri = lsp::path_to_uri(&path).unwrap();
    let source = "; 😀 UTF-16 position\n(#gn emit (name) `((#type ,name #u64)))\n(\n  @emit First\n)\n(#type Emoji😀 #u8) (@emit Second)";
    std::fs::write(&path, source).unwrap();
    let updated = source.replace("#u64", "#u32");
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(definition(2, &uri, source, "@emit First"));
    messages.push(definition(3, &uri, source, "@emit First"));
    messages.push(definition(4, &uri, source, "@emit Second"));
    messages.push(change(&uri, 2, &updated));
    messages.push(definition(5, &uri, &updated, "@emit First"));
    messages.push(definition(6, &uri, &updated, "emit First"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let first = artifact_paths(&replies, 2);
    assert_eq!(first, artifact_paths(&replies, 3));
    let second = artifact_paths(&replies, 4);
    assert_ne!(first, second);
    assert!(std::fs::read_to_string(&first[0])
        .unwrap()
        .contains("(#type First #u64)"));
    assert!(std::fs::read_to_string(&second[0])
        .unwrap()
        .contains("(#type Second #u64)"));
    let changed = artifact_paths(&replies, 5);
    assert_ne!(first, changed);
    assert!(std::fs::read_to_string(&changed[0])
        .unwrap()
        .contains("(#type First #u32)"));
    let declaration = reply(&replies, 6).get("result").unwrap();
    assert_eq!(
        declaration.get("uri").and_then(Json::string),
        Some(uri.as_str())
    );
    assert_eq!(
        declaration
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("line")
            .and_then(Json::integer),
        Some(1)
    );
    assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn macro_navigation_uses_entry_cfg_module_paths_and_all_unsaved_overlays() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-context-{}", std::process::id()));
    std::fs::create_dir_all(base.join("modules")).unwrap();
    let entry = base.join("main.lim");
    let child = base.join("child.lim");
    let generator = base.join("modules/generator.lim");
    // Both entry and imported declaration are invalid on disk.
    std::fs::write(&entry, ")").unwrap();
    std::fs::write(&generator, ")").unwrap();
    let entry_source = "(#import \"generator.lim\") (#import \"child.lim\")";
    let generator_source = "\n(#cfg-if (#cfg-is #feature selected) (#gn emit (name) `((#type ,name #u32))) (#cfg-else (#gn emit (name) `((#type ,name #u64)))))";
    let child_source = "(\n @emit Number\n)";
    let mut config = CompileConfig::default();
    config.set("feature", "selected");
    config.add_module_path(base.join("modules"));
    lim::lsp_context::LspContext {
        entry: entry.clone(),
        config,
        target: lim::TargetDescription::X86_64_SYSTEM_V,
    }
    .write(&base.join("lim.lsp"))
    .unwrap();
    let entry_uri = lsp::path_to_uri(&entry).unwrap();
    let uri = lsp::path_to_uri(&child).unwrap();
    let generator_uri = lsp::path_to_uri(&generator).unwrap();
    let mut messages = start();
    messages.push(open(&entry_uri, 1, entry_source));
    messages.push(open(&generator_uri, 1, generator_source));
    messages.push(open(&uri, 1, child_source));
    messages.push(definition(2, &uri, child_source, "@"));
    messages.push(definition(3, &uri, child_source, "emit"));
    messages.push(change(
        &generator_uri,
        2,
        &generator_source.replace("#u32", "#u16"),
    ));
    messages.push(definition(4, &uri, child_source, "@"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let before = artifact_paths(&replies, 2);
    assert!(before
        .iter()
        .all(|path| path.starts_with(base.join(".lim/generated"))));
    assert!(!child.parent().unwrap().join("modules/.lim").exists());
    assert!(std::fs::read_to_string(&before[0])
        .unwrap()
        .contains("(#type Number #u32)"));
    let after = artifact_paths(&replies, 4);
    assert_ne!(before, after);
    assert!(std::fs::read_to_string(&after[0])
        .unwrap()
        .contains("(#type Number #u16)"));
    let declaration = reply(&replies, 3).get("result").unwrap();
    assert_eq!(
        declaration.get("uri").and_then(Json::string),
        Some(generator_uri.as_str())
    );
    assert_eq!(
        declaration
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("character")
            .and_then(Json::integer),
        Some(
            generator_source
                .lines()
                .nth(1)
                .unwrap()
                .find("emit")
                .unwrap() as i64
        )
    );
    assert_eq!(std::fs::read_to_string(&entry).unwrap(), ")");
    assert_eq!(std::fs::read_to_string(&generator).unwrap(), ")");
    assert!(!child.exists());
    // A subsequent session must not inherit scoped buffers.
    let mut messages = start();
    messages.push(open(&uri, 1, child_source));
    messages.push(definition(2, &uri, child_source, "@"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(reply(&replies, 2).get("result"), Some(&Json::Null));
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn generator_name_resolves_original_span_through_external_prefixes_and_duplicate_imports() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-prefix-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let entry = base.join("main.lim");
    let child = base.join("child.lim");
    // The same source is loaded under two prefixes; its name token has two
    // semantic names, both referring to exactly the same declaration span.
    let source = "(#import-external \"child.lim\" a-) (#import-external \"child.lim\" b-)";
    std::fs::write(&entry, source).unwrap();
    lim::lsp_context::LspContext {
        entry: entry.clone(),
        config: CompileConfig::default(),
        target: lim::TargetDescription::X86_64_SYSTEM_V,
    }
    .write(&base.join("lim.lsp"))
    .unwrap();
    let child_source =
        "; unsaved generator\n(#gn emit (name) `((#type ,name #u64)))\n(@emit Number)";
    let uri = lsp::path_to_uri(&child).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, child_source));
    messages.push(definition(2, &uri, child_source, "emit Number"));
    messages.push(definition(3, &uri, child_source, "@"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let declaration = reply(&replies, 2).get("result").unwrap();
    assert_eq!(
        declaration.get("uri").and_then(Json::string),
        Some(uri.as_str())
    );
    assert_eq!(
        declaration
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("line")
            .and_then(Json::integer),
        Some(1)
    );
    assert_eq!(
        declaration
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("character")
            .and_then(Json::integer),
        Some(5)
    );
    let paths = artifact_paths(&replies, 3);
    let contents = paths
        .iter()
        .map(|path| std::fs::read_to_string(path).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(contents.contains("a-Number"), "{contents}");
    assert!(contents.contains("b-Number"), "{contents}");
    assert!(!child.exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn builtin_macro_at_navigates_but_builtin_name_and_noninvocations_do_not() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-builtin-{}", std::process::id()));
    let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
    let source = "(@#optional (: type #u64 : name Maybe))";
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(definition(2, &uri, source, "#optional"));
    messages.push(definition(3, &uri, source, "@"));
    messages.push(definition(4, &uri, source, "Maybe"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(reply(&replies, 2).get("result"), Some(&Json::Null));
    assert_eq!(reply(&replies, 4).get("result"), Some(&Json::Null));
    assert!(artifact_paths(&replies, 3)
        .iter()
        .any(|path| std::fs::read_to_string(path)
            .unwrap()
            .contains("Maybe-construct")));
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn imported_generator_name_navigation_needs_no_valid_expansion_or_artifacts() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-name-only-{}", std::process::id()));
    let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
    let generator_uri = lsp::path_to_uri(&base.join("generator.lim")).unwrap();
    let source = "(#import-external \"generator.lim\" ext-)\n(@ext-emit)";
    let generator = "; unsaved\n(#gn emit () (#gn-error \"not implemented\"))";
    let mut messages = start();
    messages.push(open(&generator_uri, 1, generator));
    messages.push(open(&uri, 1, source));
    messages.push(definition(2, &uri, source, "ext-emit"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let declaration = reply(&replies, 2).get("result").unwrap();
    assert_eq!(
        declaration.get("uri").and_then(Json::string),
        Some(generator_uri.as_str())
    );
    assert_eq!(
        declaration
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("line")
            .and_then(Json::integer),
        Some(1)
    );
    assert_eq!(
        declaration
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("character")
            .and_then(Json::integer),
        Some(5)
    );
    assert!(!base.exists(), "declaration navigation created artifacts");
}

#[test]
fn macro_navigation_returns_no_artifact_for_inactive_invalid_or_quoted_calls() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-invalid-{}", std::process::id()));
    let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
    for source in [
        "(#gn emit () `((#type Number #u64))) (#cfg-if (#cfg-is #feature never-enabled) (@emit))",
        "(#gn bad () `((#fn broken () #u64 (#return false)))) (@bad)",
        "(#gn bad () (#gn-error \"failed\")) (@bad)",
        "(#gn template () `((@missing)))",
        "(@unknown)",
    ] {
        let mut messages = start();
        messages.push(open(&uri, 1, source));
        messages.push(definition(2, &uri, source, "@"));
        finish(&mut messages);
        let (_, replies) = session(messages);
        assert_eq!(
            reply(&replies, 2).get("result"),
            Some(&Json::Null),
            "{source}"
        );
    }
    // The API may create its publication directory while validating, but
    // failed/inactive invocations must never yield navigable targets.
    if base.exists() {
        std::fs::remove_dir_all(base).unwrap();
    }
}

#[test]
fn import_paths_and_imported_functions_and_types_are_navigable_with_type_errors() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-import-navigation-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let root = base.join("main.lim");
    let child = base.join("child.lim");
    let text = "(#import \"child.lim\")\n(#import-external \"child.lim\" ext-)\n(#fn main () #u64 (#let value ext-Number 42u64) (#return (#call ext-read (: ext-value value))))\n(#fn broken () #u64 (#return #true))\n(#struct Holder () ((field Number)))\n(#enum Choice () ((Present Number) (Absent ())))";
    let imported = "(#type Number #u64)\n(#fn read ((value Number)) #u64 (#return value))";
    std::fs::write(&root, text).unwrap();
    std::fs::write(&child, imported).unwrap();
    let uri = lsp::path_to_uri(&root).unwrap();
    let child_uri = lsp::path_to_uri(&child).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, text));
    for (id, needle) in [
        (2, "child.lim"),
        (3, "#import-external"),
        (4, "ext-read"),
        (5, "ext-Number"),
    ] {
        messages.push(definition(id, &uri, text, needle));
    }
    messages.push(definition(6, &uri, text, "ext-)"));
    messages.push(definition(7, &uri, text, "Number)))"));
    messages.push(definition(8, &uri, text, "Number) (Absent"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    for id in [2, 3, 4, 5, 7, 8] {
        let result = reply(&replies, id).get("result").unwrap();
        assert_eq!(
            result.get("uri").and_then(Json::string),
            Some(child_uri.as_str()),
            "{id}: {result:?}"
        );
    }
    let result = reply(&replies, 4).get("result").unwrap();
    assert_eq!(
        result
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("line")
            .and_then(Json::integer),
        Some(1)
    );
    assert_eq!(
        result
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("character")
            .and_then(Json::integer),
        Some(5)
    );
    assert_eq!(reply(&replies, 6).get("result"), Some(&Json::Null));
    assert!(!base.join(".lim").exists());
}

#[test]
fn external_import_internal_calls_and_types_use_the_compilation_names() {
    let base = std::env::temp_dir().join(format!(
        "lim-lsp-prefixed-navigation-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&base).unwrap();
    let root = base.join("main.lim");
    let child = base.join("child.lim");
    let text = "(#cfg-if (#cfg-is #os linux)\n(#type Number #u64)\n(#fn read () Number (#return 42u64))\n(#fn invoke () Number (#return (#call read ()))))";
    std::fs::write(&root, "(#import-external \"child.lim\" first-)\n(#import-external \"child.lim\" second-)\n(#fn main () #u64 (#return (#call first-invoke ())))").unwrap();
    std::fs::write(&child, text).unwrap();
    lim::lsp_context::LspContext {
        entry: root,
        target: lim::TargetDescription::X86_64_SYSTEM_V,
        config: CompileConfig::default(),
    }
    .write(&base.join("lim.lsp"))
    .unwrap();
    let uri = lsp::path_to_uri(&child).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, text));
    messages.push(definition(2, &uri, text, "Number (#return 42u64)"));
    messages.push(definition(3, &uri, text, "read ())))"));
    messages.push(definition(4, &uri, text, "Number (#return (#call"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    for (id, line) in [(2, 1), (3, 2), (4, 1)] {
        let result = reply(&replies, id).get("result").unwrap();
        assert_eq!(result.get("uri").and_then(Json::string), Some(uri.as_str()));
        assert_eq!(
            result
                .get("range")
                .unwrap()
                .get("start")
                .unwrap()
                .get("line")
                .and_then(Json::integer),
            Some(line)
        );
    }
}

#[test]
fn import_navigation_respects_module_paths_local_precedence_and_unsaved_sources() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-module-navigation-{}", std::process::id()));
    let modules = base.join("modules");
    std::fs::create_dir_all(&modules).unwrap();
    let root = base.join("main.lim");
    let unsaved = base.join("unsaved.lim");
    let local = base.join("local.lim");
    let shared = modules.join("shared.lim");
    let text = "(#import \"shared.lim\")\n(#import \"local.lim\")\n(#import \"unsaved.lim\")\n(#fn main () #u64 (#return (#call unsaved-value ())))";
    std::fs::write(&root, text).unwrap();
    std::fs::write(&local, "(#type Local #u64)").unwrap();
    std::fs::write(modules.join("local.lim"), "(#type Other #bool)").unwrap();
    std::fs::write(&shared, "(#type Shared #u64)").unwrap();
    let mut config = CompileConfig::default();
    config.add_module_path(modules);
    lim::lsp_context::LspContext {
        entry: root.clone(),
        target: lim::TargetDescription::X86_64_SYSTEM_V,
        config,
    }
    .write(&base.join("lim.lsp"))
    .unwrap();
    let uri = lsp::path_to_uri(&root).unwrap();
    let unsaved_uri = lsp::path_to_uri(&unsaved).unwrap();
    let mut messages = start();
    messages.push(open(
        &unsaved_uri,
        1,
        "(#fn unsaved-value () #u64 (#return 42u64))",
    ));
    messages.push(open(&uri, 1, text));
    for (id, needle) in [
        (2, "shared.lim"),
        (3, "local.lim"),
        (4, "unsaved.lim"),
        (5, "unsaved-value"),
    ] {
        messages.push(definition(id, &uri, text, needle));
    }
    finish(&mut messages);
    let (_, replies) = session(messages);
    for (id, path) in [(2, shared), (3, local), (4, unsaved.clone()), (5, unsaved)] {
        assert_eq!(
            reply(&replies, id)
                .get("result")
                .unwrap()
                .get("uri")
                .and_then(Json::string),
            lsp::path_to_uri(&path).as_deref(),
            "{id}"
        );
    }
}

#[test]
fn navigation_resolves_real_async_example_imported_calls() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let base = std::env::temp_dir().join(format!(
        "lim-lsp-real-import-navigation-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&base).unwrap();
    let entry = base.join("main.lim");
    let text = std::fs::read_to_string(root.join("examples/async_fn.lim"))
        .unwrap()
        .replace("../library/", &format!("{}/library/", root.display()));
    std::fs::write(&entry, &text).unwrap();
    lim::lsp_context::LspContext {
        entry: entry.clone(),
        target: lim::TargetDescription::X86_64_SYSTEM_V,
        config: CompileConfig::default(),
    }
    .write(&base.join("lim.lsp"))
    .unwrap();
    let uri = lsp::path_to_uri(&entry).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, &text));
    messages.push(definition(2, &uri, &text, "linux-write-byte"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let result = reply(&replies, 2).get("result").unwrap();
    assert_eq!(
        result.get("uri").and_then(Json::string),
        lsp::path_to_uri(&root.join("library/linux_x86_64.lim")).as_deref(),
        "{replies:?}"
    );
    let imported = std::fs::read_to_string(root.join("library/linux_x86_64.lim")).unwrap();
    let (line, character) =
        lsp::byte_position(&imported, imported.find("linux-write-byte").unwrap());
    let start = result.get("range").unwrap().get("start").unwrap();
    assert_eq!(start.get("line").and_then(Json::integer), Some(line as i64));
    assert_eq!(
        start.get("character").and_then(Json::integer),
        Some(character as i64)
    );
}

#[test]
fn missing_and_quoted_imports_do_not_invent_definition_targets() {
    let uri = "file:///tmp/lim-lsp-missing-import-navigation.lim";
    let text = "(#import \"does-not-exist-743198.lim\")\n'(#import \"quoted.lim\")";
    let mut messages = start();
    messages.push(open(uri, 1, text));
    messages.push(definition(2, uri, text, "does-not-exist"));
    messages.push(definition(3, uri, text, "quoted.lim"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(reply(&replies, 2).get("result"), Some(&Json::Null));
    assert_eq!(reply(&replies, 3).get("result"), Some(&Json::Null));
}

#[test]
fn lifecycle_and_protocol_only_output() {
    let mut messages = vec![request(0, "textDocument/documentSymbol", "{}")];
    messages.extend(start());
    messages.push(request(2, "initialize", "{}"));
    finish(&mut messages);
    messages.insert(messages.len() - 1, request(100, "anything", "{}"));
    let (code, replies) = session(messages);
    assert_eq!(code, 0);
    assert_eq!(
        reply(&replies, 0)
            .get("error")
            .unwrap()
            .get("code")
            .unwrap()
            .integer(),
        Some(-32002)
    );
    assert_eq!(
        reply(&replies, 2)
            .get("error")
            .unwrap()
            .get("code")
            .unwrap()
            .integer(),
        Some(-32600)
    );
    assert_eq!(
        reply(&replies, 100)
            .get("error")
            .unwrap()
            .get("code")
            .unwrap()
            .integer(),
        Some(-32600)
    );
    assert_eq!(reply(&replies, 99).get("result"), Some(&Json::Null));
    assert_eq!(session(vec![notify("exit", "null")]).0, 1);
    assert_eq!(session(start()).0, 1);
}

#[test]
fn unsaved_diagnostics_versions_save_and_close_clear() {
    let uri = "file:///tmp/lim-lsp-unsaved-test.lim";
    let mut messages = start();
    messages.push(open(uri, 1, ")"));
    messages.push(change(uri, 1, "")); // stale, must be ignored
    messages.push(change(uri, 2, ""));
    messages.push(notify(
        "textDocument/didSave",
        &format!(
            "{{\"textDocument\":{{\"uri\":{}}},\"text\":\")\"}}",
            diagnostic_json::quoted(uri)
        ),
    ));
    messages.push(notify("textDocument/didClose", &document(uri)));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let p = publications(&replies);
    assert_eq!(p.len(), 4);
    assert_eq!(p[0].get("diagnostics").unwrap().array().unwrap().len(), 1);
    assert_eq!(p[0].get("version").unwrap().integer(), Some(1));
    assert_eq!(p[1].get("diagnostics").unwrap().array().unwrap().len(), 0);
    assert_eq!(p[1].get("version").unwrap().integer(), Some(2));
    assert_eq!(p[2].get("diagnostics").unwrap().array().unwrap().len(), 1);
    assert_eq!(p[3].get("diagnostics").unwrap().array().unwrap().len(), 0);
    assert!(p[3].get("version").is_none());
    assert!(!Path::new("/tmp/lim-lsp-unsaved-test.lim").exists());
}

#[test]
fn utf16_emoji_diagnostics_and_formatting() {
    assert_eq!(lsp::byte_position("a😀z\r\nβ", 5), (0, 3));
    assert_eq!(lsp::byte_position("a😀z\r\nβ", 8), (1, 0));
    let uri = "file:///tmp/lim-lsp-emoji.lim";
    let mut messages = start();
    messages.push(open(uri, 1, "\"😀\" )"));
    messages.push(change(uri, 2, "(#fn main () #u64 (#return 0u64))"));
    messages.push(request(2,"textDocument/formatting", &format!("{{\"textDocument\":{{\"uri\":{}}},\"options\":{{\"tabSize\":2,\"insertSpaces\":true}}}}",diagnostic_json::quoted(uri))));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let d = publications(&replies)[0]
        .get("diagnostics")
        .unwrap()
        .array()
        .unwrap();
    assert_eq!(
        d[0].get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("character")
            .unwrap()
            .integer(),
        Some(5)
    );
    let edit = &reply(&replies, 2).get("result").unwrap().array().unwrap()[0];
    assert_eq!(
        edit.get("newText").unwrap().string().unwrap(),
        format_source("(#fn main () #u64 (#return 0u64))").unwrap()
    );
}

#[test]
fn symbols_and_definition_only_on_declaration_names() {
    let uri = "file:///tmp/lim-lsp-symbols.lim";
    let text = "(#fn main () #u64 (#return 0u64))\n(#struct Point () ())";
    let mut messages = start();
    messages.push(open(uri, 1, text));
    messages.push(request(2, "textDocument/documentSymbol", &document(uri)));
    for (id, character) in [(3, 5), (4, 26)] {
        messages.push(request(id,"textDocument/definition",&format!("{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":0,\"character\":{character}}}}}",diagnostic_json::quoted(uri))));
    }
    finish(&mut messages);
    let (_, replies) = session(messages);
    let symbols = reply(&replies, 2).get("result").unwrap().array().unwrap();
    assert_eq!(symbols.len(), 2);
    assert_eq!(symbols[0].get("name").unwrap().string(), Some("main"));
    assert_eq!(
        reply(&replies, 3)
            .get("result")
            .unwrap()
            .get("uri")
            .unwrap()
            .string(),
        Some(uri)
    );
    assert_eq!(reply(&replies, 4).get("result"), Some(&Json::Null));
}

#[test]
fn explicit_call_roles_resolve_unique_functions_but_not_fields_or_templates() {
    let uri = "file:///tmp/lim-lsp-calls.lim";
    let source = "(#fn target () #u64 (#return 0u64))\n(#fn main () #u64 (#return (#call target (:))))\n(#struct Holder () ((target #u64)))\n'(#call target (:))";
    let mut messages = start();
    messages.push(open(uri, 1, source));
    for (id, line, character) in [(2, 1, 34), (3, 2, 18), (4, 3, 8)] {
        messages.push(request(id,"textDocument/definition", &format!("{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}",diagnostic_json::quoted(uri))));
    }
    messages.push(change(
        uri,
        2,
        &format!("{source}\n(#fn target () #u64 (#return 1u64))"),
    ));
    messages.push(request(
        5,
        "textDocument/definition",
        &format!(
            "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":1,\"character\":34}}}}",
            diagnostic_json::quoted(uri)
        ),
    ));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let target = reply(&replies, 2).get("result").unwrap();
    assert_eq!(target.get("uri").unwrap().string(), Some(uri));
    assert_eq!(
        target
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("line")
            .unwrap()
            .integer(),
        Some(0)
    );
    for id in [3, 4, 5] {
        assert_eq!(reply(&replies, id).get("result"), Some(&Json::Null));
    }
}

#[test]
fn generated_function_definition_publishes_an_exact_source_snapshot() {
    let base = std::env::temp_dir().join(format!("lim-lsp-generated-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let path = base.join("main.lim");
    let uri = format!("file://{}", path.display());
    let source = "(@#optional (: type #u64 : name Maybe))\n(#fn main () () (#let value Maybe (#call Maybe-construct (: value 42u64))) (#forget value) (#return ()))";
    let character = source
        .lines()
        .nth(1)
        .unwrap()
        .find("Maybe-construct")
        .unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(request(2, "textDocument/definition", &format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":1,\"character\":{character}}}}}", diagnostic_json::quoted(&uri))));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let result = reply(&replies, 2).get("result").unwrap();
    let target = lsp::uri_to_path(result.get("uri").unwrap().string().unwrap()).unwrap();
    assert!(target.starts_with(base.join(".lim/generated")));
    let generated = std::fs::read_to_string(&target).unwrap();
    assert!(generated.contains("Maybe-construct"));
    let range_start = result.get("range").unwrap().get("start").unwrap();
    let line = range_start.get("line").unwrap().integer().unwrap() as usize;
    let column = range_start.get("character").unwrap().integer().unwrap() as usize;
    assert!(generated.lines().nth(line).unwrap()[column..].starts_with("Maybe-construct"));
    assert!(!base.join(".lim/cache").exists());
    let modified = std::fs::metadata(&target).unwrap().modified().unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(request(2, "textDocument/definition", &format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":1,\"character\":{character}}}}}", diagnostic_json::quoted(&uri))));
    finish(&mut messages);
    let (_, repeated) = session(messages.clone());
    assert_eq!(reply(&repeated, 2).get("result"), Some(result));
    assert_eq!(
        std::fs::metadata(&target).unwrap().modified().unwrap(),
        modified
    );
    std::fs::write(&target, "; user-edited snapshot\n").unwrap();
    let (_, corrupt) = session(messages);
    assert_eq!(reply(&corrupt, 2).get("result"), Some(&Json::Null));
    assert_eq!(
        std::fs::read_to_string(&target).unwrap(),
        "; user-edited snapshot\n"
    );
    // Restore the fixture for repeatable reruns, not navigation publication.
    std::fs::write(&target, generated).unwrap();
}

#[test]
fn generated_type_navigation_tracks_unsaved_generator_changes() {
    let base = std::env::temp_dir().join(format!("lim-lsp-generated-type-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let uri = format!("file://{}", base.join("main.lim").display());
    let source = "(#gn emit (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64)))\n(@emit Number)\n(#fn main () Number (#return 42u64))";
    let position = source.lines().nth(2).unwrap().find("Number").unwrap();
    let params = format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":2,\"character\":{position}}}}}",
        diagnostic_json::quoted(&uri)
    );
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(request(2, "textDocument/definition", &params));
    messages.push(request(3, "textDocument/definition", &params));
    messages.push(change(
        &uri,
        2,
        &source.replace("#u64", "#u32").replace("42u64", "42u32"),
    ));
    messages.push(request(4, "textDocument/definition", &params));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let first = reply(&replies, 2).get("result").unwrap();
    assert_eq!(first, reply(&replies, 3).get("result").unwrap());
    let next = reply(&replies, 4).get("result").unwrap();
    assert_ne!(first, next);
    for (result, ty) in [(first, "#u64"), (next, "#u32")] {
        let path = lsp::uri_to_path(result.get("uri").unwrap().string().unwrap()).unwrap();
        let text = std::fs::read_to_string(path).unwrap();
        assert!(text.contains(&format!("(#type Number {ty})")));
        let start = result.get("range").unwrap().get("start").unwrap();
        let line = start.get("line").unwrap().integer().unwrap() as usize;
        let col = start.get("character").unwrap().integer().unwrap() as usize;
        assert!(text.lines().nth(line).unwrap()[col..].starts_with("Number"));
    }
    assert!(!base.join("main.lim").exists());
    assert!(!base.join(".lim/cache").exists());
}

#[test]
fn generated_definition_uses_unsaved_imports_and_rejects_invalid_expansions() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-generated-import-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let uri = format!("file://{}", base.join("main.lim").display());
    let imported_uri = format!("file://{}", base.join("types.lim").display());
    let source = "(#import \"types.lim\")\n(#fn main () Number (#return 42u64))";
    let imported =
        "(#gn emit (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64))) (@emit Number)";
    let character = source.lines().nth(1).unwrap().find("Number").unwrap();
    let params = format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":1,\"character\":{character}}}}}",
        diagnostic_json::quoted(&uri)
    );
    let mut messages = start();
    messages.push(open(&imported_uri, 1, imported));
    messages.push(open(&uri, 1, source));
    messages.push(request(2, "textDocument/definition", &params));
    messages.push(change(
        &imported_uri,
        2,
        &imported.replace("#u64", "MissingType"),
    ));
    messages.push(request(3, "textDocument/definition", &params));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let result = reply(&replies, 2).get("result").unwrap();
    let target = lsp::uri_to_path(result.get("uri").unwrap().string().unwrap()).unwrap();
    let text = std::fs::read_to_string(target).unwrap();
    assert!(text.contains(&format!("{}:1", base.join("types.lim").display())));
    assert_eq!(reply(&replies, 3).get("result"), Some(&Json::Null));
    assert!(!base.join("types.lim").exists());
}

#[test]
fn compilation_context_resolves_entry_symbols_from_an_unsaved_external_module() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-entry-navigation-{}", std::process::id()));
    let external =
        std::env::temp_dir().join(format!("lim-lsp-entry-external-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    std::fs::create_dir_all(&external).unwrap();
    let entry = base.join("main.lim");
    let child = external.join("child.lim");
    std::fs::write(&entry, format!("(#type Number #u64)\n(#fn target () Number (#return 42u64))\n(#import {})\n(@#optional (: type #u64 : name Maybe))\n(#fn main () Number (#return (#call child ())))", diagnostic_json::quoted(child.to_str().unwrap()))).unwrap();
    lim::lsp_context::LspContext {
        entry: entry.clone(),
        target: lim::TargetDescription::X86_64_SYSTEM_V,
        config: CompileConfig::default(),
    }
    .write(&base.join("lim.lsp"))
    .unwrap();
    let uri = format!("file://{}", child.display());
    let root = format!("file://{}", base.display());
    let source = "(#fn child () Number (#return (#call target ()))) (#fn wrap () Maybe (#return (#call Maybe-construct (: value 42u64))))";
    let mut messages = vec![request(1, "initialize", &format!("{{\"rootUri\":{},\"capabilities\":{{\"workspace\":{{\"didChangeWatchedFiles\":{{\"dynamicRegistration\":true}}}}}}}}", diagnostic_json::quoted(&root))), notify("initialized", "{}")];
    messages.push("{\"jsonrpc\":\"2.0\",\"id\":\"lim-context-watch\",\"result\":null}".into());
    messages.push(open(&uri, 1, source));
    for (id, symbol) in [(2, "target"), (3, "Number"), (4, "Maybe-construct")] {
        let character = source.find(symbol).unwrap();
        messages.push(request(id, "textDocument/definition", &format!("{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":0,\"character\":{character}}}}}", diagnostic_json::quoted(&uri))));
    }
    messages.push(notify(
        "workspace/didChangeWatchedFiles",
        &format!(
            "{{\"changes\":[{{\"uri\":{},\"type\":2}}]}}",
            diagnostic_json::quoted(&format!("file://{}", base.join("lim.lsp").display()))
        ),
    ));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert!(replies
        .iter()
        .any(|r| r.get("method").and_then(Json::string) == Some("client/registerCapability")));
    for id in [2, 3] {
        assert_eq!(
            reply(&replies, id)
                .get("result")
                .unwrap()
                .get("uri")
                .unwrap()
                .string(),
            Some(format!("file://{}", entry.display()).as_str())
        );
    }
    for report in replies.iter().filter(|r| {
        r.get("method").and_then(Json::string) == Some("textDocument/publishDiagnostics")
    }) {
        assert!(report
            .get("params")
            .unwrap()
            .get("diagnostics")
            .unwrap()
            .array()
            .unwrap()
            .is_empty());
    }
    assert!(!child.exists());
    assert!(!base.join(".lim").exists());
    let generated_uri = reply(&replies, 4)
        .get("result")
        .unwrap()
        .get("uri")
        .unwrap()
        .string()
        .unwrap();
    let generated_path = lsp::uri_to_path(generated_uri).unwrap();
    let generated = std::fs::read_to_string(generated_path).unwrap();
    let mut messages = vec![
        request(
            1,
            "initialize",
            &format!("{{\"rootUri\":{}}}", diagnostic_json::quoted(&root)),
        ),
        notify("initialized", "{}"),
    ];
    messages.push(open(&uri, 1, source));
    messages.push(open(generated_uri, 1, &generated));
    finish(&mut messages);
    let (_, replies) = session(messages);
    for report in replies.iter().filter(|r| {
        r.get("method").and_then(Json::string) == Some("textDocument/publishDiagnostics")
    }) {
        assert!(report
            .get("params")
            .unwrap()
            .get("diagnostics")
            .unwrap()
            .array()
            .unwrap()
            .is_empty());
    }
}

#[test]
fn watched_context_switch_rechecks_open_documents_without_buffer_changes() {
    struct SwitchingInput {
        input: Cursor<Vec<u8>>,
        boundary: u64,
        replacement: Option<(std::path::PathBuf, String)>,
    }
    impl SwitchingInput {
        fn update(&mut self) {
            if self.input.position() >= self.boundary {
                if let Some((path, text)) = self.replacement.take() {
                    std::fs::write(path, text).unwrap();
                }
            }
        }
    }
    impl std::io::Read for SwitchingInput {
        fn read(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
            self.update();
            std::io::Read::read(&mut self.input, buffer)
        }
    }
    impl std::io::BufRead for SwitchingInput {
        fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
            self.update();
            std::io::BufRead::fill_buf(&mut self.input)
        }
        fn consume(&mut self, amount: usize) {
            std::io::BufRead::consume(&mut self.input, amount);
        }
    }
    let base = std::env::temp_dir().join(format!("lim-lsp-watch-context-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let entry = base.join("main.lim");
    let source = "(#cfg-if (#cfg-is #feature good) (#type Number #u64) (#cfg-else (#type Number #bool))) (#import \"child.lim\") (#fn main () #u64 (#return 0u64))";
    std::fs::write(&entry, source).unwrap();
    let mut config = CompileConfig::default();
    config.set("feature", "good");
    let path = base.join("lim.lsp");
    lim::lsp_context::LspContext {
        entry,
        config,
        target: lim::TargetDescription::X86_64_SYSTEM_V,
    }
    .write(&path)
    .unwrap();
    let replacement = std::fs::read_to_string(&path)
        .unwrap()
        .replace("feature=good", "feature=bad");
    let uri = format!("file://{}", base.join("child.lim").display());
    let mut input = Vec::new();
    for message in
        start()
            .into_iter()
            .chain([open(&uri, 1, "(#fn child () Number (#return 42u64))")])
    {
        json::write_frame(&mut input, &message).unwrap();
    }
    let boundary = input.len() as u64;
    let mut messages = vec![notify(
        "workspace/didChangeWatchedFiles",
        &format!(
            "{{\"changes\":[{{\"uri\":{},\"type\":2}}]}}",
            diagnostic_json::quoted(&format!("file://{}", path.display()))
        ),
    )];
    finish(&mut messages);
    for message in messages {
        json::write_frame(&mut input, &message).unwrap();
    }
    let mut output = Vec::new();
    lsp::serve(
        SwitchingInput {
            input: Cursor::new(input),
            boundary,
            replacement: Some((path, replacement)),
        },
        &mut output,
        &CompileConfig::default(),
    )
    .unwrap();
    let mut output = Cursor::new(output);
    let mut lengths = Vec::new();
    while let Some(body) = json::read_frame(&mut output).unwrap() {
        let response = json::parse(&body).unwrap();
        if response.get("method").and_then(Json::string) == Some("textDocument/publishDiagnostics")
        {
            lengths.push(
                response
                    .get("params")
                    .unwrap()
                    .get("diagnostics")
                    .unwrap()
                    .array()
                    .unwrap()
                    .len(),
            );
        }
    }
    assert_eq!(lengths.first(), Some(&0));
    assert!(lengths.iter().any(|length| *length > 0));
}

#[test]
fn unknown_methods_invalid_types_and_json_recover() {
    let mut messages = start();
    messages.extend([
        request(2, "made/up", "{}"),
        notify("made/up", "{}"),
        "{broken".into(),
        "{\"jsonrpc\":\"2.0\",\"id\":true,\"method\":\"x\"}".into(),
        request(
            3,
            "textDocument/definition",
            "{\"textDocument\":{\"uri\":false},\"position\":{\"line\":0,\"character\":0}}",
        ),
    ]);
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(
        reply(&replies, 2)
            .get("error")
            .unwrap()
            .get("code")
            .unwrap()
            .integer(),
        Some(-32601)
    );
    assert_eq!(
        reply(&replies, 3)
            .get("error")
            .unwrap()
            .get("code")
            .unwrap()
            .integer(),
        Some(-32602)
    );
    assert!(replies.iter().any(|m| m
        .get("error")
        .and_then(|e| e.get("code"))
        .and_then(Json::integer)
        == Some(-32700)));
    assert!(replies.iter().any(|m| m
        .get("error")
        .and_then(|e| e.get("code"))
        .and_then(Json::integer)
        == Some(-32600)));
}

#[test]
fn bounded_json_types_and_unicode() {
    for value in [
        "null",
        "true",
        "false",
        "-12",
        "1.25e+3",
        "\"\\ud83d\\ude00\"",
        "{\"a\":[1,false,null,\"é\"]}",
    ] {
        let parsed = json::parse(value).unwrap();
        assert_eq!(json::parse(&parsed.render()).unwrap(), parsed);
    }
    assert_eq!(
        json::parse("\"\\ud83d\\ude00\"").unwrap().string(),
        Some("😀")
    );
    for bad in [
        "01",
        "-",
        "1.",
        "1e+-2",
        "1e999",
        "[1,]",
        "{\"a\":1,\"a\":2}",
        "\"\\ud800\"",
        "\"\\udc00\"",
        "\"\n\"",
        "true false",
    ] {
        assert!(json::parse(bad).is_err(), "{bad}");
    }
    assert!(json::parse(&format!("{}0{}", "[".repeat(66), "]".repeat(66))).is_err());
}

#[test]
fn malformed_and_bounded_framing() {
    for bad in [
        "Content-Length: x\r\n\r\n",
        "Content-Length: -1\r\n\r\n",
        "Content-Length: 8388609\r\n\r\n",
        "Content-Length: 2\r\nContent-Length: 2\r\n\r\n{}",
        "Content-Length: 2\n\n{}",
        "X: a\r\n\r\n{}",
        "Content-Length: 2\r\n\r\n{",
        "Content-Length: 99999999999999999999999\r\n\r\n",
    ] {
        assert!(
            json::read_frame(&mut Cursor::new(bad.as_bytes())).is_err(),
            "{bad}"
        );
    }
    assert!(json::read_frame(&mut Cursor::new(vec![b'x'; 9000])).is_err());
    let mut bytes = Vec::new();
    json::write_frame(&mut bytes, "\"😀\"").unwrap();
    assert_eq!(
        json::read_frame(&mut Cursor::new(bytes))
            .unwrap()
            .as_deref(),
        Some("\"😀\"")
    );
}

#[test]
fn local_file_uri_roundtrip_and_malformed_escapes() {
    let path = Path::new("/tmp/a b😀#%.lim");
    let uri = lsp::path_to_uri(path).unwrap();
    assert_eq!(lsp::uri_to_path(&uri).as_deref(), Some(path));
    assert_eq!(
        lsp::uri_to_path("file://localhost/tmp/a").as_deref(),
        Some(Path::new("/tmp/a"))
    );
    for bad in [
        "untitled:a",
        "file://remote/tmp/a",
        "file:///tmp/%",
        "file:///tmp/%xz",
        "file:///tmp/%ff",
        "file:///tmp/%00",
        "file:///tmp/a?query",
    ] {
        assert!(lsp::uri_to_path(bad).is_none(), "{bad}");
    }
}

#[test]
fn unsaved_import_overlays_recheck_importers_and_clear() {
    let root = "file:///tmp/lim-lsp-overlay/root.lim";
    let child = "file:///tmp/lim-lsp-overlay/child.lim";
    let mut messages = start();
    messages.push(open(child, 1, ""));
    messages.push(open(root, 1, "(#import \"child.lim\")"));
    messages.push(change(child, 2, ")"));
    messages.push(change(child, 3, ""));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let p = publications(&replies);
    assert!(p
        .iter()
        .any(|p| p.get("uri").unwrap().string() == Some(child)
            && !p.get("diagnostics").unwrap().array().unwrap().is_empty()));
    for uri in [root, child] {
        let last = p
            .iter()
            .rev()
            .find(|p| p.get("uri").unwrap().string() == Some(uri))
            .unwrap();
        assert!(last.get("diagnostics").unwrap().array().unwrap().is_empty());
    }
    assert!(!Path::new("/tmp/lim-lsp-overlay").exists());
}

#[test]
fn binary_stdio_generated_diagnostic_maps_to_invocation_without_artifacts() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let scratch = std::env::temp_dir().join(format!("lim-lsp-artifacts-{}", std::process::id()));
    std::fs::create_dir(&scratch).unwrap();
    let uri = lsp::path_to_uri(&scratch.join("unsaved.lim")).unwrap();
    let source = "(#gn bad () `((#fn broken () #u64 (#return false))))\n(@bad)";
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    finish(&mut messages);
    let mut input = Vec::new();
    for message in messages {
        json::write_frame(&mut input, &message).unwrap();
    }
    let mut child = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("lsp")
        .current_dir(&scratch)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(&input).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut stream = Cursor::new(output.stdout);
    let mut messages = Vec::new();
    while let Some(body) = json::read_frame(&mut stream).unwrap() {
        messages.push(json::parse(&body).unwrap());
    }
    assert!(reply(&messages, 1)
        .get("result")
        .unwrap()
        .get("capabilities")
        .is_some());
    assert_eq!(reply(&messages, 99).get("result"), Some(&Json::Null));
    let published = publications(&messages);
    assert_eq!(published.len(), 1);
    assert_eq!(
        published[0].get("uri").unwrap().string(),
        Some(uri.as_str())
    );
    let diagnostics = published[0].get("diagnostics").unwrap().array().unwrap();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0]
            .get("range")
            .unwrap()
            .get("start")
            .unwrap()
            .get("line")
            .unwrap()
            .integer(),
        Some(1)
    );
    assert!(!diagnostics[0]
        .get("relatedInformation")
        .unwrap()
        .array()
        .unwrap()
        .is_empty());
    assert_eq!(
        std::fs::read_dir(&scratch).unwrap().count(),
        0,
        "check created artifacts or saved a buffer"
    );
    std::fs::remove_dir(&scratch).unwrap();
}

#[cfg(unix)]
#[test]
fn symlinked_paths_share_overlays_for_existing_and_new_imports() {
    use std::os::unix::fs::symlink;
    let scratch = std::env::temp_dir().join(format!("lim-lsp-symlinks-{}", std::process::id()));
    std::fs::create_dir(&scratch).unwrap();
    let real = scratch.join("real");
    let alias = scratch.join("alias");
    std::fs::create_dir(&real).unwrap();
    symlink(&real, &alias).unwrap();
    let root_path = real.join("root.lim");
    // On-disk fixture content must be shadowed by the editor buffer.
    std::fs::write(&root_path, ")").unwrap();
    let root_uri = lsp::path_to_uri(&alias.join("root.lim")).unwrap();
    let child_uri = lsp::path_to_uri(&alias.join("child.lim")).unwrap();
    assert_eq!(lsp::uri_to_path(&root_uri), Some(root_path.clone()));
    assert_eq!(lsp::uri_to_path(&child_uri), Some(real.join("child.lim")));
    let mut messages = start();
    messages.push(open(&child_uri, 1, ""));
    messages.push(open(&root_uri, 1, "(#import \"child.lim\")"));
    messages.push(change(&child_uri, 2, ")"));
    messages.push(change(&child_uri, 3, ""));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let p = publications(&replies);
    let root = p
        .iter()
        .rev()
        .find(|p| p.get("uri").unwrap().string() == Some(&root_uri))
        .unwrap();
    assert!(root.get("diagnostics").unwrap().array().unwrap().is_empty());
    assert!(p
        .iter()
        .any(|p| p.get("uri").unwrap().string() == Some(&child_uri)
            && !p.get("diagnostics").unwrap().array().unwrap().is_empty()));
    assert_eq!(std::fs::read_to_string(&root_path).unwrap(), ")");
    assert!(!real.join("child.lim").exists());
    assert_eq!(std::fs::read_dir(&real).unwrap().count(), 1);
    std::fs::remove_file(&root_path).unwrap();
    std::fs::remove_file(&alias).unwrap();
    std::fs::remove_dir(&real).unwrap();
    std::fs::remove_dir(&scratch).unwrap();
}

#[test]
fn malformed_full_changes_are_atomic_and_preserve_versions() {
    let uri = "file:///tmp/lim-lsp-atomic.lim";
    let mut messages = start();
    messages.push(open(uri, 1, ")"));
    for changes in [
        "[{\"text\":\"\"},{\"text\":false}]",
        "[{\"range\":{},\"text\":\"\"}]",
        "[]",
    ] {
        messages.push(notify(
            "textDocument/didChange",
            &format!(
                "{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":{changes}}}",
                diagnostic_json::quoted(uri)
            ),
        ));
    }
    messages.push(change(uri, 2, ""));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let p = publications(&replies);
    assert_eq!(p.len(), 2);
    assert!(!p[0].get("diagnostics").unwrap().array().unwrap().is_empty());
    assert_eq!(p[1].get("version").unwrap().integer(), Some(2));
    assert!(p[1].get("diagnostics").unwrap().array().unwrap().is_empty());
}
