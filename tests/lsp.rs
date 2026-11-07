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

#[test]
fn proof_diagnostics_expose_typed_outcomes_to_editor_clients() {
    for (source, code, outcome) in [
        ("(#theorem wrong false)", "E4401", "counterexample"),
        (
            "(#theorem unsupported (#proof-for-all (: value #f32) true))",
            "E4402",
            "unsupported",
        ),
    ] {
        let mut messages = start();
        messages.push(open("file:///tmp/lim-proof-outcome-editor.lim", 1, source));
        finish(&mut messages);
        let (_, responses) = session(messages);
        let reports = publications(&responses);
        let diagnostic = &reports[0].get("diagnostics").unwrap().array().unwrap()[0];
        assert_eq!(diagnostic.get("code").unwrap().string(), Some(code));
        assert_eq!(
            diagnostic
                .get("data")
                .unwrap()
                .get("proof_outcome")
                .unwrap()
                .string(),
            Some(outcome)
        );
    }
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
    definition_offset(id, uri, text, needle, 0)
}

fn definition_offset(id: i64, uri: &str, text: &str, needle: &str, offset: usize) -> String {
    let byte = text.find(needle).unwrap() + offset;
    let (line, character) = lsp::byte_position(text, byte);
    request(id, "textDocument/definition", &format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}",
        diagnostic_json::quoted(uri)
    ))
}

fn assert_definition_token(location: &Json, uri: &str, source: &str, start: usize, name: &str) {
    assert_eq!(location.get("uri").and_then(Json::string), Some(uri));
    let range = location.get("range").unwrap();
    for (edge, byte) in [("start", start), ("end", start + name.len())] {
        let (line, character) = lsp::byte_position(source, byte);
        let position = range.get(edge).unwrap();
        assert_eq!(
            position.get("line").and_then(Json::integer),
            Some(line as i64),
            "{location:?}"
        );
        assert_eq!(
            position.get("character").and_then(Json::integer),
            Some(character as i64),
            "{location:?}"
        );
    }
}

#[test]
fn enum_case_variants_navigate_in_every_borrow_mode_without_binding_false_positives() {
    for (keyword, ty, read) in [
        ("#case", "Choice", "payload"),
        ("#case-ref", "(#ref Choice)", "(#deref payload)"),
        ("#case-ref-mut", "(#ref-mut Choice)", "(#deref payload)"),
        (
            "#case-pin",
            "(#pin-ref Choice)",
            "(#unsafe (#pin-read payload))",
        ),
        (
            "#case-pin-mut",
            "(#pin-ref-mut Choice)",
            "(#unsafe (#pin-read payload))",
        ),
    ] {
        let base =
            std::env::temp_dir().join(format!("lim-lsp-case-{}-{keyword}", std::process::id()));
        std::fs::create_dir_all(&base).unwrap();
        let path = base.join("main.lim");
        let uri = lsp::path_to_uri(&path).unwrap();
        let text = format!(
            "(#enum Choice () ((Choice.Full #u64) Choice.Empty))\n
          (#fn inspect (: input {ty}) #u64
            (#return (#match input
              ({keyword} (Choice.Full payload) (#when true)
                (#let answer #u64 {read}) answer)
              ({keyword} Choice.Empty 0u64)
              (#case _ 1u64))))"
        );
        lim::check_types(&lim::parse_program(&text).unwrap()).unwrap();
        let mut messages = start();
        messages.push(open(&uri, 1, &text));
        messages.push(definition_offset(
            2,
            &uri,
            &text,
            &format!("({keyword} (Choice.Full"),
            keyword.len() + 3,
        ));
        messages.push(definition_offset(
            3,
            &uri,
            &text,
            &format!("({keyword} Choice.Empty"),
            keyword.len() + 2,
        ));
        messages.push(definition_offset(
            4,
            &uri,
            &text,
            "(Choice.Full payload)",
            13,
        ));
        messages.push(definition_offset(5, &uri, &text, "(#case _", 7));
        finish(&mut messages);
        let (_, replies) = session(messages);
        for (id, name) in [(2, "Choice.Full"), (3, "Choice.Empty")] {
            let locations = definition_locations(&replies, id);
            assert_eq!(locations.len(), 1, "{keyword}: {replies:?}");
            assert_definition_token(locations[0], &uri, &text, text.find(name).unwrap(), name);
        }
        let binding = definition_locations(&replies, 4);
        assert_eq!(binding.len(), 1);
        assert_definition_token(
            binding[0],
            &uri,
            &text,
            text.find("payload").unwrap(),
            "payload",
        );
        assert_eq!(reply(&replies, 5).get("result"), Some(&Json::Null));
        std::fs::remove_dir_all(base).unwrap();
    }
}

#[test]
fn enum_case_variants_navigate_in_nested_and_or_patterns() {
    let base = std::env::temp_dir().join(format!("lim-lsp-nested-cases-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
    let text = "(#enum Color () (Color.Red Color.Green Color.Blue))
      (#enum Wrapped () ((Wrapped.Wrap Color)))
      (#fn nested (: input Wrapped) #u64 (#return (#match input
        (#case (Wrapped.Wrap inner) (#match inner (#case Color.Red 1u64) (#case _ 0u64))))))
      (#fn alternatives (: input Color) #u64 (#return (#match input
        (#case (#or Color.Red Color.Green) 42u64) (#case Color.Blue 0u64))))";
    lim::check_types(&lim::parse_program(text).unwrap()).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, text));
    for (id, needle, offset) in [
        (2, "(Wrapped.Wrap inner)", 1),
        (3, "(#case Color.Red", 7),
        (4, "#or Color.Red", 4),
        (5, "#or Color.Red Color.Green", 14),
    ] {
        messages.push(definition_offset(id, &uri, text, needle, offset));
    }
    finish(&mut messages);
    let (_, replies) = session(messages);
    for (id, name) in [
        (2, "Wrapped.Wrap"),
        (3, "Color.Red"),
        (4, "Color.Red"),
        (5, "Color.Green"),
    ] {
        let locations = definition_locations(&replies, id);
        assert_eq!(locations.len(), 1, "{replies:?}");
        let declaration = if name == "Wrapped.Wrap" {
            text.find("Wrapped.Wrap Color").unwrap()
        } else {
            text.find(name).unwrap()
        };
        assert_definition_token(locations[0], &uri, text, declaration, name);
    }
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn enum_case_variants_resolve_through_explicit_file_aliases() {
    let base = std::env::temp_dir().join(format!("lim-lsp-imported-cases-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let types = base.join("types.lim");
    let child = base.join("child.lim");
    let entry = base.join("main.lim");
    let types_text = "(#enum Choice () ((Choice.Full #u64) Choice.Empty))";
    let child_text = "(#alias Choice = ./types.lim::Choice)
      (#fn read (: input Choice) #u64 (#return (#match input
        (#case (Choice.Full payload) (#let answer #u64 payload) answer)
        (#case Choice.Empty 0u64))))";
    let entry_text = "(#alias Choice = ./types.lim::Choice) (#alias read = ./child.lim::read)
      (#fn main () #u64 (#let input Choice (#enum-literal Choice.Full 42u64))
        (#return (#match input (#case (Choice.Full payload) payload) (#case Choice.Empty 0u64))))";
    for (path, text) in [
        (&types, types_text),
        (&child, child_text),
        (&entry, entry_text),
    ] {
        std::fs::write(path, text).unwrap();
    }
    context(&entry, CompileConfig::default())
        .write(&base.join("lim.lsp"))
        .unwrap();
    let child_uri = lsp::path_to_uri(&child).unwrap();
    let entry_uri = lsp::path_to_uri(&entry).unwrap();
    let types_uri = lsp::path_to_uri(&types).unwrap();
    let mut messages = start();
    messages.push(open(&child_uri, 1, child_text));
    messages.push(open(&entry_uri, 1, entry_text));
    messages.push(definition_offset(
        2,
        &child_uri,
        child_text,
        "(#case (Choice.Full",
        8,
    ));
    messages.push(definition_offset(
        3,
        &entry_uri,
        entry_text,
        "(#case (Choice.Full",
        8,
    ));
    messages.push(definition_offset(
        4,
        &child_uri,
        child_text,
        "(#case Choice.Empty",
        7,
    ));
    finish(&mut messages);
    let (_, replies) = session(messages);
    for (id, name) in [(2, "Choice.Full"), (3, "Choice.Full"), (4, "Choice.Empty")] {
        let locations = definition_locations(&replies, id);
        assert_eq!(locations.len(), 1, "{replies:?}");
        assert_definition_token(
            locations[0],
            &types_uri,
            types_text,
            types_text.find(name).unwrap(),
            name,
        );
    }
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn enum_case_variants_navigate_to_user_and_builtin_generated_definitions() {
    for (label, declarations, ty, variant, empty, value) in [
        (
            "user",
            "(#gn make () `((#enum Work () ((Work.Ready #u64) Work.Pending))))\n(#generate make)",
            "Work",
            "Work.Ready",
            "Work.Pending",
            "(Work.Ready 42u64)",
        ),
        (
            "builtin",
            "(#generate #optional (: type #u64 : name Maybe))",
            "Maybe",
            "Maybe.Some",
            "Maybe.None",
            "(#call Maybe::construct (: value 42u64))",
        ),
    ] {
        let base = std::env::temp_dir().join(format!(
            "lim-lsp-generated-cases-{}-{label}",
            std::process::id()
        ));
        std::fs::create_dir_all(&base).unwrap();
        let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
        let source = format!(
            "{declarations}\n(#fn main () #u64 (#let input {ty} {value})
          (#return (#match input (#case ({variant} payload) payload) (#case {empty} 0u64))))"
        );
        let mut messages = start();
        messages.push(open(&uri, 1, &source));
        messages.push(definition_offset(
            2,
            &uri,
            &source,
            &format!("(#case ({variant}"),
            8,
        ));
        messages.push(definition_offset(
            3,
            &uri,
            &source,
            &format!("(#case {empty}"),
            7,
        ));
        finish(&mut messages);
        let (_, replies) = session(messages);
        for (id, name) in [(2, variant), (3, empty)] {
            let locations = definition_locations(&replies, id);
            assert_eq!(locations.len(), 1, "{label}: {replies:?}");
            let target_uri = locations[0].get("uri").and_then(Json::string).unwrap();
            let target = lsp::uri_to_path(target_uri).unwrap();
            assert!(target.starts_with(base.join(".lim/generated")));
            let generated = std::fs::read_to_string(target).unwrap();
            assert_definition_token(
                locations[0],
                target_uri,
                &generated,
                generated.find(name).unwrap(),
                name,
            );
        }
        std::fs::remove_dir_all(base).unwrap();
    }
}

#[test]
fn distributed_enum_contributions_navigate_through_direct_file_aliases() {
    for generated in [false, true] {
        let base = std::env::temp_dir().join(format!(
            "lim-lsp-contributed-cases-{}-{generated}",
            std::process::id()
        ));
        std::fs::create_dir_all(&base).unwrap();
        let entry = base.join("main.lim");
        let contribution = base.join("contribution.lim");
        let source="(#alias Event = ./contribution.lim::Event) (#fn main () #u64 (#let input Event (Event.Ready 42u64)) (#return (#match input (#case (Event.Ready payload) payload))))";
        let declaration = if generated {
            "(#distributed-enum Event ())\n(#gn contribute () `((#enum-contribute Event (Event.Ready #u64))))\n(#generate contribute)"
        } else {
            "(#distributed-enum Event ())\n(#enum-contribute Event (Event.Ready #u64))"
        };
        std::fs::write(&entry, source).unwrap();
        std::fs::write(&contribution, declaration).unwrap();
        let uri = lsp::path_to_uri(&entry).unwrap();
        let mut messages = start();
        messages.push(open(&uri, 1, source));
        messages.push(definition_offset(2, &uri, source, "(#case (Event.Ready", 8));
        finish(&mut messages);
        let (_, replies) = session(messages);
        let locations = definition_locations(&replies, 2);
        assert_eq!(locations.len(), 1, "{replies:?}");
        let target_uri = locations[0].get("uri").and_then(Json::string).unwrap();
        let target = lsp::uri_to_path(target_uri).unwrap();
        if generated {
            assert!(target.starts_with(base.join(".lim/generated")));
        } else {
            assert_eq!(target, contribution);
        }
        let output = std::fs::read_to_string(&target).unwrap();
        let name = if generated {
            format!(
                "{}::Event.Ready",
                contribution.canonicalize().unwrap().display()
            )
        } else {
            "Event.Ready".into()
        };
        let start = output.find(&format!("({name} #u64)")).unwrap() + 1;
        assert_definition_token(locations[0], target_uri, &output, start, &name);
        std::fs::remove_dir_all(base).unwrap();
    }
}

#[test]
fn enum_case_variants_resolve_through_direct_file_aliases() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-direct-case-alias-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let app = base.join("app.lim");
    let library_text = "(#enum Choice () ((Choice.Ready #u64) Choice.Pending))\n(#fn classify (: input Choice) #u64 (#return (#match input (#case (Choice.Ready payload) payload) (#case Choice.Pending 0u64))))";
    let entry_text = "(#alias classify = ./library.lim::classify)";
    std::fs::write(&library, library_text).unwrap();
    std::fs::write(&app, entry_text).unwrap();
    lim::lsp_context::LspContext::write_all(
        &[context(&app, CompileConfig::default())],
        &base.join("lim.lsp"),
    )
    .unwrap();
    let uri = lsp::path_to_uri(&library).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, library_text));
    messages.push(definition_offset(
        2,
        &uri,
        library_text,
        "(#case (Choice.Ready",
        8,
    ));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let locations = definition_locations(&replies, 2);
    assert_eq!(locations.len(), 1, "{replies:?}");
    assert_eq!(
        locations[0].get("uri").and_then(Json::string),
        Some(uri.as_str())
    );
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn enum_case_variants_do_not_resolve_quoted_inactive_or_ambiguous_uses() {
    let base = std::env::temp_dir().join(format!("lim-lsp-negative-cases-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
    for source in [
        "(#enum Choice () (Choice.Ready)) (#gn data () '(#match x (#case Choice.Ready 0u64)))",
        "(#enum Choice () (Choice.Ready)) (#cfg-if (#cfg-is #feature enabled) (#fn inactive () #u64 (#return (#match Choice.Ready (#case Choice.Ready 0u64)))))",
        "(#enum First () (Second.Ready)) (#enum Second () (Second.Ready)) (#fn main () #u64 (#return (#match Second.Ready (#case Second.Ready 0u64))))",
    ] {
        let mut messages = start();
        messages.push(open(&uri, 1, source));
        let needle = if source.contains("(#case Second.Ready") { "(#case Second.Ready" } else { "(#case Choice.Ready" };
        messages.push(definition_offset(2, &uri, source, needle, 7));
        finish(&mut messages);
        let (_, replies) = session(messages);
        assert_eq!(reply(&replies, 2).get("result"), Some(&Json::Null), "{source}: {replies:?}");
    }
    std::fs::remove_dir_all(base).unwrap();
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
fn repeated_entry_aliases_navigate_to_one_shared_declaration() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-entries-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let library_text = "(#fn read-value () #u64 (#return 42u64))";
    std::fs::write(&library, library_text).unwrap();
    let mut contexts = Vec::new();
    let mut entries = Vec::new();
    for name in ["app", "test", "bench"] {
        let entry = base.join(format!("{name}.lim"));
        let text = "(#alias read-value = ./library.lim::read-value)\n(#fn main () #u64 (#return (#call read-value ())))";
        std::fs::write(&entry, text).unwrap();
        contexts.push(context(&entry, CompileConfig::default()));
        entries.push((entry, text));
    }
    lim::lsp_context::LspContext::write_all(&contexts, &base.join("lim.lsp")).unwrap();
    let mut messages = start();
    for (index, (entry, text)) in entries.iter().enumerate() {
        messages.push(open(&lsp::path_to_uri(entry).unwrap(), 1, text));
        messages.push(definition(
            (index + 2) as i64,
            &lsp::path_to_uri(entry).unwrap(),
            text,
            "./library.lim::read-value",
        ));
    }
    finish(&mut messages);
    let (_, replies) = session(messages);
    let expected = lsp::path_to_uri(&library).unwrap();
    for id in [2, 3, 4] {
        let locations = definition_locations(&replies, id);
        assert_eq!(locations.len(), 1);
        assert_eq!(
            locations[0].get("uri").and_then(Json::string),
            Some(expected.as_str())
        );
    }
    assert!(!base.join(".lim").exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn multi_context_cfg_and_unsaved_buffers_select_distinct_direct_file_declarations() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-cfg-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let entry = base.join("main.lim");
    let app_file = base.join("app-module.lim");
    let test_file = base.join("test-module.lim");
    let app_text = "(#fn selected () #u64 (#return 10u64))";
    let test_text = "(#fn selected () #u64 (#return 20u64))";
    std::fs::write(&app_file, app_text).unwrap();
    std::fs::write(&test_file, test_text).unwrap();
    let entry_text="(#cfg-if (#cfg-is #mode app) (#alias selected = ./app-module.lim::selected) (#cfg-else (#alias selected = ./test-module.lim::selected))) (#fn main () #u64 (#return (#call selected ())))";
    std::fs::write(&entry, &entry_text).unwrap();
    let mut app = CompileConfig::default();
    app.set("mode", "app");
    let mut test = CompileConfig::default();
    test.set("mode", "test");
    lim::lsp_context::LspContext::write_all(
        &[context(&entry, app), context(&entry, test)],
        &base.join("lim.lsp"),
    )
    .unwrap();
    let uri = lsp::path_to_uri(&entry).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, entry_text));
    messages.push(definition(2, &uri, entry_text, "selected ("));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let locations = definition_locations(&replies, 2);
    assert_eq!(locations.len(), 2, "{locations:?}");
    let actual = locations
        .iter()
        .map(|l| l.get("uri").unwrap().string().unwrap().to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        actual,
        [
            lsp::path_to_uri(&app_file).unwrap(),
            lsp::path_to_uri(&test_file).unwrap()
        ]
        .into_iter()
        .collect()
    );
    std::fs::remove_dir_all(base).unwrap();
}
#[test]
fn custom_generator_artifacts_are_reached_through_direct_file_aliases() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-generated-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let library_text = "(#gn emit (value) `((#fn provided () #u64 (#return ,value))))";
    std::fs::write(&library, library_text).unwrap();
    let mut contexts = Vec::new();
    let mut sources = Vec::new();
    for (name, value) in [("app", 10), ("test", 20)] {
        let entry = base.join(format!("{name}.lim"));
        let text = format!("(#alias emit = ./library.lim::emit)\n(#generate emit {value}u64)\n(#fn main () #u64 (#return (#call provided ())))");
        std::fs::write(&entry, &text).unwrap();
        contexts.push(context(&entry, CompileConfig::default()));
        sources.push((entry, text));
    }
    lim::lsp_context::LspContext::write_all(&contexts, &base.join("lim.lsp")).unwrap();
    for (index, (entry, source)) in sources.iter().enumerate() {
        let uri = lsp::path_to_uri(entry).unwrap();
        let mut messages = start();
        messages.push(open(&lsp::path_to_uri(&library).unwrap(), 1, library_text));
        messages.push(open(&uri, 1, source));
        messages.push(definition(2, &uri, source, "emit ="));
        messages.push(definition(3, &uri, source, "#generate"));
        finish(&mut messages);
        let (_, replies) = session(messages);
        let declaration = reply(&replies, 2).get("result").unwrap();
        assert_eq!(
            declaration.get("uri").and_then(Json::string),
            Some(lsp::path_to_uri(&library).unwrap().as_str())
        );
        let artifacts = artifact_paths(&replies, 3);
        assert_eq!(artifacts.len(), 1);
        let generated = std::fs::read_to_string(&artifacts[0]).unwrap();
        assert!(
            generated.contains(if index == 0 {
                "#literal #u64 10"
            } else {
                "#literal #u64 20"
            }),
            "{generated}"
        );
    }
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn multi_context_direct_aliases_share_file_declaration_identity() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-modules-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let text = "(#fn read-value () #u64 (#return 42u64))";
    std::fs::write(&library, text).unwrap();
    let mut contexts = Vec::new();
    let mut entries = Vec::new();
    for name in ["app", "test"] {
        let entry = base.join(format!("{name}.lim"));
        let source = "(#alias read-value = ./library.lim::read-value)\n(#fn main () #u64 (#return (#call read-value ())))";
        std::fs::write(&entry, source).unwrap();
        contexts.push(context(&entry, CompileConfig::default()));
        entries.push((entry, source));
    }
    lim::lsp_context::LspContext::write_all(&contexts, &base.join("lim.lsp")).unwrap();
    let uri = lsp::path_to_uri(&library).unwrap();
    let mut messages = start();
    for (index, (entry, source)) in entries.iter().enumerate() {
        let entry_uri = lsp::path_to_uri(entry).unwrap();
        messages.push(open(&entry_uri, 1, source));
        messages.push(definition(
            (index + 2) as i64,
            &entry_uri,
            source,
            "./library.lim::read-value",
        ));
    }
    finish(&mut messages);
    let (_, replies) = session(messages);
    for id in [2, 3] {
        let locations = definition_locations(&replies, id);
        assert_eq!(locations.len(), 1, "{locations:?}");
        assert_eq!(
            locations[0].get("uri").and_then(Json::string),
            Some(uri.as_str())
        );
    }
    assert!(!base.join(".lim").exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn multi_context_diagnostics_identify_failing_entry_and_preserve_direct_aliases() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-errors-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let library = base.join("library.lim");
    let library_text = "(#fn read-value () #u64 (#return 42u64))";
    std::fs::write(&library, library_text).unwrap();
    let app = base.join("app.lim");
    let test = base.join("test.lim");
    let broken = base.join("broken.lim");
    let app_text = "(#alias read-value = ./library.lim::read-value) (#fn main () #u64 (#return (#call read-value ())))";
    let test_text = "(#alias read-value = ./library.lim::read-value) (#fn main () #bool (#return (#call read-value ())))";
    std::fs::write(&app, app_text).unwrap();
    std::fs::write(&test, test_text).unwrap();
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
    let uri = lsp::path_to_uri(&test).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, test_text));
    messages.push(definition(2, &uri, test_text, "./library.lim::read-value"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let result = reply(&replies, 2).get("result").unwrap();
    assert_eq!(
        result.get("uri").and_then(Json::string),
        Some(lsp::path_to_uri(&library).unwrap().as_str())
    );
    let reports = publications(&replies);
    assert!(reports.iter().any(
        |report| report.get("uri").unwrap().string() == Some(uri.as_str())
            && !report
                .get("diagnostics")
                .unwrap()
                .array()
                .unwrap()
                .is_empty()
    ));
    assert!(!base.join(".lim").exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn cfg_excluded_direct_file_calls_do_not_add_another_entries_matching_name() {
    let base = std::env::temp_dir().join(format!("lim-lsp-multi-inactive-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let entry = base.join("main.lim");
    let app_file = base.join("app-module.lim");
    let test_file = base.join("test-module.lim");
    std::fs::write(&app_file, "(#fn selected () #u64 (#return 42u64))").unwrap();
    std::fs::write(&test_file, "(#fn selected () #u64 (#return 24u64))").unwrap();
    let source="(#cfg-if (#cfg-is #mode app) (#alias selected = ./app-module.lim::selected) (#cfg-else (#alias selected = ./test-module.lim::selected))) (#fn main () #u64 (#return (#call selected ())))";
    std::fs::write(&entry, source).unwrap();
    let mut config = CompileConfig::default();
    config.set("mode", "app");
    lim::lsp_context::LspContext::write_all(&[context(&entry, config)], &base.join("lim.lsp"))
        .unwrap();
    let uri = lsp::path_to_uri(&entry).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(definition(2, &uri, source, "selected ("));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let locations = definition_locations(&replies, 2);
    assert_eq!(locations.len(), 1, "{locations:?}");
    assert_eq!(
        locations[0].get("uri").unwrap().string(),
        Some(lsp::path_to_uri(&app_file).unwrap().as_str())
    );
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn unused_type_warnings_have_warning_severity_and_clear_when_used() {
    let uri = "file:///tmp/lim-lsp-unused-types.lim";
    let source = "(#enum Unused () (Unused.Only))";
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
    let source = "; 😀 UTF-16 position\n(#gn emit (name) `((#type ,name #u64)))\n(\n  #generate emit First\n)\n(#type Emoji😀 #u8) (#generate emit Second)";
    std::fs::write(&path, source).unwrap();
    let updated = source.replace("#u64", "#u32");
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(definition(2, &uri, source, "#generate emit First"));
    messages.push(definition(3, &uri, source, "#generate emit First"));
    messages.push(definition(4, &uri, source, "#generate emit Second"));
    messages.push(change(&uri, 2, &updated));
    messages.push(definition(5, &uri, &updated, "#generate emit First"));
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
    let entry_source = "(#alias child = ./child.lim::child)";
    let generator_source = "\n(#cfg-if (#cfg-is #feature selected) (#gn emit (name) `((#type ,name #u32))) (#cfg-else (#gn emit (name) `((#type ,name #u64)))))";
    let child_source = "(#alias emit = ./modules/generator.lim::emit)\n(#generate emit Number)\n(#fn child () #u64 (#return 42u64))";
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
    messages.push(definition(2, &uri, child_source, "#generate"));
    messages.push(definition(3, &uri, child_source, "emit"));
    messages.push(change(
        &generator_uri,
        2,
        &generator_source.replace("#u32", "#u16"),
    ));
    messages.push(definition(4, &uri, child_source, "#generate"));
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
    messages.push(definition(2, &uri, child_source, "#generate"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(reply(&replies, 2).get("result"), Some(&Json::Null));
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn generator_name_resolves_original_span_through_direct_file_identity() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-prefix-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let entry = base.join("main.lim");
    let child = base.join("child.lim");
    let source = "(#alias emit = ./child.lim::emit)";
    std::fs::write(&entry, source).unwrap();
    lim::lsp_context::LspContext {
        entry: entry.clone(),
        config: CompileConfig::default(),
        target: lim::TargetDescription::X86_64_SYSTEM_V,
    }
    .write(&base.join("lim.lsp"))
    .unwrap();
    let child_source =
        "; unsaved generator\n(#gn emit (name) `((#type ,name #u64)))\n(#generate emit Number)";
    let uri = lsp::path_to_uri(&child).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, child_source));
    messages.push(definition(2, &uri, child_source, "emit Number"));
    messages.push(definition(3, &uri, child_source, "#generate"));
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
    assert!(contents.contains("#type Number"), "{contents}");
    assert!(!child.exists());
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn builtin_macro_at_navigates_but_builtin_name_and_noninvocations_do_not() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-builtin-{}", std::process::id()));
    let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
    let source = "(#generate #optional (: type #u64 : name Maybe))";
    let mut messages = start();
    messages.push(open(&uri, 1, source));
    messages.push(definition(2, &uri, source, "#optional"));
    messages.push(definition(3, &uri, source, "#generate"));
    messages.push(definition(4, &uri, source, "Maybe"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(reply(&replies, 2).get("result"), Some(&Json::Null));
    assert_eq!(reply(&replies, 4).get("result"), Some(&Json::Null));
    assert!(artifact_paths(&replies, 3)
        .iter()
        .any(|path| std::fs::read_to_string(path)
            .unwrap()
            .contains("Maybe::construct")));
    std::fs::remove_dir_all(base).unwrap();
}

#[test]
fn imported_generator_name_navigation_needs_no_valid_expansion_or_artifacts() {
    let base = std::env::temp_dir().join(format!("lim-lsp-macro-name-only-{}", std::process::id()));
    let uri = lsp::path_to_uri(&base.join("main.lim")).unwrap();
    let generator_uri = lsp::path_to_uri(&base.join("generator.lim")).unwrap();
    let source = "(#alias emit = ./generator.lim::emit)\n(#generate emit)";
    let generator = "; unsaved\n(#gn emit () (#gn-error \"not implemented\"))";
    let mut messages = start();
    messages.push(open(&generator_uri, 1, generator));
    messages.push(open(&uri, 1, source));
    messages.push(definition(2, &uri, source, "emit"));
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
        "(#gn emit () `((#type Number #u64))) (#cfg-if (#cfg-is #feature never-enabled) (#generate emit))",
        "(#gn bad () `((#fn broken () #u64 (#return false)))) (#generate bad)",
        "(#gn bad () (#gn-error \"failed\")) (#generate bad)",
        "(#gn template () `((#generate missing)))",
        "(#generate unknown)",
    ] {
        let mut messages = start();
        messages.push(open(&uri, 1, source));
        messages.push(definition(2, &uri, source, "#generate"));
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
    let text = "(#alias Number = ./child.lim::Number)\n(#alias read = ./child.lim::read)\n(#fn main () #u64 (#let value Number 42u64) (#return (#call read (: value value))))\n(#fn broken () #u64 (#return #true))\n(#struct Holder () ((field Number)))\n(#enum Choice () ((Choice.Present Number) (Choice.Absent ())))";
    let imported = "(#type Number #u64)\n(#fn read ((value Number)) #u64 (#return value))";
    std::fs::write(&root, text).unwrap();
    std::fs::write(&child, imported).unwrap();
    let uri = lsp::path_to_uri(&root).unwrap();
    let child_uri = lsp::path_to_uri(&child).unwrap();
    let mut messages = start();
    messages.push(open(&uri, 1, text));
    for (id, needle) in [
        (2, "child.lim"),
        (3, "read ="),
        (4, "read (:"),
        (5, "Number ="),
    ] {
        messages.push(definition(id, &uri, text, needle));
    }
    messages.push(definition(6, &uri, text, "value value"));
    messages.push(definition(7, &uri, text, "Number)))"));
    messages.push(definition(8, &uri, text, "Number) (Choice.Absent"));
    finish(&mut messages);
    let (_, replies) = session(messages);
    for id in [2, 3, 4, 5, 6, 7, 8] {
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
    std::fs::write(
        &root,
        "(#alias invoke = ./child.lim::invoke)\n(#fn main () Number (#return (#call invoke ())))",
    )
    .unwrap();
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
fn direct_file_navigation_resolves_project_and_relative_paths_with_unsaved_sources() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-module-navigation-{}", std::process::id()));
    let modules = base.join("modules");
    std::fs::create_dir_all(&modules).unwrap();
    let root = base.join("main.lim");
    let unsaved = base.join("unsaved.lim");
    let local = base.join("local.lim");
    let shared = modules.join("shared.lim");
    let text = "(#alias Shared = ./modules/shared.lim::Shared)\n(#alias Local = ./local.lim::Local)\n(#alias unsaved-value = ./unsaved.lim::unsaved-value)\n(#fn main () #u64 (#return (#call unsaved-value ())))";
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
fn missing_and_quoted_direct_file_references_do_not_invent_definition_targets() {
    let uri = "file:///tmp/lim-lsp-missing-import-navigation.lim";
    let text = "(#alias missing = ./does-not-exist-743198.lim::missing)\n'(#alias quoted = ./quoted.lim::quoted)";
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
    let source = "(#generate #optional (: type #u64 : name Maybe))\n(#fn main () () (#let value Maybe (#call Maybe::construct (: value 42u64))) (#forget value) (#return ()))";
    let character = source
        .lines()
        .nth(1)
        .unwrap()
        .find("Maybe::construct")
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
    assert!(generated.contains("Maybe::construct"));
    let range_start = result.get("range").unwrap().get("start").unwrap();
    let line = range_start.get("line").unwrap().integer().unwrap() as usize;
    let column = range_start.get("character").unwrap().integer().unwrap() as usize;
    assert!(generated.lines().nth(line).unwrap()[column..].starts_with("Maybe::construct"));
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
    let source = "(#gn emit (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64)))\n(#generate emit Number)\n(#fn main () Number (#return 42u64))";
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
fn generated_definition_uses_an_unsaved_direct_generator_alias_and_rejects_invalid_expansions() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-generated-import-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    let uri = format!("file://{}", base.join("main.lim").display());
    let generator_uri = format!("file://{}", base.join("types.lim").display());
    let source = "(#alias emit = ./types.lim::emit)\n(#generate emit Number)\n(#fn main () Number (#return 42u64))";
    let generator = "(#gn emit (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64)))";
    let character = source.lines().nth(2).unwrap().find("Number").unwrap();
    let params = format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":2,\"character\":{character}}}}}",
        diagnostic_json::quoted(&uri)
    );
    let mut messages = start();
    messages.push(open(&generator_uri, 1, generator));
    messages.push(open(&uri, 1, source));
    messages.push(request(2, "textDocument/definition", &params));
    messages.push(change(
        &generator_uri,
        2,
        &generator.replace("#u64", "MissingType"),
    ));
    messages.push(request(3, "textDocument/definition", &params));
    finish(&mut messages);
    let (_, replies) = session(messages);
    let result = reply(&replies, 2).get("result").unwrap();
    assert!(result
        .get("uri")
        .and_then(Json::string)
        .unwrap()
        .contains("generated-"));
    assert_eq!(reply(&replies, 3).get("result"), Some(&Json::Null));
    assert!(!base.join("types.lim").exists());
}

#[test]
fn compilation_context_navigates_an_unsaved_external_file_alias() {
    let base =
        std::env::temp_dir().join(format!("lim-lsp-entry-navigation-{}", std::process::id()));
    let external =
        std::env::temp_dir().join(format!("lim-lsp-entry-external-{}", std::process::id()));
    std::fs::create_dir_all(&base).unwrap();
    std::fs::create_dir_all(&external).unwrap();
    let entry = base.join("main.lim");
    let child = external.join("child.lim");
    let uri = lsp::path_to_uri(&child).unwrap();
    let root_uri = lsp::path_to_uri(&base).unwrap();
    let source = "(#fn child () #u64 (#return 42u64)) (#generate #optional (: type #u64 : name Maybe)) (#fn wrap () Maybe (#return (#call Maybe::construct (: value 42u64))))";
    std::fs::write(
        &entry,
        format!(
            "(#alias child = {}::child) (#fn main () #u64 (#return (#call child ())))",
            child.display()
        ),
    )
    .unwrap();
    context(&entry, CompileConfig::default())
        .write(&base.join("lim.lsp"))
        .unwrap();
    let initialize = format!(
        "{{\"rootUri\":{},\"capabilities\":{{\"workspace\":{{\"didChangeWatchedFiles\":{{\"dynamicRegistration\":true}}}}}}}}",
        diagnostic_json::quoted(&root_uri)
    );
    let mut messages = vec![
        request(1, "initialize", &initialize),
        notify("initialized", "{}"),
    ];
    messages.push("{\"jsonrpc\":\"2.0\",\"id\":\"lim-context-watch\",\"result\":null}".into());
    messages.push(open(&uri, 1, source));
    for (id, needle) in [(2, "child"), (3, "Maybe (#return"), (4, "Maybe::construct")] {
        messages.push(definition(id, &uri, source, needle));
    }
    let manifest_uri = lsp::path_to_uri(&base.join("lim.lsp")).unwrap();
    let changed = format!(
        "{{\"changes\":[{{\"uri\":{},\"type\":2}}]}}",
        diagnostic_json::quoted(&manifest_uri)
    );
    messages.push(notify("workspace/didChangeWatchedFiles", &changed));
    finish(&mut messages);
    let (_, replies) = session(messages);
    assert_eq!(
        reply(&replies, 2)
            .get("result")
            .unwrap()
            .get("uri")
            .and_then(Json::string),
        Some(uri.as_str())
    );
    let generated = reply(&replies, 4).get("result").unwrap();
    let target = lsp::uri_to_path(generated.get("uri").and_then(Json::string).unwrap()).unwrap();
    assert!(target.starts_with(external.join(".lim/generated")));
    let snapshot = std::fs::read_to_string(&target).unwrap();
    let name = format!("{}::Maybe::construct", child.display());
    let declaration = format!("(#fn {name}");
    assert_definition_token(
        generated,
        generated.get("uri").and_then(Json::string).unwrap(),
        &snapshot,
        snapshot.find(&declaration).unwrap() + "(#fn ".len(),
        &name,
    );
    assert!(!child.exists());
    assert!(!base.join(".lim").exists());
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
    let source = "(#cfg-if (#cfg-is #feature good) (#type Number #u64) (#cfg-else (#type Number #bool))) (#alias child = ./child.lim::child) (#fn main () #u64 (#return (#call child ())))";
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
    for message in start()
        .into_iter()
        .chain([open(&uri, 1, "(#fn child () #u64 (#return 42u64))")])
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
    messages.push(open(root, 1, "(#alias child = ./child.lim::child)"));
    messages.push(change(child, 2, ")"));
    messages.push(change(child, 3, "(#fn child () #u64 (#return 42u64))"));
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
    let source = "(#gn bad () `((#fn broken () #u64 (#return false))))\n(#generate bad)";
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
    messages.push(open(&root_uri, 1, "(#alias child = ./child.lim::child)"));
    messages.push(change(&child_uri, 2, ")"));
    messages.push(change(&child_uri, 3, "(#fn child () #u64 (#return 42u64))"));
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
