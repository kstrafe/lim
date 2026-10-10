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
    let text = "(#fn main () #u64 (#return 0u64))\n(#struct Point ())";
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
    let source = "(#fn target () #u64 (#return 0u64))\n(#fn main () #u64 (#return (#call target (:))))\n(#struct Holder ((target #u64)))\n'(#call target (:))";
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
    let source = "(@optional (: type #u64 : name Maybe))\n(#fn main () () (#let value Maybe (#call Maybe-construct (: value 42u64))) (#forget value) (#return ()))";
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
