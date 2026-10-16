//! Editing sessions against the real stdio server, with bounded response waits.
use lim::{
    lsp::{
        self,
        json::{self, Json},
    },
    lsp_context::LspContext,
    CompileConfig, TargetDescription,
};
use std::{
    collections::BTreeMap,
    fs,
    io::{BufReader, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, Stdio},
    sync::{
        atomic::{AtomicU64, Ordering},
        mpsc::{self, Receiver},
    },
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

fn object<const N: usize>(fields: [(&str, Json); N]) -> Json {
    Json::Object(
        fields
            .into_iter()
            .map(|(k, v)| (k.into(), v))
            .collect::<BTreeMap<_, _>>(),
    )
}
fn string(value: impl Into<String>) -> Json {
    Json::String(value.into())
}
fn number(value: usize) -> Json {
    Json::Number(value.to_string())
}
fn uri(path: &Path) -> String {
    lsp::path_to_uri(path).unwrap()
}
fn document(path: &Path) -> Json {
    object([("textDocument", object([("uri", string(uri(path)))]))])
}

// Independently calculate expected positions; do not reuse the implementation
// being tested to verify its UTF-16 source ranges.
fn position(text: &str, byte: usize) -> Json {
    let prefix = &text[..byte];
    object([
        (
            "line",
            number(prefix.bytes().filter(|b| *b == b'\n').count()),
        ),
        (
            "character",
            number(prefix.rsplit('\n').next().unwrap().encode_utf16().count()),
        ),
    ])
}
fn source_range(text: &str, start: usize, end: usize) -> Json {
    object([
        ("start", position(text, start)),
        ("end", position(text, end)),
    ])
}
fn assert_location(result: &Json, path: &Path, text: &str, declaration: &str, name: &str) {
    let start = text.find(declaration).unwrap() + declaration.find(name).unwrap();
    assert_eq!(result.get("uri"), Some(&string(uri(path))), "{result:?}");
    assert_eq!(
        result.get("range"),
        Some(&source_range(text, start, start + name.len())),
        "{result:?}"
    );
}

struct Fixture(PathBuf);
impl Fixture {
    fn new(name: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "lim-lsp-e2e-{name}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, text).unwrap();
        path
    }
    fn context(&self, entry: &Path, flavor: &str) {
        let mut config = CompileConfig::default();
        config.set("flavor", flavor);
        LspContext {
            entry: entry.to_owned(),
            config,
            target: TargetDescription::X86_64_SYSTEM_V,
        }
        .write(&self.0.join("lim.lsp"))
        .unwrap();
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        // The exact directory was created exclusively by this fixture.
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct Client {
    child: Child,
    input: Option<ChildStdin>,
    receiver: Receiver<Result<Json, String>>,
    reader: Option<JoinHandle<()>>,
    messages: Vec<Json>,
    next_id: usize,
}
impl Client {
    fn start(root: &Path) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg("lsp")
            .current_dir(root)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (sender, receiver) = mpsc::channel();
        let reader = thread::spawn(move || {
            let mut stdout = BufReader::new(stdout);
            loop {
                let message = match json::read_frame(&mut stdout) {
                    Ok(Some(body)) => json::parse(&body).map_err(str::to_owned),
                    Ok(None) => break,
                    Err(error) => Err(error.to_string()),
                };
                let failed = message.is_err();
                if sender.send(message).is_err() || failed {
                    break;
                }
            }
        });
        let mut client = Self {
            child,
            input: Some(input),
            receiver,
            reader: Some(reader),
            messages: Vec::new(),
            next_id: 1,
        };
        let capabilities = client.request(
            "initialize",
            object([("rootUri", string(uri(root))), ("capabilities", object([]))]),
        );
        let capabilities = capabilities.get("capabilities").unwrap();
        assert_eq!(
            capabilities.get("positionEncoding"),
            Some(&string("utf-16"))
        );
        for key in [
            "definitionProvider",
            "documentSymbolProvider",
            "documentFormattingProvider",
        ] {
            assert_eq!(capabilities.get(key), Some(&Json::Bool(true)));
        }
        client.notify("initialized", object([]));
        client
    }
    fn send(&mut self, message: Json) {
        json::write_frame(self.input.as_mut().unwrap(), &message.render()).unwrap();
    }
    fn notify(&mut self, method: &str, params: Json) {
        self.send(object([
            ("jsonrpc", string("2.0")),
            ("method", string(method)),
            ("params", params),
        ]));
    }
    fn response(&mut self, method: &str, params: Json) -> Json {
        let id = self.next_id;
        self.next_id += 1;
        self.send(object([
            ("jsonrpc", string("2.0")),
            ("id", number(id)),
            ("method", string(method)),
            ("params", params),
        ]));
        let deadline = Instant::now() + Duration::from_secs(15);
        loop {
            let message = self
                .receiver
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                .unwrap_or_else(|error| {
                    panic!("{method}: {error}; transcript: {:?}", self.messages)
                })
                .unwrap_or_else(|error| panic!("invalid stdio output: {error}"));
            assert_eq!(message.get("jsonrpc"), Some(&string("2.0")));
            let matched = message.get("id").and_then(Json::integer) == Some(id as i64);
            self.messages.push(message.clone());
            if matched {
                return message;
            }
        }
    }
    fn request(&mut self, method: &str, params: Json) -> Json {
        let response = self.response(method, params);
        assert!(response.get("error").is_none(), "{method}: {response:?}");
        response.get("result").unwrap().clone()
    }
    fn error(&mut self, method: &str, params: Json, code: i64) {
        let response = self.response(method, params);
        assert_eq!(
            response
                .get("error")
                .and_then(|e| e.get("code"))
                .and_then(Json::integer),
            Some(code),
            "{response:?}"
        );
    }
    fn open(&mut self, path: &Path, text: &str) {
        self.notify(
            "textDocument/didOpen",
            object([(
                "textDocument",
                object([
                    ("uri", string(uri(path))),
                    ("languageId", string("lim")),
                    ("version", number(1)),
                    ("text", string(text)),
                ]),
            )]),
        );
    }
    fn change(&mut self, path: &Path, version: usize, text: &str) {
        self.notify(
            "textDocument/didChange",
            object([
                (
                    "textDocument",
                    object([("uri", string(uri(path))), ("version", number(version))]),
                ),
                (
                    "contentChanges",
                    Json::Array(vec![object([("text", string(text))])]),
                ),
            ]),
        );
    }
    fn close(&mut self, path: &Path) {
        self.notify("textDocument/didClose", document(path));
    }
    fn definition(&mut self, path: &Path, text: &str, needle: &str) -> Json {
        self.request(
            "textDocument/definition",
            object([
                ("textDocument", object([("uri", string(uri(path)))])),
                ("position", position(text, text.find(needle).unwrap())),
            ]),
        )
    }
    fn diagnostics(&self, path: &Path) -> &Json {
        self.messages
            .iter()
            .rev()
            .find_map(|m| {
                if m.get("method").and_then(Json::string) != Some("textDocument/publishDiagnostics")
                {
                    return None;
                }
                let params = m.get("params")?;
                (params.get("uri").and_then(Json::string) == Some(uri(path).as_str()))
                    .then_some(params)
            })
            .unwrap_or_else(|| panic!("no diagnostics for {}", path.display()))
    }
    fn clear(&self, path: &Path) {
        assert!(
            self.diagnostics(path)
                .get("diagnostics")
                .unwrap()
                .array()
                .unwrap()
                .is_empty(),
            "{:?}",
            self.diagnostics(path)
        );
    }
    fn watch(&mut self, path: &Path) {
        self.notify(
            "workspace/didChangeWatchedFiles",
            object([(
                "changes",
                Json::Array(vec![object([
                    ("uri", string(uri(path))),
                    ("type", number(2)),
                ])]),
            )]),
        );
    }
    fn shutdown(mut self) {
        assert_eq!(self.request("shutdown", Json::Null), Json::Null);
        self.notify("exit", Json::Null);
        self.input.take();
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(status.success(), "server exit: {status}");
                break;
            }
            assert!(
                Instant::now() < deadline,
                "server did not exit after shutdown"
            );
            thread::sleep(Duration::from_millis(10));
        }
        self.reader.take().unwrap().join().unwrap();
    }
}
impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        self.input.take();
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
}

#[test]
fn transitive_external_imports_cfg_and_unicode_have_exact_navigation_ranges() {
    let fixture = Fixture::new("navigation");
    let leaf_text = "(#type Number #u64)\r\n(#fn glyph () #char (#return #\\😀)) (#fn leaf-value ((value Number)) Number (#return value))\r\n(#struct Holder () ((field Number)))\r\n";
    let leaf = fixture.write("modules α/leaf #%.lim", leaf_text);
    let bridge_text = "(#import \"leaf #%.lim\")\r\n(#cfg-if (#cfg-is #flavor first)\r\n (#fn proxy ((value Number)) Number (#return (#call leaf-value (: value value))))\r\n (#cfg-else (#fn proxy ((value Number)) Number (#return value))))\r\n";
    let bridge = fixture.write("modules α/bridge.lim", bridge_text);
    let root_text = "(#import-external \"modules α/bridge.lim\" ext-)\r\n(#fn glyph-root () #char (#return #\\😀)) (#fn main () ext-Number (#return (#call ext-proxy (: ext-value 42u64))))\r\n";
    let root = fixture.write("main.lim", root_text);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    for (path, text) in [
        (&root, root_text),
        (&bridge, bridge_text),
        (&leaf, leaf_text),
    ] {
        client.open(path, text);
    }
    let cases = [
        (
            &root,
            root_text,
            "ext-proxy",
            &bridge,
            bridge_text,
            "#fn proxy",
            "proxy",
        ),
        (
            &root,
            root_text,
            "ext-Number",
            &leaf,
            leaf_text,
            "#type Number",
            "Number",
        ),
        (
            &bridge,
            bridge_text,
            "leaf-value",
            &leaf,
            leaf_text,
            "#fn leaf-value",
            "leaf-value",
        ),
        (
            &bridge,
            bridge_text,
            "Number (#return (#call",
            &leaf,
            leaf_text,
            "#type Number",
            "Number",
        ),
        (
            &leaf,
            leaf_text,
            "Number)))",
            &leaf,
            leaf_text,
            "#type Number",
            "Number",
        ),
    ];
    for (path, text, needle, target, target_text, declaration, name) in cases {
        assert_location(
            &client.definition(path, text, needle),
            target,
            target_text,
            declaration,
            name,
        );
    }
    for (path, text, needle, target) in [
        (&root, root_text, "modules α/bridge.lim", &bridge),
        (&bridge, bridge_text, "leaf #%.lim", &leaf),
    ] {
        let result = client.definition(path, text, needle);
        assert_eq!(result.get("uri"), Some(&string(uri(target))));
        assert_eq!(result.get("range"), Some(&source_range("", 0, 0)));
    }
    for (path, text, needle) in [
        (&root, root_text, "ext-)"),
        (&root, root_text, "ext-value 42"),
        (&bridge, bridge_text, "value value"),
    ] {
        assert_eq!(client.definition(path, text, needle), Json::Null);
    }
    for path in [&root, &bridge, &leaf] {
        client.clear(path);
    }
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}

#[test]
fn imported_signature_and_aggregate_type_roles_and_ffi_declarations_navigate() {
    let fixture = Fixture::new("type-roles");
    let module_text = "(#type Number #u64)\n(#extern-fn #abi-c foreign ((value Number)) Number)\n(#unsafe-fn guarded ((value Number)) Number (#return value))\n(#struct Holder () ((field (#ref Number))))\n(#enum Choice () ((Data (#tuple Number Number)) Empty))\n(#struct CRecord (#repr-c) ((c-field Number)))\n(#const LIMIT Number 99u64)\n(#static COUNT Number 42u64)\n";
    let module = fixture.write("functions.lim", module_text);
    let root_text = "(#import \"functions.lim\")\n(#fn main () Number\n (#let-mut input Number 42u64)\n (#return (#unsafe (#call foreign (: value (#call guarded (: value input)))))))\n";
    let root = fixture.write("main.lim", root_text);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, root_text);
    client.open(&module, module_text);
    for (path, text, needle, declaration, name) in [
        (
            &root,
            root_text,
            "foreign",
            "#extern-fn #abi-c foreign",
            "foreign",
        ),
        (&root, root_text, "guarded", "#unsafe-fn guarded", "guarded"),
        (
            &module,
            module_text,
            "foreign",
            "#extern-fn #abi-c foreign",
            "foreign",
        ),
        (&root, root_text, "Number 42u64", "#type Number", "Number"),
        (
            &module,
            module_text,
            "Number)) Number",
            "#type Number",
            "Number",
        ),
        (
            &module,
            module_text,
            "Number)\n(#unsafe-fn",
            "#type Number",
            "Number",
        ),
        (
            &module,
            module_text,
            "Number (#return",
            "#type Number",
            "Number",
        ),
        (&module, module_text, "Number))))", "#type Number", "Number"),
        (&module, module_text, "Number)))", "#type Number", "Number"),
        (
            &module,
            module_text,
            "Number 99u64",
            "#type Number",
            "Number",
        ),
        (
            &module,
            module_text,
            "Number 42u64",
            "#type Number",
            "Number",
        ),
        (
            &module,
            module_text,
            "Number Number",
            "#type Number",
            "Number",
        ),
        (
            &module,
            module_text,
            "Number)) Empty",
            "#type Number",
            "Number",
        ),
    ] {
        assert_location(
            &client.definition(path, text, needle),
            &module,
            module_text,
            declaration,
            name,
        );
    }
    let symbols = client.request("textDocument/documentSymbol", document(&module));
    let foreign = symbols
        .array()
        .unwrap()
        .iter()
        .find(|s| s.get("name").and_then(Json::string) == Some("foreign"))
        .unwrap();
    let start = module_text.find("foreign").unwrap();
    assert_eq!(
        foreign.get("selectionRange"),
        Some(&source_range(module_text, start, start + "foreign".len()))
    );
    for needle in ["#abi-c", "#u64", "value Number", "field ("] {
        assert_eq!(client.definition(&module, module_text, needle), Json::Null);
    }
    client.clear(&root);
    client.clear(&module);
    client.shutdown();
}

#[test]
fn unsaved_import_updates_errors_stale_versions_and_close_restore_disk_definitions() {
    let fixture = Fixture::new("updates");
    let disk = "(#fn target () #u64 (#return 42u64))\n";
    let child = fixture.write("child.lim", disk);
    let root_text = "(#import \"child.lim\")\n(#fn main () #u64 (#return (#call target ())))";
    let root = fixture.write("main.lim", root_text);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, root_text);
    assert_location(
        &client.definition(&root, root_text, "target"),
        &child,
        disk,
        "#fn target",
        "target",
    );
    let broken = "; unsaved 😀\n\n(#fn target () #u64 (#return false))\n";
    client.open(&child, broken);
    assert_location(
        &client.definition(&root, root_text, "target"),
        &child,
        broken,
        "#fn target",
        "target",
    );
    let diagnostics = client
        .diagnostics(&child)
        .get("diagnostics")
        .unwrap()
        .array()
        .unwrap();
    assert_eq!(diagnostics.len(), 1);
    let start = broken.find("false").unwrap();
    assert_eq!(
        diagnostics[0].get("range"),
        Some(&source_range(broken, start, start + 5))
    );
    let repaired = broken.replace("false", "42u64");
    client.change(&child, 3, &repaired);
    assert_location(
        &client.definition(&root, root_text, "target"),
        &child,
        &repaired,
        "#fn target",
        "target",
    );
    client.clear(&root);
    client.clear(&child);
    assert_eq!(client.diagnostics(&child).get("version"), Some(&number(3)));
    client.change(&child, 2, ")");
    assert_location(
        &client.definition(&root, root_text, "target"),
        &child,
        &repaired,
        "#fn target",
        "target",
    );
    assert_eq!(client.diagnostics(&child).get("version"), Some(&number(3)));
    client.close(&child);
    assert_location(
        &client.definition(&root, root_text, "target"),
        &child,
        disk,
        "#fn target",
        "target",
    );
    client.clear(&child);
    assert_eq!(fs::read_to_string(&child).unwrap(), disk);
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}

#[test]
fn context_flag_entry_and_invalid_config_changes_retarget_navigation_and_recover() {
    let fixture = Fixture::new("contexts");
    let module_text = "(#cfg-if (#cfg-is #flavor first)\n (#fn selected () #u64 (#return 1u64))\n (#cfg-else (#fn selected () #u64 (#return 2u64))))";
    let module = fixture.write("selected.lim", module_text);
    let root_text = "(#import \"selected.lim\")\n(#fn main () #u64 (#return (#call selected ())))";
    let root = fixture.write("main.lim", root_text);
    let other = fixture.write("other.lim", "(#fn main () #u64 (#return 0u64))");
    let context_path = fixture.0.join("lim.lsp");
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, root_text);
    assert_location(
        &client.definition(&root, root_text, "selected ("),
        &module,
        module_text,
        "#fn selected () #u64 (#return 1",
        "selected",
    );
    fixture.context(&root, "second");
    client.watch(&context_path);
    assert_location(
        &client.definition(&root, root_text, "selected ("),
        &module,
        module_text,
        "#fn selected () #u64 (#return 2",
        "selected",
    );
    client.clear(&root);
    fixture.context(&other, "second");
    client.watch(&context_path);
    assert_eq!(
        client.definition(&root, root_text, "selected ("),
        Json::Null
    );
    assert!(client.diagnostics(&root).render().contains("not included"));
    fs::write(&context_path, "schema-version = 7\n").unwrap();
    client.watch(&context_path);
    assert_eq!(
        client.definition(&root, root_text, "selected ("),
        Json::Null
    );
    assert!(client
        .diagnostics(&root)
        .render()
        .contains("schema-version"));
    fixture.context(&root, "first");
    client.watch(&context_path);
    assert_location(
        &client.definition(&root, root_text, "selected ("),
        &module,
        module_text,
        "#fn selected () #u64 (#return 1",
        "selected",
    );
    client.clear(&root);
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}

#[test]
fn imported_user_and_builtin_generated_definitions_are_safe_stable_snapshots() {
    let fixture = Fixture::new("generated");
    let imported = "(#gn emit (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64)))\n(@emit Number)\n(@#optional (: type Number : name Maybe))\n";
    let types = fixture.write("types.lim", imported);
    let root_text = "(#import \"types.lim\")\n(#fn main () Number (#return 42u64))\n(#fn wrap () Maybe (#return (#call Maybe-construct (: value 42u64))))";
    let root = fixture.write("main.lim", root_text);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, root_text);
    client.open(&types, imported);
    let alias = client.definition(&root, root_text, "Number (#return");
    let constructor = client.definition(&root, root_text, "Maybe-construct");
    let mut snapshots = Vec::new();
    for (result, name, invocation_line) in
        [(&alias, "Number", 2), (&constructor, "Maybe-construct", 3)]
    {
        let path = lsp::uri_to_path(result.get("uri").unwrap().string().unwrap()).unwrap();
        assert!(path.starts_with(fixture.0.join(".lim/generated")));
        let text = fs::read_to_string(&path).unwrap();
        assert!(text.contains(&format!("{}:{invocation_line}", types.display())));
        let declaration = if name == "Number" {
            "#type Number"
        } else {
            "#fn Maybe-construct"
        };
        assert_location(result, &path, &text, declaration, name);
        snapshots.push((
            path.clone(),
            text,
            fs::metadata(path).unwrap().modified().unwrap(),
        ));
    }
    assert_eq!(
        client.definition(&root, root_text, "Number (#return"),
        alias
    );
    assert_eq!(
        client.definition(&root, root_text, "Maybe-construct"),
        constructor
    );
    client.open(&snapshots[0].0, &snapshots[0].1);
    client.request("textDocument/documentSymbol", document(&snapshots[0].0));
    client.clear(&snapshots[0].0);
    client.close(&snapshots[0].0);
    client.change(&types, 2, &imported.replace("#u64", "#u32"));
    assert_eq!(
        client.definition(&root, root_text, "Number (#return"),
        Json::Null
    );
    assert_eq!(
        client.definition(&root, root_text, "Maybe-construct"),
        Json::Null
    );
    for (path, text, modified) in &snapshots {
        assert_eq!(&fs::read_to_string(path).unwrap(), text);
        assert_eq!(&fs::metadata(path).unwrap().modified().unwrap(), modified);
    }
    let repaired = root_text.replace("42u64", "42u32");
    client.change(&root, 2, &repaired);
    let new_alias = client.definition(&root, &repaired, "Number (#return");
    assert_ne!(new_alias, alias);
    assert_ne!(new_alias, Json::Null);
    client.clear(&root);
    client.clear(&types);
    let path = lsp::uri_to_path(new_alias.get("uri").unwrap().string().unwrap()).unwrap();
    fs::write(&path, "; deliberate user edit\n").unwrap();
    assert_eq!(
        client.definition(&root, &repaired, "Number (#return"),
        Json::Null
    );
    assert_eq!(
        fs::read_to_string(&path).unwrap(),
        "; deliberate user edit\n"
    );
    assert_eq!(fs::read_to_string(&types).unwrap(), imported);
    assert_eq!(fs::read_to_string(&root).unwrap(), root_text);
    assert!(!fixture.0.join(".lim/cache").exists());
    client.shutdown();
}

#[test]
fn ambiguous_imports_fail_closed_and_deduplicated_imports_recover() {
    let fixture = Fixture::new("ambiguity");
    let first_text = "(#fn target () #u64 (#return 1u64))";
    let first = fixture.write("first.lim", first_text);
    let second_text = "(#fn target () #u64 (#return 2u64))";
    let second = fixture.write("second.lim", second_text);
    let ambiguous = "(#import \"first.lim\") (#import \"second.lim\")\n(#fn main () #u64 (#return (#call target ())))";
    let root = fixture.write("main.lim", ambiguous);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, ambiguous);
    assert_eq!(client.definition(&root, ambiguous, "target"), Json::Null);
    assert!(!client
        .diagnostics(&second)
        .get("diagnostics")
        .unwrap()
        .array()
        .unwrap()
        .is_empty());
    let repaired = "(#import \"first.lim\") (#import \"first.lim\") (#import-external \"second.lim\" other-)\n(#fn main () #u64 (#return (#call target ())))\n(#fn another () #u64 (#return (#call other-target ())))";
    client.change(&root, 2, repaired);
    assert_location(
        &client.definition(&root, repaired, "target ("),
        &first,
        first_text,
        "#fn target",
        "target",
    );
    assert_location(
        &client.definition(&root, repaired, "other-target"),
        &second,
        second_text,
        "#fn target",
        "target",
    );
    client.clear(&root);
    client.clear(&second);
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}

#[test]
fn fragmented_frames_malformed_json_and_string_request_ids_recover_over_stdio() {
    let fixture = Fixture::new("framing");
    let text = "(#fn main () #u64 (#return 42u64))";
    let path = fixture.write("main.lim", text);
    let mut client = Client::start(&fixture.0);
    client.open(&path, text);
    let input = client.input.as_mut().unwrap();
    // Split headers and a multibyte JSON string across separate writes. The
    // server must wait for complete frames and keep accepting later requests.
    input.write_all(b"Content-Len").unwrap();
    input.flush().unwrap();
    input.write_all(b"gth: 7\r\n\r\n{broken").unwrap();
    let body = object([
        ("jsonrpc", string("2.0")),
        ("id", string("navigation-😀")),
        ("method", string("textDocument/documentSymbol")),
        ("params", document(&path)),
    ])
    .render();
    let split = body.find('😀').unwrap() + 1;
    input
        .write_all(format!("Content-Length: {}\r\n\r\n", body.len()).as_bytes())
        .unwrap();
    input.write_all(&body.as_bytes()[..split]).unwrap();
    input.flush().unwrap();
    input.write_all(&body.as_bytes()[split..]).unwrap();
    input.flush().unwrap();
    client.send(object([
        ("jsonrpc", string("2.0")),
        ("id", Json::Bool(true)),
        ("method", string("invalid/id")),
    ]));
    client.request("textDocument/documentSymbol", document(&path));
    for code in [-32700, -32600] {
        assert!(client
            .messages
            .iter()
            .any(|message| message.get("id") == Some(&Json::Null)
                && message
                    .get("error")
                    .and_then(|e| e.get("code"))
                    .and_then(Json::integer)
                    == Some(code)));
    }
    let reply = client
        .messages
        .iter()
        .find(|message| message.get("id") == Some(&string("navigation-😀")))
        .unwrap();
    assert_eq!(reply.get("result").unwrap().array().unwrap().len(), 1);
    client.error("initialize", object([]), -32600);
    client.error(
        "textDocument/definition",
        object([
            (
                "textDocument",
                object([("uri", string("https://example.invalid/main.lim"))]),
            ),
            ("position", position(text, 0)),
        ]),
        -32602,
    );
    assert_location(
        &client.definition(&path, text, "main"),
        &path,
        text,
        "#fn main",
        "main",
    );
    client.clear(&path);
    client.shutdown();
}

#[test]
fn formatting_symbols_utf16_invalid_requests_and_parse_error_recovery_over_stdio() {
    let fixture = Fixture::new("protocol");
    let text = "(#fn glyph () #char (#return #\\😀)) (#fn main () #u64 (#return 42u64))\r\n";
    let path = fixture.write("editor 😀.lim", text);
    let mut client = Client::start(&fixture.0);
    client.open(&path, text);
    let symbols = client.request("textDocument/documentSymbol", document(&path));
    let symbols = symbols.array().unwrap();
    assert_eq!(symbols.len(), 2);
    for (symbol, name) in symbols.iter().zip(["glyph", "main"]) {
        assert_eq!(symbol.get("name"), Some(&string(name)));
        assert_eq!(symbol.get("kind"), Some(&number(12)));
        let start = text.find(&format!("#fn {name}")).unwrap() + 4;
        assert_eq!(
            symbol.get("selectionRange"),
            Some(&source_range(text, start, start + name.len()))
        );
        assert_location(
            &client.definition(&path, text, name),
            &path,
            text,
            &format!("#fn {name}"),
            name,
        );
    }
    let format_params = object([
        ("textDocument", object([("uri", string(uri(&path)))])),
        (
            "options",
            object([("tabSize", number(2)), ("insertSpaces", Json::Bool(true))]),
        ),
    ]);
    let edits = client.request("textDocument/formatting", format_params.clone());
    let edits = edits.array().unwrap();
    assert_eq!(edits.len(), 1);
    assert_eq!(
        edits[0].get("newText"),
        Some(&string(lim::format_source(text).unwrap()))
    );
    assert_eq!(
        edits[0].get("range"),
        Some(&source_range(text, 0, text.len()))
    );
    let emoji = position(text, text.find('😀').unwrap());
    for bad_position in [
        object([("line", number(999)), ("character", number(0))]),
        object([("line", number(0)), ("character", number(999))]),
        object([
            ("line", number(0)),
            (
                "character",
                number(emoji.get("character").unwrap().integer().unwrap() as usize + 1),
            ),
        ]),
        object([
            ("line", Json::Number("-1".into())),
            ("character", number(0)),
        ]),
    ] {
        client.error(
            "textDocument/definition",
            object([
                ("textDocument", object([("uri", string(uri(&path)))])),
                ("position", bad_position),
            ]),
            -32602,
        );
    }
    client.error("unsupported/method", object([]), -32601);
    client.change(&path, 2, ")");
    client.error("textDocument/formatting", format_params.clone(), -32803);
    let diagnostics = client
        .diagnostics(&path)
        .get("diagnostics")
        .unwrap()
        .array()
        .unwrap();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].get("range"), Some(&source_range(")", 0, 1)));
    client.change(&path, 3, text);
    assert_location(
        &client.definition(&path, text, "main"),
        &path,
        text,
        "#fn main",
        "main",
    );
    client.clear(&path);
    client.close(&path);
    client.error("textDocument/documentSymbol", document(&path), -32602);
    client.clear(&path);
    client.open(&path, text);
    assert_eq!(
        client
            .request("textDocument/documentSymbol", document(&path))
            .array()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(fs::read_to_string(&path).unwrap(), text);
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}
