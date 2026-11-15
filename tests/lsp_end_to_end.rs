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
            object([
                ("rootUri", string(uri(root))),
                (
                    "capabilities",
                    object([(
                        "textDocument",
                        object([
                            (
                                "hover",
                                object([("contentFormat", Json::Array(vec![string("markdown")]))]),
                            ),
                            (
                                "signatureHelp",
                                object([(
                                    "signatureInformation",
                                    object([(
                                        "documentationFormat",
                                        Json::Array(vec![string("markdown")]),
                                    )]),
                                )]),
                            ),
                        ]),
                    )]),
                ),
            ]),
        );
        let capabilities = capabilities.get("capabilities").unwrap();
        assert_eq!(
            capabilities.get("positionEncoding"),
            Some(&string("utf-16"))
        );
        for key in [
            "definitionProvider",
            "hoverProvider",
            "documentSymbolProvider",
            "documentFormattingProvider",
        ] {
            assert_eq!(capabilities.get(key), Some(&Json::Bool(true)));
        }
        assert!(capabilities
            .get("signatureHelpProvider")
            .and_then(|provider| provider.get("triggerCharacters"))
            .and_then(Json::array)
            .is_some_and(|triggers| !triggers.is_empty()));
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
    fn at(&mut self, method: &str, path: &Path, text: &str, byte: usize) -> Json {
        self.request(
            method,
            object([
                ("textDocument", object([("uri", string(uri(path)))])),
                ("position", position(text, byte)),
            ]),
        )
    }
    fn hover(&mut self, path: &Path, text: &str, needle: &str, name: &str) -> String {
        self.hover_at(path, text, text.find(needle).unwrap(), name)
    }
    fn hover_at(&mut self, path: &Path, text: &str, byte: usize, name: &str) -> String {
        let result = self.at("textDocument/hover", path, text, byte);
        assert_eq!(
            result.get("range"),
            Some(&source_range(text, byte, byte + name.len())),
            "{name}: {result:?}"
        );
        let contents = result.get("contents").unwrap();
        assert_eq!(contents.get("kind"), Some(&string("markdown")));
        let value = contents.get("value").and_then(Json::string).unwrap();
        assert!(value.starts_with("```lim\n"), "{value}");
        assert!(value.ends_with("```"), "{value}");
        value.to_owned()
    }
    fn signature(&mut self, path: &Path, text: &str, byte: usize) -> Json {
        self.at("textDocument/signatureHelp", path, text, byte)
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
fn library_exports_and_agglutinated_identifiers_have_definition_roles() {
    let fixture = Fixture::new("library-exports");
    let root_text = "(#export Number read)\n(#alias Number = ./implementation.lim::Number)\n(#alias read = ./implementation.lim::read)\n";
    let root = fixture.write("numbers/lib.lim", root_text);
    let implementation_text = "(#type Number #u64)\n(#fn read () Number (#return 42u64))\n";
    let implementation = fixture.write("numbers/implementation.lim", implementation_text);
    let main_text = "(#alias Number = ./numbers/lib.lim::Number)\n(#alias read = ./numbers/lib.lim::read)\n(#fn main () Number (#return (#call read ())))\n";
    let main = fixture.write("main.lim", main_text);
    let mut client = Client::start(&fixture.0);
    client.open(&main, main_text);
    client.open(&root, root_text);
    for (file, text, needle, declaration, name) in [
        (&main, main_text, "Number =", "#type Number", "Number"),
        (&main, main_text, "read =", "#fn read", "read"),
        (&root, root_text, "Number", "#type Number", "Number"),
        (&root, root_text, "read", "#fn read", "read"),
    ] {
        assert_location(
            &client.definition(file, text, needle),
            &implementation,
            implementation_text,
            declaration,
            name,
        );
    }
    assert_eq!(client.definition(&root, root_text, "#export"), Json::Null);
    client.shutdown();
}

#[test]
fn exported_enum_variants_navigate_from_literals_and_borrowed_patterns() {
    let fixture = Fixture::new("library-public-enum");
    let library_text = "(#export Status)\n(#enum Status () ((Status.Open #u64) (Status.Closed)))\n";
    let library = fixture.write("status/lib.lim", library_text);
    let main_text = "(#alias Status = ./status/lib.lim::Status)\n(#fn main () #u64\n  (#let status Status (#enum-literal Status.Open 42u64))\n  (#let view (#ref Status) (#borrow status))\n  (#return (#match view\n    (#case-ref (Status.Open payload) (#deref payload))\n    (#case-ref Status.Closed 0u64))))\n";
    let main = fixture.write("main.lim", main_text);
    fixture.context(&main, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&main, main_text);
    for (needle, name) in [
        ("Status.Open 42u64", "Status.Open"),
        ("Status.Open payload", "Status.Open"),
        ("Status.Closed 0u64", "Status.Closed"),
    ] {
        assert_location(
            &client.definition(&main, main_text, needle),
            &library,
            library_text,
            name,
            name,
        );
    }
    client.shutdown();
}

#[test]
fn file_aliases_and_direct_calls_navigate_to_the_original_declaration() {
    let fixture = Fixture::new("file-alias-navigation");
    let implementation_text = "(#fn read ((value #u64)) #u64 (#return value))\n";
    let implementation = fixture.write("library/implementation.lim", implementation_text);
    fixture.write(
        "library/lib.lim",
        "(#export read)\n(#alias read = ./implementation.lim::read)\n",
    );
    let main_text = "(#alias load = ./library/lib.lim::read)\n(#fn main () #u64 (#return (#u64::add-wrap (#call load ((value 20u64))) (#call ./library/lib.lim::read ((value 22u64))))))\n";
    let main = fixture.write("main.lim", main_text);
    fixture.context(&main, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&main, main_text);
    for needle in [
        "load =",
        "./library/lib.lim::read)",
        "load ((",
        "./library/lib.lim::read ((",
    ] {
        assert_location(
            &client.definition(&main, main_text, needle),
            &implementation,
            implementation_text,
            "#fn read",
            "read",
        );
    }
    for needle in ["#alias", "= ./library"] {
        assert_eq!(client.definition(&main, main_text, needle), Json::Null);
    }
    client.shutdown();
}

#[test]
fn project_root_file_aliases_navigate_from_the_nearest_project_root() {
    let fixture = Fixture::new("project-root-file-alias");
    fs::write(fixture.0.join("lim.project"), "schema-version = 1\nname = \"lsp-root\"\nsource-root = \"src\"\nmodule-path = \"modules\"\n").unwrap();
    let target_text = "(#fn read () #u64 (#return 42u64))\n";
    let target = fixture.write("modules/value.lim", target_text);
    let source =
        "(#alias read = project::modules/value.lim::read)\n(#fn main () #u64 (#return (#call read ())))\n";
    let root = fixture.write("src/main.lim", source);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, source);
    assert_location(
        &client.definition(&root, source, "project::modules/value.lim::read"),
        &target,
        target_text,
        "#fn read",
        "read",
    );
    client.shutdown();
}

#[test]
fn unstable_file_aliases_have_definition_targets() {
    let fixture = Fixture::new("unstable-alias-navigation");
    fixture.write("library/lib.lim", "(#export)\n");
    let implementation_text = "(#fn read () #u64 (#return 42u64))\n";
    let implementation = fixture.write("library/private.lim", implementation_text);
    let main_text = "(#alias load = (#unstable ./library/private.lim::read))\n(#fn main () #u64 (#return (#call load ())))\n";
    let main = fixture.write("main.lim", main_text);
    fixture.context(&main, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&main, main_text);
    for needle in ["load =", "./library/private.lim::read", "load ()"] {
        assert_location(
            &client.definition(&main, main_text, needle),
            &implementation,
            implementation_text,
            "#fn read",
            "read",
        );
    }
    assert_eq!(client.definition(&main, main_text, "#unstable"), Json::Null);
    client.shutdown();
}

#[test]
fn generated_private_helper_references_navigate_to_the_library_implementation() {
    let fixture = Fixture::new("generator-private-authority");
    let library_text = "(#export make)\n(#fn secret () #u64 (#return 42u64))\n(#gn make (name) `((#fn ,name () #u64 (#return (#call secret ())))))\n";
    let library = fixture.write("library/lib.lim", library_text);
    let main_text = "(#alias make = ./library/lib.lim::make)\n(#generate make generated-read)\n(#fn main () #u64 (#return (#call generated-read ())))\n";
    let main = fixture.write("main.lim", main_text);
    fixture.context(&main, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&main, main_text);
    let generated = client.definition(&main, main_text, "generated-read (");
    let path = lsp::uri_to_path(generated.get("uri").unwrap().string().unwrap()).unwrap();
    assert!(path.starts_with(fixture.0.join(".lim/generated")));
    let text = fs::read_to_string(&path).unwrap();
    client.open(&path, &text);
    assert_eq!(
        client.definition(&path, &text, "#generated-context"),
        Json::Null
    );
    assert_location(
        &client.definition(&path, &text, "secret"),
        &library,
        library_text,
        "#fn secret",
        "secret",
    );
    client.shutdown();
}

#[test]
fn repeated_direct_aliases_resolve_to_one_file_declaration_identity() {
    let fixture = Fixture::new("library-instances");
    fixture.write(
        "numbers/lib.lim",
        "(#export Number read) (#alias Number = ./implementation.lim::Number) (#alias read = ./implementation.lim::read)",
    );
    let implementation_text = "(#gn alias (name) `((#type ,name #u64)))\n(#generate alias Number)\n(#fn read () Number (#return 42u64))\n";
    let implementation = fixture.write("numbers/implementation.lim", implementation_text);
    let main_text = "(#alias read = ./numbers/lib.lim::read)\n(#alias same-read = ./numbers/lib.lim::read)\n(#alias Number = ./numbers/lib.lim::Number)\n(#fn main () #u64 (#return (#u64::add-wrap (#call read ()) (#call same-read ()))))\n(#fn number () Number (#return 1u64))\n";
    let main = fixture.write("main.lim", main_text);
    fixture.context(&main, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&main, main_text);
    for needle in ["./numbers/lib.lim::read", "read (", "same-read ("] {
        assert_location(
            &client.definition(&main, main_text, needle),
            &implementation,
            implementation_text,
            "#fn read",
            "read",
        );
    }
    let target = client.definition(&main, main_text, "./numbers/lib.lim::Number");
    let path = lsp::uri_to_path(target.get("uri").and_then(Json::string).unwrap()).unwrap();
    assert!(path.starts_with(fixture.0.join(".lim/generated")));
    let generated = fs::read_to_string(&path).unwrap();
    assert!(generated.starts_with(&format!(
        "// Generated definition invoked at {}:2\n",
        implementation.canonicalize().unwrap().display()
    )));
    assert_location(&target, &path, &generated, "#type Number", "Number");
    assert_eq!(client.definition(&main, main_text, "Number ="), target);
    client.shutdown();
}

#[test]
fn qualified_names_navigate_from_generator_arguments_and_definition_templates() {
    let fixture = Fixture::new("qualified-generator-references");
    let library_text = "(#export make)\n(#fn helper () #u64 (#return 2u64))\n(#gn make (name reader) `((#fn ,name () #u64 (#let base #u64 (#call @helper ())) (#let input #u64 (#call ,reader ())) (#return (#u64::add-wrap base input)))))\n";
    let library = fixture.write("library/lib.lim", library_text);
    let main_text = "(#alias make = ./library/lib.lim::make)\n(#fn callback () #u64 (#return 40u64))\n(#generate make generated-read @callback)\n(#fn main () #u64 (#return (#call generated-read ())))\n";
    let main = fixture.write("main.lim", main_text);
    fixture.context(&main, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&main, main_text);
    assert_location(
        &client.definition(&main, main_text, "@callback"),
        &main,
        main_text,
        "#fn callback",
        "callback",
    );
    client.open(&library, library_text);
    assert_location(
        &client.definition(&library, library_text, "@helper"),
        &library,
        library_text,
        "#fn helper",
        "helper",
    );
    client.shutdown();
}

#[test]
fn transitive_external_imports_cfg_and_unicode_have_exact_navigation_ranges() {
    let fixture = Fixture::new("navigation");
    let leaf_text = "(#type Number #u64)\r\n(#fn glyph () #char (#return #\\😀)) (#fn leaf-value ((value Number)) Number (#return value))\r\n(#struct Holder () ((field Number)))\r\n(#fn inspect-holder ((holder (#ref Holder))) () (#return ()))\r\n";
    let leaf = fixture.write("modules α/leaf #%.lim", leaf_text);
    let bridge_text = "(#alias Number = \"./leaf #%.lim::Number\")\r\n(#alias leaf-value = \"./leaf #%.lim::leaf-value\")\r\n(#cfg-if (#cfg-is #flavor first)\r\n (#fn proxy ((value Number)) Number (#return (#call leaf-value ((value value)))))\r\n (#cfg-else (#fn proxy ((value Number)) Number (#return value))))\r\n";
    let bridge = fixture.write("modules α/bridge.lim", bridge_text);
    let root_text = "(#alias Number = \"./modules α/bridge.lim::Number\")\r\n(#alias proxy = \"./modules α/bridge.lim::proxy\")\r\n(#fn glyph-root () #char (#return #\\😀)) (#fn main () Number (#return (#call proxy ((value 42u64)))))\r\n";
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
            "proxy =",
            &bridge,
            bridge_text,
            "#fn proxy",
            "proxy",
        ),
        (
            &root,
            root_text,
            "Number",
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
        (&root, root_text, "./modules α/bridge.lim::Number", &leaf),
        (&bridge, bridge_text, "leaf #%.lim::Number", &leaf),
    ] {
        let result = client.definition(path, text, needle);
        assert_location(&result, target, leaf_text, "#type Number", "Number");
    }
    assert_location(
        &client.definition(&root, root_text, "value 42"),
        &bridge,
        bridge_text,
        "#fn proxy ((value",
        "value",
    );
    assert_location(
        &client.definition(&bridge, bridge_text, "value value"),
        &leaf,
        leaf_text,
        "((value Number)) Number (#return value)",
        "value",
    );
    for path in [&root, &bridge, &leaf] {
        client.clear(path);
    }
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}

#[test]
fn source_roles_follow_external_member_owners_and_unsaved_import_changes() {
    let fixture = Fixture::new("member-roles");
    let definitions = "(#struct Left () ((value #u64)))\n(#struct Right () ((value #u64)))\n(#fn read ((item (#ref Left))) #u64 (#return (#get item value)))";
    let module = fixture.write("types.lim", definitions);
    let source = "(#alias Left = ./types.lim::Left)\n(#alias Right = ./types.lim::Right)\n(#alias read = ./types.lim::read)\n(#fn main () #u64
      (#let left Left (#struct-literal Left ((value 40u64))))
      (#let right Right (#struct-literal Right ((value 2u64))))
      (#let result #u64 (#u64::add-wrap (#call read ((item (#borrow left)))) (#get right value)))
      (#forget left) (#forget right) (#return result))";
    let root = fixture.write("main.lim", source);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, source);
    client.open(&module, definitions);
    for (path, text, needle, declaration, name) in [
        (
            &module,
            definitions,
            "value)))",
            "#struct Left () ((value",
            "value",
        ),
        (
            &root,
            source,
            "value 2u64",
            "#struct Right () ((value",
            "value",
        ),
        (&root, source, "item (#borrow", "#fn read ((item", "item"),
        (
            &root,
            source,
            "value)))",
            "#struct Right () ((value",
            "value",
        ),
    ] {
        assert_location(
            &client.definition(path, text, needle),
            &module,
            definitions,
            declaration,
            name,
        );
    }
    let updated = format!("// unsaved declaration shift\n// second line\n{definitions}");
    client.change(&module, 2, &updated);
    assert_location(
        &client.definition(&root, source, "value 2u64"),
        &module,
        &updated,
        "#struct Right () ((value",
        "value",
    );
    client.shutdown();
}

#[test]
fn generated_member_parameter_and_view_local_references_use_stable_snapshots() {
    let fixture = Fixture::new("generated-source-roles");
    let source = "(#gn emit () `((#struct Box () ((value #u64)))
      (#fn forward ((value #u64)) #u64 (#return value))))\n(#generate emit)
      (#fn main () #u64
        (#let object Box (#struct-literal Box ((value 42u64))))
        (#let result #u64 (#call forward ((value (#get object value)))))
        (#forget object) (#return result))";
    let root = fixture.write("main.lim", source);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, source);
    let field = client.definition(&root, source, "value 42u64");
    let field_path = lsp::uri_to_path(field.get("uri").unwrap().string().unwrap()).unwrap();
    let field_source = fs::read_to_string(&field_path).unwrap();
    assert_location(&field, &field_path, &field_source, "value #u64", "value");
    let label = client.definition(&root, source, "value (#get");
    let function_path = lsp::uri_to_path(label.get("uri").unwrap().string().unwrap()).unwrap();
    let function_source = fs::read_to_string(&function_path).unwrap();
    assert_location(
        &label,
        &function_path,
        &function_source,
        "value #u64",
        "value",
    );
    client.open(&function_path, &function_source);
    assert_location(
        &client.definition(&function_path, &function_source, "value))"),
        &function_path,
        &function_source,
        "value #u64",
        "value",
    );
    assert!(
        !function_path.parent().unwrap().join(".lim").exists(),
        "following a generated view must not create nested publication directories"
    );
    client.shutdown();
}

#[test]
fn generated_syntax_bundles_keep_their_definition_after_expansion() {
    let fixture = Fixture::new("generated-bundles");
    let source = "(#gn emit () `((#syntax Number (42u64))))\n(#generate emit)\n(#fn main () #u64 (#return (#syntax-splice Number)))\n";
    let root = fixture.write("main.lim", source);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, source);
    let target = client.definition(&root, source, "Number)))");
    assert!(
        target.get("uri").is_some(),
        "{target:?}: {:?}",
        client.messages
    );
    let path = lsp::uri_to_path(target.get("uri").unwrap().string().unwrap()).unwrap();
    let generated = fs::read_to_string(&path).unwrap();
    assert_location(&target, &path, &generated, "#syntax Number", "Number");
    assert!(generated.contains("main.lim:"));
    client.shutdown();
}

#[test]
fn bundled_standard_library_types_and_view_locals_have_real_targets() {
    let fixture = Fixture::new("bundled-source-roles");
    let source = "(#std)\n(#fn main () #usize (#return sYSTEM-ALLOCATION-ALIGNMENT))\n";
    let root = fixture.write("main.lim", source);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, source);
    let target = client.definition(&root, source, "sYSTEM-ALLOCATION-ALIGNMENT");
    let path = lsp::uri_to_path(target.get("uri").unwrap().string().unwrap()).unwrap();
    let bundled = fs::read_to_string(&path).unwrap();
    assert_location(
        &target,
        &path,
        &bundled,
        "#const sYSTEM-ALLOCATION-ALIGNMENT",
        "sYSTEM-ALLOCATION-ALIGNMENT",
    );
    assert!(bundled.starts_with("// Bundled source:"));
    client.open(&path, &bundled);
    assert_location(
        &client.definition(&path, &bundled, "address #usize"),
        &path,
        &bundled,
        "address #usize",
        "address",
    );
    assert!(!path.parent().unwrap().join(".lim").exists());
    client.shutdown();
}

#[test]
fn imported_signature_and_aggregate_type_roles_and_ffi_declarations_navigate() {
    let fixture = Fixture::new("type-roles");
    let module_text = "(#type Number #u64)\n(#extern-fn #abi-c foreign ((value Number)) Number)\n(#unsafe-fn guarded ((value Number)) Number (#return value))\n(#struct Holder () ((field (#ref Number))))\n(#enum Choice () ((Choice.Data (#tuple Number Number)) Choice.Empty))\n(#struct CRecord (#repr-c) ((c-field Number)))\n(#const lIMIT Number 99u64)\n(#static cOUNT Number 42u64)\n(#fn inspect ((holder (#ref Holder)) (choice (#ref Choice)) (record (#ref CRecord))) () (#return ()))\n";
    let module = fixture.write("functions.lim", module_text);
    let root_text = "(#alias Number = ./functions.lim::Number)\n(#alias foreign = ./functions.lim::foreign)\n(#alias guarded = ./functions.lim::guarded)\n(#fn main () Number\n (#let-mut input Number 42u64)\n (#return (#unsafe (#unsafe-call foreign ((value (#unsafe-call guarded ((value input)))))))))\n";
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
            "Number)) Choice.Empty",
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
    for needle in ["#abi-c", "#u64"] {
        assert_eq!(client.definition(&module, module_text, needle), Json::Null);
    }
    assert_location(
        &client.definition(&module, module_text, "value Number"),
        &module,
        module_text,
        "#extern-fn #abi-c foreign ((value",
        "value",
    );
    assert_location(
        &client.definition(&module, module_text, "field ("),
        &module,
        module_text,
        "#struct Holder () ((field",
        "field",
    );
    client.clear(&root);
    client.clear(&module);
    client.shutdown();
}

#[test]
fn unsaved_import_updates_errors_stale_versions_and_close_restore_disk_definitions() {
    let fixture = Fixture::new("updates");
    let disk = "(#fn target () #u64 (#return 42u64))\n";
    let child = fixture.write("child.lim", disk);
    let root_text =
        "(#alias target = ./child.lim::target)\n(#fn main () #u64 (#return (#call target ())))";
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
    let broken = "// unsaved 😀\n\n(#fn target () #u64 (#return false))\n";
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
    let root_text = "(#alias selected = ./selected.lim::selected)\n(#fn main () #u64 (#return (#call selected ())))";
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
fn watched_multi_entry_contexts_keep_direct_file_alias_identity() {
    let fixture = Fixture::new("multi-context-reload");
    let text = "(#fn read-value () #u64 (#return 42u64))";
    let library = fixture.write("library.lim", text);
    let app_text = "(#alias read-value = ./library.lim::read-value)\n(#fn main () #u64 (#return (#call read-value ())))";
    let test_text = app_text.to_owned();
    let app = fixture.write("app.lim", app_text);
    let test = fixture.write("test.lim", &test_text);
    let contexts = [app.clone(), test.clone()].map(|entry| LspContext {
        entry,
        target: TargetDescription::X86_64_SYSTEM_V,
        config: CompileConfig::default(),
    });
    let path = fixture.0.join("lim.lsp");
    LspContext::write_all(&contexts, &path).unwrap();
    let mut client = Client::start(&fixture.0);
    client.open(&app, app_text);
    assert_location(
        &client.definition(&app, app_text, "./library.lim::read-value"),
        &library,
        text,
        "#fn read-value",
        "read-value",
    );
    LspContext::write_all(&contexts[..1], &path).unwrap();
    client.watch(&path);
    assert_location(
        &client.definition(&app, app_text, "./library.lim::read-value"),
        &library,
        text,
        "#fn read-value",
        "read-value",
    );
    client.clear(&app);
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}
#[test]
fn imported_user_and_builtin_generated_definitions_are_safe_stable_snapshots() {
    let fixture = Fixture::new("generated");
    let imported = "(#gn emit (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64)))\n";
    let types = fixture.write("types.lim", imported);
    let root_text = "(#alias emit = ./types.lim::emit)\n(#generate emit Number)\n(#generate #optional ((type Number) (name Maybe)))\n(#fn main () Number (#return 42u64))\n(#fn wrap () Maybe (#return (#call Maybe::construct ((value 42u64)))))";
    let root = fixture.write("main.lim", root_text);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, root_text);
    client.open(&types, imported);
    let alias = client.definition(&root, root_text, "Number (#return");
    let constructor = client.definition(&root, root_text, "Maybe::construct");
    let mut snapshots = Vec::new();
    for (result, name, invocation_line) in
        [(&alias, "Number", 2), (&constructor, "Maybe::construct", 3)]
    {
        let path = lsp::uri_to_path(result.get("uri").unwrap().string().unwrap()).unwrap();
        assert!(path.starts_with(fixture.0.join(".lim/generated")));
        let text = fs::read_to_string(&path).unwrap();
        assert!(text.starts_with(&format!(
            "// Generated definition invoked at {}:{invocation_line}\n",
            root.canonicalize().unwrap().display()
        )));
        let (declaration, target_name) = if name == "Number" {
            ("#type Number".to_owned(), name.to_owned())
        } else {
            let qualified = format!("{}::{name}", root.canonicalize().unwrap().display());
            (format!("#fn {qualified}"), qualified)
        };
        assert_location(result, &path, &text, &declaration, &target_name);
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
        client.definition(&root, root_text, "Maybe::construct"),
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
        client.definition(&root, root_text, "Maybe::construct"),
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
    fs::write(&path, "// deliberate user edit\n").unwrap();
    assert_eq!(
        client.definition(&root, &repaired, "Number (#return"),
        Json::Null
    );
    assert_eq!(
        fs::read_to_string(&path).unwrap(),
        "// deliberate user edit\n"
    );
    assert_eq!(fs::read_to_string(&types).unwrap(), imported);
    assert_eq!(fs::read_to_string(&root).unwrap(), root_text);
    assert!(!fixture.0.join(".lim/cache").exists());
    client.shutdown();
}

#[test]
fn generated_enum_projection_definitions_and_payload_fields_navigate_in_every_mode() {
    for (mode, borrow) in [
        ("ref", "borrow"),
        ("ref-mut", "borrow-mut"),
        ("pin-ref", "pin-borrow"),
        ("pin-ref-mut", "pin-borrow-mut"),
    ] {
        let fixture = Fixture::new("enum-project");
        let text = format!(
            "(#alias lim-gen-enum-project = /<lim-std>/enum_project.lim::#enum-project)\n          (#struct Row () ((value #u64)))\n          (#enum Task () ((Task.Work Row) Task.Idle))\n          (#generate lim-gen-enum-project ((enum Task) (variant Task.Work) (payload Row) (mode #{mode}) (name View)))\n          (#fn main () #u64\n            (#let-mut task Task (#enum-literal Task.Work (#struct-literal Row ((value 42u64)))))\n            (#let-else (View.Some frame)\n              (#call View::project ((source (#{borrow} task))))\n              (#else (#forget task) (#return 0u64)))\n            (#let answer #u64 (#get frame value))\n            (#forget frame) (#forget task) (#return answer))"
        );
        let root = fixture.write("main.lim", &text);
        fixture.context(&root, "first");
        let mut client = Client::start(&fixture.0);
        client.open(&root, &text);
        assert_location(
            &client.definition(&root, &text, "Task.Work (#struct-literal"),
            &root,
            &text,
            "(Task.Work Row)",
            "Task.Work",
        );
        for (name, declaration) in [
            ("View.Some", "(View.Some"),
            ("View::project", "#fn View::project"),
        ] {
            let result = client.definition(&root, &text, name);
            let path = lsp::uri_to_path(result.get("uri").unwrap().string().unwrap()).unwrap();
            assert!(
                path.starts_with(fixture.0.join(".lim/generated")),
                "{result:?}"
            );
            let generated = fs::read_to_string(&path).unwrap();
            assert_location(&result, &path, &generated, declaration, name);
        }
        assert_location(
            &client.definition(&root, &text, "frame value"),
            &root,
            &text,
            "(View.Some frame)",
            "frame",
        );
        assert_location(
            &client.definition(&root, &text, "value))"),
            &root,
            &text,
            "((value #u64))",
            "value",
        );
    }
}

#[test]
fn same_spelled_declarations_keep_direct_file_identity_in_navigation() {
    let fixture = Fixture::new("direct-file-identity");
    let first_text = "(#fn target () #u64 (#return 20u64))";
    let first = fixture.write("first.lim", first_text);
    let second_text = "(#fn target () #u64 (#return 22u64))";
    let second = fixture.write("second.lim", second_text);
    let source = "(#alias first-target = ./first.lim::target) (#alias second-target = ./second.lim::target)\n(#fn main () #u64 (#return (#u64::add-wrap (#call first-target ()) (#call second-target ()))))";
    let root = fixture.write("main.lim", source);
    fixture.context(&root, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&root, source);
    assert_location(
        &client.definition(&root, source, "./first.lim::target"),
        &first,
        first_text,
        "#fn target",
        "target",
    );
    assert_location(
        &client.definition(&root, source, "./second.lim::target"),
        &second,
        second_text,
        "#fn target",
        "target",
    );
    assert_location(
        &client.definition(&root, source, "first-target ("),
        &first,
        first_text,
        "#fn target",
        "target",
    );
    assert_location(
        &client.definition(&root, source, "second-target ("),
        &second,
        second_text,
        "#fn target",
        "target",
    );
    client.clear(&root);
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
                object([("uri", string("https:project::example.invalid/main.lim"))]),
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

fn assert_signature(result: &Json, callee: &str, parameters: &[&str], active: Option<usize>) {
    let signatures = result
        .get("signatures")
        .and_then(Json::array)
        .unwrap_or_else(|| panic!("missing signature for {callee}: {result:?}"));
    assert_eq!(signatures.len(), 1, "{result:?}");
    assert_eq!(result.get("activeSignature"), Some(&number(0)));
    let signature = &signatures[0];
    let label = signature.get("label").and_then(Json::string).unwrap();
    assert!(label.contains(callee), "{result:?}");
    let displayed = signature.get("parameters").and_then(Json::array).unwrap();
    assert_eq!(displayed.len(), parameters.len(), "{result:?}");
    for (parameter, expected) in displayed.iter().zip(parameters) {
        let parameter = parameter.get("label").and_then(Json::string).unwrap();
        assert!(parameter.contains(expected), "{expected}: {result:?}");
        assert!(label.contains(parameter), "{result:?}");
    }
    if let Some(active) = active {
        assert_eq!(
            result.get("activeParameter"),
            Some(&number(active)),
            "{result:?}"
        );
    }
}

#[test]
fn hover_reports_explicit_lexical_member_and_contract_information_over_stdio() {
    let fixture = Fixture::new("hover-information");
    let source = "(#struct Left () ((value #u8)))
      (#struct Right () ((value #u64)))
      (#fn valid ((subject #u64)) #bool (#return true))
      (#fn inspect ((input #u64) (row (#ref Right))) #u64
        (#requires (#call valid ((subject input))))
        (#ensures (#call valid ((subject (#result)))))
        (#preserves (#call valid ((subject input))))
        (#let answer #u64 (#get row value))
        (#return answer))
      (#fn show ((input #u64) (row (#ref Right))) #u64
        (#return (#call inspect ((row row) (input input)))))
      (#fn other ((input #u8)) #u8 (#return input))";
    let path = fixture.write("main.lim", source);
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    for (needle, name, ty) in [
        ("input))))", "input", "#u64"),
        ("row value", "row", "(#ref Right)"),
        ("value))", "value", "#u64"),
        ("answer))", "answer", "#u64"),
    ] {
        let hover = client.hover(&path, source, needle, name);
        assert!(hover.contains(name), "{hover}");
        assert!(hover.contains(ty), "{hover}");
    }
    assert!(client
        .hover_at(&path, source, source.rfind("input").unwrap(), "input")
        .contains("#u8"));
    let function = client.hover(&path, source, "inspect", "inspect");
    for part in [
        "input",
        "#u64",
        "row",
        "(#ref Right)",
        "#requires",
        "#ensures",
        "#preserves",
        "valid",
        "#result",
    ] {
        assert!(function.contains(part), "missing {part}: {function}");
    }
    let signature = client.signature(&path, source, source.find("subject input").unwrap() + 8);
    assert_signature(&signature, "valid", &["subject"], Some(0));
    let signature = client.signature(&path, source, source.find("row row").unwrap() + 4);
    assert_signature(&signature, "inspect", &["input", "row"], Some(1));
    let docs = signature.get("signatures").unwrap().array().unwrap()[0]
        .get("documentation")
        .unwrap()
        .get("value")
        .unwrap()
        .string()
        .unwrap();
    for contract in ["#requires", "#ensures", "#preserves", "valid", "#result"] {
        assert!(docs.contains(contract), "{docs}");
    }
    for needle in ["#requires", "#result", "#return answer", "true", "#u8"] {
        assert_eq!(
            client.at(
                "textDocument/hover",
                &path,
                source,
                source.find(needle).unwrap()
            ),
            Json::Null,
            "{needle}"
        );
    }
    // The local declaration remains available through an unrelated semantic error.
    let broken = format!("{source}\n(#fn broken () #u64 (#return false))");
    client.change(&path, 2, &broken);
    assert!(client
        .hover(&path, &broken, "answer))", "answer")
        .contains("#u64"));
    assert_eq!(fs::read_to_string(&path).unwrap(), source);
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}

#[test]
fn signature_help_uses_named_parameter_order_for_all_call_spellings_over_stdio() {
    let fixture = Fixture::new("signature-spellings");
    let declarations = "(#fn choose ((first #u64) (second #u64)) #u64 (#return first))\n";
    let path = fixture.write("main.lim", declarations);
    let mut client = Client::start(&fixture.0);
    client.open(&path, declarations);
    let bodies = [
        "(#fn main () #u64 (#return (#call choose ((second 2u64) (first 1u64)))))",
        "(#fn main () #u64 (#return (choose ((second 2u64) (first 1u64)))))",
        "(#fn main () #u64 (#return (choose { second = 2u64; first = 1u64; })))",
        "(#fn main () #u64 (#return choose { second = 2u64; first = 1u64; }))",
        "(#fn main () #u64 (#return (#call choose { second = 2u64; first = 1u64; })))",
        "(#fn main () #u64 (#return : choose : (second 2u64) (first 1u64)))",
        "#fn main {\n  #params = {}; #returns = #u64;\n  #body:\n    #return choose {\n      second = 2u64;\n      first = 1u64;\n    };\n}\n",
        "#fn main {\n  #params = {}; #returns = #u64;\n  #body:\n    #return choose {\n      second:\n        #block 2u64\n      first = 1u64;\n    };\n}\n",
    ];
    for (version, body) in bodies.iter().enumerate() {
        let source = format!("{declarations}{body}");
        let program = lim::parse_program(&source)
            .unwrap_or_else(|error| panic!("cannot parse call fixture {body}: {error}"));
        lim::check_types(&program)
            .unwrap_or_else(|error| panic!("invalid call fixture {body}: {error}"));
        client.change(&path, version + 2, &source);
        // The cursor is exactly after the operand, including for indented values.
        let signature =
            client.signature(&path, &source, source.find("2u64").unwrap() + "2u64".len());
        assert_signature(&signature, "choose", &["first", "second"], Some(1));
        assert!(signature.get("signatures").unwrap().array().unwrap()[0]
            .get("label")
            .unwrap()
            .string()
            .unwrap()
            .contains("#u64"));
        client.clear(&path);
    }
    let puns = format!("{declarations}(#fn main () #u64 (#let first #u64 1u64) (#let second #u64 2u64) (#return (#call choose (($ second) ($ first)))))");
    lim::check_types(&lim::parse_program(&puns).unwrap()).unwrap();
    client.change(&path, 20, &puns);
    let signature = client.signature(&path, &puns, puns.find("$ second").unwrap() + 3);
    assert_signature(&signature, "choose", &["first", "second"], Some(1));
    let unsafe_source = "(#extern-fn #abi-c foreign ((first #u64) (second #u64)) #u64)\n(#fn main () #u64 (#return (#unsafe (#unsafe-call foreign ((second 2u64) (first 1u64))))))";
    lim::check_types(&lim::parse_program(unsafe_source).unwrap()).unwrap();
    client.change(&path, 21, unsafe_source);
    let signature = client.signature(
        &path,
        unsafe_source,
        unsafe_source.find("2u64").unwrap() + 2,
    );
    assert_signature(&signature, "foreign", &["first", "second"], Some(1));
    let nested = format!("{declarations}(#fn inner ((value #u64)) #u64 (#return value))\n(#fn main () #u64 (#return (#call choose ((second (#call inner ((value 2u64)))) (first 1u64)))))");
    client.change(&path, 22, &nested);
    let signature = client.signature(&path, &nested, nested.find("2u64").unwrap() + 2);
    assert_signature(&signature, "inner", &["value"], Some(0));
    let signature = client.signature(&path, &nested, nested.find("first 1u64").unwrap() + 7);
    assert_signature(&signature, "choose", &["first", "second"], Some(0));
    assert_eq!(client.signature(&path, &nested, nested.len()), Json::Null);
    client.clear(&path);
    // Display-only metadata remains available in an erroneous buffer. The
    // compiler's restriction on bare keyword heads must remain a diagnostic.
    let bare_keyword = "(#fn type ((value #u64)) #u64 (#return value))\n(#fn main () #u64 (#return (type ((value 42u64)))))";
    assert!(lim::parse_program(bare_keyword).is_err());
    client.change(&path, 23, bare_keyword);
    assert_signature(
        &client.signature(&path, bare_keyword, bare_keyword.find("42u64").unwrap()),
        "type",
        &["value"],
        Some(0),
    );
    assert!(client
        .hover(&path, bare_keyword, "type ((value 42", "type")
        .contains("#u64"));
    assert!(client
        .diagnostics(&path)
        .render()
        .contains("must use its '#' prefix"));
    client.shutdown();
}

#[test]
fn signature_help_recovers_unclosed_calls_without_writing_buffers_over_stdio() {
    let fixture = Fixture::new("signature-incomplete");
    let declarations = "(#fn choose ((first #u64) (second #u64)) #u64 (#return first))\n";
    let path = fixture.write("main.lim", declarations);
    let mut client = Client::start(&fixture.0);
    client.open(&path, declarations);
    for (version, suffix) in [
        "(#fn main () #u64 (#return (#call choose ",
        "(#fn main () #u64 (#return (#call choose ((second ",
        "(#fn main () #u64 (#return (#call choose ((second 2u64) (first ",
        "(#fn main () #u64 (#return (choose { second = ",
        "(#fn main () #u64 (#return : choose : : second ",
    ]
    .iter()
    .enumerate()
    {
        let source = format!("{declarations}{suffix}");
        assert!(lim::parse(&source).is_err());
        client.change(&path, version + 2, &source);
        let signature = client.signature(&path, &source, source.len());
        let active = if suffix.contains("(first ") {
            Some(0)
        } else if suffix.contains("second") {
            Some(1)
        } else {
            None
        };
        assert_signature(&signature, "choose", &["first", "second"], active);
        assert_eq!(fs::read_to_string(&path).unwrap(), declarations);
    }
    let restored = format!(
        "{declarations}(#fn main () #u64 (#return (#call choose ((second 2u64) (first 1u64)))))"
    );
    client.change(&path, 10, &restored);
    assert_signature(
        &client.signature(&path, &restored, restored.find("2u64").unwrap()),
        "choose",
        &["first", "second"],
        Some(1),
    );
    client.clear(&path);
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}

#[test]
fn hover_and_signature_follow_aliases_unsaved_dependencies_and_generated_metadata_over_stdio() {
    let fixture = Fixture::new("information-metadata");
    let disk = "(#fn original ((amount #u8) (other #u16)) #u32 (#return 0u32))";
    let dependency = fixture.write("dependency.lim", disk);
    fixture.write(
        "facade.lim",
        "(#alias forwarded = ./dependency.lim::original)",
    );
    let source = "(#alias renamed = ./facade.lim::forwarded)\n(#fn main () #u32 (#return (#call renamed ((other 2u64) (amount 1u64)))))";
    let path = fixture.write("main.lim", source);
    fixture.context(&path, "first");
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    let unsaved = "// unsaved API\n(#fn original ((amount #u64) (other #u64)) #u32 (#return 0u32))";
    client.open(&dependency, unsaved);
    let hover = client.hover(&path, source, "renamed ((", "renamed");
    for part in ["amount", "other", "#u64", "#u32"] {
        assert!(hover.contains(part), "{hover}");
    }
    assert!(!hover.contains("#u8"), "{hover}");
    let signature = client.signature(&path, source, source.find("2u64").unwrap());
    assert_signature(&signature, "original", &["amount", "other"], Some(1));
    assert!(signature.get("signatures").unwrap().array().unwrap()[0]
        .get("label")
        .unwrap()
        .string()
        .unwrap()
        .contains("#u32"));
    assert!(client
        .hover(&path, source, "other 2u64", "other")
        .contains("#u64"));
    client.clear(&path);
    assert_eq!(fs::read_to_string(&dependency).unwrap(), disk);
    assert!(!fixture.0.join(".lim").exists());
    client.close(&dependency);
    let generated = "(#gn emit () `((#fn produced ((value #u64)) #u64 (#return value))))\n(#generate emit)\n(#fn main () #u64 (#return (#call produced ((value 42u64)))))";
    client.change(&path, 2, generated);
    assert!(client
        .hover(&path, generated, "produced ((value 42", "produced")
        .contains("#u64"));
    assert!(client
        .hover(&path, generated, "value 42u64", "value")
        .contains("#u64"));
    assert_signature(
        &client.signature(&path, generated, generated.find("42u64").unwrap()),
        "produced",
        &["value"],
        Some(0),
    );
    client.clear(&path);
    let prefix = &generated[..generated.find("(#fn main").unwrap()];
    for (version, suffix) in [
        "(#fn main () #u64 (#return (#call produced ",
        "(#fn main () #u64 (#return (produced { value = ",
    ]
    .iter()
    .enumerate()
    {
        let incomplete = format!("{prefix}{suffix}");
        client.change(&path, version + 3, &incomplete);
        assert_signature(
            &client.signature(&path, &incomplete, incomplete.len()),
            "produced",
            &["value"],
            suffix.contains("value").then_some(0),
        );
    }
    fixture.write("emitted.lim", prefix);
    let incomplete_alias =
        "(#alias renamed = ./emitted.lim::produced)\n(#fn main () #u64 (#return (#call renamed ";
    client.change(&path, 5, incomplete_alias);
    assert_signature(
        &client.signature(&path, incomplete_alias, incomplete_alias.len()),
        "produced",
        &["value"],
        None,
    );
    assert!(
        !fixture.0.join(".lim").exists(),
        "information requests must not publish generated snapshots"
    );
    client.shutdown();
}

#[test]
fn information_requests_preserve_utf16_ranges_and_reject_invalid_positions_over_stdio() {
    let fixture = Fixture::new("information-utf16");
    let source = "(#fn glyph () #char (#return #\\😀)) (#fn combine ((left😀 #u64) (right #u64)) #u64 (#return left😀))\r\n(#fn main () #u64 (#return (#call combine ((right 2u64) (left😀 1u64)))))";
    let path = fixture.write("editor 😀.lim", source);
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    assert!(client
        .hover(&path, source, "left😀))", "left😀")
        .contains("#u64"));
    assert!(client
        .hover(&path, source, "left😀 1u64", "left😀")
        .contains("#u64"));
    assert_signature(
        &client.signature(&path, source, source.find("1u64").unwrap() + 1),
        "combine",
        &["left😀", "right"],
        Some(0),
    );
    let emoji = position(source, source.find('😀').unwrap());
    for method in ["textDocument/hover", "textDocument/signatureHelp"] {
        for invalid in [
            object([("line", number(99)), ("character", number(0))]),
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
                method,
                object([
                    ("textDocument", object([("uri", string(uri(&path)))])),
                    ("position", invalid),
                ]),
                -32602,
            );
        }
    }
    client.clear(&path);
    client.shutdown();
}

#[test]
fn information_requests_ignore_comments_strings_and_generator_data_over_stdio() {
    let fixture = Fixture::new("information-inert-data");
    let source = "(#fn choose ((value #u64)) #u64 (#return value))\n(#gn data () '(#call choose ((value 7u64))))\n(#generate unknown ((payload (#call choose ((value 8u64))))))\n(#fn main () #u64\n  // (#call choose ((value 9u64)))\n  (#println \"(#call choose ((value 10u64)))\")\n  (#return (#call choose ((value 42u64)))))";
    let path = fixture.write("main.lim", source);
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    for marker in ["7u64", "8u64", "9u64", "10u64"] {
        let byte = source.find(marker).unwrap();
        assert_eq!(
            client.signature(&path, source, byte),
            Json::Null,
            "{marker}"
        );
        let callee = source[..byte].rfind("choose").unwrap();
        assert_eq!(
            client.at("textDocument/hover", &path, source, callee),
            Json::Null,
            "{marker}"
        );
    }
    client.shutdown();
}

#[test]
fn information_requests_keep_context_alternatives_and_cfg_exclusions_over_stdio() {
    let fixture = Fixture::new("information-contexts");
    let source = "(#cfg-if (#cfg-is #flavor first)
      (#type Number #u8)
      (#cfg-else (#type Number #u64)))
      (#cfg-if (#cfg-is #flavor first)
        (#fn choose ((left #u8) (right #u8)) #u8 (#return left))
        (#cfg-else (#fn choose ((left #u64) (right #u64)) #u64 (#return left))))
      (#fn use ((left Number) (right Number)) Number
        (#return (#call choose ((right right) (left left)))))";
    let shared = fixture.write("shared.lim", source);
    let first = fixture.write("first.lim", "(#alias use = ./shared.lim::use) (#fn main () #u8 (#return (#call use ((right 2u8) (left 1u8)))))");
    let second = fixture.write("second.lim", "(#alias use = ./shared.lim::use) (#fn main () #u64 (#return (#call use ((right 2u64) (left 1u64)))))");
    let broken = fixture.write("broken.lim", ")");
    let contexts =
        [(first, "first"), (second, "second"), (broken, "broken")].map(|(entry, flavor)| {
            let mut config = CompileConfig::default();
            config.set("flavor", flavor);
            LspContext {
                entry,
                config,
                target: TargetDescription::X86_64_SYSTEM_V,
            }
        });
    let manifest = fixture.0.join("lim.lsp");
    LspContext::write_all(&contexts, &manifest).unwrap();
    let mut client = Client::start(&fixture.0);
    client.open(&shared, source);
    let hover = client.hover(&shared, source, "choose ((right right", "choose");
    for ty in ["#u8", "#u64"] {
        assert!(hover.contains(ty), "{hover}");
    }
    let result = client.signature(&shared, source, source.find("right right").unwrap() + 7);
    let signatures = result.get("signatures").unwrap().array().unwrap();
    assert_eq!(signatures.len(), 2, "{result:?}");
    for ty in ["#u8", "#u64"] {
        let signature = signatures
            .iter()
            .find(|signature| {
                signature
                    .get("label")
                    .unwrap()
                    .string()
                    .unwrap()
                    .contains(ty)
            })
            .unwrap();
        assert_eq!(
            signature.get("activeParameter"),
            Some(&number(1)),
            "{result:?}"
        );
    }
    // Selecting only the second context hides declarations in the first branch.
    LspContext::write_all(&contexts[1..2], &manifest).unwrap();
    client.watch(&manifest);
    assert_eq!(
        client.at(
            "textDocument/hover",
            &shared,
            source,
            source.find("choose ((left #u8").unwrap()
        ),
        Json::Null
    );
    let hover = client.hover(&shared, source, "choose ((right right", "choose");
    assert!(hover.contains("#u64"), "{hover}");
    assert!(!hover.contains("#u8"), "{hover}");
    assert_signature(
        &client.signature(&shared, source, source.find("right right").unwrap() + 7),
        "choose",
        &["left", "right"],
        Some(1),
    );
    client.shutdown();
}

#[test]
fn intrinsic_information_uses_compiler_signatures_without_definition_targets_over_stdio() {
    let fixture = Fixture::new("information-intrinsics");
    let source = "(#fn main () #u64 (#return (#call #u64::add-wrap ((right 2u64) (left 1u64)))))";
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let path = fixture.write("main.lim", source);
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    let hover = client.hover(&path, source, "#u64::add-wrap", "#u64::add-wrap");
    for part in ["#u64::add-wrap", "left", "right", "#u64"] {
        assert!(hover.contains(part), "{hover}");
    }
    assert!(client
        .hover(&path, source, "right 2u64", "right")
        .contains("#u64"));
    assert_signature(
        &client.signature(&path, source, source.find("2u64").unwrap()),
        "#u64::add-wrap",
        &["left", "right"],
        Some(1),
    );
    assert_eq!(
        client.definition(&path, source, "#u64::add-wrap"),
        Json::Null
    );
    assert_eq!(client.definition(&path, source, "right 2u64"), Json::Null);
    client.clear(&path);
    let positional = "(#fn main () #u64 (#return (#u64::add-wrap 1u64 2u64)))";
    lim::check_types(&lim::parse_program(positional).unwrap()).unwrap();
    client.change(&path, 2, positional);
    let hover = client.hover(&path, positional, "#u64::add-wrap", "#u64::add-wrap");
    for part in ["left", "right", "#u64"] {
        assert!(hover.contains(part), "{hover}");
    }
    assert_signature(
        &client.signature(&path, positional, positional.find("2u64").unwrap() + 2),
        "#u64::add-wrap",
        &["left", "right"],
        Some(1),
    );
    assert_eq!(
        client.definition(&path, positional, "#u64::add-wrap"),
        Json::Null
    );
    let direct_outer = "(#fn inner ((value #u64)) #u64 (#return value))\n(#fn main () #u64 (#return (#u64::add-wrap 1u64 (#call inner ((value 2u64))))))";
    lim::check_types(&lim::parse_program(direct_outer).unwrap()).unwrap();
    client.change(&path, 3, direct_outer);
    assert_signature(
        &client.signature(&path, direct_outer, direct_outer.find("2u64").unwrap()),
        "inner",
        &["value"],
        Some(0),
    );
    assert_signature(
        &client.signature(&path, direct_outer, direct_outer.find("1u64").unwrap()),
        "#u64::add-wrap",
        &["left", "right"],
        Some(0),
    );
    let direct_inner = "(#fn outer ((value #u64)) #u64 (#return value))\n(#fn main () #u64 (#return (#call outer ((value (#u64::add-wrap 1u64 2u64))))))";
    lim::check_types(&lim::parse_program(direct_inner).unwrap()).unwrap();
    client.change(&path, 4, direct_inner);
    assert_signature(
        &client.signature(&path, direct_inner, direct_inner.find("2u64").unwrap()),
        "#u64::add-wrap",
        &["left", "right"],
        Some(1),
    );
    let infix = "(#fn outer ((value #u64)) #u64 (#return value))\n(#fn main () #u64 (#return (#call outer ((value [#u64 #wrap; 1u64 + 2u64])))))";
    lim::check_types(&lim::parse_program(infix).unwrap()).unwrap();
    client.change(&path, 5, infix);
    // Lowered arithmetic has no authored callee: its enclosing call remains active.
    for byte in [infix.find('+').unwrap(), infix.find("2u64").unwrap()] {
        assert_signature(
            &client.signature(&path, infix, byte),
            "outer",
            &["value"],
            Some(0),
        );
    }
    assert_eq!(
        client.at("textDocument/hover", &path, infix, infix.find('+').unwrap()),
        Json::Null
    );
    let standalone_infix = "(#fn main () #u64 (#return [#u64 #wrap; 1u64 + 2u64]))";
    client.change(&path, 6, standalone_infix);
    let operator = standalone_infix.find('+').unwrap();
    assert_eq!(
        client.signature(&path, standalone_infix, operator),
        Json::Null
    );
    assert_eq!(
        client.at("textDocument/hover", &path, standalone_infix, operator),
        Json::Null
    );
    client.clear(&path);
    client.shutdown();
}

#[test]
fn hover_uses_tuple_and_match_payload_binding_types_over_stdio() {
    let fixture = Fixture::new("hover-pattern-bindings");
    let source = "(#enum Choice () ((Choice.Full #u16) Choice.Empty))
      (#fn tuple () #u64
        (#let (#tuple small large) (#tuple #u8 #u64)
          (#tuple (#tuple #u8 #u64) 1u8 2u64))
        (#forget small)
        (#return large))
      (#fn payload ((choice Choice)) #u16
        (#return (#match choice
          (#case (Choice.Full value) value)
          (#case Choice.Empty 0u16))))";
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let path = fixture.write("main.lim", source);
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    for (needle, name, ty) in [
        ("small large", "small", "#u8"),
        ("large) (#tuple", "large", "#u64"),
        ("small)", "small", "#u8"),
        ("large))", "large", "#u64"),
        ("value) value", "value", "#u16"),
        ("value)\n", "value", "#u16"),
    ] {
        let hover = client.hover(&path, source, needle, name);
        assert!(hover.contains(ty), "{hover}");
    }
    client.clear(&path);
    // Invalid enum or-patterns still retain unambiguous source binding metadata.
    let or_pattern = "(#enum Alternative () ((Alternative.First #u32) (Alternative.Second #u32)))
      (#fn either ((item Alternative)) #u32
        (#return (#match item
          (#case (#or (Alternative.First shared) (Alternative.Second shared)) shared))))";
    client.change(&path, 2, or_pattern);
    let shared = client.hover_at(
        &path,
        or_pattern,
        or_pattern.rfind("shared").unwrap(),
        "shared",
    );
    assert!(shared.contains("#u32"), "{shared}");
    assert!(client
        .diagnostics(&path)
        .render()
        .contains("or-pattern alternatives cannot bind values"));
    client.shutdown();
}

#[test]
fn information_requests_reject_ambiguous_globals_and_out_of_scope_locals_over_stdio() {
    let fixture = Fixture::new("information-ambiguity");
    let source = "(#fn choose ((value #u8)) #u8 (#return value))
      (#fn choose ((value #u64)) #u64 (#return value))
      (#fn main () #u64
        (#forget later)
        (#let later #u64 1u64)
        (#block (#let inside #u64 2u64) (#forget inside))
        (#forget inside)
        (#return (#call choose ((value later)))))";
    let path = fixture.write("main.lim", source);
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    for byte in [
        source.find("later)").unwrap(),
        source.rfind("inside)").unwrap(),
        source.find("choose ((value later").unwrap(),
    ] {
        assert_eq!(
            client.at("textDocument/hover", &path, source, byte),
            Json::Null
        );
    }
    assert_eq!(
        client.signature(&path, source, source.rfind("later").unwrap()),
        Json::Null
    );
    assert!(client
        .hover_at(&path, source, source.rfind("later").unwrap(), "later")
        .contains("#u64"));
    assert!(client
        .hover(&path, source, "inside))", "inside")
        .contains("#u64"));
    client.shutdown();
}

#[test]
fn record_function_contracts_and_refinement_named_calls_have_information_over_stdio() {
    let fixture = Fixture::new("information-record-contracts");
    let source = "#fn acceptable {
  #params = { value = #u64; };
  #returns = #bool;
  #body: #return true;
}
#fn identity {
  #params = { value = #u64; };
  #returns = #u64;
  #requires:
    acceptable { value = value; };
  #ensures:
    acceptable { value = (#result); };
  #body:
    #return value;
}
(#type Small (#where (subject #u64) (acceptable { value = subject; })))
#fn main {
  #params = {}; #returns = #u64;
  #body:
    #let input #u64 42;
    #assume acceptable { value = input; };
    #return identity { value = input; };
}
";
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let path = fixture.write("main.lim", source);
    let mut client = Client::start(&fixture.0);
    client.open(&path, source);
    let hover = client.hover(&path, source, "identity", "identity");
    for part in [
        "value",
        "#u64",
        "#requires",
        "#ensures",
        "acceptable",
        "#result",
    ] {
        assert!(hover.contains(part), "{hover}");
    }
    let signature = client.signature(
        &path,
        source,
        source.rfind("input;").unwrap() + "input".len(),
    );
    assert_signature(&signature, "identity", &["value"], Some(0));
    let documentation = signature.get("signatures").unwrap().array().unwrap()[0]
        .get("documentation")
        .unwrap()
        .get("value")
        .unwrap()
        .string()
        .unwrap();
    for contract in ["#requires", "#ensures", "acceptable", "#result"] {
        assert!(documentation.contains(contract), "{documentation}");
    }
    let signature = client.signature(
        &path,
        source,
        source.find("subject;").unwrap() + "subject".len(),
    );
    assert_signature(&signature, "acceptable", &["value"], Some(0));
    assert!(client
        .hover(&path, source, "subject;", "subject")
        .contains("#u64"));
    assert!(client
        .hover(&path, source, "value = subject", "value")
        .contains("#u64"));
    let diagnostics = client
        .diagnostics(&path)
        .get("diagnostics")
        .unwrap()
        .array()
        .unwrap();
    assert!(diagnostics
        .iter()
        .all(|diagnostic| diagnostic.get("severity") == Some(&number(2))));
    assert!(diagnostics.iter().any(
        |diagnostic| diagnostic.get("code") == Some(&string("W8000"))
            && diagnostic
                .get("message")
                .unwrap()
                .string()
                .unwrap()
                .contains("Small")
    ));
    assert!(!fixture.0.join(".lim").exists());
    client.shutdown();
}
