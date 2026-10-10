//! Synchronous, std-only LSP server. Checks never save editor buffers.
#[path = "lsp_json.rs"]
pub mod json;

use crate::diagnostic_json::quoted;
use crate::{CompileConfig, Diagnostic, Expr, Span, SpannedExpr};
use json::Json;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    io::{self, BufRead, Write},
    path::{Path, PathBuf},
};

#[derive(Clone)]
struct Document {
    path: PathBuf,
    text: String,
    version: i64,
}

/// Run on stdin/stdout. The caller should exit with the returned status.
/// I/O/framing errors are returned for reporting on stderr only.
pub fn run(config: &CompileConfig) -> io::Result<i32> {
    serve(io::stdin().lock(), io::stdout().lock(), config)
}

/// Same protocol loop with injectable streams; no logging is written to output.
pub fn serve(
    mut input: impl BufRead,
    mut output: impl Write,
    config: &CompileConfig,
) -> io::Result<i32> {
    let mut server = Server {
        config,
        documents: HashMap::new(),
        published: BTreeSet::new(),
        initialized: false,
        ready: false,
        shutdown: false,
        context_watch: false,
        root: None,
    };
    while let Some(body) = json::read_frame(&mut input)? {
        let message = match json::parse(&body) {
            Ok(value) => value,
            Err(_) => {
                error(&mut output, &Json::Null, -32700, "Parse error")?;
                continue;
            }
        };
        let id = message.get("id");
        if server.context_watch
            && id.and_then(Json::string) == Some("lim-context-watch")
            && message.get("jsonrpc").and_then(Json::string) == Some("2.0")
            && message.get("method").is_none()
            && (message.get("result").is_some() || message.get("error").is_some())
        {
            continue;
        }
        let valid_id = id
            .is_none_or(|id| matches!(id, Json::Null | Json::String(_)) || id.integer().is_some());
        let method = message.get("method").and_then(Json::string);
        if !valid_id
            || message.get("jsonrpc").and_then(Json::string) != Some("2.0")
            || method.is_none()
        {
            error(&mut output, &Json::Null, -32600, "Invalid Request")?;
            continue;
        }
        let method = method.unwrap();
        let params = message.get("params").unwrap_or(&Json::Null);
        if method == "exit" && id.is_none() {
            return Ok(if server.shutdown { 0 } else { 1 });
        }
        if let Some(id) = id {
            if method == "initialize" && !server.initialized && !server.shutdown {
                if !matches!(params, Json::Object(_)) {
                    error(&mut output, id, -32602, "Invalid params")?;
                    continue;
                }
                server.initialized = true;
                server.root = params
                    .get("rootUri")
                    .and_then(Json::string)
                    .and_then(uri_to_path);
                server.context_watch = matches!(
                    params
                        .get("capabilities")
                        .and_then(|p| p.get("workspace"))
                        .and_then(|p| p.get("didChangeWatchedFiles"))
                        .and_then(|p| p.get("dynamicRegistration")),
                    Some(Json::Bool(true))
                );
                result(
                    &mut output,
                    id,
                    r#"{"capabilities":{"positionEncoding":"utf-16","textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":true}},"documentFormattingProvider":true,"documentSymbolProvider":true,"definitionProvider":true},"serverInfo":{"name":"lim","version":"0.1.0"}}"#,
                )?;
            } else if !server.initialized {
                error(&mut output, id, -32002, "Server not initialized")?;
            } else if server.shutdown || method == "initialize" {
                error(&mut output, id, -32600, "Invalid Request")?;
            } else if method == "shutdown" {
                if !matches!(params, Json::Null) {
                    error(&mut output, id, -32602, "Invalid params")?;
                    continue;
                }
                server.shutdown = true;
                result(&mut output, id, "null")?;
            } else {
                match server.request(method, params) {
                    Ok(value) => result(&mut output, id, &value)?,
                    Err((code, message)) => error(&mut output, id, code, message)?,
                }
            }
        } else if server.initialized && !server.shutdown {
            if method == "initialized" && matches!(params, Json::Object(_)) {
                if !server.ready {
                    server.ready = true;
                    if server.context_watch {
                        json::write_frame(
                            &mut output,
                            r#"{"jsonrpc":"2.0","id":"lim-context-watch","method":"client/registerCapability","params":{"registrations":[{"id":"lim-context-watch","method":"workspace/didChangeWatchedFiles","registerOptions":{"watchers":[{"globPattern":"**/lim.lsp","kind":7}]}}]}}"#,
                        )?;
                    }
                }
            } else if server.ready && server.notification(method, params) {
                server.diagnostics(&mut output)?;
            }
        }
    }
    Ok(if server.shutdown { 0 } else { 1 })
}

fn result(out: &mut impl Write, id: &Json, value: &str) -> io::Result<()> {
    json::write_frame(
        out,
        &format!(
            "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{value}}}",
            id.render()
        ),
    )
}
fn error(out: &mut impl Write, id: &Json, code: i32, message: &str) -> io::Result<()> {
    json::write_frame(
        out,
        &format!(
            "{{\"jsonrpc\":\"2.0\",\"id\":{},\"error\":{{\"code\":{code},\"message\":{}}}}}",
            id.render(),
            quoted(message)
        ),
    )
}

struct Server<'a> {
    config: &'a CompileConfig,
    documents: HashMap<String, Document>,
    published: BTreeSet<String>,
    initialized: bool,
    ready: bool,
    shutdown: bool,
    context_watch: bool,
    root: Option<PathBuf>,
}
fn text_document(params: &Json) -> Option<&str> {
    params.get("textDocument")?.get("uri")?.string()
}
impl Server<'_> {
    fn context_file(&self, doc: &Document) -> Option<PathBuf> {
        crate::lsp_context::discover(&doc.path).or_else(|| {
            self.root
                .as_ref()
                .and_then(|root| crate::lsp_context::discover(&root.join("__lsp_root__.lim")))
        })
    }
    fn notification(&mut self, method: &str, params: &Json) -> bool {
        if method == "workspace/didChangeWatchedFiles" {
            return params
                .get("changes")
                .and_then(Json::array)
                .is_some_and(|changes| {
                    changes.iter().any(|change| {
                        change
                            .get("uri")
                            .and_then(Json::string)
                            .and_then(uri_to_path)
                            .is_some_and(|path| {
                                path.file_name().is_some_and(|name| name == "lim.lsp")
                            })
                    })
                });
        }
        let Some(uri) = text_document(params) else {
            return false;
        };
        let Some(path) = uri_to_path(uri) else {
            return false;
        };
        match method {
            "textDocument/didOpen" => {
                let Some(td) = params.get("textDocument") else {
                    return false;
                };
                let (Some(text), Some(version), Some(_)) = (
                    td.get("text").and_then(Json::string),
                    td.get("version").and_then(Json::integer),
                    td.get("languageId").and_then(Json::string),
                ) else {
                    return false;
                };
                if self.documents.contains_key(uri)
                    || self.documents.values().any(|d| d.path == path)
                {
                    return false;
                }
                self.documents.insert(
                    uri.into(),
                    Document {
                        path,
                        text: text.into(),
                        version,
                    },
                );
                true
            }
            "textDocument/didChange" => {
                let Some(version) = params
                    .get("textDocument")
                    .and_then(|v| v.get("version"))
                    .and_then(Json::integer)
                else {
                    return false;
                };
                let Some(changes) = params.get("contentChanges").and_then(Json::array) else {
                    return false;
                };
                let Some(doc) = self.documents.get_mut(uri) else {
                    return false;
                };
                if version <= doc.version || changes.is_empty() {
                    return false;
                }
                let mut replacement = None;
                for change in changes {
                    if change.get("range").is_some() || change.get("rangeLength").is_some() {
                        return false;
                    }
                    let Some(text) = change.get("text").and_then(Json::string) else {
                        return false;
                    };
                    replacement = Some(text);
                }
                doc.text = replacement.unwrap().into();
                doc.version = version;
                true
            }
            "textDocument/didSave" => {
                let Some(doc) = self.documents.get_mut(uri) else {
                    return false;
                };
                if let Some(text) = params.get("text") {
                    let Some(text) = text.string() else {
                        return false;
                    };
                    doc.text = text.into();
                }
                true
            }
            "textDocument/didClose" => self.documents.remove(uri).is_some(),
            _ => false,
        }
    }
    fn diagnostics(&mut self, out: &mut impl Write) -> io::Result<()> {
        let overlays = self
            .documents
            .values()
            .map(|d| (d.path.clone(), d.text.clone()))
            .collect::<HashMap<_, _>>();
        let mut reports: BTreeMap<String, Vec<String>> = self
            .documents
            .keys()
            .map(|u| (u.clone(), Vec::new()))
            .collect();
        let mut docs = self.documents.iter().collect::<Vec<_>>();
        docs.sort_by_key(|(uri, _)| *uri);
        for (root_uri, doc) in docs {
            if let Err(diagnostic) = crate::editor::checked_program_in_context(
                &doc.text,
                &doc.path,
                self.config,
                &overlays,
                self.context_file(doc).as_deref(),
            ) {
                let (path, source, span) = primary_location(&diagnostic, doc, &overlays);
                let uri = self
                    .documents
                    .iter()
                    .find(|(_, d)| d.path == path)
                    .map(|(u, _)| u.clone())
                    .or_else(|| path_to_uri(&path))
                    .unwrap_or_else(|| root_uri.clone());
                // Never apply an imported/generated byte span to the root buffer.
                let range = source
                    .map(|text| span_range(text, span))
                    .unwrap_or_else(|| range(0, 0, 0, 0));
                let rendered = diagnostic_json(&diagnostic, &range, &doc.path, &overlays);
                let entries = reports.entry(uri).or_default();
                if !entries.contains(&rendered) {
                    entries.push(rendered);
                }
            }
        }
        for uri in &self.published {
            reports.entry(uri.clone()).or_default();
        }
        self.published = reports
            .iter()
            .filter(|(_, d)| !d.is_empty())
            .map(|(u, _)| u.clone())
            .collect();
        for (uri, diagnostics) in reports {
            let version = self
                .documents
                .get(&uri)
                .map(|d| format!(",\"version\":{}", d.version))
                .unwrap_or_default();
            json::write_frame(out, &format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{}{version},\"diagnostics\":[{}]}}}}", quoted(&uri), diagnostics.join(",")))?;
        }
        Ok(())
    }
    fn request(&self, method: &str, params: &Json) -> Result<String, (i32, &'static str)> {
        if !matches!(
            method,
            "textDocument/formatting" | "textDocument/documentSymbol" | "textDocument/definition"
        ) {
            return Err((-32601, "Method not found"));
        }
        let uri = text_document(params)
            .filter(|u| uri_to_path(u).is_some())
            .ok_or((-32602, "Invalid params"))?;
        let doc = self
            .documents
            .get(uri)
            .ok_or((-32602, "Document is not open"))?;
        if method == "textDocument/formatting" {
            let options = params.get("options").ok_or((-32602, "Invalid params"))?;
            if !options
                .get("tabSize")
                .and_then(Json::integer)
                .is_some_and(|n| n > 0)
                || !matches!(options.get("insertSpaces"), Some(Json::Bool(_)))
            {
                return Err((-32602, "Invalid params"));
            }
            let formatted = crate::format_source(&doc.text)
                .map_err(|_| (-32803, "Source cannot be formatted"))?;
            return Ok(format!(
                "[{{\"range\":{},\"newText\":{}}}]",
                byte_range(&doc.text, 0, doc.text.len()),
                quoted(&formatted)
            ));
        }
        let declarations = declarations(&doc.text);
        if method == "textDocument/documentSymbol" {
            return Ok(format!(
                "[{}]",
                declarations
                    .iter()
                    .map(|d| format!(
                        "{{\"name\":{},\"kind\":{},\"range\":{},\"selectionRange\":{}}}",
                        quoted(&d.name),
                        d.kind,
                        span_range(&doc.text, Some(d.whole)),
                        span_range(&doc.text, Some(d.name_span))
                    ))
                    .collect::<Vec<_>>()
                    .join(",")
            ));
        }
        let pos = params.get("position").ok_or((-32602, "Invalid params"))?;
        let line = pos
            .get("line")
            .and_then(Json::integer)
            .filter(|n| *n >= 0)
            .ok_or((-32602, "Invalid params"))?;
        let character = pos
            .get("character")
            .and_then(Json::integer)
            .filter(|n| *n >= 0)
            .ok_or((-32602, "Invalid params"))?;
        let byte = position_byte(&doc.text, line as usize, character as usize)
            .ok_or((-32602, "Invalid position"))?;
        if let Some(name) = crate::parse(&doc.text)
            .ok()
            .and_then(|tree| import_reference(&tree, byte))
        {
            let overlays = self
                .documents
                .values()
                .map(|d| (d.path.clone(), d.text.clone()))
                .collect();
            let target = crate::editor::import_target(
                &doc.path,
                &name,
                self.config,
                &overlays,
                self.context_file(doc).as_deref(),
            );
            return Ok(target
                .and_then(|path| path_to_uri(&path))
                .map(|uri| {
                    format!(
                        "{{\"uri\":{},\"range\":{}}}",
                        quoted(&uri),
                        range(0, 0, 0, 0)
                    )
                })
                .unwrap_or_else(|| "null".into()));
        }
        // Explicit #call callee role has a function namespace, unlike arbitrary names.
        let callee = crate::parse(&doc.text)
            .ok()
            .and_then(|tree| call_callee(&tree, byte));
        if self.context_file(doc).is_some() {
            let name = callee.clone().or_else(|| {
                crate::parse(&doc.text)
                    .ok()
                    .and_then(|tree| type_reference(&tree, byte))
            });
            if let Some(name) = name {
                return Ok(self
                    .resolved_definition(doc, byte, &name)
                    .unwrap_or_else(|| "null".into()));
            }
        }
        if callee.is_none() {
            if let Some(name) = crate::parse(&doc.text)
                .ok()
                .and_then(|tree| type_reference(&tree, byte))
            {
                if let Some(location) = self.resolved_definition(doc, byte, &name) {
                    return Ok(location);
                }
            }
        }
        let target = if let Some(callee) = callee {
            let mut candidates = declarations
                .iter()
                .filter(|d| d.kind == 12 && d.name == callee);
            let first = candidates.next();
            if first.is_none() {
                if let Some(location) = self.resolved_definition(doc, byte, &callee) {
                    return Ok(location);
                }
            }
            if candidates.next().is_none() {
                first
            } else {
                None
            }
        } else {
            declarations
                .iter()
                .find(|d| d.name_span.start <= byte && byte < d.name_span.end)
        };
        Ok(target
            .map(|d| {
                format!(
                    "{{\"uri\":{},\"range\":{}}}",
                    quoted(uri),
                    span_range(&doc.text, Some(d.name_span))
                )
            })
            .unwrap_or_else(|| "null".into()))
    }

    fn resolved_definition(&self, doc: &Document, byte: usize, name: &str) -> Option<String> {
        let overlays = self
            .documents
            .values()
            .map(|d| (d.path.clone(), d.text.clone()))
            .collect();
        let program = crate::editor::program_in_context(
            &doc.text,
            &doc.path,
            self.config,
            &overlays,
            self.context_file(doc).as_deref(),
            false,
        )
        .ok()?;
        let mut names = BTreeSet::new();
        for expression in program.declaration_expressions.values() {
            if program
                .source_files
                .get(expression.span.source_id as usize)
                .is_some_and(|file| path_key(&file.path) == doc.path)
            {
                if let Some(resolved) = semantic_symbol(expression, &expression.expr, byte) {
                    names.insert(resolved);
                }
            }
        }
        if names.is_empty() {
            names.insert(name.to_owned());
        }
        let mut locations = BTreeSet::new();
        for name in names {
            if program
                .declaration_occurrences
                .get(&name)
                .is_some_and(|items| items.len() > 1)
            {
                continue;
            }
            if let Some(location) = self.definition_location(doc, &program, &name) {
                locations.insert(location);
            }
        }
        match locations.len() {
            0 => None,
            1 => locations.into_iter().next(),
            _ => Some(format!(
                "[{}]",
                locations.into_iter().collect::<Vec<_>>().join(",")
            )),
        }
    }

    fn definition_location(
        &self,
        doc: &Document,
        program: &crate::Program,
        name: &str,
    ) -> Option<String> {
        let expression = program.declaration_expressions.get(name)?;
        let span = expression.children.get(1)?.span;
        let file = program.source_files.get(span.source_id as usize)?;
        if let Some(path) = file_source_path(&file.path.to_string_lossy()) {
            return Some(format!(
                "{{\"uri\":{},\"range\":{}}}",
                quoted(&path_to_uri(&path)?),
                span_range(&file.source, Some(span))
            ));
        }
        // Invalid runtime programs may still navigate ordinary declarations.
        // Only publish generated source after the normal safety checks pass.
        crate::CheckedProgram::validate_with_span(program).ok()?;
        let (source, prefix) = generated_snapshot(&program, span.source_id)?;
        let hash = crate::generator::stable_hash(source.as_bytes());
        let directory = doc.path.parent()?.join(".lim/generated");
        let path = directory.join(format!("editor-{hash:032x}.lim"));
        let uri = path_to_uri(&path)?;
        // Navigation publishes a source snapshot, never a generator-cache entry.
        // Do not overwrite an existing snapshot with different contents.
        if path.exists() {
            if std::fs::read_to_string(&path).ok()? != source {
                return None;
            }
        } else {
            std::fs::create_dir_all(&directory).ok()?;
            let mut output = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .ok()?;
            output.write_all(source.as_bytes()).ok()?;
        }
        Some(format!(
            "{{\"uri\":{},\"range\":{}}}",
            quoted(&uri),
            byte_range(&source, prefix + span.start, prefix + span.end)
        ))
    }
}

fn semantic_symbol(source: &SpannedExpr, semantic: &Expr, byte: usize) -> Option<String> {
    if byte < source.span.start || byte >= source.span.end {
        return None;
    }
    if let Expr::Symbol(name) = semantic {
        return Some(name.clone());
    }
    if let Expr::List(values) = semantic {
        for (child, value) in source.children.iter().zip(values) {
            if let Some(name) = semantic_symbol(child, value, byte) {
                return Some(name);
            }
        }
    }
    None
}

fn import_reference(expressions: &[SpannedExpr], byte: usize) -> Option<String> {
    for expression in expressions {
        if byte < expression.span.start || byte >= expression.span.end {
            continue;
        }
        if matches!(expression.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            continue;
        }
        let head = expression.children.first().map(|e| &e.expr);
        if matches!(head, Some(Expr::At))
            || matches!(head, Some(Expr::Symbol(name)) if name == "#gn" || name == "#gn-fn")
        {
            continue;
        }
        if matches!(head, Some(Expr::Symbol(name)) if name == "#import" || name == "#import-external")
        {
            let path = expression.children.get(1)?;
            if (path.span.start <= byte && byte < path.span.end)
                || expression
                    .children
                    .first()
                    .is_some_and(|head| head.span.start <= byte && byte < head.span.end)
            {
                if let Expr::String(name) = &path.expr {
                    return Some(name.clone());
                }
            }
            continue;
        }
        if let Some(name) = import_reference(&expression.children, byte) {
            return Some(name);
        }
    }
    None
}

pub(crate) fn generated_snapshot(
    program: &crate::Program,
    source_id: u32,
) -> Option<(String, usize)> {
    let file = program.source_files.get(source_id as usize)?;
    let invocation = program.generated_source_invocations.get(&source_id)?;
    let origin = program.source_files.get(invocation.source_id as usize)?;
    let header = format!(
        "; Generated definition invoked at {}:{}\n",
        origin
            .path
            .display()
            .to_string()
            .replace('\n', "\\n")
            .replace('\r', "\\r"),
        invocation.line
    );
    let prefix = header.len();
    Some((format!("{header}{}", file.source), prefix))
}

fn file_source_path(name: &str) -> Option<PathBuf> {
    let path = Path::new(name);
    if path
        .components()
        .any(|c| c.as_os_str().to_string_lossy().starts_with('<'))
    {
        return None;
    }
    Some(path_key(path))
}

fn primary_location<'a>(
    d: &'a Diagnostic,
    root: &'a Document,
    overlays: &'a HashMap<PathBuf, String>,
) -> (PathBuf, Option<&'a str>, Option<Span>) {
    if let Some(path) = d.source_name.as_deref().and_then(file_source_path) {
        let text = d
            .source_text
            .as_deref()
            .or_else(|| overlays.get(&path).map(String::as_str));
        return (path, text, d.span);
    }
    if d.source_name.is_some() {
        for origin in &d.expansion_provenance {
            if let Some(path) = origin.source_name.as_deref().and_then(file_source_path) {
                let text = origin
                    .source_text
                    .as_deref()
                    .or_else(|| overlays.get(&path).map(String::as_str));
                return (path, text, Some(origin.span));
            }
        }
        // Missing file-backed provenance: attach to root without inventing a span.
        return (root.path.clone(), Some(&root.text), None);
    }
    (root.path.clone(), Some(&root.text), d.span)
}

fn diagnostic_json(
    d: &Diagnostic,
    location: &str,
    root_path: &Path,
    overlays: &HashMap<PathBuf, String>,
) -> String {
    let mut related = Vec::new();
    for label in d.labels.iter().chain(&d.expansion_provenance) {
        let Some(path) = label
            .source_name
            .as_deref()
            .or(d.source_name.as_deref())
            .map(file_source_path)
            .unwrap_or_else(|| Some(root_path.to_owned()))
        else {
            continue;
        };
        let Some(uri) = path_to_uri(&path) else {
            continue;
        };
        let Some(source) = label
            .source_text
            .as_deref()
            .or_else(|| overlays.get(&path).map(String::as_str))
            .or_else(|| {
                if d.source_name.as_deref().and_then(file_source_path).as_ref() == Some(&path) {
                    d.source_text.as_deref()
                } else {
                    None
                }
            })
        else {
            continue;
        };
        related.push(format!(
            "{{\"location\":{{\"uri\":{},\"range\":{}}},\"message\":{}}}",
            quoted(&uri),
            span_range(source, Some(label.span)),
            quoted(&label.message)
        ));
    }
    let message = std::iter::once(d.message.as_str())
        .chain(d.notes.iter().map(String::as_str))
        .collect::<Vec<_>>()
        .join("\n");
    format!("{{\"range\":{location},\"severity\":1,\"code\":{},\"source\":\"lim\",\"message\":{},\"relatedInformation\":[{}]}}", quoted(&d.code_string()), quoted(&message), related.join(","))
}

struct Declaration {
    name: String,
    kind: u8,
    whole: Span,
    name_span: Span,
}
fn call_callee(expressions: &[SpannedExpr], byte: usize) -> Option<String> {
    for expression in expressions {
        if byte < expression.span.start || byte >= expression.span.end {
            continue;
        }
        if matches!(expression.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            continue;
        }
        if let Some(Expr::Symbol(head)) = expression.children.first().map(|c| &c.expr) {
            if head == "#gn" || head == "#gn-fn" {
                continue;
            }
            if head == "#call" {
                if let Some(callee) = expression.children.get(1) {
                    if callee.span.start <= byte && byte < callee.span.end {
                        if let Expr::Symbol(name) = &callee.expr {
                            return Some(name.clone());
                        }
                    }
                }
            }
        }
        if let Some(name) = call_callee(&expression.children, byte) {
            return Some(name);
        }
    }
    None
}

// Only explicit type positions are navigable: never treat arbitrary symbols,
// named argument labels, quoted templates, or generator literals as types.
fn type_reference(expressions: &[SpannedExpr], byte: usize) -> Option<String> {
    fn in_type(expr: &SpannedExpr, byte: usize) -> Option<String> {
        if byte < expr.span.start || byte >= expr.span.end {
            return None;
        }
        if let Expr::Symbol(name) = &expr.expr {
            return Some(name.clone());
        }
        expr.children
            .iter()
            .skip(1)
            .find_map(|child| in_type(child, byte))
    }
    for expr in expressions {
        if byte < expr.span.start || byte >= expr.span.end {
            continue;
        }
        if matches!(expr.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            continue;
        }
        let head = expr.children.first().and_then(|child| match &child.expr {
            Expr::Symbol(name) => Some(name.as_str()),
            _ => None,
        });
        if matches!(head, Some("#gn" | "#gn-fn"))
            || matches!(expr.children.first().map(|e| &e.expr), Some(Expr::At))
        {
            continue;
        }
        let index = match head {
            Some("#let" | "#let-mut" | "#type") => Some(2),
            Some("#struct-literal") => Some(1),
            Some("#struct" | "#enum") => {
                if let Some(fields) = expr.children.get(2) {
                    for field in &fields.children {
                        for ty in field.children.iter().skip(1) {
                            if let Some(name) = in_type(ty, byte) {
                                return Some(name);
                            }
                        }
                    }
                }
                None
            }
            Some("#fn" | "#unsafe-fn" | "#extern-fn") => {
                if let Some(args) = expr.children.get(2) {
                    for arg in &args.children {
                        if let Some(name) = arg.children.get(1).and_then(|ty| in_type(ty, byte)) {
                            return Some(name);
                        }
                    }
                }
                Some(3)
            }
            _ => None,
        };
        if let Some(name) = index
            .and_then(|i| expr.children.get(i))
            .and_then(|ty| in_type(ty, byte))
        {
            return Some(name);
        }
        if let Some(name) = type_reference(&expr.children, byte) {
            return Some(name);
        }
    }
    None
}
fn declarations(source: &str) -> Vec<Declaration> {
    crate::parse(source)
        .unwrap_or_default()
        .iter()
        .filter_map(|expr| {
            let head = expr.children.first()?;
            let Expr::Symbol(head) = &head.expr else {
                return None;
            };
            let kind = match head.as_str() {
                "#fn" | "#unsafe-fn" | "#extern-fn" => 12,
                "#struct" => 23,
                "#enum" => 10,
                "#let" | "#let-mut" => 13,
                _ => return None,
            };
            let name = expr.children.get(1)?;
            let Expr::Symbol(value) = &name.expr else {
                return None;
            };
            Some(Declaration {
                name: value.clone(),
                kind,
                whole: expr.span,
                name_span: name.span,
            })
        })
        .collect()
}

fn range(sl: usize, sc: usize, el: usize, ec: usize) -> String {
    format!("{{\"start\":{{\"line\":{sl},\"character\":{sc}}},\"end\":{{\"line\":{el},\"character\":{ec}}}}}")
}
pub fn byte_position(text: &str, byte: usize) -> (usize, usize) {
    let mut byte = byte.min(text.len());
    while !text.is_char_boundary(byte) {
        byte -= 1;
    }
    let prefix = &text[..byte];
    let line = prefix.bytes().filter(|b| *b == b'\n').count();
    let last = prefix.rsplit('\n').next().unwrap_or("");
    (line, last.trim_end_matches('\r').encode_utf16().count())
}
fn byte_range(text: &str, start: usize, end: usize) -> String {
    let (sl, sc) = byte_position(text, start);
    let (el, ec) = byte_position(text, end.max(start));
    range(sl, sc, el, ec)
}
fn span_range(text: &str, span: Option<Span>) -> String {
    span.map(|s| byte_range(text, s.start, s.end))
        .unwrap_or_else(|| range(0, 0, 0, 0))
}
fn position_byte(text: &str, line: usize, character: usize) -> Option<usize> {
    let mut start = 0;
    for _ in 0..line {
        start += text.get(start..)?.find('\n')? + 1;
    }
    let end = text[start..]
        .find('\n')
        .map(|n| start + n)
        .unwrap_or(text.len());
    let content = text[start..end]
        .strip_suffix('\r')
        .unwrap_or(&text[start..end]);
    let mut units = 0;
    for (offset, ch) in content.char_indices() {
        if units == character {
            return Some(start + offset);
        }
        units += ch.len_utf16();
        if units > character {
            return None;
        }
    }
    if units == character {
        Some(start + content.len())
    } else {
        None
    }
}

/// Local absolute file URIs only; percent escapes must be valid UTF-8.
pub fn uri_to_path(uri: &str) -> Option<PathBuf> {
    let tail = uri.strip_prefix("file://")?;
    let tail = if tail.starts_with('/') {
        tail
    } else {
        tail.strip_prefix("localhost/")?;
        &tail["localhost".len()..]
    };
    if tail.contains(['?', '#']) {
        return None;
    }
    let mut bytes = Vec::new();
    let mut input = tail.as_bytes().iter().copied();
    while let Some(b) = input.next() {
        if b == b'%' {
            let hi = (input.next()? as char).to_digit(16)?;
            let lo = (input.next()? as char).to_digit(16)?;
            bytes.push((hi * 16 + lo) as u8);
        } else {
            bytes.push(b);
        }
    }
    let path = String::from_utf8(bytes).ok()?;
    if path.contains('\0') {
        return None;
    }
    let path = PathBuf::from(path);
    if !path.is_absolute() {
        return None;
    }
    Some(path_key(&path))
}
fn path_key(path: &Path) -> PathBuf {
    if let Ok(path) = path.canonicalize() {
        return path;
    }
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    };
    // Lexical normalization also works for unsaved, nonexistent imports.
    let mut normalized = PathBuf::new();
    for component in absolute.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                normalized.pop();
            }
            other => normalized.push(other.as_os_str()),
        }
    }
    // Resolve existing parent directories for new unsaved files as well.
    let mut prefix = normalized.as_path();
    let mut suffix = Vec::new();
    loop {
        if let Ok(mut canonical) = prefix.canonicalize() {
            for part in suffix.iter().rev() {
                canonical.push(part);
            }
            return canonical;
        }
        let (Some(name), Some(parent)) = (prefix.file_name(), prefix.parent()) else {
            break;
        };
        suffix.push(name.to_os_string());
        prefix = parent;
    }
    normalized
}
pub fn path_to_uri(path: &Path) -> Option<String> {
    if !path.is_absolute() {
        return None;
    }
    let text = path.to_str()?;
    let mut uri = String::from("file://");
    for b in text.bytes() {
        if b.is_ascii_alphanumeric() || matches!(b, b'/' | b'-' | b'_' | b'.' | b'~' | b':') {
            uri.push(b as char);
        } else {
            use std::fmt::Write;
            let _ = write!(uri, "%{b:02X}");
        }
    }
    Some(uri)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn generated_diagnostic_uses_file_invocation_and_related_provenance() {
        let root = Document {
            path: PathBuf::from("/tmp/lsp-generated-root.lim"),
            text: "😀\n(@broken)".into(),
            version: 1,
        };
        let invocation = Span {
            start: 5,
            end: 14,
            line: 2,
            column: 1,
            source_id: 0,
        };
        let mut diagnostic = Diagnostic::new(crate::DiagnosticCode::Type, "generated error")
            .with_source("<generated:broken>", "bad")
            .with_span(Span {
                start: 0,
                end: 3,
                line: 1,
                column: 1,
                source_id: 1,
            });
        diagnostic
            .expansion_provenance
            .push(crate::DiagnosticLabel {
                message: "generated from this invocation".into(),
                span: invocation,
                source_name: Some(root.path.display().to_string()),
                source_text: Some(root.text.clone()),
            });
        let overlays = HashMap::from([(root.path.clone(), root.text.clone())]);
        let (path, text, span) = primary_location(&diagnostic, &root, &overlays);
        assert_eq!(path, root.path);
        assert_eq!(span, Some(invocation));
        let range = span_range(text.unwrap(), span);
        let report =
            json::parse(&diagnostic_json(&diagnostic, &range, &root.path, &overlays)).unwrap();
        assert_eq!(
            report
                .get("range")
                .unwrap()
                .get("start")
                .unwrap()
                .get("line")
                .unwrap()
                .integer(),
            Some(1)
        );
        let related = report.get("relatedInformation").unwrap().array().unwrap();
        assert_eq!(related.len(), 1);
        assert_eq!(
            related[0]
                .get("location")
                .unwrap()
                .get("uri")
                .unwrap()
                .string(),
            Some("file:///tmp/lsp-generated-root.lim")
        );
        assert!(!report.render().contains("file:///%3C"));
    }
}
