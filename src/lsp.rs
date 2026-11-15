//! Synchronous, std-only LSP server. Checks never save editor buffers.
#[path = "lsp_information.rs"]
mod information;
#[path = "lsp_json.rs"]
pub mod json;
#[path = "lsp_navigation.rs"]
pub(crate) mod navigation;
#[path = "lsp_signature.rs"]
mod signature;
#[path = "lsp_syntax_policy.rs"]
mod syntax_policy;

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
        signature_no_active_parameter: false,
        hover_markup: "plaintext",
        signature_markup: "plaintext",
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
                server.signature_no_active_parameter = matches!(
                    params
                        .get("capabilities")
                        .and_then(|value| value.get("textDocument"))
                        .and_then(|value| value.get("signatureHelp"))
                        .and_then(|value| value.get("signatureInformation"))
                        .and_then(|value| value.get("noActiveParameterSupport")),
                    Some(Json::Bool(true))
                );
                let capabilities = params
                    .get("capabilities")
                    .and_then(|value| value.get("textDocument"));
                server.hover_markup = preferred_markup(
                    capabilities
                        .and_then(|value| value.get("hover"))
                        .and_then(|value| value.get("contentFormat")),
                );
                server.signature_markup = preferred_markup(
                    capabilities
                        .and_then(|value| value.get("signatureHelp"))
                        .and_then(|value| value.get("signatureInformation"))
                        .and_then(|value| value.get("documentationFormat")),
                );
                result(
                    &mut output,
                    id,
                    r#"{"capabilities":{"positionEncoding":"utf-16","textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":true}},"documentFormattingProvider":true,"documentSymbolProvider":true,"definitionProvider":true,"hoverProvider":true,"signatureHelpProvider":{"triggerCharacters":[" ","(","{",":"],"retriggerCharacters":[" ",";",")","}"]}},"serverInfo":{"name":"lim","version":"0.1.0"}}"#,
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
    signature_no_active_parameter: bool,
    hover_markup: &'static str,
    signature_markup: &'static str,
    root: Option<PathBuf>,
}
fn text_document(params: &Json) -> Option<&str> {
    params.get("textDocument")?.get("uri")?.string()
}

fn code_markdown(text: &str) -> String {
    let longest = text.split(|c| c != '`').map(str::len).max().unwrap_or(0);
    let fence = "`".repeat(3.max(longest + 1));
    format!("{fence}lim\n{text}\n{fence}")
}

fn preferred_markup(formats: Option<&Json>) -> &'static str {
    formats
        .and_then(Json::array)
        .into_iter()
        .flatten()
        .find_map(|format| match format.string() {
            Some("markdown") => Some("markdown"),
            Some("plaintext") => Some("plaintext"),
            _ => None,
        })
        .unwrap_or("plaintext")
}

fn markup_content(kind: &str, text: &str) -> String {
    let value = if kind == "markdown" {
        code_markdown(text)
    } else {
        text.to_owned()
    };
    format!("{{\"kind\":{},\"value\":{}}}", quoted(kind), quoted(&value))
}

/// Keep compilation contexts separate while presenting every distinct result.
/// A broken entry cannot hide useful information from another valid entry.
fn merge_information(method: &str, mut results: BTreeSet<String>) -> String {
    if results.len() <= 1 {
        return results.pop_first().unwrap_or_else(|| "null".into());
    }
    let values = results
        .iter()
        .filter_map(|result| json::parse(result).ok())
        .collect::<Vec<_>>();
    if method == "textDocument/hover" {
        let kind = values
            .first()
            .and_then(|value| value.get("contents")?.get("kind")?.string())
            .unwrap_or("plaintext");
        let contents = values
            .iter()
            .filter_map(|value| value.get("contents")?.get("value")?.string())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .join(if kind == "markdown" {
                "\n\n---\n\n"
            } else {
                "\n\n"
            });
        let range = values
            .first()
            .and_then(|value| value.get("range"))
            .map(|range| format!(",\"range\":{}", range.render()))
            .unwrap_or_default();
        format!(
            "{{\"contents\":{{\"kind\":{},\"value\":{}}}{range}}}",
            quoted(kind),
            quoted(&contents)
        )
    } else {
        let signatures = values
            .iter()
            .filter_map(|value| value.get("signatures").and_then(Json::array))
            .flatten()
            .map(Json::render)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let active = signatures
            .first()
            .and_then(|signature| json::parse(signature).ok())
            .and_then(|signature| signature.get("activeParameter").map(Json::render))
            .map(|active| format!(",\"activeParameter\":{active}"))
            .unwrap_or_default();
        format!(
            "{{\"signatures\":[{}],\"activeSignature\":0{active}}}",
            signatures.join(",")
        )
    }
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
            let diagnostics = self.context_diagnostics(doc, &overlays);
            for diagnostic in diagnostics {
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
            json::write_frame(
                out,
                &format!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{}{version},\"diagnostics\":[{}]}}}}",
                    quoted(&uri),
                    diagnostics.join(",")
                ),
            )?;
        }
        Ok(())
    }

    fn context_diagnostics(
        &self,
        doc: &Document,
        overlays: &HashMap<PathBuf, String>,
    ) -> Vec<Diagnostic> {
        let manifest = self.context_file(doc);
        let check = || {
            let (result, warnings) = crate::with_warnings(|| {
                crate::editor::checked_program_in_context(
                    &doc.text,
                    &doc.path,
                    self.config,
                    overlays,
                    manifest.as_deref(),
                )
            });
            match result {
                Ok(_) => warnings,
                Err(error) => vec![error],
            }
        };
        let Some(manifest) = manifest.as_deref() else {
            return check();
        };
        let contexts = match crate::lsp_context::LspContext::read_all(manifest) {
            Ok(contexts) => contexts,
            Err(message) => {
                return vec![
                    Diagnostic::new(crate::DiagnosticCode::Cli, message)
                        .with_source(doc.path.display().to_string(), &doc.text),
                ];
            }
        };
        let multiple = contexts.len() > 1;
        let mut matched = false;
        let mut diagnostics = Vec::new();
        for context in contexts {
            crate::lsp_context::with_selected(&context, || {
                if multiple
                    && !crate::editor::context_includes_file(
                        &doc.text,
                        &doc.path,
                        self.config,
                        overlays,
                        Some(manifest),
                    )
                {
                    return;
                }
                matched = true;
                let mut current = check();
                if multiple {
                    for diagnostic in &mut current {
                        diagnostic
                            .notes
                            .push(format!("compilation context: {}", context.label()));
                    }
                }
                diagnostics.extend(current);
            });
        }
        if !matched {
            diagnostics.push(
                Diagnostic::new(
                    crate::DiagnosticCode::Cli,
                    "file is not included by any LSP entry under the selected cfg",
                )
                .with_source(doc.path.display().to_string(), &doc.text),
            );
        }
        diagnostics
    }

    fn request(&self, method: &str, params: &Json) -> Result<String, (i32, &'static str)> {
        if !matches!(
            method,
            "textDocument/definition" | "textDocument/hover" | "textDocument/signatureHelp"
        ) {
            return self.request_single(method, params);
        }
        let uri = text_document(params)
            .filter(|uri| uri_to_path(uri).is_some())
            .ok_or((-32602, "Invalid params"))?;
        let doc = self
            .documents
            .get(uri)
            .ok_or((-32602, "Document is not open"))?;
        let position = params.get("position").ok_or((-32602, "Invalid params"))?;
        let line = position
            .get("line")
            .and_then(Json::integer)
            .filter(|n| *n >= 0)
            .ok_or((-32602, "Invalid params"))?;
        let character = position
            .get("character")
            .and_then(Json::integer)
            .filter(|n| *n >= 0)
            .ok_or((-32602, "Invalid params"))?;
        position_byte(&doc.text, line as usize, character as usize)
            .ok_or((-32602, "Invalid position"))?;
        let Some(manifest) = self.context_file(doc) else {
            return self.request_single(method, params);
        };
        let contexts = match crate::lsp_context::LspContext::read_all(&manifest) {
            Ok(contexts) => contexts,
            Err(_) => return Ok("null".into()),
        };
        if contexts.len() == 1 {
            return crate::lsp_context::with_selected(&contexts[0], || {
                self.request_single(method, params)
            });
        }
        let overlays = self
            .documents
            .values()
            .map(|document| (document.path.clone(), document.text.clone()))
            .collect();
        if method != "textDocument/definition" {
            let mut results = BTreeSet::new();
            for context in contexts {
                crate::lsp_context::with_selected(
                    &context,
                    || -> Result<(), (i32, &'static str)> {
                        if crate::editor::context_includes_file(
                            &doc.text,
                            &doc.path,
                            self.config,
                            &overlays,
                            Some(&manifest),
                        ) {
                            let value = self.request_single(method, params)?;
                            if value != "null" {
                                results.insert(value);
                            }
                        }
                        Ok(())
                    },
                )?;
            }
            return Ok(merge_information(method, results));
        }
        let mut locations = BTreeSet::new();
        let mut array_result = false;
        for context in contexts {
            crate::lsp_context::with_selected(&context, || -> Result<(), (i32, &'static str)> {
                if !crate::editor::context_includes_file(
                    &doc.text,
                    &doc.path,
                    self.config,
                    &overlays,
                    Some(&manifest),
                ) {
                    return Ok(());
                }
                let result = self.request_single(method, params)?;
                match json::parse(&result).map_err(|_| (-32603, "Invalid definition result"))? {
                    Json::Array(values) => {
                        array_result = true;
                        locations.extend(values.iter().map(Json::render));
                    }
                    Json::Null => {}
                    location => {
                        locations.insert(location.render());
                    }
                }
                Ok(())
            })?;
        }
        Ok(match locations.len() {
            0 => "null".into(),
            1 if !array_result => locations.into_iter().next().unwrap(),
            _ => format!("[{}]", locations.into_iter().collect::<Vec<_>>().join(",")),
        })
    }

    fn request_single(&self, method: &str, params: &Json) -> Result<String, (i32, &'static str)> {
        if !matches!(
            method,
            "textDocument/formatting"
                | "textDocument/documentSymbol"
                | "textDocument/definition"
                | "textDocument/hover"
                | "textDocument/signatureHelp"
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
        if matches!(method, "textDocument/hover" | "textDocument/signatureHelp") {
            return Ok(self
                .document_information(doc, byte, method)
                .unwrap_or_else(|| "null".into()));
        }
        if let Some((span, name)) = crate::parse_source_unit(&doc.text)
            .ok()
            .and_then(|tree| generator_reference(&tree, byte))
        {
            let overlays = self
                .documents
                .values()
                .map(|d| (d.path.clone(), d.text.clone()))
                .collect();
            let context = self.context_file(doc);
            if name.is_some() {
                let target = crate::editor::generator_definition_in_context(
                    &doc.text,
                    &doc.path,
                    self.config,
                    &overlays,
                    context.as_deref(),
                    byte,
                )
                .ok()
                .flatten();
                return Ok(target
                    .and_then(|(path, source, span)| {
                        if crate::standard_library::source(&path) == Some(source.as_str()) {
                            let header = format!("// Bundled source: {}\n", path.display());
                            return self.snapshot_location(
                                doc,
                                &format!("{header}{source}"),
                                header.len(),
                                span,
                            );
                        }
                        // Builtins without a physical declaration have no definition target.
                        let uri = path_to_uri(&file_source_path(&path.to_string_lossy())?)?;
                        Some(format!(
                            "{{\"uri\":{},\"range\":{}}}",
                            quoted(&uri),
                            span_range(&source, Some(span))
                        ))
                    })
                    .unwrap_or_else(|| "null".into()));
            }
            let paths = crate::editor::locate_generated_in_context(
                &doc.text,
                &doc.path,
                self.config,
                &overlays,
                context.as_deref(),
                span.start,
                span.end,
            )
            .unwrap_or_default();
            let locations = paths
                .iter()
                .filter_map(|path| path_to_uri(path))
                .map(|uri| {
                    format!(
                        "{{\"uri\":{},\"range\":{}}}",
                        quoted(&uri),
                        range(0, 0, 0, 0)
                    )
                })
                .collect::<Vec<_>>();
            return Ok(if locations.is_empty() {
                "null".into()
            } else {
                format!("[{}]", locations.join(","))
            });
        }
        if let Some(locations) = self.indexed_definition(doc, byte) {
            return Ok(locations);
        }
        if let Some(name) = crate::parse_source_unit(&doc.text)
            .ok()
            .and_then(|tree| case_variant_reference(&tree, byte))
        {
            return Ok(self
                .resolved_symbol_definition(doc, byte, &name, true)
                .unwrap_or_else(|| "null".into()));
        }
        // Explicit #call callee role has a function namespace, unlike arbitrary names.
        let callee = crate::parse_source_unit(&doc.text)
            .ok()
            .and_then(|tree| call_callee(&tree, byte));
        if self.context_file(doc).is_some() {
            let name = callee.clone().or_else(|| {
                crate::parse_source_unit(&doc.text)
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
            if let Some(name) = crate::parse_source_unit(&doc.text)
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

    fn document_information(&self, doc: &Document, byte: usize, method: &str) -> Option<String> {
        let call = if method == "textDocument/signatureHelp" {
            Some(signature::call(&doc.text, byte)?)
        } else {
            None
        };
        let recovered;
        let source = if let Some(call) = &call {
            call.source.as_str()
        } else {
            recovered = signature::recover(&doc.text)?;
            recovered.as_str()
        };
        let query_byte = call.as_ref().map_or(byte, |call| call.callee.start);
        let overlays = self
            .documents
            .values()
            .map(|document| (document.path.clone(), document.text.clone()))
            .collect();
        let context = crate::editor::information_context(
            source,
            &doc.path,
            self.config,
            &overlays,
            self.context_file(doc).as_deref(),
            query_byte,
        )
        .ok()?;
        let files = context
            .program
            .as_ref()
            .map_or(context.files.as_slice(), |program| {
                program.source_files.as_slice()
            });
        let mut queries = files
            .iter()
            .enumerate()
            .filter(|(_, file)| path_key(&file.path) == doc.path)
            .map(|(file, _)| (file as u32, query_byte, 0))
            .collect::<Vec<_>>();
        if queries.is_empty() {
            if let Some(program) = &context.program {
                queries.extend((0..program.source_files.len()).filter_map(|id| {
                    let (source, prefix) = generated_snapshot(program, id as u32)?;
                    (source == doc.text)
                        .then(|| {
                            query_byte
                                .checked_sub(prefix)
                                .map(|byte| (id as u32, byte, prefix))
                        })
                        .flatten()
                }));
            }
        }
        let mut results = BTreeSet::new();
        for (file, query_byte, prefix) in queries {
            if let Some(call) = &call {
                let Some(signature) = information::signature(&context, file, query_byte) else {
                    continue;
                };
                let active = call.argument.as_ref().and_then(|name| {
                    signature
                        .parameters
                        .iter()
                        .position(|(parameter, _)| parameter == name)
                }).or_else(|| (signature.parameters.len() == 1
                    && signature.parameters[0].0 == "#arg").then_some(0));
                let active = active
                    .map(|index| format!(",\"activeParameter\":{index}"))
                    .unwrap_or_else(|| {
                        if self.signature_no_active_parameter {
                            ",\"activeParameter\":null".into()
                        } else {
                            String::new()
                        }
                    });
                let documentation = if signature.contracts.is_empty() {
                    String::new()
                } else {
                    format!(
                        ",\"documentation\":{}",
                        markup_content(self.signature_markup, &signature.contracts.join("\n"))
                    )
                };
                let parameters = signature
                    .parameters
                    .iter()
                    .map(|(_, label)| format!("{{\"label\":{}}}", quoted(label)))
                    .collect::<Vec<_>>()
                    .join(",");
                results.insert(format!(
                    "{{\"signatures\":[{{\"label\":{},\"parameters\":[{parameters}]{documentation}{active}}}],\"activeSignature\":0{active}}}",
                    quoted(&signature.label)
                ));
            } else if let Some((span, text)) = information::hover(&context, file, query_byte) {
                // Recovery only appends syntax; hover ranges always belong to the
                // original open document, never to synthetic completions.
                if prefix + span.end <= doc.text.len() {
                    results.insert(format!(
                        "{{\"contents\":{},\"range\":{}}}",
                        markup_content(self.hover_markup, &text),
                        byte_range(&doc.text, prefix + span.start, prefix + span.end)
                    ));
                }
            }
        }
        (!results.is_empty()).then(|| merge_information(method, results))
    }

    fn resolved_definition(&self, doc: &Document, byte: usize, name: &str) -> Option<String> {
        self.resolved_symbol_definition(doc, byte, name, false)
    }

    fn indexed_definition(&self, doc: &Document, byte: usize) -> Option<String> {
        let overlays = self
            .documents
            .values()
            .map(|doc| (doc.path.clone(), doc.text.clone()))
            .collect();
        let context = crate::editor::navigation_context(
            &doc.text,
            &doc.path,
            self.config,
            &overlays,
            self.context_file(doc).as_deref(),
            byte,
        )
        .ok()?;
        let files = context
            .program
            .as_ref()
            .map_or(context.files.as_slice(), |program| {
                program.source_files.as_slice()
            });
        let mut queries = files
            .iter()
            .enumerate()
            .filter(|(_, file)| path_key(&file.path) == doc.path)
            .map(|(file, _)| (file as u32, byte))
            .collect::<Vec<_>>();
        if queries.is_empty() {
            if let Some(program) = &context.program {
                queries.extend((0..program.source_files.len()).filter_map(|id| {
                    let (source, prefix) = generated_snapshot(program, id as u32)?;
                    (source == doc.text)
                        .then(|| byte.checked_sub(prefix).map(|byte| (id as u32, byte)))
                        .flatten()
                }));
            }
        }
        let targets = queries.into_iter().flat_map(|(file, byte)| {
            navigation::Index::new(context.program.as_ref(), &context.forms, file, byte).resolve()
        });
        let mut locations = BTreeSet::new();
        for span in targets {
            let file = files.get(span.source_id as usize)?;
            if let Some(path) = file_source_path(&file.path.to_string_lossy()) {
                locations.insert(format!(
                    "{{\"uri\":{},\"range\":{}}}",
                    quoted(&path_to_uri(&path)?),
                    span_range(&file.source, Some(span))
                ));
            } else if let Some(program) = &context.program {
                if let Some(location) = self.span_location(doc, program, span) {
                    locations.insert(location);
                }
            } else if crate::standard_library::source(&file.path) == Some(file.source.as_str()) {
                // Lexical label resolution can finish before expanding the
                // program. Bundled declarations are already trusted source,
                // so their targets still need an editor-readable snapshot.
                let header = format!("// Bundled source: {}\n", file.path.display());
                if let Some(location) = self.snapshot_location(
                    doc, &format!("{header}{}", file.source), header.len(), span,
                ) {
                    locations.insert(location);
                }
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

    fn resolved_symbol_definition(
        &self,
        doc: &Document,
        byte: usize,
        name: &str,
        variant_only: bool,
    ) -> Option<String> {
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
                && expression.span.start <= byte
                && byte < expression.span.end
            {
                // Case normalization changes the spanned arm shape (including
                // synthetic blocks). Align the compilation names with that
                // same shape before mapping the cursor, especially in external
                // imports whose source spelling differs from the semantic name.
                let mut semantic = crate::normalize_keywords(expression.expr.clone());
                crate::normalize_match_cases_expr(&mut semantic);
                if let Some(resolved) = semantic_symbol(expression, &semantic, byte) {
                    names.insert(resolved);
                }
            }
        }
        if names.is_empty() {
            // A file can belong to this entry while the queried declaration is
            // cfg-excluded. Do not bind that inactive use to an unrelated name.
            // Original async bodies and published snapshots have generated
            // source identities rather than ordinary declaration trees.
            let generated = program.generated_source_invocations.values().any(|span| {
                span.start <= byte
                    && byte < span.end
                    && program
                        .source_files
                        .get(span.source_id as usize)
                        .is_some_and(|file| path_key(&file.path) == doc.path)
            });
            let snapshot = doc
                .path
                .file_name()
                .is_some_and(|name| name.to_string_lossy().starts_with("editor-"))
                && doc.path.parent().is_some_and(|parent| {
                    parent.file_name().is_some_and(|name| name == "generated")
                })
                && (0..program.source_files.len()).any(|id| {
                    generated_snapshot(&program, id as u32)
                        .is_some_and(|(source, _)| source == doc.text)
                });
            if !generated && !snapshot {
                return None;
            }
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
            if let Some(location) = self.definition_location(doc, &program, &name, variant_only) {
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
        variant_only: bool,
    ) -> Option<String> {
        // The semantic recovery path must not reinterpret structural source
        // labels as a jump to a compiler-interned record's whole source range.
        if crate::anonymous_records::is_record(name) {
            return None;
        }
        let span = if variant_only {
            variant_definition_span(program, name)?
        } else {
            let expression = program.declaration_expressions.get(name)?;
            expression
                .children
                .get(declaration_name_index(expression))?
                .span
        };
        self.span_location(doc, program, span)
    }

    fn span_location(
        &self,
        doc: &Document,
        program: &crate::Program,
        span: Span,
    ) -> Option<String> {
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
        if crate::standard_library::source(&file.path) != Some(file.source.as_str()) {
            crate::CheckedProgram::validate_with_span(program).ok()?;
        }
        let (source, prefix) = generated_snapshot(&program, span.source_id)?;
        self.snapshot_location(doc, &source, prefix, span)
    }

    fn snapshot_location(
        &self,
        doc: &Document,
        source: &str,
        prefix: usize,
        span: Span,
    ) -> Option<String> {
        let hash = crate::generator::stable_hash(source.as_bytes());
        let parent = doc.path.parent()?;
        let directory = if parent.file_name().is_some_and(|name| name == "generated")
            && parent
                .parent()
                .and_then(Path::file_name)
                .is_some_and(|name| name == ".lim")
        {
            parent.to_owned()
        } else {
            parent.join(".lim/generated")
        };
        let path = directory.join(format!("editor-{hash:032x}.lim"));
        let uri = path_to_uri(&path)?;
        // Navigation publishes a source snapshot, never a generator-cache entry.
        // Do not overwrite an existing snapshot with different contents.
        if path.exists() {
            if std::fs::read_to_string(&path).ok()?.as_str() != source {
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
            byte_range(source, prefix + span.start, prefix + span.end)
        ))
    }
}

/// Variants retain their own source identity, including distributed contributions
/// and generated enums. Never redirect a variant use to its containing type.
fn variant_definition_span(program: &crate::Program, name: &str) -> Option<Span> {
    let mut owners = program.items.iter().filter_map(|item| match item {
        crate::Item::Enum {
            name: owner,
            variants,
            ..
        } if variants.iter().any(|variant| variant.name == name) => Some(owner),
        _ => None,
    });
    let owner = owners.next()?;
    if owners.next().is_some()
        || program
            .declaration_occurrences
            .get(owner)
            .is_some_and(|items| items.len() > 1)
    {
        return None;
    }
    let declaration = program.declaration_expressions.get(owner)?;
    let Expr::List(parts) = &declaration.expr else {
        return None;
    };
    let Expr::List(variants) = parts.get(3)? else {
        return None;
    };
    let source = declaration.children.get(3)?;
    variants
        .iter()
        .zip(&source.children)
        .find_map(|(variant, source)| {
            let (symbol, span) = match variant {
                Expr::Symbol(symbol) => (symbol, source.span),
                Expr::List(parts) => {
                    let Expr::Symbol(symbol) = parts.first()? else {
                        return None;
                    };
                    (symbol, source.children.first()?.span)
                }
                _ => return None,
            };
            (symbol == name).then_some(span)
        })
}

pub(crate) fn semantic_symbol(
    source: &SpannedExpr,
    semantic: &Expr,
    byte: usize,
) -> Option<String> {
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

pub(crate) fn generated_snapshot(
    program: &crate::Program,
    source_id: u32,
) -> Option<(String, usize)> {
    let file = program.source_files.get(source_id as usize)?;
    if crate::standard_library::source(&file.path) == Some(file.source.as_str()) {
        let header = format!("// Bundled source: {}\n", file.path.display());
        let prefix = header.len();
        return Some((format!("{header}{}", file.source), prefix));
    }
    let invocation = program.generated_source_invocations.get(&source_id)?;
    let origin = program.source_files.get(invocation.source_id as usize)?;
    let header = format!(
        "// Generated definition invoked at {}:{}\n",
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
    let severity = match d.severity {
        crate::DiagnosticSeverity::Error => 1,
        crate::DiagnosticSeverity::Warning => 2,
    };
    format!(
        "{{\"range\":{location},\"severity\":{severity},\"code\":{},\"source\":\"lim\",\"message\":{},\"relatedInformation\":[{}]}}",
        quoted(&d.code_string()),
        quoted(&message),
        related.join(",")
    )
}

struct Declaration {
    name: String,
    kind: u8,
    whole: Span,
    name_span: Span,
}
fn declaration_name_index(expression: &SpannedExpr) -> usize {
    if matches!(expression.children.first().map(|child| &child.expr), Some(Expr::Symbol(head)) if head == "#extern-fn")
    {
        2 // The explicit #abi-c convention precedes the function name.
    } else {
        1
    }
}
// The #generate token and generator name have distinct navigation roles. Use token
// spans rather than the containing list: #generate may occur on a later line.
fn generator_reference(expressions: &[SpannedExpr], byte: usize) -> Option<(Span, Option<String>)> {
    for expression in expressions {
        if byte < expression.span.start || byte >= expression.span.end {
            continue;
        }
        if matches!(expression.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            continue;
        }
        if matches!(expression.children.first().map(|child| &child.expr), Some(Expr::Symbol(head)) if head == "#gn" || head == "#gn-fn")
        {
            continue;
        }
        if let Some(at) = expression.children.first().filter(|child| {
            matches!(&child.expr, Expr::Symbol(head) if matches!(head.as_str(), "#dispatch-fn" | "#dispatch-case"))
        }) {
            if at.span.start <= byte && byte < at.span.end {
                return Some((at.span, None));
            }
        }
        if let Some(at) = expression
            .children
            .first()
            .filter(|child| matches!(child.expr, Expr::Generate))
        {
            if at.span.start <= byte && byte < at.span.end {
                return Some((at.span, None));
            }
            if let Some(name) = expression.children.get(1) {
                if name.span.start <= byte && byte < name.span.end {
                    if let Expr::Symbol(name) = &name.expr {
                        return Some((at.span, Some(name.clone())));
                    }
                }
            }
            continue;
        }
        if let Some(reference) = generator_reference(&expression.children, byte) {
            return Some(reference);
        }
    }
    None
}
/// Recognize variant positions, not payload bindings or arbitrary symbols.
fn case_variant_reference(expressions: &[SpannedExpr], byte: usize) -> Option<String> {
    fn pattern(node: &SpannedExpr, byte: usize, bare: bool) -> Option<String> {
        if byte < node.span.start || byte >= node.span.end {
            return None;
        }
        match &node.expr {
            Expr::Symbol(name) if bare && name != "_" && !name.starts_with('#') => {
                Some(name.clone())
            }
            Expr::List(_) => {
                let head = node.children.first()?;
                let Expr::Symbol(name) = &head.expr else {
                    return None;
                };
                if !name.starts_with('#')
                    && name != "_"
                    && head.span.start <= byte
                    && byte < head.span.end
                {
                    return Some(name.clone());
                }
                if matches!(name.as_str(), "#range" | "#literal") {
                    return None;
                }
                node.children.iter().skip(1).find_map(|child| {
                    pattern(
                        child,
                        byte,
                        matches!(name.as_str(), "#or" | "#tuple" | "#array"),
                    )
                })
            }
            _ => None,
        }
    }
    for node in expressions {
        if byte < node.span.start || byte >= node.span.end {
            continue;
        }
        if matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            continue;
        }
        let head = node.children.first().map(|child| &child.expr);
        if matches!(head, Some(Expr::Symbol(name)) if matches!(name.as_str(), "#gn" | "#gn-fn"))
            || matches!(head, Some(Expr::Generate))
        {
            continue;
        }
        if matches!(head, Some(Expr::Symbol(name)) if name == "#match") {
            for arm in node.children.iter().skip(2) {
                if matches!(arm.children.first().map(|child| &child.expr), Some(Expr::Symbol(name))
                    if name == "#case" || crate::borrow_case::Mode::from_keyword(name).is_some())
                {
                    if let Some(name) = arm
                        .children
                        .get(1)
                        .and_then(|node| pattern(node, byte, true))
                    {
                        return Some(name);
                    }
                }
            }
        }
        if let Some(name) = case_variant_reference(&node.children, byte) {
            return Some(name);
        }
    }
    None
}

fn call_callee(expressions: &[SpannedExpr], byte: usize) -> Option<String> {
    for expression in expressions {
        if byte < expression.span.start || byte >= expression.span.end {
            continue;
        }
        if matches!(expression.expr, Expr::Quote(_) | Expr::QuasiQuote(_))
            || matches!(expression.children.first().map(|head| &head.expr), Some(Expr::Generate))
        {
            // Generator literal and nested function roles are handled by the
            // navigation index. Do not reinterpret a data pair as a positional
            // runtime call merely because its first symbol names a function.
            continue;
        }
        if let Some(Expr::Symbol(head)) = expression.children.first().map(|c| &c.expr) {
            if head == "#gn" || head == "#gn-fn" {
                continue;
            }
            if matches!(head.as_str(), "#call" | "#unsafe-call") {
                if let Some(callee) = expression.children.get(1) {
                    if callee.span.start <= byte && byte < callee.span.end {
                        if let Expr::Symbol(name) = &callee.expr {
                            return Some(name.clone());
                        }
                    }
                }
            }
            if crate::surface_syntax::callable_name(head)
                && expression.children.len() == 2
                && expression.children[0].span.start <= byte
                && byte < expression.children[0].span.end
            {
                return Some(head.clone());
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
            || matches!(expr.children.first().map(|e| &e.expr), Some(Expr::Generate))
        {
            continue;
        }
        let index = match head {
            Some("#let" | "#let-mut") => {
                if let Some(kind) = navigation::binding_parts(expr).0 {
                    if let Some(name) = in_type(kind, byte) {
                        return Some(name);
                    }
                }
                None
            }
            Some("#const" | "#static" | "#type") => Some(2),
            Some("#struct-literal") => Some(1),
            Some("#enum-contribute") => {
                if let Some(name) = expr
                    .children
                    .get(1)
                    .and_then(|target| in_type(target, byte))
                {
                    return Some(name);
                }
                if let Some(variant) = expr.children.get(2) {
                    for ty in variant.children.iter().skip(1) {
                        if let Some(name) = in_type(ty, byte) {
                            return Some(name);
                        }
                    }
                }
                None
            }
            Some("#struct" | "#enum") => {
                let fields_index = 3;
                if let Some(fields) = expr.children.get(fields_index) {
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
                let name_index = declaration_name_index(expr);
                if let Some(args) = expr.children.get(name_index + 1) {
                    for arg in &args.children {
                        if let Some(name) = arg.children.get(1).and_then(|ty| in_type(ty, byte)) {
                            return Some(name);
                        }
                    }
                }
                Some(name_index + 2)
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
    crate::parse_source_unit(source)
        .unwrap_or_default()
        .iter()
        .filter_map(|expr| {
            let head = expr.children.first()?;
            let Expr::Symbol(head) = &head.expr else {
                return None;
            };
            let kind = match head.as_str() {
                "#fn" | "#unsafe-fn" | "#extern-fn" | "#dispatch-fn" => 12,
                "#struct" => 23,
                "#enum" | "#distributed-enum" => 10,
                "#let" | "#let-mut" => 13,
                _ => return None,
            };
            let name = expr.children.get(declaration_name_index(expr))?;
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
    format!(
        "{{\"start\":{{\"line\":{sl},\"character\":{sc}}},\"end\":{{\"line\":{el},\"character\":{ec}}}}}"
    )
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
    #[test]
    fn distributed_enum_declarations_and_payloads_are_indexed() {
        let source = "#distributed-enum Error ()\n#enum-contribute Error (Error.Failure Payload)\n";
        let definitions = super::declarations(source);
        assert_eq!(definitions.len(), 1);
        assert_eq!(definitions[0].name, "Error");
        assert_eq!(definitions[0].kind, 10);
        let forms = crate::parse_source_unit(source).unwrap();
        for name in ["Error", "Payload"] {
            assert_eq!(
                super::type_reference(
                    &forms,
                    if name == "Error" {
                        source.rfind("Error (").unwrap()
                    } else {
                        source.rfind(name).unwrap()
                    }
                )
                .as_deref(),
                Some(name)
            );
        }
        assert_eq!(
            super::type_reference(&forms, source.find("Error.Failure").unwrap()),
            None
        );
    }

    use super::*;
    #[test]
    fn generated_diagnostic_uses_file_invocation_and_related_provenance() {
        let root = Document {
            path: PathBuf::from("/tmp/lsp-generated-root.lim"),
            text: "😀\n(#generate broken)".into(),
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
