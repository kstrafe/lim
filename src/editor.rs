//! Read-only checking of editor buffers, including unsaved imports.
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};

thread_local! {
    static SOURCES: RefCell<HashMap<PathBuf, String>> = RefCell::new(HashMap::new());
}

pub(crate) fn path_key(path: &Path) -> PathBuf {
    if let Ok(path) = path.canonicalize() {
        return path;
    }
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    };
    let mut result = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                result.pop();
            }
            other => result.push(other.as_os_str()),
        }
    }
    result
}

pub(crate) fn source(path: &Path) -> Option<String> {
    SOURCES.with(|sources| {
        let sources = sources.borrow();
        if sources.is_empty() {
            None
        } else {
            sources.get(&path_key(path)).cloned()
        }
    })
}

struct Restore(HashMap<PathBuf, String>);
impl Drop for Restore {
    fn drop(&mut self) {
        SOURCES.with(|sources| *sources.borrow_mut() = std::mem::take(&mut self.0));
    }
}

/// Check without writing generated files or cache entries. Buffers shadow disk
/// only for this call; imported diagnostics retain their own source and spans.
pub fn check_source_for_editor(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
) -> Result<(), crate::Diagnostic> {
    if let Some(manifest) = crate::lsp_context::discover(path) {
        let contexts = crate::lsp_context::LspContext::read_all(&manifest).map_err(|message| {
            crate::Diagnostic::new(crate::DiagnosticCode::Cli, message)
                .with_source(path.display().to_string(), source)
        })?;
        if contexts.len() == 1 {
            return crate::lsp_context::with_selected(&contexts[0], || {
                checked_program_in_context(source, path, config, overlays, Some(&manifest))
                    .map(|_| ())
            });
        }
        let mut included = false;
        for context in contexts {
            crate::lsp_context::with_selected(&context, || {
                if context_includes_file(source, path, config, overlays, Some(&manifest)) {
                    included = true;
                    checked_program_in_context(source, path, config, overlays, Some(&manifest))
                        .map(|_| ())
                } else {
                    Ok(())
                }
            })?;
        }
        if included {
            return Ok(());
        }
        return Err(crate::Diagnostic::new(
            crate::DiagnosticCode::Cli,
            "file is not included by any LSP entry under the selected cfg",
        )
        .with_source(path.display().to_string(), source));
    }
    checked_program_for_editor(source, path, config, overlays).map(|_| ())
}

/// Import membership does not require successful type checking or generation.
/// Broken/unrelated entries must not add definitions to another entry's graph.
pub(crate) fn context_includes_file(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
) -> bool {
    with_compilation_context(
        source,
        path,
        config,
        overlays,
        context_file,
        |entry_source, entry, config, _| {
            if path_key(entry) == path_key(path) {
                return Ok(true);
            }
            match crate::load_imports_with_sources(
                entry_source,
                entry.parent().unwrap_or(Path::new(".")),
                Some(entry),
                config,
            ) {
                Ok((_, files)) => Ok(files
                    .iter()
                    .any(|file| path_key(&file.path) == path_key(path))),
                Err(error) => {
                    let diagnostic = crate::generator_diagnostic(error, entry, entry_source);
                    Ok(diagnostic
                        .source_name
                        .as_deref()
                        .is_some_and(|name| path_key(Path::new(name)) == path_key(path)))
                }
            }
        },
    )
    .unwrap_or(false)
        || (path
            .file_name()
            .is_some_and(|name| name.to_string_lossy().starts_with("editor-"))
            && program_in_context(source, path, config, overlays, context_file, false).is_ok())
}

pub(crate) fn checked_program_for_editor(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
) -> Result<crate::Program, crate::Diagnostic> {
    checked_program_in_context(source, path, config, overlays, None)
}

pub(crate) fn checked_program_in_context(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
) -> Result<crate::Program, crate::Diagnostic> {
    program_in_context(source, path, config, overlays, context_file, true)
}

pub(crate) struct NavigationContext {
    pub program: Option<crate::Program>,
    pub forms: Vec<crate::SpannedExpr>,
    pub files: Vec<crate::SourceFile>,
}

/// Keep lexical navigation available when unrelated generation/checking fails.
/// Only the normal checked publication path may expose generated definitions.
pub(crate) fn navigation_context(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    byte: usize,
) -> Result<NavigationContext, crate::Diagnostic> {
    navigation_context_impl(source, path, config, overlays, context_file, byte, false)
}

/// Display-only declaration metadata may remain useful while a call is being
/// edited. This context must never be used to publish generated source snapshots.
pub(crate) fn information_context(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    byte: usize,
) -> Result<NavigationContext, crate::Diagnostic> {
    navigation_context_impl(source, path, config, overlays, context_file, byte, true)
}

fn navigation_context_impl(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    byte: usize,
    partial_information: bool,
) -> Result<NavigationContext, crate::Diagnostic> {
    with_compilation_context(
        source,
        path,
        config,
        overlays,
        context_file,
        |entry_source, entry, config, _| {
            let base = entry.parent().unwrap_or(Path::new("."));
            let (mut forms, files) =
                crate::load_imports_with_sources(entry_source, base, Some(entry), config)
                    .map_err(|error| crate::generator_diagnostic(error, entry, entry_source))?;
            if let Some(file) = files
                .iter()
                .position(|file| path_key(&file.path) == path_key(path))
            {
                if !crate::lsp::navigation::Index::new(None, &forms, file as u32, byte)
                    .resolve_lexical()
                    .is_empty()
                {
                    return Ok(NavigationContext {
                        program: None,
                        forms,
                        files,
                    });
                }
            }
            let program =
                crate::prepare_program_syntax(entry_source, base, Some(entry), config, None)
                    .and_then(|prepared| {
                        let expanded = crate::expand_prepared_program(&prepared);
                        if partial_information && expanded.is_err() {
                            // Reuse the existing declaration planner before call
                            // normalization. Missing argument labels must not
                            // hide the generated signature needed to finish them.
                            let program =
                                crate::generator::frontend::parse_prepared_async_declarations(
                                    &prepared,
                                )?;
                            crate::file_access::validate(&program)?;
                            Ok(program)
                        } else {
                            expanded
                        }
                    })
                    .ok();
            if let Some(program) = &program {
                let map = files
                    .iter()
                    .map(|file| {
                        program
                            .source_files
                            .iter()
                            .position(|candidate| path_key(&candidate.path) == path_key(&file.path))
                            .map(|id| id as u32)
                    })
                    .collect::<Option<Vec<_>>>();
                let Some(map) = map else {
                    return Err(crate::Diagnostic::new(
                        crate::DiagnosticCode::Cli,
                        "navigation source identities do not match the compilation context",
                    ));
                };
                fn remap(node: &mut crate::SpannedExpr, map: &[u32]) {
                    node.span.source_id = map[node.span.source_id as usize];
                    for child in &mut node.children {
                        remap(child, map);
                    }
                }
                for form in &mut forms {
                    remap(form, &map);
                }
                for (id, file) in program.source_files.iter().enumerate() {
                    if !program
                        .generated_source_invocations
                        .contains_key(&(id as u32))
                    {
                        continue;
                    }
                    if let Ok(outlines) = crate::parse_source_unit(&file.source) {
                        for mut outline in outlines {
                            if matches!(&outline.expr, crate::Expr::List(parts)
                                if matches!(parts.first(), Some(crate::Expr::Symbol(head)) if head == "#syntax"))
                            {
                                crate::set_source_id(&mut outline, id as u32);
                                forms.push(outline);
                            }
                        }
                    }
                }
            }
            Ok(NavigationContext {
                program,
                forms,
                files,
            })
        },
    )
}

pub(crate) fn program_in_context(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    validate: bool,
) -> Result<crate::Program, crate::Diagnostic> {
    with_compilation_context(
        source,
        path,
        config,
        overlays,
        context_file,
        |entry_source, entry, config, has_context| {
            let absolute = path_key(path);
            let prepared = crate::prepare_program_syntax(
                entry_source,
                entry.parent().unwrap_or(Path::new(".")),
                Some(entry),
                config,
                None,
            )
            .map_err(|error| crate::generator_diagnostic(error, entry, entry_source))?;
            let program = crate::expand_prepared_program(&prepared)
                .map_err(|error| crate::generator_diagnostic(error, entry, entry_source))?;
            if has_context
                && !program
                    .source_files
                    .iter()
                    .any(|file| path_key(&file.path) == absolute)
                && !(path
                    .file_name()
                    .is_some_and(|name| name.to_string_lossy().starts_with("editor-"))
                    && path.parent().is_some_and(|parent| {
                        parent.file_name().is_some_and(|name| name == "generated")
                    })
                    && (0..program.source_files.len()).any(|id| {
                        crate::lsp::generated_snapshot(&program, id as u32)
                            .is_some_and(|(text, _)| text == source)
                    }))
            {
                return Err(crate::Diagnostic::new(
                    crate::DiagnosticCode::Cli,
                    format!(
                        "file is not included by LSP entry '{}' under the selected cfg",
                        entry.display()
                    ),
                )
                .with_source(path.display().to_string(), source.to_owned()));
            }
            if validate {
                crate::CheckedProgram::validate_with_span(&program).map_err(
                    |(message, code, span, labels)| {
                        crate::analysis_diagnostic(message, code, span, labels, &program)
                    },
                )?;
                crate::warnings::record_program(&program);
            }
            Ok(program)
        },
    )
}

/// Resolve and publish artifacts using the same entry, cfg, and buffer scope as checking.
pub(crate) fn locate_generated_in_context(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    start: usize,
    end: usize,
) -> Result<Vec<PathBuf>, crate::Diagnostic> {
    with_compilation_context(
        source,
        path,
        config,
        overlays,
        context_file,
        |source, entry, config, _| {
            crate::locate_generated(source, entry, config, &path_key(path), start, end)
        },
    )
}

pub(crate) fn generator_definition_in_context(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    byte: usize,
) -> Result<Option<(PathBuf, String, crate::Span)>, crate::Diagnostic> {
    with_compilation_context(
        source,
        path,
        config,
        overlays,
        context_file,
        |source, entry, config, _| {
            let (forms, files) = crate::load_imports_with_sources(
                source,
                entry.parent().unwrap_or(Path::new(".")),
                Some(entry),
                config,
            )
            .map_err(|error| crate::generator_diagnostic(error, entry, source))?;
            if !files
                .iter()
                .any(|file| path_key(&file.path) == path_key(path))
            {
                return Ok(None);
            }
            // External imports rewrite names while preserving source spans. Recover
            // the invocation's compilation name from those forms, not buffer text.
            let names = forms
                .iter()
                .filter(|form| {
                    files
                        .get(form.span.source_id as usize)
                        .is_some_and(|file| path_key(&file.path) == path_key(path))
                })
                .filter_map(|form| crate::lsp::semantic_symbol(form, &form.expr, byte))
                .collect::<std::collections::BTreeSet<_>>();
            if names.is_empty() {
                return Ok(None);
            }
            let mut seen = std::collections::HashSet::new();
            let mut matches = forms.iter().filter_map(|form| {
                let crate::Expr::Symbol(head) = &form.children.first()?.expr else {
                    return None;
                };
                if head != "#gn" {
                    return None;
                }
                let declaration = form.children.get(1)?;
                let crate::Expr::Symbol(name) = &declaration.expr else {
                    return None;
                };
                if !names.contains(name) {
                    return None;
                }
                let file = files.get(declaration.span.source_id as usize)?;
                if !seen.insert((
                    path_key(&file.path),
                    declaration.span.start,
                    declaration.span.end,
                )) {
                    return None;
                }
                Some((file.path.clone(), file.source.clone(), declaration.span))
            });
            let first = matches.next();
            Ok(if matches.next().is_none() {
                first
            } else {
                None
            })
        },
    )
}

fn with_compilation_context<T>(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    operation: impl FnOnce(&str, &Path, &crate::CompileConfig, bool) -> Result<T, crate::Diagnostic>,
) -> Result<T, crate::Diagnostic> {
    let mut overlays: HashMap<PathBuf, String> = overlays
        .iter()
        .map(|(path, text)| (path_key(path), text.clone()))
        .collect();
    overlays.insert(path_key(path), source.to_owned());
    let _restore = Restore(SOURCES.with(|sources| sources.replace(overlays)));
    let mut config = config.clone();
    let absolute = path_key(path);
    let context = context_file
        .map(Path::to_owned)
        .or_else(|| crate::lsp_context::discover(path))
        .map(|manifest| {
            crate::lsp_context::selected(&manifest).map_err(|message| {
                crate::Diagnostic::new(crate::DiagnosticCode::Cli, message)
                    .with_source(path.display().to_string(), source.to_owned())
            })
        })
        .transpose()?;
    let entry = context
        .as_ref()
        .map_or(absolute.clone(), |context| context.entry.clone());
    if let Some(context) = &context {
        config = context.config.clone();
    } else {
        for directory in absolute.parent().into_iter().flat_map(Path::ancestors) {
            let manifest = directory.join("lim.project");
            if manifest.is_file() {
                let project = crate::read_project(&manifest).map_err(|message| {
                    crate::Diagnostic::new(crate::DiagnosticCode::Cli, message)
                        .with_source(path.display().to_string(), source.to_owned())
                })?;
                config.add_module_path(project.source_root);
                for module in project.module_paths {
                    config.add_module_path(module);
                }
                break;
            }
        }
    }
    let entry_source = if entry == absolute {
        source.to_owned()
    } else {
        self::source(&entry)
            .or_else(|| std::fs::read_to_string(&entry).ok())
            .ok_or_else(|| {
                crate::Diagnostic::new(
                    crate::DiagnosticCode::Cli,
                    format!("cannot read LSP entry '{}'", entry.display()),
                )
                .with_source(path.display().to_string(), source.to_owned())
            })?
    };
    operation(&entry_source, &entry, &config, context.is_some())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsaved_imports_override_disk_without_creating_artifacts() {
        let base = std::env::temp_dir().join(format!("lim-editor-overlay-{}", std::process::id()));
        let root = base.join("main.lim");
        let imported = base.join("values.lim");
        assert!(!base.exists());
        let source =
            "#alias value = ./values.lim::value\n#fn main { #params = (); #returns = #u64; #body = ( (#return (#call value ())) ); }\n";
        let overlays = HashMap::from([(imported, "#fn value { #params = (); #returns = #u64; #body = ( (#return 42u64) ); }\n".into())]);
        check_source_for_editor(source, &root, &crate::CompileConfig::default(), &overlays)
            .unwrap();
        assert!(
            !base.exists(),
            "editor checks must not create cache/source files"
        );
        let error = check_source_for_editor(
            source,
            &root,
            &crate::CompileConfig::default(),
            &HashMap::new(),
        )
        .unwrap_err();
        assert!(
            error.message.contains("cannot resolve import"),
            "{}",
            error.message
        );
    }

    #[test]
    fn project_module_paths_are_discovered_for_nested_buffers() {
        let base = std::env::temp_dir().join(format!("lim-editor-project-{}", std::process::id()));
        std::fs::create_dir(&base).unwrap();
        std::fs::create_dir_all(base.join("src/nested")).unwrap();
        std::fs::create_dir(base.join("modules")).unwrap();
        std::fs::write(base.join("lim.project"), "schema-version = 1\nname = \"editor\"\nsource-root = \"src\"\nmodule-path = \"modules\"\n").unwrap();
        let root = base.join("src/nested/main.lim");
        let overlays = HashMap::from([(
            base.join("modules/value.lim"),
            "#fn value { #params = (); #returns = #u64; #body = ( (#return 42u64) ); }\n".into(),
        )]);
        let result = check_source_for_editor(
            "#alias value = project::modules/value.lim::value\n#fn main { #params = (); #returns = #u64; #body = ( (#return (#call value ())) ); }\n",
            &root,
            &crate::CompileConfig::default(),
            &overlays,
        );
        assert!(!base.join("src/nested/.lim").exists());
        std::fs::remove_dir_all(&base).unwrap();
        result.unwrap();
    }

    #[test]
    fn imported_error_keeps_the_unsaved_source_span() {
        let base = std::env::temp_dir().join(format!("lim-editor-error-{}", std::process::id()));
        let root = base.join("main.lim");
        let imported = base.join("bad.lim");
        let invalid = "#fn wrong { #params = (); #returns = #u64; #body = ( (#return true) ); }\n";
        let overlays = HashMap::from([(imported.clone(), invalid.into())]);
        let error = check_source_for_editor(
            "#alias wrong = ./bad.lim::wrong\n",
            &root,
            &crate::CompileConfig::default(),
            &overlays,
        )
        .unwrap_err();
        assert_eq!(error.code, crate::DiagnosticCode::Type);
        assert_eq!(error.source_name.as_deref(), imported.to_str());
        assert_eq!(error.source_text.as_deref(), Some(invalid));
        assert!(error.span.is_some());
        assert!(!base.exists());
    }
}
