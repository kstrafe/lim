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

pub(crate) fn import_target(
    path: &Path,
    name: &str,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
) -> Option<PathBuf> {
    let overlays = overlays
        .iter()
        .map(|(p, s)| (path_key(p), s.clone()))
        .collect();
    let _restore = Restore(SOURCES.with(|sources| sources.replace(overlays)));
    let mut config = config.clone();
    if let Some(context) = context_file
        .map(Path::to_owned)
        .or_else(|| crate::lsp_context::discover(path))
    {
        config = crate::lsp_context::LspContext::read(&context).ok()?.config;
    } else {
        for directory in path.parent()?.ancestors() {
            let manifest = directory.join("lim.project");
            if manifest.is_file() {
                let project = crate::read_project(&manifest).ok()?;
                config.add_module_path(project.source_root);
                for module in project.module_paths {
                    config.add_module_path(module);
                }
                break;
            }
        }
    }
    let candidate = crate::import_candidate(path.parent()?, name, &config);
    if candidate.is_file() || self::source(&candidate).is_some() {
        Some(path_key(&candidate))
    } else {
        None
    }
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
    checked_program_for_editor(source, path, config, overlays).map(|_| ())
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

pub(crate) fn program_in_context(
    source: &str,
    path: &Path,
    config: &crate::CompileConfig,
    overlays: &HashMap<PathBuf, String>,
    context_file: Option<&Path>,
    validate: bool,
) -> Result<crate::Program, crate::Diagnostic> {
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
            crate::lsp_context::LspContext::read(&manifest).map_err(|message| {
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
    let prepared = crate::prepare_program_syntax(
        &entry_source,
        entry.parent().unwrap_or(Path::new(".")),
        Some(&entry),
        &config,
        None,
    )
    .map_err(|error| crate::generator_diagnostic(error, &entry, &entry_source))?;
    let program = crate::expand_prepared_program(&prepared)
        .map_err(|error| crate::generator_diagnostic(error, &entry, &entry_source))?;
    if context.is_some()
        && !program
            .source_files
            .iter()
            .any(|file| path_key(&file.path) == absolute)
        && !(path
            .file_name()
            .is_some_and(|name| name.to_string_lossy().starts_with("editor-"))
            && path
                .parent()
                .is_some_and(|parent| parent.file_name().is_some_and(|name| name == "generated"))
            && program.generated_source_invocations.keys().any(|id| {
                crate::lsp::generated_snapshot(&program, *id)
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
    }
    Ok(program)
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
        let source = "(#import \"values.lim\") (#fn main () #u64 (#return (#call value ())))";
        let overlays = HashMap::from([(imported, "(#fn value () #u64 (#return 42u64))".into())]);
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
            "(#fn value () #u64 (#return 42u64))".into(),
        )]);
        let result = check_source_for_editor(
            "(#import \"value.lim\") (#fn main () #u64 (#return (#call value ())))",
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
        let invalid = "(#fn wrong () #u64 (#return true))";
        let overlays = HashMap::from([(imported.clone(), invalid.into())]);
        let error = check_source_for_editor(
            "(#import \"bad.lim\")",
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
