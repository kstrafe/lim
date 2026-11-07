//! Select a theorem only after the complete source graph has been checked.
use std::path::Path;

use crate::{CompileConfig, Diagnostic, DiagnosticCode, Item, Program, ProofOutcome};

/// A file check can retain a bounded rendered excerpt without cloning the
/// entire proof source. Structured positions still refer to the authored file.
#[derive(Debug)]
pub struct TheoremFileError {
    diagnostic: Option<Diagnostic>,
    rendered: String,
}
impl TheoremFileError {
    pub(crate) fn input(message: String) -> Self {
        Self {
            diagnostic: None,
            rendered: message,
        }
    }
    pub(crate) fn positioned(diagnostic: Diagnostic, rendered: String) -> Self {
        Self {
            diagnostic: Some(diagnostic),
            rendered,
        }
    }
    pub(crate) fn from_diagnostic(diagnostic: Diagnostic, source: &str, path: &Path) -> Self {
        let rendered = crate::render_diagnostic(&diagnostic, source, &path.display().to_string());
        Self::positioned(diagnostic, rendered)
    }
    /// Input I/O errors have no source diagnostic. Proof errors keep exact
    /// global spans; use Display for their bounded text excerpt.
    pub fn diagnostic(&self) -> Option<&Diagnostic> {
        self.diagnostic.as_ref()
    }
    pub fn proof_outcome(&self) -> Option<ProofOutcome> {
        self.diagnostic.as_ref().and_then(Diagnostic::proof_outcome)
    }
}
impl std::fmt::Display for TheoremFileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.rendered)
    }
}
impl std::error::Error for TheoremFileError {}

/// Check a theorem from a file using the ordinary program frontend.
pub fn check_theorem_details_from_file_with_config(
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<CheckedTheorem, TheoremFileError> {
    let _input = crate::timing::stage("input_read");
    let source = std::fs::read_to_string(path)
        .map_err(|error| TheoremFileError::input(error.to_string()))?;
    drop(_input);
    check_general(&source, path, config, name)
        .map_err(|diagnostic| TheoremFileError::from_diagnostic(diagnostic, &source, path))
}

/// Check the complete program source graph, then resolve a root-file theorem
/// name or alias. Returns its canonical identity.
/// Does not emit native artifacts or invoke an external prover.
pub fn check_theorem_from_path_with_config(
    source: &str,
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<String, Diagnostic> {
    check_theorem_details_from_path_with_config(source, path, config, name)
        .map(|checked| checked.name)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedTheorem {
    pub name: String,
    pub outcome: ProofOutcome,
}

/// Render a successful theorem check as one newline-free JSON object.
pub fn render_checked_theorem_json(theorem: &CheckedTheorem) -> String {
    format!(
        "{{\"schema_version\":1,\"category\":\"proof\",\"theorem\":{},\"proof_outcome\":\"{}\"}}",
        crate::diagnostic_json::quoted(&theorem.name),
        theorem.outcome.as_str()
    )
}

/// Validate the complete program, then select a root-file theorem.
pub fn check_theorem_details_from_path_with_config(
    source: &str,
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<CheckedTheorem, Diagnostic> {
    check_general(source, path, config, name)
}

pub(crate) fn check_general(
    source: &str,
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<CheckedTheorem, Diagnostic> {
    let prepare = crate::timing::stage("prepare_imports_parse_cfg");
    let prepared = crate::prepare_program_syntax(
        source,
        path.parent().unwrap_or(Path::new(".")),
        Some(path),
        config,
        None,
    )
    .map_err(|error| crate::generator_diagnostic(error, path, source))?;
    drop(prepare);
    let expansion = crate::timing::stage("expansion");
    let (mut owned, _) = crate::expand_prepared_owned_program(&prepared, config, "check-theorem")
        .map_err(|error| crate::generator_diagnostic(error, path, source))?;
    // Expansion owns its syntax and source locations. Release the preparation
    // graph before semantic validation.
    drop(prepared);
    drop(expansion);
    let validation = crate::timing::stage("semantic_validate");
    owned.validate().map_err(|(message, code, span, labels)| {
        crate::analysis_diagnostic(message, code, span, labels, owned.program())
    })?;
    drop(validation);

    let program = owned.program();
    let canonical = resolve_root_name(program, name).ok_or_else(|| {
        Diagnostic::new(
            DiagnosticCode::ProofInvalid,
            format!("unknown theorem '{name}'"),
        )
        .with_source(path.display().to_string(), source)
    })?;
    let proposition = program.items.iter().find_map(|item| match item {
        Item::Proof { name, proposition } if name == canonical => Some(proposition),
        _ => None,
    });
    let Some(_) = proposition else {
        return Err(selection_error(
            program,
            canonical,
            name,
            "is not a theorem",
            path,
            source,
        ));
    };
    crate::warnings::record_program(program);
    Ok(CheckedTheorem {
        name: canonical.to_owned(),
        outcome: ProofOutcome::Proved,
    })
}

fn resolve_root_name<'a>(program: &'a Program, requested: &str) -> Option<&'a str> {
    let root = program.source_files.first()?;
    if let Some(scope) = &root.file_scope {
        return scope.names.get(requested).map(String::as_str).or_else(|| {
            // A canonical identity is selectable only if the root already has
            // a local declaration or authorized alias exposing that identity.
            scope
                .names
                .values()
                .find(|name| name.as_str() == requested)
                .map(String::as_str)
        });
    }
    program.items.iter().find_map(|item| {
        let name = match item {
            Item::Proof { name, .. } => name,
            _ => return None,
        };
        if name != requested {
            return None;
        }
        let mut origin = *program.declaration_spans.get(name)?;
        let mut visited = std::collections::HashSet::new();
        while let Some(invocation) = program.generated_source_invocations.get(&origin.source_id) {
            if !visited.insert(origin.source_id) {
                return None;
            }
            origin = *invocation;
        }
        (origin.source_id == 0).then_some(name.as_str())
    })
}

fn selection_error(
    program: &Program,
    canonical: &str,
    requested: &str,
    reason: &str,
    path: &Path,
    source: &str,
) -> Diagnostic {
    let span = crate::proof::declaration_span(program, canonical);
    let mut error = crate::analysis_diagnostic(
        format!("'{requested}' {reason}"),
        DiagnosticCode::ProofInvalid,
        span,
        Vec::new(),
        program,
    );
    if error.source_name.is_none() {
        error = error.with_source(path.display().to_string(), source);
    }
    error
}
