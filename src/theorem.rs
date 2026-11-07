//! Select a theorem only after the complete source graph has been checked.
use std::path::Path;

use crate::{CompileConfig, Diagnostic, DiagnosticCode, Expr, Item, Program};

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
}
impl std::fmt::Display for TheoremFileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.rendered)
    }
}
impl std::error::Error for TheoremFileError {}

/// Check a theorem from a file without retaining all mathematical source text.
/// Contextual source uses the ordinary frontend and keeps its existing rules.
pub fn check_theorem_details_from_file_with_config(
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<CheckedTheorem, TheoremFileError> {
    if config
        .values
        .get("async-lowering")
        .is_none_or(|value| value == "graph")
    {
        if let Some(checked) = crate::proof::check_standalone_theorem_file(path, config, name) {
            return checked;
        }
    }
    let _input = crate::timing::stage("input_read");
    let source = std::fs::read_to_string(path)
        .map_err(|error| TheoremFileError::input(error.to_string()))?;
    drop(_input);
    check_general(&source, path, config, name)
        .map_err(|diagnostic| TheoremFileError::from_diagnostic(diagnostic, &source, path))
}

/// Check every ordinary and mathematical obligation in the source graph, then
/// resolve a root-file theorem name or alias. Returns its canonical identity.
/// Does not emit native artifacts or invoke an external prover.
/// Returning an identity does not claim an axiom-free proof. Use the details
/// variant to inspect the selected theorem's logical foundation inventory.
pub fn check_theorem_from_path_with_config(
    source: &str,
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<String, Diagnostic> {
    check_theorem_details_from_path_with_config(source, path, config, name)
        .map(|checked| checked.name)
}

/// A checked target with its transitive logical assumptions. An empty basis
/// means none of the explicit classical foundation constants is reachable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedTheorem {
    pub budget: crate::ProofBudget,
    pub name: String,
    pub foundations: Vec<String>,
}

/// Validate the complete program, select a theorem, and audit types and bodies
/// reachable from it for the fixed logical foundation constants.
pub fn check_theorem_details_from_path_with_config(
    source: &str,
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<CheckedTheorem, Diagnostic> {
    // Invalid global settings still receive the general frontend's diagnostics.
    // All contextual source forms likewise fall back; this probe grants no
    // import, generator, private-name, or authored-gensym authority.
    if config
        .values
        .get("async-lowering")
        .is_none_or(|value| value == "graph")
    {
        if let Some(checked) =
            crate::proof::check_standalone_theorem(source, path, config.proof_budget, name)
        {
            return checked;
        }
    }
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
    // graph before proof checking allocates its independent kernel terms.
    drop(prepared);
    drop(expansion);
    let validation = crate::timing::stage("semantic_validate");
    owned.validate().map_err(|(message, code, span, labels)| {
        crate::analysis_diagnostic(message, code, span, labels, owned.program())
    })?;
    drop(validation);

    let program = owned.program();
    let canonical = resolve_root_name(program, name).ok_or_else(|| {
        Diagnostic::new(DiagnosticCode::Proof, format!("unknown theorem '{name}'"))
            .with_source(path.display().to_string(), source)
    })?;
    let proposition = program.items.iter().find_map(|item| match item {
        Item::Proof { name, proposition } if name == canonical => Some(proposition),
        _ => None,
    });
    let Some(proposition) = proposition else {
        return Err(selection_error(
            program,
            canonical,
            name,
            "is not a theorem",
            path,
            source,
        ));
    };
    if matches!(proposition, Expr::List(parts)
        if matches!(parts.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#proof-definition" | "proof-definition"
                | "#proof-opaque" | "proof-opaque"
                | "#proof-inductive" | "proof-inductive")))
    {
        return Err(selection_error(
            program,
            canonical,
            name,
            "is a mathematical definition, not a theorem",
            path,
            source,
        ));
    }
    crate::warnings::record_program(program);
    let _audit = crate::timing::stage("proof_foundation_audit");
    let foundations =
        crate::proof::checked_theorem_foundations(program, canonical).map_err(|message| {
            crate::analysis_diagnostic(
                message,
                DiagnosticCode::Proof,
                crate::proof::declaration_span(program, canonical),
                Vec::new(),
                program,
            )
        })?;
    Ok(CheckedTheorem {
        budget: program.proof_budget,
        name: canonical.to_owned(),
        foundations,
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
        DiagnosticCode::Proof,
        span,
        Vec::new(),
        program,
    );
    if error.source_name.is_none() {
        error = error.with_source(path.display().to_string(), source);
    }
    error
}
