//! Select a theorem only after the complete source graph has been checked.
use std::path::Path;

use crate::{CompileConfig, Diagnostic, DiagnosticCode, Expr, Item, Program};

/// Check every ordinary and mathematical obligation in the source graph, then
/// resolve a root-file theorem name or alias. Returns its canonical identity.
/// Does not emit native artifacts or invoke an external prover.
pub fn check_theorem_from_path_with_config(
    source: &str,
    path: &Path,
    config: &CompileConfig,
    name: &str,
) -> Result<String, Diagnostic> {
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
    Ok(canonical.to_owned())
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
