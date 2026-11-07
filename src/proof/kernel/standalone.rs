//! Check a closed, mathematical-only root without retaining a general Program.
//! The inventory is only a source adapter: the common kernel checks every body.
use super::{check_declarations_with_limits, native_source::Source};
use crate::{CheckedTheorem, Diagnostic, DiagnosticCode, ProofBudget};
use std::{collections::HashSet, path::Path};

pub(crate) fn check(
    text: &str,
    path: &Path,
    budget: ProofBudget,
    target: &str,
) -> Option<Result<CheckedTheorem, Diagnostic>> {
    let inventory = crate::timing::stage("proof_source_inventory");
    let source = Source::standalone(text)?;
    drop(inventory);

    let diagnostic = |message, span: Option<crate::Span>| {
        let source_name = if span.is_some() {
            crate::editor::path_key(path).display().to_string()
        } else {
            path.display().to_string()
        };
        let mut diagnostic =
            Diagnostic::new(DiagnosticCode::Proof, message).with_source(source_name, text);
        if let Some(span) = span {
            diagnostic = diagnostic.with_span(span);
        }
        diagnostic
    };
    Some(validate(&source, budget, target, diagnostic))
}

pub(crate) fn check_file(
    path: &Path,
    config: &crate::CompileConfig,
    target: &str,
) -> Option<Result<CheckedTheorem, crate::TheoremFileError>> {
    let input = crate::timing::stage("input_read");
    let captured = match super::native_file::Input::open(path) {
        Ok(Some(captured)) => captured,
        Ok(None) => return None,
        Err(error) => return Some(Err(crate::TheoremFileError::input(error.to_string()))),
    };
    drop(input);
    let snapshot = match captured {
        super::native_file::Input::Memory(text) => {
            // A bounded resident input keeps the existing small-proof path.
            // The consumed bytes remain immutable through any general fallback.
            return Some(match check(&text, path, config.proof_budget, target) {
                Some(checked) => checked.map_err(|mut diagnostic| {
                    let rendered =
                        crate::render_diagnostic(&diagnostic, &text, &path.display().to_string());
                    diagnostic.source_text = None;
                    crate::TheoremFileError::positioned(diagnostic, rendered)
                }),
                None => crate::theorem::check_general(&text, path, config, target).map_err(
                    |diagnostic| crate::TheoremFileError::from_diagnostic(diagnostic, &text, path),
                ),
            });
        }
        super::native_file::Input::Paged(snapshot) => snapshot,
    };
    let inventory = crate::timing::stage("proof_source_inventory");
    let Some(source) = Source::standalone_snapshot(snapshot.clone()) else {
        drop(inventory);
        return Some(match snapshot.text() {
            Ok(text) => {
                crate::theorem::check_general(&text, path, config, target).map_err(|diagnostic| {
                    crate::TheoremFileError::from_diagnostic(diagnostic, &text, path)
                })
            }
            Err(error) => Err(crate::TheoremFileError::input(error.to_string())),
        });
    };
    drop(inventory);
    let diagnostic = |message: String, span: Option<crate::Span>| {
        let source_name = if span.is_some() {
            crate::editor::path_key(path).display().to_string()
        } else {
            path.display().to_string()
        };
        let mut diagnostic = Diagnostic::new(DiagnosticCode::Proof, message);
        diagnostic.source_name = Some(source_name.clone());
        diagnostic.span = span;
        let mut rendered = format!(
            "{}[{}]: {}",
            diagnostic.severity.as_str(),
            diagnostic.code_string(),
            diagnostic.message
        );
        if let Some(span) = span {
            // Build only the real source hunk; never attach a partial source
            // string to a diagnostic carrying global byte offsets.
            match snapshot.hunk(&source_name, span) {
                Ok(hunk) => rendered.push_str(&hunk),
                Err(why) => {
                    rendered.push_str(&format!("\n  = note: source excerpt unavailable: {why}"))
                }
            }
        }
        crate::TheoremFileError::positioned(diagnostic, rendered)
    };
    Some(validate(&source, config.proof_budget, target, diagnostic))
}

pub(super) fn validate<E>(
    source: &Source<'_>,
    budget: ProofBudget,
    target: &str,
    diagnostic: impl Fn(String, Option<crate::Span>) -> E,
) -> Result<CheckedTheorem, E> {
    let validation = crate::timing::stage("semantic_validate");
    // Selection never skips obligations, even in unrelated declarations.
    check_declarations_with_limits(source, budget, &HashSet::new(), source.proof_limits())
        .map_err(|(name, why)| {
            diagnostic(
                format!("theorem '{}': {why}", crate::file_access::local_name(&name)),
                source.named_span(&name),
            )
        })?;
    drop(validation);
    let span = source
        .named_span(target)
        .ok_or_else(|| diagnostic(format!("unknown theorem '{target}'"), None))?;
    if !source.is_theorem(target) {
        return Err(diagnostic(
            format!("'{target}' is a mathematical definition, not a theorem"),
            Some(span),
        ));
    }
    let _audit = crate::timing::stage("proof_foundation_audit");
    let foundations = source
        .foundation_dependencies(target)
        .map_err(|why| diagnostic(why, Some(span)))?;
    Ok(CheckedTheorem {
        budget,
        name: target.to_owned(),
        foundations,
    })
}
