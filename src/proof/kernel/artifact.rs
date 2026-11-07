//! Recheck a closed mathematical artifact from its frozen source bytes.
//! No imports, generator execution, cached judgments, or general fallback.
use super::{native_file::Snapshot, native_source::Source, standalone};
use crate::{
    CheckedTheorem, Diagnostic, DiagnosticCode, NativeProofLimits, ProofBudget, TheoremFileError,
};
use std::{fs::File, path::Path};

pub fn check_proof_artifact_from_path(
    path: &Path,
    budget: ProofBudget,
    limits: NativeProofLimits,
    target: &str,
) -> Result<CheckedTheorem, TheoremFileError> {
    let limits = limits.validate().map_err(TheoremFileError::input)?;
    let input = File::open(path).map_err(|why| TheoremFileError::input(why.to_string()))?;
    let snapshot = {
        let _stage = crate::timing::stage("input_read");
        Snapshot::capture_with_limit(input, limits.max_bytes)
            .map_err(|why| TheoremFileError::input(why.to_string()))?
    };
    let source = {
        let _stage = crate::timing::stage("proof_source_inventory");
        Source::snapshot_with_limits(snapshot.clone(), limits).map_err(TheoremFileError::input)?
    };
    standalone::validate(
        &source,
        budget,
        target,
        |message, span: Option<crate::Span>| {
            let source_name = crate::editor::path_key(path).display().to_string();
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
                match snapshot.hunk(&source_name, span) {
                    Ok(hunk) => rendered.push_str(&hunk),
                    Err(why) => {
                        rendered.push_str(&format!("\n  = note: source excerpt unavailable: {why}"))
                    }
                }
            }
            TheoremFileError::positioned(diagnostic, rendered)
        },
    )
}
