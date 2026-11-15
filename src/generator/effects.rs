//! Rendering of explicitly selected template effects. This never summarizes a
//! runtime body or changes an authored function's written permissions.
use std::collections::BTreeSet;

use crate::{Expr, SpannedExpr, Type};

pub(crate) const RAW_BOUNDARY: &str = "(#effects (#io #global-access))";

/// Names of generated helpers with an explicit effect signature. The caller
/// template includes their declarations; only signature fields are inspected.
pub(crate) fn declared_helpers(sources: &[String]) -> Result<Vec<String>, String> {
    let mut names = BTreeSet::new();
    for source in sources {
        for node in crate::parse(source)? {
            let Expr::List(parts) = node.expr else {
                continue;
            };
            if !matches!(parts.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#fn" | "#unsafe-fn"))
            {
                continue;
            }
            if parts.get(4).is_some_and(crate::effects::is_clause) {
                if let Some(Expr::Symbol(name)) = parts.get(1) {
                    names.insert(name.clone());
                }
            }
        }
    }
    Ok(names.into_iter().collect())
}

pub(crate) fn clause(
    written: Option<&SpannedExpr>,
    raw_boundary: bool,
    callbacks: impl IntoIterator<Item = String>,
) -> Result<String, String> {
    let mut entries = match written.filter(|node| crate::effects::is_clause(&node.expr)) {
        Some(node) => {
            let Expr::List(parts) = &node.expr else {
                unreachable!()
            };
            let Some(Expr::List(entries)) = parts.get(1) else {
                return Err(
                    "generated effect interface lost its written qualification list".into(),
                );
            };
            entries.to_vec()
        }
        None => Vec::new(),
    };
    if raw_boundary {
        for name in ["#io", "#global-access"] {
            let value = Expr::Symbol(name.into());
            if !entries.iter().any(|entry| {
                crate::normalize_keywords(entry.clone()) == crate::normalize_keywords(value.clone())
            }) {
                entries.push(value);
            }
        }
    }
    let callbacks = callbacks.into_iter().collect::<BTreeSet<_>>();
    if !callbacks.is_empty() {
        entries.push(Expr::List(
            vec![
                Expr::Symbol("#effects-of".into()),
                Expr::List(callbacks.into_iter().map(Expr::Symbol).collect()),
            ]
            .into(),
        ));
    }
    if entries.is_empty() {
        return Ok(String::new());
    }
    let value = Expr::List(entries.into());
    crate::effects::Declaration::parse(&value)?;
    crate::expression_source(&Expr::List(
        vec![Expr::Symbol("#effects".into()), value].into(),
    ))
}

pub(crate) fn clone_clause(ty: &Type, declarations: &crate::typed_ir::Declarations) -> String {
    let Ok(Type::Named(owner)) = crate::typed_ir::resolve_type(ty, &declarations.aliases) else {
        return String::new();
    };
    let function = format!("{owner}::clone");
    if declarations.function_id(&function).is_none() {
        return String::new();
    }
    // Names come from checked declaration identities, never type text supplied
    // by a template caller or an inferred summary of the clone body.
    clause(None, false, [function]).expect("checked clone effect interface")
}
