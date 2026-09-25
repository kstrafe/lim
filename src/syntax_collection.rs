//! Closed-world syntax collections: imports/cfg first, freeze second,
//! generator evaluation last. Generators cannot mutate these snapshots.
use crate::source_error::SourceError;
use crate::{DiagnosticCode, Expr, SpannedExpr};
use std::collections::{BTreeMap, HashMap};

fn error(message: impl Into<String>, source: &SpannedExpr, child: usize) -> SourceError {
    SourceError::new(message, DiagnosticCode::Generator).at(source
        .children
        .get(child)
        .unwrap_or(source)
        .span)
}

fn name<'a>(items: &'a [Expr], index: usize, source: &SpannedExpr) -> Result<&'a str, SourceError> {
    match items.get(index) {
        Some(Expr::Symbol(name)) if !name.starts_with('#') && !name.starts_with('@') => Ok(name),
        _ => Err(error(
            "syntax collection names and contribution keys must be identifiers",
            source,
            index,
        )),
    }
}

pub(crate) fn freeze(
    forms: Vec<SpannedExpr>,
) -> Result<(Vec<SpannedExpr>, HashMap<String, Expr>), SourceError> {
    let mut collections: HashMap<String, BTreeMap<String, Expr>> = HashMap::new();
    for form in &forms {
        let Expr::List(items) = &form.expr else {
            continue;
        };
        if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#syntax-collection") {
            continue;
        }
        if items.len() != 2 {
            return Err(error("#syntax-collection requires one name", form, 0));
        }
        let name = name(items, 1, form)?;
        if collections.insert(name.into(), BTreeMap::new()).is_some() {
            return Err(error(
                format!("duplicate syntax collection '{name}'"),
                form,
                1,
            ));
        }
    }
    let mut remaining = Vec::new();
    for form in forms {
        let Expr::List(items) = &form.expr else {
            remaining.push(form);
            continue;
        };
        match items.first() {
            Some(Expr::Symbol(head)) if head == "#syntax-collection" => {}
            Some(Expr::Symbol(head)) if head == "#syntax-contribute" => {
                if items.len() != 4 {
                    return Err(error(
                        "#syntax-contribute requires a collection, unique key, and syntax value",
                        &form,
                        0,
                    ));
                }
                let collection = name(items, 1, &form)?;
                let key = name(items, 2, &form)?;
                let entries = collections.get_mut(collection).ok_or_else(|| {
                    error(
                        format!("unknown syntax collection '{collection}'"),
                        &form,
                        1,
                    )
                })?;
                if let Some(previous) = entries.get(key) {
                    if previous != &items[3] {
                        return Err(error(format!("conflicting contribution '{key}' to syntax collection '{collection}'"), &form, 2));
                    }
                } else {
                    entries.insert(key.into(), items[3].clone());
                }
            }
            _ => remaining.push(form),
        }
    }
    Ok((
        remaining,
        collections
            .into_iter()
            .map(|(name, entries)| (name, Expr::List(entries.into_values().collect())))
            .collect(),
    ))
}
