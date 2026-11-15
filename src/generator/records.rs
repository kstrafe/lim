//! Labelled syntax inputs. Records remain ordinary canonical pair lists.
use super::{at_span, GeneratorParameter};
use crate::{source_error::SourceError, Expr, Span, SpannedExpr};
use std::collections::{HashMap, HashSet};

fn child(source: &SpannedExpr, index: usize) -> &SpannedExpr {
    source.children.get(index).unwrap_or(source)
}

pub(super) fn parameters(
    expression: &Expr,
    source: &SpannedExpr,
) -> Result<Vec<GeneratorParameter>, SourceError> {
    let fail = |message: String, span| at_span(message, span, "generator record pattern");
    let Expr::List(fields) = expression else {
        return Err(fail(
            "parameters require a named record pattern".into(),
            source.span,
        ));
    };
    let mut labels = HashSet::new();
    let mut bindings = HashSet::new();
    let mut result = Vec::with_capacity(fields.len());
    for (index, field) in fields.iter().enumerate() {
        let tree = child(source, index);
        let Expr::List(pair) = field else {
            return Err(fail(
                "parameters require (label binding) pairs; positional parameters are not supported"
                    .into(),
                tree.span,
            ));
        };
        let [Expr::Symbol(label), pattern] = pair.as_slice() else {
            return Err(fail(
                "parameters require (label binding) pairs".into(),
                tree.span,
            ));
        };
        if label.starts_with(['#', '@']) || label.is_empty() {
            return Err(fail(
                format!("invalid generator argument label '{label}'"),
                child(tree, 0).span,
            ));
        }
        if !labels.insert(label.clone()) {
            return Err(fail(
                format!("duplicate generator argument label '{label}'"),
                child(tree, 0).span,
            ));
        }
        let value = child(tree, 1);
        let (name, annotations, binding_span) = match pattern {
            Expr::Symbol(name) => (name, &[][..], value.span),
            Expr::List(parts) => match parts.first() {
                Some(Expr::Symbol(name)) => (name, &parts[1..], child(value, 0).span),
                _ => {
                    return Err(fail(
                        "record values must bind a name or (binding Capability...)".into(),
                        value.span,
                    ))
                }
            },
            _ => {
                return Err(fail(
                    "record values must bind a name or (binding Capability...)".into(),
                    value.span,
                ))
            }
        };
        if name.starts_with(['#', '@']) || name.is_empty() {
            return Err(fail(
                format!("invalid generator binding '{name}'"),
                binding_span,
            ));
        }
        if !bindings.insert(name.clone()) {
            return Err(fail(
                format!("duplicate generator binding '{name}'"),
                binding_span,
            ));
        }
        let mut capabilities = Vec::with_capacity(annotations.len());
        for (index, annotation) in annotations.iter().enumerate() {
            match annotation {
                Expr::Symbol(name) if !name.starts_with(['#', '@']) => {
                    capabilities.push(name.clone())
                }
                _ => {
                    return Err(fail(
                        "generator capability annotations must be capability names".into(),
                        child(value, index + 1).span,
                    ))
                }
            }
        }
        result.push(GeneratorParameter {
            label: label.clone(),
            name: name.clone(),
            capabilities,
        });
    }
    Ok(result)
}

pub(super) struct ArgumentError<'a> {
    pub message: String,
    pub expression: &'a Expr,
}

/// Validate all labels before evaluating any value. The returned sequence is
/// in written order; each index identifies its declaration-order binding.
pub(super) fn arguments<'a>(
    items: &'a [Expr],
    parameters: &[GeneratorParameter],
    operation: &str,
) -> Result<Vec<(usize, &'a Expr)>, ArgumentError<'a>> {
    let fail = |message, expression| ArgumentError {
        message,
        expression,
    };
    if items.len() != 3 {
        return Err(fail(format!("{operation} requires exactly one named argument record; positional arguments are not supported"), items.get(2).unwrap_or(&items[1])));
    }
    let record = &items[2];
    let Expr::List(fields) = record else {
        return Err(fail(
            format!("{operation} requires a named argument record"),
            record,
        ));
    };
    let mut seen = HashSet::new();
    let mut result = Vec::with_capacity(fields.len());
    for field in fields {
        let Expr::List(pair) = field else {
            return Err(fail(
                format!("{operation} arguments require (label value) pairs"),
                field,
            ));
        };
        let [Expr::Symbol(label), value] = pair.as_slice() else {
            return Err(fail(
                format!("{operation} arguments require (label value) pairs"),
                field,
            ));
        };
        let Some(index) = parameters
            .iter()
            .position(|parameter| parameter.label == *label)
        else {
            return Err(fail(
                format!("{operation} has no argument '{label}'"),
                &pair[0],
            ));
        };
        if !seen.insert(index) {
            return Err(fail(
                format!("{operation} repeats argument '{label}'"),
                &pair[0],
            ));
        }
        result.push((index, value));
    }
    if let Some((_, parameter)) = parameters
        .iter()
        .enumerate()
        .find(|(index, _)| !seen.contains(index))
    {
        return Err(fail(
            format!("{operation} is missing argument '{}'", parameter.label),
            record,
        ));
    }
    Ok(result)
}

/// Match by position in the expression tree, never by token spelling: two
/// identical labels must still identify their distinct authored occurrences.
pub(super) fn source_span(root: &Expr, target: &Expr, source: &SpannedExpr) -> Option<Span> {
    if std::ptr::eq(root, target) {
        return Some(source.span);
    }
    match root {
        Expr::List(items) => items
            .iter()
            .zip(&source.children)
            .find_map(|(item, tree)| source_span(item, target, tree)),
        Expr::Quote(inner)
        | Expr::QuasiQuote(inner)
        | Expr::Unquote(inner)
        | Expr::UnquoteSplicing(inner) => source
            .children
            .first()
            .and_then(|tree| source_span(inner, target, tree)),
        _ => None,
    }
}

pub(super) fn evaluation_spans(
    root: &Expr,
    source: &SpannedExpr,
    output: &mut HashMap<usize, Span>,
) {
    output.insert(std::ptr::from_ref(root) as usize, source.span);
    match root {
        Expr::List(items) => {
            for (item, tree) in items.iter().zip(&source.children) {
                evaluation_spans(item, tree, output);
            }
        }
        Expr::Quote(inner)
        | Expr::QuasiQuote(inner)
        | Expr::Unquote(inner)
        | Expr::UnquoteSplicing(inner) => {
            if let Some(tree) = source.children.first() {
                evaluation_spans(inner, tree, output);
            }
        }
        _ => {}
    }
}

/// Generated artifacts contain their own parsed source spans. Caller layout
/// and argument order therefore do not belong in this syntax artifact key.
/// Other compiler caches continue using the full dependency/span identity.
pub(super) fn dependency_context(forms: &[SpannedExpr], config: &crate::CompileConfig) -> String {
    let declarations = forms
        .iter()
        .filter_map(|form| {
            let Expr::List(items) = &form.expr else {
                return None;
            };
            if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#gn") {
                return None;
            }
            let Some(Expr::Symbol(name)) = items.get(1) else {
                return None;
            };
            let parameters = parameters(items.get(2)?, child(form, 2)).ok()?;
            Some((name.as_str(), parameters))
        })
        .collect::<HashMap<_, _>>();
    let mut settings = config.values.iter().collect::<Vec<_>>();
    settings.sort();
    let mut identity = format!("named-generator-dependencies-v1\ncfg={settings:?}\n");
    for form in forms {
        let canonical = match &form.expr {
            Expr::List(items) if matches!(items.first(), Some(Expr::Generate)) => {
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    declarations.get(name.as_str()).and_then(|parameters| {
                        let values = arguments(items, parameters, "#generate").ok()?;
                        let mut ordered = vec![Expr::List(Vec::new().into()); parameters.len()];
                        for (index, value) in values {
                            ordered[index] = Expr::List(
                                vec![Expr::Symbol(parameters[index].label.clone()), value.clone()]
                                    .into(),
                            );
                        }
                        Some(Expr::List(
                            vec![
                                Expr::Generate,
                                Expr::Symbol(name.clone()),
                                Expr::List(ordered.into()),
                            ]
                            .into(),
                        ))
                    })
                } else {
                    None
                }
            }
            _ => None,
        };
        let syntax = crate::expression_source(canonical.as_ref().unwrap_or(&form.expr))
            .expect("loaded syntax is printable");
        identity.push_str(&format!("{}:{syntax}\n", syntax.len()));
    }
    format!(
        "named-generator-dependencies-v1:{:032x}",
        super::stable_hash(identity.as_bytes())
    )
}
