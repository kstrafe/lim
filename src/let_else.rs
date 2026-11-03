//! Resolve compact enum patterns using declarations, never RHS type inference.
use std::collections::HashMap;

use crate::{source_error::SourceError, Expr, Item, SourceExpression, Span, SpannedExpr};

fn head(node: &SpannedExpr) -> &str {
    match &node.expr {
        Expr::List(parts) => match parts.first() {
            Some(Expr::Symbol(name)) => name,
            _ => "",
        },
        _ => "",
    }
}

fn compact(node: &SpannedExpr) -> bool {
    head(node) == "#let-else" && node.children.len() == 4 && head(&node.children[3]) == "#else"
}

fn needed(node: &SpannedExpr) -> bool {
    compact(node) || node.children.iter().any(needed)
}

fn variant_name(pattern: &SpannedExpr) -> Option<&str> {
    match &pattern.expr {
        Expr::Symbol(name) => Some(name),
        Expr::List(_) => pattern.children.first().and_then(variant_name),
        _ => None,
    }
}

fn symbol(name: impl Into<String>, span: Span) -> SpannedExpr {
    SpannedExpr {
        expr: Expr::Symbol(name.into()),
        span,
        children: vec![].into(),
    }
}

fn sync(node: &mut SpannedExpr) {
    if !node.children.is_empty() {
        node.expr = Expr::List(
            node.children
                .iter()
                .map(|child| child.expr.clone())
                .collect(),
        );
    }
}

fn error(message: impl Into<String>, span: Span) -> SourceError {
    SourceError::new(message, crate::DiagnosticCode::Type).at(span)
}

/// Keep canonical statement metadata and runtime items in sync, preserving all
/// original spans. Expansion planning may defer not-yet-emitted protocol enums.
pub(crate) fn normalize(
    items: &mut [Item],
    statement_spans: &mut HashMap<(String, usize), Span>,
    statement_expressions: &mut HashMap<(String, usize), SpannedExpr>,
    declaration_expressions: &mut HashMap<String, SourceExpression>,
    declaration_occurrences: &mut HashMap<String, Vec<SourceExpression>>,
    defer_missing_enums: bool,
) -> Result<(), SourceError> {
    if !declaration_expressions.values().any(|node| needed(node)) {
        return Ok(());
    }
    let owners = items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { name, variants, .. } => Some((name, variants)),
            _ => None,
        })
        .flat_map(|(name, variants)| {
            variants
                .iter()
                .map(move |variant| (variant.name.clone(), name.clone()))
        })
        .collect::<HashMap<_, _>>();
    fn unavailable(node: &SpannedExpr, owners: &HashMap<String, String>) -> bool {
        (compact(node)
            && variant_name(&node.children[1]).is_some_and(|name| !owners.contains_key(name)))
            || node.children.iter().any(|child| unavailable(child, owners))
    }
    for item in items {
        let Item::Function(function) = item else {
            continue;
        };
        let name = function.name.clone();
        let Some(original) = declaration_expressions
            .get(&name)
            .filter(|node| needed(node))
        else {
            continue;
        };
        if defer_missing_enums && unavailable(original, &owners) {
            continue;
        }
        let mut source = original.clone();
        lower(&mut source, &owners)?;
        let mut expression = crate::normalize_keywords(source.expr.clone());
        crate::normalize_match_cases_expr(&mut expression);
        *item = crate::parse_item(&expression).map_err(|message| error(message, source.span))?;
        statement_spans.retain(|(owner, _), _| owner != &name);
        statement_expressions.retain(|(owner, _), _| owner != &name);
        crate::collect_function_statement_spans(&source, statement_spans, statement_expressions);
        declaration_expressions.insert(name.clone(), source.clone());
        if let Some(occurrences) = declaration_occurrences.get_mut(&name) {
            for occurrence in occurrences
                .iter_mut()
                .filter(|node| node.span == source.span)
            {
                *occurrence = source.clone();
            }
        }
    }
    Ok(())
}

fn lower(node: &mut SpannedExpr, owners: &HashMap<String, String>) -> Result<(), SourceError> {
    for child in &mut node.children {
        lower(child, owners)?;
    }
    sync(node);
    if !compact(node) {
        return Ok(());
    }
    let pattern = &node.children[1];
    let variant = variant_name(pattern)
        .ok_or_else(|| error("let-else requires a named enum variant", pattern.span))?;
    let owner = owners.get(variant).ok_or_else(|| {
        error(
            format!("unknown enum variant '{variant}' in let-else"),
            pattern.span,
        )
    })?;
    let mut fallback = node.children[3].clone();
    // The internal typed form can also bind a failure pattern. Plain #else
    // deliberately exposes no success or failure bindings.
    let fallback_head_span = fallback.children[0].span;
    fallback.children.insert(1, symbol("_", fallback_head_span));
    sync(&mut fallback);
    node.children = vec![
        node.children[0].clone(),
        pattern.clone(),
        symbol(owner, pattern.span),
        node.children[2].clone(),
        fallback,
    ]
    .into();
    sync(node);
    Ok(())
}
