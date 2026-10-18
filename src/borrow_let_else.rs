//! Borrowed let-else is ordinary borrowed matching, not an asserting projection.
use std::collections::HashMap;

use crate::{borrow_case::Mode, source_error::SourceError, Expr, Item, Span, SpannedExpr, Type};

pub(crate) fn mode(name: &str) -> Option<Mode> {
    Some(match name.trim_start_matches('#') {
        "let-else-ref" => Mode {
            pinned: false,
            mutable: false,
        },
        "let-else-ref-mut" => Mode {
            pinned: false,
            mutable: true,
        },
        "let-else-pin" => Mode {
            pinned: true,
            mutable: false,
        },
        "let-else-pin-mut" => Mode {
            pinned: true,
            mutable: true,
        },
        _ => return None,
    })
}

fn head(node: &SpannedExpr) -> &str {
    match &node.expr {
        Expr::List(parts) => match parts.first() {
            Some(Expr::Symbol(name)) => name,
            _ => "",
        },
        _ => "",
    }
}
fn needed(node: &SpannedExpr) -> bool {
    mode(head(node)).is_some() || node.children.iter().any(needed)
}
fn symbol(name: impl Into<String>, span: Span) -> SpannedExpr {
    SpannedExpr {
        expr: Expr::Symbol(name.into()),
        span,
        children: vec![],
    }
}
fn list(children: Vec<SpannedExpr>, span: Span) -> SpannedExpr {
    SpannedExpr {
        expr: Expr::List(children.iter().map(|node| node.expr.clone()).collect()),
        span,
        children,
    }
}
fn form(name: &str, args: Vec<SpannedExpr>, span: Span) -> SpannedExpr {
    list(
        std::iter::once(symbol(name, span)).chain(args).collect(),
        span,
    )
}
fn error(message: impl Into<String>, span: Span) -> SourceError {
    SourceError::new(message, crate::DiagnosticCode::Type).at(span)
}
fn type_node(kind: &Type, span: Span) -> Result<SpannedExpr, SourceError> {
    let mut node = crate::parse(&crate::type_source(kind))
        .map_err(|message| error(message.to_string(), span))?
        .remove(0);
    fn stamp(node: &mut SpannedExpr, span: Span) {
        node.span = span;
        for child in &mut node.children {
            stamp(child, span);
        }
    }
    stamp(&mut node, span);
    Ok(node)
}

/// Keep the lowered source tree and runtime item identical so checked binding
/// identities, diagnostics and native emission all use the same ordinary match.
pub(crate) fn normalize(
    items: &mut [Item],
    statement_spans: &mut HashMap<(String, usize), Span>,
    statement_expressions: &mut HashMap<(String, usize), SpannedExpr>,
    declaration_expressions: &mut HashMap<String, SpannedExpr>,
    declaration_occurrences: &mut HashMap<String, Vec<SpannedExpr>>,
    defer_missing_enums: bool,
) -> Result<(), SourceError> {
    if !declaration_expressions.values().any(needed) {
        return Ok(());
    }
    let mut enums = HashMap::new();
    let mut aliases = HashMap::new();
    for item in items.iter() {
        match item {
            Item::Enum { name, variants, .. } => {
                enums.insert(name.clone(), variants.clone());
            }
            Item::TypeAlias { name, target, .. } => {
                aliases.insert(name.clone(), target.clone());
            }
            _ => {}
        }
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
        let mut source = original.clone();
        fn unavailable(
            node: &SpannedExpr,
            enums: &HashMap<String, Vec<crate::EnumVariant>>,
            aliases: &HashMap<String, Type>,
        ) -> bool {
            if mode(head(node)).is_some() {
                if let Some(kind) = node.children.get(2).and_then(|kind| {
                    crate::parse_type(Some(&crate::normalize_keywords(kind.expr.clone()))).ok()
                }) {
                    if let Ok(
                        Type::Reference { target, .. } | Type::PinnedReference { target, .. },
                    ) = crate::typed_ir::resolve_type(&kind, aliases)
                    {
                        if let Type::Named(name) = target.as_ref() {
                            if !enums.contains_key(name) {
                                return true;
                            }
                        }
                    }
                }
            }
            node.children
                .iter()
                .any(|child| unavailable(child, enums, aliases))
        }
        // Graph planning may know a generated protocol's name before its enum
        // declaration exists. Final program normalization is authoritative.
        if defer_missing_enums && unavailable(&source, &enums, &aliases) {
            continue;
        }
        let identity = format!("{name}:{}:{}", source.span.source_id, source.span.start);
        let mut names = crate::gensym::Scope::new('b', &identity);
        lower(&mut source, &enums, &aliases, &mut names)?;
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

fn lower(
    node: &mut SpannedExpr,
    enums: &HashMap<String, Vec<crate::EnumVariant>>,
    aliases: &HashMap<String, Type>,
    names: &mut crate::gensym::Scope,
) -> Result<(), SourceError> {
    let mut children = Vec::with_capacity(node.children.len());
    for mut child in std::mem::take(&mut node.children) {
        lower(&mut child, enums, aliases, names)?;
        children.push(child);
    }
    node.children = children;
    if let Expr::List(parts) = &mut node.expr {
        if !node.children.is_empty() {
            *parts = node
                .children
                .iter()
                .map(|child| child.expr.clone())
                .collect();
        }
    }
    let Some(mode) = mode(head(node)) else {
        return Ok(());
    };
    let span = node.span;
    let xs = &node.children;
    if xs.len() < 5 {
        return Err(error(
            "borrowed let-else requires a pattern, reference type, value and diverging fallback",
            span,
        ));
    }
    let input_type = crate::parse_type(Some(&crate::normalize_keywords(xs[2].expr.clone())))
        .map_err(|message| error(message, xs[2].span))?;
    let resolved = crate::typed_ir::resolve_type(&input_type, aliases)
        .map_err(|message| error(message, xs[2].span))?;
    let target = match &resolved {
        Type::Reference { mutable, target } if !mode.pinned && (!mode.mutable || *mutable) => target,
        Type::PinnedReference { mutable, target } if mode.pinned && (!mode.mutable || *mutable) => target,
        _ => return Err(error("borrowed let-else mode requires a compatible ordinary or pinned reference type and mutability", xs[2].span)),
    };
    let Type::Named(owner) = target.as_ref() else {
        return Err(error(
            "borrowed let-else requires a reference to an enum",
            xs[2].span,
        ));
    };
    let variants = enums.get(owner).ok_or_else(|| {
        error(
            format!("borrowed let-else requires an enum; '{owner}' is not an enum"),
            xs[2].span,
        )
    })?;
    let (variant_name, binder) = match &xs[1].expr {
        Expr::Symbol(name) => (name.as_str(), None),
        Expr::List(parts) if parts.len() == 2 => match &parts[0] {
            Expr::Symbol(name) => (name.as_str(), xs[1].children.get(1)),
            _ => {
                return Err(error(
                    "borrowed let-else pattern must name a variant",
                    xs[1].span,
                ))
            }
        },
        _ => {
            return Err(error(
                "borrowed let-else pattern must be Variant or (Variant binding)",
                xs[1].span,
            ))
        }
    };
    let variant = variants
        .iter()
        .find(|variant| variant.name == variant_name)
        .ok_or_else(|| {
            error(
                format!("'{variant_name}' is not a variant of '{owner}'"),
                xs[1].children.first().unwrap_or(&xs[1]).span,
            )
        })?;
    let result_type = match (variant.fields.first(), binder) {
        (None, None) => Type::Unit,
        (Some(payload), Some(binder)) if matches!(&binder.expr, Expr::Symbol(_)) => {
            if matches!(&binder.expr, Expr::Symbol(name) if name == "_") {
                Type::Unit
            } else {
                mode.reference(
                    crate::typed_ir::resolve_type(payload, aliases)
                        .map_err(|message| error(message, xs[1].span))?,
                )
            }
        }
        _ => {
            return Err(error(
                "payload variants require one symbol binding; fieldless variants require none",
                xs[1].span,
            ))
        }
    };
    let (failure_pattern, fallback) = if head(&xs[4]) == "#else" {
        if xs.len() != 5 || xs[4].children.len() < 3 {
            return Err(error("#else must contain a failure pattern and diverging statements, and be the only fallback", xs[4].span));
        }
        (
            Some(xs[4].children[1].clone()),
            xs[4].children[2..].to_vec(),
        )
    } else {
        (None, xs[4..].to_vec())
    };
    let statements = fallback
        .iter()
        .map(|node| crate::parse_statement(&crate::normalize_keywords(node.expr.clone())))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|message| error(message, xs[4].span))?;
    if !statements
        .last()
        .is_some_and(crate::typecheck::statement_diverges)
    {
        return Err(error("borrowed let-else fallback must diverge with return, break, continue, panic, or unreachable", xs[4].span));
    }
    // Check the explicitly typed input once. The case binder is compiler-owned,
    // distinct from the user's outer binding (including in the source map).
    let payload = names
        .fresh("borrowed-let-payload")
        .map_err(|message| error(message, span))?;
    let value = if matches!(xs[3].expr, Expr::Symbol(_)) {
        // Reborrow named handles; do not move an exclusive pin/reference.
        let mutable = matches!(
            resolved,
            Type::Reference { mutable: true, .. } | Type::PinnedReference { mutable: true, .. }
        );
        let borrow = match (mode.pinned, mutable) {
            (false, false) => "#borrow",
            (false, true) => "#borrow-mut",
            (true, false) => "#pin-borrow",
            (true, true) => "#pin-borrow-mut",
        };
        form(
            borrow,
            vec![form("#deref", vec![xs[3].clone()], xs[3].span)],
            xs[3].span,
        )
    } else {
        xs[3].clone()
    };
    // Keep the type-checking temporary inside the receiver expression's scope.
    // Returning its handle transfers the loan to the match's own saved receiver;
    // no inaccessible reference local survives this statement in the caller.
    let input = names
        .fresh("borrowed-let-input")
        .map_err(|message| error(message, span))?;
    let receiver = form(
        "#block",
        vec![
            form(
                "#let",
                vec![symbol(&input, xs[3].span), xs[2].clone(), value],
                xs[3].span,
            ),
            symbol(input, xs[3].span),
        ],
        xs[3].span,
    );
    let mut pattern = xs[1].clone();
    let binds_value = !matches!(result_type, Type::Unit);
    if binds_value {
        pattern.children[1] = symbol(&payload, binder.unwrap().span);
        pattern.expr = Expr::List(
            pattern
                .children
                .iter()
                .map(|node| node.expr.clone())
                .collect(),
        );
    }
    // Arms are already in the normalized representation used by parsed source.
    let success_pattern = form(mode.keyword(), vec![pattern], xs[1].span);
    let success_value = if binds_value {
        symbol(&payload, binder.unwrap().span)
    } else {
        list(vec![], xs[1].span)
    };
    let success = list(vec![success_pattern, success_value], xs[1].span);
    let failure_pattern = failure_pattern
        .map(|pattern| {
            if matches!(&pattern.expr, Expr::Symbol(name) if name == "_") {
                pattern
            } else {
                form(mode.keyword(), vec![pattern], xs[4].span)
            }
        })
        .unwrap_or_else(|| symbol("_", xs[4].span));
    let failure = list(
        vec![failure_pattern, form("#block", fallback, xs[4].span)],
        xs[4].span,
    );
    let matched = form("#match", vec![receiver, success, failure], span);
    if binds_value {
        let result_type = type_node(&result_type, xs[2].span)?;
        *node = form(
            "#let",
            vec![binder.unwrap().clone(), result_type, matched],
            span,
        );
    } else {
        *node = matched;
    }
    Ok(())
}
