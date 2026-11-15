//! Record conditionals lower only within function syntax, including literal
//! generator function templates. The ordinary conditional and block checkers
//! retain control flow, evidence, scope, and ownership semantics.
use std::collections::HashSet;

use crate::{Expr, ParseError, Span, SpannedExpr as Node};

fn name(node: &Node) -> &str {
    match &node.expr {
        Expr::Symbol(name) => name,
        _ => "",
    }
}

fn list(children: Vec<Node>, span: Span) -> Node {
    Node {
        expr: Expr::List(children.iter().map(|child| child.expr.clone()).collect()),
        span,
        children: children.into(),
    }
}

fn error(message: String, span: Span) -> ParseError {
    ParseError { message, span }
}

fn record(node: &Node, records: &HashSet<usize>) -> bool {
    records.contains(&node.span.start)
        || node.children.first().is_some_and(|pair| {
            pair.children
                .first()
                .is_some_and(|key| name(key).starts_with('#'))
        })
}

fn branch(value: Node, source: Option<&str>) -> Node {
    // Both inline and indented colon values retain the colon's source offset.
    // Their forms are statements in an existing #block; #return/#break never
    // become newly accepted bare expressions. An '=' value stays an expression.
    if source.and_then(|source| source.as_bytes().get(value.span.start)) != Some(&b':') {
        return value;
    }
    let span = value.span;
    let mut children = vec![Node {
        expr: Expr::Symbol("#block".into()),
        span: Span {
            end: span.start,
            ..span
        },
        children: Vec::new().into(),
    }];
    if value
        .children
        .first()
        .is_some_and(|child| matches!(child.expr, Expr::List(_)))
    {
        // A layout/semicolon collection contains complete forms.
        children.extend(value.children.iter().cloned());
    } else if value.children.len() == 1 && !name(&value.children[0]).starts_with('#') {
        // A scalar-only colon group supplies its sole value.
        children.push(value.children[0].clone());
    } else {
        // An inline colon introduces one form, e.g. `#then: #return 42;`.
        children.push(value);
    }
    list(children, span)
}

fn expression(
    node: &mut Node,
    records: &HashSet<usize>,
    source: Option<&str>,
) -> Result<(), ParseError> {
    if !matches!(node.expr, Expr::List(_)) || node.children.is_empty() {
        // Quotes/unquotes remain data here. Literal #fn containers were
        // independently visited by the reader when their syntax was complete.
        return Ok(());
    }
    let head = name(&node.children[0]).to_owned();
    if matches!(
        head.as_str(),
        "#gn" | "#gn-fn" | "#fn" | "#unsafe-fn" | "#effects"
    ) || matches!(node.children[0].expr, Expr::Generate)
    {
        return Ok(());
    }
    if matches!(head.as_str(), "#if" | "#if-valid")
        && node.children.get(1).is_some_and(|node| record(node, records))
    {
        if node.children.len() != 2 {
            return Err(error(
                format!("{head} record must be its only operand"),
                node.children[2].span,
            ));
        }
        let fields = &node.children[1];
        let mut values: [Option<Node>; 3] = [None, None, None];
        const KEYS: [&str; 3] = ["#condition", "#then", "#else"];
        for pair in &fields.children {
            if pair.children.len() != 2 {
                return Err(error(
                    format!("{head} record requires key/value pairs"),
                    pair.span,
                ));
            }
            let key = &pair.children[0];
            let Some(index) = KEYS.iter().position(|expected| *expected == name(key)) else {
                return Err(error(
                    format!("unknown {head} field '{}'", name(key)),
                    key.span,
                ));
            };
            if values[index].replace(pair.children[1].clone()).is_some() {
                return Err(error(
                    format!("duplicate {head} field '{}'", name(key)),
                    key.span,
                ));
            }
        }
        for (key, value) in KEYS.iter().zip(&values) {
            if value.is_none() {
                return Err(error(
                    format!("{head} record requires '{key}'"),
                    fields.span,
                ));
            }
        }
        let [condition, then_value, else_value] = values.map(Option::unwrap);
        *node = list(
            vec![
                node.children[0].clone(),
                condition,
                branch(then_value, source),
                branch(else_value, source),
            ],
            node.span,
        );
    }
    let operands = usize::from(matches!(
        node.children[0].expr,
        Expr::Symbol(_) | Expr::Function(_) | Expr::Generate
    ));
    for child in node.children.iter_mut().skip(operands) {
        expression(child, records, source)?;
    }
    node.expr = Expr::List(node.children.iter().map(|child| child.expr.clone()).collect());
    Ok(())
}

pub(super) fn function(
    mut node: Node,
    records: &HashSet<usize>,
    source: Option<&str>,
) -> Result<Node, ParseError> {
    if !node
        .children
        .first()
        .is_some_and(|head| matches!(name(head), "#fn" | "#unsafe-fn"))
    {
        return Ok(node);
    }
    // The record reader has already normalized the signature. Parameter and
    // result types are syntax, not executable conditional operands.
    for child in node.children.iter_mut().skip(4) {
        expression(child, records, source)?;
    }
    node.expr = Expr::List(node.children.iter().map(|child| child.expr.clone()).collect());
    Ok(node)
}
