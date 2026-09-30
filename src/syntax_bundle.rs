//! Immutable literal syntax bundles; explicit list splicing, not type inference.
use std::collections::HashMap;

use crate::{source_error::SourceError, DiagnosticCode, Expr, Span, SpannedExpr};

#[derive(Default)]
pub(crate) struct Bundles {
    pub definitions: HashMap<String, SpannedExpr>,
    pub uses: HashMap<Span, Vec<Span>>,
}

fn head(expression: &SpannedExpr, name: &str) -> bool {
    matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(h)) if h == name))
}

fn child(expression: &SpannedExpr, index: usize) -> SpannedExpr {
    let Expr::List(items) = &expression.expr else {
        unreachable!()
    };
    let mut result = expression
        .children
        .get(index)
        .cloned()
        .unwrap_or_else(|| SpannedExpr {
            expr: items[index].clone(),
            span: expression.span,
            children: vec![],
        });
    // External-import prefixing updates syntax independently of source children.
    result.expr = items[index].clone();
    result
}

fn error(message: impl Into<String>, span: Span) -> SourceError {
    SourceError::new(message, DiagnosticCode::Parse).at(span)
}

fn needs_expansion(expression: &Expr) -> bool {
    let Expr::List(items) = expression else {
        return false;
    };
    if matches!(items.first(), Some(Expr::Symbol(h)) if matches!(h.as_str(), "#gn" | "#gn-fn")) {
        return false;
    }
    matches!(items.first(), Some(Expr::Symbol(h)) if matches!(h.as_str(), "#syntax" | "#syntax-splice"))
        || items.iter().any(needs_expansion)
}

impl Bundles {
    pub fn expand(
        &mut self,
        forms: Vec<SpannedExpr>,
        strict: bool,
    ) -> Result<Vec<SpannedExpr>, SourceError> {
        let mut remaining = Vec::new();
        for form in forms {
            if !head(&form, "#syntax") {
                remaining.push(form);
                continue;
            }
            let Expr::List(items) = &form.expr else {
                unreachable!()
            };
            let [_, Expr::Symbol(name), Expr::List(_)] = items.as_slice() else {
                return Err(error("#syntax requires an identifier and a literal list: (#syntax Name (syntax ...))", form.span));
            };
            if name.starts_with('#') || name.starts_with('@') {
                return Err(error(
                    "syntax bundle names must be user-defined identifiers",
                    child(&form, 1).span,
                ));
            }
            if let Some(previous) = self.definitions.get(name) {
                return Err(error(
                    format!("duplicate syntax bundle '{name}'"),
                    child(&form, 1).span,
                )
                .with_label(previous.span, "previous syntax bundle definition"));
            }
            self.definitions.insert(name.clone(), child(&form, 2));
        }
        let mut budget = 1_000_000usize;
        // Validate all bundles, including unused ones, so cycles never hide.
        let mut names = self.definitions.keys().cloned().collect::<Vec<_>>();
        names.sort();
        for name in names {
            self.walk(
                self.definitions[&name].clone(),
                strict,
                &mut vec![name],
                &mut budget,
                0,
            )?;
        }
        let expanded = remaining
            .into_iter()
            .map(|form| self.walk(form, strict, &mut vec![], &mut budget, 0))
            .collect::<Result<Vec<_>, _>>()?;
        for form in &expanded {
            let Expr::List(items) = &form.expr else {
                continue;
            };
            let Some(Expr::Symbol(kind)) = items.first() else {
                continue;
            };
            let index = match kind.as_str() {
                "#extern-fn" => 2,
                "#fn" | "#unsafe-fn" | "#type" | "#struct" | "#enum" | "#gn" | "#gn-fn"
                | "#let" | "#let-mut" | "#const" | "#static" | "#capability"
                | "#syntax-collection" => 1,
                _ => continue,
            };
            if let Some(Expr::Symbol(name)) = items.get(index) {
                if let Some(definition) = self.definitions.get(name) {
                    return Err(error(
                        format!("declaration '{name}' conflicts with a syntax bundle"),
                        child(form, index).span,
                    )
                    .with_label(definition.span, "syntax bundle defined here"));
                }
            }
        }
        Ok(expanded)
    }

    fn walk(
        &mut self,
        expression: SpannedExpr,
        strict: bool,
        active: &mut Vec<String>,
        budget: &mut usize,
        depth: usize,
    ) -> Result<SpannedExpr, SourceError> {
        if depth > 128 || *budget == 0 {
            return Err(error(
                "syntax bundle expansion exceeds its depth or node limit",
                expression.span,
            ));
        }
        *budget -= 1;
        if !needs_expansion(&expression.expr) {
            return Ok(expression);
        }
        let Expr::List(items) = &expression.expr else {
            return Ok(expression);
        };
        // Generator templates and quoted data stay literal until emitted.
        if matches!(items.first(), Some(Expr::Symbol(h)) if matches!(h.as_str(), "#gn" | "#gn-fn"))
        {
            return Ok(expression);
        }
        if head(&expression, "#syntax-splice") {
            return Err(error(
                "#syntax-splice must be an element of a surrounding list",
                expression.span,
            ));
        }
        if head(&expression, "#syntax") {
            return Err(error(
                "#syntax declarations are only allowed at top level",
                expression.span,
            ));
        }
        let preserve_empty_children = expression.children.is_empty();
        let mut children = Vec::new();
        for index in 0..items.len() {
            let current = child(&expression, index);
            if !head(&current, "#syntax-splice") {
                children.push(self.walk(current, strict, active, budget, depth + 1)?);
                continue;
            }
            let Expr::List(splice) = &current.expr else {
                unreachable!()
            };
            let [_, Expr::Symbol(name)] = splice.as_slice() else {
                return Err(error(
                    "#syntax-splice requires exactly one syntax bundle name",
                    current.span,
                ));
            };
            let Some(definition) = self.definitions.get(name).cloned() else {
                if !strict {
                    children.push(current);
                    continue;
                }
                return Err(error(
                    format!("unknown syntax bundle '{name}'"),
                    current.span,
                ));
            };
            if active.contains(name) {
                return Err(error(
                    format!(
                        "recursive syntax bundle expansion: {} -> {name}",
                        active.join(" -> ")
                    ),
                    current.span,
                )
                .with_label(definition.span, "syntax bundle defined here"));
            }
            active.push(name.clone());
            let expanded = self.walk(definition.clone(), strict, active, budget, depth + 1)?;
            active.pop();
            let Expr::List(values) = &expanded.expr else {
                unreachable!()
            };
            if values.len() > *budget {
                return Err(error(
                    "syntax bundle expansion exceeds its depth or node limit",
                    current.span,
                ));
            }
            *budget -= values.len();
            self.uses
                .entry(current.span)
                .or_default()
                .push(definition.span);
            for index in 0..values.len() {
                let mut value = child(&expanded, index);
                remap(&mut value, current.span);
                children.push(value);
            }
        }
        Ok(SpannedExpr {
            expr: Expr::List(children.iter().map(|child| child.expr.clone()).collect()),
            span: expression.span,
            children: if preserve_empty_children {
                vec![]
            } else {
                children
            },
        })
    }
}

fn remap(expression: &mut SpannedExpr, span: Span) {
    expression.span = span;
    for child in &mut expression.children {
        remap(child, span);
    }
}
