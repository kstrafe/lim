//! Immutable literal syntax bundles; explicit list splicing, not type inference.
use std::collections::HashMap;

use crate::{source_error::SourceError, DiagnosticCode, Expr, Span, SpannedExpr};

#[derive(Default)]
pub(crate) struct Bundles {
    pub definitions: HashMap<String, SpannedExpr>,
    pub uses: HashMap<Span, Vec<Span>>,
    splice_provenance: Option<SpliceProvenance>,
}

struct SpliceProvenance {
    contexts: HashMap<u32, Span>,
    base: usize,
    sources: Vec<(crate::SourceFile, Span)>,
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
            children: vec![].into(),
        });
    // Synthetic expansion trees may not carry children for every literal node.
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
    matches!(items.first(), Some(Expr::Symbol(h)) if matches!(h.as_str(), "#syntax" | "#syntax-splice")
        || (h == "#await" && items.len() == 3 && matches!(items.get(1), Some(Expr::Symbol(_)))))
        || items.iter().any(needs_expansion)
}

impl Bundles {
    pub(crate) fn expand_with_provenance(
        &mut self,
        forms: Vec<SpannedExpr>,
        files: &mut Vec<crate::SourceFile>,
        contexts: &mut HashMap<u32, Span>,
        origins: &mut HashMap<u32, Span>,
    ) -> Result<Vec<SpannedExpr>, SourceError> {
        if !contexts.is_empty() {
            self.splice_provenance = Some(SpliceProvenance {
                contexts: contexts.clone(),
                base: files.len(),
                sources: Vec::new(),
            });
        }
        let result = self.expand(forms, true);
        if let Some(provenance) = self.splice_provenance.take() {
            *contexts = provenance.contexts;
            for (file, origin) in provenance.sources {
                origins.insert(files.len() as u32, origin);
                files.push(file);
            }
        }
        if result.is_ok() {
            // Bundles disappear before runtime parsing. Retain their validated
            // declaration identities, including bundles synthesized by another
            // generator after the ordinary file-resolution pass.
            for (name, definition) in &self.definitions {
                let mut source = definition.span.source_id;
                for _ in 0..origins.len() {
                    let Some(origin) = origins.get(&source) else {
                        break;
                    };
                    source = origin.source_id;
                }
                if let Some(scope) = files
                    .get_mut(source as usize)
                    .and_then(|file| file.file_scope.as_mut())
                {
                    std::sync::Arc::make_mut(scope)
                        .declared
                        .insert(name.clone());
                }
            }
        }
        result
    }

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
                | "#distributed-enum" => 1,
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
        if head(&expression, "#await") {
            let Expr::List(items) = &expression.expr else {
                unreachable!()
            };
            if items.len() == 3 && matches!(items.get(1), Some(Expr::Symbol(_))) {
                let name = child(&expression, 1);
                let splice_head = SpannedExpr {
                    expr: Expr::Symbol("#syntax-splice".into()),
                    span: name.span,
                    children: vec![].into(),
                };
                let splice = SpannedExpr {
                    expr: Expr::List(vec![splice_head.expr.clone(), name.expr.clone()]),
                    span: name.span,
                    children: vec![splice_head, name].into(),
                };
                let children = vec![child(&expression, 0), splice, child(&expression, 2)];
                return self.walk(
                    SpannedExpr {
                        expr: Expr::List(children.iter().map(|child| child.expr.clone()).collect()),
                        span: expression.span,
                        children: children.into(),
                    },
                    strict,
                    active,
                    budget,
                    depth + 1,
                );
            }
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
                if let Some(provenance) = &mut self.splice_provenance {
                    let syntax =
                        crate::generator_authority::Syntax::from_tree(&value, &provenance.contexts);
                    let text = crate::expression_source(&value.expr)?;
                    value = crate::parse(&text)?.remove(0);
                    let source_id = u32::try_from(provenance.base + provenance.sources.len())
                        .map_err(|_| "too many syntax splice sources")?;
                    crate::set_source_id(&mut value, source_id);
                    syntax.attach(&value, &mut provenance.contexts);
                    provenance.sources.push((
                        crate::SourceFile {
                            file_scope: None,
                            path: "<generated syntax splice>".into(),
                            source: text,
                        },
                        current.span,
                    ));
                } else {
                    remap(&mut value, current.span);
                }
                children.push(value);
            }
        }
        Ok(SpannedExpr {
            expr: Expr::List(children.iter().map(|child| child.expr.clone()).collect()),
            span: expression.span,
            children: if preserve_empty_children {
                vec![].into()
            } else {
                children.into()
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
