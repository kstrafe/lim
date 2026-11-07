//! Generated-file authority, reconstructed from validated expansion contexts.
use crate::{Expr, Span, SpannedExpr};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub(crate) struct Syntax {
    pub expr: Expr,
    context: Option<Span>,
}

impl From<Expr> for Syntax {
    fn from(expr: Expr) -> Self {
        Self {
            expr,
            context: None,
        }
    }
}

impl Syntax {
    pub fn authored(expr: Expr, context: Option<Span>) -> Self {
        Self { expr, context }
    }

    pub fn authority(&self) -> Option<Span> {
        self.context
    }
    pub fn has_authority(&self) -> bool {
        self.context.is_some()
    }

    pub fn identity(&self) -> String {
        // Inputs were checked before interpretation. Permissions belong to the
        // producing file, not individual input tokens.
        format!("{:?}", self.expr)
    }

    pub fn list(values: Vec<Self>) -> Self {
        Expr::List(values.into_iter().map(|value| value.expr).collect()).into()
    }

    pub fn parts(self) -> Option<Vec<Self>> {
        let Expr::List(items) = self.expr else {
            return None;
        };
        Some(
            items
                .into_iter()
                .map(|expr| Self::authored(expr, self.context))
                .collect(),
        )
    }

    pub fn wrap(self, constructor: fn(Box<Expr>) -> Expr) -> Self {
        Self::authored(constructor(Box::new(self.expr)), self.context)
    }

    pub fn attach(&self, tree: &SpannedExpr, target: &mut HashMap<u32, Span>) {
        if let Some(context) = self.context {
            target.insert(tree.span.source_id, context);
        }
    }

    pub fn from_tree(tree: &SpannedExpr, contexts: &HashMap<u32, Span>) -> Self {
        Self::authored(tree.expr.clone(), source_context(tree.span, contexts))
    }
}

pub(crate) fn source_context(span: Span, contexts: &HashMap<u32, Span>) -> Option<Span> {
    contexts.get(&span.source_id).copied()
}

pub(crate) const HEADER: &str = "#generated-context";

pub(crate) fn is_header(expr: &Expr) -> bool {
    matches!(expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == HEADER))
}

pub(crate) fn matches_key(key: &str, forms: &[SpannedExpr]) -> bool {
    key.lines()
        .find_map(|line| line.strip_prefix("context="))
        .is_none_or(|expected| {
            forms.first().is_some_and(|form| {
                crate::expression_source(&form.expr).is_ok_and(|actual| actual == expected)
            })
        })
}

pub(crate) fn validate_output(expr: &Expr) -> Result<(), String> {
    if is_header(expr) {
        return Err(
            "#generated-context is compiler-owned; a generator cannot manufacture a context header"
                .into(),
        );
    }
    match expr {
        Expr::Symbol(name) if name.starts_with('@') => {
            Err("@ qualification must be written in source before generator execution, not manufactured by a generator".into())
        }
        Expr::List(items) => { for item in items { validate_output(item)?; } Ok(()) }
        Expr::Quote(inner) | Expr::QuasiQuote(inner) | Expr::Unquote(inner) | Expr::UnquoteSplicing(inner) => validate_output(inner),
        _ => Ok(()),
    }
}

pub(crate) fn restore(expressions: Vec<Expr>) -> Vec<Syntax> {
    expressions
        .into_iter()
        .filter(|expr| !is_header(expr))
        .map(Syntax::from)
        .collect()
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
pub(crate) fn without_header(source: &str) -> String {
    crate::parse(source)
        .unwrap()
        .into_iter()
        .filter(|form| !is_header(&form.expr))
        .map(|form| crate::expression_source(&form.expr).unwrap())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Compiler lowerings preserve the source file's context, not token spelling.
pub(crate) fn transfer_builtin(
    input: &SpannedExpr,
    output: &SpannedExpr,
    contexts: &mut HashMap<u32, Span>,
) {
    if let Some(context) = source_context(input.span, contexts) {
        contexts.insert(output.span.source_id, context);
    }
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    #[test]
    fn generated_context_applies_to_the_file_not_individual_tokens() {
        let author = Span::new(1, 9, 1, 2);
        let mut tree = crate::parse("(#fn generated () #u64 (#return 42u64))")
            .unwrap()
            .remove(0);
        crate::set_source_id(&mut tree, 7);
        let mut contexts = HashMap::new();
        Syntax::authored(tree.expr.clone(), Some(author)).attach(&tree, &mut contexts);
        assert_eq!(contexts.len(), 1);
        assert_eq!(
            source_context(tree.children[1].span, &contexts),
            Some(author)
        );
        assert_eq!(source_context(author, &contexts), None);
    }
}
