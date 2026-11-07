use std::{
    fmt,
    ops::{Deref, DerefMut},
    sync::Arc,
};

use crate::SpannedExpr;

/// Shared, copy-on-write storage for a complete immutable declaration source root.
#[derive(Clone, Eq, PartialEq)]
pub(crate) struct SourceExpression(Arc<SpannedExpr>);

impl Deref for SourceExpression {
    type Target = SpannedExpr;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SourceExpression {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.0)
    }
}

impl fmt::Debug for SourceExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl From<SpannedExpr> for SourceExpression {
    fn from(expression: SpannedExpr) -> Self {
        Self(Arc::new(expression))
    }
}

impl From<SourceExpression> for SpannedExpr {
    fn from(expression: SourceExpression) -> Self {
        Arc::try_unwrap(expression.0).unwrap_or_else(|shared| (*shared).clone())
    }
}

#[cfg(test)]
mod tests {
    use super::SourceExpression;
    use crate::{Expr, SourceChildren, Span, SpannedExpr};
    use std::sync::Arc;

    fn node(expr: Expr, span: Span, children: Vec<SpannedExpr>) -> SpannedExpr {
        SpannedExpr {
            expr,
            span,
            children: SourceChildren::from(children),
        }
    }

    fn span(start: usize, end: usize, source_id: u32) -> Span {
        Span {
            start,
            end,
            line: 3,
            column: 5,
            source_id,
        }
    }

    #[test]
    fn retains_root_and_child_spans_and_provenance() {
        let child = node(Expr::Symbol("child".into()), span(4, 9, 7), vec![]);
        let source = SourceExpression::from(node(
            Expr::List(vec![Expr::Symbol("root".into()), Expr::Symbol("child".into())].into()),
            span(0, 10, 7),
            vec![child],
        ));

        assert_eq!(source.span, span(0, 10, 7));
        assert_eq!(source.children[0].span, span(4, 9, 7));
        assert_eq!(
            format!("{source:?}"),
            format!("{:?}", SpannedExpr::from(source.clone()))
        );
    }

    #[test]
    fn clones_share_until_nested_mutation_then_isolate() {
        let expression = node(
            Expr::List(vec![Expr::Symbol("root".into())].into()),
            span(0, 5, 2),
            vec![node(Expr::Symbol("before".into()), span(1, 4, 2), vec![])],
        );
        let mut left = SourceExpression::from(expression);
        let right = left.clone();
        assert!(Arc::ptr_eq(&left.0, &right.0));

        left.children[0].expr = Expr::Symbol("after".into());
        assert!(!Arc::ptr_eq(&left.0, &right.0));
        assert_eq!(left.children[0].expr, Expr::Symbol("after".into()));
        assert_eq!(right.children[0].expr, Expr::Symbol("before".into()));
        assert_eq!(left.children[0].span, span(1, 4, 2));
        left.expr = Expr::Symbol("new-root".into());
        left.span.source_id = 19;
        assert!(matches!(right.expr, Expr::List(_)));
        assert_eq!(right.span.source_id, 2);
    }

    #[test]
    fn conversions_preserve_empty_spans_and_reuse_unique_storage() {
        let original = node(Expr::Symbol("empty".into()), span(8, 8, 11), vec![]);
        let source = SourceExpression::from(original.clone());
        let unique_weak = Arc::downgrade(&source.0);
        let recovered_unique = SpannedExpr::from(source);
        assert!(unique_weak.upgrade().is_none());
        assert_eq!(recovered_unique, original);

        let source = SourceExpression::from(original.clone());
        let shared = source.clone();
        assert!(Arc::ptr_eq(&source.0, &shared.0));
        let recovered_shared = SpannedExpr::from(shared.clone());
        assert_eq!(recovered_shared, original);
        assert!(Arc::ptr_eq(&source.0, &shared.0));
        assert_eq!(recovered_shared.span, span(8, 8, 11));
        assert!(recovered_shared.children.is_empty());
    }

    #[test]
    fn normalized_declaration_inventories_share_but_program_clones_isolate_edits() {
        let source = "(#enum Maybe () ((Maybe.Some #u64) Maybe.None))
          (#fn extract ((value Maybe)) #u64
            (#let-else (Maybe.Some result) value (#else (#return 0u64)))
            (#return result))";
        let original = crate::parse_program(source).unwrap();
        crate::check_types(&original).unwrap();
        let canonical = &original.declaration_expressions["extract"];
        let occurrence = &original.declaration_occurrences["extract"][0];
        assert!(Arc::ptr_eq(&canonical.0, &occurrence.0));
        assert_eq!(canonical, occurrence);

        let mut copied = original.clone();
        let copied_source = copied.declaration_expressions.get_mut("extract").unwrap();
        assert!(Arc::ptr_eq(&canonical.0, &copied_source.0));
        copied_source.expr = Expr::Symbol("changed".into());
        copied_source.span.source_id = 99;
        assert_eq!(&original.declaration_expressions["extract"], canonical);
        assert_eq!(&copied.declaration_occurrences["extract"][0], occurrence);
        assert_ne!(&copied.declaration_expressions["extract"], canonical);
        assert_eq!(canonical.span.source_id, 0);
    }
}
