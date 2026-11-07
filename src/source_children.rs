use std::ops::{Deref, DerefMut};
use std::slice;
use std::sync::Arc;

use crate::SpannedExpr;

/// Copy-on-write storage for source expression children.
///
/// This shares only the source tree. It carries no proof or judgment data.
#[derive(Clone, Default)]
pub struct SourceChildren(Option<Arc<Vec<SpannedExpr>>>);

impl PartialEq for SourceChildren {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(left), Some(right)) if Arc::ptr_eq(left, right) => true,
            _ => self.deref() == other.deref(),
        }
    }
}

impl Eq for SourceChildren {}

impl SourceChildren {
    /// Returns mutable children, detaching shared storage when necessary.
    /// An empty collection stays allocation-free.
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, SpannedExpr> {
        match self.0.as_mut() {
            Some(children) if !children.is_empty() => Arc::make_mut(children).iter_mut(),
            _ => slice::IterMut::default(),
        }
    }
}

impl std::fmt::Debug for SourceChildren {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}

impl Deref for SourceChildren {
    type Target = Vec<SpannedExpr>;

    fn deref(&self) -> &Self::Target {
        static EMPTY: Vec<SpannedExpr> = Vec::new();
        self.0.as_deref().unwrap_or(&EMPTY)
    }
}

impl DerefMut for SourceChildren {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(self.0.get_or_insert_with(|| Arc::new(Vec::new())))
    }
}

impl From<Vec<SpannedExpr>> for SourceChildren {
    fn from(children: Vec<SpannedExpr>) -> Self {
        if children.is_empty() {
            Self::default()
        } else {
            Self(Some(Arc::new(children)))
        }
    }
}

impl From<SourceChildren> for Vec<SpannedExpr> {
    fn from(children: SourceChildren) -> Self {
        match children.0 {
            None => Vec::new(),
            Some(children) => Arc::try_unwrap(children).unwrap_or_else(|shared| (*shared).clone()),
        }
    }
}

impl IntoIterator for SourceChildren {
    type Item = SpannedExpr;
    type IntoIter = std::vec::IntoIter<SpannedExpr>;

    fn into_iter(self) -> Self::IntoIter {
        Vec::from(self).into_iter()
    }
}

impl<'a> IntoIterator for &'a SourceChildren {
    type Item = &'a SpannedExpr;
    type IntoIter = slice::Iter<'a, SpannedExpr>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut SourceChildren {
    type Item = &'a mut SpannedExpr;
    type IntoIter = slice::IterMut<'a, SpannedExpr>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl FromIterator<SpannedExpr> for SourceChildren {
    fn from_iter<T: IntoIterator<Item = SpannedExpr>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;
    use crate::{Expr, Span};

    fn expr(value: i128) -> SpannedExpr {
        SpannedExpr {
            expr: Expr::Integer(value),
            span: Span::new(value as usize, value as usize + 1, 1, 1),
            children: Vec::new().into(),
        }
    }

    #[test]
    fn clone_shares_then_mutations_detach() {
        let original = SourceChildren::from(vec![expr(1), expr(2)]);
        let mut copied = original.clone();
        assert!(Arc::ptr_eq(
            original.0.as_ref().unwrap(),
            copied.0.as_ref().unwrap()
        ));

        copied[0].expr = Expr::Integer(3);
        assert_eq!(original[0].expr, Expr::Integer(1));
        assert_eq!(copied[0].expr, Expr::Integer(3));

        let mut through_iter = original.clone();
        through_iter.iter_mut().next().unwrap().expr = Expr::Integer(4);
        assert_eq!(original[0].expr, Expr::Integer(1));

        let mut through_get_mut = original.clone();
        through_get_mut.get_mut(1).unwrap().expr = Expr::Integer(5);
        assert_eq!(original[1].expr, Expr::Integer(2));

        let mut through_extend = original.clone();
        through_extend.extend([expr(6)]);
        assert_eq!(original.len(), 2);
        assert_eq!(through_extend.len(), 3);
    }

    #[test]
    fn empty_mut_iteration_does_not_allocate_or_materialize_storage() {
        let mut children = SourceChildren::default();
        assert_eq!(children.iter_mut().count(), 0);
        assert!(children.0.is_none());
        assert_eq!((&mut children).into_iter().count(), 0);
        assert!(children.0.is_none());

        let mut allocated_empty = SourceChildren::from(vec![expr(0)]);
        allocated_empty.clear();
        let allocation = allocated_empty.0.as_ref().unwrap().clone();
        let strong_count = Arc::strong_count(&allocation);
        assert_eq!(allocated_empty.iter_mut().count(), 0);
        assert_eq!(Arc::strong_count(&allocation), strong_count);
        assert!(Arc::ptr_eq(
            allocated_empty.0.as_ref().unwrap(),
            &allocation
        ));
        assert_eq!(SourceChildren::default(), allocated_empty);
    }

    #[test]
    fn conversions_debug_equality_and_iteration_match_vec() {
        let values = vec![expr(7), expr(8)];
        let children = SourceChildren::from(values.clone());
        assert_eq!(format!("{children:?}"), format!("{values:?}"));
        assert_eq!(children, SourceChildren::from(values.clone()));
        assert_eq!(children.iter().count(), 2);
        assert_eq!(children.clone().into_iter().collect::<Vec<_>>(), values);
        assert_eq!(Vec::from(children.clone()), values);

        let shared = children.clone();
        assert_eq!(Vec::from(children), Vec::from(shared));
        assert!(SourceChildren::from(Vec::new()).0.is_none());
        assert!(Vec::from(SourceChildren::default()).is_empty());
        let collected: SourceChildren = [expr(9)].into_iter().collect();
        assert_eq!(collected.len(), 1);
    }

    #[test]
    fn cloning_expression_preserves_value_semantics() {
        let expression = SpannedExpr {
            expr: Expr::List(vec![Expr::Integer(10)].into()),
            span: Span::new(0, 2, 1, 1),
            children: vec![expr(10)].into(),
        };
        let mut copied = expression.clone();
        assert!(Arc::ptr_eq(
            expression.children.0.as_ref().unwrap(),
            copied.children.0.as_ref().unwrap()
        ));

        copied.children[0].span.end = 99;
        assert_eq!(expression.children[0].span.end, 11);
        assert_eq!(copied.children[0].span.end, 99);
    }
}
