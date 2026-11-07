use std::ops::{Deref, DerefMut};
use std::slice;
use std::sync::Arc;

use crate::Expr;

/// Copy-on-write storage for expression list values.
#[derive(Clone, Default)]
pub struct ExprList(Option<Arc<Vec<Expr>>>);

impl PartialEq for ExprList {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(left), Some(right)) if Arc::ptr_eq(left, right) => true,
            _ => self.deref() == other.deref(),
        }
    }
}

impl Eq for ExprList {}

impl ExprList {
    /// Returns mutable values, detaching shared storage when necessary.
    /// An empty collection stays allocation-free.
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, Expr> {
        match self.0.as_mut() {
            Some(values) if !values.is_empty() => Arc::make_mut(values).iter_mut(),
            _ => slice::IterMut::default(),
        }
    }
}

impl std::fmt::Debug for ExprList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}

impl Deref for ExprList {
    type Target = Vec<Expr>;

    fn deref(&self) -> &Self::Target {
        static EMPTY: Vec<Expr> = Vec::new();
        self.0.as_deref().unwrap_or(&EMPTY)
    }
}

impl DerefMut for ExprList {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(self.0.get_or_insert_with(|| Arc::new(Vec::new())))
    }
}

impl From<Vec<Expr>> for ExprList {
    fn from(values: Vec<Expr>) -> Self {
        if values.is_empty() {
            Self::default()
        } else {
            Self(Some(Arc::new(values)))
        }
    }
}

impl From<ExprList> for Vec<Expr> {
    fn from(values: ExprList) -> Self {
        match values.0 {
            None => Vec::new(),
            Some(values) => Arc::try_unwrap(values).unwrap_or_else(|shared| (*shared).clone()),
        }
    }
}

impl IntoIterator for ExprList {
    type Item = Expr;
    type IntoIter = std::vec::IntoIter<Expr>;

    fn into_iter(self) -> Self::IntoIter {
        Vec::from(self).into_iter()
    }
}

impl<'a> IntoIterator for &'a ExprList {
    type Item = &'a Expr;
    type IntoIter = slice::Iter<'a, Expr>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut ExprList {
    type Item = &'a mut Expr;
    type IntoIter = slice::IterMut<'a, Expr>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl FromIterator<Expr> for ExprList {
    fn from_iter<T: IntoIterator<Item = Expr>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    #[test]
    fn clone_shares_and_mutation_detaches() {
        let original = ExprList::from(vec![Expr::Integer(1), Expr::Integer(2)]);
        let mut copied = original.clone();
        assert!(Arc::ptr_eq(
            original.0.as_ref().unwrap(),
            copied.0.as_ref().unwrap()
        ));

        copied[0] = Expr::Integer(3);
        assert_eq!(original[0], Expr::Integer(1));
        assert_eq!(copied[0], Expr::Integer(3));
    }

    #[test]
    fn empty_mut_iteration_does_not_allocate_or_detach() {
        let mut empty = ExprList::default();
        assert_eq!(empty.iter_mut().count(), 0);
        assert!(empty.0.is_none());

        let mut allocated = ExprList::from(vec![Expr::Integer(0)]);
        allocated.clear();
        let storage = allocated.0.as_ref().unwrap().clone();
        assert_eq!((&mut allocated).into_iter().count(), 0);
        assert!(Arc::ptr_eq(allocated.0.as_ref().unwrap(), &storage));
        assert_eq!(ExprList::default(), allocated);
    }

    #[test]
    fn conversions_debug_equality_and_iteration_match_vec() {
        let values = vec![Expr::Integer(7), Expr::Integer(8)];
        let list = ExprList::from(values.clone());
        assert_eq!(format!("{list:?}"), format!("{values:?}"));
        assert_eq!(list, ExprList::from(values.clone()));
        assert_eq!(list.iter().count(), 2);
        assert_eq!(list.clone().into_iter().collect::<Vec<_>>(), values);
        assert_eq!(Vec::from(list), values);
        assert!(ExprList::from(Vec::new()).0.is_none());
        let collected: ExprList = [Expr::Integer(9)].into_iter().collect();
        assert_eq!(collected.len(), 1);
    }
}
