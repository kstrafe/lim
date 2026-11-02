//! Declaration initializers retain source expression IDs where possible.
//! This table stores syntax roots only; it contains no checked judgments.
use super::{expressions::Expressions, levels::Levels, names::Names, Result, T};

pub(super) enum Initializer {
    Source(usize),
    Native(T),
}

pub(super) struct Initializers {
    enabled: bool,
    entries: Vec<Option<Initializer>>,
}

impl Initializers {
    pub(super) fn new(enabled: bool) -> Self {
        Self {
            enabled,
            entries: Vec::new(),
        }
    }

    pub(super) fn push(
        &mut self,
        report_id: usize,
        initializer: Option<Initializer>,
    ) -> Result<()> {
        if !self.enabled {
            return if initializer.is_none() {
                Ok(())
            } else {
                Err("declaration initializers are disabled".into())
            };
        }
        if report_id != self.entries.len() {
            return Err("declaration initializer index is not contiguous".into());
        }
        if self.entries.len() >= super::MAX_DECLARATIONS {
            return Err("declaration initializer limit exceeded".into());
        }
        self.entries.push(initializer);
        Ok(())
    }

    pub(super) fn get(
        &self,
        id: usize,
        expressions: &Expressions,
        names: &Names,
        levels: &Levels,
    ) -> Result<Option<T>> {
        if !self.enabled {
            return Ok(None);
        }
        match self
            .entries
            .get(id)
            .ok_or_else(|| "declaration initializer index is out of range".to_string())?
        {
            None => Ok(None),
            Some(Initializer::Source(expression_id)) => {
                expressions.get(*expression_id, names, levels).map(Some)
            }
            Some(Initializer::Native(value)) => Ok(Some(value.clone())),
        }
    }

    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::{term, Kernel, Level, Term};
    use super::*;

    fn tables() -> (Expressions, Names, Levels) {
        (
            Expressions::with_limit(false, 0),
            Names::new(),
            Levels::new(),
        )
    }

    fn expression(
        expressions: &mut Expressions,
        expression: super::super::expressions::Expression,
        depth: usize,
        names: &Names,
        levels: &Levels,
    ) {
        expressions
            .push(expression, depth, 0, names, levels)
            .unwrap();
    }

    #[test]
    fn source_initializers_reconstruct_paged_expressions() {
        use super::super::expressions::Expression;
        let (mut expressions, names, levels) = tables();
        expression(&mut expressions, Expression::Sort(0), 1, &names, &levels);
        expression(&mut expressions, Expression::Var(0), 1, &names, &levels);
        expression(&mut expressions, Expression::Lam(0, 1), 2, &names, &levels);
        let mut initializers = Initializers::new(true);
        for id in 0..3 {
            initializers
                .push(id, Some(Initializer::Source(id)))
                .unwrap();
        }
        for id in 0..3 {
            let first = initializers
                .get(id, &expressions, &names, &levels)
                .unwrap()
                .unwrap();
            let weak = std::sync::Arc::downgrade(&first);
            drop(first);
            assert!(weak.upgrade().is_none());
            let second = initializers
                .get(id, &expressions, &names, &levels)
                .unwrap()
                .unwrap();
            let expected = match id {
                0 => term(Term::Sort(Level::number(0).unwrap())),
                1 => term(Term::Var(0)),
                2 => term(Term::Lam(
                    term(Term::Sort(Level::number(0).unwrap())),
                    term(Term::Var(0)),
                )),
                _ => unreachable!(),
            };
            assert!(Kernel::new().same_syntax(&second, &expected).unwrap());
        }
    }

    #[test]
    fn native_and_source_roots_are_distinct_storage_modes() {
        use super::super::expressions::Expression;
        let (mut expressions, names, levels) = tables();
        expression(&mut expressions, Expression::Var(0), 1, &names, &levels);
        let native = term(Term::Sort(Level::number(0).unwrap()));
        let mut initializers = Initializers::new(true);
        initializers
            .push(0, Some(Initializer::Native(native.clone())))
            .unwrap();
        initializers.push(1, Some(Initializer::Source(0))).unwrap();
        let got_native = initializers
            .get(0, &expressions, &names, &levels)
            .unwrap()
            .unwrap();
        let got_source = initializers
            .get(1, &expressions, &names, &levels)
            .unwrap()
            .unwrap();
        let mut kernel = Kernel::new();
        assert!(kernel.same_syntax(&got_native, &native).unwrap());
        assert!(!kernel.same_syntax(&got_native, &got_source).unwrap());
    }

    #[test]
    fn empty_slots_disabled_storage_and_indices() {
        let (expressions, names, levels) = tables();
        let mut empty = Initializers::new(true);
        assert!(empty.get(0, &expressions, &names, &levels).is_err());
        assert!(empty.push(1, None).is_err());
        empty.push(0, None).unwrap();
        assert!(empty
            .get(0, &expressions, &names, &levels)
            .unwrap()
            .is_none());

        let mut invalid_source = Initializers::new(true);
        invalid_source
            .push(0, Some(Initializer::Source(usize::MAX)))
            .unwrap();
        assert!(invalid_source
            .get(0, &expressions, &names, &levels)
            .is_err());

        let mut disabled = Initializers::new(false);
        disabled.push(100, None).unwrap();
        assert_eq!(disabled.len(), 0);
        assert!(disabled
            .get(0, &expressions, &names, &levels)
            .unwrap()
            .is_none());
        assert!(disabled
            .push(0, Some(Initializer::Native(term(Term::Var(0)))))
            .is_err());
    }

    #[test]
    fn declaration_capacity_is_checked() {
        let mut initializers = Initializers::new(true);
        for id in 0..super::super::MAX_DECLARATIONS {
            initializers.push(id, None).unwrap();
        }
        assert!(initializers
            .push(super::super::MAX_DECLARATIONS, None)
            .is_err());
    }
}
