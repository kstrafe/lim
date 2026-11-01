//! Quotient computation checks representatives and well-definedness explicitly.
//! These rules do not assert equality of related representatives (Quot.sound).
use super::*;

impl Kernel {
    fn quotient_inputs(
        &mut self,
        ctx: &[T],
        level: &Level,
        ty: &T,
        relation: &T,
        depth: usize,
    ) -> Result<()> {
        self.check(ctx, ty, &term(Term::Sort(level.clone())), depth + 1)?;
        let relation_type = term(Term::Pi(
            ty.clone(),
            term(Term::Pi(
                self.shift(ty, 1, 0, depth + 1)?,
                term(Term::Sort(Level::number(0)?)),
            )),
        ));
        self.check(ctx, relation, &relation_type, depth + 1)
    }
    pub(super) fn quotient_type(
        &mut self,
        ctx: &[T],
        level: &Level,
        ty: &T,
        relation: &T,
        depth: usize,
    ) -> Result<T> {
        self.quotient_inputs(ctx, level, ty, relation, depth + 1)?;
        Ok(term(Term::Sort(level.clone())))
    }
    pub(super) fn quotient_make(
        &mut self,
        ctx: &[T],
        level: &Level,
        ty: &T,
        relation: &T,
        value: &T,
        depth: usize,
    ) -> Result<T> {
        self.quotient_inputs(ctx, level, ty, relation, depth + 1)?;
        self.check(ctx, value, ty, depth + 1)?;
        Ok(term(Term::QuotType(
            level.clone(),
            ty.clone(),
            relation.clone(),
        )))
    }
    #[expect(clippy::too_many_arguments)]
    pub(super) fn quotient_lift(
        &mut self,
        ctx: &[T],
        source_level: &Level,
        target_level: &Level,
        ty: &T,
        relation: &T,
        target: &T,
        function: &T,
        respect: &T,
        subject: &T,
        depth: usize,
    ) -> Result<T> {
        self.quotient_inputs(ctx, source_level, ty, relation, depth + 1)?;
        self.check(
            ctx,
            target,
            &term(Term::Sort(target_level.clone())),
            depth + 1,
        )?;
        let function_type = term(Term::Pi(ty.clone(), self.shift(target, 1, 0, depth + 1)?));
        self.check(ctx, function, &function_type, depth + 1)?;
        let second_domain = self.shift(ty, 1, 0, depth + 1)?;
        let premise = apps(
            self.shift(relation, 2, 0, depth + 1)?,
            &[term(Term::Var(1)), term(Term::Var(0))],
        );
        let shifted_function = self.shift(function, 3, 0, depth + 1)?;
        let conclusion = term(Term::Eq(
            self.shift(target, 3, 0, depth + 1)?,
            apps(shifted_function.clone(), &[term(Term::Var(2))]),
            apps(shifted_function, &[term(Term::Var(1))]),
        ));
        let expected = term(Term::Pi(
            ty.clone(),
            term(Term::Pi(second_domain, term(Term::Pi(premise, conclusion)))),
        ));
        self.check(ctx, respect, &expected, depth + 1)?;
        self.check(
            ctx,
            subject,
            &term(Term::QuotType(
                source_level.clone(),
                ty.clone(),
                relation.clone(),
            )),
            depth + 1,
        )?;
        Ok(target.clone())
    }
    #[expect(clippy::too_many_arguments)]
    pub(super) fn quotient_induct(
        &mut self,
        ctx: &[T],
        level: &Level,
        ty: &T,
        relation: &T,
        motive: &T,
        branch: &T,
        subject: &T,
        depth: usize,
    ) -> Result<T> {
        self.quotient_inputs(ctx, level, ty, relation, depth + 1)?;
        let quotient = term(Term::QuotType(level.clone(), ty.clone(), relation.clone()));
        self.check(
            ctx,
            motive,
            &term(Term::Pi(
                quotient.clone(),
                term(Term::Sort(Level::number(0)?)),
            )),
            depth + 1,
        )?;
        let made = term(Term::QuotMake(
            level.clone(),
            self.shift(ty, 1, 0, depth + 1)?,
            self.shift(relation, 1, 0, depth + 1)?,
            term(Term::Var(0)),
        ));
        let expected = term(Term::Pi(
            ty.clone(),
            apps(self.shift(motive, 1, 0, depth + 1)?, &[made]),
        ));
        self.check(ctx, branch, &expected, depth + 1)?;
        self.check(ctx, subject, &quotient, depth + 1)?;
        Ok(apps(motive.clone(), std::slice::from_ref(subject)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn nat() -> T {
        term(Term::Global("#pt-nat".into(), vec![]))
    }
    fn variable(index: usize) -> T {
        term(Term::Var(index))
    }
    fn lambda(ty: T, body: T) -> T {
        term(Term::Lam(ty, body))
    }
    fn zero() -> T {
        term(Term::Ctor {
            family: "#pt-nat".into(),
            levels: vec![],
            parameters: vec![],
            constructor: "zero".into(),
            fields: vec![],
        })
    }
    fn level() -> Level {
        Level::number(1).unwrap()
    }
    fn relation() -> T {
        lambda(
            nat(),
            lambda(nat(), term(Term::Eq(nat(), variable(1), variable(0)))),
        )
    }
    #[test]
    fn propositional_induction_reduces_on_a_constructor() {
        let mut kernel = Kernel::new();
        let quotient = term(Term::QuotType(level(), nat(), relation()));
        let proposition = term(Term::Eq(nat(), zero(), zero()));
        let proof = term(Term::Refl(nat(), zero()));
        let value = term(Term::QuotInduct {
            level: level(),
            ty: nat(),
            relation: relation(),
            motive: lambda(quotient, proposition.clone()),
            branch: lambda(nat(), proof.clone()),
            subject: term(Term::QuotMake(level(), nat(), relation(), zero())),
        });
        kernel.check(&[], &value, &proposition, 0).unwrap();
        kernel.reset_budget();
        let reduced = kernel.whnf(&[], &value, 0).unwrap();
        assert!(matches!(reduced.as_ref(), Term::Refl(..)));
        assert!(kernel.same_syntax(&reduced, &proof).unwrap());
    }
    #[test]
    fn a_neutral_lift_keeps_its_subject_and_respect_proof() {
        let mut kernel = Kernel::new();
        let quotient = term(Term::QuotType(level(), nat(), relation()));
        let respect = lambda(
            nat(),
            lambda(
                nat(),
                lambda(term(Term::Eq(nat(), variable(1), variable(0))), variable(0)),
            ),
        );
        let value = term(Term::QuotLift {
            source_level: level(),
            target_level: level(),
            ty: nat(),
            relation: relation(),
            target: nat(),
            function: lambda(nat(), variable(0)),
            respect,
            subject: variable(0),
        });
        kernel
            .check(&[quotient.clone()], &value, &nat(), 0)
            .unwrap();
        kernel.reset_budget();
        let reduced = kernel.whnf(&[quotient], &value, 0).unwrap();
        assert!(
            matches!(reduced.as_ref(),Term::QuotLift{subject,..} if matches!(subject.as_ref(),Term::Var(0)))
        );
    }
}
