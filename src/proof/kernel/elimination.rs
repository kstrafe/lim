//! Motives, branch telescopes and computation for an entire inductive group.
use super::*;

impl Kernel {
    #[expect(clippy::too_many_arguments)]
    pub(super) fn induction(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        motive: &T,
        branches: &[T],
        subject: &T,
        depth: usize,
    ) -> Result<T> {
        let (family, _) = self.family(name, levels, depth + 1)?;
        if family.group.len() != 1 {
            return Err(
                "group families require #pt-mutual-induct or #pt-nested-induct with all motives and branches"
                    .into(),
            );
        }
        self.group_induction(
            ctx,
            name,
            levels,
            parameters,
            indices,
            &[RecursionCase {
                family: name.into(),
                motive: motive.clone(),
                branches: branches.to_vec(),
            }],
            subject,
            depth + 1,
        )
    }

    #[expect(clippy::too_many_arguments)]
    pub(super) fn mutual_induction(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        cases: &[RecursionCase],
        subject: &T,
        depth: usize,
    ) -> Result<T> {
        let (family, _) = self.family(name, levels, depth + 1)?;
        if family.group.len() < 2 {
            return Err("#pt-mutual-induct requires a mutually declared family".into());
        }
        self.group_induction(
            ctx,
            name,
            levels,
            parameters,
            indices,
            cases,
            subject,
            depth + 1,
        )
    }

    #[expect(clippy::too_many_arguments)]
    fn group_induction(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        cases: &[RecursionCase],
        subject: &T,
        depth: usize,
    ) -> Result<T> {
        if self.provisional_family(name) {
            return Err("cannot eliminate a provisional inductive family".into());
        }
        let (desc, map) = self.family(name, levels, depth + 1)?;
        if cases.len() != desc.group.len()
            || !cases
                .iter()
                .zip(&desc.group)
                .all(|(case, name)| &case.family == name)
        {
            return Err(
                "induction cases must cover every group family exactly once in declaration order"
                    .into(),
            );
        }
        if parameters.len() != desc.parameters.len() || indices.len() != desc.indices.len() {
            return Err("induction parameter, index, or branch count mismatch".into());
        }
        let (decl, _) = self.specialization(name, levels, depth + 1)?;
        let ty = self.universes(&decl.ty, &map, depth + 1)?;
        let telescope = self.arguments(ctx, ty, parameters, depth + 1)?;
        self.arguments(ctx, telescope, indices, depth + 1)?;
        let subject_type = self.family_application(name, levels, parameters, indices, depth + 1)?;
        self.check(ctx, subject, &subject_type, depth + 1)?;
        // Validate *all* motives before any of them is used in an IH type.
        for case in cases {
            let (member, _) = self.family(&case.family, levels, depth + 1)?;
            if member.group != desc.group || case.branches.len() != member.constructors.len() {
                return Err("induction parameter, index, or branch count mismatch".into());
            }
            self.induction_motive(
                ctx,
                &case.family,
                levels,
                parameters,
                &case.motive,
                depth + 1,
            )?;
        }
        let motives = cases
            .iter()
            .map(|case| (case.family.clone(), case.motive.clone()))
            .collect::<Vec<_>>();
        for case in cases {
            let (member, _) = self.family(&case.family, levels, depth + 1)?;
            for (constructor, branch) in member.constructors.iter().zip(&case.branches) {
                let expected = self.group_branch_type(
                    ctx,
                    &case.family,
                    levels,
                    parameters,
                    &motives,
                    constructor,
                    depth + 1,
                )?;
                self.check(ctx, branch, &expected, depth + 1)?;
            }
        }
        let motive = motive_for(&motives, name)?;
        let result = apps(apps(motive, indices), std::slice::from_ref(subject));
        self.sort(ctx, &result, depth + 1)?;
        Ok(result)
    }

    fn induction_motive(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        motive: &T,
        depth: usize,
    ) -> Result<()> {
        let (desc, map) = self.family(name, levels, depth + 1)?;
        if parameters.len() != desc.parameters.len() {
            return Err("induction parameter count mismatch".into());
        }
        let (decl, _) = self.specialization(name, levels, depth + 1)?;
        let ty = self.universes(&decl.ty, &map, depth + 1)?;
        let mut telescope = self.arguments(ctx, ty, parameters, depth + 1)?;
        let mut mt = self.infer(ctx, motive, depth + 1)?;
        let mut motive_context = ctx.to_vec();
        let mut generic_family =
            self.family_application(name, levels, parameters, &[], depth + 1)?;
        for _ in &desc.indices {
            let expected = self.whnf(&motive_context, &telescope, depth + 1)?;
            let actual = self.whnf(&motive_context, &mt, depth + 1)?;
            let (Term::Pi(domain, rest), Term::Pi(actual_domain, actual_rest)) =
                (expected.as_ref(), actual.as_ref())
            else {
                return Err("induction motive must bind every index".into());
            };
            if !self.convertible(&motive_context, domain, actual_domain, depth + 1)? {
                return Err("induction motive has the wrong index type".into());
            }
            motive_context.push(domain.clone());
            telescope = rest.clone();
            mt = actual_rest.clone();
            generic_family = term(Term::App(
                self.shift(&generic_family, 1, 0, depth + 1)?,
                term(Term::Var(0)),
            ));
        }
        let mt = self.whnf(&motive_context, &mt, depth + 1)?;
        let Term::Pi(domain, range) = mt.as_ref() else {
            return Err("induction motive must bind its subject".into());
        };
        if !self.convertible(&motive_context, domain, &generic_family, depth + 1)? {
            return Err("induction motive has the wrong generic subject type".into());
        }
        motive_context.push(domain.clone());
        let range = self.whnf(&motive_context, range, depth + 1)?;
        let Term::Sort(target_sort) = range.as_ref() else {
            return Err("induction motive must return a fixed universe sort".into());
        };
        if !desc.large && !desc.sort.substitute(&map)?.zero_implies_zero(target_sort)? {
            return Err("large elimination from this proposition is forbidden".into());
        }
        Ok(())
    }

    #[expect(clippy::too_many_arguments)]
    pub(super) fn group_branch_type(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        motives: &[(String, T)],
        ctor: &Constructor,
        depth: usize,
    ) -> Result<T> {
        let (mut ty, recursive) = self.constructor_type(name, levels, &ctor.name, depth + 1)?;
        for parameter in parameters {
            let reduced = self.whnf(ctx, &ty, depth + 1)?;
            let Term::Pi(_, body) = reduced.as_ref() else {
                return Err("invalid constructor telescope".into());
            };
            ty = self.instantiate(body, parameter, depth + 1)?;
        }
        let mut domains = vec![];
        let mut inner = ctx.to_vec();
        let mut args: Vec<T> = vec![];
        let mut params = parameters.to_vec();
        let mut motives = motives.to_vec();
        for target in recursive {
            let reduced = self.whnf(&inner, &ty, depth + 1)?;
            let Term::Pi(domain, body) = reduced.as_ref() else {
                return Err("invalid constructor field telescope".into());
            };
            domains.push(domain.clone());
            inner.push(domain.clone());
            ty = body.clone();
            args = self.shift_many(&args, 1, depth + 1)?;
            args.push(term(Term::Var(0)));
            params = self.shift_many(&params, 1, depth + 1)?;
            motives = self.shift_motives(&motives, depth + 1)?;
            if let Some(target) = target {
                let field_type = self.shift(domain, 1, 0, depth + 1)?;
                let ih = self.recursive_hypothesis_type(
                    &inner,
                    &target,
                    levels,
                    &params,
                    &motives,
                    &field_type,
                    &term(Term::Var(0)),
                    depth + 1,
                )?;
                domains.push(ih.clone());
                inner.push(ih);
                ty = self.shift(&ty, 1, 0, depth + 1)?;
                args = self.shift_many(&args, 1, depth + 1)?;
                params = self.shift_many(&params, 1, depth + 1)?;
                motives = self.shift_motives(&motives, depth + 1)?;
            }
        }
        let result_indices = self.family_indices(&inner, name, levels, &params, &ty, depth + 1)?;
        let value = self.family_constructor(name, levels, &params, &ctor.name, args, depth + 1)?;
        Ok(pis(
            &domains,
            term(Term::App(
                apps(motive_for(&motives, name)?, &result_indices),
                value,
            )),
        ))
    }

    #[cfg(test)]
    #[expect(clippy::too_many_arguments)]
    pub(super) fn branch_type(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        motive: &T,
        ctor: &Constructor,
        depth: usize,
    ) -> Result<T> {
        self.group_branch_type(
            ctx,
            name,
            levels,
            parameters,
            &[(name.into(), motive.clone())],
            ctor,
            depth,
        )
    }

    fn shift_motives(&mut self, motives: &[(String, T)], depth: usize) -> Result<Vec<(String, T)>> {
        motives
            .iter()
            .map(|(name, value)| Ok((name.clone(), self.shift(value, 1, 0, depth + 1)?)))
            .collect()
    }

    #[expect(clippy::too_many_arguments)]
    fn recursive_hypothesis_type(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        motives: &[(String, T)],
        field_type: &T,
        field: &T,
        depth: usize,
    ) -> Result<T> {
        self.tick(depth)?;
        let shape = self.whnf(ctx, field_type, depth + 1)?;
        if let Term::Pi(domain, range) = shape.as_ref() {
            let mut inner = ctx.to_vec();
            inner.push(domain.clone());
            let parameters = self.shift_many(parameters, 1, depth + 1)?;
            let motives = self.shift_motives(motives, depth + 1)?;
            let applied = term(Term::App(
                self.shift(field, 1, 0, depth + 1)?,
                term(Term::Var(0)),
            ));
            let result = self.recursive_hypothesis_type(
                &inner,
                name,
                levels,
                &parameters,
                &motives,
                range,
                &applied,
                depth + 1,
            )?;
            return Ok(term(Term::Pi(domain.clone(), result)));
        }
        let indices = self.family_indices(ctx, name, levels, parameters, &shape, depth + 1)?;
        Ok(apps(
            apps(motive_for(motives, name)?, &indices),
            &[field.clone()],
        ))
    }

    fn shift_cases(&mut self, cases: &[RecursionCase], depth: usize) -> Result<Vec<RecursionCase>> {
        cases
            .iter()
            .map(|case| {
                Ok(RecursionCase {
                    family: case.family.clone(),
                    motive: self.shift(&case.motive, 1, 0, depth + 1)?,
                    branches: self.shift_many(&case.branches, 1, depth + 1)?,
                })
            })
            .collect()
    }

    #[expect(clippy::too_many_arguments)]
    fn recursive_hypothesis_value(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        cases: &[RecursionCase],
        field_type: &T,
        field: &T,
        depth: usize,
    ) -> Result<T> {
        self.tick(depth)?;
        let shape = self.whnf(ctx, field_type, depth + 1)?;
        if let Term::Pi(domain, range) = shape.as_ref() {
            let mut inner = ctx.to_vec();
            inner.push(domain.clone());
            let parameters = self.shift_many(parameters, 1, depth + 1)?;
            let cases = self.shift_cases(cases, depth + 1)?;
            let applied = term(Term::App(
                self.shift(field, 1, 0, depth + 1)?,
                term(Term::Var(0)),
            ));
            let result = self.recursive_hypothesis_value(
                &inner,
                name,
                levels,
                &parameters,
                &cases,
                range,
                &applied,
                depth + 1,
            )?;
            return Ok(term(Term::Lam(domain.clone(), result)));
        }
        let indices = self.family_indices(ctx, name, levels, parameters, &shape, depth + 1)?;
        Ok(recursor(
            name,
            levels,
            parameters,
            &indices,
            cases,
            field.clone(),
        )?)
    }

    #[expect(clippy::too_many_arguments)]
    pub(super) fn reduce_induction(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        cases: &[RecursionCase],
        subject: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        let subject = self.whnf(ctx, subject, depth + 1)?;
        let subject = self.natural_constructor(&subject, depth + 1)?;
        let (desc, map) = self.family(name, levels, depth + 1)?;
        let case = cases
            .iter()
            .find(|case| case.family == name)
            .ok_or("missing induction family case")?;
        let Term::Ctor {
            family: actual,
            constructor,
            fields,
            ..
        } = subject.as_ref()
        else {
            // The unit/K/record eta rules apply only to a singleton group.
            if desc.group.len() == 1 && desc.constructors.len() == 1 {
                let ctor = &desc.constructors[0];
                if ctor.fields.is_empty() {
                    let mut reduces = desc.indices.is_empty();
                    if !reduces && desc.sort.substitute(&map)?.zero() {
                        let (ty, _) = self.constructor_type(name, levels, &ctor.name, depth + 1)?;
                        let ty = self.arguments(ctx, ty, parameters, depth + 1)?;
                        let results =
                            self.family_indices(ctx, name, levels, parameters, &ty, depth + 1)?;
                        reduces = self.same_many(ctx, indices, &results, depth + 1)?;
                    }
                    if reduces {
                        return Ok(Some(
                            case.branches
                                .first()
                                .cloned()
                                .ok_or("missing induction branch")?,
                        ));
                    }
                }
                if desc.indices.is_empty()
                    && !ctor.recursive.iter().any(Option::is_some)
                    && (desc.large
                        || desc
                            .sort
                            .substitute(&map)?
                            .zero_implies_zero(&Level::number(1)?)?)
                {
                    let mut result = case
                        .branches
                        .first()
                        .cloned()
                        .ok_or("missing induction branch")?;
                    for index in 0..ctor.fields.len() {
                        result = term(Term::App(
                            result,
                            term(Term::Project {
                                family: name.into(),
                                index,
                                subject: subject.clone(),
                            }),
                        ));
                    }
                    return Ok(Some(result));
                }
            }
            return Ok(None);
        };
        let original = self.family_application(name, levels, parameters, &[], depth + 1)?;
        let (original, _) = nested::application(&original);
        if !matches!(original.as_ref(),Term::Global(expected,_) if expected==actual) {
            return Err("induction subject belongs to a different family".into());
        }
        let index = desc
            .constructors
            .iter()
            .position(|c| &c.name == constructor)
            .ok_or("invalid induction constructor")?;
        let mut result = case
            .branches
            .get(index)
            .cloned()
            .ok_or("missing induction branch")?;
        let ctor = &desc.constructors[index];
        if fields.len() != ctor.fields.len() {
            return Err("invalid induction constructor field count".into());
        }
        let (mut telescope, _) = self.constructor_type(name, levels, constructor, depth + 1)?;
        for parameter in parameters {
            let reduced = self.whnf(ctx, &telescope, depth + 1)?;
            let Term::Pi(_, body) = reduced.as_ref() else {
                return Err("invalid constructor parameter telescope".into());
            };
            telescope = self.instantiate(body, parameter, depth + 1)?;
        }
        for (field, target) in fields.iter().zip(&ctor.recursive) {
            let reduced = self.whnf(ctx, &telescope, depth + 1)?;
            let Term::Pi(domain, body) = reduced.as_ref() else {
                return Err("invalid constructor field telescope".into());
            };
            let ih = if let Some(target) = target {
                Some(self.recursive_hypothesis_value(
                    ctx,
                    target,
                    levels,
                    parameters,
                    cases,
                    domain,
                    field,
                    depth + 1,
                )?)
            } else {
                None
            };
            telescope = self.instantiate(body, field, depth + 1)?;
            result = term(Term::App(result, field.clone()));
            if let Some(ih) = ih {
                result = term(Term::App(result, ih));
            }
        }
        Ok(Some(result))
    }
}

fn motive_for(motives: &[(String, T)], name: &str) -> Result<T> {
    motives
        .iter()
        .find(|(family, _)| family == name)
        .map(|(_, motive)| motive.clone())
        .ok_or_else(|| "missing induction family motive".into())
}
fn recursor(
    name: &str,
    levels: &[Level],
    parameters: &[T],
    indices: &[T],
    cases: &[RecursionCase],
    subject: T,
) -> Result<T> {
    if cases.len() == 1 {
        let case = &cases[0];
        if case.family != name {
            return Err("missing induction family case".into());
        }
        Ok(term(Term::Induct {
            family: name.into(),
            levels: levels.to_vec(),
            parameters: parameters.to_vec(),
            indices: indices.to_vec(),
            motive: case.motive.clone(),
            branches: case.branches.clone(),
            subject,
        }))
    } else {
        Ok(term(Term::MutualInduct {
            family: name.into(),
            levels: levels.to_vec(),
            parameters: parameters.to_vec(),
            indices: indices.to_vec(),
            cases: cases.to_vec(),
            subject,
        }))
    }
}
