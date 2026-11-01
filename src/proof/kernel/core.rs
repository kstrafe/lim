//! Explicit dependent type checking, independent of parsing and proof search.
//! There is no native execution or cache bypass. The external-evidence rule
//! installs opaque program atoms supplied by the validated certificate adapter.
use super::level::same_levels;
pub(super) use super::level::Level;
#[cfg(test)]
use super::level::LEVEL;
use std::collections::HashMap;
use std::sync::Arc;

pub(super) type Result<T> = std::result::Result<T, String>;
pub(super) type T = Arc<Term>;
pub(super) fn term(t: Term) -> T {
    Arc::new(t)
}
const WORK: usize = 200_000;
const DEPTH: usize = 96;
#[derive(Clone, Debug)]
pub(super) enum Term {
    Sort(Level),
    Var(usize),
    Global(String, Vec<Level>),
    Pi(T, T),
    Lam(T, T),
    App(T, T),
    Sigma(T, T),
    Pair(T, T, T),
    First(T),
    Second(T),
    Eq(T, T, T),
    Refl(T, T),
    EqElim {
        ty: T,
        left: T,
        motive: T,
        base: T,
        right: T,
        proof: T,
    },
    Ctor {
        family: String,
        levels: Vec<Level>,
        parameters: Vec<T>,
        constructor: String,
        fields: Vec<T>,
    },
    Induct {
        family: String,
        levels: Vec<Level>,
        parameters: Vec<T>,
        motive: T,
        branches: Vec<T>,
        subject: T,
    },
    SelfType,
}
#[derive(Clone)]
pub(super) struct Constructor {
    pub name: String,
    pub fields: Vec<T>,
    pub recursive: Vec<bool>,
}
#[derive(Clone)]
pub(super) struct Family {
    pub parameters: Vec<T>,
    pub sort: Level,
    pub constructors: Vec<Constructor>,
    pub large: bool,
}
#[derive(Clone)]
pub(super) struct Declaration {
    pub universes: Vec<String>,
    pub ty: T,
    pub value: Option<T>,
    pub family: Option<Family>,
}
pub(super) struct Kernel {
    declarations: HashMap<String, Declaration>,
    work: usize,
}
impl Kernel {
    pub fn new() -> Self {
        let mut result = Self {
            declarations: HashMap::new(),
            work: 0,
        };
        let nat = term(Term::Global("#pt-nat".into(), vec![]));
        let family = Family {
            parameters: vec![],
            sort: Level::number(1).unwrap(),
            constructors: vec![
                Constructor {
                    name: "zero".into(),
                    fields: vec![],
                    recursive: vec![],
                },
                Constructor {
                    name: "succ".into(),
                    fields: vec![nat],
                    recursive: vec![true],
                },
            ],
            large: true,
        };
        result.declarations.insert(
            "#pt-nat".into(),
            Declaration {
                universes: vec![],
                ty: term(Term::Sort(family.sort.clone())),
                value: None,
                family: Some(family),
            },
        );
        result.declarations.insert(
            "#pt-false".into(),
            Declaration {
                universes: vec![],
                ty: term(Term::Sort(Level::number(0).unwrap())),
                value: None,
                family: Some(Family {
                    parameters: vec![],
                    sort: Level::number(0).unwrap(),
                    constructors: vec![],
                    large: true,
                }),
            },
        );
        result
    }
    pub fn contains(&self, name: &str) -> bool {
        self.declarations.contains_key(name)
    }
    fn scope(&mut self, universes: &[String], terms: &[T]) -> Result<()> {
        let map = universes
            .iter()
            .map(|u| (u.clone(), Level::variable(u.clone())))
            .collect::<HashMap<_, _>>();
        if map.len() != universes.len() {
            return Err("duplicate universe parameter".into());
        }
        for value in terms {
            self.universes(value, &map, 0)?;
        }
        Ok(())
    }
    pub fn reset_budget(&mut self) {
        self.work = 0;
    }
    fn tick(&mut self, depth: usize) -> Result<()> {
        self.work += 1;
        if depth > DEPTH || self.work > WORK {
            return Err("kernel resource limit exceeded; no theorem was established".into());
        }
        Ok(())
    }
    /// The adapter may install only propositions certified by the program
    /// checker. These are opaque atoms; no generic mathematical rule uses this.
    pub fn certified_program_fact(&mut self, name: &str) {
        let fact = format!("$program:{name}");
        self.declarations.insert(
            fact.clone(),
            Declaration {
                universes: vec![],
                ty: term(Term::Sort(Level::number(0).unwrap())),
                value: None,
                family: None,
            },
        );
        self.declarations.insert(
            format!("$certificate:{name}"),
            Declaration {
                universes: vec![],
                ty: term(Term::Global(fact, vec![])),
                value: None,
                family: None,
            },
        );
    }
    pub fn definition(
        &mut self,
        name: &str,
        universes: Vec<String>,
        ty: T,
        value: T,
        theorem: bool,
    ) -> Result<()> {
        if self.declarations.contains_key(name) {
            return Err("duplicate kernel declaration".into());
        }
        self.scope(&universes, &[ty.clone(), value.clone()])?;
        let sort = self.sort(&[], &ty, 0)?;
        if theorem && !sort.zero() {
            return Err("#proof-theorem must state a proposition in #pt-prop".into());
        }
        self.check(&[], &value, &ty, 0)?;
        self.declarations.insert(
            name.into(),
            Declaration {
                universes,
                ty,
                value: (!theorem).then_some(value),
                family: None,
            },
        );
        Ok(())
    }
    pub fn inductive(
        &mut self,
        name: &str,
        universes: Vec<String>,
        parameters: Vec<T>,
        sort: Level,
        constructors: Vec<(String, Vec<T>)>,
    ) -> Result<()> {
        if self.declarations.contains_key(name) {
            return Err("duplicate kernel declaration".into());
        }
        let mut scoped = parameters.clone();
        scoped.push(term(Term::Sort(sort.clone())));
        for (_, fields) in &constructors {
            scoped.extend(fields.iter().cloned());
        }
        self.scope(&universes, &scoped)?;
        let mut context = vec![];
        for parameter in &parameters {
            self.sort(&context, parameter, 0)?;
            context.push(parameter.clone());
        }
        let family_type = pis(&parameters, term(Term::Sort(sort.clone())));
        let mut family = Family {
            parameters: parameters.clone(),
            sort: sort.clone(),
            constructors: vec![],
            large: constructors.len() <= 1,
        };
        self.declarations.insert(
            name.into(),
            Declaration {
                universes: universes.clone(),
                ty: family_type.clone(),
                value: None,
                family: Some(family.clone()),
            },
        );
        let levels = universes
            .iter()
            .map(|u| Level::variable(u.clone()))
            .collect::<Vec<_>>();
        let outcome = (|| {
            let mut labels = std::collections::HashSet::new();
            for (constructor, fields) in constructors {
                if !labels.insert(constructor.clone()) {
                    return Err("duplicate inductive constructor".into());
                }
                let mut ctx = context.clone();
                let mut checked = vec![];
                let mut recursive = vec![];
                for field in fields {
                    let direct = matches!(field.as_ref(), Term::SelfType);
                    let field = if direct {
                        let params = (0..parameters.len())
                            .map(|i| term(Term::Var(checked.len() + parameters.len() - 1 - i)))
                            .collect::<Vec<_>>();
                        apps(term(Term::Global(name.into(), levels.clone())), &params)
                    } else {
                        if contains_recursive(&field, name) {
                            return Err("inductive recursion must be a direct #pt-self field (strict positivity)".into());
                        }
                        field
                    };
                    let field_sort = self.sort(&ctx, &field, 0)?;
                    if !field_sort.imax(&sort)?.at_most(&sort)? {
                        return Err("inductive field exceeds the datatype's universe".into());
                    }
                    family.large &= sort.zero_implies_zero(&field_sort)?;
                    ctx.push(field.clone());
                    checked.push(field);
                    recursive.push(direct);
                }
                family.constructors.push(Constructor {
                    name: constructor,
                    fields: checked,
                    recursive,
                });
            }
            self.declarations.insert(
                name.into(),
                Declaration {
                    universes,
                    ty: family_type,
                    value: None,
                    family: Some(family),
                },
            );
            Ok(())
        })();
        if outcome.is_err() {
            self.declarations.remove(name);
        }
        outcome
    }
    fn specialization(
        &mut self,
        name: &str,
        levels: &[Level],
        depth: usize,
    ) -> Result<(Declaration, HashMap<String, Level>)> {
        self.tick(depth)?;
        let declaration = self
            .declarations
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown or unchecked kernel declaration '{name}'"))?;
        if declaration.universes.len() != levels.len() {
            return Err(format!(
                "'{name}' requires {} explicit universe argument(s)",
                declaration.universes.len()
            ));
        }
        let values = declaration
            .universes
            .iter()
            .cloned()
            .zip(levels.iter().cloned())
            .collect();
        Ok((declaration, values))
    }
    fn family(
        &mut self,
        name: &str,
        levels: &[Level],
        depth: usize,
    ) -> Result<(Family, HashMap<String, Level>)> {
        let (decl, map) = self.specialization(name, levels, depth)?;
        Ok((decl.family.ok_or("an inductive datatype is required")?, map))
    }
    fn constructor_type(
        &mut self,
        name: &str,
        levels: &[Level],
        constructor: &str,
        depth: usize,
    ) -> Result<(T, Vec<bool>)> {
        let (family, map) = self.family(name, levels, depth)?;
        let ctor = family
            .constructors
            .iter()
            .find(|c| c.name == constructor)
            .ok_or("unknown inductive constructor")?;
        let count = family.parameters.len() + ctor.fields.len();
        let params = (0..family.parameters.len())
            .map(|i| term(Term::Var(count - 1 - i)))
            .collect::<Vec<_>>();
        let result = apps(term(Term::Global(name.into(), levels.to_vec())), &params);
        // The return already uses specialized universe levels. Substitute only
        // telescope annotations, never substitute the caller's levels again.
        let mut domains = vec![];
        for ty in family.parameters.iter().chain(&ctor.fields) {
            domains.push(self.universes(ty, &map, depth + 1)?);
        }
        Ok((pis(&domains, result), ctor.recursive.clone()))
    }
    fn arguments(&mut self, ctx: &[T], mut ty: T, args: &[T], depth: usize) -> Result<T> {
        for arg in args {
            let reduced = self.whnf(&ty, depth + 1)?;
            let Term::Pi(domain, body) = reduced.as_ref() else {
                return Err("too many arguments or non-function application".into());
            };
            self.check(ctx, arg, domain, depth + 1)?;
            ty = self.instantiate(body, arg, depth + 1)?;
        }
        Ok(ty)
    }
    fn check(&mut self, ctx: &[T], value: &T, expected: &T, depth: usize) -> Result<()> {
        self.tick(depth)?;
        let actual = self.infer(ctx, value, depth + 1)?;
        if self.convertible(&actual, expected, depth + 1)? {
            Ok(())
        } else {
            Err("kernel type mismatch: proof term does not establish its declared type".into())
        }
    }
    fn sort(&mut self, ctx: &[T], value: &T, depth: usize) -> Result<Level> {
        let ty = self.infer(ctx, value, depth + 1)?;
        let ty = self.whnf(&ty, depth + 1)?;
        if let Term::Sort(level) = ty.as_ref() {
            Ok(level.clone())
        } else {
            Err("kernel expected a type or proposition".into())
        }
    }
    fn infer(&mut self, ctx: &[T], value: &T, depth: usize) -> Result<T> {
        self.tick(depth)?;
        match value.as_ref() {
            Term::Sort(level) => Ok(term(Term::Sort(level.successor()?))),
            Term::Var(index) => {
                let offset = index.checked_add(1).ok_or("unbound kernel variable")?;
                let ty = ctx
                    .get(
                        ctx.len()
                            .checked_sub(offset)
                            .ok_or("unbound kernel variable")?,
                    )
                    .ok_or("unbound kernel variable")?;
                self.shift(ty, offset, 0, depth + 1)
            }
            Term::Global(name, levels) => {
                let (decl, map) = self.specialization(name, levels, depth + 1)?;
                self.universes(&decl.ty, &map, depth + 1)
            }
            Term::Pi(domain, body) | Term::Sigma(domain, body) => {
                let a = self.sort(ctx, domain, depth + 1)?;
                let mut inner = ctx.to_vec();
                inner.push(domain.clone());
                let b = self.sort(&inner, body, depth + 1)?;
                let result = if matches!(value.as_ref(), Term::Pi(..)) {
                    a.imax(&b)?
                } else {
                    a.maximum(&b)?.maximum(&Level::number(1)?)?
                };
                Ok(term(Term::Sort(result)))
            }
            Term::Lam(domain, body) => {
                self.sort(ctx, domain, depth + 1)?;
                let mut inner = ctx.to_vec();
                inner.push(domain.clone());
                let ty = self.infer(&inner, body, depth + 1)?;
                Ok(term(Term::Pi(domain.clone(), ty)))
            }
            Term::App(function, arg) => {
                let ty = self.infer(ctx, function, depth + 1)?;
                self.arguments(ctx, ty, std::slice::from_ref(arg), depth + 1)
            }
            Term::Pair(ty, first, second) => {
                self.sort(ctx, ty, depth + 1)?;
                let shape = self.whnf(ty, depth + 1)?;
                let Term::Sigma(a, b) = shape.as_ref() else {
                    return Err("#pt-pair requires an explicit dependent-pair type".into());
                };
                self.check(ctx, first, a, depth + 1)?;
                let second_type = self.instantiate(b, first, depth + 1)?;
                self.check(ctx, second, &second_type, depth + 1)?;
                Ok(ty.clone())
            }
            Term::First(pair) | Term::Second(pair) => {
                let ty = self.infer(ctx, pair, depth + 1)?;
                let ty = self.whnf(&ty, depth + 1)?;
                let Term::Sigma(a, b) = ty.as_ref() else {
                    return Err("dependent-pair projection requires a Sigma value".into());
                };
                if matches!(value.as_ref(), Term::First(_)) {
                    Ok(a.clone())
                } else {
                    self.instantiate(b, &term(Term::First(pair.clone())), depth + 1)
                }
            }
            Term::Eq(ty, a, b) => {
                self.sort(ctx, ty, depth + 1)?;
                self.check(ctx, a, ty, depth + 1)?;
                self.check(ctx, b, ty, depth + 1)?;
                Ok(term(Term::Sort(Level::number(0)?)))
            }
            Term::Refl(ty, a) => {
                self.sort(ctx, ty, depth + 1)?;
                self.check(ctx, a, ty, depth + 1)?;
                Ok(term(Term::Eq(ty.clone(), a.clone(), a.clone())))
            }
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => self.equality_elimination(ctx, ty, left, motive, base, right, proof, depth + 1),
            Term::Ctor {
                family,
                levels,
                parameters,
                constructor,
                fields,
            } => {
                let (desc, _) = self.family(family, levels, depth + 1)?;
                let ctor = desc
                    .constructors
                    .iter()
                    .find(|c| &c.name == constructor)
                    .ok_or("unknown inductive constructor")?;
                if parameters.len() != desc.parameters.len() || fields.len() != ctor.fields.len() {
                    return Err("inductive constructor argument count mismatch".into());
                }
                let (ty, _) = self.constructor_type(family, levels, constructor, depth + 1)?;
                let ty = self.arguments(ctx, ty, parameters, depth + 1)?;
                self.arguments(ctx, ty, fields, depth + 1)
            }
            Term::Induct {
                family,
                levels,
                parameters,
                motive,
                branches,
                subject,
            } => self.induction(
                ctx,
                family,
                levels,
                parameters,
                motive,
                branches,
                subject,
                depth + 1,
            ),
            Term::SelfType => Err("#pt-self is only valid as a direct inductive field type".into()),
        }
    }
    #[expect(clippy::too_many_arguments)]
    fn equality_elimination(
        &mut self,
        ctx: &[T],
        ty: &T,
        left: &T,
        motive: &T,
        base: &T,
        right: &T,
        proof: &T,
        depth: usize,
    ) -> Result<T> {
        self.sort(ctx, ty, depth + 1)?;
        self.check(ctx, left, ty, depth + 1)?;
        self.check(ctx, right, ty, depth + 1)?;
        self.check(
            ctx,
            proof,
            &term(Term::Eq(ty.clone(), left.clone(), right.clone())),
            depth + 1,
        )?;
        let mt = self.infer(ctx, motive, depth + 1)?;
        let mt = self.whnf(&mt, depth + 1)?;
        let Term::Pi(domain, rest) = mt.as_ref() else {
            return Err("equality motive requires an endpoint binder".into());
        };
        if !self.convertible(domain, ty, depth + 1)? {
            return Err("equality motive endpoint has the wrong type".into());
        }
        let rest = self.whnf(rest, depth + 1)?;
        let Term::Pi(equality, range) = rest.as_ref() else {
            return Err("equality motive requires an equality-proof binder".into());
        };
        let shifted_type = self.shift(ty, 1, 0, depth + 1)?;
        let shifted_left = self.shift(left, 1, 0, depth + 1)?;
        let expected = term(Term::Eq(shifted_type, shifted_left, term(Term::Var(0))));
        if !self.convertible(equality, &expected, depth + 1)? {
            return Err(
                "equality motive proof binder must depend on its arbitrary endpoint".into(),
            );
        }
        if !matches!(self.whnf(range, depth + 1)?.as_ref(), Term::Sort(_)) {
            return Err("equality motive must return a fixed universe sort".into());
        }
        let base_type = apps(
            motive.clone(),
            &[left.clone(), term(Term::Refl(ty.clone(), left.clone()))],
        );
        self.sort(ctx, &base_type, depth + 1)?;
        self.check(ctx, base, &base_type, depth + 1)?;
        let result = apps(motive.clone(), &[right.clone(), proof.clone()]);
        self.sort(ctx, &result, depth + 1)?;
        Ok(result)
    }
    #[expect(clippy::too_many_arguments)]
    fn induction(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        motive: &T,
        branches: &[T],
        subject: &T,
        depth: usize,
    ) -> Result<T> {
        let (desc, map) = self.family(name, levels, depth + 1)?;
        if parameters.len() != desc.parameters.len() || branches.len() != desc.constructors.len() {
            return Err("induction parameter or branch count mismatch".into());
        }
        let (decl, _) = self.specialization(name, levels, depth + 1)?;
        let ty = self.universes(&decl.ty, &map, depth + 1)?;
        self.arguments(ctx, ty, parameters, depth + 1)?;
        let family_type = apps(term(Term::Global(name.into(), levels.to_vec())), parameters);
        self.check(ctx, subject, &family_type, depth + 1)?;
        let mt = self.infer(ctx, motive, depth + 1)?;
        let mt = self.whnf(&mt, depth + 1)?;
        let Term::Pi(domain, range) = mt.as_ref() else {
            return Err("induction motive must bind its subject".into());
        };
        if !matches!(self.whnf(range, depth + 1)?.as_ref(), Term::Sort(_)) {
            return Err("induction motive must return a fixed universe sort".into());
        }
        if !self.convertible(domain, &family_type, depth + 1)? {
            return Err("induction motive has the wrong subject type".into());
        }
        let result = apps(motive.clone(), std::slice::from_ref(subject));
        let target_sort = self.sort(ctx, &result, depth + 1)?;
        if !desc.large
            && !desc
                .sort
                .substitute(&map)?
                .zero_implies_zero(&target_sort)?
        {
            return Err("large elimination from this proposition is forbidden".into());
        }
        for (ctor, branch) in desc.constructors.iter().zip(branches) {
            let expected = self.branch_type(name, levels, parameters, motive, ctor, depth + 1)?;
            self.check(ctx, branch, &expected, depth + 1)?;
        }
        Ok(result)
    }
    fn branch_type(
        &mut self,
        name: &str,
        levels: &[Level],
        parameters: &[T],
        motive: &T,
        ctor: &Constructor,
        depth: usize,
    ) -> Result<T> {
        let (mut ty, recursive) = self.constructor_type(name, levels, &ctor.name, depth + 1)?;
        // The parameter application was already checked by induction.
        for parameter in parameters {
            let reduced = self.whnf(&ty, depth + 1)?;
            let Term::Pi(_, body) = reduced.as_ref() else {
                return Err("invalid constructor telescope".into());
            };
            ty = self.instantiate(body, parameter, depth + 1)?;
        }
        let mut domains = vec![];
        let mut args: Vec<T> = vec![];
        let mut params = parameters.to_vec();
        let mut motive = motive.clone();
        for is_recursive in recursive {
            let reduced = self.whnf(&ty, depth + 1)?;
            let Term::Pi(domain, body) = reduced.as_ref() else {
                return Err("invalid constructor field telescope".into());
            };
            domains.push(domain.clone());
            ty = body.clone();
            args = self.shift_many(&args, 1, depth + 1)?;
            args.push(term(Term::Var(0)));
            params = self.shift_many(&params, 1, depth + 1)?;
            motive = self.shift(&motive, 1, 0, depth + 1)?;
            if is_recursive {
                domains.push(term(Term::App(motive.clone(), term(Term::Var(0)))));
                ty = self.shift(&ty, 1, 0, depth + 1)?;
                args = self.shift_many(&args, 1, depth + 1)?;
                params = self.shift_many(&params, 1, depth + 1)?;
                motive = self.shift(&motive, 1, 0, depth + 1)?;
            }
        }
        let value = term(Term::Ctor {
            family: name.into(),
            levels: levels.to_vec(),
            parameters: params,
            constructor: ctor.name.clone(),
            fields: args,
        });
        Ok(pis(&domains, term(Term::App(motive, value))))
    }
    fn whnf(&mut self, value: &T, depth: usize) -> Result<T> {
        self.tick(depth)?;
        let mut value = value.clone();
        loop {
            self.tick(depth)?;
            match value.as_ref() {
                Term::Global(name, levels) => {
                    let (decl, map) = self.specialization(name, levels, depth + 1)?;
                    let Some(body) = decl.value else {
                        return Ok(value);
                    };
                    value = self.universes(&body, &map, depth + 1)?;
                }
                Term::App(function, arg) => {
                    let f = self.whnf(function, depth + 1)?;
                    if let Term::Lam(_, body) = f.as_ref() {
                        value = self.instantiate(body, arg, depth + 1)?;
                    } else {
                        return Ok(term(Term::App(f, arg.clone())));
                    }
                }
                Term::First(pair) | Term::Second(pair) => {
                    let reduced = self.whnf(pair, depth + 1)?;
                    if let Term::Pair(_, a, b) = reduced.as_ref() {
                        value = if matches!(value.as_ref(), Term::First(_)) {
                            a.clone()
                        } else {
                            b.clone()
                        };
                    } else {
                        return Ok(value);
                    }
                }
                Term::EqElim { proof, base, .. } => {
                    let reduced = self.whnf(proof, depth + 1)?;
                    if matches!(reduced.as_ref(), Term::Refl(..)) {
                        value = base.clone();
                    } else {
                        return Ok(value);
                    }
                }
                Term::Induct {
                    family,
                    levels,
                    parameters,
                    motive,
                    branches,
                    subject,
                } => {
                    let subject = self.whnf(subject, depth + 1)?;
                    let Term::Ctor {
                        family: actual,
                        constructor,
                        fields,
                        ..
                    } = subject.as_ref()
                    else {
                        return Ok(value);
                    };
                    if actual != family {
                        return Err("induction subject belongs to a different family".into());
                    }
                    let (desc, _) = self.family(family, levels, depth + 1)?;
                    let index = desc
                        .constructors
                        .iter()
                        .position(|c| &c.name == constructor)
                        .ok_or("invalid induction constructor")?;
                    let mut result = branches
                        .get(index)
                        .cloned()
                        .ok_or("missing induction branch")?;
                    for (field, recursive) in fields.iter().zip(&desc.constructors[index].recursive)
                    {
                        result = term(Term::App(result, field.clone()));
                        if *recursive {
                            result = term(Term::App(
                                result,
                                term(Term::Induct {
                                    family: family.clone(),
                                    levels: levels.clone(),
                                    parameters: parameters.clone(),
                                    motive: motive.clone(),
                                    branches: branches.clone(),
                                    subject: field.clone(),
                                }),
                            ));
                        }
                    }
                    value = result;
                }
                _ => return Ok(value),
            }
        }
    }
    fn convertible(&mut self, a: &T, b: &T, depth: usize) -> Result<bool> {
        self.tick(depth)?;
        if Arc::ptr_eq(a, b) {
            return Ok(true);
        }
        let a = self.whnf(a, depth + 1)?;
        let b = self.whnf(b, depth + 1)?;
        match (a.as_ref(), b.as_ref()) {
            (Term::Sort(a), Term::Sort(b)) => a.equivalent(b),
            (Term::Var(a), Term::Var(b)) => Ok(a == b),
            (Term::Global(a, u), Term::Global(b, v)) => Ok(a == b && same_levels(u, v)?),
            (Term::Pi(a, b), Term::Pi(c, d))
            | (Term::Lam(a, b), Term::Lam(c, d))
            | (Term::Sigma(a, b), Term::Sigma(c, d))
            | (Term::App(a, b), Term::App(c, d)) => {
                Ok(self.convertible(a, c, depth + 1)? && self.convertible(b, d, depth + 1)?)
            }
            (Term::Pair(a, b, c), Term::Pair(d, e, f)) | (Term::Eq(a, b, c), Term::Eq(d, e, f)) => {
                Ok(self.convertible(a, d, depth + 1)?
                    && self.convertible(b, e, depth + 1)?
                    && self.convertible(c, f, depth + 1)?)
            }
            (Term::First(a), Term::First(b)) | (Term::Second(a), Term::Second(b)) => {
                self.convertible(a, b, depth + 1)
            }
            (Term::Refl(a, b), Term::Refl(c, d)) => {
                Ok(self.convertible(a, c, depth + 1)? && self.convertible(b, d, depth + 1)?)
            }
            (
                Term::Ctor {
                    family: a,
                    levels: u,
                    parameters: p,
                    constructor: c,
                    fields: f,
                },
                Term::Ctor {
                    family: b,
                    levels: v,
                    parameters: q,
                    constructor: d,
                    fields: g,
                },
            ) => Ok(a == b
                && same_levels(u, v)?
                && c == d
                && self.same_many(p, q, depth + 1)?
                && self.same_many(f, g, depth + 1)?),
            (
                Term::Induct {
                    family: a,
                    levels: u,
                    parameters: p,
                    motive: m,
                    branches: r,
                    subject: s,
                },
                Term::Induct {
                    family: b,
                    levels: v,
                    parameters: q,
                    motive: n,
                    branches: t,
                    subject: w,
                },
            ) => Ok(a == b
                && same_levels(u, v)?
                && self.same_many(p, q, depth + 1)?
                && self.convertible(m, n, depth + 1)?
                && self.same_many(r, t, depth + 1)?
                && self.convertible(s, w, depth + 1)?),
            (
                Term::EqElim {
                    ty: a,
                    left: b,
                    motive: c,
                    base: d,
                    right: e,
                    proof: f,
                },
                Term::EqElim {
                    ty: g,
                    left: h,
                    motive: i,
                    base: j,
                    right: k,
                    proof: l,
                },
            ) => self.same_many(
                &[
                    a.clone(),
                    b.clone(),
                    c.clone(),
                    d.clone(),
                    e.clone(),
                    f.clone(),
                ],
                &[
                    g.clone(),
                    h.clone(),
                    i.clone(),
                    j.clone(),
                    k.clone(),
                    l.clone(),
                ],
                depth + 1,
            ),
            _ => Ok(false),
        }
    }
    fn same_many(&mut self, a: &[T], b: &[T], depth: usize) -> Result<bool> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            if !self.convertible(a, b, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn shift_many(&mut self, values: &[T], amount: usize, depth: usize) -> Result<Vec<T>> {
        values
            .iter()
            .map(|t| self.shift(t, amount, 0, depth + 1))
            .collect()
    }
    fn shift(&mut self, value: &T, amount: usize, cutoff: usize, depth: usize) -> Result<T> {
        self.transform(
            value,
            cutoff,
            depth,
            &mut |_, index, binders| {
                Ok(term(Term::Var(if index >= binders {
                    index.checked_add(amount).ok_or("variable index overflow")?
                } else {
                    index
                })))
            },
            &mut |l| Ok(l.clone()),
        )
    }
    fn instantiate(&mut self, body: &T, arg: &T, depth: usize) -> Result<T> {
        self.transform(
            body,
            0,
            depth,
            &mut |kernel, index, binders| {
                if index == binders {
                    kernel.shift(arg, binders, 0, depth + 1)
                } else {
                    Ok(term(Term::Var(if index > binders {
                        index - 1
                    } else {
                        index
                    })))
                }
            },
            &mut |l| Ok(l.clone()),
        )
    }
    fn universes(&mut self, value: &T, map: &HashMap<String, Level>, depth: usize) -> Result<T> {
        self.transform(
            value,
            0,
            depth,
            &mut |_, index, _| Ok(term(Term::Var(index))),
            &mut |l| l.substitute(map),
        )
    }
    fn transform(
        &mut self,
        value: &T,
        binders: usize,
        depth: usize,
        var: &mut impl FnMut(&mut Self, usize, usize) -> Result<T>,
        level: &mut impl FnMut(&Level) -> Result<Level>,
    ) -> Result<T> {
        self.tick(depth)?;
        macro_rules! walk {
            ($t:expr) => {
                self.transform($t, binders, depth + 1, var, level)?
            };
        }
        macro_rules! many {
            ($ts:expr) => {
                $ts.iter()
                    .map(|t| self.transform(t, binders, depth + 1, var, level))
                    .collect::<Result<Vec<_>>>()?
            };
        }
        Ok(term(match value.as_ref() {
            Term::Var(index) => return var(self, *index, binders),
            Term::Sort(l) => Term::Sort(level(l)?),
            Term::Global(n, ls) => Term::Global(
                n.clone(),
                ls.iter().map(&mut *level).collect::<Result<_>>()?,
            ),
            Term::Pi(a, b) | Term::Lam(a, b) | Term::Sigma(a, b) => {
                let a = walk!(a);
                let b = self.transform(b, binders + 1, depth + 1, var, level)?;
                match value.as_ref() {
                    Term::Pi(..) => Term::Pi(a, b),
                    Term::Lam(..) => Term::Lam(a, b),
                    _ => Term::Sigma(a, b),
                }
            }
            Term::App(a, b) => Term::App(walk!(a), walk!(b)),
            Term::Pair(a, b, c) => Term::Pair(walk!(a), walk!(b), walk!(c)),
            Term::First(a) => Term::First(walk!(a)),
            Term::Second(a) => Term::Second(walk!(a)),
            Term::Eq(a, b, c) => Term::Eq(walk!(a), walk!(b), walk!(c)),
            Term::Refl(a, b) => Term::Refl(walk!(a), walk!(b)),
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => Term::EqElim {
                ty: walk!(ty),
                left: walk!(left),
                motive: walk!(motive),
                base: walk!(base),
                right: walk!(right),
                proof: walk!(proof),
            },
            Term::Ctor {
                family,
                levels,
                parameters,
                constructor,
                fields,
            } => Term::Ctor {
                family: family.clone(),
                levels: levels.iter().map(&mut *level).collect::<Result<_>>()?,
                parameters: many!(parameters),
                constructor: constructor.clone(),
                fields: many!(fields),
            },
            Term::Induct {
                family,
                levels,
                parameters,
                motive,
                branches,
                subject,
            } => Term::Induct {
                family: family.clone(),
                levels: levels.iter().map(&mut *level).collect::<Result<_>>()?,
                parameters: many!(parameters),
                motive: walk!(motive),
                branches: many!(branches),
                subject: walk!(subject),
            },
            Term::SelfType => Term::SelfType,
        }))
    }
}
pub(super) fn apps(mut f: T, args: &[T]) -> T {
    for arg in args {
        f = term(Term::App(f, arg.clone()));
    }
    f
}
fn pis(domains: &[T], mut body: T) -> T {
    for domain in domains.iter().rev() {
        body = term(Term::Pi(domain.clone(), body));
    }
    body
}
fn contains_recursive(t: &T, name: &str) -> bool {
    match t.as_ref() {
        Term::SelfType => true,
        Term::Global(global, _) if global == name => true,
        Term::Ctor { family, .. } | Term::Induct { family, .. } if family == name => true,
        Term::Pi(a, b)
        | Term::Lam(a, b)
        | Term::App(a, b)
        | Term::Sigma(a, b)
        | Term::Refl(a, b) => contains_recursive(a, name) || contains_recursive(b, name),
        Term::Pair(a, b, c) | Term::Eq(a, b, c) => {
            contains_recursive(a, name)
                || contains_recursive(b, name)
                || contains_recursive(c, name)
        }
        Term::First(a) | Term::Second(a) => contains_recursive(a, name),
        Term::EqElim {
            ty,
            left,
            motive,
            base,
            right,
            proof,
        } => [ty, left, motive, base, right, proof]
            .iter()
            .any(|t| contains_recursive(t, name)),
        Term::Ctor {
            parameters, fields, ..
        } => parameters
            .iter()
            .chain(fields)
            .any(|t| contains_recursive(t, name)),
        Term::Induct {
            parameters,
            motive,
            branches,
            subject,
            ..
        } => parameters
            .iter()
            .chain(branches)
            .chain([motive, subject])
            .any(|t| contains_recursive(t, name)),
        _ => false,
    }
}

#[cfg(test)]
#[path = "core_tests.rs"]
mod core_tests;
