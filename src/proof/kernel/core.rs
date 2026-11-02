//! Explicit dependent type checking, independent of parsing and proof search.
//! There is no native execution or cache bypass. The external-evidence rule
//! installs opaque program atoms supplied by the validated certificate adapter.
use super::level::same_levels;
pub(super) use super::level::Level;
#[cfg(test)]
use super::level::LEVEL;
use std::collections::HashMap;
use std::ops::ControlFlow;
use std::sync::Arc;
#[path = "beta.rs"]
mod beta;
#[path = "elimination.rs"]
mod elimination;
#[path = "export.rs"]
pub(super) mod export;
#[path = "foundation.rs"]
pub(super) mod foundation;
#[path = "inductive.rs"]
mod inductive;
#[path = "natural.rs"]
mod natural;
#[path = "nested.rs"]
mod nested;
pub(super) use natural::Natural;
#[path = "quotient.rs"]
mod quotient;
#[path = "syntax.rs"]
mod syntax;
use nested::{NestedBuild, NestedFamily};

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
    NatLiteral {
        family: String,
        value: Natural,
    },
    Pi(T, T),
    Lam(T, T),
    Let(T, T, T),
    App(T, T),
    Sigma(T, T),
    Pair(T, T, T),
    First(T),
    Second(T),
    Project {
        family: String,
        index: usize,
        subject: T,
    },
    Eq(T, T, T),
    Refl(T, T),
    QuotType(Level, T, T),
    QuotMake(Level, T, T, T),
    QuotLift {
        source_level: Level,
        target_level: Level,
        ty: T,
        relation: T,
        target: T,
        function: T,
        respect: T,
        subject: T,
    },
    QuotInduct {
        level: Level,
        ty: T,
        relation: T,
        motive: T,
        branch: T,
        subject: T,
    },
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
        indices: Vec<T>,
        motive: T,
        branches: Vec<T>,
        subject: T,
    },
    MutualInduct {
        family: String,
        levels: Vec<Level>,
        parameters: Vec<T>,
        indices: Vec<T>,
        cases: Vec<RecursionCase>,
        subject: T,
    },
    NestedInduct {
        family: String,
        levels: Vec<Level>,
        parameters: Vec<T>,
        selected: usize,
        indices: Vec<T>,
        cases: Vec<NestedCase>,
        subject: T,
    },
    SelfType,
    SelfAt(Vec<T>),
    Recur(String, Vec<T>),
}
#[derive(Clone, Debug)]
pub(super) struct RecursionCase {
    pub family: String,
    pub motive: T,
    pub branches: Vec<T>,
}
#[derive(Clone, Debug)]
pub(super) struct NestedCase {
    pub selector: T,
    pub motive: T,
    pub branches: Vec<T>,
}
pub(super) struct InductiveInput {
    pub name: String,
    pub universes: Vec<String>,
    pub parameters: Vec<T>,
    pub indices: Vec<T>,
    pub sort: Level,
    pub constructors: Vec<(String, Vec<T>, Vec<T>)>,
}
#[derive(Clone)]
pub(super) struct Constructor {
    pub name: String,
    pub fields: Vec<T>,
    pub recursive: Vec<Option<String>>,
    pub result_indices: Vec<T>,
}
#[derive(Clone)]
pub(super) struct Family {
    pub group: Vec<String>,
    pub parameters: Vec<T>,
    pub indices: Vec<T>,
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
    nested: HashMap<String, NestedFamily>,
    nested_build: Option<NestedBuild>,
    work: usize,
    transformed_bytes: usize,
}
impl Kernel {
    pub fn new() -> Self {
        let mut result = Self {
            declarations: HashMap::new(),
            nested: HashMap::new(),
            nested_build: None,
            work: 0,
            transformed_bytes: 0,
        };
        let nat = term(Term::Global("#pt-nat".into(), vec![]));
        let family = Family {
            group: vec!["#pt-nat".into()],
            parameters: vec![],
            indices: vec![],
            sort: Level::number(1).unwrap(),
            constructors: vec![
                Constructor {
                    name: "zero".into(),
                    fields: vec![],
                    recursive: vec![],
                    result_indices: vec![],
                },
                Constructor {
                    name: "succ".into(),
                    fields: vec![nat],
                    recursive: vec![Some("#pt-nat".into())],
                    result_indices: vec![],
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
                    group: vec!["#pt-false".into()],
                    parameters: vec![],
                    indices: vec![],
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
            || self.nested.contains_key(name)
            || foundation::label(name).is_some()
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
        self.transformed_bytes = 0;
    }
    fn charge_transformation(&mut self, bytes: usize) -> Result<()> {
        self.transformed_bytes = self.transformed_bytes.saturating_add(bytes);
        if self.transformed_bytes > 64 * 1024 * 1024 {
            return Err(
                "kernel transformation allocation limit exceeded; no theorem was established"
                    .into(),
            );
        }
        Ok(())
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
        if self.contains(name) {
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
    /// Check a concrete initializer before making the declaration opaque.
    /// Unlike a theorem, its type need not be a proposition.
    pub(super) fn opaque_definition(
        &mut self,
        name: &str,
        universes: Vec<String>,
        ty: T,
        value: T,
    ) -> Result<()> {
        self.definition(name, universes, ty, value, false)?;
        self.declarations
            .get_mut(name)
            .ok_or("missing checked opaque definition")?
            .value = None;
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
        self.declare_inductive(
            name,
            universes,
            parameters,
            vec![],
            sort,
            constructors
                .into_iter()
                .map(|(n, f)| (n, f, vec![]))
                .collect(),
        )
    }
    pub fn indexed_inductive(
        &mut self,
        name: &str,
        universes: Vec<String>,
        parameters: Vec<T>,
        indices: Vec<T>,
        sort: Level,
        constructors: Vec<(String, Vec<T>, Vec<T>)>,
    ) -> Result<()> {
        if indices.is_empty() {
            return Err("indexed inductives require at least one index".into());
        }
        self.declare_inductive(name, universes, parameters, indices, sort, constructors)
    }
    fn declare_inductive(
        &mut self,
        name: &str,
        universes: Vec<String>,
        parameters: Vec<T>,
        indices: Vec<T>,
        sort: Level,
        constructors: Vec<(String, Vec<T>, Vec<T>)>,
    ) -> Result<()> {
        self.declare_group(vec![InductiveInput {
            name: name.into(),
            universes,
            parameters,
            indices,
            sort,
            constructors,
        }])
    }
    fn specialization(
        &mut self,
        name: &str,
        levels: &[Level],
        depth: usize,
    ) -> Result<(Declaration, HashMap<String, Level>)> {
        self.tick(depth)?;
        self.ensure_logical_foundation(name, depth + 1)?;
        let declaration = self
            .declarations
            .get(name)
            .or_else(|| self.nested.get(name).map(|nested| &nested.declaration))
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
    ) -> Result<(T, Vec<Option<String>>)> {
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
        let indices = ctor
            .result_indices
            .iter()
            .map(|value| self.universes(value, &map, depth + 1))
            .collect::<Result<Vec<_>>>()?;
        let result = self.family_application(name, levels, &params, &indices, depth + 1)?;
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
            let reduced = self.whnf(ctx, &ty, depth + 1)?;
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
        if self.convertible(ctx, &actual, expected, depth + 1)? {
            Ok(())
        } else {
            Err("kernel type mismatch: proof term does not establish its declared type".into())
        }
    }
    fn sort(&mut self, ctx: &[T], value: &T, depth: usize) -> Result<Level> {
        let ty = self.infer(ctx, value, depth + 1)?;
        let ty = self.whnf(ctx, &ty, depth + 1)?;
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
                if self.nested.contains_key(name) {
                    return Err("internal nested family is not a global constant".into());
                }
                let (decl, map) = self.specialization(name, levels, depth + 1)?;
                // A checked monomorphic signature is already closed and
                // scoped. Reuse it as we do its immutable unfolded body.
                if map.is_empty() {
                    Ok(decl.ty)
                } else {
                    self.universes(&decl.ty, &map, depth + 1)
                }
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
            Term::Let(ty, value, body) => {
                // Validate even unused bindings before zeta substitution.
                // Checking the body under an abstract lambda binder would
                // lose the definition needed by dependent type aliases.
                self.sort(ctx, ty, depth + 1)?;
                self.check(ctx, value, ty, depth + 1)?;
                let instantiated = self.instantiate(body, value, depth + 1)?;
                self.infer(ctx, &instantiated, depth + 1)
            }
            Term::App(function, arg) => {
                let ty = self.infer(ctx, function, depth + 1)?;
                self.arguments(ctx, ty, std::slice::from_ref(arg), depth + 1)
            }
            Term::Pair(ty, first, second) => {
                self.sort(ctx, ty, depth + 1)?;
                let shape = self.whnf(ctx, ty, depth + 1)?;
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
                let ty = self.whnf(ctx, &ty, depth + 1)?;
                let Term::Sigma(a, b) = ty.as_ref() else {
                    return Err("dependent-pair projection requires a Sigma value".into());
                };
                if matches!(value.as_ref(), Term::First(_)) {
                    Ok(a.clone())
                } else {
                    self.instantiate(b, &term(Term::First(pair.clone())), depth + 1)
                }
            }
            Term::Project {
                family,
                index,
                subject,
            } => self.projection_type(ctx, family, *index, subject, depth + 1),
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
            Term::QuotType(level, ty, relation) => {
                self.quotient_type(ctx, level, ty, relation, depth + 1)
            }
            Term::QuotMake(level, ty, relation, value) => {
                self.quotient_make(ctx, level, ty, relation, value, depth + 1)
            }
            Term::QuotLift {
                source_level,
                target_level,
                ty,
                relation,
                target,
                function,
                respect,
                subject,
            } => self.quotient_lift(
                ctx,
                source_level,
                target_level,
                ty,
                relation,
                target,
                function,
                respect,
                subject,
                depth + 1,
            ),
            Term::QuotInduct {
                level,
                ty,
                relation,
                motive,
                branch,
                subject,
            } => self.quotient_induct(ctx, level, ty, relation, motive, branch, subject, depth + 1),
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => self.equality_elimination(ctx, ty, left, motive, base, right, proof, depth + 1),
            Term::NatLiteral { family, .. } => {
                self.natural_family(family, depth + 1)?;
                Ok(term(Term::Global(family.clone(), vec![])))
            }
            Term::Ctor {
                family,
                levels,
                parameters,
                constructor,
                fields,
            } => {
                if self.provisional_family(family) {
                    return Err("cannot construct a provisional inductive family".into());
                }
                if self.nested.contains_key(family) {
                    return Err(
                        "internal nested families require their original constructors".into(),
                    );
                }
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
                indices,
                motive,
                branches,
                subject,
            } => self.induction(
                ctx,
                family,
                levels,
                parameters,
                indices,
                motive,
                branches,
                subject,
                depth + 1,
            ),
            Term::MutualInduct {
                family,
                levels,
                parameters,
                indices,
                cases,
                subject,
            } => self.mutual_induction(
                ctx,
                family,
                levels,
                parameters,
                indices,
                cases,
                subject,
                depth + 1,
            ),
            Term::NestedInduct {
                family,
                levels,
                parameters,
                selected,
                indices,
                cases,
                subject,
            } => {
                let cases = self.nested_cases(ctx, family, levels, parameters, cases, depth + 1)?;
                let family = &cases
                    .get(*selected)
                    .ok_or("nested induction case index is out of range")?
                    .family;
                self.mutual_induction(
                    ctx,
                    family,
                    levels,
                    parameters,
                    indices,
                    &cases,
                    subject,
                    depth + 1,
                )
            }
            Term::SelfType | Term::SelfAt(_) | Term::Recur(..) => Err(
                "recursive markers are only valid in strictly positive inductive field codomains"
                    .into(),
            ),
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
        let mt = self.whnf(ctx, &mt, depth + 1)?;
        let Term::Pi(domain, rest) = mt.as_ref() else {
            return Err("equality motive requires an endpoint binder".into());
        };
        if !self.convertible(ctx, domain, ty, depth + 1)? {
            return Err("equality motive endpoint has the wrong type".into());
        }
        let mut endpoint_context = ctx.to_vec();
        endpoint_context.push(domain.clone());
        let rest = self.whnf(&endpoint_context, rest, depth + 1)?;
        let Term::Pi(equality, range) = rest.as_ref() else {
            return Err("equality motive requires an equality-proof binder".into());
        };
        let shifted_type = self.shift(ty, 1, 0, depth + 1)?;
        let shifted_left = self.shift(left, 1, 0, depth + 1)?;
        let expected = term(Term::Eq(shifted_type, shifted_left, term(Term::Var(0))));
        if !self.convertible(&endpoint_context, equality, &expected, depth + 1)? {
            return Err(
                "equality motive proof binder must depend on its arbitrary endpoint".into(),
            );
        }
        let mut motive_context = endpoint_context;
        motive_context.push(equality.clone());
        if !matches!(
            self.whnf(&motive_context, range, depth + 1)?.as_ref(),
            Term::Sort(_)
        ) {
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
    fn family_indices(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        ty: &T,
        depth: usize,
    ) -> Result<Vec<T>> {
        let (desc, _) = self.family(name, levels, depth + 1)?;
        let mut head = self.whnf(ctx, ty, depth + 1)?;
        let mut arguments = vec![];
        while let Term::App(function, argument) = head.as_ref() {
            self.tick(depth)?;
            arguments.push(argument.clone());
            head = function.clone();
        }
        arguments.reverse();
        let Term::Global(actual, actual_levels) = head.as_ref() else {
            return Err("expected a fully applied inductive family".into());
        };
        let expected = self.family_application(name, levels, parameters, &[], depth + 1)?;
        let (expected_head, expected_parameters) = nested::application(&expected);
        let Term::Global(expected_name, expected_levels) = expected_head.as_ref() else {
            return Err("invalid family head".into());
        };
        if actual != expected_name
            || !same_levels(expected_levels, actual_levels)?
            || arguments.len() != expected_parameters.len() + desc.indices.len()
        {
            return Err("inductive family application has the wrong head or arity".into());
        }
        if !self.same_many(
            ctx,
            &expected_parameters,
            &arguments[..expected_parameters.len()],
            depth + 1,
        )? {
            return Err("recursive inductive parameters must remain uniform".into());
        }
        Ok(arguments.split_off(expected_parameters.len()))
    }
    /// Recognize a fully applied nonrecursive, unindexed record type. Merely
    /// having one constructor is insufficient for projection and eta rules.
    fn record_type(
        &mut self,
        shape: &T,
        depth: usize,
    ) -> Result<Option<(String, Vec<Level>, Vec<T>, Family)>> {
        let mut head = shape.clone();
        let mut parameters = vec![];
        while let Term::App(function, argument) = head.as_ref() {
            self.tick(depth)?;
            parameters.push(argument.clone());
            head = function.clone();
        }
        let Term::Global(name, levels) = head.as_ref() else {
            return Ok(None);
        };
        let Some(family) = self.declarations.get(name).and_then(|d| d.family.clone()) else {
            return Ok(None);
        };
        if family.group.len() != 1
            || !family.indices.is_empty()
            || family.parameters.len() != parameters.len()
            || family.constructors.len() != 1
            || family.constructors[0].recursive.iter().any(Option::is_some)
        {
            return Ok(None);
        }
        parameters.reverse();
        Ok(Some((name.clone(), levels.clone(), parameters, family)))
    }
    fn projection_type(
        &mut self,
        ctx: &[T],
        name: &str,
        index: usize,
        subject: &T,
        depth: usize,
    ) -> Result<T> {
        if self.provisional_family(name) {
            return Err("cannot project a provisional inductive family".into());
        }
        let ty = self.infer(ctx, subject, depth + 1)?;
        let shape = self.whnf(ctx, &ty, depth + 1)?;
        let Some((actual, levels, parameters, family)) = self.record_type(&shape, depth + 1)?
        else {
            return Err(
                "#pt-project requires an unindexed, single-constructor nonrecursive record".into(),
            );
        };
        if actual != name {
            return Err("#pt-project subject belongs to a different record family".into());
        }
        let constructor = &family.constructors[0];
        if index >= constructor.fields.len() {
            return Err("#pt-project field index is out of range".into());
        }
        let (_, map) = self.family(name, &levels, depth + 1)?;
        let source_sort = family.sort.substitute(&map)?;
        let (ty, _) = self.constructor_type(name, &levels, &constructor.name, depth + 1)?;
        let mut telescope = self.arguments(ctx, ty, &parameters, depth + 1)?;
        for position in 0..=index {
            let reduced = self.whnf(ctx, &telescope, depth + 1)?;
            let Term::Pi(domain, body) = reduced.as_ref() else {
                return Err("invalid record field telescope".into());
            };
            // A hidden data field cannot escape Prop, including through a
            // later field's dependent type. Skip unused predecessors without
            // fabricating an ill-typed projection into the returned type.
            if position == index || self.uses_bound_variable(body, depth + 1)? {
                let field_sort = self.sort(ctx, domain, depth + 1)?;
                if !source_sort.zero_implies_zero(&field_sort)? {
                    return Err("#pt-project cannot extract data or a data-dependent field from a proposition".into());
                }
            }
            if position == index {
                return Ok(domain.clone());
            }
            let field = term(Term::Project {
                family: name.into(),
                index: position,
                subject: subject.clone(),
            });
            telescope = self.instantiate(body, &field, depth + 1)?;
        }
        Err("invalid record field index".into())
    }
    fn uses_bound_variable(&mut self, body: &T, depth: usize) -> Result<bool> {
        let mut found = false;
        self.transform(
            body,
            0,
            depth,
            &mut |_, index, binders| {
                found |= index == binders;
                Ok(term(Term::Var(index)))
            },
            &mut |level| Ok(level.clone()),
        )?;
        Ok(found)
    }
    fn whnf(&mut self, ctx: &[T], value: &T, depth: usize) -> Result<T> {
        self.tick(depth)?;
        let mut value = value.clone();
        loop {
            self.tick(depth)?;
            if matches!(value.as_ref(), Term::App(..) | Term::Project { .. }) {
                let head = self.natural_head(&value, depth + 1)?;
                if !Arc::ptr_eq(&head, &value) {
                    value = head;
                    continue;
                }
            }
            match value.as_ref() {
                Term::Global(name, levels) => {
                    let (decl, map) = self.specialization(name, levels, depth + 1)?;
                    let Some(body) = decl.value else {
                        return Ok(value);
                    };
                    // Its declaration was fully scoped and checked before
                    // insertion. With no universe parameters, unfolding needs
                    // no substitution or copy. Scope validation still always
                    // traverses source terms, including monomorphic ones.
                    value = if map.is_empty() {
                        body
                    } else {
                        self.universes(&body, &map, depth + 1)?
                    };
                }
                Term::App(function, arg) => {
                    let f = self.whnf(ctx, function, depth + 1)?;
                    if let Term::Lam(_, body) = f.as_ref() {
                        value = self.instantiate(body, arg, depth + 1)?;
                    } else {
                        return Ok(term(Term::App(f, arg.clone())));
                    }
                }
                Term::Let(_, definition, body) => {
                    value = self.instantiate(body, definition, depth + 1)?;
                }
                Term::First(pair) | Term::Second(pair) => {
                    let reduced = self.whnf(ctx, pair, depth + 1)?;
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
                Term::Project {
                    family,
                    index,
                    subject,
                } => {
                    let reduced = self.whnf(ctx, subject, depth + 1)?;
                    if let Term::Ctor {
                        family: actual,
                        fields,
                        ..
                    } = reduced.as_ref()
                    {
                        if actual == family {
                            value = fields
                                .get(*index)
                                .cloned()
                                .ok_or("invalid record field index")?;
                            continue;
                        }
                    }
                    return Ok(value);
                }
                Term::EqElim {
                    proof,
                    base,
                    left,
                    right,
                    ..
                } => {
                    let reduced = self.whnf(ctx, proof, depth + 1)?;
                    if matches!(reduced.as_ref(), Term::Refl(..))
                        || self.convertible(ctx, left, right, depth + 1)?
                    {
                        value = base.clone();
                    } else {
                        return Ok(value);
                    }
                }
                Term::Induct {
                    family,
                    levels,
                    parameters,
                    indices,
                    motive,
                    branches,
                    subject,
                } => {
                    let cases = [RecursionCase {
                        family: family.clone(),
                        motive: motive.clone(),
                        branches: branches.clone(),
                    }];
                    if let Some(reduced) = self.reduce_induction(
                        ctx,
                        family,
                        levels,
                        parameters,
                        indices,
                        &cases,
                        subject,
                        depth + 1,
                    )? {
                        value = reduced;
                    } else {
                        return Ok(value);
                    }
                }
                Term::MutualInduct {
                    family,
                    levels,
                    parameters,
                    indices,
                    cases,
                    subject,
                } => {
                    if let Some(reduced) = self.reduce_induction(
                        ctx,
                        family,
                        levels,
                        parameters,
                        indices,
                        cases,
                        subject,
                        depth + 1,
                    )? {
                        value = reduced;
                    } else {
                        return Ok(value);
                    }
                }
                Term::NestedInduct {
                    family,
                    levels,
                    parameters,
                    selected,
                    indices,
                    cases,
                    subject,
                } => {
                    let cases =
                        self.nested_cases(ctx, family, levels, parameters, cases, depth + 1)?;
                    let family = cases
                        .get(*selected)
                        .ok_or("nested induction case index is out of range")?
                        .family
                        .clone();
                    value = term(Term::MutualInduct {
                        family,
                        levels: levels.clone(),
                        parameters: parameters.clone(),
                        indices: indices.clone(),
                        cases,
                        subject: subject.clone(),
                    });
                }
                Term::QuotLift {
                    source_level,
                    ty,
                    relation,
                    function,
                    subject,
                    ..
                }
                | Term::QuotInduct {
                    level: source_level,
                    ty,
                    relation,
                    branch: function,
                    subject,
                    ..
                } => {
                    let reduced = self.whnf(ctx, subject, depth + 1)?;
                    if let Term::QuotMake(
                        actual_level,
                        actual_ty,
                        actual_relation,
                        representative,
                    ) = reduced.as_ref()
                    {
                        if source_level.equivalent(actual_level)?
                            && self.convertible(ctx, ty, actual_ty, depth + 1)?
                            && self.convertible(ctx, relation, actual_relation, depth + 1)?
                        {
                            value = apps(function.clone(), std::slice::from_ref(representative));
                            continue;
                        }
                    }
                    return Ok(value);
                }
                _ => return Ok(value),
            }
        }
    }
    fn convertible(&mut self, ctx: &[T], a: &T, b: &T, depth: usize) -> Result<bool> {
        self.conversion(ctx, a, b, true, depth)
    }
    fn conversion(&mut self, ctx: &[T], a: &T, b: &T, eta: bool, depth: usize) -> Result<bool> {
        self.tick(depth)?;
        // Identical syntax needs no reduction. In particular, unfolding two
        // copies of the same dependent predicate can duplicate its history.
        // Source typing still happens in check before this comparison.
        if Arc::ptr_eq(a, b) || self.same_syntax(a, b)? {
            return Ok(true);
        }
        let a = self.whnf(ctx, a, depth + 1)?;
        let b = self.whnf(ctx, b, depth + 1)?;
        if Arc::ptr_eq(&a, &b) || self.same_syntax(&a, &b)? {
            return Ok(true);
        }
        if matches!(
            (a.as_ref(), b.as_ref()),
            (Term::NatLiteral { .. }, Term::Ctor { .. })
                | (Term::Ctor { .. }, Term::NatLiteral { .. })
        ) {
            let a = self.natural_constructor(&a, depth + 1)?;
            let b = self.natural_constructor(&b, depth + 1)?;
            return self.conversion(ctx, &a, &b, eta, depth + 1);
        }
        let structurally_equal = match (a.as_ref(), b.as_ref()) {
            (
                Term::NatLiteral {
                    family: a,
                    value: x,
                },
                Term::NatLiteral {
                    family: b,
                    value: y,
                },
            ) => Ok(a == b && x == y),
            (Term::Sort(a), Term::Sort(b)) => a.equivalent(b),
            (Term::Var(a), Term::Var(b)) => Ok(a == b),
            (Term::Global(a, u), Term::Global(b, v)) => Ok(a == b && same_levels(u, v)?),
            (Term::QuotType(u, a, r), Term::QuotType(v, b, s)) => Ok(u.equivalent(v)?
                && self.convertible(ctx, a, b, depth + 1)?
                && self.convertible(ctx, r, s, depth + 1)?),
            (Term::QuotMake(u, a, r, x), Term::QuotMake(v, b, s, y)) => Ok(u.equivalent(v)?
                && self.same_many(
                    ctx,
                    &[a.clone(), r.clone(), x.clone()],
                    &[b.clone(), s.clone(), y.clone()],
                    depth + 1,
                )?),
            (
                Term::QuotLift {
                    source_level: u,
                    target_level: v,
                    ty: a,
                    relation: r,
                    target: b,
                    function: f,
                    respect: h,
                    subject: q,
                },
                Term::QuotLift {
                    source_level: w,
                    target_level: z,
                    ty: c,
                    relation: s,
                    target: d,
                    function: g,
                    respect: i,
                    subject: p,
                },
            ) => Ok(u.equivalent(w)?
                && v.equivalent(z)?
                && self.same_many(
                    ctx,
                    &[
                        a.clone(),
                        r.clone(),
                        b.clone(),
                        f.clone(),
                        h.clone(),
                        q.clone(),
                    ],
                    &[
                        c.clone(),
                        s.clone(),
                        d.clone(),
                        g.clone(),
                        i.clone(),
                        p.clone(),
                    ],
                    depth + 1,
                )?),
            (
                Term::QuotInduct {
                    level: u,
                    ty: a,
                    relation: r,
                    motive: m,
                    branch: b,
                    subject: q,
                },
                Term::QuotInduct {
                    level: v,
                    ty: c,
                    relation: s,
                    motive: n,
                    branch: d,
                    subject: p,
                },
            ) => Ok(u.equivalent(v)?
                && self.same_many(
                    ctx,
                    &[a.clone(), r.clone(), m.clone(), b.clone(), q.clone()],
                    &[c.clone(), s.clone(), n.clone(), d.clone(), p.clone()],
                    depth + 1,
                )?),
            (Term::Pi(a, b), Term::Pi(c, d))
            | (Term::Lam(a, b), Term::Lam(c, d))
            | (Term::Sigma(a, b), Term::Sigma(c, d)) => {
                if self.convertible(ctx, a, c, depth + 1)? {
                    let mut inner = ctx.to_vec();
                    inner.push(a.clone());
                    self.convertible(&inner, b, d, depth + 1)
                } else {
                    Ok(false)
                }
            }
            // Comparing neutral heads or projection subjects with eta again
            // would revisit the same problem. Arguments keep full conversion.
            (Term::App(a, b), Term::App(c, d)) => {
                Ok(self.conversion(ctx, a, c, false, depth + 1)?
                    && self.convertible(ctx, b, d, depth + 1)?)
            }
            (Term::Pair(a, b, c), Term::Pair(d, e, f)) | (Term::Eq(a, b, c), Term::Eq(d, e, f)) => {
                Ok(self.convertible(ctx, a, d, depth + 1)?
                    && self.convertible(ctx, b, e, depth + 1)?
                    && self.convertible(ctx, c, f, depth + 1)?)
            }
            (Term::First(a), Term::First(b)) | (Term::Second(a), Term::Second(b)) => {
                self.conversion(ctx, a, b, false, depth + 1)
            }
            (
                Term::Project {
                    family: a,
                    index: i,
                    subject: s,
                },
                Term::Project {
                    family: b,
                    index: j,
                    subject: t,
                },
            ) => Ok(a == b && i == j && self.conversion(ctx, s, t, false, depth + 1)?),
            (Term::Refl(a, b), Term::Refl(c, d)) => Ok(self.convertible(ctx, a, c, depth + 1)?
                && self.convertible(ctx, b, d, depth + 1)?),
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
                && self.same_many(ctx, p, q, depth + 1)?
                && self.same_many(ctx, f, g, depth + 1)?),
            (
                Term::Induct {
                    family: a,
                    levels: u,
                    parameters: p,
                    indices: i,
                    motive: m,
                    branches: r,
                    subject: s,
                },
                Term::Induct {
                    family: b,
                    levels: v,
                    parameters: q,
                    indices: j,
                    motive: n,
                    branches: t,
                    subject: w,
                },
            ) => Ok(a == b
                && same_levels(u, v)?
                && self.same_many(ctx, p, q, depth + 1)?
                && self.same_many(ctx, i, j, depth + 1)?
                && self.convertible(ctx, m, n, depth + 1)?
                && self.same_many(ctx, r, t, depth + 1)?
                && self.convertible(ctx, s, w, depth + 1)?),
            (
                Term::MutualInduct {
                    family: a,
                    levels: u,
                    parameters: p,
                    indices: i,
                    cases: c,
                    subject: s,
                },
                Term::MutualInduct {
                    family: b,
                    levels: v,
                    parameters: q,
                    indices: j,
                    cases: d,
                    subject: t,
                },
            ) => {
                let mut equal = a == b
                    && same_levels(u, v)?
                    && self.same_many(ctx, p, q, depth + 1)?
                    && self.same_many(ctx, i, j, depth + 1)?
                    && c.len() == d.len();
                if equal {
                    for (c, d) in c.iter().zip(d) {
                        equal = c.family == d.family
                            && self.convertible(ctx, &c.motive, &d.motive, depth + 1)?
                            && self.same_many(ctx, &c.branches, &d.branches, depth + 1)?;
                        if !equal {
                            break;
                        }
                    }
                }
                Ok(equal && self.convertible(ctx, s, t, depth + 1)?)
            }
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
                ctx,
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
        }?;
        if structurally_equal {
            return Ok(true);
        }
        // Classify the type of a term, not the term's syntax. Prop itself is a
        // type, and arbitrary Sort-polymorphic data is not necessarily proof.
        let a_type = self.infer(ctx, &a, depth + 1)?;
        if self.sort(ctx, &a_type, depth + 1)?.zero() {
            let b_type = self.infer(ctx, &b, depth + 1)?;
            return self.convertible(ctx, &a_type, &b_type, depth + 1);
        }
        let shape = self.whnf(ctx, &a_type, depth + 1)?;
        if self.unit_type(&shape, depth + 1)? {
            let b_type = self.infer(ctx, &b, depth + 1)?;
            return self.convertible(ctx, &a_type, &b_type, depth + 1);
        }
        if !eta {
            return Ok(false);
        }
        // Compare at a shared Pi/Sigma/record type, including two neutral values.
        // Restricting this to explicit lambdas/pairs loses transitivity when
        // proof-irrelevant components compare equal through a reconstruction.
        let record = self.record_type(&shape, depth + 1)?;
        if !matches!(shape.as_ref(), Term::Pi(..) | Term::Sigma(..)) && record.is_none() {
            return Ok(false);
        }
        let b_type = self.infer(ctx, &b, depth + 1)?;
        if !self.convertible(ctx, &a_type, &b_type, depth + 1)? {
            return Ok(false);
        }
        match shape.as_ref() {
            Term::Pi(domain, _) => self.function_eta(ctx, domain, &a, &b, depth + 1),
            Term::Sigma(..) => self.pair_eta(ctx, &a, &b, depth + 1),
            _ => {
                let Some((name, _, _, family)) = record else {
                    return Ok(false);
                };
                for index in 0..family.constructors[0].fields.len() {
                    let left = term(Term::Project {
                        family: name.clone(),
                        index,
                        subject: a.clone(),
                    });
                    let right = term(Term::Project {
                        family: name.clone(),
                        index,
                        subject: b.clone(),
                    });
                    if !self.convertible(ctx, &left, &right, depth + 1)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }
    /// Recognize a fully applied, already weak-head-normalized datatype type.
    /// A zero-field constructor cannot carry a recursive field. Parameters
    /// and universe arguments are preserved by the subsequent type comparison.
    fn unit_type(&mut self, shape: &T, depth: usize) -> Result<bool> {
        let mut head = shape.clone();
        let mut supplied = 0;
        while let Term::App(function, _) = head.as_ref() {
            self.tick(depth)?;
            supplied += 1;
            head = function.clone();
        }
        let Term::Global(name, _) = head.as_ref() else {
            return Ok(false);
        };
        Ok(self
            .declarations
            .get(name)
            .and_then(|declaration| declaration.family.as_ref())
            .is_some_and(|family| {
                family.group.len() == 1
                    && family.parameters.len() == supplied
                    && family.indices.is_empty()
                    && family.constructors.len() == 1
                    && family.constructors[0].fields.is_empty()
            }))
    }
    fn function_eta(&mut self, ctx: &[T], domain: &T, a: &T, b: &T, depth: usize) -> Result<bool> {
        let mut inner = ctx.to_vec();
        inner.push(domain.clone());
        let argument = term(Term::Var(0));
        let a = term(Term::App(self.shift(a, 1, 0, depth + 1)?, argument.clone()));
        let b = term(Term::App(self.shift(b, 1, 0, depth + 1)?, argument));
        self.convertible(&inner, &a, &b, depth + 1)
    }
    fn pair_eta(&mut self, ctx: &[T], a: &T, b: &T, depth: usize) -> Result<bool> {
        Ok(self.convertible(
            ctx,
            &term(Term::First(a.clone())),
            &term(Term::First(b.clone())),
            depth + 1,
        )? && self.convertible(
            ctx,
            &term(Term::Second(a.clone())),
            &term(Term::Second(b.clone())),
            depth + 1,
        )?)
    }
    fn same_many(&mut self, ctx: &[T], a: &[T], b: &[T], depth: usize) -> Result<bool> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            if !self.convertible(ctx, a, b, depth + 1)? {
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
        // The argument and traversal depth are fixed for this substitution;
        // only the number of intervening binders changes its shifted form.
        // Keep reuse local so neither another argument nor a later declaration
        // can inherit the result, and charge the table before inserting.
        let mut shifted = HashMap::<usize, T>::new();
        self.transform(
            body,
            0,
            depth,
            &mut |kernel, index, binders| {
                if index == binders {
                    if let Some(value) = shifted.get(&binders) {
                        return Ok(value.clone());
                    }
                    let value = kernel.shift(arg, binders, 0, depth + 1)?;
                    kernel.charge_transformation(256)?;
                    shifted.insert(binders, value.clone());
                    Ok(value)
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
        self.transform_nodes(
            value,
            binders,
            depth,
            &mut |_, value, _, _| Ok(ControlFlow::Continue(value.clone())),
            var,
            level,
        )
    }
    fn transform_nodes(
        &mut self,
        value: &T,
        binders: usize,
        depth: usize,
        node: &mut impl FnMut(&mut Self, &T, usize, usize) -> Result<ControlFlow<T, T>>,
        var: &mut impl FnMut(&mut Self, usize, usize) -> Result<T>,
        level: &mut impl FnMut(&Level) -> Result<Level>,
    ) -> Result<T> {
        self.tick(depth)?;
        let value = match node(self, value, binders, depth)? {
            ControlFlow::Continue(value) => value,
            ControlFlow::Break(value) => {
                self.charge_transformation(128)?;
                return Ok(value);
            }
        };
        macro_rules! walk {
            ($t:expr) => {
                self.transform_nodes($t, binders, depth + 1, node, var, level)?
            };
        }
        macro_rules! many {
            ($ts:expr) => {
                $ts.iter()
                    .map(|t| self.transform_nodes(t, binders, depth + 1, node, var, level))
                    .collect::<Result<Vec<_>>>()?
            };
        }
        let transformed = match value.as_ref() {
            Term::Var(index) => {
                self.charge_transformation(128)?;
                return var(self, *index, binders);
            }
            Term::Sort(l) => Term::Sort(level(l)?),
            Term::NatLiteral { family, value } => Term::NatLiteral {
                family: family.clone(),
                value: value.clone(),
            },
            Term::Global(n, ls) => Term::Global(
                n.clone(),
                ls.iter().map(&mut *level).collect::<Result<_>>()?,
            ),
            Term::Pi(a, b) | Term::Lam(a, b) | Term::Sigma(a, b) => {
                let a = walk!(a);
                let b = self.transform_nodes(b, binders + 1, depth + 1, node, var, level)?;
                match value.as_ref() {
                    Term::Pi(..) => Term::Pi(a, b),
                    Term::Lam(..) => Term::Lam(a, b),
                    _ => Term::Sigma(a, b),
                }
            }
            Term::App(a, b) => Term::App(walk!(a), walk!(b)),
            Term::Let(ty, value, body) => Term::Let(
                walk!(ty),
                walk!(value),
                self.transform_nodes(body, binders + 1, depth + 1, node, var, level)?,
            ),
            Term::Pair(a, b, c) => Term::Pair(walk!(a), walk!(b), walk!(c)),
            Term::First(a) => Term::First(walk!(a)),
            Term::Second(a) => Term::Second(walk!(a)),
            Term::Project {
                family,
                index,
                subject,
            } => Term::Project {
                family: family.clone(),
                index: *index,
                subject: walk!(subject),
            },
            Term::Eq(a, b, c) => Term::Eq(walk!(a), walk!(b), walk!(c)),
            Term::Refl(a, b) => Term::Refl(walk!(a), walk!(b)),
            Term::QuotType(l, a, r) => Term::QuotType(level(l)?, walk!(a), walk!(r)),
            Term::QuotMake(l, a, r, v) => Term::QuotMake(level(l)?, walk!(a), walk!(r), walk!(v)),
            Term::QuotLift {
                source_level,
                target_level,
                ty,
                relation,
                target,
                function,
                respect,
                subject,
            } => Term::QuotLift {
                source_level: level(source_level)?,
                target_level: level(target_level)?,
                ty: walk!(ty),
                relation: walk!(relation),
                target: walk!(target),
                function: walk!(function),
                respect: walk!(respect),
                subject: walk!(subject),
            },
            Term::QuotInduct {
                level: l,
                ty,
                relation,
                motive,
                branch,
                subject,
            } => Term::QuotInduct {
                level: level(l)?,
                ty: walk!(ty),
                relation: walk!(relation),
                motive: walk!(motive),
                branch: walk!(branch),
                subject: walk!(subject),
            },
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
                indices,
                motive,
                branches,
                subject,
            } => Term::Induct {
                family: family.clone(),
                levels: levels.iter().map(&mut *level).collect::<Result<_>>()?,
                parameters: many!(parameters),
                indices: many!(indices),
                motive: walk!(motive),
                branches: many!(branches),
                subject: walk!(subject),
            },
            Term::SelfType => Term::SelfType,
            Term::SelfAt(indices) => Term::SelfAt(many!(indices)),
            Term::Recur(name, indices) => Term::Recur(name.clone(), many!(indices)),
            Term::MutualInduct {
                family,
                levels,
                parameters,
                indices,
                cases,
                subject,
            } => Term::MutualInduct {
                family: family.clone(),
                levels: levels.iter().map(&mut *level).collect::<Result<_>>()?,
                parameters: many!(parameters),
                indices: many!(indices),
                cases: cases
                    .iter()
                    .map(|case| {
                        Ok(RecursionCase {
                            family: case.family.clone(),
                            motive: self.transform_nodes(
                                &case.motive,
                                binders,
                                depth + 1,
                                node,
                                var,
                                level,
                            )?,
                            branches: case
                                .branches
                                .iter()
                                .map(|branch| {
                                    self.transform_nodes(
                                        branch,
                                        binders,
                                        depth + 1,
                                        node,
                                        var,
                                        level,
                                    )
                                })
                                .collect::<Result<_>>()?,
                        })
                    })
                    .collect::<Result<_>>()?,
                subject: walk!(subject),
            },
            Term::NestedInduct {
                family,
                levels,
                parameters,
                selected,
                indices,
                cases,
                subject,
            } => Term::NestedInduct {
                family: family.clone(),
                levels: levels.iter().map(&mut *level).collect::<Result<_>>()?,
                parameters: many!(parameters),
                selected: *selected,
                indices: many!(indices),
                cases: cases
                    .iter()
                    .map(|case| {
                        Ok(NestedCase {
                            selector: self.transform_nodes(
                                &case.selector,
                                binders,
                                depth + 1,
                                node,
                                var,
                                level,
                            )?,
                            motive: self.transform_nodes(
                                &case.motive,
                                binders,
                                depth + 1,
                                node,
                                var,
                                level,
                            )?,
                            branches: case
                                .branches
                                .iter()
                                .map(|branch| {
                                    self.transform_nodes(
                                        branch,
                                        binders,
                                        depth + 1,
                                        node,
                                        var,
                                        level,
                                    )
                                })
                                .collect::<Result<_>>()?,
                        })
                    })
                    .collect::<Result<_>>()?,
                subject: walk!(subject),
            },
        };
        let levels = match &transformed {
            Term::Sort(level) => level.memory_weight(),
            Term::QuotType(level, ..)
            | Term::QuotMake(level, ..)
            | Term::QuotInduct { level, .. } => level.memory_weight(),
            Term::QuotLift {
                source_level,
                target_level,
                ..
            } => source_level
                .memory_weight()
                .saturating_add(target_level.memory_weight()),
            Term::Global(_, levels)
            | Term::Ctor { levels, .. }
            | Term::Induct { levels, .. }
            | Term::MutualInduct { levels, .. }
            | Term::NestedInduct { levels, .. } => levels.iter().map(Level::memory_weight).sum(),
            _ => 0,
        };
        let name_bytes = match &transformed {
            Term::NatLiteral { family, value } => {
                family.len().saturating_add(value.decimal().len())
            }
            Term::Global(name, _) | Term::Recur(name, _) => name.len(),
            Term::Ctor {
                family,
                constructor,
                ..
            } => family.len().saturating_add(constructor.len()),
            Term::MutualInduct { family, cases, .. } => {
                cases.iter().fold(family.len(), |total, case| {
                    total.saturating_add(case.family.len())
                })
            }
            Term::Induct { family, .. }
            | Term::NestedInduct { family, .. }
            | Term::Project { family, .. } => family.len(),
            _ => 0,
        };
        self.charge_transformation(128usize.saturating_add(levels).saturating_add(name_bytes))?;
        Ok(term(transformed))
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
        Term::SelfType | Term::SelfAt(_) | Term::Recur(..) => true,
        Term::Global(global, _) if global == name => true,
        Term::NatLiteral { family, .. }
        | Term::Ctor { family, .. }
        | Term::Induct { family, .. }
        | Term::MutualInduct { family, .. }
        | Term::NestedInduct { family, .. }
        | Term::Project { family, .. }
            if family == name =>
        {
            true
        }
        Term::Pi(a, b)
        | Term::Lam(a, b)
        | Term::App(a, b)
        | Term::Sigma(a, b)
        | Term::Refl(a, b) => contains_recursive(a, name) || contains_recursive(b, name),
        Term::Pair(a, b, c) | Term::Eq(a, b, c) | Term::Let(a, b, c) => {
            contains_recursive(a, name)
                || contains_recursive(b, name)
                || contains_recursive(c, name)
        }
        Term::First(a) | Term::Second(a) | Term::Project { subject: a, .. } => {
            contains_recursive(a, name)
        }
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
        Term::QuotType(_, ty, relation) => {
            [ty, relation].iter().any(|t| contains_recursive(t, name))
        }
        Term::QuotMake(_, ty, relation, value) => [ty, relation, value]
            .iter()
            .any(|t| contains_recursive(t, name)),
        Term::QuotLift {
            ty,
            relation,
            target,
            function,
            respect,
            subject,
            ..
        } => [ty, relation, target, function, respect, subject]
            .iter()
            .any(|t| contains_recursive(t, name)),
        Term::QuotInduct {
            ty,
            relation,
            motive,
            branch,
            subject,
            ..
        } => [ty, relation, motive, branch, subject]
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
            indices,
            motive,
            branches,
            subject,
            ..
        } => parameters
            .iter()
            .chain(indices)
            .chain(branches)
            .chain([motive, subject])
            .any(|t| contains_recursive(t, name)),
        Term::MutualInduct {
            parameters,
            indices,
            cases,
            subject,
            ..
        } => {
            parameters
                .iter()
                .chain(indices)
                .chain(std::iter::once(subject))
                .any(|t| contains_recursive(t, name))
                || cases.iter().any(|case| {
                    case.family == name
                        || contains_recursive(&case.motive, name)
                        || case.branches.iter().any(|t| contains_recursive(t, name))
                })
        }
        Term::NestedInduct {
            parameters,
            indices,
            cases,
            subject,
            ..
        } => {
            parameters
                .iter()
                .chain(indices)
                .chain(std::iter::once(subject))
                .any(|t| contains_recursive(t, name))
                || cases.iter().any(|case| {
                    contains_recursive(&case.selector, name)
                        || contains_recursive(&case.motive, name)
                        || case.branches.iter().any(|t| contains_recursive(t, name))
                })
        }
        _ => false,
    }
}

#[cfg(test)]
#[path = "core_tests.rs"]
mod core_tests;
