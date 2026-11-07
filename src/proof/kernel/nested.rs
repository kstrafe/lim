//! Nested recursion views are derived from already checked container signatures.
//! They are scoped eliminator cases, never new global constants or constructors.
use super::*;

#[derive(Clone)]
pub(super) struct NestedFamily {
    pub declaration: Declaration,
    pub(super) source: String,
    pub(super) levels: Vec<Level>,
    pub(super) arguments: Vec<T>,
}
pub(super) struct NestedBuild {
    pub roots: Vec<String>,
    pub universes: Vec<String>,
    pub parameters: Vec<T>,
    pub sort: Level,
    pub aliases: Vec<String>,
    pub pending: Vec<InductiveInput>,
}

impl Kernel {
    /// Resolve explicit physical type selectors to this declaration's scoped
    /// cases. Selectors are checked before conversion can erase any subterm.
    pub(super) fn nested_cases(
        &mut self,
        ctx: &[T],
        name: &str,
        levels: &[Level],
        parameters: &[T],
        cases: &[NestedCase],
        depth: usize,
    ) -> Result<Vec<RecursionCase>> {
        self.tick(depth)?;
        if self.provisional_family(name) {
            return Err("cannot eliminate a provisional inductive family".into());
        }
        let (family, _) = self.family(name, levels, depth + 1)?;
        if self.nested.contains_key(name)? || !self.nested.any(&family.group)? {
            return Err("#pt-nested-induct requires a family with nested recursion cases".into());
        }
        if cases.len() != family.group.len() {
            return Err(
                "nested induction cases must cover every root and container in derivation order"
                    .into(),
            );
        }
        cases.iter().zip(&family.group).map(|(case, key)| {
            self.infer(ctx, &case.selector, depth + 1)?;
            let expected = self.family_application(key, levels, parameters, &[], depth + 1)?;
            if !self.convertible(ctx, &case.selector, &expected, depth + 1)? {
                return Err("nested induction selector must name the partially applied family type in derivation order".into());
            }
            Ok(RecursionCase {
                family: key.clone(),
                motive: case.motive.clone(),
                branches: case.branches.clone(),
            })
        }).collect()
    }
    pub(super) fn provisional_family(&self, name: &str) -> bool {
        self.nested_build.as_ref().is_some_and(|build| {
            build
                .roots
                .iter()
                .chain(&build.aliases)
                .any(|member| member == name)
        })
    }

    fn uniform_nested_arguments(&mut self, ctx: &[T], arguments: &[T], depth: usize) -> Result<()> {
        let build = self.nested_build.as_ref().ok_or("missing nested build")?;
        let roots = build.roots.clone();
        let count = build.parameters.len();
        let levels = build
            .universes
            .iter()
            .cloned()
            .map(Level::variable)
            .collect::<Vec<_>>();
        let mut pending = arguments
            .iter()
            .cloned()
            .map(|value| (value, 0usize))
            .collect::<Vec<_>>();
        let mut seen = std::collections::HashSet::new();
        while let Some((value, binders)) = pending.pop() {
            if !seen.insert((Arc::as_ptr(&value) as usize, binders)) {
                continue;
            }
            self.tick(depth + binders)?;
            let (head, args) = application(&value);
            if let Term::Global(name, actual) = head.as_ref() {
                if roots.contains(name) {
                    if !same_levels(&levels, actual)? || args.len() < count {
                        return Err(
                            "nested recursive parameters and universes must remain uniform".into(),
                        );
                    }
                    for (position, arg) in args[..count].iter().enumerate() {
                        let index = ctx
                            .len()
                            .checked_add(binders)
                            .and_then(|size| size.checked_sub(position + 1))
                            .ok_or("invalid nested uniform parameter context")?;
                        if !matches!(arg.as_ref(),Term::Var(actual) if *actual==index) {
                            return Err("nested recursive parameters must remain uniform".into());
                        }
                    }
                    if args
                        .iter()
                        .any(|arg| roots.iter().any(|name| contains_recursive(arg, name)))
                    {
                        return Err("recursive occurrences in nested family arguments violate strict positivity".into());
                    }
                    continue;
                }
            }
            match value.as_ref() {
                Term::QuotType(_, a, r) => {
                    pending.extend([a.clone(), r.clone()].into_iter().map(|v| (v, binders)))
                }
                Term::QuotMake(_, a, r, x) => pending.extend(
                    [a.clone(), r.clone(), x.clone()]
                        .into_iter()
                        .map(|v| (v, binders)),
                ),
                Term::QuotLift {
                    ty,
                    relation,
                    target,
                    function,
                    respect,
                    subject,
                    ..
                } => pending.extend(
                    [ty, relation, target, function, respect, subject]
                        .into_iter()
                        .cloned()
                        .map(|v| (v, binders)),
                ),
                Term::QuotInduct {
                    ty,
                    relation,
                    motive,
                    branch,
                    subject,
                    ..
                } => pending.extend(
                    [ty, relation, motive, branch, subject]
                        .into_iter()
                        .cloned()
                        .map(|v| (v, binders)),
                ),
                Term::Pi(a, b) | Term::Lam(a, b) | Term::Sigma(a, b) => {
                    pending.push((a.clone(), binders));
                    pending.push((b.clone(), binders + 1));
                }
                Term::Let(a, b, c) => {
                    pending.extend([
                        (a.clone(), binders),
                        (b.clone(), binders),
                        (c.clone(), binders + 1),
                    ]);
                }
                Term::App(a, b) | Term::Refl(a, b) => {
                    pending.extend([(a.clone(), binders), (b.clone(), binders)])
                }
                Term::Pair(a, b, c) | Term::Eq(a, b, c) => pending.extend([
                    (a.clone(), binders),
                    (b.clone(), binders),
                    (c.clone(), binders),
                ]),
                Term::First(a) | Term::Second(a) | Term::Project { subject: a, .. } => {
                    pending.push((a.clone(), binders))
                }
                Term::Ctor {
                    parameters, fields, ..
                } => pending.extend(
                    parameters
                        .iter()
                        .chain(fields)
                        .cloned()
                        .map(|v| (v, binders)),
                ),
                Term::Induct {
                    parameters,
                    indices,
                    motive,
                    branches,
                    subject,
                    ..
                } => pending.extend(
                    parameters
                        .iter()
                        .chain(indices)
                        .chain(branches)
                        .chain([motive, subject])
                        .cloned()
                        .map(|v| (v, binders)),
                ),
                Term::MutualInduct {
                    parameters,
                    indices,
                    cases,
                    subject,
                    ..
                } => {
                    pending.extend(
                        parameters
                            .iter()
                            .chain(indices)
                            .chain([subject])
                            .cloned()
                            .map(|v| (v, binders)),
                    );
                    for case in cases {
                        pending.push((case.motive.clone(), binders));
                        pending.extend(case.branches.iter().cloned().map(|v| (v, binders)));
                    }
                }
                Term::NestedInduct {
                    parameters,
                    indices,
                    cases,
                    subject,
                    ..
                } => {
                    pending.extend(
                        parameters
                            .iter()
                            .chain(indices)
                            .chain([subject])
                            .cloned()
                            .map(|v| (v, binders)),
                    );
                    for case in cases {
                        pending.extend(
                            [case.selector.clone(), case.motive.clone()]
                                .into_iter()
                                .chain(case.branches.iter().cloned())
                                .map(|v| (v, binders)),
                        );
                    }
                }
                Term::EqElim {
                    ty,
                    left,
                    motive,
                    base,
                    right,
                    proof,
                } => pending.extend(
                    [ty, left, motive, base, right, proof]
                        .into_iter()
                        .cloned()
                        .map(|v| (v, binders)),
                ),
                Term::SelfType | Term::SelfAt(_) | Term::Recur(..) => {
                    return Err("unexpanded marker in nested parameter specialization".into())
                }
                Term::NatLiteral { .. } | Term::Global(..) | Term::Sort(_) | Term::Var(_) => {}
            }
        }
        Ok(())
    }

    fn template(
        &mut self,
        value: &T,
        parameters: &[T],
        map: &HashMap<String, Level>,
        depth: usize,
    ) -> Result<T> {
        self.transform(
            value,
            0,
            depth,
            &mut |kernel, index, binders| {
                if index < binders {
                    return Ok(term(Term::Var(index)));
                }
                let parameter = index - binders;
                let position = parameters
                    .len()
                    .checked_sub(
                        parameter
                            .checked_add(1)
                            .ok_or("nested variable index overflow")?,
                    )
                    .ok_or("unbound variable in nested specialization")?;
                kernel.shift(&parameters[position], binders, 0, depth + 1)
            },
            &mut |level| level.substitute(map),
        )
    }

    pub(super) fn family_application(
        &mut self,
        name: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        depth: usize,
    ) -> Result<T> {
        self.tick(depth)?;
        if let Some(view) = self.nested.get(name)? {
            if parameters.len()
                != view
                    .declaration
                    .family
                    .as_ref()
                    .ok_or("missing nested signature")?
                    .parameters
                    .len()
            {
                return Err("nested family parameter count mismatch".into());
            }
            let (_, map) = self.specialization(name, levels, depth + 1)?;
            let arguments = view
                .arguments
                .iter()
                .map(|arg| self.template(arg, parameters, &map, depth + 1))
                .collect::<Result<Vec<_>>>()?;
            let levels = view
                .levels
                .iter()
                .map(|level| level.substitute(&map))
                .collect::<Result<Vec<_>>>()?;
            return Ok(apps(
                apps(term(Term::Global(view.source, levels)), &arguments),
                indices,
            ));
        }
        Ok(apps(
            apps(term(Term::Global(name.into(), levels.to_vec())), parameters),
            indices,
        ))
    }

    pub(super) fn family_constructor(
        &mut self,
        name: &str,
        levels: &[Level],
        parameters: &[T],
        constructor: &str,
        fields: Vec<T>,
        depth: usize,
    ) -> Result<T> {
        let value = self.family_application(name, levels, parameters, &[], depth + 1)?;
        let (head, parameters) = application(&value);
        let Term::Global(family, levels) = head.as_ref() else {
            return Err("invalid nested constructor origin".into());
        };
        Ok(term(Term::Ctor {
            family: family.clone(),
            levels: levels.clone(),
            parameters,
            constructor: constructor.into(),
            fields,
        }))
    }

    pub(super) fn nested_field(
        &mut self,
        ctx: &[T],
        source: &str,
        levels: &[Level],
        arguments: &[T],
        depth: usize,
    ) -> Result<String> {
        let (family, _) = self.family(source, levels, depth + 1)?;
        if arguments.len() != family.parameters.len() + family.indices.len() {
            return Err("nested family must be fully applied".into());
        }
        let roots = self
            .nested_build
            .as_ref()
            .ok_or("missing nested build")?
            .roots
            .clone();
        if arguments[family.parameters.len()..]
            .iter()
            .any(|index| roots.iter().any(|root| contains_recursive(index, root)))
        {
            return Err("recursive occurrences in nested indices violate strict positivity".into());
        }
        self.uniform_nested_arguments(ctx, &arguments[..family.parameters.len()], depth + 1)?;
        let build = self
            .nested_build
            .as_ref()
            .ok_or("nested specialization outside an inductive group")?;
        let extra = ctx
            .len()
            .checked_sub(build.parameters.len())
            .ok_or("invalid nested parameter context")?;
        let parameters = arguments[..family.parameters.len()].iter().map(|value| {
            self.transform(value, 0, depth + 1, &mut |_, index, binders| {
                if index < binders { return Ok(term(Term::Var(index))); }
                if index - binders < extra { return Err("nested inductive parameters cannot capture constructor-local variables".into()); }
                Ok(term(Term::Var(index-extra)))
            }, &mut |level|Ok(level.clone()))
        }).collect::<Result<Vec<_>>>()?;
        self.nested_instance(source, levels, &parameters, depth + 1)
    }

    fn nested_instance(
        &mut self,
        source: &str,
        levels: &[Level],
        arguments: &[T],
        depth: usize,
    ) -> Result<String> {
        self.tick(depth)?;
        // Canonicalize an older scoped view back to its real container. This
        // keeps repeated and nested specializations finite and nominal.
        let spelled = self.family_application(source, levels, arguments, &[], depth + 1)?;
        let (head, arguments) = application(&spelled);
        let Term::Global(source, levels) = head.as_ref() else {
            return Err("nested specialization requires a checked inductive container".into());
        };
        let build = self.nested_build.as_ref().ok_or("missing nested build")?;
        let aliases = build.aliases.clone();
        let roots = build.roots.clone();
        let universes = build.universes.clone();
        let parameters = build.parameters.clone();
        let sort = build.sort.clone();
        if let Some(alias) = self.cached_nested(source, levels, &arguments)? {
            return Ok(alias);
        }
        if roots.len() + aliases.len() >= 16 {
            return Err("expanded nested inductive group limit exceeded".into());
        }
        if roots.contains(source) {
            return Err("nested specialization cannot change recursive family parameters".into());
        }
        let (original, map) = self.specialization(source, levels, depth + 1)?;
        let family = original
            .family
            .as_ref()
            .ok_or("nested parameters require an already checked inductive container")?
            .clone();
        if arguments.len() != family.parameters.len() {
            return Err("nested parameter specialization arity mismatch".into());
        }
        if let Some(first) = self.nested.roots(&family.group)?.first() {
            if first != source {
                self.nested_instance(first, levels, &arguments, depth + 1)?;
                if let Some(alias) = self.cached_nested(source, levels, &arguments)? {
                    return Ok(alias);
                }
            }
        }
        if !family.sort.substitute(&map)?.equivalent(&sort)? {
            return Err("nested families must share the declaring group's universe sort".into());
        }
        let mut header = self.universes(&original.ty, &map, depth + 1)?;
        for argument in &arguments {
            let shape = self.whnf(&parameters, &header, depth + 1)?;
            let Term::Pi(domain, body) = shape.as_ref() else {
                return Err("invalid nested container parameter telescope".into());
            };
            self.check(&parameters, argument, domain, depth + 1)?;
            header = self.instantiate(body, argument, depth + 1)?;
        }
        let mut context = parameters.clone();
        let mut rest = header.clone();
        let mut indices = vec![];
        for _ in &family.indices {
            let shape = self.whnf(&context, &rest, depth + 1)?;
            let Term::Pi(domain, body) = shape.as_ref() else {
                return Err("invalid nested index telescope".into());
            };
            if roots.iter().any(|root| contains_recursive(domain, root)) {
                return Err(
                    "nested index types cannot depend on the declaring inductive group".into(),
                );
            }
            self.sort(&context, domain, depth + 1)?;
            context.push(domain.clone());
            indices.push(domain.clone());
            rest = body.clone();
        }
        let range = self.whnf(&context, &rest, depth + 1)?;
        if !matches!(range.as_ref(),Term::Sort(level) if level == &sort) {
            return Err("nested header must end in the shared sort".into());
        }
        let key = format!(
            "$nested:{}:{}:{}",
            roots[0].len(),
            roots[0],
            aliases.len() + 1
        );
        if self.contains(&key)? {
            return Err("nested auxiliary identity collision".into());
        }
        self.nested.insert(
            key.clone(),
            NestedFamily {
                source: source.clone(),
                levels: levels.clone(),
                arguments: arguments.clone(),
                declaration: Declaration {
                    universes: universes.clone(),
                    ty: pis(&parameters, header),
                    value: None,
                    family: Some(Family {
                        group: roots.clone(),
                        parameters: parameters.clone(),
                        indices: indices.clone(),
                        sort: sort.clone(),
                        constructors: vec![],
                        large: false,
                    }),
                },
            },
        )?;
        self.nested_build
            .as_mut()
            .ok_or("missing nested build")?
            .aliases
            .push(key.clone());
        let mut constructors = vec![];
        for constructor in &family.constructors {
            let (mut telescope, _) =
                self.constructor_type(source, levels, &constructor.name, depth + 1)?;
            for argument in &arguments {
                let shape = self.whnf(&parameters, &telescope, depth + 1)?;
                let Term::Pi(_, body) = shape.as_ref() else {
                    return Err("invalid nested constructor parameter telescope".into());
                };
                telescope = self.instantiate(body, argument, depth + 1)?;
            }
            // Check the complete specialization before peeling it. Unused
            // ill-typed parameters and wrappers cannot disappear here.
            self.sort(&parameters, &telescope, depth + 1)?;
            let mut context = parameters.clone();
            let mut fields = vec![];
            for _ in &constructor.fields {
                let shape = self.whnf(&context, &telescope, depth + 1)?;
                let Term::Pi(domain, body) = shape.as_ref() else {
                    return Err("invalid nested constructor field telescope".into());
                };
                let normalized = self.whnf(&context, domain, depth + 1)?;
                context.push(normalized.clone());
                fields.push(normalized);
                telescope = body.clone();
            }
            let arguments = self.shift_many(&arguments, fields.len(), depth + 1)?;
            let results =
                self.family_indices(&context, source, levels, &arguments, &telescope, depth + 1)?;
            constructors.push((constructor.name.clone(), fields, results));
        }
        self.nested_build
            .as_mut()
            .ok_or("missing nested build")?
            .pending
            .push(InductiveInput {
                name: key.clone(),
                universes,
                parameters,
                indices,
                sort,
                constructors,
            });
        // A checked source mutual group is specialized together, including
        // siblings not reached by a particular constructor field.
        for member in &family.group {
            // Old auxiliary cases are rediscovered from their physical field
            // types when their owning constructor is processed. Copying them
            // here would change Lean's breadth-first auxiliary numbering.
            if member != source && !self.nested.contains_key(member)? {
                self.nested_instance(member, levels, &arguments, depth + 1)?;
            }
        }
        Ok(key)
    }

    fn cached_nested(
        &mut self,
        source: &str,
        levels: &[Level],
        arguments: &[T],
    ) -> Result<Option<String>> {
        let aliases = self
            .nested_build
            .as_ref()
            .ok_or("missing nested build")?
            .aliases
            .clone();
        for alias in aliases {
            let view = self.nested.get(&alias)?.ok_or("missing nested view")?;
            if view.source != source
                || view.levels != levels
                || view.arguments.len() != arguments.len()
            {
                continue;
            }
            let mut same = true;
            for (left, right) in view.arguments.iter().zip(arguments) {
                if !self.same_syntax(left, right)? {
                    same = false;
                    break;
                }
            }
            if same {
                return Ok(Some(alias));
            }
        }
        Ok(None)
    }
}

pub(super) fn application(value: &T) -> (T, Vec<T>) {
    let mut head = value.clone();
    let mut arguments = vec![];
    while let Term::App(function, argument) = head.as_ref() {
        arguments.push(argument.clone());
        head = function.clone();
    }
    arguments.reverse();
    (head, arguments)
}

#[cfg(test)]
#[path = "nested_tests.rs"]
mod tests;
