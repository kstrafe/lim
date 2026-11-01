//! Atomic inductive group installation and uniform strict positivity.
use super::*;

impl Kernel {
    pub fn mutual_inductive(
        &mut self,
        inputs: Vec<InductiveInput>,
    ) -> std::result::Result<(), (String, String)> {
        let mut failing = inputs
            .first()
            .map(|input| input.name.clone())
            .unwrap_or_default();
        if !(2..=16).contains(&inputs.len()) {
            return Err((
                failing,
                "mutual inductives require between 2 and 16 families".into(),
            ));
        }
        self.check_group(inputs, &mut failing)
            .map_err(|why| (failing, why))
    }

    pub(super) fn declare_group(&mut self, inputs: Vec<InductiveInput>) -> Result<()> {
        self.check_group(inputs, &mut String::new())
    }

    fn check_group(&mut self, inputs: Vec<InductiveInput>, failing: &mut String) -> Result<()> {
        let first = inputs.first().ok_or("empty inductive group")?;
        let names = inputs
            .iter()
            .map(|input| input.name.clone())
            .collect::<Vec<_>>();
        let unique = names.iter().collect::<std::collections::HashSet<_>>();
        if unique.len() != names.len() || names.iter().any(|name| self.contains(name)) {
            return Err("duplicate kernel declaration in inductive group".into());
        }
        let universes = first.universes.clone();
        let sort = first.sort.clone();
        let parameters = first.parameters.clone();
        // All headers are checked before any provisional family is visible.
        // A group's parameters/indices cannot depend on a member being defined.
        for input in &inputs {
            *failing = input.name.clone();
            if input.universes != universes
                || !input.sort.equivalent(&sort)?
                || input.parameters.len() != parameters.len()
            {
                return Err(
                    "mutual families must share universe parameters, uniform parameters, and sort"
                        .into(),
                );
            }
            let mut scoped = input.parameters.clone();
            scoped.extend(input.indices.iter().cloned());
            scoped.push(term(Term::Sort(input.sort.clone())));
            for (_, fields, results) in &input.constructors {
                scoped.extend(fields.iter().cloned());
                scoped.extend(results.iter().cloned());
            }
            self.scope(&universes, &scoped)?;
            if input
                .parameters
                .iter()
                .chain(&input.indices)
                .any(|ty| contains_group(ty, &names))
            {
                return Err("inductive group occurrences in parameter or index types violate strict positivity".into());
            }
            let mut context = vec![];
            for (expected, actual) in parameters.iter().zip(&input.parameters) {
                self.sort(&context, actual, 0)?;
                if !self.convertible(&context, expected, actual, 0)? {
                    return Err(
                        "mutual families must have the same uniform parameter telescope".into(),
                    );
                }
                context.push(actual.clone());
            }
            for index in &input.indices {
                self.sort(&context, index, 0)?;
                context.push(index.clone());
            }
        }
        for input in &inputs {
            self.declarations.insert(
                input.name.clone(),
                Declaration {
                    universes: universes.clone(),
                    ty: pis(
                        &parameters,
                        pis(&input.indices, term(Term::Sort(sort.clone()))),
                    ),
                    value: None,
                    family: Some(Family {
                        group: names.clone(),
                        parameters: parameters.clone(),
                        indices: input.indices.clone(),
                        sort: sort.clone(),
                        constructors: vec![],
                        // Mutual predicates eliminate only to Prop; a positive
                        // specialization can still eliminate to data by its guard.
                        large: names.len() == 1 && input.constructors.len() <= 1,
                    }),
                },
            );
        }
        let levels = universes
            .iter()
            .map(|u| Level::variable(u.clone()))
            .collect::<Vec<_>>();
        self.nested_build = Some(NestedBuild {
            roots: names.clone(),
            universes: universes.clone(),
            parameters: parameters.clone(),
            sort: sort.clone(),
            aliases: vec![],
            pending: vec![],
        });
        let mut queue = std::collections::VecDeque::from(inputs);
        let mut outcome = (|| {
            while let Some(input) = queue.pop_front() {
                *failing = input.name.clone();
                let name = &input.name;
                let (mut family, _) = self.family(name, &levels, 0)?;
                let mut labels = std::collections::HashSet::new();
                for (constructor, fields, result_indices) in input.constructors {
                    if !labels.insert(constructor.clone()) {
                        return Err("duplicate inductive constructor".into());
                    }
                    let mut ctx = parameters.clone();
                    let mut checked = vec![];
                    let mut recursive = vec![];
                    let mut field_sorts = vec![];
                    for field in fields {
                        let params = (0..parameters.len())
                            .map(|i| term(Term::Var(checked.len() + parameters.len() - 1 - i)))
                            .collect::<Vec<_>>();
                        let (field, target) = self
                            .prepare_group_field(&ctx, name, &names, &levels, &params, &field, 0)?;
                        let field_sort = self.sort(&ctx, &field, 0)?;
                        if !field_sort.imax(&sort)?.at_most(&sort)? {
                            return Err("inductive field exceeds the datatype's universe".into());
                        }
                        field_sorts.push(field_sort);
                        ctx.push(field.clone());
                        checked.push(field);
                        recursive.push(target);
                    }
                    if result_indices.len() != family.indices.len() {
                        return Err(
                            "constructor result index count does not match the family".into()
                        );
                    }
                    if result_indices
                        .iter()
                        .any(|index| contains_group(index, &names))
                    {
                        return Err("recursive occurrences in constructor result indices violate strict positivity".into());
                    }
                    let params = (0..parameters.len())
                        .map(|i| term(Term::Var(checked.len() + parameters.len() - 1 - i)))
                        .collect::<Vec<_>>();
                    let result =
                        self.family_application(name, &levels, &params, &result_indices, 0)?;
                    self.sort(&ctx, &result, 0)?;
                    for (position, field_sort) in field_sorts.iter().enumerate() {
                        let field_index = checked.len() - 1 - position;
                        let exposed = result_indices.iter().any(|index| matches!(index.as_ref(), Term::Var(found) if *found == field_index));
                        family.large &= exposed || sort.zero_implies_zero(field_sort)?;
                    }
                    family.constructors.push(Constructor {
                        name: constructor,
                        fields: checked,
                        recursive,
                        result_indices,
                    });
                }
                self.declarations
                    .get_mut(name)
                    .or_else(|| self.nested.get_mut(name).map(|view| &mut view.declaration))
                    .ok_or("missing provisional inductive family")?
                    .family = Some(family);
                queue.extend(
                    self.nested_build
                        .as_mut()
                        .ok_or("missing nested build")?
                        .pending
                        .drain(..),
                );
            }
            Ok(())
        })();
        let build = self.nested_build.take().ok_or("missing nested build")?;
        if outcome.is_ok() {
            let group = names
                .iter()
                .chain(&build.aliases)
                .cloned()
                .collect::<Vec<_>>();
            outcome = (|| {
                for name in &group {
                    let declaration = self
                        .declarations
                        .get_mut(name)
                        .or_else(|| self.nested.get_mut(name).map(|view| &mut view.declaration))
                        .ok_or("missing checked group family")?;
                    let family = declaration
                        .family
                        .as_mut()
                        .ok_or("missing checked group descriptor")?;
                    family.group = group.clone();
                    if group.len() > 1 {
                        family.large = false;
                    }
                }
                Ok(())
            })();
        }
        if outcome.is_err() {
            for name in &names {
                self.declarations.remove(name);
            }
            for name in build.aliases {
                self.nested.remove(&name);
            }
        }
        outcome
    }

    #[expect(clippy::too_many_arguments)]
    fn prepare_group_field(
        &mut self,
        ctx: &[T],
        current: &str,
        group: &[String],
        levels: &[Level],
        parameters: &[T],
        field: &T,
        depth: usize,
    ) -> Result<(T, Option<String>)> {
        self.tick(depth)?;
        if !contains_group(field, group) {
            return Ok((field.clone(), None));
        }
        match field.as_ref() {
            Term::Pi(domain, body) => {
                if contains_group(domain, group) {
                    return Err("recursive occurrences in function domains violate strict positivity".into());
                }
                self.sort(ctx, domain, depth + 1)?;
                let mut inner = ctx.to_vec(); inner.push(domain.clone());
                let parameters = self.shift_many(parameters, 1, depth + 1)?;
                let (body, target) = self.prepare_group_field(&inner, current, group, levels, &parameters, body, depth + 1)?;
                Ok((term(Term::Pi(domain.clone(), body)), target))
            }
            Term::Let(ty, value, body) => {
                if contains_group(ty, group) || contains_group(value, group) {
                    return Err("recursive occurrences in let definitions violate strict positivity".into());
                }
                self.sort(ctx, ty, depth + 1)?;
                self.check(ctx, value, ty, depth + 1)?;
                let body = self.instantiate(body, value, depth + 1)?;
                self.prepare_group_field(ctx, current, group, levels, parameters, &body, depth + 1)
            }
            Term::SelfType | Term::SelfAt(_) | Term::Recur(_, _) => {
                let (target, indices) = match field.as_ref() {
                    Term::SelfType => (current, vec![]),
                    Term::SelfAt(indices) => (current, indices.clone()),
                    Term::Recur(target, indices) => (target.as_str(), indices.clone()),
                    _ => unreachable!(),
                };
                if !group.iter().any(|name| name == target) {
                    return Err("#pt-recur must select a member of the current inductive group".into());
                }
                let (family, _) = self.family(target, levels, depth + 1)?;
                if matches!(field.as_ref(), Term::SelfType) && !family.indices.is_empty() {
                    return Err("indexed recursive fields require #pt-self-at with explicit indices".into());
                }
                if matches!(field.as_ref(), Term::SelfAt(_)) && family.indices.is_empty() {
                    return Err("#pt-self-at index count does not match the indexed family".into());
                }
                if indices.len() != family.indices.len() {
                    return Err("recursive marker index count does not match the indexed family; use #pt-self-at or #pt-recur with explicit indices".into());
                }
                if indices.iter().any(|index| contains_group(index, group)) {
                    return Err("recursive occurrences in an index violate strict positivity".into());
                }
                let result = apps(apps(term(Term::Global(target.into(), levels.to_vec())), parameters), &indices);
                Ok((result, Some(target.into())))
            }
            // An elaborated importer can retain an explicit fully applied
            // sibling family. Validate every argument before accepting it.
            Term::Global(..) | Term::App(..) => {
                let mut head = field.clone(); let mut arguments = vec![];
                while let Term::App(function, argument) = head.as_ref() { self.tick(depth)?; arguments.push(argument.clone()); head = function.clone(); }
                arguments.reverse();
                if let Term::Global(target, actual_levels) = head.as_ref() {
                    if group.iter().any(|name| name == target) {
                        if !same_levels(levels, actual_levels)? || arguments.len() < parameters.len() {
                            return Err("recursive inductive parameters and universes must remain uniform".into());
                        }
                        if arguments.iter().any(|arg| contains_group(arg, group)) {
                            return Err("recursive occurrences in family arguments violate strict positivity".into());
                        }
                        // Enforce uniform shape, then check the complete
                        // application, including unused arguments, before
                        // accepting the recursive field.
                        self.family_indices(ctx, target, levels, parameters, field, depth + 1)?;
                        self.sort(ctx, field, depth + 1)?;
                        return Ok((field.clone(), Some(target.clone())));
                    }
                    if self.nested_replay && self.declarations.get(target).is_some_and(|decl|decl.family.is_some()) {
                        // Parameter specialization is checked before it can
                        // define an auxiliary view; positivity is then checked
                        // on every specialized constructor field in the queue.
                        self.sort(ctx,field,depth+1)?;
                        let target=self.nested_field(ctx,target,actual_levels,&arguments,depth+1)?;
                        return Ok((field.clone(),Some(target)));
                    }
                }
                Err("recursive fields must end in a group family through strictly positive Pi codomains (strict positivity)".into())
            }
            _ => Err("recursive fields must end in #pt-self, #pt-self-at or #pt-recur through strictly positive Pi codomains (strict positivity)".into()),
        }
    }
}

fn contains_group(term: &T, names: &[String]) -> bool {
    names.iter().any(|name| contains_recursive(term, name))
}
