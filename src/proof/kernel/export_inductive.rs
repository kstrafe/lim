//! Reconstruct inductives and recursors from checked constructor types.
//! Exported recursor types, flags and reduction rules cannot install rules.
use super::*;

#[derive(Clone)]
struct TypeSpec {
    name: Name,
    universes: Vec<String>,
    ty: T,
    parameters: usize,
    indices: usize,
    constructors: Vec<Name>,
    domains: Vec<T>,
    sort: Level,
    nested: usize,
}
struct ConstructorSpec {
    name: Name,
    family: String,
    universes: Vec<String>,
    ty: T,
    domains: Vec<T>,
    indices: Vec<T>,
}
struct RecursorSpec {
    name: Name,
    family: String,
    universes: Vec<String>,
    ty: T,
    rules: Vec<(String, usize, T)>,
}

impl Replay {
    pub(super) fn inductive(&mut self, body: &Json) -> Result<()> {
        let data = fields(body, &["types", "ctors", "recs"])?;
        let type_values = array(&data["types"], 16)?;
        if type_values.is_empty() {
            return Err("an inductive block must contain a family".into());
        }
        let mut types = vec![];
        for value in type_values {
            let value = fields(
                value,
                &[
                    "name",
                    "levelParams",
                    "type",
                    "numParams",
                    "numIndices",
                    "all",
                    "ctors",
                    "numNested",
                    "isRec",
                    "isUnsafe",
                    "isReflexive",
                ],
            )?;
            if boolean(&value["isUnsafe"])? {
                return Err("unsafe inductives are forbidden".into());
            }
            boolean(&value["isRec"])?;
            boolean(&value["isReflexive"])?;
            let nested = index(&value["numNested"])?;
            if nested > 16 {
                return Err("nested inductive count limit exceeded".into());
            }
            let name = self.name(&value["name"])?;
            let universes = self.universes(&value["levelParams"])?;
            let ty = self.expression(&value["type"])?;
            let parameters = index(&value["numParams"])?;
            let indices = index(&value["numIndices"])?;
            if parameters > 64 || indices > 64 {
                return Err("inductive parameter/index limit exceeded".into());
            }
            let dependencies = dependencies(std::slice::from_ref(&ty))?;
            self.dependencies_known(&dependencies, &[])?;
            self.reset_budget()?;
            self.kernel.scope(&universes, std::slice::from_ref(&ty))?;
            self.kernel.sort(&[], &ty, 0)?;
            let (domains, range) = self.peel(&ty, parameters + indices, &[])?;
            let range = self.kernel.whnf(&domains, &range, 0)?;
            let Term::Sort(sort) = range.as_ref() else {
                return Err("inductive header must end in a fixed Sort".into());
            };
            let members = self.name_list(&value["all"], 16)?;
            types.push((
                TypeSpec {
                    name,
                    universes,
                    ty,
                    parameters,
                    indices,
                    constructors: self.name_list(&value["ctors"], 64)?,
                    domains,
                    sort: sort.clone(),
                    nested,
                },
                members,
            ));
        }
        let group = types
            .iter()
            .map(|(spec, _)| spec.name.key.clone())
            .collect::<Vec<_>>();
        if group.iter().collect::<HashSet<_>>().len() != group.len() {
            return Err("duplicate inductive family in export block".into());
        }
        for (_, members) in &types {
            if members.iter().map(|n| &n.key).ne(group.iter()) {
                return Err("inductive block membership must match its ordered family list".into());
            }
        }
        let types = types.into_iter().map(|(spec, _)| spec).collect::<Vec<_>>();
        let mut constructors = vec![];
        let ctor_values = array(&data["ctors"], 16 * 64)?;
        for value in ctor_values {
            let value = fields(
                value,
                &[
                    "name",
                    "levelParams",
                    "type",
                    "induct",
                    "cidx",
                    "numParams",
                    "numFields",
                    "isUnsafe",
                ],
            )?;
            if boolean(&value["isUnsafe"])? {
                return Err("unsafe constructors are forbidden".into());
            }
            let family = self.name(&value["induct"])?;
            let spec = types
                .iter()
                .find(|spec| spec.name.key == family.key)
                .ok_or("constructor names a family outside its block")?;
            let position = index(&value["cidx"])?;
            let name = self.name(&value["name"])?;
            let fields_count = index(&value["numFields"])?;
            if fields_count > 64
                || spec
                    .constructors
                    .get(position)
                    .is_none_or(|expected| expected.key != name.key)
                || constructors
                    .iter()
                    .any(|ctor: &ConstructorSpec| ctor.name.key == name.key)
                || index(&value["numParams"])? != spec.parameters
            {
                return Err("constructor index, count or ownership metadata mismatch".into());
            }
            let universes = self.universes(&value["levelParams"])?;
            if universes != spec.universes {
                return Err("constructor universes must match its family".into());
            }
            let ty = self.expression(&value["type"])?;
            self.dependencies_known(&dependencies(std::slice::from_ref(&ty))?, &group)?;
            self.reset_budget()?;
            self.kernel.scope(&universes, std::slice::from_ref(&ty))?;
            let (domains, result) = self.peel(&ty, spec.parameters + fields_count, &group)?;
            let (head, args) = application(&result);
            let Term::Global(actual, levels) = head.as_ref() else {
                return Err("constructor return must directly apply its inductive family".into());
            };
            let expected_levels = spec
                .universes
                .iter()
                .cloned()
                .map(Level::variable)
                .collect::<Vec<_>>();
            if actual != &spec.name.key
                || !same_levels(levels, &expected_levels)?
                || args.len() != spec.parameters + spec.indices
            {
                return Err(
                    "constructor return family, universe or argument count mismatch".into(),
                );
            }
            let expected_parameters = (0..spec.parameters)
                .map(|i| term(Term::Var(domains.len() - 1 - i)))
                .collect::<Vec<_>>();
            // Do not use unvalidated provisional families for this comparison.
            // Uniform constructor parameters are the exact telescope variables.
            if !args[..spec.parameters]
                .iter()
                .zip(&expected_parameters)
                .all(|(a, b)| matches!((a.as_ref(),b.as_ref()),(Term::Var(a),Term::Var(b)) if a==b))
            {
                return Err("constructor parameters are not uniform telescope variables".into());
            }
            constructors.push(ConstructorSpec {
                name,
                family: family.key,
                universes,
                ty,
                domains,
                indices: args[spec.parameters..].to_vec(),
            });
        }
        let expected_ctor_names = types
            .iter()
            .flat_map(|spec| spec.constructors.iter().map(|name| name.key.clone()))
            .collect::<Vec<_>>();
        if expected_ctor_names.len() != constructors.len()
            || constructors
                .iter()
                .map(|ctor| &ctor.name.key)
                .ne(expected_ctor_names.iter())
        {
            return Err("inductive block must supply every constructor in family order".into());
        }
        let raw_recs = array(&data["recs"], 16)?;
        self.room(types.len() + constructors.len() + raw_recs.len())?;
        let all_names = group
            .iter()
            .cloned()
            .chain(constructors.iter().map(|ctor| ctor.name.key.clone()))
            .chain(
                raw_recs
                    .iter()
                    .map(|value| {
                        self.name(value.get("name").ok_or("missing recursor name")?)
                            .map(|name| name.key)
                    })
                    .collect::<Result<Vec<_>>>()?,
            )
            .collect::<Vec<_>>();
        if all_names.iter().collect::<HashSet<_>>().len() != all_names.len()
            || all_names.iter().any(|name| self.kernel.contains(name))
        {
            return Err("duplicate declaration identity in inductive block".into());
        }
        let inputs = types
            .iter()
            .map(|spec| InductiveInput {
                name: spec.name.key.clone(),
                universes: spec.universes.clone(),
                parameters: spec.domains[..spec.parameters].to_vec(),
                indices: spec.domains[spec.parameters..].to_vec(),
                sort: spec.sort.clone(),
                constructors: constructors
                    .iter()
                    .filter(|ctor| ctor.family == spec.name.key)
                    .map(|ctor| {
                        (
                            ctor.name.key.clone(),
                            ctor.domains[spec.parameters..].to_vec(),
                            ctor.indices.clone(),
                        )
                    })
                    .collect(),
            })
            .collect::<Vec<_>>();
        self.reset_budget()?;
        self.kernel.declare_group(inputs)?;
        let root = &types[0];
        let levels = root
            .universes
            .iter()
            .cloned()
            .map(Level::variable)
            .collect::<Vec<_>>();
        let (derived, _) = self.kernel.family(&root.name.key, &levels, 0)?;
        let nested_count = derived.group.len() - types.len();
        if types.iter().any(|spec| spec.nested != nested_count) {
            return Err(
                "exported nested count disagrees with reconstructed auxiliary families".into(),
            );
        }
        if raw_recs.len() != derived.group.len() {
            return Err(
                "inductive block must supply one standard recursor per reconstructed family".into(),
            );
        }
        let mut eliminators = types
            .iter()
            .map(|spec| (spec.clone(), suffixed(&spec.name, "rec")))
            .collect::<Vec<_>>();
        for (index, key) in derived.group.iter().skip(types.len()).enumerate() {
            let (declaration, _) = self.kernel.specialization(key, &levels, 0)?;
            let family = declaration
                .family
                .ok_or("missing reconstructed nested family")?;
            let mut domains = family.parameters.clone();
            domains.extend(family.indices.iter().cloned());
            let constructors = family
                .constructors
                .iter()
                .map(|ctor| {
                    self.names
                        .by_key(&ctor.name)?
                        .map(std::borrow::Cow::into_owned)
                        .ok_or_else(|| "missing original nested constructor name".to_owned())
                })
                .collect::<Result<Vec<_>>>()?;
            eliminators.push((
                TypeSpec {
                    name: Name {
                        key: key.clone(),
                        display: format!("nested case {}", index + 1),
                        depth: 1,
                    },
                    universes: root.universes.clone(),
                    ty: declaration.ty,
                    parameters: family.parameters.len(),
                    indices: family.indices.len(),
                    constructors,
                    domains,
                    sort: family.sort,
                    nested: 0,
                },
                suffixed(&root.name, &format!("rec_{}", index + 1)),
            ));
        }
        let expanded_types = eliminators
            .iter()
            .map(|(spec, _)| spec.clone())
            .collect::<Vec<_>>();
        let constructor_count = expanded_types
            .iter()
            .map(|spec| spec.constructors.len())
            .sum::<usize>();
        // Peeling cannot erase ill-typed type wrappers or unused arguments.
        for spec in &types {
            self.reset_budget()?;
            self.kernel.sort(&[], &spec.ty, 0)?;
            let derived = self
                .kernel
                .declarations
                .get(&spec.name.key)?
                .ok_or("missing checked family")?
                .ty
                .clone();
            if !self.kernel.convertible(&[], &derived, &spec.ty, 0)? {
                return Err("exported inductive type disagrees with its checked header".into());
            }
        }
        for ctor in &constructors {
            let spec = types
                .iter()
                .find(|spec| spec.name.key == ctor.family)
                .ok_or("missing constructor family")?;
            self.reset_budget()?;
            self.kernel.sort(&[], &ctor.ty, 0)?;
            let mut ctx = vec![];
            for (expected, actual) in spec.domains[..spec.parameters]
                .iter()
                .zip(&ctor.domains[..spec.parameters])
            {
                if !self.kernel.convertible(&ctx, expected, actual, 0)? {
                    return Err("constructor parameter telescope differs from its family".into());
                }
                ctx.push(expected.clone());
            }
            let (derived, _) = self.kernel.constructor_type(
                &ctor.family,
                &ctor
                    .universes
                    .iter()
                    .cloned()
                    .map(Level::variable)
                    .collect::<Vec<_>>(),
                &ctor.name.key,
                0,
            )?;
            if !self.kernel.convertible(&[], &derived, &ctor.ty, 0)? {
                return Err("exported constructor type differs from its checked fields".into());
            }
            let count = ctor.domains.len();
            let args = (0..count)
                .map(|i| term(Term::Var(count - 1 - i)))
                .collect::<Vec<_>>();
            let body = term(Term::Ctor {
                family: ctor.family.clone(),
                levels: ctor
                    .universes
                    .iter()
                    .cloned()
                    .map(Level::variable)
                    .collect(),
                parameters: args[..spec.parameters].to_vec(),
                constructor: ctor.name.key.clone(),
                fields: args[spec.parameters..].to_vec(),
            });
            self.reset_budget()?;
            self.kernel.definition(
                &ctor.name.key,
                ctor.universes.clone(),
                ctor.ty.clone(),
                lambdas(&ctor.domains, body),
                false,
            )?;
        }
        // Validate the complete metadata before constructing any wrapper.
        let mut recursors = vec![];
        for value in raw_recs {
            let value = fields(
                value,
                &[
                    "name",
                    "levelParams",
                    "type",
                    "all",
                    "numParams",
                    "numIndices",
                    "numMotives",
                    "numMinors",
                    "rules",
                    "k",
                    "isUnsafe",
                ],
            )?;
            if boolean(&value["isUnsafe"])? {
                return Err("unsafe recursors are forbidden".into());
            }
            let name = self.name(&value["name"])?;
            let spec = eliminators
                .iter()
                .find(|(_, expected)| name.key == expected.key)
                .map(|(spec, _)| spec)
                .ok_or("recursor is not a derived member or auxiliary recursor")?;
            if recursors
                .iter()
                .any(|r: &RecursorSpec| r.family == spec.name.key)
            {
                return Err("duplicate family recursor".into());
            }
            let members = self.name_list(&value["all"], 16)?;
            if members.iter().map(|n| &n.key).ne(group.iter())
                || index(&value["numParams"])? != spec.parameters
                || index(&value["numIndices"])? != spec.indices
                || index(&value["numMotives"])? != expanded_types.len()
                || index(&value["numMinors"])? != constructor_count
            {
                return Err("recursor membership or telescope counts mismatch".into());
            }
            let k = expanded_types.len() == 1
                && spec.sort.zero()
                && spec.constructors.len() == 1
                && constructors[0].domains.len() == spec.parameters;
            if boolean(&value["k"])? != k {
                return Err("exported K flag disagrees with the checked constructor shape".into());
            }
            let universes = self.universes(&value["levelParams"])?;
            if !spec.universes.iter().all(|u| universes.contains(u))
                || universes.len() > spec.universes.len() + 1
            {
                return Err(
                    "recursor universe parameters do not extend the family universes".into(),
                );
            }
            let ty = self.expression(&value["type"])?;
            self.dependencies_known(
                &dependencies(std::slice::from_ref(&ty))?,
                &all_names[..group.len() + constructors.len()],
            )?;
            let mut rules = vec![];
            for rule in array(&value["rules"], 64)? {
                let rule = fields(rule, &["ctor", "nfields", "rhs"])?;
                let ctor = self.name(&rule["ctor"])?;
                let (family, _) = self.kernel.family(&spec.name.key, &levels, 0)?;
                let expected = family
                    .constructors
                    .iter()
                    .find(|c| c.name == ctor.key)
                    .ok_or("recursor rule names a foreign constructor")?;
                let nfields = index(&rule["nfields"])?;
                if nfields != expected.fields.len()
                    || rules.iter().any(|(name, _, _)| name == &ctor.key)
                {
                    return Err("recursor rule field count or uniqueness mismatch".into());
                }
                let rhs = self.expression(&rule["rhs"])?;
                self.dependencies_known(&dependencies(std::slice::from_ref(&rhs))?, &all_names)?;
                rules.push((ctor.key, nfields, rhs));
            }
            if rules.len() != spec.constructors.len() {
                return Err("recursor must supply a computation rule for every constructor".into());
            }
            recursors.push(RecursorSpec {
                name,
                family: spec.name.key.clone(),
                universes,
                ty,
                rules,
            });
        }
        for rec in &recursors {
            self.install_recursor(rec, &expanded_types, constructor_count)?;
        }
        for rec in &recursors {
            self.check_recursor_rules(rec, &expanded_types, constructor_count)?;
        }
        // Receipts preserve all raw dependencies, even erased proof terms.
        for spec in &types {
            let roots = std::iter::once(&spec.ty)
                .chain(
                    constructors
                        .iter()
                        .filter(|c| c.family == spec.name.key)
                        .map(|c| &c.ty),
                )
                .cloned()
                .collect::<Vec<_>>();
            self.remember(&spec.name, "inductive", dependencies(&roots)?)?;
        }
        for ctor in &constructors {
            self.remember(
                &ctor.name,
                "constructor",
                dependencies(std::slice::from_ref(&ctor.ty))?,
            )?;
        }
        for rec in &recursors {
            let roots = std::iter::once(&rec.ty)
                .chain(rec.rules.iter().map(|(_, _, rhs)| rhs))
                .cloned()
                .collect::<Vec<_>>();
            self.remember(&rec.name, "recursor", dependencies(&roots)?)?;
        }
        Ok(())
    }

    fn peel(&mut self, ty: &T, count: usize, group: &[String]) -> Result<(Vec<T>, T)> {
        let mut domains = vec![];
        let mut current = ty.clone();
        for _ in 0..count {
            loop {
                if let Term::Pi(domain, body) = current.as_ref() {
                    domains.push(domain.clone());
                    current = body.clone();
                    break;
                }
                if let Term::Let(annotation, value, body) = current.as_ref() {
                    if group.iter().any(|name| {
                        contains_recursive(annotation, name) || contains_recursive(value, name)
                    }) {
                        return Err("recursive occurrence erased by a constructor type wrapper violates strict positivity".into());
                    }
                    current = self.kernel.instantiate(body, value, 0)?;
                    continue;
                }
                if group.iter().any(|name| contains_recursive(&current, name)) {
                    return Err(
                        "noncanonical recursive constructor telescope violates strict positivity"
                            .into(),
                    );
                }
                let reduced = self.kernel.whnf(&domains, &current, 0)?;
                if !matches!(reduced.as_ref(), Term::Pi(..) | Term::Let(..)) {
                    return Err("exported telescope has too few Pi binders".into());
                }
                current = reduced;
            }
        }
        Ok((domains, current))
    }

    fn install_recursor(
        &mut self,
        rec: &RecursorSpec,
        types: &[TypeSpec],
        constructor_count: usize,
    ) -> Result<()> {
        let spec = types
            .iter()
            .find(|spec| spec.name.key == rec.family)
            .ok_or("missing recursor family")?;
        let prefix = spec.parameters + types.len() + constructor_count;
        let count = prefix + spec.indices + 1;
        self.reset_budget()?;
        self.kernel
            .scope(&rec.universes, std::slice::from_ref(&rec.ty))?;
        self.kernel.sort(&[], &rec.ty, 0)?;
        let (domains, _) = self.peel(&rec.ty, count, &[])?;
        let var = |position| term(Term::Var(count - 1 - position));
        let parameters = (0..spec.parameters).map(var).collect::<Vec<_>>();
        let levels = spec
            .universes
            .iter()
            .cloned()
            .map(Level::variable)
            .collect::<Vec<_>>();
        let motives = types
            .iter()
            .enumerate()
            .map(|(i, spec)| (spec.name.key.clone(), var(spec.parameters + i)))
            .collect::<Vec<_>>();
        let mut cases = vec![];
        let mut minor = 0;
        for member in types {
            let (family, _) = self.kernel.family(&member.name.key, &levels, 0)?;
            let mut branches = vec![];
            for ctor in &family.constructors {
                let expected = self.kernel.group_branch_type(
                    &domains,
                    &member.name.key,
                    &levels,
                    &parameters,
                    &motives,
                    ctor,
                    0,
                )?;
                let length =
                    ctor.fields.len() + ctor.recursive.iter().filter(|r| r.is_some()).count();
                let mut inner = domains.clone();
                let mut branch_domains = vec![];
                let mut rest = expected;
                for _ in 0..length {
                    let reduced = self.kernel.whnf(&inner, &rest, 0)?;
                    let Term::Pi(domain, body) = reduced.as_ref() else {
                        return Err("invalid derived branch telescope".into());
                    };
                    branch_domains.push(domain.clone());
                    inner.push(domain.clone());
                    rest = body.clone();
                }
                let mut fields = vec![];
                let mut ihs = vec![];
                let mut position = 0;
                for target in &ctor.recursive {
                    fields.push(term(Term::Var(length - 1 - position)));
                    position += 1;
                    if target.is_some() {
                        ihs.push(term(Term::Var(length - 1 - position)));
                        position += 1;
                    }
                }
                let body = apps(
                    apps(
                        self.kernel.shift(
                            &var(spec.parameters + types.len() + minor),
                            length,
                            0,
                            0,
                        )?,
                        &fields,
                    ),
                    &ihs,
                );
                branches.push(lambdas(&branch_domains, body));
                minor += 1;
            }
            cases.push(RecursionCase {
                family: member.name.key.clone(),
                motive: motives[cases.len()].1.clone(),
                branches,
            });
        }
        let indices = (prefix..prefix + spec.indices).map(var).collect::<Vec<_>>();
        let subject = var(count - 1);
        let body = make_recursor(&rec.family, levels, parameters, indices, cases, subject);
        self.reset_budget()?;
        self.kernel
            .definition(
                &rec.name.key,
                rec.universes.clone(),
                rec.ty.clone(),
                lambdas(&domains, body),
                false,
            )
            .map_err(|why| format!("recursor '{}': {why}", rec.name.display))
    }

    fn check_recursor_rules(
        &mut self,
        rec: &RecursorSpec,
        types: &[TypeSpec],
        constructor_count: usize,
    ) -> Result<()> {
        let spec = types
            .iter()
            .find(|spec| spec.name.key == rec.family)
            .ok_or("missing recursor family")?;
        let prefix_count = spec.parameters + types.len() + constructor_count;
        for (label, _, provided) in &rec.rules {
            self.reset_budget()?;
            self.kernel
                .scope(&rec.universes, std::slice::from_ref(provided))?;
            let levels = spec
                .universes
                .iter()
                .cloned()
                .map(Level::variable)
                .collect::<Vec<_>>();
            let (family, _) = self.kernel.family(&rec.family, &levels, 0)?;
            let ctor = family
                .constructors
                .iter()
                .find(|ctor| &ctor.name == label)
                .ok_or("missing rule constructor")?;
            let (mut domains, _) = self.peel(&rec.ty, prefix_count, &[])?;
            let levels = spec
                .universes
                .iter()
                .cloned()
                .map(Level::variable)
                .collect::<Vec<_>>();
            let (mut telescope, _) =
                self.kernel
                    .constructor_type(&rec.family, &levels, label, 0)?;
            for i in 0..spec.parameters {
                let reduced = self.kernel.whnf(&domains, &telescope, 0)?;
                let Term::Pi(_, body) = reduced.as_ref() else {
                    return Err("invalid constructor parameter telescope".into());
                };
                telescope =
                    self.kernel
                        .instantiate(body, &term(Term::Var(prefix_count - 1 - i)), 0)?;
            }
            for _ in 0..ctor.fields.len() {
                let reduced = self.kernel.whnf(&domains, &telescope, 0)?;
                let Term::Pi(domain, body) = reduced.as_ref() else {
                    return Err("invalid constructor field telescope".into());
                };
                domains.push(domain.clone());
                telescope = body.clone();
            }
            let count = domains.len();
            let parameters = (0..spec.parameters)
                .map(|i| term(Term::Var(count - 1 - i)))
                .collect::<Vec<_>>();
            let indices = self.kernel.family_indices(
                &domains,
                &rec.family,
                &levels,
                &parameters,
                &telescope,
                0,
            )?;
            let fields = (prefix_count..count)
                .map(|i| term(Term::Var(count - 1 - i)))
                .collect();
            let subject = self.kernel.family_constructor(
                &rec.family,
                &levels,
                &parameters,
                label,
                fields,
                0,
            )?;
            let args = (0..prefix_count)
                .map(|i| term(Term::Var(count - 1 - i)))
                .chain(indices)
                .chain(std::iter::once(subject))
                .collect::<Vec<_>>();
            let computed = lambdas(
                &domains,
                apps(
                    term(Term::Global(
                        rec.name.key.clone(),
                        rec.universes.iter().cloned().map(Level::variable).collect(),
                    )),
                    &args,
                ),
            );
            let expected = self.kernel.infer(&[], &computed, 0)?;
            self.kernel.check(&[], provided, &expected, 0)?;
            if !self.kernel.convertible(&[], provided, &computed, 0)? {
                return Err(format!(
                    "recursor '{}' has a forged or stale computation rule",
                    rec.name.display
                ));
            }
        }
        Ok(())
    }
}

fn suffixed(root: &Name, segment: &str) -> Name {
    Name {
        key: format!("{}s{}:{segment}", root.key, segment.len()),
        display: format!("{}.{segment}", root.display),
        depth: root.depth + 1,
    }
}

fn application(value: &T) -> (T, Vec<T>) {
    let mut head = value.clone();
    let mut args = vec![];
    while let Term::App(function, argument) = head.as_ref() {
        args.push(argument.clone());
        head = function.clone();
    }
    args.reverse();
    (head, args)
}
fn lambdas(domains: &[T], mut body: T) -> T {
    for domain in domains.iter().rev() {
        body = term(Term::Lam(domain.clone(), body));
    }
    body
}
fn make_recursor(
    family: &str,
    levels: Vec<Level>,
    parameters: Vec<T>,
    indices: Vec<T>,
    cases: Vec<RecursionCase>,
    subject: T,
) -> T {
    if cases.len() == 1 {
        let case = &cases[0];
        term(Term::Induct {
            family: family.into(),
            levels,
            parameters,
            indices,
            motive: case.motive.clone(),
            branches: case.branches.clone(),
            subject,
        })
    } else {
        term(Term::MutualInduct {
            family: family.into(),
            levels,
            parameters,
            indices,
            cases,
            subject,
        })
    }
}
