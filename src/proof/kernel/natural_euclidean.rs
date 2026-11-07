//! Closed Euclidean observations of a checked course-of-values recurrence.
//! Names never authorize computation. Only the selected field's data flow is
//! observed; source inference still checks all types, values and proof fields.
use super::*;

struct TagShape {
    constructors: Vec<(String, usize)>,
    parameters: usize,
}

#[derive(Clone, Copy)]
enum EuclideanObservation {
    Quotient,
    Remainder,
}

/// Private validated data flow; callers cannot construct an arithmetic model.
pub(in crate::proof::kernel) struct EuclideanModel {
    family: String,
    divisor: Natural,
    observation: EuclideanObservation,
}

impl EuclideanModel {
    pub(in crate::proof::kernel) fn family(&self) -> &str {
        &self.family
    }
}

struct EuclideanDivisor {
    value: Natural,
    expression: T,
}

struct RegionTags {
    divisor: Option<EuclideanDivisor>,
    // The state is below, equal to, or above the same positive divisor.
    tags: [usize; 3],
}

impl Kernel {
    pub(super) fn natural_euclidean_observation(
        &mut self,
        value: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        let Term::App(function, _) = value.as_ref() else {
            return Ok(None);
        };
        let Term::App(function, input) = function.as_ref() else {
            return Ok(None);
        };
        let Term::Project {
            family: record,
            index: 0,
            subject,
        } = function.as_ref()
        else {
            return Ok(None);
        };
        // The observation requires a closed numeral. A bare context variable
        // cannot supply one; do not inspect its recurrence and discarded proof
        // arguments before reaching that same refusal at euclidean_number.
        if matches!(input.as_ref(), Term::Var(_)) {
            return Ok(None);
        }
        let observed = self.euclidean_induction_view(subject, depth + 1)?;
        let Some((model, fuel)) = self.natural_euclidean_model(record, &observed, depth + 1)?
        else {
            return Ok(None);
        };
        let family = &model.family;
        let Some(input) = self.euclidean_number(family, input, depth + 1)? else {
            return Ok(None);
        };
        let (quotient, remainder) = self.euclidean_divide(&model, &input, depth + 1)?;
        // There are q positive steps and one terminal step. Never assume a
        // proof argument establishes sufficient fuel for definitional reduction.
        if !self.euclidean_has_fuel(family, &fuel, &quotient, depth + 1)? {
            return Ok(None);
        }
        let value = match model.observation {
            EuclideanObservation::Quotient => quotient,
            EuclideanObservation::Remainder => remainder,
        };
        self.charge_transformation(TERM_NODE_BYTES + family.len() + value.decimal().len())?;
        Ok(Some(term(Term::NatLiteral {
            family: family.clone(),
            value,
        })))
    }

    /// Recognize checked code without evaluating its input or expanding its
    /// history. Only this routine constructs a model; names confer no authority.
    pub(in crate::proof::kernel) fn natural_euclidean_model(
        &mut self,
        record: &str,
        observed: &T,
        depth: usize,
    ) -> Result<Option<(EuclideanModel, T)>> {
        let Some(desc) = self.natural_euclidean_header(record, observed, depth + 1)? else {
            return Ok(None);
        };
        let Term::Induct {
            family,
            branches,
            subject: fuel,
            ..
        } = observed.as_ref()
        else {
            return Ok(None);
        };
        let step = self.natural_head(&branches[1], depth + 1)?;
        let Term::Lam(domain, rest) = step.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let rest = self.natural_head(rest, depth + 1)?;
        let Term::Lam(_, body) = rest.as_ref() else {
            return Ok(None);
        };
        let body = self.natural_head(body, depth + 1)?;
        let Term::Ctor {
            family: actual,
            constructor,
            fields,
            ..
        } = body.as_ref()
        else {
            return Ok(None);
        };
        if actual != record
            || constructor != &desc.constructors[0].name
            || fields.len() != desc.constructors[0].fields.len()
        {
            return Ok(None);
        }
        let function = self.natural_head(&fields[0], depth + 1)?;
        let Term::Lam(domain, body) = function.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let body = self.natural_head(body, depth + 1)?;
        let Term::Lam(domain, body) = body.as_ref() else {
            return Ok(None);
        };
        if !self.euclidean_proposition(domain, depth + 1)? {
            return Ok(None);
        }
        // Under fuel, old record, state and its proof: state=1, record=2.
        let Some((divisor, observation)) = self.euclidean_step(family, record, body, depth + 1)?
        else {
            return Ok(None);
        };
        self.charge_transformation(256 + family.len() + divisor.value.decimal().len())?;
        Ok(Some((
            EuclideanModel {
                family: family.clone(),
                divisor: divisor.value,
                observation,
            },
            fuel.clone(),
        )))
    }

    /// A cheap eligibility check, also used before a delayed VM forces fuel.
    /// Only the complete model recognizer authorizes scalar observation.
    pub(in crate::proof::kernel) fn natural_euclidean_header(
        &mut self,
        record: &str,
        observed: &T,
        depth: usize,
    ) -> Result<Option<Family>> {
        self.tick(depth)?;
        let Term::Induct {
            family,
            levels,
            parameters,
            indices,
            motive,
            branches,
            subject: fuel,
        } = observed.as_ref()
        else {
            return Ok(None);
        };
        if !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || branches.len() != 2
            || self.provisional_family(record)
            || self.nested.contains_key(record)?
            || self.natural_recursor_family(family, depth + 1)?.is_none()
        {
            return Ok(None);
        }
        // The base does not inspect the successor branch at all. Do not
        // speculate into discarded arithmetic when the fuel is already zero.
        let fuel_head = self.euclidean_induction_view(fuel, depth + 1)?;
        if matches!(fuel_head.as_ref(), Term::NatLiteral { family: actual, value }
            if actual == family && value.decimal() == "0")
            || matches!(fuel_head.as_ref(), Term::Ctor { family: actual, constructor, fields, .. }
                if actual == family && fields.is_empty()
                    && constructor == &self.natural_family(family, depth + 1)?.constructors[0].name)
        {
            return Ok(None);
        }

        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, body) = motive.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(None);
        }
        let shape = self.natural_head(body, depth + 1)?;
        let Some((actual, record_levels, arguments, desc)) = self.record_type(&shape, depth + 1)?
        else {
            return Ok(None);
        };
        if actual != record
            || arguments.is_empty()
            || desc.constructors[0].fields.is_empty()
            || !matches!(desc.constructors[0].fields[0].as_ref(), Term::Var(i) if *i == arguments.len()-1)
        {
            return Ok(None);
        }
        let (_, map) = self.family(record, &record_levels, depth + 1)?;
        if !desc.sort.substitute(&map)?.equivalent(&Level::number(1)?)?
            || !self.euclidean_function_type(&arguments[0], family, depth + 1)?
        {
            return Ok(None);
        }

        Ok(Some(desc))
    }

    fn euclidean_divide(
        &mut self,
        model: &EuclideanModel,
        input: &Natural,
        depth: usize,
    ) -> Result<(Natural, Natural)> {
        self.charge_transformation(
            512 + 4 * (input.decimal().len() + model.divisor.decimal().len()),
        )?;
        input.divide_remainder_metered(&model.divisor, |work| {
            self.charge_work(work)?;
            self.tick(depth + 1)
        })
    }

    /// A delayed observation may supply canonical scalar operands directly.
    /// Its real fuel, including the terminal successor, is still mandatory.
    pub(in crate::proof::kernel) fn natural_euclidean_scalars(
        &mut self,
        model: &EuclideanModel,
        input: &Natural,
        fuel: &Natural,
        depth: usize,
    ) -> Result<Option<Natural>> {
        self.tick(depth)?;
        let (quotient, remainder) = self.euclidean_divide(model, input, depth + 1)?;
        self.charge_work(fuel.decimal().len().min(quotient.decimal().len()) + 1)?;
        if decimal_order(fuel, &quotient) != std::cmp::Ordering::Greater {
            return Ok(None);
        }
        Ok(Some(match model.observation {
            EuclideanObservation::Quotient => quotient,
            EuclideanObservation::Remainder => remainder,
        }))
    }

    /// Expose beta/delta/zeta only. Stop before natural iota so the entire
    /// history fold remains available for the observation's structural checks.
    fn euclidean_induction_view(&mut self, value: &T, depth: usize) -> Result<T> {
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
                    value = if map.is_empty() {
                        body
                    } else {
                        self.universes(&body, &map, depth + 1)?
                    };
                }
                Term::App(function, argument) => {
                    if matches!(function.as_ref(), Term::App(..)) {
                        if let Some(reduced) = self.natural_beta_spine(&value, depth)? {
                            value = reduced;
                            continue;
                        }
                    }
                    let reduced = self.euclidean_induction_view(function, depth + 1)?;
                    if let Term::Lam(_, body) = reduced.as_ref() {
                        value = self.instantiate(body, argument, depth + 1)?;
                    } else if Arc::ptr_eq(function, &reduced) {
                        return Ok(value);
                    } else {
                        self.charge_transformation(TERM_NODE_BYTES)?;
                        return Ok(term(Term::App(reduced, argument.clone())));
                    }
                }
                Term::Let(_, definition, body) => {
                    value = self.instantiate(body, definition, depth + 1)?
                }
                Term::Project {
                    family,
                    index,
                    subject,
                } => {
                    let reduced = self.euclidean_induction_view(subject, depth + 1)?;
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
                    if Arc::ptr_eq(subject, &reduced) {
                        return Ok(value);
                    }
                    self.charge_transformation(TERM_NODE_BYTES + family.len())?;
                    return Ok(term(Term::Project {
                        family: family.clone(),
                        index: *index,
                        subject: reduced,
                    }));
                }
                _ => return Ok(value),
            }
        }
    }

    fn euclidean_number(
        &mut self,
        family: &str,
        value: &T,
        depth: usize,
    ) -> Result<Option<Natural>> {
        if let Some(number) = self.euclidean_compact_number(family, value, depth)? {
            return Ok(Some(number));
        }
        self.natural_probe_number(family, value, depth)
    }

    /// Recognize compact numerals without forcing arbitrary arithmetic in an
    /// operand that ordinary evaluation might discard.
    fn euclidean_compact_number(
        &mut self,
        family: &str,
        value: &T,
        depth: usize,
    ) -> Result<Option<Natural>> {
        self.tick(depth)?;
        let value = self.euclidean_induction_view(value, depth + 1)?;
        if let Term::NatLiteral {
            family: actual,
            value,
        } = value.as_ref()
        {
            if actual == family {
                self.charge_transformation(128 + value.decimal().len())?;
                return Ok(Some(value.clone()));
            }
            return Ok(None);
        }
        let Term::Ctor {
            family: actual,
            levels,
            parameters,
            constructor,
            fields,
        } = value.as_ref()
        else {
            return Ok(None);
        };
        if actual != family || !levels.is_empty() || !parameters.is_empty() {
            return Ok(None);
        }
        let desc = self.natural_family(family, depth + 1)?;
        if constructor == &desc.constructors[0].name && fields.is_empty() {
            return Ok(Some(Natural::parse("0")?));
        }
        if constructor != &desc.constructors[1].name || fields.len() != 1 {
            return Ok(None);
        }
        let Some(base) = self.euclidean_compact_number(family, &fields[0], depth + 1)? else {
            return Ok(None);
        };
        if base.decimal().len() == MAX_DIGITS {
            self.charge_work(base.decimal().len())?;
            if base.decimal().bytes().all(|b| b == b'9') {
                return Ok(None);
            }
        }
        self.charge_work(base.decimal().len() + 1)?;
        self.tick(depth + 1)?;
        self.charge_transformation(256 + base.decimal().len())?;
        Ok(Some(base.add(&Natural::parse("1")?)?))
    }

    fn euclidean_has_fuel(
        &mut self,
        family: &str,
        value: &T,
        quotient: &Natural,
        depth: usize,
    ) -> Result<bool> {
        self.tick(depth)?;
        let mut value = value.clone();
        self.charge_transformation(128 + quotient.decimal().len())?;
        let mut required = quotient.clone();
        let desc = self.natural_family(family, depth + 1)?;
        let mut level = depth;
        loop {
            value = self.euclidean_induction_view(&value, level + 1)?;
            if let Term::NatLiteral {
                family: actual,
                value,
            } = value.as_ref()
            {
                if actual != family {
                    return Ok(false);
                }
                self.charge_work(value.decimal().len().min(required.decimal().len()) + 1)?;
                return Ok(decimal_order(value, &required) == std::cmp::Ordering::Greater);
            }
            let Term::Ctor {
                family: actual,
                levels,
                parameters,
                constructor,
                fields,
            } = value.as_ref()
            else {
                let Some(fuel) = self.natural_probe_number(family, &value, level + 1)? else {
                    return Ok(false);
                };
                self.charge_work(fuel.decimal().len().min(required.decimal().len()) + 1)?;
                return Ok(decimal_order(&fuel, &required) == std::cmp::Ordering::Greater);
            };
            if actual != family
                || !levels.is_empty()
                || !parameters.is_empty()
                || constructor != &desc.constructors[1].name
                || fields.len() != 1
            {
                return Ok(false);
            }
            if required.decimal() == "0" {
                return Ok(true);
            }
            self.charge_work(required.decimal().len())?;
            self.tick(level + 1)?;
            self.charge_transformation(128 + required.decimal().len())?;
            required = required
                .predecessor()
                .ok_or("missing positive fuel bound")?;
            value = fields[0].clone();
            level += 1;
        }
    }

    fn euclidean_function_type(&mut self, value: &T, family: &str, depth: usize) -> Result<bool> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        let Term::Pi(domain, rest) = value.as_ref() else {
            return Ok(false);
        };
        if !self.natural_type(domain, family, depth + 1)? {
            return Ok(false);
        }
        let rest = self.natural_head(rest, depth + 1)?;
        let Term::Pi(domain, range) = rest.as_ref() else {
            return Ok(false);
        };
        Ok(self.euclidean_proposition(domain, depth + 1)?
            && self.natural_type(range, family, depth + 1)?)
    }

    fn euclidean_proposition(&mut self, value: &T, depth: usize) -> Result<bool> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        if matches!(value.as_ref(), Term::Eq(..)) {
            return Ok(true);
        }
        let (head, arguments) = self.euclidean_application_spine(&value, depth + 1)?;
        let Term::Global(name, levels) = head.as_ref() else {
            return Ok(false);
        };
        if self.provisional_family(name) || self.nested.contains_key(name)? {
            return Ok(false);
        }
        let (decl, map) = self.specialization(name, levels, depth + 1)?;
        if let Some(desc) = decl.family {
            return Ok(
                arguments.len() == desc.parameters.len() + desc.indices.len()
                    && desc.sort.substitute(&map)?.zero(),
            );
        }
        let ty = if map.is_empty() {
            decl.ty
        } else {
            self.universes(&decl.ty, &map, depth + 1)?
        };
        Ok(arguments.is_empty() && matches!(ty.as_ref(),Term::Sort(level) if level.zero()))
    }

    fn euclidean_tag_shape(&mut self, family: &str, depth: usize) -> Result<Option<TagShape>> {
        self.tick(depth)?;
        if self.provisional_family(family) || self.nested.contains_key(family)? {
            return Ok(None);
        }
        let Some(decl) = self.declarations.get(family)? else {
            return Ok(None);
        };
        let Some(desc) = decl.family.clone() else {
            return Ok(None);
        };
        if !decl.universes.is_empty()
            || desc.group != [family]
            || !desc.indices.is_empty()
            || desc.constructors.len() != 2
            || !desc.sort.equivalent(&Level::number(1)?)?
        {
            return Ok(None);
        }
        if desc
            .parameters
            .iter()
            .any(|p| !matches!(p.as_ref(),Term::Sort(level) if level.zero()))
        {
            return Ok(None);
        }
        let mut constructors = Vec::new();
        self.charge_transformation(256 + family.len())?;
        for constructor in desc.constructors {
            let mut context = desc.parameters.clone();
            for field in &constructor.fields {
                if !self.sort(&context, field, depth + 1)?.zero() {
                    return Ok(None);
                }
                context.push(field.clone());
            }
            self.charge_transformation(128 + constructor.name.len())?;
            constructors.push((constructor.name, constructor.fields.len()));
        }
        Ok(Some(TagShape {
            constructors,
            parameters: desc.parameters.len(),
        }))
    }

    fn euclidean_constructor_tag(
        &mut self,
        value: &T,
        family: &str,
        shape: &TagShape,
        depth: usize,
    ) -> Result<Option<usize>> {
        self.tick(depth)?;
        let Term::Ctor {
            family: actual,
            levels,
            parameters,
            constructor,
            fields,
        } = value.as_ref()
        else {
            return Ok(None);
        };
        if actual != family || !levels.is_empty() || parameters.len() != shape.parameters {
            return Ok(None);
        }
        Ok(shape
            .constructors
            .iter()
            .position(|(name, count)| name == constructor && *count == fields.len()))
    }

    fn euclidean_drop_fields(
        &mut self,
        value: &T,
        fields: usize,
        depth: usize,
    ) -> Result<Option<T>> {
        self.tick(depth)?;
        let mut value = value.clone();
        for index in 0..fields {
            value = self.natural_head(&value, depth + index + 1)?;
            let Term::Lam(_, body) = value.as_ref() else {
                return Ok(None);
            };
            value = body.clone();
        }
        Ok(Some(value))
    }

    fn euclidean_application_spine(&mut self, value: &T, depth: usize) -> Result<(T, Vec<T>)> {
        let mut head = value.clone();
        let mut arguments = Vec::new();
        while let Term::App(function, argument) = head.as_ref() {
            self.tick(depth + arguments.len())?;
            self.charge_transformation(32)?;
            arguments.push(argument.clone());
            head = function.clone();
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    /// Interpret only finite constructor tags. Constructor fields must all
    /// have Prop types, so selecting a branch never inspects proof payloads.
    /// Every split comes from the already checked paired-predecessor rule.
    fn euclidean_tags(
        &mut self,
        value: &T,
        natural: &str,
        family: &str,
        state: usize,
        depth: usize,
    ) -> Result<Option<RegionTags>> {
        self.tick(depth)?;
        let Some(shape) = self.euclidean_tag_shape(family, depth + 1)? else {
            return Ok(None);
        };
        let value = self.natural_head(value, depth + 1)?;
        if let Some(tag) = self.euclidean_constructor_tag(&value, family, &shape, depth + 1)? {
            return Ok(Some(RegionTags {
                divisor: None,
                tags: [tag; 3],
            }));
        }
        if let Some(tags) =
            self.euclidean_comparison_tags(&value, natural, family, &shape, state, depth + 1)?
        {
            return Ok(Some(tags));
        }
        let Term::Induct {
            family: subject_family,
            levels,
            parameters,
            indices,
            branches,
            subject,
            ..
        } = value.as_ref()
        else {
            return Ok(None);
        };
        let Some(subject_shape) = self.euclidean_tag_shape(subject_family, depth + 1)? else {
            return Ok(None);
        };
        if !levels.is_empty()
            || !indices.is_empty()
            || parameters.len() != subject_shape.parameters
            || branches.len() != subject_shape.constructors.len()
        {
            return Ok(None);
        }
        let Some(subject) =
            self.euclidean_tags(subject, natural, subject_family, state, depth + 1)?
        else {
            return Ok(None);
        };
        if subject.divisor.is_none() {
            let ordinal = subject.tags[0];
            let fields = subject_shape.constructors[ordinal].1;
            let Some(body) = self.euclidean_drop_fields(&branches[ordinal], fields, depth + 1)?
            else {
                return Ok(None);
            };
            return self.euclidean_tags(&body, natural, family, state + fields, depth + 1);
        }
        let mut tags = [0; 3];
        for (region, ordinal) in subject.tags.iter().copied().enumerate() {
            let fields = subject_shape.constructors[ordinal].1;
            let Some(body) = self.euclidean_drop_fields(&branches[ordinal], fields, depth + 1)?
            else {
                return Ok(None);
            };
            let Some(branch) =
                self.euclidean_tags(&body, natural, family, state + fields, depth + 1)?
            else {
                return Ok(None);
            };
            // A second independent split is outside this recurrence. Do not
            // infer universal behavior by testing a few concrete states.
            if branch.divisor.is_some() {
                return Ok(None);
            }
            tags[region] = branch.tags[0];
        }
        Ok(Some(RegionTags {
            divisor: subject.divisor,
            tags,
        }))
    }

    #[expect(clippy::too_many_arguments)]
    fn euclidean_comparison_tags(
        &mut self,
        value: &T,
        natural: &str,
        family: &str,
        shape: &TagShape,
        state: usize,
        depth: usize,
    ) -> Result<Option<RegionTags>> {
        self.tick(depth)?;
        let Term::App(function, right) = value.as_ref() else {
            return Ok(None);
        };
        let function = self.natural_head(function, depth + 1)?;
        let Term::Induct {
            family: actual,
            levels,
            parameters,
            indices,
            motive,
            branches,
            subject: left,
        } = function.as_ref()
        else {
            return Ok(None);
        };
        if actual != natural
            || !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || self.natural_recursor_family(natural, depth + 1)?.is_none()
        {
            return Ok(None);
        }
        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, result) = motive.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, natural, depth + 1)? {
            return Ok(None);
        }
        let result = self.natural_head(result, depth + 1)?;
        let Term::Pi(domain, range) = result.as_ref() else {
            return Ok(None);
        };
        if !self.natural_type(domain, natural, depth + 1)? {
            return Ok(None);
        }
        let range = self.natural_head(range, depth + 1)?;
        if !matches!(range.as_ref(),Term::Global(name,levels) if name == family && levels.is_empty())
        {
            return Ok(None);
        }
        let Some(terminals) =
            self.natural_comparison_terminals(natural, &result, branches, depth + 1)?
        else {
            return Ok(None);
        };
        let mut tags = [0; 3];
        for (tag, terminal) in tags.iter_mut().zip(terminals) {
            let Some(ordinal) =
                self.euclidean_constructor_tag(&terminal, family, shape, depth + 1)?
            else {
                return Ok(None);
            };
            *tag = ordinal;
        }
        let left_head = self.natural_head(left, depth + 1)?;
        let right_head = self.natural_head(right, depth + 1)?;
        let (divisor, tags) = if matches!(left_head.as_ref(),Term::Var(i) if *i == state) {
            let Some(divisor) = self.euclidean_number(natural, &right_head, depth + 1)? else {
                return Ok(None);
            };
            (
                EuclideanDivisor {
                    value: divisor,
                    expression: right.clone(),
                },
                [tags[1], tags[0], tags[2]],
            )
        } else if matches!(right_head.as_ref(),Term::Var(i) if *i == state) {
            let Some(divisor) = self.euclidean_number(natural, &left_head, depth + 1)? else {
                return Ok(None);
            };
            (
                EuclideanDivisor {
                    value: divisor,
                    expression: left.clone(),
                },
                [tags[2], tags[0], tags[1]],
            )
        } else {
            return Ok(None);
        };
        Ok(Some(RegionTags {
            divisor: Some(divisor),
            tags,
        }))
    }

    fn euclidean_step(
        &mut self,
        natural: &str,
        record: &str,
        value: &T,
        depth: usize,
    ) -> Result<Option<(EuclideanDivisor, EuclideanObservation)>> {
        self.tick(depth)?;
        let value = self.natural_head(value, depth + 1)?;
        let Term::Induct {
            family,
            levels,
            parameters,
            indices,
            branches,
            subject,
            ..
        } = value.as_ref()
        else {
            return Ok(None);
        };
        let Some(shape) = self.euclidean_tag_shape(family, depth + 1)? else {
            return Ok(None);
        };
        if !levels.is_empty()
            || !indices.is_empty()
            || parameters.len() != shape.parameters
            || branches.len() != shape.constructors.len()
        {
            return Ok(None);
        }
        let Some(guard) = self.euclidean_tags(subject, natural, family, 1, depth + 1)? else {
            return Ok(None);
        };
        let Some(divisor) = guard.divisor else {
            return Ok(None);
        };
        if divisor.value.decimal() == "0"
            || guard.tags[0] == guard.tags[1]
            || guard.tags[1] != guard.tags[2]
        {
            return Ok(None);
        }
        let positive = guard.tags[1];
        let negative = guard.tags[0];
        let Some(terminal) = self.euclidean_drop_fields(
            &branches[negative],
            shape.constructors[negative].1,
            depth + 1,
        )?
        else {
            return Ok(None);
        };
        let terminal = self.natural_head(&terminal, depth + 1)?;
        let observation = if matches!(terminal.as_ref(), Term::Var(index)
            if *index == 1 + shape.constructors[negative].1)
        {
            EuclideanObservation::Remainder
        } else if self
            .euclidean_compact_number(natural, &terminal, depth + 1)?
            .is_some_and(|value| value.decimal() == "0")
        {
            EuclideanObservation::Quotient
        } else {
            return Ok(None);
        };
        let fields = shape.constructors[positive].1;
        let Some(body) = self.euclidean_drop_fields(&branches[positive], fields, depth + 1)? else {
            return Ok(None);
        };
        let Some(bias) = self.euclidean_recursive_bias(
            natural,
            record,
            &body,
            1 + fields,
            2 + fields,
            &divisor,
            depth + 1,
        )?
        else {
            return Ok(None);
        };
        let expected = match observation {
            EuclideanObservation::Quotient => "1",
            EuclideanObservation::Remainder => "0",
        };
        if bias.decimal() != expected {
            return Ok(None);
        }
        Ok(Some((divisor, observation)))
    }

    #[expect(clippy::too_many_arguments)]
    fn euclidean_recursive_bias(
        &mut self,
        natural: &str,
        record: &str,
        value: &T,
        state: usize,
        previous: usize,
        divisor: &EuclideanDivisor,
        depth: usize,
    ) -> Result<Option<Natural>> {
        self.tick(depth)?;
        // Add a fresh Nat-result binder for the recursive call. All existing
        // locals are shifted past it, including locals appearing in types.
        let value = self.shift(value, 1, 0, depth + 1)?;
        let mut refused = false;
        let mut found = false;
        let body = self.transform_nodes(
            &value,0,depth+1,
            &mut |kernel,value,binders,depth| {
                if refused { return Ok(ControlFlow::Break(value.clone())) }
                let value = kernel.natural_head(value,depth+1)?;
                if let Term::App(function,_) = value.as_ref() {
                    if let Term::App(function,argument) = function.as_ref() {
                        if matches!(function.as_ref(),Term::Project { family,index:0,subject }
                            if family == record && matches!(subject.as_ref(),Term::Var(i) if *i == previous+1+binders))
                        {
                            if !kernel.euclidean_state_update(natural,argument,state+1+binders,divisor,depth+1)? {
                                refused = true;
                                return Ok(ControlFlow::Break(value));
                            }
                            found = true;
                            return Ok(ControlFlow::Break(term(Term::Var(binders))));
                        }
                    }
                }
                if matches!(value.as_ref(),Term::Var(i) if *i == previous+1+binders) {
                    refused = true;
                    return Ok(ControlFlow::Break(value));
                }
                Ok(ControlFlow::Continue(value))
            },
            &mut |_,index,_| Ok(term(Term::Var(index))),
            &mut |level| Ok(level.clone()),
        )?;
        if refused || !found {
            return Ok(None);
        }
        self.natural_translation_bias(natural, &body, 0, depth + 1)
    }

    fn euclidean_state_update(
        &mut self,
        natural: &str,
        value: &T,
        state: usize,
        divisor: &EuclideanDivisor,
        depth: usize,
    ) -> Result<bool> {
        self.tick(depth)?;
        // The guard certified a context-independent reduction of this exact
        // expression. Reuse its value in an application argument, then still
        // verify the entire predecessor-iteration shape and constant count.
        let specialized = if let Term::App(function, argument) = value.as_ref() {
            if self.same_syntax(argument, &divisor.expression)? {
                self.charge_transformation(256 + natural.len() + divisor.value.decimal().len())?;
                term(Term::App(
                    function.clone(),
                    term(Term::NatLiteral {
                        family: natural.to_owned(),
                        value: divisor.value.clone(),
                    }),
                ))
            } else {
                value.clone()
            }
        } else {
            value.clone()
        };
        let value = self.natural_head(&specialized, depth + 1)?;
        let Term::Induct {
            family,
            levels,
            parameters,
            indices,
            motive,
            branches,
            subject,
        } = value.as_ref()
        else {
            return Ok(false);
        };
        if family != natural
            || !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || branches.len() != 2
        {
            return Ok(false);
        }
        let motive = self.natural_head(motive, depth + 1)?;
        let Term::Lam(domain, range) = motive.as_ref() else {
            return Ok(false);
        };
        if !self.natural_type(domain, natural, depth + 1)?
            || !self.natural_type(range, natural, depth + 1)?
        {
            return Ok(false);
        }
        let base = self.natural_head(&branches[0], depth + 1)?;
        if !matches!(base.as_ref(),Term::Var(i) if *i == state) {
            return Ok(false);
        }
        if self.euclidean_number(natural, subject, depth + 1)?.as_ref() != Some(&divisor.value) {
            return Ok(false);
        }
        let step = self.natural_head(&branches[1], depth + 1)?;
        let Term::Lam(domain, body) = step.as_ref() else {
            return Ok(false);
        };
        if !self.natural_type(domain, natural, depth + 1)? {
            return Ok(false);
        }
        let body = self.natural_head(body, depth + 1)?;
        let Term::Lam(domain, body) = body.as_ref() else {
            return Ok(false);
        };
        if !self.natural_type(domain, natural, depth + 1)? {
            return Ok(false);
        }
        Ok(self
            .natural_predecessor_subject(natural, body, depth + 1)?
            .is_some_and(|subject| matches!(subject.as_ref(), Term::Var(0))))
    }
}

fn decimal_order(left: &Natural, right: &Natural) -> std::cmp::Ordering {
    (left.decimal().len(), left.decimal()).cmp(&(right.decimal().len(), right.decimal()))
}

#[cfg(test)]
#[path = "natural_euclidean_tests.rs"]
mod tests;
