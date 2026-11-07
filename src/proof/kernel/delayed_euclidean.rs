//! Observe a complete applied history projection before the VM performs iota.
//! Templates and scalar operands keep their own captured environments. This
//! never installs a numeric result in a record or function memo entry.
use super::*;

impl Machine<'_> {
    fn euclidean_accessor(&mut self) -> Result<Option<(String, Slot)>> {
        let [.., Frame::Apply(_), Frame::Apply(input), Frame::Project(accessor)] =
            self.frames.as_slice()
        else {
            return Ok(None);
        };
        let (accessor, _) = self.source_at(*accessor);
        let Term::Project {
            family, index: 0, ..
        } = accessor.as_ref()
        else {
            return Ok(None);
        };
        let input = *input;
        self.kernel.charge_transformation(64 + family.len())?;
        Ok(Some((family.clone(), input)))
    }

    pub(super) fn begin_euclidean(&mut self, template: Slot, value: &T) -> Result<bool> {
        if self.euclidean_checks >= 256 || self.euclidean_failures >= 4 {
            return Ok(false);
        }
        let Some((record, input)) = self.euclidean_accessor()? else {
            return Ok(false);
        };
        // Known small values favor ordinary reduction, especially when checked
        // declaration tables are cold. This hint never forces an operand.
        if self.small_euclidean_input(input)? {
            return Ok(false);
        }
        self.euclidean_checks += 1;
        let Term::Induct {
            family,
            levels,
            parameters,
            indices,
            branches,
            ..
        } = value.as_ref()
        else {
            return Ok(false);
        };
        if !levels.is_empty()
            || !parameters.is_empty()
            || !indices.is_empty()
            || branches.len() != 2
            || self
                .kernel
                .natural_recursor_family(family, self.depth + 1)?
                .is_none()
        {
            return Ok(false);
        }
        let Some(model) = self.euclidean_model(template, record)? else {
            return Ok(false);
        };
        self.push(Frame::EuclideanFuel {
            template,
            input,
            model,
        })?;
        Ok(true)
    }

    fn small_euclidean_input(&mut self, mut input: Slot) -> Result<bool> {
        for _ in 0..32 {
            self.kernel.tick(self.depth)?;
            if let Some(value) = self.memo[input] {
                input = value;
                continue;
            }
            let Thunk::Source(value, environment) = &self.nodes[input] else {
                return Ok(false);
            };
            match value.as_ref() {
                Term::NatLiteral { value, .. } => {
                    let digits = value.decimal().as_bytes();
                    return Ok(digits.len() == 1
                        || digits.len() == 2 && (digits[0] - b'0') * 10 + digits[1] - b'0' <= 32);
                }
                Term::Var(index) => {
                    let Some(value) = self.variable(*environment, *index)? else {
                        return Ok(false);
                    };
                    input = value;
                }
                _ => return Ok(false),
            }
        }
        Ok(false)
    }

    fn resume_euclidean(&mut self, template: Slot, fuel: Slot) -> Result<Slot> {
        self.euclidean_failures += 1;
        self.push(Frame::Induct(template))?;
        Ok(fuel)
    }

    pub(super) fn euclidean_fuel(
        &mut self,
        template: Slot,
        input: Slot,
        fuel: Slot,
        model: usize,
        value: &T,
        neutral: bool,
    ) -> Result<Slot> {
        let Term::NatLiteral {
            family,
            value: count,
        } = value.as_ref()
        else {
            return self.resume_euclidean(template, fuel);
        };
        if neutral || count.decimal() == "0" || family != self.euclidean_models[model].family() {
            return self.resume_euclidean(template, fuel);
        }
        self.push(Frame::EuclideanInput {
            template,
            fuel,
            model,
        })?;
        self.force(input)
    }

    fn euclidean_model(&mut self, template: Slot, record: String) -> Result<Option<usize>> {
        let (source, environment) = self.source_at(template);
        let Term::Induct {
            family: natural,
            levels,
            parameters,
            indices,
            motive,
            branches,
            ..
        } = source.as_ref()
        else {
            return Err("invalid delayed Euclidean template".into());
        };
        // Reuse a model only for exactly the same immutable code and every
        // captured dependency of its motive and step. Fuel and the arbitrary
        // base are deliberately separate; each call must satisfy its real bound.
        let mut cached_index = None;
        for (index, (cached_record, cached_source, cached_environment)) in
            self.euclidean_sources.iter().enumerate()
        {
            self.kernel.tick(self.depth)?;
            let Term::Induct {
                motive: cached_motive,
                branches: cached_branches,
                ..
            } = cached_source.as_ref()
            else {
                return Err("invalid Euclidean cache key".into());
            };
            if *cached_record == record
                && self.euclidean_models[index].family() == natural
                && closure::same_closure(
                    self.kernel,
                    &self.nodes,
                    &self.bindings,
                    &mut self.euclidean_free,
                    motive,
                    environment,
                    cached_motive,
                    *cached_environment,
                    self.depth + 1,
                )?
                && closure::same_closure(
                    self.kernel,
                    &self.nodes,
                    &self.bindings,
                    &mut self.euclidean_free,
                    &branches[1],
                    environment,
                    &cached_branches[1],
                    *cached_environment,
                    self.depth + 1,
                )?
            {
                cached_index = Some(index);
                break;
            }
        }
        if let Some(model) = cached_index {
            return Ok(Some(model));
        }
        self.kernel.charge_transformation(512 + 2 * natural.len())?;
        // Only a recognizer view: the actual subject stays in its own thunk.
        // A positive placeholder allows checking the successor recurrence
        // without inspecting any runtime operand. No such view is published.
        let positive = term(Term::NatLiteral {
            family: natural.clone(),
            value: Natural::parse("1")?,
        });
        let closed_fuel = term(Term::Induct {
            family: natural.clone(),
            levels: levels.clone(),
            parameters: parameters.clone(),
            indices: indices.clone(),
            motive: motive.clone(),
            branches: branches.clone(),
            subject: positive,
        });
        let depth = self.depth;
        let nodes = &self.nodes;
        let memo = &self.memo;
        let bindings = &self.bindings;
        let closed = self
            .kernel
            .reduction_probe_limits(depth, 16_384, 2 << 20, |kernel| {
                close_model_template(
                    kernel,
                    nodes,
                    memo,
                    bindings,
                    &record,
                    &closed_fuel,
                    environment,
                    depth + 1,
                )
            })?
            .flatten();
        let Some(closed) = closed else {
            return Ok(None);
        };
        let Some((model, _)) = self
            .kernel
            .natural_euclidean_model(&record, &closed, depth + 1)?
        else {
            return Ok(None);
        };
        reserve(self.kernel, &mut self.euclidean_models)?;
        reserve(self.kernel, &mut self.euclidean_sources)?;
        self.kernel.charge_transformation(256 + record.len())?;
        let model_index = self.euclidean_models.len();
        self.euclidean_models.push(model);
        self.euclidean_sources
            .push((record, source.clone(), environment));
        Ok(Some(model_index))
    }

    pub(super) fn euclidean_input(
        &mut self,
        template: Slot,
        fuel: Slot,
        model: usize,
        value: &T,
        neutral: bool,
    ) -> Result<Slot> {
        let Term::NatLiteral {
            family,
            value: input,
        } = value.as_ref()
        else {
            return self.resume_euclidean(template, fuel);
        };
        let (fuel_value, _) = self.source_at(fuel);
        let Term::NatLiteral {
            value: fuel_count, ..
        } = fuel_value.as_ref()
        else {
            return Err("lost delayed Euclidean fuel".into());
        };
        let model = &self.euclidean_models[model];
        if neutral || model.family() != family {
            return self.resume_euclidean(template, fuel);
        }
        let Some(result) =
            self.kernel
                .natural_euclidean_scalars(model, input, fuel_count, self.depth + 1)?
        else {
            return self.resume_euclidean(template, fuel);
        };
        // The uninterrupted suffix still belongs to this complete call. Never
        // cross an Update barrier or write a scalar into a history/function.
        if self.euclidean_accessor()?.is_none() {
            return Err("lost delayed Euclidean application".into());
        }
        self.frames.truncate(self.frames.len() - 3);
        self.number(family, result)
    }
}

/// Specialize bounded static code from its actual captured environment.
/// Recursive-hypothesis thunks and incomplete neutral heads are never quoted.
/// Scalar input/fuel operands remain separate VM slots, not reconstructed calls.
#[expect(clippy::too_many_arguments)]
fn capture(
    kernel: &mut Kernel,
    nodes: &[Thunk],
    memo: &[Option<Slot>],
    bindings: &[Binding],
    slot: Slot,
    remaining: &mut usize,
    depth: usize,
) -> Result<Option<T>> {
    kernel.tick(depth)?;
    if *remaining == 0 {
        return Ok(None);
    }
    *remaining -= 1;
    if let Some(result) = memo[slot] {
        return capture(kernel, nodes, memo, bindings, result, remaining, depth + 1);
    }
    let Thunk::Source(value, environment) = &nodes[slot] else {
        return Ok(None);
    };
    let mut node = |_: &mut Kernel, value: &T, _: usize, _: usize| {
        if *remaining == 0 {
            return Err(REDUCTION_PROBE_DECLINED.into());
        }
        *remaining -= 1;
        Ok(ControlFlow::Continue(value.clone()))
    };
    kernel
        .transform_nodes(
            value,
            0,
            depth + 1,
            &mut node,
            &mut |kernel, index, binders| {
                if index < binders {
                    return Ok(term(Term::Var(index)));
                }
                let Some(slot) =
                    lookup(kernel, bindings, *environment, index - binders, depth + 1)?
                else {
                    return Err(REDUCTION_PROBE_DECLINED.into());
                };
                let Some(result) =
                    capture(kernel, nodes, memo, bindings, slot, &mut 4096, depth + 1)?
                else {
                    return Err(REDUCTION_PROBE_DECLINED.into());
                };
                Ok(result)
            },
            &mut |level| Ok(level.clone()),
        )
        .map(Some)
}

fn lookup(
    kernel: &mut Kernel,
    bindings: &[Binding],
    mut environment: Environment,
    mut index: usize,
    depth: usize,
) -> Result<Option<Slot>> {
    while let Some(at) = environment {
        kernel.tick(depth)?;
        if index == 0 {
            return Ok(Some(bindings[at].value));
        }
        index -= 1;
        environment = bindings[at].parent;
    }
    Ok(None)
}

#[expect(clippy::too_many_arguments)]
fn code_source(
    kernel: &mut Kernel,
    nodes: &[Thunk],
    memo: &[Option<Slot>],
    bindings: &[Binding],
    value: &T,
    environment: Environment,
    depth: usize,
) -> Result<Option<(T, Environment)>> {
    let mut value = value.clone();
    let mut environment = environment;
    for _ in 0..32 {
        kernel.tick(depth)?;
        let Term::Var(index) = value.as_ref() else {
            return Ok(Some((value, environment)));
        };
        let Some(mut slot) = lookup(kernel, bindings, environment, *index, depth + 1)? else {
            return Ok(None);
        };
        for _ in 0..32 {
            kernel.tick(depth)?;
            if let Some(result) = memo[slot] {
                slot = result;
            } else {
                break;
            }
        }
        let Thunk::Source(source, scope) = &nodes[slot] else {
            return Ok(None);
        };
        value = source.clone();
        environment = *scope;
    }
    Ok(None)
}

/// Build a recognizer-only view, leaving the unused base shared. Specialize
/// the motive first so unrelated packed-state folds decline before their step
/// is traversed. The bounded static successor template retains all annotations;
/// the existing model checker observes its selected field. This view is never
/// inferred or published as a source term.
#[expect(clippy::too_many_arguments)]
fn close_model_template(
    kernel: &mut Kernel,
    nodes: &[Thunk],
    memo: &[Option<Slot>],
    bindings: &[Binding],
    record: &str,
    value: &T,
    environment: Environment,
    depth: usize,
) -> Result<Option<T>> {
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
        return Ok(None);
    };
    if branches.len() != 2 {
        return Ok(None);
    }
    let Some((motive_source, motive_environment)) = code_source(
        kernel,
        nodes,
        memo,
        bindings,
        motive,
        environment,
        depth + 1,
    )?
    else {
        return Ok(None);
    };
    let motive = close_template(
        kernel,
        nodes,
        memo,
        bindings,
        &motive_source,
        motive_environment,
        0,
        depth + 1,
    )?;
    kernel.charge_transformation(384 + family.len())?;
    let header = term(Term::Induct {
        family: family.clone(),
        levels: levels.clone(),
        parameters: parameters.clone(),
        indices: indices.clone(),
        motive: motive.clone(),
        branches: branches.clone(),
        subject: subject.clone(),
    });
    if kernel
        .natural_euclidean_header(record, &header, depth + 1)?
        .is_none()
    {
        return Ok(None);
    }
    let Some((step_source, step_environment)) = code_source(
        kernel,
        nodes,
        memo,
        bindings,
        &branches[1],
        environment,
        depth + 1,
    )?
    else {
        return Ok(None);
    };
    let step_source = close_template(
        kernel,
        nodes,
        memo,
        bindings,
        &step_source,
        step_environment,
        0,
        depth + 1,
    )?;
    let step = kernel.natural_head(&step_source, depth + 1)?;
    let Term::Lam(domain, rest) = step.as_ref() else {
        return Ok(None);
    };
    let rest = kernel.natural_head(rest, depth + 1)?;
    let Term::Lam(old_type, body) = rest.as_ref() else {
        return Ok(None);
    };
    let body = kernel.natural_head(body, depth + 1)?;
    let Term::Ctor {
        family: actual,
        levels: record_levels,
        parameters: record_parameters,
        constructor,
        fields,
    } = body.as_ref()
    else {
        return Ok(None);
    };
    if actual != record || fields.is_empty() {
        return Ok(None);
    }
    let domain = domain.clone();
    let selected = fields[0].clone();
    kernel.charge_transformation(
        768 + fields.len() * std::mem::size_of::<T>() + family.len() + actual.len(),
    )?;
    let mut retained_fields = fields.clone();
    retained_fields[0] = selected;
    let body = term(Term::Ctor {
        family: actual.clone(),
        levels: record_levels.clone(),
        parameters: record_parameters.clone(),
        constructor: constructor.clone(),
        fields: retained_fields,
    });
    let step = term(Term::Lam(domain, term(Term::Lam(old_type.clone(), body))));
    Ok(Some(term(Term::Induct {
        family: family.clone(),
        levels: levels.clone(),
        parameters: parameters.clone(),
        indices: indices.clone(),
        motive,
        branches: vec![branches[0].clone(), step],
        subject: subject.clone(),
    })))
}

#[expect(clippy::too_many_arguments)]
fn close_template(
    kernel: &mut Kernel,
    nodes: &[Thunk],
    memo: &[Option<Slot>],
    bindings: &[Binding],
    value: &T,
    environment: Environment,
    initial_binders: usize,
    depth: usize,
) -> Result<T> {
    let mut captures = Vec::<(Slot, T)>::new();
    kernel.transform_shared(
        value,
        initial_binders,
        depth + 1,
        &mut |kernel, index, binders| {
            if index < binders {
                return Ok(term(Term::Var(index)));
            }
            let Some(slot) = lookup(kernel, bindings, environment, index - binders, depth + 1)?
            else {
                return Err(REDUCTION_PROBE_DECLINED.into());
            };
            let replacement =
                if let Some((_, value)) = captures.iter().find(|(key, _)| *key == slot) {
                    value.clone()
                } else {
                    if captures.len() >= 64 {
                        return Err(REDUCTION_PROBE_DECLINED.into());
                    }
                    let Some(value) =
                        capture(kernel, nodes, memo, bindings, slot, &mut 4096, depth + 1)?
                    else {
                        return Err(REDUCTION_PROBE_DECLINED.into());
                    };
                    reserve(kernel, &mut captures)?;
                    captures.push((slot, value.clone()));
                    value
                };
            Ok(replacement)
        },
        &mut |level| Ok(level.clone()),
    )
}
