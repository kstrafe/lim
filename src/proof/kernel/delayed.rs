//! Operation-local weak-head evaluation with delayed term substitutions.
//! Captured environments and continuations use arena indices, so cleanup has
//! no recursive closure chain. This computes syntax, never a typing judgment.
use super::*;

#[path = "delayed_closure.rs"]
mod closure;
#[path = "delayed_euclidean.rs"]
mod euclidean;
#[path = "delayed_metadata.rs"]
mod metadata;

type Slot = usize;
type Environment = Option<usize>;

#[derive(Clone)]
enum Thunk {
    Source(T, Environment),
    Recursor {
        template: Slot,
        subject: Slot,
    },
    // This is only a stuck proof/subject marker. Its head is not the full
    // application and must never be reified or compared as an endpoint.
    Neutral(T),
    Indices {
        template: Slot,
        parameters: Environment,
        position: usize,
    },
}
struct Binding {
    value: Slot,
    parent: Environment,
}
#[derive(Clone, Copy)]
enum Frame {
    Update(Slot),
    Apply(Slot),
    Project(Slot),
    First,
    Second,
    Induct(Slot),
    EqProof(Slot),
    EqLeft {
        right: Slot,
        base: Slot,
    },
    EqRight {
        left: Slot,
        base: Slot,
    },
    Successor(Slot),
    EuclideanFuel {
        template: Slot,
        input: Slot,
        model: usize,
    },
    EuclideanInput {
        template: Slot,
        fuel: Slot,
        model: usize,
    },
}
struct Machine<'a> {
    kernel: &'a mut Kernel,
    nodes: Vec<Thunk>,
    memo: Vec<Option<Slot>>,
    bindings: Vec<Binding>,
    frames: Vec<Frame>,
    globals: std::collections::BTreeMap<String, (Vec<Level>, T)>,
    depth: usize,
    euclidean_models: Vec<EuclideanModel>,
    euclidean_sources: Vec<(String, T, Environment)>,
    euclidean_free: Vec<(T, Vec<usize>)>,
    euclidean_checks: usize,
    euclidean_failures: usize,
}

fn reserve<E>(kernel: &mut Kernel, arena: &mut Vec<E>) -> Result<()> {
    if arena.len() != arena.capacity() {
        return Ok(());
    }
    let capacity = arena
        .capacity()
        .checked_mul(2)
        .ok_or("delayed arena capacity overflow")?
        .max(4);
    let bytes = capacity
        .checked_mul(std::mem::size_of::<E>())
        .and_then(|n| n.checked_add(64))
        .ok_or("delayed arena allocation overflow")?;
    // Charge the whole replacement allocation, including spare capacity,
    // before asking the allocator. Reusing an existing slot allocates nothing.
    kernel.charge_transformation(bytes)?;
    arena
        .try_reserve_exact(capacity - arena.len())
        .map_err(|_| "delayed arena allocation failed".to_owned())
}

impl Kernel {
    /// Observe a closed natural field before ordinary projection reduction
    /// substitutes a recursive record through each use of its earlier fields.
    /// Eligibility only schedules the existing evaluator; it must still
    /// compute the scalar from the checked constructor and recursor bodies.
    pub(in crate::proof::kernel) fn delayed_record_projection(
        &mut self,
        value: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        let Term::Project {
            family,
            index,
            subject,
        } = value.as_ref()
        else {
            return Ok(None);
        };
        if self.delayed_active
            || self.reduction_probe_budget.is_some()
            || self.delayed_projection_attempts >= 4
            || !matches!(
                subject.as_ref(),
                Term::App(..) | Term::Induct { .. } | Term::Project { .. }
            )
            || self.provisional_family(family)
            || self.nested.contains_key(family)?
        {
            return Ok(None);
        }
        let Some(eligible) = self.reduction_probe_limits(depth, 4096, 256 << 10, |kernel| {
            let Some(declaration) = kernel.declarations.get(family)? else {
                return Ok(false);
            };
            if !declaration.universes.is_empty() {
                return Ok(false);
            }
            let (record, _) = kernel.family(family, &[], depth + 1)?;
            if record.group.len() != 1
                || !record.indices.is_empty()
                || record.constructors.len() != 1
                || !record.sort.equivalent(&Level::number(1)?)?
                || record.constructors[0].recursive.iter().any(Option::is_some)
            {
                return Ok(false);
            }
            let Some(field) = record.constructors[0].fields.get(*index) else {
                return Ok(false);
            };
            let Term::Global(natural, levels) = field.as_ref() else {
                return Ok(false);
            };
            Ok(levels.is_empty()
                && kernel
                    .natural_recursor_family(natural, depth + 1)?
                    .is_some())
        })?
        else {
            return Ok(None);
        };
        if !eligible {
            return Ok(None);
        }
        self.delayed_projection_attempts += 1;
        self.delayed_closed_fold(value, depth + 1)
    }

    /// A checked scalar wrapper that packs a record for a tail call may hide
    /// an entire function-valued recursor. Observe the original application
    /// before eager head exposure substitutes through that computation.
    /// This is only an eligibility filter: the VM must compute the result.
    pub(in crate::proof::kernel) fn delayed_record_wrapper(
        &mut self,
        value: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        if self.delayed_active
            || !matches!(value.as_ref(), Term::App(..))
            || self.reduction_probe_budget.is_some()
            || self.delayed_wrapper_attempts >= 4
            || self.delayed_wrapper_checks >= 256
            || self
                .failed_wrapper_roots
                .iter()
                .any(|source| source.as_ptr() == Arc::as_ptr(value))
        {
            return Ok(None);
        }
        self.delayed_wrapper_checks += 1;
        let Some((family, compact_arithmetic)) = self
            .reduction_probe_limits(depth, 4096, 256 << 10, |kernel| {
                kernel.record_wrapper_candidate(value, depth + 1)
            })?
            .flatten()
        else {
            return Ok(None);
        };
        self.delayed_wrapper_attempts += 1;
        // Newly exposed scalar folds can still be affine (e.g. doubling).
        // Existing packed-state observations retain their original schedule.
        if compact_arithmetic {
            if let Some(number) = self.natural_probe_number(&family, value, depth + 1)? {
                self.charge_transformation(
                    TERM_NODE_BYTES + family.len() + number.decimal().len(),
                )?;
                return Ok(Some(term(Term::NatLiteral {
                    family,
                    value: number,
                })));
            }
        }
        // A declined observation still needs ordinary reduction. Preserve a
        // quarter of the remaining work and half the transformation allowance
        // instead of consuming the hard budget in an optional linear walk.
        let remaining_work = self.budget.work().saturating_sub(self.work);
        let remaining_bytes = self
            .budget
            .phase_bytes()
            .saturating_sub(self.transformed_bytes);
        let work = (remaining_work - remaining_work / 4).min(262_144);
        let bytes = (remaining_bytes / 2).min(32 * 1024 * 1024);
        let result = self.delayed_scalar_with_limits(value, depth + 1, work, bytes);
        if matches!(&result, Ok(None)) {
            self.remember_failed_wrapper(value)?;
        }
        result
    }

    fn remember_failed_wrapper(&mut self, value: &T) -> Result<()> {
        if self.failed_wrapper_roots.capacity() == 0 {
            let bytes = 64 + 4 * std::mem::size_of::<std::sync::Weak<TermNode>>();
            // A probe may stop with almost no enclosing allowance left. In
            // that case simply omit this optional scheduling hint.
            if self
                .budget
                .phase_bytes()
                .saturating_sub(self.transformed_bytes)
                <= bytes
            {
                return Ok(());
            }
            self.charge_transformation(bytes)?;
            self.failed_wrapper_roots
                .try_reserve_exact(4)
                .map_err(|_| "failed-wrapper table allocation failed")?;
        }
        // At most four wide attempts occur per phase. A Weak keeps an old
        // address from matching a different allocation without retaining the
        // expression graph. Successful results and genuine errors aren't cached.
        self.failed_wrapper_roots.push(Arc::downgrade(value));
        Ok(())
    }

    fn record_wrapper_candidate(
        &mut self,
        value: &T,
        depth: usize,
    ) -> Result<Option<(String, bool)>> {
        let mut value = value.clone();
        let mut pending = 0;
        let mut result_type = None;
        let mut root_parameters = None;
        // Follow checked call templates without substituting their arguments.
        // Only the original root's complete scalar result controls scheduling.
        for _ in 0..8 {
            let mut head = &value;
            let mut count = pending;
            while let Term::App(function, _) = head.as_ref() {
                self.tick(depth)?;
                count += 1;
                if count > 32 {
                    return Ok(None);
                }
                head = function;
            }
            let Term::Global(name, levels) = head.as_ref() else {
                return Ok(None);
            };
            let Some(declaration) = self.declarations.get(name)? else {
                return Ok(None);
            };
            if declaration.universes.len() != levels.len() {
                return Err(format!(
                    "'{name}' requires {} explicit universe argument(s)",
                    declaration.universes.len()
                ));
            }
            let Some(mut body) = declaration.value.as_ref() else {
                return Ok(None);
            };
            if result_type.is_none() {
                let mut ty = &declaration.ty;
                for _ in 0..count {
                    self.tick(depth)?;
                    let Term::Pi(_, range) = ty.as_ref() else {
                        return Ok(None);
                    };
                    ty = range;
                }
                result_type = Some(ty.clone());
                root_parameters = Some((declaration.ty.clone(), count));
            }
            pending = count;
            while pending > 0 {
                self.tick(depth)?;
                let Term::Lam(_, next) = body.as_ref() else {
                    break;
                };
                body = next;
                pending -= 1;
            }
            let packed_record = pending == 0 && self.record_tail_candidate(body, depth + 1)?;
            let applied_fold = self.delayed_candidate(body)
                || pending > 0
                    && matches!(
                        body.as_ref(),
                        Term::Project { index: 0, .. } | Term::Induct { .. }
                    );
            if packed_record || applied_fold {
                let Term::Global(result, levels) = result_type.as_ref().unwrap().as_ref() else {
                    return Ok(None);
                };
                if !levels.is_empty() || metadata::natural(self, result, depth + 1)?.is_none() {
                    return Ok(None);
                }
                if !packed_record {
                    // History/function step workers keep their existing path.
                    // New fold forwarding requires scalar root parameters.
                    let (root_type, count) = root_parameters.as_ref().unwrap();
                    let mut ty = root_type;
                    for _ in 0..*count {
                        let Term::Pi(domain, range) = ty.as_ref() else {
                            return Ok(None);
                        };
                        let Term::Global(family, levels) = domain.as_ref() else {
                            return Ok(None);
                        };
                        if !levels.is_empty()
                            || metadata::natural(self, family, depth + 1)?.is_none()
                        {
                            return Ok(None);
                        }
                        ty = range;
                    }
                }
                self.charge_transformation(64 + result.len())?;
                return Ok(Some((result.clone(), !packed_record)));
            }
            value = body.clone();
        }
        Ok(None)
    }

    fn record_tail_candidate(&mut self, value: &T, depth: usize) -> Result<bool> {
        let Term::App(function, record) = value.as_ref() else {
            return Ok(false);
        };
        let mut head = function;
        let mut count = 0;
        while let Term::App(function, _) = head.as_ref() {
            self.tick(depth)?;
            count += 1;
            if count > 32 {
                return Ok(false);
            }
            head = function;
        }
        if !matches!(head.as_ref(), Term::Global(..)) {
            return Ok(false);
        }
        let Some(record) = self.record_constructor_template(record, depth + 1)? else {
            return Ok(false);
        };
        let Term::Ctor {
            family,
            levels,
            parameters,
            constructor,
            fields,
        } = record.as_ref()
        else {
            return Ok(false);
        };
        if fields.is_empty()
            || self.provisional_family(family)
            || self.nested.contains_key(family)?
        {
            return Ok(false);
        }
        let (owner, _) = metadata::family(self, family, levels, depth + 1)?;
        let desc = owner.family.as_ref().expect("checked family");
        if desc.group.len() != 1
            || !desc.indices.is_empty()
            || desc.constructors.len() != 1
            || parameters.len() != desc.parameters.len()
        {
            return Ok(false);
        }
        let ctor = &desc.constructors[0];
        self.charge_work(ctor.recursive.len())?;
        Ok(&ctor.name == constructor
            && ctor.fields.len() == fields.len()
            && ctor.recursive.iter().all(Option::is_none))
    }

    /// Exported constructors can be checked lambda wrappers around a Ctor.
    /// Return only their shape for scheduling; an uninstantiated template is
    /// never a reduction result and its fields are never inspected as values.
    fn record_constructor_template(&mut self, value: &T, depth: usize) -> Result<Option<T>> {
        if matches!(value.as_ref(), Term::Ctor { .. }) {
            return Ok(Some(value.clone()));
        }
        let mut head = value;
        let mut count = 0;
        while let Term::App(function, _) = head.as_ref() {
            self.tick(depth)?;
            count += 1;
            if count > 32 {
                return Ok(None);
            }
            head = function;
        }
        let Term::Global(name, levels) = head.as_ref() else {
            return Ok(None);
        };
        let Some(declaration) = self.declarations.get(name)? else {
            return Ok(None);
        };
        let Some(mut body) = declaration.value.as_ref() else {
            return Ok(None);
        };
        if declaration.universes.len() != levels.len() {
            return Ok(None);
        }
        for _ in 0..count {
            self.tick(depth)?;
            let Term::Lam(_, next) = body.as_ref() else {
                return Ok(None);
            };
            body = next;
        }
        Ok(matches!(body.as_ref(), Term::Ctor { .. }).then(|| body.clone()))
    }

    /// Try only after ordinary arithmetic exposure has stopped at an applied
    /// recursor or projection. Scalar affine/power folds retain their fast path.
    pub(in crate::proof::kernel) fn delayed_candidate(&self, value: &T) -> bool {
        let mut head = value;
        let mut arguments = 0;
        while let Term::App(function, _) = head.as_ref() {
            arguments += 1;
            if arguments > 32 {
                return false;
            }
            head = function;
        }
        if arguments == 0 {
            return false;
        }
        match head.as_ref() {
            Term::Project { .. } => true,
            Term::Induct { motive, .. } => {
                let Term::Lam(_, result) = motive.as_ref() else {
                    return false;
                };
                let mut result = result;
                for _ in 0..arguments {
                    let Term::Pi(_, body) = result.as_ref() else {
                        return false;
                    };
                    result = body;
                }
                // A partial function is not a scalar result. Do not spend a
                // closure probe just to discover another lambda at its head.
                matches!(result.as_ref(), Term::Global(..))
            }
            _ => false,
        }
    }

    pub(in crate::proof::kernel) fn delayed_scalar(
        &mut self,
        value: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        self.delayed_scalar_with_limits(value, depth, 65_536, 8 * 1024 * 1024)
    }

    /// A closed scalar fold reaches this after affine/subtraction decline.
    /// Reuse the existing wide observation allowance,
    /// retaining fallback reserves and all enclosing hard/probe limits.
    pub(in crate::proof::kernel) fn delayed_closed_fold(
        &mut self,
        value: &T,
        depth: usize,
    ) -> Result<Option<T>> {
        let work = self.budget.work().saturating_sub(self.work);
        let bytes = self
            .budget
            .phase_bytes()
            .saturating_sub(self.transformed_bytes);
        self.delayed_scalar_with_limits(
            value,
            depth,
            (work - work / 4).min(262_144),
            (bytes / 2).min(32 << 20),
        )
    }

    fn delayed_scalar_with_limits(
        &mut self,
        value: &T,
        depth: usize,
        work: usize,
        bytes: usize,
    ) -> Result<Option<T>> {
        // Nested probes inherit the parent's limits. The operation guard also
        // prevents reentry through declaration/family helpers inside this VM.
        if self.delayed_active {
            return Ok(None);
        }
        self.delayed_active = true;
        let result = self.reduction_probe_limits(depth, work, bytes, |kernel| {
            let mut machine = Machine {
                kernel,
                nodes: vec![],
                memo: vec![],
                bindings: vec![],
                frames: vec![],
                globals: std::collections::BTreeMap::new(),
                depth: depth + 1,
                euclidean_models: vec![],
                euclidean_sources: vec![],
                euclidean_free: vec![],
                euclidean_checks: 0,
                euclidean_failures: 0,
            };
            let root = machine.source(value.clone(), None)?;
            machine.run(root)
        });
        self.delayed_active = false;
        Ok(result?.flatten())
    }
}

impl Machine<'_> {
    fn node(&mut self, node: Thunk) -> Result<Slot> {
        reserve(self.kernel, &mut self.nodes)?;
        reserve(self.kernel, &mut self.memo)?;
        let index = self.nodes.len();
        self.nodes.push(node);
        self.memo.push(None);
        Ok(index)
    }
    fn source(&mut self, value: T, environment: Environment) -> Result<Slot> {
        self.node(Thunk::Source(value, environment))
    }
    fn bind(&mut self, value: Slot, parent: Environment) -> Result<Environment> {
        reserve(self.kernel, &mut self.bindings)?;
        let index = self.bindings.len();
        self.bindings.push(Binding { value, parent });
        Ok(Some(index))
    }
    fn push(&mut self, frame: Frame) -> Result<()> {
        reserve(self.kernel, &mut self.frames)?;
        self.frames.push(frame);
        Ok(())
    }
    fn source_at(&self, slot: Slot) -> (T, Environment) {
        let Thunk::Source(value, environment) = &self.nodes[slot] else {
            unreachable!("source template");
        };
        (value.clone(), *environment)
    }
    fn number(&mut self, family: &str, value: Natural) -> Result<Slot> {
        self.kernel
            .charge_transformation(TERM_NODE_BYTES + family.len() + value.decimal().len())?;
        self.source(
            term(Term::NatLiteral {
                family: family.into(),
                value,
            }),
            None,
        )
    }
    fn variable(&mut self, mut environment: Environment, mut index: usize) -> Result<Option<Slot>> {
        while let Some(at) = environment {
            self.kernel.tick(self.depth)?;
            let binding = &self.bindings[at];
            if index == 0 {
                return Ok(Some(binding.value));
            }
            index -= 1;
            environment = binding.parent;
        }
        Ok(None)
    }

    fn force(&mut self, slot: Slot) -> Result<Slot> {
        if let Some(result) = self.memo[slot] {
            return Ok(result);
        }
        let immediate = matches!(&self.nodes[slot], Thunk::Source(value, _) if matches!(value.as_ref(),
            Term::Lam(..) | Term::Ctor { .. } | Term::Pair(..) | Term::NatLiteral { .. }
                | Term::Sort(_) | Term::Refl(..)));
        if !immediate {
            self.push(Frame::Update(slot))?;
        }
        Ok(slot)
    }

    fn run(&mut self, mut current: Slot) -> Result<Option<T>> {
        loop {
            // Continuations live in a metered arena, not on the Rust call
            // stack. Real recursive helper calls still check their depth.
            self.kernel.tick(self.depth)?;
            if let Some(result) = self.memo[current] {
                current = result;
                continue;
            }
            let (value, environment, neutral) = match self.nodes[current].clone() {
                Thunk::Recursor { template, subject } => {
                    self.push(Frame::Induct(template))?;
                    current = self.force(subject)?;
                    continue;
                }
                Thunk::Indices {
                    template,
                    parameters,
                    position,
                } => {
                    let Some(next) = self.compare_index(template, parameters, position)? else {
                        return Ok(None);
                    };
                    current = next;
                    continue;
                }
                Thunk::Neutral(head) => (head, None, true),
                Thunk::Source(value, environment) => (value, environment, false),
            };
            if !neutral {
                match value.as_ref() {
                    Term::Var(index) => {
                        let Some(bound) = self.variable(environment, *index)? else {
                            return Ok(None);
                        };
                        current = self.force(bound)?;
                        continue;
                    }
                    Term::Global(name, levels) => {
                        let (declaration, map) =
                            metadata::specialization(self.kernel, name, levels, self.depth + 1)?;
                        if let Some(body) = &declaration.value {
                            let body = body.clone();
                            let body = if let Some((_, value)) =
                                self.globals.get(name).filter(|(key, _)| key == levels)
                            {
                                value.clone()
                            } else {
                                // Retain checked monomorphic templates too: a
                                // cold declaration table may decode an equal
                                // body at a fresh address on every lookup.
                                let body = if map.is_empty() {
                                    body
                                } else {
                                    self.kernel.universes(&body, &map, self.depth + 1)?
                                };
                                if self.globals.len() < 64 || self.globals.contains_key(name) {
                                    let bytes = levels.iter().fold(
                                        4096usize.saturating_add(name.len()).saturating_add(
                                            levels
                                                .len()
                                                .saturating_mul(std::mem::size_of::<Level>()),
                                        ),
                                        |bytes, level| {
                                            bytes.saturating_add(level.storage_memory_weight())
                                        },
                                    );
                                    self.kernel.charge_transformation(bytes)?;
                                    self.globals
                                        .insert(name.clone(), (levels.clone(), body.clone()));
                                }
                                body
                            };
                            // Checked global bodies have their own closed term scope.
                            current = self.source(body, None)?;
                            continue;
                        }
                    }
                    Term::App(function, argument) => {
                        let argument = self.source(argument.clone(), environment)?;
                        self.push(Frame::Apply(argument))?;
                        current = self.source(function.clone(), environment)?;
                        continue;
                    }
                    Term::Lam(_, body) => {
                        if let Some(Frame::Apply(argument)) = self.frames.last().copied() {
                            self.frames.pop();
                            let scope = self.bind(argument, environment)?;
                            current = self.source(body.clone(), scope)?;
                            continue;
                        }
                    }
                    Term::Let(_, definition, body) => {
                        let definition = self.source(definition.clone(), environment)?;
                        let scope = self.bind(definition, environment)?;
                        current = self.source(body.clone(), scope)?;
                        continue;
                    }
                    Term::Project { subject, .. } => {
                        self.push(Frame::Project(current))?;
                        current = self.source(subject.clone(), environment)?;
                        continue;
                    }
                    Term::First(pair) | Term::Second(pair) => {
                        self.push(if matches!(value.as_ref(), Term::First(_)) {
                            Frame::First
                        } else {
                            Frame::Second
                        })?;
                        current = self.source(pair.clone(), environment)?;
                        continue;
                    }
                    Term::Induct { subject, .. } => {
                        if self.begin_euclidean(current, &value)? {
                            current = self.source(subject.clone(), environment)?;
                            current = self.force(current)?;
                            continue;
                        }
                        self.push(Frame::Induct(current))?;
                        current = self.source(subject.clone(), environment)?;
                        continue;
                    }
                    Term::EqElim { proof, .. } => {
                        self.push(Frame::EqProof(current))?;
                        current = self.source(proof.clone(), environment)?;
                        continue;
                    }
                    _ => {}
                }
            }
            // Only scalar consumers force successor fields. Ordinary iota and
            // projections can discard a predecessor or other payload lazily.
            let scalar = matches!(
                self.frames.last(),
                None | Some(
                    Frame::EqLeft { .. }
                        | Frame::EqRight { .. }
                        | Frame::Successor(_)
                        | Frame::EuclideanFuel { .. }
                        | Frame::EuclideanInput { .. }
                )
            );
            if scalar && !neutral {
                if let Some(next) = self.compact_constructor(current, &value, environment)? {
                    current = next;
                    continue;
                }
            }
            let Some(frame) = self.frames.pop() else {
                return if neutral {
                    Ok(None)
                } else {
                    self.closed_leaf(&value, false)
                };
            };
            match frame {
                Frame::EuclideanFuel {
                    template,
                    input,
                    model,
                } => {
                    current =
                        self.euclidean_fuel(template, input, current, model, &value, neutral)?;
                }
                Frame::EuclideanInput {
                    template,
                    fuel,
                    model,
                } => {
                    current = self.euclidean_input(template, fuel, model, &value, neutral)?;
                }
                Frame::Update(original) => {
                    // Source templates stay immutable: recursive hypotheses
                    // can still refer to their original recursor after force.
                    if original != current {
                        self.memo[original] = Some(current);
                    }
                }
                Frame::Apply(_) => {
                    if neutral || matches!(value.as_ref(), Term::Global(..)) {
                        current = self.node(Thunk::Neutral(value))?;
                    } else {
                        return Ok(None);
                    }
                }
                Frame::Project(accessor) => {
                    let (accessor, _) = self.source_at(accessor);
                    if neutral {
                        current = self.node(Thunk::Neutral(accessor))?;
                        continue;
                    }
                    let Term::Project {
                        family: expected,
                        index,
                        ..
                    } = accessor.as_ref()
                    else {
                        unreachable!("projection frame");
                    };
                    let Term::Ctor { family, fields, .. } = value.as_ref() else {
                        current = self.node(Thunk::Neutral(accessor))?;
                        continue;
                    };
                    if expected != family {
                        return Ok(None);
                    }
                    let field = fields
                        .get(*index)
                        .cloned()
                        .ok_or("invalid record field index")?;
                    current = self.source(field, environment)?;
                }
                Frame::First | Frame::Second => {
                    if neutral {
                        current = self.node(Thunk::Neutral(value))?;
                        continue;
                    }
                    let Term::Pair(_, first, second) = value.as_ref() else {
                        current = self.node(Thunk::Neutral(value))?;
                        continue;
                    };
                    let selected = if matches!(frame, Frame::First) {
                        first
                    } else {
                        second
                    };
                    current = self.source(selected.clone(), environment)?;
                }
                Frame::Induct(template) => {
                    let Some(branch) = self.induct(template, &value, environment, neutral)? else {
                        let (source, _) = self.source_at(template);
                        current = self.node(Thunk::Neutral(source))?;
                        continue;
                    };
                    current = branch;
                }
                Frame::EqProof(template) => {
                    let (template, scope) = self.source_at(template);
                    let Term::EqElim {
                        base, left, right, ..
                    } = template.as_ref()
                    else {
                        unreachable!("equality frame");
                    };
                    let base = self.source(base.clone(), scope)?;
                    if !neutral && matches!(value.as_ref(), Term::Refl(..)) {
                        current = base;
                    } else {
                        let right = self.source(right.clone(), scope)?;
                        self.push(Frame::EqLeft { right, base })?;
                        current = self.source(left.clone(), scope)?;
                    }
                }
                Frame::EqLeft { right, base } => {
                    if neutral {
                        return Ok(None);
                    }
                    let Some(left) = self.closed_leaf(&value, true)? else {
                        return Ok(None);
                    };
                    let left = self.source(left, None)?;
                    self.push(Frame::EqRight { left, base })?;
                    current = right;
                }
                Frame::EqRight { left, base } => {
                    if neutral {
                        return Ok(None);
                    }
                    let Some(right) = self.closed_leaf(&value, true)? else {
                        return Ok(None);
                    };
                    let (left, _) = self.source_at(left);
                    if !self
                        .kernel
                        .convertible(&[], &left, &right, self.depth + 1)?
                    {
                        return Ok(None);
                    }
                    current = base;
                }
                Frame::Successor(source_slot) => {
                    if neutral {
                        return Ok(None);
                    }
                    let (source, _) = self.source_at(source_slot);
                    let Term::Ctor { family, .. } = source.as_ref() else {
                        unreachable!("successor frame");
                    };
                    let Term::NatLiteral {
                        family: actual,
                        value,
                    } = value.as_ref()
                    else {
                        return Ok(None);
                    };
                    if family != actual {
                        return Ok(None);
                    }
                    self.kernel.charge_work(value.decimal().len() + 1)?;
                    self.kernel
                        .charge_transformation(256 + value.decimal().len())?;
                    current = self.number(family, value.add(&Natural::parse("1")?)?)?;
                    self.memo[source_slot] = Some(current);
                }
            }
        }
    }

    fn closed_leaf(&mut self, value: &T, equality: bool) -> Result<Option<T>> {
        match value.as_ref() {
            Term::NatLiteral { family, .. } => {
                if self.kernel.provisional_family(family)
                    || self.kernel.nested.contains_key(family)?
                {
                    return Err("natural literal requires a completed natural-number family".into());
                }
                let (declaration, _) = metadata::family(self.kernel, family, &[], self.depth + 1)?;
                if !natural_shape(family, declaration.family.as_ref().expect("checked family"))? {
                    return Err("natural literal requires a parameterless Type-0 family with zero and successor constructors".into());
                }
                Ok(Some(value.clone()))
            }
            Term::Ctor {
                family,
                levels,
                parameters,
                constructor,
                fields,
            } if parameters.is_empty() && fields.is_empty() => {
                if self.kernel.provisional_family(family)
                    || self.kernel.nested.contains_key(family)?
                {
                    return Ok(None);
                }
                let (declaration, _) =
                    metadata::family(self.kernel, family, levels, self.depth + 1)?;
                let desc = declaration.family.as_ref().expect("checked family");
                self.kernel.charge_work(desc.constructors.len())?;
                if !desc
                    .constructors
                    .iter()
                    .any(|c| &c.name == constructor && c.fields.is_empty())
                {
                    return Err("invalid constructor for delayed scalar".into());
                }
                Ok(Some(value.clone()))
            }
            Term::Global(..) | Term::Sort(_) if equality => Ok(Some(value.clone())),
            _ => Ok(None),
        }
    }

    fn compact_constructor(
        &mut self,
        source: Slot,
        value: &T,
        environment: Environment,
    ) -> Result<Option<Slot>> {
        let Term::Ctor {
            family,
            levels,
            parameters,
            constructor,
            fields,
        } = value.as_ref()
        else {
            return Ok(None);
        };
        if !levels.is_empty() || !parameters.is_empty() {
            return Ok(None);
        }
        let Some(declaration) = metadata::natural(self.kernel, family, self.depth + 1)? else {
            return Ok(None);
        };
        let desc = declaration.family.as_ref().expect("natural family");
        if constructor == &desc.constructors[0].name && fields.is_empty() {
            let zero = self.number(family, Natural::parse("0")?)?;
            self.memo[source] = Some(zero);
            return Ok(Some(zero));
        }
        if constructor == &desc.constructors[1].name && fields.len() == 1 {
            self.push(Frame::Successor(source))?;
            return self.source(fields[0].clone(), environment).map(Some);
        }
        Ok(None)
    }

    fn induct(
        &mut self,
        template: Slot,
        value: &T,
        environment: Environment,
        neutral: bool,
    ) -> Result<Option<Slot>> {
        let (source, scope) = self.source_at(template);
        let Term::Induct {
            family,
            levels,
            parameters,
            indices,
            branches,
            ..
        } = source.as_ref()
        else {
            unreachable!("induction template");
        };
        if self.kernel.provisional_family(family) || self.kernel.nested.contains_key(family)? {
            return Ok(None);
        }
        let (declaration, _) = metadata::family(self.kernel, family, levels, self.depth + 1)?;
        let desc = declaration.family.as_ref().expect("checked family");
        if desc.group.len() != 1 {
            return Ok(None);
        }
        if parameters.len() != desc.parameters.len()
            || indices.len() != desc.indices.len()
            || branches.len() != desc.constructors.len()
        {
            return Err("induction parameter, index, or branch count mismatch".into());
        }
        if neutral {
            return self.neutral_induct(template, desc);
        }
        let (ordinal, mut fields, natural) = match value.as_ref() {
            Term::NatLiteral {
                family: actual,
                value,
            } if actual == family
                && levels.is_empty()
                && parameters.is_empty()
                && indices.is_empty() =>
            {
                if metadata::natural(self.kernel, family, self.depth + 1)?.is_none() {
                    return Ok(None);
                }
                self.kernel.charge_work(value.decimal().len() + 1)?;
                self.kernel
                    .charge_transformation(256 + value.decimal().len())?;
                match value.predecessor() {
                    None => (0, vec![], true),
                    Some(previous) => (1, vec![self.number(family, previous)?], true),
                }
            }
            Term::Ctor {
                family: actual,
                levels: actual_levels,
                parameters: actual_parameters,
                constructor,
                fields,
            } => {
                if actual != family
                    || !same_levels(levels, actual_levels)?
                    || actual_parameters.len() != parameters.len()
                {
                    return Ok(None);
                }
                self.kernel.charge_work(desc.constructors.len())?;
                let ordinal = desc
                    .constructors
                    .iter()
                    .position(|c| &c.name == constructor)
                    .ok_or("invalid induction constructor")?;
                if fields.len() != desc.constructors[ordinal].fields.len() {
                    return Err("invalid induction constructor field count".into());
                }
                let natural = metadata::natural(self.kernel, family, self.depth + 1)?.is_some();
                if !natural {
                    self.kernel
                        .charge_work(desc.constructors[ordinal].fields.len())?;
                    for (domain, target) in desc.constructors[ordinal]
                        .fields
                        .iter()
                        .zip(&desc.constructors[ordinal].recursive)
                    {
                        if let Some(target) = target {
                            // Only direct, non-indexed recursive fields of this
                            // family have the same recursor template. Indexed,
                            // mutual and function-valued recursion must use the
                            // ordinary dependent reduction instead.
                            let mut head = domain;
                            let mut argument_count = 0usize;
                            while let Term::App(function, _) = head.as_ref() {
                                self.kernel.tick(self.depth + 1)?;
                                argument_count = argument_count.saturating_add(1);
                                head = function;
                            }
                            if !indices.is_empty()
                                || !desc.indices.is_empty()
                                || target != family
                                || argument_count != parameters.len()
                                || !matches!(head.as_ref(), Term::Global(actual, actual_levels)
                                    if actual == family && same_levels(levels, actual_levels)?)
                            {
                                return Ok(None);
                            }
                        }
                    }
                }
                self.kernel
                    .charge_transformation(fields.len().saturating_mul(64))?;
                let mut arguments = Vec::with_capacity(fields.len().saturating_mul(2));
                for (field, target) in fields.iter().zip(&desc.constructors[ordinal].recursive) {
                    let field = self.source(field.clone(), environment)?;
                    arguments.push(field);
                    if !natural && target.is_some() {
                        arguments.push(self.node(Thunk::Recursor {
                            template,
                            subject: field,
                        })?);
                    }
                }
                (ordinal, arguments, natural)
            }
            _ => return self.neutral_induct(template, desc),
        };
        if natural && ordinal == 1 {
            let previous = *fields.first().ok_or("missing natural predecessor")?;
            let recursive = self.node(Thunk::Recursor {
                template,
                subject: previous,
            })?;
            fields.push(recursive);
        }
        for field in fields.into_iter().rev() {
            self.push(Frame::Apply(field))?;
        }
        self.source(branches[ordinal].clone(), scope).map(Some)
    }

    fn neutral_induct(&mut self, template: Slot, desc: &Family) -> Result<Option<Slot>> {
        if desc.constructors.len() != 1 || !desc.constructors[0].fields.is_empty() {
            return Ok(None);
        }
        let (source, scope) = self.source_at(template);
        let Term::Induct {
            family,
            levels,
            parameters,
            branches,
            ..
        } = source.as_ref()
        else {
            unreachable!("induction template");
        };
        if desc.indices.is_empty() {
            return self.source(branches[0].clone(), scope).map(Some);
        }
        let (_, map) = metadata::family(self.kernel, family, levels, self.depth + 1)?;
        // Match ordinary reduction exactly: indexed K is a Prop rule. A
        // singleton indexed datatype in Type cannot reduce a neutral subject.
        if !desc.sort.substitute(&map)?.zero() {
            return Ok(None);
        }
        let mut captured = None;
        for parameter in parameters {
            let value = self.source(parameter.clone(), scope)?;
            captured = self.bind(value, captured)?;
        }
        self.node(Thunk::Indices {
            template,
            parameters: captured,
            position: 0,
        })
        .map(Some)
    }

    fn compare_index(
        &mut self,
        template: Slot,
        captured: Environment,
        position: usize,
    ) -> Result<Option<Slot>> {
        let (source, scope) = self.source_at(template);
        let Term::Induct {
            family,
            levels,
            indices,
            branches,
            ..
        } = source.as_ref()
        else {
            unreachable!("induction template");
        };
        let Some(actual) = indices.get(position) else {
            return self.source(branches[0].clone(), scope).map(Some);
        };
        let (declaration, map) = metadata::family(self.kernel, family, levels, self.depth + 1)?;
        let desc = declaration.family.as_ref().expect("checked family");
        let expected = &desc.constructors[0].result_indices[position];
        let expected = if map.is_empty() {
            expected.clone()
        } else {
            self.kernel.universes(expected, &map, self.depth + 1)?
        };
        let right = self.source(expected, captured)?;
        let base = self.node(Thunk::Indices {
            template,
            parameters: captured,
            position: position + 1,
        })?;
        self.push(Frame::EqLeft { right, base })?;
        self.source(actual.clone(), scope).map(Some)
    }
}
