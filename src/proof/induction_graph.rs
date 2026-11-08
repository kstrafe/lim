//! Bounded changing reference graphs. References select existing locations;
//! no abstract referents are allocated. Every continuing/exit graph must be
//! covered by the enumerated loop heads, and all possible mutable targets are
//! included in every head's write frame, including targets lost by retargeting.
use super::*;
use induction_memory::{Changes, WriteFrame};

#[derive(Default)]
struct Pool {
    places: Vec<(Location, Type, bool)>,
    handles: Vec<Value>,
    bytes: usize,
    max_cases: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program("(#fn run () () (#return ()))").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        test(&mut Engine::new(&checked, &graph, Span::new(0, 0, 1, 1)));
    }

    fn changing_counter(
        engine: &mut Engine<'_, '_>,
    ) -> (State, Changes, Location, Location, Location) {
        let mut state = State::new();
        let left = engine
            .allocate(
                &mut state,
                Value::Bits(Circuit::constant(10, 8, false), Type::U8),
            )
            .unwrap();
        let ty = Type::Reference {
            mutable: true,
            target: Box::new(Type::U8),
        };
        engine
            .bind(
                &mut state,
                "current".into(),
                ty,
                Value::Ref {
                    place: left.clone(),
                    target: Type::U8,
                    mutable: true,
                    pinned: false,
                },
            )
            .unwrap();
        engine
            .bind(
                &mut state,
                "right".into(),
                Type::U8,
                Value::Bits(Circuit::constant(11, 8, false), Type::U8),
            )
            .unwrap();
        let locals = &state.frames.last().unwrap().locals;
        let current = locals["current"].0.clone();
        let right = locals["right"].0.clone();
        let changes = Changes {
            locals: BTreeSet::from(["current".into()]),
            borrowed: BTreeMap::from([("right".into(), true)]),
            memory: true,
            ..Changes::default()
        };
        (state, changes, current, left, right)
    }

    #[test]
    fn every_graph_head_havocs_both_past_and_future_mutable_targets() {
        with_engine(|engine| {
            let (entry, changes, _, left, right) = changing_counter(engine);
            let locals = entry.frames.last().unwrap().locals.clone();
            let heads = engine
                .induction_graph_states(entry.clone(), &locals, &changes)
                .unwrap();
            assert_eq!(heads.len(), 2);
            engine.induction_graph_covers(&heads, &entry).unwrap();
            for head in heads {
                assert_eq!(
                    head.heap.len(),
                    entry.heap.len(),
                    "abstraction must not allocate unrelated referents"
                );
                for place in [&left, &right] {
                    let old = engine.read(&entry, place).unwrap();
                    let new = engine.read(&head, place).unwrap();
                    let same = engine.equal(&old, &new).unwrap();
                    let changed = engine.circuit.and(head.guard, engine.circuit.not(same));
                    assert!(
                        engine.circuit.satisfy(changed).unwrap().is_some(),
                        "a target from another iteration was frozen"
                    );
                }
            }
        });
    }

    #[test]
    fn equal_contents_in_a_new_root_do_not_establish_reference_graph_coverage() {
        with_engine(|engine| {
            let (entry, changes, current, _, _) = changing_counter(engine);
            let locals = entry.frames.last().unwrap().locals.clone();
            let heads = engine
                .induction_graph_states(entry.clone(), &locals, &changes)
                .unwrap();
            let mut post = entry;
            let new = engine
                .allocate(
                    &mut post,
                    Value::Bits(Circuit::constant(10, 8, false), Type::U8),
                )
                .unwrap();
            engine
                .write(
                    &mut post,
                    &current,
                    Value::Ref {
                        place: new,
                        target: Type::U8,
                        mutable: true,
                        pinned: false,
                    },
                )
                .unwrap();
            let error = engine.induction_graph_covers(&heads, &post).unwrap_err();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::Unsupported)
            );
            post.guard = FALSE;
            engine.induction_graph_covers(&heads, &post).unwrap();
        });
    }

    #[test]
    fn representation_budget_is_checked_before_cloning_graph_combinations() {
        with_engine(|engine| {
            let (mut entry, mut changes, _, _, _) = changing_counter(engine);
            entry.frames.last_mut().unwrap().function = "x".repeat(4 * 1024 * 1024);
            for index in 0..20 {
                let name = format!("target-{index}");
                engine
                    .bind(
                        &mut entry,
                        name.clone(),
                        Type::U8,
                        Value::Bits(Circuit::constant(index, 8, false), Type::U8),
                    )
                    .unwrap();
                changes.borrowed.insert(name, true);
            }
            let locals = entry.frames.last().unwrap().locals.clone();
            let error = engine
                .induction_graph_states(entry, &locals, &changes)
                .err()
                .expect("unbounded fanout accepted");
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::ResourceLimit)
            );
            assert!(error.to_string().contains("64 MiB"), "{error}");
        });
    }

    #[test]
    fn readonly_borrow_sources_do_not_become_mutable_reference_choices() {
        with_engine(|engine| {
            let (entry, mut changes, _, _, right) = changing_counter(engine);
            changes.borrowed.insert("right".into(), false);
            let locals = entry.frames.last().unwrap().locals.clone();
            let heads = engine
                .induction_graph_states(entry.clone(), &locals, &changes)
                .unwrap();
            assert_eq!(heads.len(), 1);
            let old = engine.read(&entry, &right).unwrap();
            let current = engine.read(&heads[0], &right).unwrap();
            assert_eq!(engine.equal(&old, &current).unwrap(), TRUE);
        });
    }
}

const GRAPH_BYTES: usize = 64 * 1024 * 1024;
const LOCATION_BYTES: usize = 16 * 1024;

impl Engine<'_, '_> {
    fn graph_type_bytes(&mut self, ty: &Type, owned: bool, depth: usize) -> Result<usize> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction graph size nesting exceeds 32"));
        }
        let mut bytes = 1024 + std::mem::size_of::<Value>() + std::mem::size_of::<Type>();
        if !owned {
            match ty {
                Type::Named(name) => bytes = bytes.saturating_add(name.len()),
                Type::Reference { target, .. }
                | Type::PinnedReference { target, .. }
                | Type::Array(target, _)
                | Type::Slice(target)
                | Type::MutableSlice(target)
                | Type::RawPointer { target, .. }
                | Type::PinOwned(target)
                | Type::PinShared(target)
                | Type::Atomic(target) => {
                    bytes = bytes.saturating_add(self.graph_type_bytes(target, false, depth + 1)?)
                }
                Type::Tuple(types) => {
                    for ty in types {
                        bytes =
                            bytes.saturating_add(self.graph_type_bytes(ty, false, depth + 1)?);
                    }
                }
                _ => {}
            }
        } else {
            let ty = self.resolve_type(ty)?;
            match &ty {
                Type::Reference { target, .. }
                | Type::PinnedReference { target, .. }
                | Type::Slice(target)
                | Type::MutableSlice(target) => {
                    bytes = bytes
                        .saturating_add(LOCATION_BYTES)
                        .saturating_add(self.graph_type_bytes(target, false, depth + 1)?)
                }
                Type::RawPointer { target, .. }
                | Type::PinOwned(target)
                | Type::PinShared(target)
                | Type::Atomic(target) => {
                    bytes = bytes.saturating_add(self.graph_type_bytes(target, false, depth + 1)?)
                }
                Type::Array(element, len) => {
                    bytes = bytes.saturating_add(
                        self.graph_type_bytes(element, true, depth + 1)?
                            .saturating_mul(*len),
                    )
                }
                Type::Tuple(types) => {
                    for ty in types {
                        bytes = bytes.saturating_add(self.graph_type_bytes(ty, true, depth + 1)?);
                    }
                }
                Type::Named(name) if self.records.contains_key(name) => {
                    bytes = bytes.saturating_add(name.len());
                    for field in self.records[name].clone() {
                        bytes = bytes
                            .saturating_add(field.name.len())
                            .saturating_add(self.graph_type_bytes(&field.ty, true, depth + 1)?);
                    }
                }
                Type::Named(name) if self.enums.contains_key(name) => {
                    bytes = bytes.saturating_add(name.len());
                    for variant in self.enums[name].clone() {
                        bytes = bytes.saturating_add(32);
                        for ty in variant.fields {
                            bytes = bytes.saturating_add(self.graph_type_bytes(
                                &ty,
                                true,
                                depth + 1,
                            )?);
                        }
                    }
                }
                _ => {}
            }
        }
        if bytes > GRAPH_BYTES {
            return Err(Error::limit(
                "induction graph representation exceeds 64 MiB",
            ));
        }
        Ok(bytes)
    }

    fn graph_limit(&self, pool: &Pool, count: usize) -> Result<()> {
        self.limit_paths(count)?;
        if count > pool.max_cases {
            return Err(Error::limit(
                "induction graph retained states exceed 64 MiB",
            ));
        }
        Ok(())
    }

    fn graph_charge(&mut self, pool: &mut Pool, ty: &Type) -> Result<()> {
        pool.bytes = pool
            .bytes
            .saturating_add(LOCATION_BYTES)
            .saturating_add(self.graph_type_bytes(ty, false, 0)?);
        if pool.bytes > GRAPH_BYTES {
            return Err(Error::limit(
                "induction graph location catalog exceeds 64 MiB",
            ));
        }
        Ok(())
    }
    fn graph_layout(
        &mut self,
        pool: &mut Pool,
        place: Location,
        ty: &Type,
        mutable: bool,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction graph layout nesting exceeds 32"));
        }
        let ty = self.resolve_type(ty)?;
        if pool.places.iter().any(|(known, target, access)| {
            *access == mutable && *target == ty && self.same_location(known, &place) == TRUE
        }) {
            return Ok(());
        }
        if pool.places.len() >= 4096 {
            return Err(Error::limit("induction graph location budget exceeds 4096"));
        }
        self.graph_charge(pool, &ty)?;
        pool.places.push((place.clone(), ty.clone(), mutable));
        let fields = match &ty {
            Type::Named(name) if self.records.contains_key(name) => self.records[name]
                .iter()
                .enumerate()
                .map(|(index, field)| (Segment::Field(index), field.ty.clone()))
                .collect(),
            Type::Named(name) if self.enums.contains_key(name) => self.enums[name]
                .iter()
                .enumerate()
                .filter_map(|(index, variant)| {
                    variant
                        .fields
                        .first()
                        .map(|ty| (Segment::Payload(index), ty.clone()))
                })
                .collect(),
            Type::Tuple(types) => types
                .iter()
                .enumerate()
                .map(|(index, ty)| (Segment::Field(index), ty.clone()))
                .collect(),
            Type::Array(element, len) => {
                if *len > 64 {
                    return Err(Error::limit("induction graph arrays exceed 64 elements"));
                }
                (0..*len)
                    .map(|index| {
                        (
                            Segment::Index(Circuit::constant(index as u128, 64, false)),
                            (**element).clone(),
                        )
                    })
                    .collect()
            }
            _ => Vec::new(), // A reference's referent has a separate location.
        };
        for (segment, ty) in fields {
            let mut child = place.clone();
            child.path.push(segment);
            self.graph_layout(pool, child, &ty, mutable, depth + 1)?;
        }
        Ok(())
    }

    fn graph_handles(&mut self, pool: &mut Pool, value: &Value, depth: usize) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction graph value nesting exceeds 32"));
        }
        match value {
            Value::Ref {
                place,
                target,
                mutable,
                ..
            } => {
                if pool.handles.len() >= 4096 {
                    return Err(Error::limit("induction graph handle budget exceeds 4096"));
                }
                self.graph_charge(pool, &value.ty())?;
                pool.handles.push(value.clone());
                self.graph_layout(pool, place.clone(), target, *mutable, 0)?;
            }
            Value::Slice(_) => {
                if pool.handles.len() >= 4096 {
                    return Err(Error::limit("induction graph handle budget exceeds 4096"));
                }
                self.graph_charge(pool, &value.ty())?;
                pool.handles.push(value.clone());
                // Geometry is checked by the ordinary slice/frame model.
                // Its array layout is supplied separately by the source heap.
            }
            Value::Record(_, fields) => {
                for (_, value) in fields {
                    self.graph_handles(pool, value, depth + 1)?;
                }
            }
            Value::Array(_, values) | Value::Tuple(values) => {
                for value in values {
                    self.graph_handles(pool, value, depth + 1)?;
                }
            }
            Value::Enum(_, _, values) => {
                for value in values.iter().flatten() {
                    self.graph_handles(pool, value, depth + 1)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn graph_choices(&mut self, pool: &Pool, ty: &Type, state: &State) -> Result<Vec<Value>> {
        let ty = self.resolve_type(ty)?;
        let mut choices = Vec::new();
        let mut offer = |engine: &mut Self, value: Value| -> Result<()> {
            for known in &choices {
                if engine.induction_same_references(known, &value, 0)? == TRUE {
                    return Ok(());
                }
            }
            engine.graph_limit(pool, choices.len() + 1)?;
            choices.push(value);
            Ok(())
        };
        for value in &pool.handles {
            if self.resolve_type(&value.ty())? == ty {
                offer(self, value.clone())?;
            }
        }
        match &ty {
            Type::Reference { target, mutable } | Type::PinnedReference { target, mutable } => {
                let target = self.resolve_type(target)?;
                for (place, stored, access) in &pool.places {
                    if *stored == target
                        && (!mutable || *access)
                        && (!mutable
                            || !state
                                .globals
                                .values()
                                .any(|global| global.root == place.root))
                    {
                        offer(
                            self,
                            Value::Ref {
                                place: place.clone(),
                                target: target.clone(),
                                mutable: *mutable,
                                pinned: matches!(ty, Type::PinnedReference { .. }),
                            },
                        )?;
                    }
                }
            }
            Type::Slice(element) | Type::MutableSlice(element) => {
                let mutable = matches!(ty, Type::MutableSlice(_));
                let element = self.resolve_type(element)?;
                for (place, stored, access) in &pool.places {
                    let Type::Array(stored, len) = stored else {
                        continue;
                    };
                    if self.resolve_type(stored)? != element || (mutable && !access) {
                        continue;
                    }
                    for start in 0..=*len {
                        for end in start..=*len {
                            offer(
                                self,
                                Value::Slice(Slice {
                                    place: place.clone(),
                                    element: element.clone(),
                                    mutable,
                                    start: Circuit::constant(start as u128, 64, false),
                                    len: Circuit::constant((end - start) as u128, 64, false),
                                }),
                            )?;
                        }
                    }
                }
            }
            _ => {
                return Err(Error::checker(
                    "induction graph requested a non-handle choice",
                ))
            }
        }
        Ok(choices)
    }

    fn graph_leaf_types(&mut self, ty: &Type, pending: &mut Vec<Type>, depth: usize) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction graph type nesting exceeds 32"));
        }
        let ty = self.resolve_type(ty)?;
        match &ty {
            Type::Reference { .. }
            | Type::PinnedReference { .. }
            | Type::Slice(_)
            | Type::MutableSlice(_) => pending.push(ty),
            Type::Array(element, len) if *len != 0 => {
                self.graph_leaf_types(element, pending, depth + 1)?
            }
            Type::Tuple(types) => {
                for ty in types {
                    self.graph_leaf_types(ty, pending, depth + 1)?;
                }
            }
            Type::Named(name) if self.records.contains_key(name) => {
                for field in self.records[name].clone() {
                    self.graph_leaf_types(&field.ty, pending, depth + 1)?;
                }
            }
            Type::Named(name) if self.enums.contains_key(name) => {
                for variant in self.enums[name].clone() {
                    for ty in variant.fields {
                        self.graph_leaf_types(&ty, pending, depth + 1)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn graph_region(&mut self, places: &mut Vec<Location>, mut place: Location) -> Result<()> {
        // Coarsen conditional payloads and symbolic indices to initialized
        // enclosing storage. Never write a field of an absent enum variant.
        if let Some(index) = place.path.iter().position(|segment| {
            matches!(segment, Segment::Payload(_))
                || matches!(segment, Segment::Index(index) if index.bits.iter().any(|bit| *bit > TRUE))
        }) {
            place.path.truncate(index);
        }
        let covers = |engine: &mut Self, a: &Location, b: &Location| {
            a.root == b.root
                && a.path.len() <= b.path.len()
                && engine.same_location(
                    a,
                    &Location {
                        root: b.root,
                        path: b.path[..a.path.len()].to_vec(),
                    },
                ) == TRUE
        };
        if places.iter().any(|known| covers(self, known, &place)) {
            return Ok(());
        }
        places.retain(|known| !covers(self, &place, known));
        if places.len() >= 256 {
            return Err(Error::limit(
                "induction graph write frame exceeds 256 regions",
            ));
        }
        places.push(place);
        Ok(())
    }

    fn graph_values(
        &mut self,
        mut state: State,
        ty: &Type,
        pool: &Pool,
        depth: usize,
    ) -> Result<Vec<(State, Value)>> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit(
                "induction graph abstraction nesting exceeds 32",
            ));
        }
        let ty = self.resolve_type(ty)?;
        if !self.handle_type(&ty, 0)? {
            let value = self.fresh_value(&mut state, &ty, 0)?;
            return Ok(vec![(state, value)]);
        }
        if matches!(
            ty,
            Type::Reference { .. }
                | Type::PinnedReference { .. }
                | Type::Slice(_)
                | Type::MutableSlice(_)
        ) {
            return Ok(self
                .graph_choices(pool, &ty, &state)?
                .into_iter()
                .map(|value| (state.clone(), value))
                .collect());
        }
        if let Type::Named(name) = &ty {
            if let Some(variants) = self.enums.get(name).cloned() {
                let mut output = Vec::new();
                for (index, variant) in variants.iter().enumerate() {
                    let runs = if let Some(ty) = variant.fields.first() {
                        self.graph_values(state.clone(), ty, pool, depth + 1)?
                    } else {
                        vec![(state.clone(), Value::Unit)]
                    };
                    for (state, value) in runs {
                        let value = self.construct_enum(
                            name,
                            index,
                            (!variant.fields.is_empty()).then_some(value),
                        )?;
                        output.push((state, value));
                        self.graph_limit(pool, output.len())?;
                    }
                }
                return Ok(output);
            }
        }
        let fields = match &ty {
            Type::Named(name) if self.records.contains_key(name) => self.records[name]
                .iter()
                .map(|field| field.ty.clone())
                .collect(),
            Type::Array(element, len) => vec![(**element).clone(); *len],
            Type::Tuple(types) => types.clone(),
            _ => {
                return Err(Error::unsupported(
                    "induction graph cannot abstract this aggregate",
                ))
            }
        };
        let mut runs = vec![(state, Vec::new())];
        for field in fields {
            let mut next = Vec::new();
            for (state, values) in runs {
                for (state, value) in self.graph_values(state, &field, pool, depth + 1)? {
                    let mut values = values.clone();
                    values.push(value);
                    next.push((state, values));
                    self.graph_limit(pool, next.len())?;
                }
            }
            runs = next;
        }
        Ok(runs
            .into_iter()
            .map(|(state, values)| {
                let value = match &ty {
                    Type::Named(name) => Value::Record(
                        name.clone(),
                        self.records[name]
                            .iter()
                            .map(|field| field.name.clone())
                            .zip(values)
                            .collect(),
                    ),
                    Type::Array(element, _) => Value::Array((**element).clone(), values),
                    Type::Tuple(_) => Value::Tuple(values),
                    _ => unreachable!(),
                };
                (state, value)
            })
            .collect())
    }

    pub(super) fn induction_state_bytes(&mut self, state: &State) -> Result<usize> {
        // Include B-tree storage for input referent provenance in clone budgets.
        let mut state_bytes =
            1usize.saturating_add(state.abstract_referent_count().saturating_mul(64));
        for value in state
            .heap
            .iter()
            .chain(std::iter::once(&state.value))
            .chain(state.result.iter())
        {
            state_bytes =
                state_bytes.saturating_add(self.graph_type_bytes(&value.ty(), true, 0)?);
            if let Value::Claim(evidence) = value {
                for witness in &evidence.witnesses {
                    state_bytes = state_bytes.saturating_add(witness.text.len());
                }
            }
        }
        for frame in &state.frames {
            state_bytes = state_bytes.saturating_add(frame.function.len());
            for (name, (_, ty)) in &frame.locals {
                state_bytes = state_bytes
                    .saturating_add(name.len())
                    .saturating_add(LOCATION_BYTES)
                    .saturating_add(self.graph_type_bytes(ty, false, 0)?);
            }
        }
        for name in state.globals.keys() {
            state_bytes = state_bytes
                .saturating_add(name.len())
                .saturating_add(LOCATION_BYTES);
        }
        for fact in &state.validations {
            state_bytes = state_bytes.saturating_add(fact.retained_bytes());
        }
        Ok(state_bytes)
    }

    pub(super) fn induction_graph_states(
        &mut self,
        state: State,
        locals: &BTreeMap<String, (Location, Type)>,
        changes: &Changes,
    ) -> Result<Vec<State>> {
        let state_bytes = self.induction_state_bytes(&state)?;
        if state_bytes > GRAPH_BYTES {
            return Err(Error::limit(
                "induction graph retained states exceed 64 MiB",
            ));
        }
        let mut pool = Pool {
            max_cases: (GRAPH_BYTES / state_bytes).min(256),
            ..Pool::default()
        };
        for value in &state.heap {
            self.graph_handles(&mut pool, value, 0)?;
        }
        // Explicitly borrowed owned sources can introduce addresses not already
        // carried by a handle. Iteration-local storage is not a stable target.
        for (name, mutable) in &changes.borrowed {
            if let Some((place, ty)) = locals.get(name) {
                self.graph_layout(&mut pool, place.clone(), ty, *mutable, 0)?;
            }
        }
        for handle in pool.handles.clone() {
            if let Value::Slice(view) = handle {
                let value = self.read(&state, &view.place)?;
                self.graph_layout(&mut pool, view.place, &value.ty(), view.mutable, 0)?;
            }
        }
        let mut frame = WriteFrame::default();
        if changes.memory {
            for (place, _) in locals.values() {
                let value = self.read(&state, place)?;
                self.induction_reachable(&state, &value, TRUE, &mut frame, 0)?;
            }
        }
        let mut places = Vec::new();
        for name in &changes.locals {
            if let Some((place, _)) = locals.get(name) {
                self.graph_region(&mut places, place.clone())?;
            } else if self.globals.contains_key(name)
                || self.constants.contains_key(name)
                || state.globals.contains_key(name)
            {
                return Err(Error::unsupported("induction cannot havoc global storage"));
            }
        }
        for (place, _) in frame.regions {
            self.graph_region(&mut places, place)?;
        }
        let mut pending = Vec::new();
        for place in &places {
            let value = self.read(&state, place)?;
            self.graph_leaf_types(&value.ty(), &mut pending, 0)?;
        }
        let mut seen = Vec::new();
        while let Some(ty) = pending.pop() {
            self.tick()?;
            if seen.contains(&ty) {
                continue;
            }
            seen.push(ty.clone());
            let choices = self.graph_choices(&pool, &ty, &state)?;
            for value in choices {
                match value {
                    Value::Ref {
                        place,
                        target,
                        mutable,
                        ..
                    } => {
                        if mutable {
                            self.graph_region(&mut places, place)?;
                        }
                        self.graph_leaf_types(&target, &mut pending, 0)?;
                    }
                    Value::Slice(view) => {
                        if view.mutable {
                            self.graph_region(&mut places, view.place)?;
                        }
                        self.graph_leaf_types(&view.element, &mut pending, 0)?;
                    }
                    _ => unreachable!(),
                }
            }
            // A newly writable enclosing enum/array may add further handles.
            for place in &places {
                let value = self.read(&state, place)?;
                self.graph_leaf_types(&value.ty(), &mut pending, 0)?;
            }
        }
        if places.iter().any(|place| {
            state
                .globals
                .values()
                .any(|global| global.root == place.root)
        }) {
            return Err(Error::unsupported(
                "induction cannot havoc global storage through an alias",
            ));
        }
        let mut runs = vec![state];
        for place in places {
            let mut next = Vec::new();
            for state in runs {
                let previous = self.read(&state, &place)?;
                for (mut state, value) in self.graph_values(state, &previous.ty(), &pool, 0)? {
                    self.write(&mut state, &place, value)?;
                    next.push(state);
                    self.graph_limit(&pool, next.len())?;
                }
            }
            runs = next;
        }
        if runs.is_empty() {
            return Err(Error::unsupported(
                "no bounded reference graph covers this loop",
            ));
        }
        Ok(runs)
    }

    pub(super) fn induction_graph_covers(&mut self, heads: &[State], state: &State) -> Result<()> {
        let mut covered = FALSE;
        for head in heads {
            let matches = self.induction_reference_relation(head, state)?;
            covered = self.circuit.or(covered, matches);
        }
        let bad = self.circuit.and(state.guard, self.circuit.not(covered));
        if self.circuit.satisfy(bad)?.is_some() {
            return Err(Error::unsupported(
                "loop reference graph is outside the bounded induction abstraction",
            ));
        }
        Ok(())
    }
}
