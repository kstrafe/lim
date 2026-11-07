//! Abstract loop data without inventing new reference identities. This bounded
//! model requires the reference graph to remain stable on every modeled step.
use super::*;

#[derive(Default)]
pub(super) struct Changes {
    pub locals: BTreeSet<String>,
    pub memory: bool,
}

#[derive(Default)]
struct WriteFrame {
    regions: Vec<(Location, Bit)>,
    seen: Vec<(Location, Bit)>,
    visits: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program("(#fn run () () (#return ()))").unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        test(&mut Engine::new(
            &checked,
            &graph,
            crate::Span::new(0, 0, 1, 1),
        ));
    }

    fn backing(engine: &mut Engine<'_, '_>, state: &mut State) -> Location {
        engine
            .allocate(
                state,
                Value::Array(
                    Type::U8,
                    (10..13)
                        .map(|value| Value::Bits(Circuit::constant(value, 8, false), Type::U8))
                        .collect(),
                ),
            )
            .unwrap()
    }

    fn bind_view(
        engine: &mut Engine<'_, '_>,
        state: &mut State,
        place: Location,
        start: Word,
        len: Word,
    ) {
        let view = Slice {
            place,
            start,
            len,
            element: Type::U8,
            mutable: true,
        };
        engine
            .bind(
                state,
                "z-view".into(),
                Type::MutableSlice(Box::new(Type::U8)),
                Value::Slice(view),
            )
            .unwrap();
    }

    #[test]
    fn slice_frames_preserve_outside_elements_for_every_bounded_range() {
        with_engine(|engine| {
            for start in 0..=3 {
                for end in start..=3 {
                    let mut entry = State::new();
                    let array = backing(engine, &mut entry);
                    bind_view(
                        engine,
                        &mut entry,
                        array.clone(),
                        Circuit::constant(start, 64, false),
                        Circuit::constant(end - start, 64, false),
                    );
                    let locals = entry.frames.last().unwrap().locals.clone();
                    let changes = Changes {
                        memory: true,
                        ..Changes::default()
                    };
                    let post = engine
                        .induction_memory_states(entry.clone(), &locals, &changes)
                        .unwrap()
                        .pop()
                        .unwrap();
                    for index in 0..3 {
                        let mut place = array.clone();
                        place
                            .path
                            .push(Segment::Index(Circuit::constant(index, 64, false)));
                        let old = engine.read(&entry, &place).unwrap();
                        let new = engine.read(&post, &place).unwrap();
                        let same = engine.equal(&old, &new).unwrap();
                        let changed = engine.circuit.and(post.guard, engine.circuit.not(same));
                        assert_eq!(
                            engine.circuit.satisfy(changed).unwrap().is_some(),
                            start <= index && index < end,
                            "range={start}..{end} index={index}"
                        );
                    }
                }
            }
        });
    }

    #[test]
    fn inactive_slice_writes_cannot_restore_stale_overlapping_parent_data() {
        with_engine(|engine| {
            let mut entry = State::new();
            let array = backing(engine, &mut entry);
            let target = Type::Array(Box::new(Type::U8), 3);
            engine
                .bind(
                    &mut entry,
                    "a-source".into(),
                    Type::Reference {
                        mutable: true,
                        target: Box::new(target.clone()),
                    },
                    Value::Ref {
                        place: array.clone(),
                        target,
                        mutable: true,
                        pinned: false,
                    },
                )
                .unwrap();
            let start = engine.circuit.word(64, false);
            let beyond = engine
                .circuit
                .lt_word(&Circuit::constant(2, 64, false), &start);
            entry.guard = engine.circuit.not(beyond);
            bind_view(
                engine,
                &mut entry,
                array.clone(),
                start.clone(),
                Circuit::constant(1, 64, false),
            );
            let locals = entry.frames.last().unwrap().locals.clone();
            let changes = Changes {
                memory: true,
                ..Changes::default()
            };
            let post = engine
                .induction_memory_states(entry.clone(), &locals, &changes)
                .unwrap()
                .pop()
                .unwrap();
            for index in 0..3 {
                let mut place = array.clone();
                place
                    .path
                    .push(Segment::Index(Circuit::constant(index, 64, false)));
                let old = engine.read(&entry, &place).unwrap();
                let new = engine.read(&post, &place).unwrap();
                let same = engine.equal(&old, &new).unwrap();
                let inside = engine
                    .circuit
                    .eq_word(&start, &Circuit::constant(index, 64, false));
                let outside = engine.circuit.and(post.guard, engine.circuit.not(inside));
                let changed = engine.circuit.and(outside, engine.circuit.not(same));
                assert!(
                    engine.circuit.satisfy(changed).unwrap().is_some(),
                    "index={index}"
                );
            }
        });
    }

    #[test]
    fn invalid_or_wrapped_slice_geometry_cannot_enter_a_loop_frame() {
        with_engine(|engine| {
            for (start, len) in [(4, 0), (0, 4), (u64::MAX as u128, 1)] {
                let mut state = State::new();
                let array = backing(engine, &mut state);
                bind_view(
                    engine,
                    &mut state,
                    array,
                    Circuit::constant(start, 64, false),
                    Circuit::constant(len, 64, false),
                );
                let locals = state.frames.last().unwrap().locals.clone();
                let changes = Changes {
                    memory: true,
                    ..Changes::default()
                };
                let error = engine
                    .induction_memory_states(state, &locals, &changes)
                    .err()
                    .expect("invalid view accepted");
                assert!(error.to_string().contains("slice geometry"), "{error}");
            }
        });
    }

    #[test]
    fn changing_slice_backing_start_or_length_cannot_preserve_a_loop_graph() {
        with_engine(|engine| {
            let mut entry = State::new();
            let array = backing(engine, &mut entry);
            let other = backing(engine, &mut entry);
            bind_view(
                engine,
                &mut entry,
                array.clone(),
                Circuit::constant(0, 64, false),
                Circuit::constant(2, 64, false),
            );
            let place = entry.frames.last().unwrap().locals["z-view"].0.clone();
            for (backing, start, len) in [(other, 0, 2), (array.clone(), 1, 2), (array, 0, 1)] {
                let mut post = entry.clone();
                engine
                    .write(
                        &mut post,
                        &place,
                        Value::Slice(Slice {
                            place: backing,
                            element: Type::U8,
                            mutable: true,
                            start: Circuit::constant(start, 64, false),
                            len: Circuit::constant(len, 64, false),
                        }),
                    )
                    .unwrap();
                let error = engine.induction_reference_shape(&entry, &post).unwrap_err();
                assert_eq!(
                    error.diagnostic_code(),
                    crate::DiagnosticCode::ProofUnsupported
                );
            }
        });
    }

    #[test]
    fn an_indirect_global_destination_cannot_enter_an_ordinary_loop_frame() {
        let program =
            crate::parse_program("(#fn run (: target (#ref-mut #u8)) () (#return ()))").unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, crate::Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let ty = Type::Reference {
            mutable: true,
            target: Box::new(Type::U8),
        };
        let value = engine.fresh_value(&mut state, &ty, 0).unwrap();
        let Value::Ref { place, .. } = &value else {
            panic!("reference expected")
        };
        // Unsafe/external models must not make globals ordinary input regions.
        state.globals.insert("hidden-global".into(), place.clone());
        engine.bind(&mut state, "target".into(), ty, value).unwrap();
        let locals = state.frames.last().unwrap().locals.clone();
        let changes = Changes {
            memory: true,
            ..Changes::default()
        };
        let error = engine
            .induction_memory_states(state, &locals, &changes)
            .err()
            .expect("global frame accepted");
        assert_eq!(
            error.diagnostic_code(),
            crate::DiagnosticCode::ProofUnsupported
        );
        assert!(error
            .to_string()
            .contains("global storage through an alias"));
    }
}

impl Engine<'_, '_> {
    pub(super) fn induction_memory_states(
        &mut self,
        state: State,
        locals: &BTreeMap<String, (Location, Type)>,
        changes: &Changes,
    ) -> Result<Vec<State>> {
        let mut roots = Vec::new();
        for name in &changes.locals {
            let Some((place, _)) = locals.get(name) else {
                if self.globals.contains_key(name)
                    || state.globals.contains_key(name)
                    || self.constants.contains_key(name)
                {
                    return Err(Error::unsupported("induction cannot havoc global storage"));
                }
                continue; // An iteration-local binding is recreated by the body.
            };
            if !place.path.is_empty() {
                return Err(Error::unsupported("induction requires owned root bindings"));
            }
            roots.push(place.clone());
        }
        let mut frame = WriteFrame::default();
        if changes.memory {
            for (place, _) in locals.values() {
                let value = self.read(&state, place)?;
                self.induction_reachable(&state, &value, TRUE, &mut frame, 0)?;
            }
        }
        let mut state = state;
        let mut places = roots
            .into_iter()
            .map(|place| (place, TRUE))
            .collect::<Vec<_>>();
        for (place, active) in frame.regions {
            if state
                .globals
                .values()
                .any(|global| global.root == place.root)
            {
                return Err(Error::unsupported(
                    "induction cannot havoc global storage through an alias",
                ));
            }
            if let Some((_, known)) = places
                .iter_mut()
                .find(|(known, _)| self.same_location(known, &place) == TRUE)
            {
                *known = self.circuit.or(*known, active);
            } else {
                places.push((place, active));
            }
        }
        if places.len() > 4096 {
            return Err(Error::limit("induction write frame exceeds 4096 entries"));
        }
        // Snapshot all old handles before writing any overlapping region.
        let mut writes = Vec::new();
        for (place, active) in places {
            let previous = self.read(&state, &place)?;
            let value = self.induction_fresh(&mut state, &previous, 0)?;
            writes.push((place, value, active));
        }
        for (place, value, active) in writes {
            // An earlier overlapping write may already have freshened this
            // region. Inactive writes must retain that current value.
            let current = self.read(&state, &place)?;
            let value = self.merge(active, &value, &current)?;
            self.write(&mut state, &place, value)?;
        }
        Ok(vec![state])
    }

    fn induction_region(
        &mut self,
        frame: &mut WriteFrame,
        place: &Location,
        active: Bit,
    ) -> Result<()> {
        if let Some((_, known)) = frame
            .regions
            .iter_mut()
            .find(|(known, _)| self.same_location(known, place) == TRUE)
        {
            *known = self.circuit.or(*known, active);
        } else {
            if frame.regions.len() >= 256 {
                return Err(Error::limit("induction writable-region budget exceeds 256"));
            }
            frame.regions.push((place.clone(), active));
        }
        Ok(())
    }

    fn induction_reachable(
        &mut self,
        state: &State,
        value: &Value,
        active: Bit,
        frame: &mut WriteFrame,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction storage nesting exceeds 32"));
        }
        if !self.handle_type(&value.ty(), 0)? {
            return Ok(());
        }
        let feasible = self.circuit.and(state.guard, active);
        if active == FALSE || self.circuit.satisfy(feasible)?.is_none() {
            return Ok(());
        }
        frame.visits += 1;
        if frame.visits > 4096 {
            return Err(Error::limit(
                "induction reachable-storage budget exceeds 4096",
            ));
        }
        match value {
            Value::Ref { place, mutable, .. } => {
                if *mutable {
                    self.induction_region(frame, place, active)?;
                }
                let unseen = if let Some((_, known)) = frame
                    .seen
                    .iter_mut()
                    .find(|(known, _)| self.same_location(known, place) == TRUE)
                {
                    let unseen = self.circuit.and(active, self.circuit.not(*known));
                    *known = self.circuit.or(*known, active);
                    unseen
                } else {
                    frame.seen.push((place.clone(), active));
                    active
                };
                let feasible = self.circuit.and(state.guard, unseen);
                if self.circuit.satisfy(feasible)?.is_some() {
                    let target = self.read(state, place)?;
                    self.induction_reachable(state, &target, unseen, frame, depth + 1)?;
                }
            }
            Value::Slice(view) => {
                let values = self.induction_slice_values(state, view, active)?;
                let end = self
                    .circuit
                    .binary("add", Some("wrap"), &view.start, &view.len)?
                    .0;
                for (index, value) in values.iter().enumerate() {
                    let index = Circuit::constant(index as u128, 64, false);
                    let before = self.circuit.lt_word(&index, &view.start);
                    let before_end = self.circuit.lt_word(&index, &end);
                    let inside = self.circuit.and(self.circuit.not(before), before_end);
                    let selected = self.circuit.and(active, inside);
                    let feasible = self.circuit.and(state.guard, selected);
                    if self.circuit.satisfy(feasible)?.is_none() {
                        continue;
                    }
                    if view.mutable {
                        let mut place = view.place.clone();
                        place.path.push(Segment::Index(index));
                        self.induction_region(frame, &place, selected)?;
                    }
                    self.induction_reachable(state, value, selected, frame, depth + 1)?;
                }
            }
            Value::Record(_, fields) => {
                for (_, value) in fields {
                    self.induction_reachable(state, value, active, frame, depth + 1)?;
                }
            }
            Value::Array(_, values) | Value::Tuple(values) => {
                for value in values {
                    self.induction_reachable(state, value, active, frame, depth + 1)?;
                }
            }
            Value::Enum(_, tag, values) => {
                for (index, value) in values.iter().enumerate() {
                    if let Some(value) = value {
                        let selected = self
                            .circuit
                            .eq_word(tag, &Circuit::constant(index as u128, 64, false));
                        let selected = self.circuit.and(active, selected);
                        self.induction_reachable(state, value, selected, frame, depth + 1)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn induction_slice_values(
        &mut self,
        state: &State,
        view: &Slice,
        active: Bit,
    ) -> Result<Vec<Value>> {
        let Value::Array(element, values) = self.read(state, &view.place)? else {
            return Err(Error::unsupported(
                "induction slices require modeled array backing storage",
            ));
        };
        if values.len() > 64 {
            return Err(Error::limit(
                "symbolic slice backing arrays are limited to 64 elements",
            ));
        }
        if self.resolve_type(&element)? != self.resolve_type(&view.element)?
            || view.start.bits.len() != 64
            || view.len.bits.len() != 64
            || view.start.signed
            || view.len.signed
        {
            return Err(Error::checker("invalid induction slice representation"));
        }
        let backing = Circuit::constant(values.len() as u128, 64, false);
        let past_start = self.circuit.lt_word(&backing, &view.start);
        let remaining = self
            .circuit
            .binary("sub", Some("wrap"), &backing, &view.start)?
            .0;
        let past_end = self.circuit.lt_word(&remaining, &view.len);
        let invalid = self.circuit.or(past_start, past_end);
        let guard = self.circuit.and(state.guard, active);
        let bad = self.circuit.and(guard, invalid);
        self.require_unsat(bad, "induction slice geometry can exceed its backing array")?;
        Ok(values)
    }

    fn induction_fresh(
        &mut self,
        state: &mut State,
        previous: &Value,
        depth: usize,
    ) -> Result<Value> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction storage nesting exceeds 32"));
        }
        if !previous.contains_ref() && !self.handle_type(&previous.ty(), 0)? {
            return self.fresh_value(state, &previous.ty(), 0);
        }
        Ok(match previous {
            Value::Ref { .. } | Value::Slice(_) => previous.clone(),
            Value::Record(name, fields) => Value::Record(
                name.clone(),
                fields
                    .iter()
                    .map(|(name, value)| {
                        Ok((name.clone(), self.induction_fresh(state, value, depth + 1)?))
                    })
                    .collect::<Result<_>>()?,
            ),
            Value::Array(ty, values) => Value::Array(
                ty.clone(),
                values
                    .iter()
                    .map(|value| self.induction_fresh(state, value, depth + 1))
                    .collect::<Result<_>>()?,
            ),
            Value::Tuple(values) => Value::Tuple(
                values
                    .iter()
                    .map(|value| self.induction_fresh(state, value, depth + 1))
                    .collect::<Result<_>>()?,
            ),
            Value::Enum(name, tag, values) => Value::Enum(
                name.clone(),
                tag.clone(),
                values
                    .iter()
                    .map(|value| {
                        value
                            .as_ref()
                            .map(|value| self.induction_fresh(state, value, depth + 1))
                            .transpose()
                    })
                    .collect::<Result<_>>()?,
            ),
            _ => {
                return Err(Error::unsupported(
                    "induction cannot preserve this storage representation",
                ))
            }
        })
    }

    pub(super) fn induction_reference_shape(&mut self, entry: &State, state: &State) -> Result<()> {
        if state.heap.len() < entry.heap.len() {
            return Err(Error::checker("induction lost existing symbolic storage"));
        }
        let mut covered = TRUE;
        for (previous, current) in entry.heap.iter().zip(&state.heap) {
            let valid = self.induction_same_references(previous, current, 0)?;
            covered = self.circuit.and(covered, valid);
        }
        let bad = self.circuit.and(state.guard, self.circuit.not(covered));
        if self.circuit.satisfy(bad)?.is_some() {
            return Err(Error::unsupported(
                "induction cannot change reference identities or reference-bearing enum tags",
            ));
        }
        Ok(())
    }

    fn induction_same_references(
        &mut self,
        previous: &Value,
        current: &Value,
        depth: usize,
    ) -> Result<Bit> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction reference nesting exceeds 32"));
        }
        self.compatible(current, &previous.ty())?;
        if !previous.contains_ref() && !self.handle_type(&previous.ty(), 0)? {
            return Ok(TRUE);
        }
        Ok(match (previous, current) {
            (Value::Slice(a), Value::Slice(b)) => {
                let place = self.same_location(&a.place, &b.place);
                let start = self.circuit.eq_word(&a.start, &b.start);
                let len = self.circuit.eq_word(&a.len, &b.len);
                let geometry = self.circuit.and(start, len);
                self.circuit.and(place, geometry)
            }
            (
                Value::Ref {
                    place: a,
                    mutable: am,
                    pinned: ap,
                    ..
                },
                Value::Ref {
                    place: b,
                    mutable: bm,
                    pinned: bp,
                    ..
                },
            ) if am == bm && ap == bp => self.same_location(a, b),
            (Value::Record(_, a), Value::Record(_, b)) => {
                if a.len() != b.len() {
                    return Err(Error::checker("induction record layout changed"));
                }
                let mut valid = TRUE;
                for ((name, a), (other, b)) in a.iter().zip(b) {
                    if name != other {
                        return Err(Error::checker("induction record field changed"));
                    }
                    let same = self.induction_same_references(a, b, depth + 1)?;
                    valid = self.circuit.and(valid, same);
                }
                valid
            }
            (Value::Array(_, a), Value::Array(_, b)) | (Value::Tuple(a), Value::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(Error::checker("induction aggregate layout changed"));
                }
                let mut valid = TRUE;
                for (a, b) in a.iter().zip(b) {
                    let same = self.induction_same_references(a, b, depth + 1)?;
                    valid = self.circuit.and(valid, same);
                }
                valid
            }
            (Value::Enum(_, a_tag, a), Value::Enum(_, b_tag, b)) => {
                if a.len() != b.len() {
                    return Err(Error::checker("induction enum layout changed"));
                }
                let mut valid = self.circuit.eq_word(a_tag, b_tag);
                for (index, (a, b)) in a.iter().zip(b).enumerate() {
                    let active = self
                        .circuit
                        .eq_word(a_tag, &Circuit::constant(index as u128, 64, false));
                    let same = match (a, b) {
                        (Some(a), Some(b)) => self.induction_same_references(a, b, depth + 1)?,
                        (None, None) => TRUE,
                        (Some(value), None) | (None, Some(value)) => {
                            if self.handle_type(&value.ty(), 0)? {
                                FALSE
                            } else {
                                TRUE
                            }
                        }
                    };
                    let branch = self.circuit.or(self.circuit.not(active), same);
                    valid = self.circuit.and(valid, branch);
                }
                valid
            }
            _ => {
                return Err(Error::unsupported(
                    "induction cannot compare this reference representation",
                ))
            }
        })
    }

    pub(super) fn handle_type(&mut self, ty: &Type, depth: usize) -> Result<bool> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction type nesting exceeds 32"));
        }
        Ok(match self.resolve_type(ty)? {
            Type::Reference { .. }
            | Type::PinnedReference { .. }
            | Type::Slice(_)
            | Type::MutableSlice(_) => true,
            Type::Array(element, len) => len != 0 && self.handle_type(&element, depth + 1)?,
            Type::Tuple(types) => {
                let mut found = false;
                for ty in types {
                    found |= self.handle_type(&ty, depth + 1)?;
                }
                found
            }
            Type::Named(name) if self.records.contains_key(&name) => {
                let mut found = false;
                for field in self.records[&name].clone() {
                    found |= self.handle_type(&field.ty, depth + 1)?;
                }
                found
            }
            Type::Named(name) if self.enums.contains_key(&name) => {
                let mut found = false;
                for variant in self.enums[&name].clone() {
                    for ty in variant.fields {
                        found |= self.handle_type(&ty, depth + 1)?;
                    }
                }
                found
            }
            _ => false,
        })
    }
}
