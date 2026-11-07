//! Abstract loop data without inventing new reference identities. This bounded
//! model requires the reference graph to remain stable on every modeled step.
use super::*;

#[derive(Default)]
pub(super) struct Changes {
    pub locals: BTreeSet<String>,
    pub memory: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

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
        // Slice write frames need backing-range enumeration, not just stable
        // handles. Never silently omit them from the loop's mutable frame.
        for value in &state.heap {
            self.induction_no_slices(value, 0)?;
        }
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
        let frames = if changes.memory {
            let arguments = locals
                .values()
                .map(|(place, _)| self.read(&state, place))
                .collect::<Result<Vec<_>>>()?;
            self.contract_targets(state, &arguments)?
        } else {
            vec![(state, Vec::new())]
        };
        let mut output = Vec::new();
        for (mut state, targets) in frames {
            let mut places = roots.clone();
            for target in targets.into_iter().filter(|target| target.mutable) {
                if state
                    .globals
                    .values()
                    .any(|global| global.root == target.place.root)
                {
                    return Err(Error::unsupported(
                        "induction cannot havoc global storage through an alias",
                    ));
                }
                if !places
                    .iter()
                    .any(|place| self.same_location(place, &target.place) == TRUE)
                {
                    places.push(target.place);
                }
            }
            if places.len() > 4096 {
                return Err(Error::limit("induction write frame exceeds 4096 entries"));
            }
            // Snapshot all old handles before writing any overlapping region.
            let mut writes = Vec::new();
            for place in places {
                let previous = self.read(&state, &place)?;
                let value = self.induction_fresh(&mut state, &previous, 0)?;
                writes.push((place, value));
            }
            for (place, value) in writes {
                self.write(&mut state, &place, value)?;
            }
            output.push(state);
        }
        Ok(output)
    }

    fn induction_no_slices(&mut self, value: &Value, depth: usize) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("induction storage nesting exceeds 32"));
        }
        match value {
            Value::Slice(_) => {
                return Err(Error::unsupported(
                    "induction over slice backing storage is not modeled",
                ))
            }
            Value::Record(_, fields) => {
                for (_, value) in fields {
                    self.induction_no_slices(value, depth + 1)?;
                }
            }
            Value::Array(_, values) | Value::Tuple(values) => {
                for value in values {
                    self.induction_no_slices(value, depth + 1)?;
                }
            }
            Value::Enum(_, _, values) => {
                for value in values.iter().flatten() {
                    self.induction_no_slices(value, depth + 1)?;
                }
            }
            _ => {}
        }
        Ok(())
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
        if !previous.contains_ref() && !self.reference_type(&previous.ty(), 0)? {
            return self.fresh_value(state, &previous.ty(), 0);
        }
        Ok(match previous {
            Value::Ref { .. } => previous.clone(),
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
        if !previous.contains_ref() && !self.reference_type(&previous.ty(), 0)? {
            return Ok(TRUE);
        }
        Ok(match (previous, current) {
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
                            if self.reference_type(&value.ty(), 0)? {
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
}
