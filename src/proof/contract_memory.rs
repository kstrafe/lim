//! The frame of a borrowed contract is the storage reachable through its
//! active mutable arguments. Do not freshen reference identities themselves.
//! Writes use the ordinary heap update path, including validation invalidation.
use super::*;
use crate::typed_place::Segment as Path;
use symbolic::Location;

#[derive(Clone)]
pub(super) struct Target {
    pub place: Location,
    pub ty: Type,
    pub parameter: usize,
    pub storage: Vec<Path>,
    pub mutable: bool,
}
type Writes = Vec<Target>;

impl Engine<'_, '_> {
    pub(super) fn contract_memory_states(
        &mut self,
        state: State,
        function: &Function,
        arguments: &[Value],
        guards: Option<&guarded_returns::Guards>,
    ) -> Result<Vec<State>> {
        let entry = state.clone();
        let runs = self.contract_targets(state, arguments)?;
        let mut output = Vec::with_capacity(runs.len());
        for (state, writes) in runs {
            let mut prepared = vec![(state, Vec::new())];
            for target in writes.iter().filter(|target| target.mutable) {
                let mut next = Vec::new();
                for (state, replacements) in prepared {
                    for (state, value) in self.contract_stored_values(
                        state, &entry, function, arguments, target, guards,
                    )? {
                        let mut replacements = replacements.clone();
                        replacements.push((target.place.clone(), value));
                        next.push((state, replacements));
                        if next.len() > 256
                            || next.iter().map(|(_, values)| values.len()).sum::<usize>() > 4096
                        {
                            return Err(Error::limit("contract store frame alternatives exceed 256 paths or 4096 replacements"));
                        }
                    }
                }
                prepared = next;
            }
            for (mut state, replacements) in prepared {
                if state.guard != FALSE {
                    for (place, value) in replacements {
                        self.write(&mut state, &place, value)?;
                    }
                }
                output.push(state);
                if output.len() > 256 {
                    return Err(Error::limit("contract store frame alternatives exceed 256"));
                }
            }
        }
        Ok(output)
    }

    pub(super) fn contract_targets(
        &mut self,
        state: State,
        arguments: &[Value],
    ) -> Result<Vec<(State, Writes)>> {
        let mut runs = vec![(state, Vec::new())];
        for (parameter, argument) in arguments.iter().enumerate() {
            runs = self.contract_writes(runs, argument, parameter, &[], 0)?;
        }
        Ok(runs)
    }

    fn contract_writes(
        &mut self,
        mut runs: Vec<(State, Writes)>,
        value: &Value,
        parameter: usize,
        storage: &[Path],
        depth: usize,
    ) -> Result<Vec<(State, Writes)>> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("contract argument frame nesting exceeds 32"));
        }
        match value {
            Value::Ref {
                place,
                target,
                mutable,
                ..
            } => {
                if !*mutable && !self.reference_type(target, 0)? {
                    return Ok(runs);
                }
                let mut output = Vec::new();
                for (state, mut writes) in runs {
                    if writes.iter().any(|known| {
                        self.same_location(&known.place, place) == TRUE
                            && (!*mutable || known.mutable)
                    }) {
                        output.push((state, writes));
                        continue;
                    }
                    if writes.len() >= 256 {
                        return Err(Error::limit(
                            "contract writable-location budget exceeds 256",
                        ));
                    }
                    writes.push(Target {
                        place: place.clone(),
                        ty: target.clone(),
                        parameter,
                        storage: storage.to_vec(),
                        mutable: *mutable,
                    });
                    let value = self.read(&state, place)?;
                    let mut nested = storage.to_vec();
                    nested.push(Path::Dereference);
                    output.extend(self.contract_writes(
                        vec![(state, writes)],
                        &value,
                        parameter,
                        &nested,
                        depth + 1,
                    )?);
                    self.contract_frame_budget(&output)?;
                }
                return Ok(output);
            }
            Value::Record(name, fields) => {
                for (field_name, field) in fields {
                    let field_id = self
                        .checked
                        .declarations()
                        .field_id(&Type::Named(name.clone()), field_name)
                        .ok_or_else(|| Error::checker("missing contract target field"))?;
                    let mut nested = storage.to_vec();
                    nested.push(Path::Field(field_id));
                    runs = self.contract_writes(runs, field, parameter, &nested, depth + 1)?;
                }
            }
            Value::Tuple(values) | Value::Array(_, values) => {
                let array = matches!(value, Value::Array(_, _));
                for (index, value) in values.iter().enumerate() {
                    let mut nested = storage.to_vec();
                    nested.push(if array {
                        Path::Index(index as u128)
                    } else {
                        Path::Tuple(index)
                    });
                    runs = self.contract_writes(runs, value, parameter, &nested, depth + 1)?;
                }
            }
            Value::Enum(name, tag, values) if self.possible_mutable_reference(value)? => {
                let mut output = Vec::new();
                for (state, writes) in runs {
                    for (index, payload) in values.iter().enumerate() {
                        self.tick()?;
                        let selected = self
                            .circuit
                            .eq_word(tag, &Circuit::constant(index as u128, 64, false));
                        let mut state = state.clone();
                        state.guard = self.circuit.and(state.guard, selected);
                        if state.guard == FALSE {
                            continue;
                        }
                        let mut branch = vec![(state, writes.clone())];
                        if let Some(payload) = payload {
                            let variant_name = &self.enums[name][index].name;
                            let variant = self
                                .checked
                                .declarations()
                                .variant_id(&Type::Named(name.clone()), variant_name)
                                .ok_or_else(|| Error::checker("missing contract target variant"))?;
                            let mut nested = storage.to_vec();
                            nested.push(Path::Payload(variant, 0));
                            branch = self.contract_writes(
                                branch,
                                payload,
                                parameter,
                                &nested,
                                depth + 1,
                            )?;
                        }
                        output.extend(branch);
                        self.contract_frame_budget(&output)?;
                    }
                }
                return Ok(output);
            }
            _ => {}
        }
        self.contract_frame_budget(&runs)?;
        Ok(runs)
    }

    fn contract_frame_budget(&self, runs: &[(State, Writes)]) -> Result<()> {
        if runs.len() > 256 || runs.iter().map(|(_, writes)| writes.len()).sum::<usize>() > 4096 {
            return Err(Error::limit(
                "contract frame alternatives exceed 256 paths or 4096 writable entries",
            ));
        }
        Ok(())
    }

    fn possible_mutable_reference(&mut self, value: &Value) -> Result<bool> {
        Ok(match value {
            Value::Ref {
                mutable, target, ..
            } => *mutable || self.reference_type(target, 0)?,
            Value::Record(_, fields) => {
                let mut found = false;
                for (_, value) in fields {
                    found |= self.possible_mutable_reference(value)?;
                }
                found
            }
            Value::Array(_, values) | Value::Tuple(values) => {
                let mut found = false;
                for value in values {
                    found |= self.possible_mutable_reference(value)?;
                }
                found
            }
            Value::Enum(_, _, values) => {
                let mut found = false;
                for value in values.iter().flatten() {
                    found |= self.possible_mutable_reference(value)?;
                }
                found
            }
            _ => false,
        })
    }
}
