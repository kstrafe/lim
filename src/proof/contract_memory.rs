//! The frame of a borrowed contract is the storage reachable through its
//! active mutable arguments. Do not freshen reference identities themselves.
//! Writes use the ordinary heap update path, including validation invalidation.
use super::*;
use symbolic::Location;

type Writes = Vec<(Location, Type)>;

impl Engine<'_, '_> {
    pub(super) fn contract_memory_states(
        &mut self,
        state: State,
        arguments: &[Value],
    ) -> Result<Vec<State>> {
        let mut runs = vec![(state, Vec::new())];
        for argument in arguments {
            runs = self.contract_writes(runs, argument, 0)?;
        }
        let mut output = Vec::with_capacity(runs.len());
        for (mut state, writes) in runs {
            if state.guard != FALSE {
                for (place, ty) in writes {
                    let value = self.fresh_value(&mut state, &ty, 0)?;
                    self.write(&mut state, &place, value)?;
                }
            }
            output.push(state);
        }
        Ok(output)
    }

    fn contract_writes(
        &mut self,
        mut runs: Vec<(State, Writes)>,
        value: &Value,
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
                mutable: true,
                ..
            } => {
                for (_, writes) in &mut runs {
                    if writes.len() >= 256 {
                        return Err(Error::limit(
                            "contract writable-location budget exceeds 256",
                        ));
                    }
                    writes.push((place.clone(), target.clone()));
                }
            }
            Value::Record(_, fields) => {
                for (_, field) in fields {
                    runs = self.contract_writes(runs, field, depth + 1)?;
                }
            }
            Value::Tuple(values) | Value::Array(_, values) => {
                for value in values {
                    runs = self.contract_writes(runs, value, depth + 1)?;
                }
            }
            Value::Enum(_, tag, values) if values.iter().flatten().any(has_mutable_reference) => {
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
                            branch = self.contract_writes(branch, payload, depth + 1)?;
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
}

fn has_mutable_reference(value: &Value) -> bool {
    match value {
        Value::Ref { mutable, .. } => *mutable,
        Value::Record(_, fields) => fields.iter().any(|(_, value)| has_mutable_reference(value)),
        Value::Array(_, values) | Value::Tuple(values) => values.iter().any(has_mutable_reference),
        Value::Enum(_, _, values) => values.iter().flatten().any(has_mutable_reference),
        _ => false,
    }
}
