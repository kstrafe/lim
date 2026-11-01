//! Execution-local validation facts are about storage identity, never contents.
//! Writes revoke facts through aliases, projections and referenced dependencies.
use super::symbolic::{Location, Segment};
use super::*;

const FACT_LIMIT: usize = 64;
const DEPENDENCY_LIMIT: usize = 128;
const TOTAL_DEPENDENCY_LIMIT: usize = 256;

#[derive(Clone)]
pub(super) struct ValidationRule {
    pub validator: String,
    pub validator_parameter: usize,
    pub action: String,
    pub action_parameter: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_the_active_enum_payload_is_a_referenced_dependency() {
        let program = crate::parse_program(
            "(#enum Choice () ((Choice.Left (#ref-mut #u8)) (Choice.Right (#ref-mut #u8))))\n\
             (#struct Holder () ((choice Choice)))",
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let reference = engine
            .fresh_value(
                &mut state,
                &Type::Reference {
                    mutable: false,
                    target: Box::new(Type::Named("Holder".into())),
                },
                0,
            )
            .unwrap();
        let Value::Ref { place: subject, .. } = reference else {
            panic!("holder reference")
        };
        let Value::Record(_, fields) = engine.read(&state, &subject).unwrap() else {
            panic!("holder")
        };
        let Value::Enum(_, tag, payloads) = &fields[0].1 else {
            panic!("choice")
        };
        let Some(Value::Ref { place: left, .. }) = &payloads[0] else {
            panic!("left reference")
        };
        engine
            .complete_validation(&mut state, &subject, TRUE)
            .unwrap();
        engine.invalidate_validations(&mut state, left).unwrap();
        let valid = engine
            .validated_argument(
                &state,
                &Value::Ref {
                    place: subject,
                    target: Type::Named("Holder".into()),
                    mutable: false,
                    pinned: false,
                },
            )
            .unwrap();
        let right = engine
            .circuit
            .eq_word(tag, &Circuit::constant(1, 64, false));
        let different = engine.circuit.xor(valid, right);
        let wrong = engine.circuit.and(state.guard, different);
        engine
            .require_unsat(wrong, "only the active payload can invalidate the holder")
            .unwrap();
    }
}

#[derive(Clone)]
pub(super) struct ValidationFact {
    subject: Location,
    dependencies: Vec<Dependency>,
    valid: Bit,
}

#[derive(Clone)]
struct Dependency {
    place: Location,
    active: Bit,
}

impl<'a, 'p> Engine<'a, 'p> {
    pub(super) fn validation_rule(&self, args: &[Expr]) -> Result<(&'p Function, Trace)> {
        arity("proof-requires-validation", args, 3)?;
        let entry = self.function(symbol(&args[0])?)?;
        let (validator, validator_parameter, validator_type) =
            self.validation_descriptor(&args[1])?;
        let (action, action_parameter, action_type) = self.validation_descriptor(&args[2])?;
        if self.resolve_type(&validator.return_type)? != Type::Bool {
            return Err("the validation function must return #bool".into());
        }
        if validator_type != action_type {
            return Err("validation and action parameters must reference the same type".into());
        }
        Ok((
            entry,
            Trace::Validated(ValidationRule {
                validator: validator.name.clone(),
                validator_parameter,
                action: action.name.clone(),
                action_parameter,
            }),
        ))
    }

    fn validation_descriptor(&self, expr: &Expr) -> Result<(&'p Function, usize, Type)> {
        let descriptor = list(expr)?;
        if descriptor.len() != 2 {
            return Err("a validation descriptor is (function parameter-name)".into());
        }
        let function = self.function(symbol(&descriptor[0])?)?;
        let name = symbol(&descriptor[1])?;
        let index = function
            .parameters
            .iter()
            .position(|parameter| parameter.name == name)
            .ok_or_else(|| {
                format!(
                    "function '{}' has no parameter '{name}'",
                    crate::file_access::local_name(&function.name)
                )
            })?;
        let target = match self.resolve_type(&function.parameters[index].ty)? {
            Type::Reference { target, .. } | Type::PinnedReference { target, .. } => *target,
            _ => return Err("validation descriptors require reference parameters".into()),
        };
        Ok((function, index, self.resolve_type(&target)?))
    }

    pub(super) fn validation_argument(
        &self,
        function: &str,
        arguments: &[Value],
    ) -> Result<Option<Location>> {
        let Some(Trace::Validated(rule)) = &self.trace else {
            return Ok(None);
        };
        if function != rule.validator {
            return Ok(None);
        }
        match &arguments[rule.validator_parameter] {
            Value::Ref { place, .. } => Ok(Some(place.clone())),
            _ => Err("unproved: validation parameter has no symbolic storage identity".into()),
        }
    }

    pub(super) fn validated_argument(&mut self, state: &State, argument: &Value) -> Result<Bit> {
        let Value::Ref { place, .. } = argument else {
            return Err("unproved: action parameter has no symbolic storage identity".into());
        };
        let mut valid = FALSE;
        for fact in &state.validations {
            self.tick()?;
            let same = self.same_location(&fact.subject, place);
            let checked = self.circuit.and(same, fact.valid);
            valid = self.circuit.or(valid, checked);
        }
        Ok(valid)
    }

    pub(super) fn complete_validation(
        &mut self,
        state: &mut State,
        subject: &Location,
        succeeded: Bit,
    ) -> Result<()> {
        // A later failure revokes an earlier success, too. A validator may have
        // other parameters, so repeated calls need not return the same result.
        for fact in &mut state.validations {
            self.tick()?;
            let same = self.same_location(&fact.subject, subject);
            fact.valid = self.circuit.and(fact.valid, self.circuit.not(same));
        }
        state.validations.retain(|fact| fact.valid != FALSE);
        if succeeded == FALSE {
            return Ok(());
        }
        let mut dependencies = Vec::new();
        self.validation_dependencies(state, subject, TRUE, &mut dependencies, 0)?;
        let total = state
            .validations
            .iter()
            .map(|fact| fact.dependencies.len())
            .sum::<usize>();
        if state.validations.len() >= FACT_LIMIT
            || total + dependencies.len() > TOTAL_DEPENDENCY_LIMIT
        {
            return Err("unproved: validation fact budget exhausted".into());
        }
        state.validations.push(ValidationFact {
            subject: subject.clone(),
            dependencies,
            valid: succeeded,
        });
        Ok(())
    }

    pub(super) fn invalidate_validations(
        &mut self,
        state: &mut State,
        written: &Location,
    ) -> Result<()> {
        for fact in &mut state.validations {
            let mut overlaps = FALSE;
            for dependency in &fact.dependencies {
                self.tick()?;
                let overlap = self.overlapping_locations(&dependency.place, written);
                let overlap = self.circuit.and(dependency.active, overlap);
                overlaps = self.circuit.or(overlaps, overlap);
            }
            fact.valid = self.circuit.and(fact.valid, self.circuit.not(overlaps));
        }
        Ok(())
    }

    fn same_location(&mut self, left: &Location, right: &Location) -> Bit {
        if left.path.len() != right.path.len() {
            return FALSE;
        }
        self.overlapping_locations(left, right)
    }

    fn overlapping_locations(&mut self, left: &Location, right: &Location) -> Bit {
        if left.root != right.root {
            return FALSE;
        }
        let mut same = TRUE;
        for (left, right) in left.path.iter().zip(&right.path) {
            let segment = match (left, right) {
                (Segment::Field(a), Segment::Field(b))
                | (Segment::Payload(a), Segment::Payload(b)) => bit(a == b),
                (Segment::Index(a), Segment::Index(b)) => self.circuit.eq_word(a, b),
                _ => FALSE,
            };
            same = self.circuit.and(same, segment);
        }
        same
    }

    fn validation_dependencies(
        &mut self,
        state: &State,
        place: &Location,
        active: Bit,
        dependencies: &mut Vec<Dependency>,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err("unproved: validation dependency nesting exceeds 32".into());
        }
        if active == FALSE {
            return Ok(());
        }
        let mut seen = false;
        for existing in dependencies.iter_mut() {
            if self.same_location(&existing.place, place) == TRUE {
                let merged = self.circuit.or(existing.active, active);
                if merged == existing.active {
                    return Ok(());
                }
                existing.active = merged;
                seen = true;
                break;
            }
        }
        if !seen {
            if dependencies.len() >= DEPENDENCY_LIMIT {
                return Err("unproved: validation dependency budget exhausted".into());
            }
            dependencies.push(Dependency {
                place: place.clone(),
                active,
            });
        }
        let value = self.read(state, place)?;
        self.validation_referents(state, &value, active, dependencies, depth + 1)
    }

    fn validation_referents(
        &mut self,
        state: &State,
        value: &Value,
        active: Bit,
        dependencies: &mut Vec<Dependency>,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err("unproved: validation dependency nesting exceeds 32".into());
        }
        match value {
            Value::Ref { place, .. } => {
                self.validation_dependencies(state, place, active, dependencies, depth + 1)
            }
            Value::Record(_, fields) => {
                for (_, value) in fields {
                    self.validation_referents(state, value, active, dependencies, depth + 1)?;
                }
                Ok(())
            }
            Value::Array(_, values) | Value::Tuple(values) => {
                for value in values {
                    self.validation_referents(state, value, active, dependencies, depth + 1)?;
                }
                Ok(())
            }
            Value::Enum(_, tag, values) => {
                for (index, value) in values.iter().enumerate() {
                    if let Some(value) = value {
                        let selected = Circuit::constant(index as u128, tag.bits.len(), false);
                        let selected = self.circuit.eq_word(tag, &selected);
                        let selected = self.circuit.and(active, selected);
                        self.validation_referents(state, value, selected, dependencies, depth + 1)?;
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
}
