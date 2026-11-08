//! Execution-local validation facts are about storage identity, never contents.
//! Writes revoke facts through aliases, projections and referenced dependencies.
use super::symbolic::{Location, Segment};
use super::*;

const FACT_LIMIT: usize = 64;
const DEPENDENCY_LIMIT: usize = 128;
const TOTAL_DEPENDENCY_LIMIT: usize = 256;

#[derive(Clone, Copy)]
pub(super) enum ValidationMode {
    None,
    Check,
    Assume,
}

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

    #[test]
    fn slice_validation_tracks_only_elements_in_its_symbolic_range() {
        let program = crate::parse_program("(#struct Holder () ((view (#slice #u8))))").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let reference = engine
            .fresh_value(
                &mut state,
                &Type::Reference {
                    mutable: true,
                    target: Box::new(Type::Array(Box::new(Type::U8), 3)),
                },
                0,
            )
            .unwrap();
        let Value::Ref { place: array, .. } = reference else {
            panic!("array reference")
        };
        let start = engine.circuit.word(64, false);
        state.guard = engine
            .circuit
            .lt_word(&start, &Circuit::constant(3, 64, false));
        engine
            .bind(
                &mut state,
                "holder".into(),
                Type::Named("Holder".into()),
                Value::Record(
                    "Holder".into(),
                    vec![(
                        "view".into(),
                        Value::Slice(symbolic::Slice {
                            place: array.clone(),
                            element: Type::U8,
                            start: start.clone(),
                            len: Circuit::constant(1, 64, false),
                            mutable: false,
                        }),
                    )],
                ),
            )
            .unwrap();
        let subject = state.frames.last().unwrap().locals["holder"].0.clone();
        engine
            .complete_validation(&mut state, &subject, TRUE)
            .unwrap();
        let argument = Value::Ref {
            place: subject,
            target: Type::Named("Holder".into()),
            mutable: false,
            pinned: false,
        };
        for index in 0..3 {
            let mut changed = state.clone();
            let index = Circuit::constant(index, 64, false);
            let mut written = array.clone();
            written.path.push(Segment::Index(index.clone()));
            engine
                .invalidate_validations(&mut changed, &written)
                .unwrap();
            let valid = engine.validated_argument(&changed, &argument).unwrap();
            let overlaps = engine.circuit.eq_word(&start, &index);
            let expected = engine.circuit.not(overlaps);
            let different = engine.circuit.xor(valid, expected);
            let bad = engine.circuit.and(state.guard, different);
            engine
                .require_unsat(bad, "a slice depends only on its selected elements")
                .unwrap();
        }
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

impl ValidationFact {
    pub(super) fn retained_bytes(&self) -> usize {
        fn location(place: &Location) -> usize {
            let mut bytes = std::mem::size_of::<Location>()
                + place.path.capacity() * std::mem::size_of::<Segment>();
            for segment in &place.path {
                bytes = bytes.saturating_add(match segment {
                    Segment::Field(_) => 0,
                    Segment::Index(word) => word.bits.capacity() * std::mem::size_of::<Bit>(),
                    Segment::Payload(_) => 0,
                });
            }
            bytes
        }
        let mut bytes = location(&self.subject)
            .saturating_add(self.dependencies.capacity() * std::mem::size_of::<Dependency>());
        for dependency in &self.dependencies {
            bytes = bytes.saturating_add(location(&dependency.place));
        }
        bytes
    }
}

impl<'a, 'p> Engine<'a, 'p> {
    pub(super) fn validation_query(
        &mut self,
        state: State,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        arity("proof-validated", args, 2)?;
        if matches!(self.validation_mode, ValidationMode::None) {
            return Err(Error::invalid(
                "#proof-validated is only a positive loop-invariant requirement",
            ));
        }
        let Some(Trace::Validated(rule)) = &self.trace else {
            return Err(Error::unsupported(
                "#proof-validated requires a #proof-requires-validation claim",
            ));
        };
        let (function, parameter, target) = self.validation_descriptor(&args[0])?;
        if function.name != rule.validator || parameter != rule.validator_parameter {
            return Err(Error::invalid(
                "#proof-validated must select the claim's validator and parameter",
            ));
        }
        let mut output = Vec::new();
        for (mut state, argument) in self.expr(state, &args[1], true)? {
            let Value::Ref {
                place,
                target: actual,
                ..
            } = &argument
            else {
                return Err(Error::invalid(
                    "#proof-validated requires a reference to the validated object",
                ));
            };
            if self.resolve_type(actual)? != target {
                return Err(Error::invalid("#proof-validated reference does not match the validator parameter's target type"));
            }
            if matches!(self.validation_mode, ValidationMode::Assume) {
                // Each unknown location receives an independent lower-bound
                // fact. Excluding aliases of earlier subjects keeps repeated
                // queries consistent and prevents later seeds changing them.
                let mut known = FALSE;
                for fact in &state.validations {
                    self.tick()?;
                    let same = self.same_location(&fact.subject, place);
                    known = self.circuit.or(known, same);
                }
                if known != TRUE {
                    let fresh = self.circuit.fresh();
                    let valid = self.circuit.and(fresh, known ^ 1);
                    self.add_validation_fact(&mut state, place, valid)?;
                }
            }
            let valid = self.validated_argument(&state, &argument)?;
            output.push((state, Value::Bool(valid)));
        }
        self.limit_paths(output.len())?;
        Ok(output)
    }

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
        if descriptor.len() != 3
            || !matches!(&descriptor[0], Expr::Symbol(head) if head == "#parameter-of")
        {
            return Err(
                "a validation descriptor is (#parameter-of function parameter-name)".into(),
            );
        }
        let function = self.function(symbol(&descriptor[1])?)?;
        let name = symbol(&descriptor[2])?;
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
            _ => Err(Error::unsupported(
                "validation parameter has no symbolic storage identity",
            )),
        }
    }

    pub(super) fn validated_argument(&mut self, state: &State, argument: &Value) -> Result<Bit> {
        let Value::Ref { place, .. } = argument else {
            return Err(Error::unsupported(
                "action parameter has no symbolic storage identity",
            ));
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
        self.add_validation_fact(state, subject, succeeded)
    }

    fn add_validation_fact(
        &mut self,
        state: &mut State,
        subject: &Location,
        valid: Bit,
    ) -> Result<()> {
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
            return Err(Error::limit("validation fact budget exhausted"));
        }
        state.validations.push(ValidationFact {
            subject: subject.clone(),
            dependencies,
            valid,
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

    pub(super) fn same_location(&mut self, left: &Location, right: &Location) -> Bit {
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
            return Err(Error::limit("validation dependency nesting exceeds 32"));
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
                return Err(Error::limit("validation dependency budget exhausted"));
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
            return Err(Error::limit("validation dependency nesting exceeds 32"));
        }
        match value {
            Value::Ref { place, .. } => {
                self.validation_dependencies(state, place, active, dependencies, depth + 1)
            }
            Value::Slice(view) => {
                let Value::Array(_, values) = self.read(state, &view.place)? else {
                    return Err(Error::checker("a slice lost its backing array"));
                };
                let end = self
                    .circuit
                    .binary("add", Some("wrap"), &view.start, &view.len)?
                    .0;
                for index in 0..values.len() {
                    let index = Circuit::constant(index as u128, 64, false);
                    let before = self.circuit.lt_word(&index, &view.start);
                    let within_end = self.circuit.lt_word(&index, &end);
                    let within = self.circuit.and(self.circuit.not(before), within_end);
                    let selected = self.circuit.and(active, within);
                    let mut place = view.place.clone();
                    place.path.push(Segment::Index(index));
                    self.validation_dependencies(state, &place, selected, dependencies, depth + 1)?;
                }
                Ok(())
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
