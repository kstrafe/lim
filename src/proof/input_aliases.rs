//! Bounded equivalence partitions for scalar shared validation inputs.
//! This is exact only when no new shared parent can contain an aliased subobject.
//! Other input shapes retain the conservative alias guard.
use super::*;

const CASE_LIMIT: usize = 256;
const ROOT_LIMIT: usize = 64;
const RETAINED_BYTES: usize = 64 * 1024 * 1024;

pub(in crate::proof) struct InputCase {
    pub state: State,
    pub arguments: Vec<Value>,
}

fn scalar_input(ty: &Type) -> bool {
    matches!(ty, Type::Bool | Type::Char)
        || (scalar(ty).is_some() && !matches!(ty, Type::RawPointer { .. }))
}

impl Engine<'_, '_> {
    fn alias_partitions(
        &mut self,
        roots: &[usize],
        index: usize,
        representatives: &mut Vec<usize>,
        output: &mut Vec<Vec<usize>>,
        limit: usize,
    ) -> Result<()> {
        self.tick()?;
        if index == roots.len() {
            if output.len() >= limit {
                return Err(Error::limit(
                    "scalar input alias alternatives exceed the retained-state or 256-case budget",
                ));
            }
            output.push(representatives.clone());
            return Ok(());
        }
        // A new class first keeps the ordinary disjoint case first. Existing
        // canonical classes produce every remaining partition exactly once.
        representatives.push(roots[index]);
        self.alias_partitions(roots, index + 1, representatives, output, limit)?;
        representatives.pop();
        let classes: BTreeSet<_> = representatives.iter().copied().collect();
        for representative in classes {
            representatives.push(representative);
            self.alias_partitions(roots, index + 1, representatives, output, limit)?;
            representatives.pop();
        }
        Ok(())
    }

    fn remap_input_value(
        &mut self,
        value: &mut Value,
        mapping: &BTreeMap<usize, usize>,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("input alias value nesting exceeds 32"));
        }
        match value {
            Value::Ref { place, .. } => {
                if let Some(&root) = mapping.get(&place.root) {
                    place.root = root;
                }
            }
            Value::Slice(view) => {
                if let Some(&root) = mapping.get(&view.place.root) {
                    view.place.root = root;
                }
            }
            Value::Record(_, fields) => {
                for (_, value) in fields {
                    self.remap_input_value(value, mapping, depth + 1)?;
                }
            }
            Value::Array(_, values) | Value::Tuple(values) => {
                for value in values {
                    self.remap_input_value(value, mapping, depth + 1)?;
                }
            }
            Value::Enum(_, _, values) => {
                for value in values.iter_mut().flatten() {
                    self.remap_input_value(value, mapping, depth + 1)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    pub(in crate::proof) fn scalar_alias_cases(
        &mut self,
        state: &State,
        arguments: &[Value],
        root_start: usize,
    ) -> Result<Option<Vec<InputCase>>> {
        let Some(Trace::Validated(rule)) = &self.trace else {
            return Ok(None);
        };
        let function = self.function(&rule.validator)?;
        let (Type::Reference { target, .. } | Type::PinnedReference { target, .. }) =
            self.resolve_type(&function.parameters[rule.validator_parameter].ty)?
        else {
            return Err(Error::checker(
                "validation parameter lost its reference type",
            ));
        };
        if !scalar_input(&target) {
            return Ok(None);
        }
        // Exclusive parents are absent from the shared-root set, but pinned
        // parents and retained references may still relate to internal fields.
        for &root in state.input_referents.range(root_start..) {
            self.tick()?;
            if state.input_parents.contains(&root)
                || !scalar_input(&self.resolve_type(&state.heap[root].ty())?)
            {
                return Ok(None);
            }
        }
        let mut roots = Vec::new();
        for &root in &state.abstract_referents {
            self.tick()?;
            if root < root_start {
                continue;
            }
            let value = state
                .heap
                .get(root)
                .ok_or_else(|| Error::checker("input alias root is absent"))?;
            let ty = self.resolve_type(&value.ty())?;
            if !scalar_input(&ty) {
                // A shared parent can alias another root's subobject. Scalar
                // partitions alone must never declare such roots disjoint.
                return Ok(None);
            }
            if ty == *target {
                roots.push(root);
            }
        }
        if roots.len() < 2 {
            return Ok(None);
        }
        if roots.len() > ROOT_LIMIT {
            return Err(Error::limit("scalar input aliases exceed 64 roots"));
        }
        if !state.validations.is_empty() {
            return Err(Error::checker(
                "input aliases require clean validation facts",
            ));
        }
        let mut bytes = self.induction_state_bytes(state)?;
        for argument in arguments {
            bytes = bytes.saturating_add(self.induction_value_bytes(argument)?);
        }
        bytes = bytes.saturating_add(roots.len().saturating_mul(roots.len()).saturating_mul(64));
        if bytes > RETAINED_BYTES {
            return Err(Error::limit("scalar input alias states exceed 64 MiB"));
        }
        let limit = (RETAINED_BYTES / bytes.max(1)).min(CASE_LIMIT);
        let mut partitions = Vec::new();
        self.alias_partitions(&roots, 0, &mut Vec::new(), &mut partitions, limit)?;
        let mut output = Vec::new();
        for representatives in partitions {
            self.tick()?;
            let mapping: BTreeMap<_, _> = roots.iter().copied().zip(representatives).collect();
            let mut case = state.clone();
            for (&root, &representative) in &mapping {
                if root != representative {
                    let equal = self.equal(&state.heap[root], &state.heap[representative])?;
                    case.guard = self.circuit.and(case.guard, equal);
                }
            }
            for value in &mut case.heap {
                self.remap_input_value(value, &mapping, 0)?;
            }
            self.remap_input_value(&mut case.value, &mapping, 0)?;
            if let Some(value) = &mut case.result {
                self.remap_input_value(value, &mapping, 0)?;
            }
            for frame in &mut case.frames {
                for (place, _) in frame.locals.values_mut() {
                    if let Some(&root) = mapping.get(&place.root) {
                        place.root = root;
                    }
                }
            }
            for place in case.globals.values_mut() {
                if let Some(&root) = mapping.get(&place.root) {
                    place.root = root;
                }
            }
            case.abstract_referents = case
                .abstract_referents
                .iter()
                .map(|root| mapping.get(root).copied().unwrap_or(*root))
                .collect();
            case.input_referents = case
                .input_referents
                .iter()
                .map(|root| mapping.get(root).copied().unwrap_or(*root))
                .collect();
            case.input_parents = case
                .input_parents
                .iter()
                .map(|root| mapping.get(root).copied().unwrap_or(*root))
                .collect();
            case.input_parent_aliases = case
                .input_parent_aliases
                .iter()
                .filter_map(|&(a, b)| {
                    let a = mapping.get(&a).copied().unwrap_or(a);
                    let b = mapping.get(&b).copied().unwrap_or(b);
                    (a != b).then_some((a.min(b), a.max(b)))
                })
                .collect();
            let mut distinct = BTreeSet::new();
            for (a, b) in &case.disjoint_inputs {
                let a = mapping.get(a).copied().unwrap_or(*a);
                let b = mapping.get(b).copied().unwrap_or(*b);
                if a == b {
                    case.guard = FALSE;
                } else {
                    distinct.insert((a.min(b), a.max(b)));
                }
            }
            let classes: Vec<_> = mapping
                .values()
                .copied()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            for (index, &a) in classes.iter().enumerate() {
                for &b in &classes[index + 1..] {
                    distinct.insert((a.min(b), a.max(b)));
                }
            }
            case.disjoint_inputs = distinct;
            let mut arguments = arguments.to_vec();
            for value in &mut arguments {
                self.remap_input_value(value, &mapping, 0)?;
            }
            output.push(InputCase {
                state: case,
                arguments,
            });
        }
        Ok(Some(output))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program(
            r#"
          (#struct Inputs () (: first (#ref #u8) : second (#ref #u8)))
          (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
          (#fn perform (: user (#ref #u8)) () (#return ()))
        "#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        engine.trace = Some(Trace::Validated(ValidationRule {
            validator: "validate".into(),
            validator_parameter: 0,
            action: "perform".into(),
            action_parameter: 0,
        }));
        test(&mut engine);
    }
    fn inputs(engine: &mut Engine<'_, '_>, count: usize) -> (State, Vec<Value>) {
        let mut state = State::new();
        let ty = Type::Reference {
            mutable: false,
            target: Box::new(Type::U8),
        };
        let values = (0..count)
            .map(|_| engine.fresh_value(&mut state, &ty, 0).unwrap())
            .collect();
        (state, values)
    }

    #[test]
    fn partitions_cover_every_labeled_alias_assignment_without_duplicates() {
        with_engine(|engine| {
            for count in 0..=6usize {
                let roots: Vec<_> = (0..count).collect();
                let mut output = Vec::new();
                engine
                    .alias_partitions(&roots, 0, &mut Vec::new(), &mut output, CASE_LIMIT)
                    .unwrap();
                let actual: BTreeSet<_> = output.iter().cloned().collect();
                assert_eq!(actual.len(), output.len());
                assert_eq!(actual.len(), [1, 1, 2, 5, 15, 52, 203][count]);
                if count <= 5 {
                    let mut expected = BTreeSet::new();
                    for mut assignment in 0..count.max(1).pow(count as u32) {
                        let mut first = BTreeMap::new();
                        let mut canonical = Vec::new();
                        for index in 0..count {
                            let label = assignment % count;
                            assignment /= count;
                            canonical.push(*first.entry(label).or_insert(index));
                        }
                        expected.insert(canonical);
                    }
                    assert_eq!(actual, expected);
                }
            }
        });
    }

    #[test]
    fn aliased_arguments_share_storage_and_constrain_the_original_values() {
        with_engine(|engine| {
            let (state, arguments) = inputs(engine, 2);
            let cases = engine
                .scalar_alias_cases(&state, &arguments, 0)
                .unwrap()
                .unwrap();
            assert_eq!(cases.len(), 2);
            let root = |value: &Value| match value {
                Value::Ref { place, .. } => place.root,
                _ => panic!("reference"),
            };
            assert_ne!(root(&cases[0].arguments[0]), root(&cases[0].arguments[1]));
            assert!(!cases[0].state.possibly_aliasing_roots(0).contains(&1));
            assert_eq!(root(&cases[1].arguments[0]), root(&cases[1].arguments[1]));
            let equal = engine.equal(&state.heap[0], &state.heap[1]).unwrap();
            let inconsistent = engine.circuit.and(cases[1].state.guard, equal ^ 1);
            assert!(engine.circuit.satisfy(inconsistent).unwrap().is_none());
        });
    }

    #[test]
    fn owned_reference_fields_are_remapped_but_shared_parents_keep_the_guard() {
        with_engine(|engine| {
            let mut state = State::new();
            let owned = engine
                .fresh_value(&mut state, &Type::Named("Inputs".into()), 0)
                .unwrap();
            let cases = engine
                .scalar_alias_cases(&state, &[owned], 0)
                .unwrap()
                .unwrap();
            let Value::Record(_, fields) = &cases[1].arguments[0] else {
                panic!("record")
            };
            let Value::Ref { place: a, .. } = &fields[0].1 else {
                panic!("ref")
            };
            let Value::Ref { place: b, .. } = &fields[1].1 else {
                panic!("ref")
            };
            assert_eq!(engine.same_location(a, b), TRUE);
            let mut state = State::new();
            let shared = engine
                .fresh_value(
                    &mut state,
                    &Type::Reference {
                        mutable: false,
                        target: Box::new(Type::Named("Inputs".into())),
                    },
                    0,
                )
                .unwrap();
            assert!(engine
                .scalar_alias_cases(&state, &[shared], 0)
                .unwrap()
                .is_none());
        });
    }

    #[test]
    fn explicit_distinct_inputs_do_not_assume_distinction_from_globals_or_later_roots() {
        with_engine(|engine| {
            let (state, arguments) = inputs(engine, 2);
            let mut case = engine
                .scalar_alias_cases(&state, &arguments, 0)
                .unwrap()
                .unwrap()
                .remove(0);
            let global = engine
                .allocate(
                    &mut case.state,
                    Value::Bits(Circuit::constant(0, 8, false), Type::U8),
                )
                .unwrap();
            case.state.globals.insert("global".into(), global.clone());
            assert!(case.state.possibly_aliasing_roots(0).contains(&global.root));
            let later = engine
                .fresh_value(
                    &mut case.state,
                    &Type::Reference {
                        mutable: false,
                        target: Box::new(Type::U8),
                    },
                    0,
                )
                .unwrap();
            let Value::Ref { place, .. } = later else {
                panic!("ref")
            };
            assert!(case.state.possibly_aliasing_roots(0).contains(&place.root));
            assert!(!case.state.possibly_aliasing_roots(0).contains(&1));
        });
    }

    #[test]
    fn earlier_origins_are_not_partitioned_or_declared_distinct_from_new_inputs() {
        with_engine(|engine| {
            let (mut state, earlier) = inputs(engine, 1);
            let start = state.heap_len();
            let ty = Type::Reference {
                mutable: false,
                target: Box::new(Type::U8),
            };
            let first = engine.fresh_value(&mut state, &ty, 0).unwrap();
            let second = engine.fresh_value(&mut state, &ty, 0).unwrap();
            let cases = engine
                .scalar_alias_cases(&state, &[first, second], start)
                .unwrap()
                .unwrap();
            let Value::Ref { place: old, .. } = &earlier[0] else {
                panic!("ref")
            };
            assert_eq!(cases.len(), 2);
            assert!(cases[0]
                .state
                .possibly_aliasing_roots(start)
                .contains(&old.root));
            assert!(!cases[0]
                .state
                .possibly_aliasing_roots(start)
                .contains(&(start + 1)));
            assert!(cases[1]
                .state
                .possibly_aliasing_roots(start)
                .contains(&old.root));
            assert_eq!(
                engine
                    .equal(&state.heap[old.root], &cases[1].state.heap[old.root])
                    .unwrap(),
                TRUE
            );
        });
    }

    #[test]
    fn only_the_validator_target_type_is_partitioned_and_zero_sized_inputs_fall_back() {
        with_engine(|engine| {
            let (mut state, mut arguments) = inputs(engine, 2);
            let ty = Type::Reference {
                mutable: false,
                target: Box::new(Type::Bool),
            };
            arguments.push(engine.fresh_value(&mut state, &ty, 0).unwrap());
            let cases = engine
                .scalar_alias_cases(&state, &arguments, 0)
                .unwrap()
                .unwrap();
            assert_eq!(cases.len(), 2);
            for case in cases {
                let Value::Ref { place, target, .. } = &case.arguments[2] else {
                    panic!("ref")
                };
                assert_eq!(place.root, 2);
                assert_eq!(target, &Type::Bool);
                assert!(case.state.possibly_aliasing_roots(0).contains(&2));
            }
            arguments.push(
                engine
                    .fresh_value(
                        &mut state,
                        &Type::Reference {
                            mutable: false,
                            target: Box::new(Type::Unit),
                        },
                        0,
                    )
                    .unwrap(),
            );
            assert!(engine
                .scalar_alias_cases(&state, &arguments, 0)
                .unwrap()
                .is_none());
        });
    }

    #[test]
    fn case_and_retained_byte_limits_fail_before_cloning_case_states() {
        with_engine(|engine| {
            let (state, arguments) = inputs(engine, 7);
            let error = engine
                .scalar_alias_cases(&state, &arguments, 0)
                .err()
                .unwrap();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::ResourceLimit)
            );
            let (mut state, arguments) = inputs(engine, 4);
            state.frames[0].function = "x".repeat(8 * 1024 * 1024);
            let error = engine
                .scalar_alias_cases(&state, &arguments, 0)
                .err()
                .unwrap();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::ResourceLimit)
            );
        });
    }
}
