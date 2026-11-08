//! Split handle-bearing array selections into actual locations. Numeric array
//! operations keep compact multiplexers; handles never acquire invented IDs.
use super::*;

impl Engine<'_, '_> {
    pub(super) fn array_index_cases(
        &mut self,
        state: State,
        element: &Type,
        len: usize,
        index: &Word,
    ) -> Result<Vec<(State, Word)>> {
        // Establish coverage before enumerating valid elements. Otherwise an
        // out-of-bounds execution could disappear from the proof obligation.
        self.bounds(&state, index, len)?;
        if !self.handle_type(element, 0)? {
            return Ok(vec![(state, index.clone())]);
        }
        if len > 64 {
            return Err(Error::limit(
                "symbolic reference-bearing arrays are limited to 64 elements",
            ));
        }
        let mut output = Vec::new();
        for offset in 0..len {
            self.tick()?;
            let fixed = Circuit::constant(offset as u128, index.bits.len(), false);
            let selected = self.circuit.eq_word(index, &fixed);
            let mut branch = state.clone();
            branch.guard = self.circuit.and(branch.guard, selected);
            if self.circuit.satisfy(branch.guard)?.is_some() {
                output.push((branch, fixed));
                self.limit_paths(output.len())?;
            }
        }
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program(
            r#"
          (#enum Maybe () (: Maybe.Some #u8 : Maybe.None))
          (#fn run () () (#return ()))
        "#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        test(&mut Engine::new(&checked, &graph, Span::new(0, 0, 1, 1)));
    }

    #[test]
    fn guarded_elements_cover_exactly_the_admitted_index_domain() {
        with_engine(|engine| {
            let index = engine.circuit.word(64, false);
            let bound = Circuit::constant(3, 64, false);
            let mut state = State::new();
            state.guard = engine.circuit.lt_word(&index, &bound);
            let element = Type::Reference {
                mutable: false,
                target: Box::new(Type::U8),
            };
            let cases = engine
                .array_index_cases(state.clone(), &element, 3, &index)
                .unwrap();
            assert_eq!(cases.len(), 3);
            let mut covered = FALSE;
            for (offset, (branch, fixed)) in cases.iter().enumerate() {
                let constant = Circuit::constant(offset as u128, 64, false);
                assert_eq!(fixed.bits, constant.bits);
                let selected = engine.circuit.eq_word(&index, fixed);
                let outside = engine
                    .circuit
                    .and(branch.guard, engine.circuit.not(selected));
                assert!(engine.circuit.satisfy(outside).unwrap().is_none());
                let repeated = engine.circuit.and(covered, branch.guard);
                assert!(engine.circuit.satisfy(repeated).unwrap().is_none());
                covered = engine.circuit.or(covered, branch.guard);
            }
            let missing = engine.circuit.xor(state.guard, covered);
            assert!(engine.circuit.satisfy(missing).unwrap().is_none());
        });
    }

    #[test]
    fn numeric_elements_keep_one_symbolic_index() {
        with_engine(|engine| {
            let index = engine.circuit.word(64, false);
            let mut state = State::new();
            state.guard = engine
                .circuit
                .lt_word(&index, &Circuit::constant(4, 64, false));
            let cases = engine
                .array_index_cases(state, &Type::U8, 4, &index)
                .unwrap();
            assert_eq!(cases.len(), 1);
            assert_eq!(cases[0].1.bits, index.bits);
        });
    }

    #[test]
    fn unsupported_size_and_unguarded_bounds_do_not_drop_executions() {
        with_engine(|engine| {
            let element = Type::Reference {
                mutable: false,
                target: Box::new(Type::U8),
            };
            let oversized = engine
                .array_index_cases(State::new(), &element, 65, &Circuit::constant(0, 64, false))
                .err()
                .unwrap();
            assert_eq!(
                oversized.diagnostic_code().proof_outcome(),
                Some(crate::ProofOutcome::ResourceLimit)
            );
            let index = engine.circuit.word(64, false);
            let unbounded = engine
                .array_index_cases(State::new(), &element, 2, &index)
                .err()
                .unwrap();
            assert_eq!(
                unbounded.diagnostic_code().proof_outcome(),
                Some(crate::ProofOutcome::Counterexample)
            );
        });
    }

    #[test]
    fn constant_projection_write_does_not_inspect_an_unselected_absent_payload() {
        with_engine(|engine| {
            let mut state = State::new();
            let byte = |value| Value::Bits(Circuit::constant(value, 8, false), Type::U8);
            let present = Value::Enum(
                "Maybe".into(),
                Circuit::constant(0, 64, false),
                vec![Some(byte(1)), None],
            );
            let absent = Value::Enum(
                "Maybe".into(),
                Circuit::constant(1, 64, false),
                vec![None, None],
            );
            let mut place = engine
                .allocate(
                    &mut state,
                    Value::Array(Type::Named("Maybe".into()), vec![present, absent.clone()]),
                )
                .unwrap();
            place.path = vec![
                Segment::Index(Circuit::constant(0, 64, false)),
                Segment::Payload(0),
            ];
            engine.write(&mut state, &place, byte(9)).unwrap();
            let changed = engine.read(&state, &place).unwrap();
            assert_eq!(engine.equal(&changed, &byte(9)).unwrap(), TRUE);
            place.path = vec![Segment::Index(Circuit::constant(1, 64, false))];
            let preserved = engine.read(&state, &place).unwrap();
            assert_eq!(engine.equal(&preserved, &absent).unwrap(), TRUE);
        });
    }
}
