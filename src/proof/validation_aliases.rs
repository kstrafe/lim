//! Necessary contents equality for validation subjects that might be identical.
//! Equal contents never grant identity. References deliberately contribute no
//! address or pointee constraints; shared input roots can represent aliases.
use super::*;

impl Engine<'_, '_> {
    pub(super) fn validation_contents_may_equal(
        &mut self,
        a: &Value,
        b: &Value,
        depth: usize,
    ) -> Result<Bit> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("validation alias contents nesting exceeds 32"));
        }
        if self.resolve_type(&a.ty())? != self.resolve_type(&b.ty())? {
            return Err(Error::checker(
                "validation subjects have incompatible contents types",
            ));
        }
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => {
                let different = self.circuit.xor(*a, *b);
                Ok(different ^ 1)
            }
            (Value::Bits(a, _), Value::Bits(b, _)) => Ok(self.circuit.eq_word(a, b)),
            (Value::Record(_, a), Value::Record(_, b)) => {
                if a.len() != b.len() || a.iter().zip(b).any(|((a, _), (b, _))| a != b) {
                    return Err(Error::checker("validation record contents shape mismatch"));
                }
                let mut equal = TRUE;
                for ((_, a), (_, b)) in a.iter().zip(b) {
                    let field = self.validation_contents_may_equal(a, b, depth + 1)?;
                    equal = self.circuit.and(equal, field);
                }
                Ok(equal)
            }
            (Value::Array(_, a), Value::Array(_, b)) | (Value::Tuple(a), Value::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(Error::checker(
                        "validation aggregate contents shape mismatch",
                    ));
                }
                let mut equal = TRUE;
                for (a, b) in a.iter().zip(b) {
                    let element = self.validation_contents_may_equal(a, b, depth + 1)?;
                    equal = self.circuit.and(equal, element);
                }
                Ok(equal)
            }
            (Value::Enum(_, a_tag, a), Value::Enum(_, b_tag, b)) => {
                if a.len() != b.len() {
                    return Err(Error::checker("validation enum contents shape mismatch"));
                }
                let mut equal = self.circuit.eq_word(a_tag, b_tag);
                for (index, (a, b)) in a.iter().zip(b).enumerate() {
                    self.tick()?;
                    if let (Some(a), Some(b)) = (a, b) {
                        let payload = self.validation_contents_may_equal(a, b, depth + 1)?;
                        let selected = self
                            .circuit
                            .eq_word(a_tag, &Circuit::constant(index as u128, 64, false));
                        let matches = self.circuit.or(selected ^ 1, payload);
                        equal = self.circuit.and(equal, matches);
                    }
                    // Missing payloads describe inactive constructors. They
                    // are not data differences that can establish identity.
                }
                Ok(equal)
            }
            (Value::Slice(a), Value::Slice(b)) => {
                // Length is an intrinsic part of a stored slice value. Start
                // offsets are relative to modeled backing allocations, whose
                // physical relationships may differ between input roots.
                Ok(self.circuit.eq_word(&a.len, &b.len))
            }
            (Value::Ref { .. }, Value::Ref { .. })
            | (Value::Unit, Value::Unit)
            | (Value::Claim(_), _)
            | (_, Value::Claim(_)) => Ok(TRUE),
            _ => Err(Error::checker(
                "validation contents representation mismatch",
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use symbolic::{Location, Slice};

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program("(#fn entry () () (#return ()))").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        test(&mut Engine::new(&checked, &graph, Span::new(0, 0, 1, 1)));
    }
    fn byte(value: u128) -> Value {
        Value::Bits(Circuit::constant(value, 8, false), Type::U8)
    }
    fn reference(root: usize) -> Value {
        Value::Ref {
            place: Location { root, path: vec![] },
            target: Type::U8,
            mutable: false,
            pinned: false,
        }
    }

    #[test]
    fn value_refinement_matches_every_assignment_of_small_symbolic_contents() {
        with_engine(|engine| {
            let mut a = Circuit::constant(0, 8, false);
            let mut b = Circuit::constant(0, 8, false);
            for index in 0..2 {
                a.bits[index] = engine.circuit.fresh();
                b.bits[index] = engine.circuit.fresh();
            }
            let av = Value::Tuple(vec![
                Value::Array(Type::U8, vec![Value::Bits(a.clone(), Type::U8), byte(7)]),
                Value::Bool(a.bits[0]),
            ]);
            let bv = Value::Tuple(vec![
                Value::Array(Type::U8, vec![Value::Bits(b.clone(), Type::U8), byte(7)]),
                Value::Bool(b.bits[0]),
            ]);
            let equal = engine.validation_contents_may_equal(&av, &bv, 0).unwrap();
            for left in 0..4 {
                for right in 0..4 {
                    let mut model = vec![false; engine.circuit.input_boundary() + 1];
                    for index in 0..2 {
                        model[(a.bits[index] >> 1) as usize] = left & (1 << index) != 0;
                        model[(b.bits[index] >> 1) as usize] = right & (1 << index) != 0;
                    }
                    assert_eq!(engine.circuit.eval(equal, &model), left == right);
                }
            }
        });
    }

    #[test]
    fn reference_root_numbers_and_referent_contents_do_not_establish_distinction() {
        with_engine(|engine| {
            assert_eq!(
                engine
                    .validation_contents_may_equal(&reference(0), &reference(999), 0)
                    .unwrap(),
                TRUE
            );
            let a = Value::Record(
                "Holder".into(),
                vec![("id".into(), byte(7)), ("link".into(), reference(0))],
            );
            let mut b = Value::Record(
                "Holder".into(),
                vec![("id".into(), byte(7)), ("link".into(), reference(999))],
            );
            assert_eq!(
                engine.validation_contents_may_equal(&a, &b, 0).unwrap(),
                TRUE
            );
            let Value::Record(_, fields) = &mut b else {
                unreachable!()
            };
            fields[0].1 = byte(8);
            assert_eq!(
                engine.validation_contents_may_equal(&a, &b, 0).unwrap(),
                FALSE
            );
        });
    }

    #[test]
    fn slice_length_is_intrinsic_but_backing_and_start_are_not_compared() {
        with_engine(|engine| {
            let view = |root, start, len| {
                Value::Slice(Slice {
                    place: Location { root, path: vec![] },
                    element: Type::U8,
                    start: Circuit::constant(start, 64, false),
                    len: Circuit::constant(len, 64, false),
                    mutable: false,
                })
            };
            assert_eq!(
                engine
                    .validation_contents_may_equal(&view(1, 0, 2), &view(99, 17, 2), 0)
                    .unwrap(),
                TRUE
            );
            assert_eq!(
                engine
                    .validation_contents_may_equal(&view(1, 0, 2), &view(99, 0, 3), 0)
                    .unwrap(),
                FALSE
            );
        });
    }

    #[test]
    fn only_active_enum_payloads_constrain_contents() {
        with_engine(|engine| {
            let value = |tag, payload| {
                Value::Enum(
                    "Choice".into(),
                    Circuit::constant(tag, 64, false),
                    vec![None, payload],
                )
            };
            assert_eq!(
                engine
                    .validation_contents_may_equal(
                        &value(0, Some(byte(1))),
                        &value(0, Some(byte(2))),
                        0
                    )
                    .unwrap(),
                TRUE
            );
            assert_eq!(
                engine
                    .validation_contents_may_equal(
                        &value(1, Some(byte(1))),
                        &value(1, Some(byte(2))),
                        0
                    )
                    .unwrap(),
                FALSE
            );
            assert_eq!(
                engine
                    .validation_contents_may_equal(&value(0, None), &value(0, Some(byte(2))), 0)
                    .unwrap(),
                TRUE
            );
            assert_eq!(
                engine
                    .validation_contents_may_equal(&value(0, None), &value(1, Some(byte(2))), 0)
                    .unwrap(),
                FALSE
            );
        });
    }

    #[test]
    fn malformed_representations_and_depth_exhaustion_are_errors() {
        with_engine(|engine| {
            let a = Value::Record("Broken".into(), vec![("first".into(), byte(0))]);
            let b = Value::Record("Broken".into(), vec![("second".into(), byte(0))]);
            let error = engine.validation_contents_may_equal(&a, &b, 0).unwrap_err();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::CheckerError)
            );
            let error = engine
                .validation_contents_may_equal(&Value::Unit, &Value::Unit, 33)
                .unwrap_err();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::ResourceLimit)
            );
        });
    }

    #[test]
    fn inactive_enum_payload_visits_are_charged_to_the_work_budget() {
        with_engine(|engine| {
            engine.steps = 99_998;
            let value = Value::Enum(
                "Choice".into(),
                Circuit::constant(0, 64, false),
                vec![None, None],
            );
            let error = engine
                .validation_contents_may_equal(&value, &value, 0)
                .unwrap_err();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(ProofOutcome::ResourceLimit)
            );
        });
    }
}
