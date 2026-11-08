//! Collection predicates observe current modeled storage. Slice membership is
//! a guard on each backing element, so symbolic ranges need no path enumeration.
use super::*;

struct Collection {
    element: Type,
    entries: Vec<(Bit, Value)>,
    len: Word,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program(
            "(#fn less (: left #u8 : right #u8) #bool (#return (#u8::lt left right)))",
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        test(&mut Engine::new(&checked, &graph, Span::new(0, 0, 1, 1)));
    }

    fn assign(model: &mut [bool], word: &Word, value: usize) {
        for (index, bit) in word.bits.iter().enumerate() {
            if *bit > TRUE {
                model[(bit >> 1) as usize] = ((value >> index) & 1 != 0) ^ (bit & 1 != 0);
            }
        }
    }

    fn byte(engine: &mut Engine<'_, '_>) -> Word {
        let mut word = Circuit::constant(0, 8, false);
        word.bits[0] = engine.circuit.fresh();
        word.bits[1] = engine.circuit.fresh();
        word
    }

    #[test]
    fn symbolic_membership_and_properties_match_every_valid_small_range() {
        with_engine(|engine| {
            let mut state = State::new();
            let values = [3u128, 1, 1, 2];
            let array = Value::Array(
                Type::U8,
                values
                    .iter()
                    .map(|value| Value::Bits(Circuit::constant(*value, 8, false), Type::U8))
                    .collect(),
            );
            let place = engine.allocate(&mut state, array).unwrap();
            let mut start = Circuit::constant(0, 64, false);
            let mut end = start.clone();
            for index in 0..3 {
                start.bits[index] = engine.circuit.fresh();
                end.bits[index] = engine.circuit.fresh();
            }
            let reversed = engine.circuit.lt_word(&end, &start);
            let beyond = engine
                .circuit
                .lt_word(&Circuit::constant(4, 64, false), &end);
            let bad = engine.circuit.or(reversed, beyond);
            state.guard = bad ^ 1;
            let len = engine
                .circuit
                .binary("sub", Some("wrap"), &end, &start)
                .unwrap()
                .0;
            let collection = engine
                .collection(
                    &state,
                    Value::Slice(Slice {
                        place,
                        element: Type::U8,
                        start: start.clone(),
                        len,
                        mutable: false,
                    }),
                )
                .unwrap();
            let unique = engine.collection_unique(&state, &collection).unwrap();
            let comparator = engine.function("less").unwrap();
            let sorted = engine
                .collection_sorted(&state, &collection, comparator)
                .unwrap();
            for first in 0..=4 {
                for last in first..=4 {
                    let mut model = vec![false; engine.circuit.input_boundary() + 1];
                    assign(&mut model, &start, first);
                    assign(&mut model, &end, last);
                    for (index, (active, _)) in collection.entries.iter().enumerate() {
                        assert_eq!(
                            engine.circuit.eval(*active, &model),
                            (first..last).contains(&index)
                        );
                    }
                    let selected = &values[first..last];
                    assert_eq!(
                        engine.circuit.eval(unique, &model),
                        selected.iter().collect::<BTreeSet<_>>().len() == selected.len()
                    );
                    assert_eq!(
                        engine.circuit.eval(sorted, &model),
                        selected.windows(2).all(|pair| pair[0] <= pair[1])
                    );
                }
            }
        });
    }

    #[test]
    fn multiplicities_and_uniqueness_match_exhaustive_small_value_assignments() {
        with_engine(|engine| {
            let state = State::new();
            let words = (0..6).map(|_| byte(engine)).collect::<Vec<_>>();
            let make = |values: &[Word]| Collection {
                element: Type::U8,
                len: Circuit::constant(values.len() as u128, 64, false),
                entries: values
                    .iter()
                    .map(|word| (TRUE, Value::Bits(word.clone(), Type::U8)))
                    .collect(),
            };
            let left = make(&words[..3]);
            let right = make(&words[3..]);
            let permutation = engine
                .collection_permutation(&state, &left, &right)
                .unwrap();
            let unique = engine.collection_unique(&state, &left).unwrap();
            for mut assignment in 0..4096 {
                let mut model = vec![false; engine.circuit.input_boundary() + 1];
                let mut values = Vec::new();
                for word in &words {
                    let value = assignment & 3;
                    assignment >>= 2;
                    assign(&mut model, word, value);
                    values.push(value);
                }
                let mut expected_left = values[..3].to_vec();
                let mut expected_right = values[3..].to_vec();
                expected_left.sort();
                expected_right.sort();
                assert_eq!(
                    engine.circuit.eval(permutation, &model),
                    expected_left == expected_right
                );
                assert_eq!(
                    engine.circuit.eval(unique, &model),
                    expected_left.windows(2).all(|pair| pair[0] != pair[1])
                );
            }
        });
    }
}

impl Engine<'_, '_> {
    fn collection(&mut self, state: &State, value: Value) -> Result<Collection> {
        self.tick()?;
        match value {
            Value::Array(element, values) => {
                if values.len() > 64 {
                    return Err(Error::limit(
                        "collection properties support at most 64 elements",
                    ));
                }
                Ok(Collection {
                    element,
                    len: Circuit::constant(values.len() as u128, 64, false),
                    entries: values.into_iter().map(|value| (TRUE, value)).collect(),
                })
            }
            Value::Slice(view) => {
                let values = self.slice_backing_values(state, &view, TRUE)?;
                let mut entries = Vec::with_capacity(values.len());
                for (index, value) in values.into_iter().enumerate() {
                    self.tick()?;
                    let index = Circuit::constant(index as u128, 64, false);
                    let before = self.circuit.lt_word(&index, &view.start);
                    let offset = self
                        .circuit
                        .binary("sub", Some("wrap"), &index, &view.start)?
                        .0;
                    let within = self.circuit.lt_word(&offset, &view.len);
                    let active = self.circuit.and(before ^ 1, within);
                    entries.push((active, value));
                }
                Ok(Collection {
                    element: view.element,
                    entries,
                    len: view.len,
                })
            }
            _ => Err(Error::invalid(
                "a collection theorem requires a fixed array or modeled slice value",
            )),
        }
    }

    fn collection_match(
        &mut self,
        state: &State,
        a: &Value,
        b: &Value,
        active: Bit,
    ) -> Result<Bit> {
        self.tick()?;
        if active == FALSE {
            return Ok(FALSE);
        }
        match self.equal(a, b) {
            Ok(equal) => Ok(self.circuit.and(active, equal)),
            Err(error) if error.diagnostic_code() == crate::DiagnosticCode::ProofUnsupported => {
                // An unselected backing element contributes no comparison.
                // Infeasibility cannot discard checker or resource failures.
                let used = self.circuit.and(state.guard, active);
                if self.circuit.satisfy(used)?.is_none() {
                    Ok(FALSE)
                } else {
                    Err(error)
                }
            }
            Err(error) => Err(error),
        }
    }

    fn collection_count(
        &mut self,
        state: &State,
        value: &Value,
        values: &Collection,
    ) -> Result<Word> {
        // A backing array contains at most 64 elements; an eight-bit count
        // cannot wrap even when every selected element compares equal.
        let mut count = Circuit::constant(0, 8, false);
        for (active, candidate) in &values.entries {
            let matched = self.collection_match(state, value, candidate, *active)?;
            let mut add = Circuit::constant(0, 8, false);
            add.bits[0] = matched;
            count = self.circuit.binary("add", Some("wrap"), &count, &add)?.0;
        }
        Ok(count)
    }

    fn collection_permutation(
        &mut self,
        state: &State,
        a: &Collection,
        b: &Collection,
    ) -> Result<Bit> {
        if self.resolve_type(&a.element)? != self.resolve_type(&b.element)? {
            return Err(Error::invalid(
                "permutation collections must have the same element type",
            ));
        }
        let mut result = self.circuit.eq_word(&a.len, &b.len);
        if result == FALSE {
            return Ok(FALSE);
        }
        for (active, value) in &a.entries {
            self.tick()?;
            if *active == FALSE {
                continue;
            }
            let mut selected = state.clone();
            selected.guard = self.circuit.and(selected.guard, result);
            selected.guard = self.circuit.and(selected.guard, *active);
            if self.circuit.satisfy(selected.guard)?.is_none() {
                continue;
            }
            let left = self.collection_count(&selected, value, a)?;
            let right = self.collection_count(&selected, value, b)?;
            let equal = self.circuit.eq_word(&left, &right);
            let valid = self.circuit.or(*active ^ 1, equal);
            result = self.circuit.and(result, valid);
        }
        Ok(result)
    }

    fn collection_unique(&mut self, state: &State, values: &Collection) -> Result<Bit> {
        let mut result = TRUE;
        for (index, (active, value)) in values.entries.iter().enumerate() {
            for (other_active, other) in &values.entries[index + 1..] {
                let both = self.circuit.and(*active, *other_active);
                let matched = self.collection_match(state, value, other, both)?;
                result = self.circuit.and(result, matched ^ 1);
            }
        }
        Ok(result)
    }

    fn collection_sorted(
        &mut self,
        state: &State,
        values: &Collection,
        comparator: &Function,
    ) -> Result<Bit> {
        if self.resolve_type(&comparator.return_type)? != Type::Bool
            || comparator.parameters.len() != 2
        {
            return Err(Error::invalid(
                "sort comparator must take two explicit values and return #bool",
            ));
        }
        for parameter in &comparator.parameters {
            if self.resolve_type(&parameter.ty)? != self.resolve_type(&values.element)? {
                return Err(Error::invalid(
                    "sort comparator parameter types must match the collection element type",
                ));
            }
        }
        let mut result = TRUE;
        for pair in values.entries.windows(2) {
            self.tick()?;
            // A slice is contiguous: selected adjacent backing elements are
            // exactly its adjacent elements. Never call on excluded values.
            let active = self.circuit.and(pair[0].0, pair[1].0);
            let mut selected = state.clone();
            selected.guard = self.circuit.and(selected.guard, active);
            if self.circuit.satisfy(selected.guard)?.is_none() {
                continue;
            }
            let calls = self.call(
                selected,
                comparator,
                vec![pair[1].1.clone(), pair[0].1.clone()],
                true,
            )?;
            for (run, value) in calls {
                let valid = self.circuit.or(run.guard ^ 1, value.boolean()? ^ 1);
                result = self.circuit.and(result, valid);
            }
        }
        Ok(result)
    }

    pub(in crate::proof) fn collection_property(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        arity(head, args, if head == "proof-unique" { 1 } else { 2 })?;
        let mut output = Vec::new();
        for (state, a) in self.expr(state, &args[0], true)? {
            let a = self.collection(&state, a)?;
            match head {
                "proof-sorted" => {
                    let comparator = self.function(symbol(&args[1])?)?;
                    let result = self.collection_sorted(&state, &a, comparator)?;
                    output.push((state, Value::Bool(result)));
                }
                "proof-unique" => {
                    let result = self.collection_unique(&state, &a)?;
                    output.push((state, Value::Bool(result)));
                }
                "proof-permutation" => {
                    for (state, b) in self.expr(state, &args[1], true)? {
                        let b = self.collection(&state, b)?;
                        let result = self.collection_permutation(&state, &a, &b)?;
                        output.push((state, Value::Bool(result)));
                    }
                }
                _ => return Err(Error::checker("unknown collection property")),
            }
            self.limit_paths(output.len())?;
        }
        Ok(output)
    }
}
