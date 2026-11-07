//! Read-only formulas can share one state after their guarded operations have
//! been checked. Effectful expressions and witness-bearing claims retain paths.
use super::*;
use symbolic::Flow;

impl Engine<'_, '_> {
    pub(super) fn implication(
        &mut self,
        state: State,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        arity("proof-implies", args, 2)?;
        let mut output = Vec::new();
        for (mut state, condition) in self.proposition(state, &args[0])? {
            let condition = condition.boolean()?;
            let original = state.clone();
            let observational = self.is_observation(&state, &args[1], 0);
            let mut false_case = state.clone();
            false_case.guard = self.circuit.and(state.guard, self.circuit.not(condition));
            state.guard = self.circuit.and(state.guard, condition);
            let runs = self.proposition(state, &args[1])?;
            if observational {
                if let Some(value) = self.compact_implication(&original, condition, &runs)? {
                    output.push((original, value));
                    continue;
                }
            }
            output.push((false_case, Value::Bool(TRUE)));
            output.extend(runs);
        }
        Ok(output)
    }

    pub(super) fn is_observation(&self, state: &State, expr: &Expr, depth: usize) -> bool {
        let mut pending = vec![(state, expr, depth)];
        while let Some((state, expr, depth)) = pending.pop() {
            if depth > 64 {
                return false;
            }
            match expr {
                Expr::Symbol(name)
                    if matches!(name.as_str(), "true" | "false")
                        || state
                            .frames
                            .last()
                            .is_some_and(|frame| frame.locals.contains_key(name)) => {}
                Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Char(_) => {}
                Expr::List(items) if items.is_empty() => {}
                Expr::List(_) => {
                    let Some((head, args)) = form(expr) else {
                        return false;
                    };
                    if numeric(head).is_some()
                        || matches!(
                            head,
                            "proof-and"
                                | "proof-or"
                                | "proof-not"
                                | "proof-implies"
                                | "proof-eq"
                                | "if"
                                | "index"
                                | "deref"
                                | "slice-len"
                                | "slice-mut-len"
                                | "slice-idx"
                                | "slice-mut-idx"
                        )
                    {
                        pending.extend(args.iter().map(|arg| (state, arg, depth + 1)));
                        continue;
                    }
                    match head {
                        "literal"
                            if args.len() == 2
                                && matches!(
                                    args[1],
                                    Expr::Integer(_) | Expr::UnsignedInteger(_)
                                ) => {}
                        "get" | "as" | "variant-is" if args.len() == 2 => {
                            pending.push((state, &args[0], depth + 1))
                        }
                        "proof-no-overflow" if args.len() == 3 => {
                            pending.extend(args[1..].iter().map(|arg| (state, arg, depth + 1)))
                        }
                        "proof-result" if args.is_empty() => {}
                        "proof-old" if args.len() == 1 => {
                            let Some(old) = self.old.as_ref() else {
                                return false;
                            };
                            pending.push((old, &args[0], depth + 1));
                        }
                        _ => return false,
                    }
                }
                _ => return false,
            }
        }
        true
    }

    pub(super) fn compact_implication(
        &mut self,
        original: &State,
        condition: Bit,
        runs: &[(State, Value)],
    ) -> Result<Option<Value>> {
        if original.flow != Flow::Normal
            || runs.iter().any(|(state, value)| {
                state.revision() != original.revision()
                    || state.flow != Flow::Normal
                    || matches!(value, Value::Claim(_))
            })
        {
            return Ok(None);
        }
        let required = self.circuit.and(original.guard, condition);
        if let [(state, value)] = runs {
            if state.guard == required {
                // The consequence has exactly the checked input guard. Do not
                // duplicate that entire guard inside the resulting Boolean.
                let truth = value.boolean()?;
                return Ok(Some(Value::Bool(
                    self.circuit.or(self.circuit.not(condition), truth),
                )));
            }
        }
        let mut covered = FALSE;
        let mut holds = self.circuit.not(condition);
        for (state, value) in runs {
            let truth = value.boolean()?;
            covered = self.circuit.or(covered, state.guard);
            let satisfied = self.circuit.and(state.guard, truth);
            holds = self.circuit.or(holds, satisfied);
        }
        let missing = self.circuit.and(required, self.circuit.not(covered));
        if self.circuit.satisfy(missing)?.is_some() {
            return Err(Error::unsupported(
                "read-only implication does not cover every feasible guarded execution",
            ));
        }
        Ok(Some(Value::Bool(holds)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program("(#fn run () () (#return ()))").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        test(&mut Engine::new(&checked, &graph, Span::new(0, 0, 1, 1)));
    }

    #[test]
    fn missing_guarded_executions_cannot_be_compacted_into_a_proof() {
        with_engine(|engine| {
            let state = State::new();
            let condition = engine.circuit.fresh();
            let extra = engine.circuit.fresh();
            let mut incomplete = state.clone();
            incomplete.guard = engine.circuit.and(condition, extra);
            let error = engine
                .compact_implication(&state, condition, &[(incomplete, Value::Bool(TRUE))])
                .unwrap_err();
            assert_eq!(
                error.diagnostic_code(),
                crate::DiagnosticCode::ProofUnsupported
            );
        });
    }

    #[test]
    fn heap_updates_and_counterexample_evidence_keep_separate_executions() {
        with_engine(|engine| {
            let mut state = State::new();
            engine
                .bind(
                    &mut state,
                    "value".into(),
                    Type::U8,
                    Value::Bits(Circuit::constant(0, 8, false), Type::U8),
                )
                .unwrap();
            let place = state.frames.last().unwrap().locals["value"].0.clone();
            let mut updated = state.clone();
            engine
                .write(
                    &mut updated,
                    &place,
                    Value::Bits(Circuit::constant(1, 8, false), Type::U8),
                )
                .unwrap();
            assert!(engine
                .compact_implication(&state, TRUE, &[(updated, Value::Bool(TRUE))])
                .unwrap()
                .is_none());
            let claim = Value::Claim(Box::new(Evidence {
                value: FALSE,
                witnesses: vec![Witness {
                    guard: TRUE,
                    text: "original witness".into(),
                }],
                omitted: false,
            }));
            assert!(engine
                .compact_implication(&state, TRUE, &[(state.clone(), claim)])
                .unwrap()
                .is_none());
        });
    }

    #[test]
    fn compacted_branching_observations_match_the_boolean_truth_table() {
        with_engine(|engine| {
            let state = State::new();
            let condition = engine.circuit.fresh();
            let branch = engine.circuit.fresh();
            let left = engine.circuit.fresh();
            let right = engine.circuit.fresh();
            let mut yes = state.clone();
            yes.guard = engine.circuit.and(condition, branch);
            let mut no = state.clone();
            no.guard = engine.circuit.and(condition, engine.circuit.not(branch));
            let value = engine
                .compact_implication(
                    &state,
                    condition,
                    &[(yes, Value::Bool(left)), (no, Value::Bool(right))],
                )
                .unwrap()
                .unwrap()
                .boolean()
                .unwrap();
            for c in [false, true] {
                for b in [false, true] {
                    for l in [false, true] {
                        for r in [false, true] {
                            let mut assignment = TRUE;
                            for (bit, truth) in [(condition, c), (branch, b), (left, l), (right, r)]
                            {
                                let literal = if truth { bit } else { engine.circuit.not(bit) };
                                assignment = engine.circuit.and(assignment, literal);
                            }
                            let model = engine.circuit.satisfy(assignment).unwrap().unwrap();
                            assert_eq!(
                                Circuit::bit_in_model(value, &model),
                                !c || if b { l } else { r }
                            );
                        }
                    }
                }
            }
        });
    }
}
