//! Finite call-history monitors composed with checked loop invariants.
//! Backedges forget iteration-local data, retaining only an overapproximation
//! of entry-input guards. Exits come from an actual tested iteration (or the
//! concrete zero-iteration case), never an unrelated abstract false test.
use super::*;

const WAVES: usize = 64;
const RETAINED_BYTES: usize = 64 * 1024 * 1024;

impl<'a, 'p> Engine<'a, 'p> {
    fn trace_config_guards(&mut self, state: &State) -> Vec<Bit> {
        match self.trace.as_ref().unwrap() {
            Trace::When { .. } => (0..4)
                .map(|config| {
                    let observed = state.observed ^ u32::from(config & 1 == 0);
                    let acted = state.acted ^ u32::from(config & 2 == 0);
                    let guard = self.circuit.and(observed, acted);
                    self.circuit.and(state.guard, guard)
                })
                .collect(),
            Trace::Before { .. } => vec![
                self.circuit.and(state.guard, state.required ^ 1),
                self.circuit.and(state.guard, state.required),
            ],
            Trace::Validated(_) => vec![state.guard],
        }
    }

    fn set_trace_config(&self, state: &mut State, config: usize) {
        state.observed = FALSE;
        state.acted = FALSE;
        state.required = FALSE;
        match self.trace.as_ref().unwrap() {
            Trace::When { .. } => {
                state.observed = u32::from(config & 1 != 0);
                state.acted = u32::from(config & 2 != 0);
            }
            Trace::Before { .. } => state.required = u32::from(config != 0),
            Trace::Validated(_) => {}
        }
    }

    fn trace_loop_tests(
        &mut self,
        state: State,
        condition: Option<&Expr>,
    ) -> Result<Vec<(State, Value)>> {
        let tests = if let Some(condition) = condition {
            self.expr(state, condition, false)?
        } else {
            vec![(state, Value::Bool(TRUE))]
        };
        for (state, test) in &tests {
            if state.flow != Flow::Normal {
                return Err(Error::unsupported("induction condition transfers control"));
            }
            test.boolean()?;
        }
        Ok(tests)
    }

    fn trace_loop_exit(
        &mut self,
        output: &mut Vec<(State, Value)>,
        bytes: &mut usize,
        state: State,
        value: Value,
    ) -> Result<()> {
        if self.circuit.satisfy(state.guard)?.is_none() {
            return Ok(());
        }
        self.limit_paths(output.len() + 1)?;
        // The returned value can duplicate the state's value; charge both.
        *bytes = bytes.saturating_add(self.induction_state_bytes(&state)?.saturating_mul(2));
        if *bytes > RETAINED_BYTES {
            return Err(Error::limit(
                "trace induction retained states exceed 64 MiB",
            ));
        }
        output.push((state, value));
        Ok(())
    }

    pub(super) fn inductive_trace_loop(
        &mut self,
        entry: State,
        heads: Vec<State>,
        locals: &BTreeMap<String, (Location, Type)>,
        label: Option<&str>,
        condition: Option<&Expr>,
        body: &[Statement],
        step: Option<&Statement>,
        invariant: &Invariant,
        changing: bool,
        boundary: usize,
    ) -> Result<Option<Vec<(State, Value)>>> {
        let mut initial_exits = Vec::new();
        let mut initial_bytes = 0;
        let mut reachable = vec![FALSE; self.trace_config_guards(&entry).len()];
        for (mut state, test) in self.trace_loop_tests(entry.clone(), condition)? {
            let test = test.boolean()?;
            let mut exit = state.clone();
            exit.guard = self.circuit.and(exit.guard, test ^ 1);
            exit.value = Value::Unit;
            self.trace_loop_exit(&mut initial_exits, &mut initial_bytes, exit, Value::Unit)?;
            state.guard = self.circuit.and(state.guard, test);
            for (slot, guard) in reachable.iter_mut().zip(self.trace_config_guards(&state)) {
                let guard = self.circuit.project_upper(guard, boundary)?;
                *slot = self.circuit.or(*slot, guard);
            }
        }
        for _ in 0..WAVES {
            self.tick()?;
            let mut output = initial_exits.clone();
            let mut bytes = initial_bytes;
            let mut next = reachable.clone();
            for (config, guard) in reachable.iter().copied().enumerate() {
                if self.circuit.satisfy(guard)?.is_none() {
                    continue;
                }
                for head in &heads {
                    let mut state = head.clone();
                    state.guard = self.circuit.and(state.guard, guard);
                    self.set_trace_config(&mut state, config);
                    for (mut state, predicate) in
                        self.loop_predicate(state, &invariant.predicate, true)?
                    {
                        if state.flow != Flow::Normal {
                            return Err(Error::unsupported("invariant transfers control"));
                        }
                        state.guard = self.circuit.and(state.guard, predicate.boolean()?);
                        for (state, old_rank) in self.expr(state, &invariant.rank, true)? {
                            let Value::Bits(old_rank, old_type) = old_rank else {
                                return Err(Error::invalid(
                                    "loop rank must be an unsigned integer",
                                ));
                            };
                            if state.flow != Flow::Normal || old_rank.signed {
                                return Err(Error::invalid(
                                    "loop rank must be a pure unsigned integer",
                                ));
                            }
                            for (mut state, test) in self.trace_loop_tests(state, condition)? {
                                state.guard = self.circuit.and(state.guard, test.boolean()?);
                                if self.circuit.satisfy(state.guard)?.is_none() {
                                    continue;
                                }
                                for mut state in self.statements(vec![state], body)? {
                                    let continuing = state.flow == Flow::Normal
                                        || matches!(&state.flow, Flow::Continue(target)
                                            if target.is_none() || target.as_deref() == label);
                                    if !continuing {
                                        if changing {
                                            self.induction_graph_covers(&heads, &state)?;
                                        } else if !self.induction_shape_fits(&entry, &state)? {
                                            return Ok(None);
                                        }
                                        if matches!(&state.flow, Flow::Break(target)
                                            if target.is_none() || target.as_deref() == label)
                                        {
                                            state.flow = Flow::Normal;
                                        }
                                        state.frames.last_mut().unwrap().locals = locals.clone();
                                        let value = state.value.clone();
                                        self.trace_loop_exit(
                                            &mut output,
                                            &mut bytes,
                                            state,
                                            value,
                                        )?;
                                        continue;
                                    }
                                    state.flow = Flow::Normal;
                                    state.frames.last_mut().unwrap().locals = locals.clone();
                                    let runs = if let Some(step) = step {
                                        self.statement(state, step)?
                                    } else {
                                        vec![state]
                                    };
                                    for mut state in runs {
                                        if state.flow != Flow::Normal {
                                            return Err(Error::unsupported(
                                                "induction step transfers control",
                                            ));
                                        }
                                        state.frames.last_mut().unwrap().locals = locals.clone();
                                        if changing {
                                            self.induction_graph_covers(&heads, &state)?;
                                        } else if !self.induction_shape_fits(&entry, &state)? {
                                            return Ok(None);
                                        }
                                        let preserved = self.loop_predicate(
                                            state.clone(),
                                            &invariant.predicate,
                                            false,
                                        )?;
                                        self.establish(
                                            preserved,
                                            "loop invariant is not preserved",
                                        )?;
                                        for (state, rank) in
                                            self.expr(state, &invariant.rank, true)?
                                        {
                                            let Value::Bits(rank, ty) = rank else {
                                                return Err(Error::invalid(
                                                    "loop rank is not numeric",
                                                ));
                                            };
                                            if state.flow != Flow::Normal
                                                || rank.signed
                                                || rank.bits.len() != old_rank.bits.len()
                                                || ty != old_type
                                            {
                                                return Err(Error::invalid(
                                                    "loop rank type changed or transfers control",
                                                ));
                                            }
                                            let decreases = self.circuit.lt_word(&rank, &old_rank);
                                            let bad = self.circuit.and(state.guard, decreases ^ 1);
                                            self.require_unsat(
                                                bad,
                                                "loop rank does not strictly decrease",
                                            )?;
                                            for (mut state, test) in
                                                self.trace_loop_tests(state, condition)?
                                            {
                                                let test = test.boolean()?;
                                                let mut exit = state.clone();
                                                exit.guard = self.circuit.and(exit.guard, test ^ 1);
                                                exit.value = Value::Unit;
                                                self.trace_loop_exit(
                                                    &mut output,
                                                    &mut bytes,
                                                    exit,
                                                    Value::Unit,
                                                )?;
                                                state.guard = self.circuit.and(state.guard, test);
                                                for (slot, guard) in next
                                                    .iter_mut()
                                                    .zip(self.trace_config_guards(&state))
                                                {
                                                    let guard = self
                                                        .circuit
                                                        .project_upper(guard, boundary)?;
                                                    *slot = self.circuit.or(*slot, guard);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            let mut growing = false;
            for (&new, &old) in next.iter().zip(&reachable) {
                let addition = self.circuit.and(new, old ^ 1);
                growing |= self.circuit.satisfy(addition)?.is_some();
            }
            if !growing {
                return Ok(Some(output));
            }
            reachable = next;
        }
        Err(Error::limit("trace induction fixed point exceeds 64 waves"))
    }
}
