//! Input quantification for trace claims. Try the conservative guard first;
//! retry only typed alias uncertainty with complete bounded scalar partitions.
use super::*;

impl<'a, 'p> Engine<'a, 'p> {
    fn trace_input_case(
        &mut self,
        original: &State,
        state: State,
        function: &Function,
        arguments: Vec<Value>,
        input_start: usize,
    ) -> Result<Value> {
        self.inputs.truncate(input_start);
        for (parameter, value) in function.parameters.iter().zip(&arguments) {
            self.inputs.push((parameter.name.clone(), value.clone()));
        }
        self.input_state = Some(state.clone());
        let runs = self.call(state.clone(), function, arguments, false)?;
        if runs.is_empty() {
            return Err(Error::unsupported("no complete execution trace"));
        }
        // Event monitors carry everything this claim needs. Do not retain all
        // completed call heaps while checking the next quantified input case.
        drop(runs);
        let safe = self.circuit.not(self.trace_violation);
        let mut result = self.close_claim(
            original.clone(),
            vec![(state, Value::Bool(safe))],
            input_start,
        )?;
        if result.len() != 1 {
            return Err(Error::checker(
                "closed trace claim did not produce one result",
            ));
        }
        Ok(result.pop().unwrap().1)
    }

    pub(super) fn trace_claim(
        &mut self,
        mut state: State,
        function: &Function,
        trace: Trace,
    ) -> Result<Vec<(State, Value)>> {
        let original = state.clone();
        let input_start = self.inputs.len();
        let previous_input = self.input_state.take();
        let previous_violation = self.trace_violation;
        let previous_induction = self.inductive_witness;
        let previous_alias = self.alias_witness;
        self.trace = Some(trace);
        self.trace_violation = FALSE;
        let result = (|| {
            state.validations.clear();
            let root_start = state.heap_len();
            let mut arguments = Vec::new();
            for parameter in &function.parameters {
                arguments.push(self.fresh_value(&mut state, &parameter.ty, 0)?);
            }
            let attempt = self.trace_input_case(
                &original,
                state.clone(),
                function,
                arguments.clone(),
                input_start,
            );
            let value = match attempt {
                Ok(value) => value,
                Err(error) if error.has_input_alias_uncertainty() => {
                    self.inductive_witness = previous_induction;
                    self.alias_witness = previous_alias;
                    self.trace_violation = FALSE;
                    let Some(cases) = self.scalar_alias_cases(&state, &arguments, root_start)?
                    else {
                        return Err(error);
                    };
                    let mut value = Value::Bool(TRUE);
                    for case in cases {
                        if self.circuit.satisfy(case.state.guard)?.is_none() {
                            continue;
                        }
                        self.inductive_witness = previous_induction;
                        self.alias_witness = previous_alias;
                        self.trace_violation = FALSE;
                        let next = self.trace_input_case(
                            &original,
                            case.state,
                            function,
                            case.arguments,
                            input_start,
                        )?;
                        value = self.combine_claims("proof-and", &value, &next)?;
                    }
                    value
                }
                Err(error) => return Err(error),
            };
            Ok(vec![(original, value)])
        })();
        self.trace = None;
        self.inputs.truncate(input_start);
        self.input_state = previous_input;
        self.trace_violation = previous_violation;
        self.inductive_witness = previous_induction;
        self.alias_witness = previous_alias;
        result
    }
}
