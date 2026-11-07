//! Quantified obligations keep their input/state frames off the recursive
//! Boolean dispatcher stack. They still use the ordinary validated program.
use super::*;

impl Engine<'_, '_> {
    pub(super) fn quantified_values(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        arity(head, args, 2)?;
        if self.quantified {
            return Err(Error::unsupported(
                "nested quantified claims are unsupported; combine #proof-for-all bindings",
            ));
        }
        self.quantified = true;
        let original = state.clone();
        let input_start = self.inputs.len();
        let mut state = state;
        for binding in list(&args[0])? {
            let binding = list(binding)?;
            if binding.len() != 2 {
                return Err("#proof-for-all requires (name Type) pairs".into());
            }
            let name = symbol(&binding[0])?.to_owned();
            if state.frames.last().unwrap().locals.contains_key(&name) {
                return Err(format!("proof binding '{name}' shadows an existing binding").into());
            }
            let ty = proof_type(&binding[1], true)?;
            let value = self.fresh_value(&mut state, &ty, 0)?;
            self.inputs.push((name.clone(), value.clone()));
            self.bind(&mut state, name, ty, value)?;
        }
        self.input_state = Some(state.clone());
        let runs = self.proposition(state, &args[1])?;
        self.quantified = false;
        self.close_claim(original, runs, input_start)
    }

    pub(super) fn contract_claim(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        arity(head, args, 3)?;
        if self.quantified {
            return Err(Error::unsupported(
                "nested quantified claims are unsupported",
            ));
        }
        self.quantified = true;
        let original = state.clone();
        let input_start = self.inputs.len();
        if !state.frames.last().unwrap().locals.is_empty() {
            return Err("a contract quantifies its own declared function parameters; put it outside #proof-for-all".into());
        }
        let function = self.function(symbol(&args[0])?)?;
        let mut arguments = Vec::new();
        let mut state = state;
        for parameter in &function.parameters {
            let value = self.fresh_value(&mut state, &parameter.ty, 0)?;
            self.inputs.push((parameter.name.clone(), value.clone()));
            self.bind(
                &mut state,
                parameter.name.clone(),
                parameter.ty.clone(),
                value.clone(),
            )?;
            arguments.push(value);
        }
        self.old = Some(state.clone());
        self.input_state = Some(state.clone());
        let mut output = Vec::new();
        for (mut state, pre) in self.proposition(state, &args[1])? {
            let pre = pre.boolean()?;
            state.guard = self.circuit.and(state.guard, pre);
            for (mut state, result) in self.call(state, function, arguments.clone(), false)? {
                if self.verify_reference_origins {
                    self.verify_contract_return(&state, function, &arguments, &result)?;
                    let entry = self
                        .old
                        .clone()
                        .ok_or_else(|| Error::checker("missing contract entry snapshot"))?;
                    self.verify_contract_stores(&entry, &state, function, &arguments)?;
                }
                state.result = Some(result);
                output.extend(self.proposition(state, &args[2])?);
            }
        }
        self.old = None;
        self.quantified = false;
        self.close_claim(original, output, input_start)
    }
}
