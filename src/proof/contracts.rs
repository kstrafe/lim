//! Explicit reuse of proved contracts. Stored and returned references use
//! checked origins without implicit environment access.
//! Abstract summary results may establish a claim, but cannot refute one.
use super::*;
use symbolic::Frame;

#[derive(Clone)]
pub(super) struct Contract<'p> {
    name: String,
    function: String,
    pre: &'p Expr,
    post: &'p Expr,
    span: Span,
}

pub(super) struct Order {
    pub sequence: Vec<usize>,
    pub providers: BTreeSet<usize>,
}

/// Check all explicit dependencies before evaluating any theorem. A stable,
/// iterative topological order permits forward references without assumptions
/// or an unbounded Rust call stack for long theorem dependency chains.
pub(super) fn order<'p>(
    proofs: &[(&'p String, &'p Expr)],
) -> std::result::Result<Order, (&'p String, Error)> {
    let names = proofs
        .iter()
        .enumerate()
        .map(|(index, (name, _))| (name.as_str(), index))
        .collect::<HashMap<_, _>>();
    let mut required = vec![0; proofs.len()];
    let mut users = vec![Vec::new(); proofs.len()];
    let mut providers = BTreeSet::new();
    for (index, (name, expr)) in proofs.iter().enumerate() {
        let mut dependencies = BTreeSet::new();
        let mut work = vec![*expr];
        while let Some(expr) = work.pop() {
            if let Some(("proof-using", args)) = form(expr) {
                let dependencies_here = (|| {
                    arity("proof-using", args, 2)?;
                    let mut seen = BTreeSet::new();
                    for dependency in list(&args[0])? {
                        let dependency = symbol(dependency)?;
                        if !seen.insert(dependency) {
                            return Err(Error::invalid(
                                "duplicate contract theorem in #proof-using",
                            ));
                        }
                        let Some(&provider) = names.get(dependency) else {
                            return Err(Error::invalid(format!(
                                "unknown contract theorem '{dependency}'"
                            )));
                        };
                        dependencies.insert(provider);
                    }
                    Ok(())
                })();
                dependencies_here.map_err(|error| (*name, error))?;
            }
            if let Expr::List(items) = expr {
                work.extend(items);
            }
        }
        required[index] = dependencies.len();
        for dependency in dependencies {
            providers.insert(dependency);
            users[dependency].push(index);
        }
    }
    let mut ready = required
        .iter()
        .enumerate()
        .filter_map(|(index, &count)| (count == 0).then_some(index))
        .collect::<BTreeSet<_>>();
    let mut output = Vec::with_capacity(proofs.len());
    while let Some(index) = ready.pop_first() {
        output.push(index);
        for &user in &users[index] {
            required[user] -= 1;
            if required[user] == 0 {
                ready.insert(user);
            }
        }
    }
    if output.len() != proofs.len() {
        let index = required.iter().position(|&count| count != 0).unwrap();
        return Err((
            proofs[index].0,
            Error::invalid("cyclic #proof-using theorem dependencies are not assumptions"),
        ));
    }
    Ok(Order {
        sequence: output,
        providers,
    })
}

impl<'a, 'p> Engine<'a, 'p> {
    /// Selected contracts already exclude implicit global/environment access.
    /// Their mutation flag determines whether loop induction needs a write frame.
    pub(super) fn induction_contracts(&mut self) -> Result<BTreeMap<String, bool>> {
        let mut allowed = BTreeMap::new();
        if self.summary_depth != 0 {
            return Ok(allowed);
        }
        for name in self.summaries.keys().cloned().collect::<Vec<_>>() {
            self.tick()?;
            let mutates = self.graph.forbidden_effect(&name, "mutation")?.is_some();
            allowed.insert(name, mutates);
        }
        Ok(allowed)
    }

    pub(super) fn verified_contract(
        &self,
        name: &str,
        mut expr: &'p Expr,
        span: Span,
    ) -> Option<Contract<'p>> {
        // Only wrappers preserving the truth of the entire direct contract
        // qualify. In particular, negation/implication/disjunction cannot
        // smuggle a false contract into the verified summary registry.
        loop {
            let (head, args) = form(expr)?;
            match head {
                "proof-with-invariants" | "proof-loop-limit" | "proof-using" if args.len() == 2 => {
                    expr = &args[1];
                }
                "proof-contract" if args.len() == 3 => {
                    return Some(Contract {
                        name: name.into(),
                        function: symbol(&args[0]).ok()?.into(),
                        pre: &args[1],
                        post: &args[2],
                        span,
                    })
                }
                _ => return None,
            }
        }
    }

    pub(super) fn using_contracts(
        &mut self,
        state: State,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        arity("proof-using", args, 2)?;
        let previous = self.summaries.clone();
        let output = (|| {
            for name in list(&args[0])? {
                let name = symbol(name)?;
                let contract = self
                    .contracts
                    .and_then(|contracts| contracts.get(name))
                    .cloned()
                    .ok_or_else(|| {
                        Error::invalid(format!(
                            "'{name}' is not a verified direct #proof-contract theorem"
                        ))
                    })?;
                self.contract_frame(&contract)?;
                if self
                    .summaries
                    .insert(contract.function.clone(), contract)
                    .is_some()
                {
                    return Err(Error::invalid(
                        "multiple selected contracts for the same function",
                    ));
                }
            }
            self.proposition(state, &args[1])
        })();
        self.summaries = previous;
        output
    }

    fn contract_frame(&mut self, contract: &Contract<'p>) -> Result<()> {
        let function = self.function(&contract.function)?;
        for parameter in &function.parameters {
            self.contract_type(&parameter.ty, 0)?;
        }
        self.contract_type(&function.return_type, 0)?;
        for effect in ["unsafe", "io", "allocation", "external", "asm"] {
            if self
                .graph
                .forbidden_effect(&function.name, effect)?
                .is_some()
            {
                return Err(Error::unsupported(format!(
                    "contract '{}' cannot summarize a function with {effect} effects",
                    contract.name
                )));
            }
        }
        if self.graph.accesses_globals(&function.name)? {
            return Err(Error::unsupported(
                "reusable contracts do not yet summarize implicit global storage reads or writes",
            ));
        }
        Ok(())
    }

    fn contract_type(&mut self, ty: &Type, depth: usize) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("contract frame type nesting exceeds 32"));
        }
        let ty = self.resolve_type(ty)?;
        if !matches!(ty, Type::RawPointer { .. })
            && (scalar(&ty).is_some() || matches!(ty, Type::Unit | Type::Bool))
        {
            return Ok(());
        }
        match ty {
            Type::Reference { target, .. } | Type::PinnedReference { target, .. } =>
            {
                self.contract_type(&target, depth + 1)
            }
            Type::Array(element, _) => self.contract_type(&element, depth + 1),
            Type::Tuple(elements) => {
                for element in elements {
                    self.contract_type(&element, depth + 1)?;
                }
                Ok(())
            }
            Type::Named(name) if self.records.contains_key(&name) => {
                for field in self.records[&name].clone() {
                    self.contract_type(&field.ty, depth + 1)?;
                }
                Ok(())
            }
            Type::Named(name) if self.enums.contains_key(&name) => {
                for variant in self.enums[&name].clone() {
                    for field in variant.fields {
                        self.contract_type(&field, depth + 1)?;
                    }
                }
                Ok(())
            }
            _ => Err(Error::unsupported(
                "reusable contracts require modeled value types; raw pointers and environment values are not modeled",
            )),
        }
    }

    pub(super) fn apply_contract(
        &mut self,
        mut state: State,
        function: &Function,
        arguments: Vec<Value>,
        contract: &Contract<'p>,
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        if self.trace.is_some() {
            return Err(Error::unsupported("result contracts do not summarize execution traces; inspect the function body for trace proofs"));
        }
        let mutates = self
            .graph
            .forbidden_effect(&function.name, "mutation")?
            .is_some();
        if spec && mutates {
            return Err(Error::unsupported(
                "a mutating contract cannot be invoked as a specification call",
            ));
        }
        self.summary_witness = true;
        state.frames.push(Frame {
            function: function.name.clone(),
            locals: BTreeMap::new(),
        });
        for (parameter, value) in function.parameters.iter().zip(arguments.iter().cloned()) {
            self.bind(
                &mut state,
                parameter.name.clone(),
                parameter.ty.clone(),
                value,
            )?;
        }
        let previous_old = self.old.replace(state.clone());
        let previous_span = self.spec_span.replace(contract.span);
        // Contract specification calls are executed, not recursively summarized.
        // This prevents a postcondition calling its own function from looping
        // or assuming the postcondition it is in the process of instantiating.
        self.summary_depth += 1;
        let output = (|| {
            let saved_result = state.result.take();
            let mut output = Vec::new();
            for (mut state, pre) in self.proposition(state, contract.pre)? {
                let condition = pre.boolean()?;
                let bad = self.circuit.and(state.guard, self.circuit.not(condition));
                if self.circuit.satisfy(bad)?.is_some() {
                    return Err(Error::contract(format!(
                        "cannot establish precondition of contract '{}' at call to '{}'",
                        contract.name, function.name
                    )));
                }
                state.guard = self.circuit.and(state.guard, condition);
                let states = if mutates {
                    self.contract_memory_states(state, function, &arguments)?
                } else {
                    vec![state]
                };
                for state in states {
                    for (mut state, result) in
                        self.contract_return_values(state, function, &arguments)?
                    {
                        state.result = Some(result.clone());
                        for (mut state, post) in self.proposition(state, contract.post)? {
                            state.guard = self.circuit.and(state.guard, post.boolean()?);
                            state.result = saved_result.clone();
                            state.frames.pop();
                            output.push((state, result.clone()));
                        }
                        self.limit_paths(output.len())?;
                    }
                    self.limit_paths(output.len())?;
                }
            }
            self.limit_paths(output.len())?;
            Ok(output)
        })();
        self.summary_depth -= 1;
        self.old = previous_old;
        self.spec_span = previous_span;
        output
    }
}
