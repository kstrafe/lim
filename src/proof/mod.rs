//! Compile-time propositions checked against the validated, expanded program.
//! No theorem is an assumption: unsupported semantics and exhausted budgets fail.
mod contracts;
mod counterexample;
mod graph;
#[cfg(test)]
mod induction_tests;
mod logic;
mod outcome;
mod symbolic;
mod validation;

use crate::typecheck::{AnalysisError, CheckedProgram};
use crate::{Expr, Function, Item, Span, Type};
use counterexample::{Evidence, Witness};
use graph::Graph;
use logic::{Bit, Circuit, Word, FALSE, TRUE};
use outcome::Error;
pub use outcome::ProofOutcome;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use symbolic::{State, Value};
use validation::ValidationRule;

type Result<T> = std::result::Result<T, Error>;

#[derive(Clone)]
struct Invariant {
    predicate: Expr,
    rank: Expr,
}

#[derive(Clone)]
enum Trace {
    When {
        observed: String,
        expected: bool,
        action: String,
    },
    Before {
        required: String,
        action: String,
    },
    Validated(ValidationRule),
}

impl Trace {
    fn action(&self) -> &str {
        match self {
            Self::When { action, .. } | Self::Before { action, .. } => action,
            Self::Validated(rule) => &rule.action,
        }
    }
}

struct Engine<'a, 'p> {
    checked: &'a CheckedProgram<'p>,
    graph: &'a Graph,
    circuit: Circuit,
    functions: HashMap<String, &'p Function>,
    aliases: HashMap<String, Type>,
    records: HashMap<String, Vec<crate::Field>>,
    enums: HashMap<String, Vec<crate::EnumVariant>>,
    opaque: BTreeSet<String>,
    constants: HashMap<String, (Type, Expr)>,
    globals: HashMap<String, Type>,
    span: Span,
    inputs: Vec<(String, Value)>,
    input_state: Option<State>,
    inductive_witness: bool,
    summary_witness: bool,
    contracts: Option<&'a HashMap<String, contracts::Contract<'p>>>,
    summaries: HashMap<String, contracts::Contract<'p>>,
    summary_depth: usize,
    spec_span: Option<Span>,
    checked_expression_depth: usize,
    old: Option<State>,
    steps: usize,
    loop_limit: usize,
    invariants: HashMap<(String, String), Invariant>,
    trace: Option<Trace>,
    trace_violation: Bit,
    depth: usize,
    quantified: bool,
    evaluation_depth: usize,
}

pub(crate) fn check(checked: &CheckedProgram<'_>) -> std::result::Result<(), AnalysisError> {
    let proofs = checked
        .program()
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Proof { name, proposition } => Some((name, proposition)),
            _ => None,
        })
        .collect::<Vec<_>>();
    if proofs.is_empty() {
        return Ok(());
    }
    let _timing = crate::timing::stage("proof");
    let graph = Graph::new(checked.program(), checked.declarations());
    let order = contracts::order(&proofs).map_err(|(name, error)| {
        AnalysisError::from((
            format!(
                "theorem '{}': {error}",
                crate::file_access::local_name(name)
            ),
            error.diagnostic_code(),
            declaration_span(checked.program(), name),
            Vec::new(),
        ))
    })?;
    let mut verified = HashMap::new();
    for index in order {
        let (name, proposition) = proofs[index];
        let span =
            declaration_span(checked.program(), name).unwrap_or_else(|| Span::new(0, 0, 1, 1));
        let mut engine = Engine::new(checked, &graph, span);
        engine.contracts = Some(&verified);
        let outcome = engine
            .proposition(State::new(), proposition)
            .and_then(|states| engine.establish(states, "the proposition is false"));
        if let Err(message) = outcome {
            let code = message.diagnostic_code();
            return Err((
                format!(
                    "theorem '{}': {message}",
                    crate::file_access::local_name(name)
                ),
                code,
                Some(span),
                Vec::new(),
            )
                .into());
        }
        if let Some(contract) = engine.verified_contract(name, proposition, span) {
            verified.insert(name.clone(), contract);
        }
    }
    Ok(())
}

impl<'a, 'p> Engine<'a, 'p> {
    fn new(checked: &'a CheckedProgram<'p>, graph: &'a Graph, span: Span) -> Self {
        let mut engine = Self {
            checked,
            graph,
            circuit: Circuit::new(),
            functions: HashMap::new(),
            aliases: HashMap::new(),
            records: HashMap::new(),
            enums: HashMap::new(),
            opaque: BTreeSet::new(),
            constants: HashMap::new(),
            globals: HashMap::new(),
            span,
            inputs: Vec::new(),
            input_state: None,
            inductive_witness: false,
            summary_witness: false,
            contracts: None,
            summaries: HashMap::new(),
            summary_depth: 0,
            spec_span: None,
            checked_expression_depth: 0,
            old: None,
            steps: 0,
            loop_limit: 32,
            invariants: HashMap::new(),
            trace: None,
            trace_violation: FALSE,
            depth: 0,
            quantified: false,
            evaluation_depth: 0,
        };
        for item in &checked.program().items {
            match item {
                Item::Function(function) => {
                    engine.functions.insert(function.name.clone(), function);
                }
                Item::TypeAlias { name, target, .. } => {
                    engine.aliases.insert(name.clone(), target.clone());
                }
                Item::Struct { name, fields, .. } => {
                    engine.records.insert(name.clone(), fields.clone());
                }
                Item::Enum { name, variants, .. } => {
                    engine.enums.insert(name.clone(), variants.clone());
                }
                Item::OpaqueAnnotation { type_name } => {
                    engine.opaque.insert(type_name.clone());
                }
                Item::Let {
                    name,
                    ty,
                    value,
                    mutable: false,
                } => {
                    engine
                        .constants
                        .insert(name.clone(), (ty.clone(), value.clone()));
                }
                Item::Let { name, ty, .. } | Item::Static { name, ty, .. } => {
                    engine.globals.insert(name.clone(), ty.clone());
                }
                _ => {}
            }
        }
        engine
    }

    fn tick(&mut self) -> Result<()> {
        self.steps += 1;
        if self.steps > 100_000 {
            return Err(Error::limit("symbolic execution budget exhausted"));
        }
        Ok(())
    }

    fn function(&self, name: &str) -> Result<&'p Function> {
        self.functions
            .get(name)
            .copied()
            .ok_or_else(|| Error::invalid(format!("unknown proof function '{name}'")))
    }

    fn establish(&mut self, states: Vec<(State, Value)>, explanation: &str) -> Result<()> {
        if states.is_empty() {
            return Err(Error::unsupported(
                "the proposition produced no logical value",
            ));
        }
        for (state, value) in states {
            let condition = value.boolean()?;
            let bad = self.circuit.and(state.guard, self.circuit.not(condition));
            self.require_unsat_with_evidence(bad, explanation, Some(&value))?;
        }
        // Budget exhaustion remains an error even if simplification returned true.
        self.circuit.satisfy(FALSE)?;
        Ok(())
    }

    fn require_unsat(&mut self, bad: Bit, explanation: &str) -> Result<()> {
        self.require_unsat_with_evidence(bad, explanation, None)
    }

    fn require_unsat_with_evidence(
        &mut self,
        bad: Bit,
        explanation: &str,
        value: Option<&Value>,
    ) -> Result<()> {
        match self
            .circuit
            .satisfy(bad)
            .map_err(|why| why.context(format!("while checking {explanation}")))?
        {
            None => Ok(()),
            Some(model) => {
                if self.summary_witness {
                    return Err(Error::contract(format!("{explanation}; selected contracts do not establish this obligation; an abstract result is not a concrete execution counterexample")));
                }
                if let Some(example) = value.and_then(|value| self.claim_evidence(value, &model)) {
                    return Err(Error::counterexample(format!(
                        "{explanation}; quantified counterexample: {example}"
                    )));
                }
                let examples = self.render_inputs(0, &model);
                if self.inductive_witness {
                    return Err(Error::induction(format!("{explanation}; inductive obligation witness (initial inputs are not a concrete execution replay): {examples}")));
                }
                Err(Error::counterexample(format!(
                    "{explanation}; counterexample: {}",
                    if examples.is_empty() {
                        "no named input bindings"
                    } else {
                        &examples
                    }
                )))
            }
        }
    }

    fn close_claim(
        &mut self,
        original: State,
        runs: Vec<(State, Value)>,
        input_start: usize,
    ) -> Result<Vec<(State, Value)>> {
        if runs.is_empty() {
            return Err(Error::unsupported("no complete symbolic executions"));
        }
        let mut violations = Vec::with_capacity(runs.len());
        for (state, value) in runs {
            let invalid = self
                .circuit
                .and(state.guard, self.circuit.not(value.boolean()?));
            violations.push(invalid);
        }
        // A claim fails if any complete path admits a counterexample. Checking
        // each path separately keeps its guard available to propagation, and
        // avoids a large disjunction of mutually exclusive execution states.
        let mut model = None;
        for invalid in violations {
            model = self
                .circuit
                .satisfy(invalid)
                .map_err(|why| why.context("while checking a complete execution"))?;
            if model.is_some() {
                break;
            }
        }
        let value = if let Some(model) = &model {
            if self.summary_witness {
                return Err(Error::contract("selected contracts do not establish the claim; an abstract result is not a concrete execution counterexample"));
            }
            let inputs = self.render_inputs(input_start, model);
            if self.inductive_witness {
                // A model of an over-approximated loop state does not refute
                // the program contract. In particular its negation must not
                // turn an insufficient invariant into a proved theorem.
                return Err(Error::induction(format!("supplied invariants do not establish the claim; inductive obligation witness (initial inputs are not a concrete execution replay): {inputs}")));
            }
            let example = if let Some(Trace::Validated(rule)) = &self.trace {
                let explanation = format!("'{}' can be called without completed successful '{}' validation of the same object (or after that validation was invalidated)", crate::file_access::local_name(&rule.action), crate::file_access::local_name(&rule.validator));
                if inputs.is_empty() {
                    explanation
                } else {
                    format!("{explanation}; {inputs}")
                }
            } else {
                if inputs.is_empty() {
                    "no named input bindings".into()
                } else {
                    inputs
                }
            };
            Value::Claim(Box::new(Evidence {
                value: FALSE,
                witnesses: vec![Witness {
                    guard: TRUE,
                    text: example.into(),
                }],
                omitted: false,
            }))
        } else {
            Value::Bool(TRUE)
        };
        self.inputs.truncate(input_start);
        self.input_state = None;
        self.inductive_witness = false;
        // Keep abstraction provenance for the entire theorem. A later logical
        // subclaim may still carry a guard/result derived from an earlier call.
        Ok(vec![(original, value)])
    }

    fn proposition(&mut self, state: State, expr: &Expr) -> Result<Vec<(State, Value)>> {
        if self.evaluation_depth >= 32 {
            return Err(Error::limit("proof evaluation nesting exceeds 32"));
        }
        self.evaluation_depth += 1;
        let output = self.proposition_inner(state, expr);
        self.evaluation_depth -= 1;
        output
    }

    fn proposition_inner(&mut self, state: State, expr: &Expr) -> Result<Vec<(State, Value)>> {
        self.tick()?;
        let Some((head, args)) = form(expr) else {
            return self.expr(state, expr, true);
        };
        match head {
            "proof-using" => self.using_contracts(state, args),
            "proof-and" | "proof-or" => {
                if args.is_empty() {
                    return Err(format!("#{head} requires at least one proposition").into());
                }
                let mut states = vec![(
                    state,
                    Value::Bool(if head == "proof-and" { TRUE } else { FALSE }),
                )];
                for argument in args {
                    let mut next = Vec::new();
                    for (state, previous) in states {
                        for (state, value) in self.proposition(state, argument)? {
                            let result = self.combine_claims(head, &previous, &value)?;
                            next.push((state, result));
                        }
                    }
                    self.limit_paths(next.len())?;
                    states = next;
                }
                Ok(states)
            }
            "proof-not" => {
                arity(head, args, 1)?;
                self.proposition(state, &args[0])?
                    .into_iter()
                    .map(|(state, value)| {
                        Ok((state, Value::Bool(self.circuit.not(value.boolean()?))))
                    })
                    .collect()
            }
            "proof-implies" => {
                arity(head, args, 2)?;
                let mut output = Vec::new();
                for (mut state, condition) in self.proposition(state, &args[0])? {
                    let condition = condition.boolean()?;
                    let mut false_case = state.clone();
                    false_case.guard = self.circuit.and(state.guard, self.circuit.not(condition));
                    output.push((false_case, Value::Bool(TRUE)));
                    state.guard = self.circuit.and(state.guard, condition);
                    output.extend(self.proposition(state, &args[1])?);
                }
                Ok(output)
            }
            "proof-eq" => {
                arity(head, args, 2)?;
                let mut output = Vec::new();
                for (state, a) in self.expr(state, &args[0], true)? {
                    for (state, b) in self.expr(state, &args[1], true)? {
                        let same = self.equal(&a, &b)?;
                        output.push((state, Value::Bool(same)));
                    }
                }
                Ok(output)
            }
            "proof-calls-directly" | "proof-calls-transitively" => {
                arity(head, args, 2)?;
                let from = symbol(&args[0])?;
                let to = symbol(&args[1])?;
                let found = self
                    .graph
                    .path(from, to, head == "proof-calls-directly")?
                    .is_some();
                if !found {
                    for effect in ["asm", "external"] {
                        if self.graph.forbidden_effect(from, effect)?.is_some() {
                            return Err(Error::unsupported(
                                "opaque execution prevents establishing call absence",
                            ));
                        }
                    }
                }
                Ok(vec![(state, Value::Bool(bit(found)))])
            }
            "proof-no-effects" => {
                arity(head, args, 2)?;
                let from = symbol(&args[0])?;
                let effects = list(&args[1])?;
                if effects.is_empty() {
                    return Err("#proof-no-effects needs an explicit nonempty effect list".into());
                }
                let mut clean = true;
                for effect in effects {
                    let effect = symbol(effect)?
                        .trim_start_matches('#')
                        .strip_prefix("proof-")
                        .ok_or("effect names require #proof- prefixes")?;
                    clean &= self.graph.forbidden_effect(from, effect)?.is_none();
                }
                Ok(vec![(state, Value::Bool(bit(clean)))])
            }
            "proof-only-unsafe" => {
                arity(head, args, 2)?;
                let allowed = list(&args[1])?
                    .iter()
                    .map(|value| symbol(value).map(str::to_owned))
                    .collect::<Result<BTreeSet<_>>>()?;
                for name in &allowed {
                    if let Some(builtin) = name.strip_prefix('#') {
                        if !crate::is_builtin_form(builtin) {
                            return Err(format!("unknown unsafe builtin '{name}'").into());
                        }
                    } else {
                        self.function(name)?;
                    }
                }
                let clean = self
                    .graph
                    .unsafe_outside(symbol(&args[0])?, &allowed)?
                    .is_none();
                Ok(vec![(state, Value::Bool(bit(clean)))])
            }
            "proof-stack-at-most" => {
                arity(head, args, 3)?;
                let function = symbol(&args[0])?;
                self.function(function)?;
                let Expr::String(target) = &args[1] else {
                    return Err("stack proofs require an explicit target string".into());
                };
                let target = crate::TargetDescription::parse(target)?;
                if target != crate::TargetDescription::X86_64_SYSTEM_V {
                    return Err(Error::unsupported(
                        "stack certificates currently require x86_64-sysv",
                    ));
                }
                let bound = literal_usize(&args[2])?;
                let assembly = crate::codegen::generate_checked_assembly(self.checked, target)
                    .map_err(|error| Error::unsupported(error.to_string()))?;
                let bytes = crate::stack_usage::bounded_entry_stack(
                    &assembly,
                    &crate::codegen::asm_symbol(function),
                )?;
                Ok(vec![(state, Value::Bool(bit(bytes <= bound)))])
            }
            "proof-for-all" => {
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
                        return Err(
                            format!("proof binding '{name}' shadows an existing binding").into(),
                        );
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
            "proof-contract" => {
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
                    for (mut state, result) in
                        self.call(state, function, arguments.clone(), false)?
                    {
                        state.result = Some(result);
                        output.extend(self.proposition(state, &args[2])?);
                    }
                }
                self.old = None;
                self.quantified = false;
                self.close_claim(original, output, input_start)
            }
            "proof-calls-when" | "proof-calls-before" | "proof-requires-validation" => {
                if self.quantified {
                    return Err("trace claims quantify their own function inputs; put them outside #proof-for-all".into());
                }
                let original = state.clone();
                let input_start = self.inputs.len();
                if self.trace.is_some() {
                    return Err(Error::unsupported(
                        "nested execution-trace claims are unsupported",
                    ));
                }
                let (function, trace) = if head == "proof-calls-when" {
                    arity(head, args, 4)?;
                    let observed = symbol(&args[1])?.to_owned();
                    if self.resolve_type(&self.function(&observed)?.return_type)? != Type::Bool {
                        return Err("the observed function must return #bool".into());
                    }
                    let expected = match symbol(&args[2])? {
                        "true" => true,
                        "false" => false,
                        _ => return Err("the observed result must be true or false".into()),
                    };
                    (
                        self.function(symbol(&args[0])?)?,
                        Trace::When {
                            observed,
                            expected,
                            action: symbol(&args[3])?.into(),
                        },
                    )
                } else if head == "proof-calls-before" {
                    arity(head, args, 3)?;
                    (
                        self.function(symbol(&args[0])?)?,
                        Trace::Before {
                            required: symbol(&args[1])?.into(),
                            action: symbol(&args[2])?.into(),
                        },
                    )
                } else {
                    self.validation_rule(args)?
                };
                self.function(trace.action())?;
                if let Trace::Before { required, .. } = &trace {
                    self.function(required)?;
                }
                self.trace = Some(trace);
                self.trace_violation = FALSE;
                let mut state = state;
                state.validations.clear();
                let mut arguments = Vec::new();
                for parameter in &function.parameters {
                    let value = self.fresh_value(&mut state, &parameter.ty, 0)?;
                    self.inputs.push((parameter.name.clone(), value.clone()));
                    arguments.push(value);
                }
                self.input_state = Some(state.clone());
                let runs = self.call(state.clone(), function, arguments, false)?;
                // At least one trace must be analysed; nontermination is never
                // silently treated as evidence that an operation cannot run.
                if runs.is_empty() {
                    return Err(Error::unsupported("no complete execution trace"));
                }
                let safe = self.circuit.not(self.trace_violation);
                let result =
                    self.close_claim(original, vec![(state, Value::Bool(safe))], input_start);
                self.trace = None;
                result
            }
            "proof-no-overflow" => {
                arity(head, args, 3)?;
                let name = symbol(&args[0])?;
                if !name.starts_with('#') {
                    return Err("overflow operations require canonical # prefixed keywords".into());
                }
                let (ty, op, mode) = numeric(name)
                    .ok_or("#proof-no-overflow requires an integer add/sub/mul builtin")?;
                if matches!(ty, Type::Char | Type::Bool | Type::F32 | Type::F64)
                    || mode.is_none()
                    || !matches!(op.as_str(), "add" | "sub" | "mul")
                {
                    return Err("#proof-no-overflow requires an explicit integer add/sub/mul -wrap or -saturate builtin".into());
                }
                let mut output = Vec::new();
                for (state, a) in self.expr(state, &args[1], true)? {
                    for (state, b) in self.expr(state, &args[2], true)? {
                        let a = self.word_of(&a, &ty)?;
                        let b = self.word_of(&b, &ty)?;
                        let valid = self.circuit.no_overflow(&op, &a, &b)?;
                        output.push((state, Value::Bool(valid)));
                    }
                }
                Ok(output)
            }
            "proof-loop-limit" => {
                arity(head, args, 2)?;
                let limit = literal_usize(&args[0])?;
                if limit == 0 || limit > 1024 {
                    return Err("proof loop limits must be in 1..=1024".into());
                }
                let previous = self.loop_limit;
                self.loop_limit = limit;
                let output = self.proposition(state, &args[1]);
                self.loop_limit = previous;
                output
            }
            "proof-with-invariants" => {
                arity(head, args, 2)?;
                let previous = self.invariants.clone();
                for descriptor in list(&args[0])? {
                    let parts = list(descriptor)?;
                    if parts.len() != 4 {
                        return Err(
                            "an invariant is (function loop-label predicate unsigned-rank)".into(),
                        );
                    }
                    let function = symbol(&parts[0])?.to_owned();
                    self.function(&function)?;
                    let label = symbol(&parts[1])?.to_owned();
                    let body = self
                        .checked
                        .declarations()
                        .bodies
                        .get(&function)
                        .ok_or_else(|| {
                            Error::unsupported("invariant function has no checked implementation")
                        })?;
                    if loop_label_count(body, &label) != 1 {
                        return Err(format!("invariant label '{label}' must identify exactly one loop in '{function}'").into());
                    }
                    if self
                        .invariants
                        .insert(
                            (function, label),
                            Invariant {
                                predicate: parts[2].clone(),
                                rank: parts[3].clone(),
                            },
                        )
                        .is_some()
                    {
                        return Err("duplicate loop invariant".into());
                    }
                }
                let output = self.proposition(state, &args[1]);
                self.invariants = previous;
                output
            }
            "proof-permutation" | "proof-sorted" => self.array_property(state, head, args),
            _ if head.starts_with("proof-") && !matches!(head, "proof-result" | "proof-old") => {
                Err(format!("unknown or misplaced proof form '#{head}'").into())
            }
            _ => self.expr(state, expr, true),
        }
    }

    fn limit_paths(&self, count: usize) -> Result<()> {
        if count > 4096 {
            Err(Error::limit("symbolic path budget exhausted"))
        } else {
            Ok(())
        }
    }

    fn word_of(&self, value: &Value, ty: &Type) -> Result<Word> {
        match value {
            Value::Bits(word, actual) if self.resolve_type(actual)? == self.resolve_type(ty)? => {
                Ok(word.clone())
            }
            _ => Err(format!("proof operand type mismatch: expected {ty:?}").into()),
        }
    }

    fn resolve_type(&self, ty: &Type) -> Result<Type> {
        crate::typed_ir::resolve_type(ty, &self.aliases).map_err(Into::into)
    }
}

fn bit(value: bool) -> Bit {
    if value {
        TRUE
    } else {
        FALSE
    }
}
fn form(expr: &Expr) -> Option<(&str, &[Expr])> {
    if let Expr::List(items) = expr {
        Some((
            symbol(items.first()?).ok()?.trim_start_matches('#'),
            &items[1..],
        ))
    } else {
        None
    }
}
fn symbol(expr: &Expr) -> Result<&str> {
    match expr {
        Expr::Symbol(name) | Expr::Function(name) => Ok(name),
        _ => Err("proof syntax requires an identifier".into()),
    }
}
fn list(expr: &Expr) -> Result<&[Expr]> {
    match expr {
        Expr::List(items) => Ok(items),
        _ => Err("proof syntax requires a list".into()),
    }
}
fn arity(head: &str, args: &[Expr], expected: usize) -> Result<()> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(format!(
            "#{head} expects {expected} operand(s), received {}",
            args.len()
        )
        .into())
    }
}
fn literal_usize(expr: &Expr) -> Result<usize> {
    match expr {
        Expr::Integer(n) if *n >= 0 => {
            usize::try_from(*n).map_err(|_| "proof bound too large".into())
        }
        Expr::UnsignedInteger(n) => usize::try_from(*n).map_err(|_| "proof bound too large".into()),
        Expr::List(items)
            if items.len() == 3
                && symbol(&items[0])
                    .is_ok_and(|head| head.trim_start_matches('#') == "literal") =>
        {
            literal_usize(&items[2])
        }
        _ => Err("proof bound requires an unsigned integer literal".into()),
    }
}
fn scalar(ty: &Type) -> Option<(usize, bool)> {
    use Type::*;
    Some(match ty {
        I8 => (8, true),
        I16 => (16, true),
        I32 => (32, true),
        I64 | Isize => (64, true),
        I128 => (128, true),
        U8 => (8, false),
        U16 => (16, false),
        U32 | Char => (32, false),
        U64 | Usize | Type::RawPointer { .. } => (64, false),
        U128 => (128, false),
        _ => return None,
    })
}
fn numeric(head: &str) -> Option<(Type, String, Option<String>)> {
    let public = if head.starts_with('#') {
        head.to_owned()
    } else if head.contains("::") {
        format!("#{head}")
    } else {
        crate::names::numeric_source(head)?
    };
    crate::names::numeric_operation(&public)?;
    let (ty, operation) = public.strip_prefix('#')?.split_once("::")?;
    let (operation, mode) = operation
        .strip_suffix("-wrap")
        .map(|op| (op, Some("wrap".to_owned())))
        .or_else(|| {
            operation
                .strip_suffix("-saturate")
                .map(|op| (op, Some("saturate".to_owned())))
        })
        .unwrap_or((operation, None));
    Some((
        Type::from_name(&format!("#{ty}")),
        operation.to_owned(),
        mode,
    ))
}

fn loop_label_count(body: &crate::typed_body::Body, label: &str) -> usize {
    use crate::typed_body::{Control, NodeKind};
    let mut count = 0;
    let mut pending = vec![body.instructions.as_slice()];
    for node in &body.nodes {
        match &node.kind {
            NodeKind::Block(statements) | NodeKind::Loop(statements) => pending.push(statements),
            NodeKind::Labeled(name, inner)
                if name == label && matches!(body.nodes[inner.0].kind, NodeKind::Loop(_)) =>
            {
                count += 1
            }
            _ => {}
        }
    }
    while let Some(statements) = pending.pop() {
        let mut single: Vec<_> = statements.iter().collect();
        while let Some(statement) = single.pop() {
            match &statement.control {
                Control::Labeled(name, inner) => {
                    if name == label
                        && matches!(
                            inner.control,
                            Control::While(..) | Control::Loop(..) | Control::For(..)
                        )
                    {
                        count += 1;
                    }
                    single.push(inner);
                }
                Control::While(_, body) | Control::Loop(body) => pending.push(body),
                Control::For(init, _, step, body) => {
                    single.push(init);
                    single.push(step);
                    pending.push(body);
                }
                Control::Destructure {
                    otherwise: Some(body),
                    ..
                } => pending.push(body),
                _ => {}
            }
        }
    }
    count
}

fn proof_type(expr: &Expr, written: bool) -> Result<Type> {
    fn explicit(expr: &Expr) -> Result<()> {
        match expr {
            Expr::Symbol(name) if crate::is_primitive_type_name(name) => {
                Err("proof primitive types require canonical # prefixed keywords".into())
            }
            Expr::List(items) if !items.is_empty() => {
                if !symbol(&items[0])?.starts_with('#') {
                    return Err(
                        "proof type constructors require canonical # prefixed keywords".into(),
                    );
                }
                for part in &items[1..] {
                    explicit(part)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    if written {
        explicit(expr)?;
    }
    crate::parse_type(Some(&crate::normalize_keywords(expr.clone()))).map_err(Into::into)
}

pub(crate) fn declaration_span(program: &crate::Program, name: &str) -> Option<Span> {
    program
        .declaration_expressions
        .get(name)
        .map(|node| {
            if node.children.len() == 3 {
                node.children[2].span
            } else {
                node.span
            }
        })
        .or_else(|| program.declaration_spans.get(name).copied())
}
