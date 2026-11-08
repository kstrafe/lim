//! Guarded refinements of checked return and store May-origins, captured during
//! provider verification. Conditions contain input data and fresh abstract choices,
//! never physical provider heap IDs or assumptions supplied by the caller.
use super::*;
use crate::typed_place::Segment as Path;
use contract_return::ReferenceModel;
use std::sync::Arc;

const BYTE_LIMIT: usize = 64 * 1024 * 1024;
const KEY_LIMIT: usize = 256;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct StoreScope {
    pub parameter: usize,
    pub storage: Vec<Path>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum Key {
    Origin(Vec<Path>, usize, Vec<usize>),
    Variant(Vec<Path>, usize),
    StoreOrigin(StoreScope, Vec<Path>, usize, Vec<usize>),
    StoreVariant(StoreScope, Vec<Path>, usize),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_engine(test: impl FnOnce(&mut Engine<'_, '_>)) {
        let program = crate::parse_program(r#"
          (#struct Frame () (: flag #bool : retained (#pin-ref #u8)))
          (#fn choose (: frame (#pin-ref-mut Frame) : condition #bool : left (#ref #u8) : right (#ref #u8)) (#ref #u8)
            (#pin-set-field frame flag false)
            (#return (#if condition left right)))
        "#).unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        test(&mut Engine::new(&checked, &graph, Span::new(0, 0, 1, 1)));
    }

    #[test]
    fn mutating_pinned_parents_do_not_publish_fresh_root_identity_guards() {
        with_engine(|engine| {
            engine.verify_reference_origins = true;
            let function = engine.function("choose").unwrap();
            assert!(engine
                .graph
                .forbidden_effect("choose", "mutation")
                .unwrap()
                .is_some());
            let mut state = State::new();
            let arguments = function
                .parameters
                .iter()
                .map(|parameter| engine.fresh_value(&mut state, &parameter.ty, 0))
                .collect::<Result<Vec<_>>>()
                .unwrap();
            engine
                .begin_return_guards(function, &mut state, &arguments)
                .unwrap();
            assert!(engine.return_guard_capture.is_none());
        });
    }

    #[test]
    fn typed_parent_overlap_disables_refinement_but_plain_handles_do_not() {
        let program = crate::parse_program(
            r#"
          (#struct Slot () (: reference (#ref #u8)))
          (#struct Holder () (: value #u8 : reference (#ref #u8)))
          (#fn slot-update (: slot (#ref-mut Slot) : next (#ref #u8)) ()
            (#deref-set slot (#struct-literal Slot (: reference next)))
            (#return ()))
          (#fn holder-update (: holder (#ref-mut Holder) : next (#ref #u8)) ()
            (#deref-set holder (#struct-literal Holder (: value 0u8 : reference next)))
            (#return ()))
        "#,
        )
        .unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        for (name, guarded) in [("slot-update", true), ("holder-update", false)] {
            let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
            engine.verify_reference_origins = true;
            let function = engine.function(name).unwrap();
            let mut state = State::new();
            let arguments = function
                .parameters
                .iter()
                .map(|parameter| engine.fresh_value(&mut state, &parameter.ty, 0))
                .collect::<Result<Vec<_>>>()
                .unwrap();
            engine
                .begin_return_guards(function, &mut state, &arguments)
                .unwrap();
            assert_eq!(engine.return_guard_capture.is_some(), guarded, "{name}");
            assert_eq!(state.has_input_parent_aliases(), !guarded, "{name}");
        }
    }

    #[test]
    fn condition_and_binding_budgets_fail_before_retaining_more_data() {
        with_engine(|engine| {
            engine.return_guard_capture = Some(Capture {
                function: "choose".into(),
                guards: Guards::new(),
            });
            for index in 0..KEY_LIMIT {
                engine
                    .add_return_guard(Key::Origin(vec![Path::Tuple(index)], 0, Vec::new()), TRUE)
                    .unwrap();
            }
            let error = engine
                .add_return_guard(
                    Key::Origin(vec![Path::Tuple(KEY_LIMIT)], 0, Vec::new()),
                    TRUE,
                )
                .unwrap_err();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(crate::ProofOutcome::ResourceLimit)
            );
            assert_eq!(
                engine.return_guard_capture.as_ref().unwrap().guards.len(),
                KEY_LIMIT
            );
            let bit = engine.circuit.fresh();
            let mut found = Bindings {
                found: BTreeMap::new(),
                bytes: BYTE_LIMIT,
            };
            let error = engine
                .guard_bindings(
                    &State::new(),
                    &Value::Bool(bit),
                    0,
                    &[],
                    &BTreeSet::from([((bit >> 1) as usize)]),
                    &mut found,
                    0,
                )
                .unwrap_err();
            assert_eq!(
                error.diagnostic_code().proof_outcome(),
                Some(crate::ProofOutcome::ResourceLimit)
            );
            assert!(found.found.is_empty());
        });
    }
}
pub(super) type Guards = BTreeMap<Key, Bit>;

pub(super) struct Capture {
    function: String,
    guards: Guards,
}

#[derive(Default)]
struct Bindings {
    found: BTreeMap<usize, Binding>,
    bytes: usize,
}

#[derive(Clone, Debug)]
enum Step {
    Dereference,
    Field(usize),
    Element(usize),
    Payload(usize),
}

#[derive(Clone, Debug)]
enum Leaf {
    Bool,
    Word(Type, usize, bool),
    Tag,
}

#[derive(Clone, Debug)]
struct Binding {
    parameter: usize,
    path: Vec<Step>,
    leaf: Leaf,
    bit: usize,
}

pub(super) struct Summary {
    function: String,
    keys: Vec<Key>,
    template: logic::Template,
    bindings: Vec<Option<Binding>>,
    bytes: usize,
}

impl Summary {
    pub(super) fn retained_bytes(&self) -> usize {
        self.bytes
    }
}

impl Engine<'_, '_> {
    pub(super) fn begin_return_guards(
        &mut self,
        function: &Function,
        state: &mut State,
        arguments: &[Value],
    ) -> Result<()> {
        if self.verify_reference_origins {
            let mutates = self
                .graph
                .forbidden_effect(&function.name, "mutation")?
                .is_some();
            let mut needed = self.reference_type(&function.return_type, 0)?;
            if mutates {
                for parameter in &function.parameters {
                    needed |= self.stores_references(&parameter.ty, 0)?;
                    if self.guarded_alias_risk(&parameter.ty, 0)? {
                        return Ok(());
                    }
                }
                self.register_contract_input_storage(state, arguments)?;
                if state.has_input_parent_aliases() {
                    // In-place typed overlap can conceal internal aliases.
                    // Independent fresh roots cannot refine these May-origins.
                    return Ok(());
                }
            }
            if !needed {
                return Ok(());
            }
            self.return_guard_capture = Some(Capture {
                function: function.name.clone(),
                guards: Guards::new(),
            });
        }
        Ok(())
    }

    fn guarded_alias_risk(&mut self, ty: &Type, depth: usize) -> Result<bool> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("guarded reference alias nesting exceeds 32"));
        }
        Ok(match self.resolve_type(ty)? {
            Type::PinnedReference { mutable: true, .. } => true,
            Type::Reference { target, .. } | Type::PinnedReference { target, .. } => {
                self.guarded_alias_risk(&target, depth + 1)?
            }
            Type::Array(element, _) => self.guarded_alias_risk(&element, depth + 1)?,
            Type::Tuple(types) => {
                let mut risk = false;
                for ty in types {
                    risk |= self.guarded_alias_risk(&ty, depth + 1)?;
                }
                risk
            }
            Type::Named(name) if self.records.contains_key(&name) => {
                let mut risk = false;
                for field in self.records[&name].clone() {
                    risk |= self.guarded_alias_risk(&field.ty, depth + 1)?;
                }
                risk
            }
            Type::Named(name) if self.enums.contains_key(&name) => {
                let mut risk = false;
                for variant in self.enums[&name].clone() {
                    for ty in variant.fields {
                        risk |= self.guarded_alias_risk(&ty, depth + 1)?;
                    }
                }
                risk
            }
            _ => false,
        })
    }

    fn add_return_guard(&mut self, key: Key, guard: Bit) -> Result<()> {
        if guard == FALSE {
            return Ok(());
        }
        let Some(capture) = self.return_guard_capture.as_mut() else {
            return Ok(());
        };
        if capture.guards.len() >= KEY_LIMIT && !capture.guards.contains_key(&key) {
            return Err(Error::limit(
                "guarded reference summaries exceed 256 conditions",
            ));
        }
        let old = capture.guards.get(&key).copied().unwrap_or(FALSE);
        capture.guards.insert(key, self.circuit.or(old, guard));
        Ok(())
    }

    pub(super) fn capture_return_guards(
        &mut self,
        state: &State,
        function: &Function,
        arguments: &[Value],
        value: &Value,
    ) -> Result<()> {
        if !self
            .return_guard_capture
            .as_ref()
            .is_some_and(|capture| capture.function == function.name)
        {
            return Ok(());
        }
        let id = self
            .checked
            .declarations()
            .function_id(&function.name)
            .ok_or_else(|| Error::checker("missing guarded reference function identity"))?;
        let origins = self.checked.declarations().bodies[&function.name]
            .call_return_origins
            .get(&id)
            .cloned()
            .unwrap_or_default();
        let entry = self
            .old
            .clone()
            .ok_or_else(|| Error::checker("guarded references need their entry snapshot"))?;
        self.capture_return_value(state, &entry, arguments, value, &[], &origins, None, 0)
    }

    pub(super) fn capture_return_value(
        &mut self,
        state: &State,
        entry: &State,
        arguments: &[Value],
        value: &Value,
        path: &[Path],
        origins: &[crate::typed_body::ParameterLoanSummary],
        scope: Option<&StoreScope>,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("guarded reference nesting exceeds 32"));
        }
        if self.circuit.satisfy(state.guard)?.is_none() {
            return Ok(());
        }
        if !self.reference_type(&value.ty(), 0)? {
            return Ok(());
        }
        match value {
            Value::Ref {
                place,
                target,
                mutable,
                pinned,
            } => {
                for (index, source) in origins.iter().enumerate().filter(|(_, source)| {
                    !source.lifetime_only && contract_return::path_matches(&source.storage, path)
                }) {
                    let model = ReferenceModel {
                        arguments,
                        source: Some(entry),
                        origins: vec![source.clone()],
                        bounds: Default::default(),
                        guards: None,
                    };
                    for candidate in self.reference_candidates(
                        state.clone(),
                        path,
                        target,
                        *mutable,
                        *pinned,
                        &model,
                    )? {
                        let Value::Ref { place: origin, .. } = candidate.reference else {
                            return Err(Error::checker(
                                "guarded reference candidate is not a reference",
                            ));
                        };
                        let same = self.same_location(place, &origin);
                        let selected = self.circuit.and(candidate.state.guard, same);
                        let key = match scope {
                            Some(scope) => Key::StoreOrigin(
                                scope.clone(),
                                path.to_vec(),
                                index,
                                candidate.selection,
                            ),
                            None => Key::Origin(path.to_vec(), index, candidate.selection),
                        };
                        self.add_return_guard(key, selected)?;
                    }
                }
            }
            Value::Record(name, fields) => {
                for (field, value) in fields {
                    let id = self
                        .checked
                        .declarations()
                        .field_id(&Type::Named(name.clone()), field)
                        .ok_or_else(|| Error::checker("missing guarded reference field"))?;
                    let mut nested = path.to_vec();
                    nested.push(Path::Field(id));
                    self.capture_return_value(
                        state,
                        entry,
                        arguments,
                        value,
                        &nested,
                        origins,
                        scope,
                        depth + 1,
                    )?;
                }
            }
            Value::Tuple(values) | Value::Array(_, values) => {
                let array = matches!(value, Value::Array(_, _));
                for (index, value) in values.iter().enumerate() {
                    let mut nested = path.to_vec();
                    nested.push(if array {
                        Path::Index(index as u128)
                    } else {
                        Path::Tuple(index)
                    });
                    self.capture_return_value(
                        state,
                        entry,
                        arguments,
                        value,
                        &nested,
                        origins,
                        scope,
                        depth + 1,
                    )?;
                }
            }
            Value::Enum(name, tag, values) => {
                for (index, payload) in values.iter().enumerate() {
                    self.tick()?;
                    let selected = self
                        .circuit
                        .eq_word(tag, &Circuit::constant(index as u128, 64, false));
                    let mut branch = state.clone();
                    branch.guard = self.circuit.and(branch.guard, selected);
                    let key = match scope {
                        Some(scope) => Key::StoreVariant(scope.clone(), path.to_vec(), index),
                        None => Key::Variant(path.to_vec(), index),
                    };
                    self.add_return_guard(key, branch.guard)?;
                    if let Some(payload) = payload {
                        let id = self
                            .checked
                            .declarations()
                            .variant_id(&Type::Named(name.clone()), &self.enums[name][index].name)
                            .ok_or_else(|| Error::checker("missing guarded reference variant"))?;
                        let mut nested = path.to_vec();
                        nested.push(Path::Payload(id, 0));
                        self.capture_return_value(
                            &branch,
                            entry,
                            arguments,
                            payload,
                            &nested,
                            origins,
                            scope,
                            depth + 1,
                        )?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn finish_return_guards(
        &mut self,
        function: &Function,
        entry: &State,
        arguments: &[Value],
    ) -> Result<()> {
        let Some(capture) = self.return_guard_capture.take() else {
            return Ok(());
        };
        if capture.function != function.name {
            return Err(Error::checker("guarded reference capture changed function"));
        }
        let keys = capture.guards.keys().cloned().collect::<Vec<_>>();
        let roots = capture.guards.values().copied().collect::<Vec<_>>();
        let template = self.circuit.template(&roots)?;
        let needed = template.inputs().iter().copied().collect::<BTreeSet<_>>();
        let mut found = Bindings::default();
        if !needed.is_empty() {
            for (parameter, argument) in arguments.iter().enumerate() {
                self.guard_bindings(entry, argument, parameter, &[], &needed, &mut found, 0)?;
            }
        }
        let bindings = template
            .inputs()
            .iter()
            .map(|id| found.found.remove(id))
            .collect::<Vec<_>>();
        let mut bytes = template
            .retained_bytes()
            .saturating_add(capture.function.len());
        for key in &keys {
            let path = match key {
                Key::Origin(path, _, selection) => {
                    bytes =
                        bytes.saturating_add(selection.capacity() * std::mem::size_of::<usize>());
                    path
                }
                Key::Variant(path, _) => path,
                Key::StoreOrigin(scope, path, _, selection) => {
                    bytes =
                        bytes.saturating_add(selection.capacity() * std::mem::size_of::<usize>());
                    bytes = bytes
                        .saturating_add(scope.storage.capacity() * std::mem::size_of::<Path>());
                    path
                }
                Key::StoreVariant(scope, path, _) => {
                    bytes = bytes
                        .saturating_add(scope.storage.capacity() * std::mem::size_of::<Path>());
                    path
                }
            };
            bytes = bytes.saturating_add(
                std::mem::size_of::<Key>() + path.capacity() * std::mem::size_of::<Path>(),
            );
        }
        for binding in &bindings {
            bytes = bytes.saturating_add(std::mem::size_of::<Option<Binding>>());
            if let Some(binding) = binding {
                bytes = bytes.saturating_add(binding.path.capacity() * std::mem::size_of::<Step>());
            }
        }
        if bytes > BYTE_LIMIT {
            return Err(Error::limit("guarded reference summary exceeds 64 MiB"));
        }
        let summary = Summary {
            function: capture.function,
            keys,
            template,
            bindings,
            bytes,
        };
        // Replay with the provider's original inputs and abstract choices.
        // This independently checks binding paths and circuit substitution.
        let actual = self.replay_return_guards(&summary, entry, arguments, true)?;
        for (key, expected) in capture.guards {
            let replayed = actual
                .get(&key)
                .copied()
                .ok_or_else(|| Error::checker("guarded reference replay omitted a condition"))?;
            let different = self.circuit.xor(expected, replayed);
            if self.circuit.satisfy(different)?.is_some() {
                return Err(Error::checker(
                    "guarded reference replay changed a provider condition",
                ));
            }
        }
        self.guarded_return_summary = Some(Arc::new(summary));
        Ok(())
    }

    fn guard_bindings(
        &mut self,
        state: &State,
        value: &Value,
        parameter: usize,
        path: &[Step],
        needed: &BTreeSet<usize>,
        found: &mut Bindings,
        depth: usize,
    ) -> Result<()> {
        self.tick()?;
        if depth > 32 {
            return Err(Error::limit("guarded reference input nesting exceeds 32"));
        }
        let leaf = match value {
            Value::Bool(bit) => Some((Leaf::Bool, vec![*bit])),
            Value::Bits(word, ty) => Some((
                Leaf::Word(self.resolve_type(ty)?, word.bits.len(), word.signed),
                word.bits.clone(),
            )),
            Value::Enum(_, tag, _) => Some((Leaf::Tag, tag.bits.clone())),
            _ => None,
        };
        if let Some((leaf, bits)) = leaf {
            for (bit, value) in bits.into_iter().enumerate() {
                let id = (value >> 1) as usize;
                if value & 1 == 0 && needed.contains(&id) && !found.found.contains_key(&id) {
                    found.bytes = found.bytes.saturating_add(
                        std::mem::size_of::<Binding>()
                            + 64
                            + path.len().saturating_mul(std::mem::size_of::<Step>()),
                    );
                    if found.bytes > BYTE_LIMIT {
                        return Err(Error::limit(
                            "guarded reference input bindings exceed 64 MiB",
                        ));
                    }
                    let binding = Binding {
                        parameter,
                        path: path.to_vec(),
                        leaf: leaf.clone(),
                        bit,
                    };
                    found.found.insert(id, binding);
                }
            }
        }
        match value {
            Value::Ref { place, .. } => {
                let value = self.read(state, place)?;
                let mut nested = path.to_vec();
                nested.push(Step::Dereference);
                self.guard_bindings(state, &value, parameter, &nested, needed, found, depth + 1)?;
            }
            Value::Record(_, fields) => {
                for (index, (_, value)) in fields.iter().enumerate() {
                    let mut nested = path.to_vec();
                    nested.push(Step::Field(index));
                    self.guard_bindings(
                        state,
                        value,
                        parameter,
                        &nested,
                        needed,
                        found,
                        depth + 1,
                    )?;
                }
            }
            Value::Tuple(values) | Value::Array(_, values) => {
                for (index, value) in values.iter().enumerate() {
                    let mut nested = path.to_vec();
                    nested.push(Step::Element(index));
                    self.guard_bindings(
                        state,
                        value,
                        parameter,
                        &nested,
                        needed,
                        found,
                        depth + 1,
                    )?;
                }
            }
            Value::Enum(_, _, values) => {
                for (index, value) in values.iter().enumerate() {
                    if let Some(value) = value {
                        let mut nested = path.to_vec();
                        nested.push(Step::Payload(index));
                        self.guard_bindings(
                            state,
                            value,
                            parameter,
                            &nested,
                            needed,
                            found,
                            depth + 1,
                        )?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn guard_binding_bit(
        &mut self,
        binding: &Binding,
        state: &State,
        arguments: &[Value],
    ) -> Result<Option<Bit>> {
        self.tick()?;
        let mut value = arguments
            .get(binding.parameter)
            .cloned()
            .ok_or_else(|| Error::checker("guarded reference parameter is missing"))?;
        for step in &binding.path {
            self.tick()?;
            value = match (step, value) {
                (Step::Dereference, Value::Ref { place, .. }) => self.read(state, &place)?,
                (Step::Field(index), Value::Record(_, fields)) => fields
                    .get(*index)
                    .ok_or_else(|| Error::checker("guarded reference input field is missing"))?
                    .1
                    .clone(),
                (Step::Element(index), Value::Tuple(values) | Value::Array(_, values)) => values
                    .get(*index)
                    .cloned()
                    .ok_or_else(|| Error::checker("guarded reference input element is missing"))?,
                (Step::Payload(index), Value::Enum(_, _, values)) => match values.get(*index) {
                    Some(Some(value)) => value.clone(),
                    Some(None) => return Ok(None),
                    None => {
                        return Err(Error::checker("guarded reference input variant is missing"))
                    }
                },
                _ => {
                    return Err(Error::checker(
                        "guarded reference input projection has incompatible storage",
                    ))
                }
            };
        }
        let bits = match (&binding.leaf, &value) {
            (Leaf::Bool, _) if value.ty() == Type::Bool => vec![value.boolean()?],
            (Leaf::Word(ty, width, signed), Value::Bits(word, actual))
                if self.resolve_type(actual)? == *ty
                    && word.bits.len() == *width
                    && word.signed == *signed =>
            {
                word.bits.clone()
            }
            (Leaf::Tag, Value::Enum(_, tag, _)) if tag.bits.len() == 64 && !tag.signed => {
                tag.bits.clone()
            }
            _ => {
                return Err(Error::checker(
                    "guarded reference input scalar has incompatible type",
                ))
            }
        };
        Ok(Some(*bits.get(binding.bit).ok_or_else(|| {
            Error::checker("guarded reference input bit is missing")
        })?))
    }

    fn replay_return_guards(
        &mut self,
        summary: &Summary,
        state: &State,
        arguments: &[Value],
        original: bool,
    ) -> Result<Guards> {
        for _ in 0..summary.template.node_count() {
            self.tick()?;
        }
        let mut inputs = Vec::with_capacity(summary.bindings.len());
        for (id, binding) in summary.template.inputs().iter().zip(&summary.bindings) {
            let bit = match binding {
                Some(binding) => self.guard_binding_bit(binding, state, arguments)?,
                None => None,
            };
            inputs.push(bit.unwrap_or_else(|| {
                if original {
                    (*id as Bit) << 1
                } else {
                    self.circuit.fresh()
                }
            }));
        }
        let roots = self
            .circuit
            .instantiate_template(&summary.template, &inputs)?;
        if roots.len() != summary.keys.len() {
            return Err(Error::checker(
                "guarded reference roots have incompatible shape",
            ));
        }
        Ok(summary.keys.iter().cloned().zip(roots).collect())
    }

    pub(super) fn instantiate_return_guards(
        &mut self,
        summary: Option<&Summary>,
        function: &Function,
        state: &State,
        arguments: &[Value],
    ) -> Result<Option<Guards>> {
        let Some(summary) = summary else {
            return Ok(None);
        };
        if summary.function != function.name {
            return Err(Error::checker(
                "guarded reference summary belongs to another function",
            ));
        }
        self.replay_return_guards(summary, state, arguments, false)
            .map(Some)
    }
}
