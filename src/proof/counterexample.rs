//! Bounded witnesses belong to logical values, not a mutable global last error.
//! Input references are read from the state frozen before program execution.
use super::symbolic::{Location, Segment};
use super::*;
use std::sync::Arc;

const INPUT_LIMIT: usize = 12;
const ITEM_LIMIT: usize = 8;
const DEPTH_LIMIT: usize = 12;
const NODE_LIMIT: usize = 256;
const BYTE_LIMIT: usize = 8192;
const WITNESS_LIMIT: usize = 8;

#[derive(Clone, Debug)]
pub(super) struct Witness {
    pub guard: Bit,
    pub text: Arc<str>,
}

#[derive(Clone, Debug)]
pub(super) struct Evidence {
    pub value: Bit,
    pub witnesses: Vec<Witness>,
    pub omitted: bool,
}

impl Engine<'_, '_> {
    pub(super) fn combine_claims(&mut self, head: &str, a: &Value, b: &Value) -> Result<Value> {
        let left = a.boolean()?;
        let right = b.boolean()?;
        let value = if head == "proof-and" {
            self.circuit.and(left, right)
        } else {
            self.circuit.or(left, right)
        };
        let mut witnesses = Vec::new();
        let mut omitted = false;
        for operand in [a, b] {
            let Value::Claim(evidence) = operand else {
                continue;
            };
            let failed = self.circuit.not(evidence.value);
            for witness in &evidence.witnesses {
                let guard = self.circuit.and(witness.guard, failed);
                if guard == FALSE {
                    continue;
                }
                if witnesses.len() == WITNESS_LIMIT {
                    omitted = true;
                    continue;
                }
                witnesses.push(Witness {
                    guard,
                    text: witness.text.clone(),
                });
            }
            omitted |= evidence.omitted && failed != FALSE;
        }
        if value == TRUE || witnesses.is_empty() && !omitted {
            Ok(Value::Bool(value))
        } else {
            Ok(Value::Claim(Box::new(Evidence {
                value,
                witnesses,
                omitted,
            })))
        }
    }

    pub(super) fn claim_evidence(&self, value: &Value, model: &[bool]) -> Option<String> {
        let Value::Claim(evidence) = value else {
            return None;
        };
        let mut output = Output::default();
        let active = evidence
            .witnesses
            .iter()
            .filter(|witness| Circuit::bit_in_model(witness.guard, model))
            .collect::<Vec<_>>();
        let mut count = 0;
        for witness in &active {
            if count != 0 {
                output.push("; ");
            }
            if active.len() > 1 {
                output.push(&format!("witness {}: ", count + 1));
            }
            output.push(&witness.text);
            count += 1;
        }
        if count == 0 {
            return None;
        }
        if evidence.omitted {
            output.push("; ... (additional counterexamples omitted)");
        }
        Some(output.text)
    }

    pub(super) fn render_inputs(&self, start: usize, model: &[bool]) -> String {
        let mut rendering = Rendering {
            engine: self,
            model,
            state: self.input_state.as_ref(),
            identities: BTreeMap::new(),
            nodes: 0,
            output: Output::default(),
        };
        let inputs = &self.inputs[start..];
        for (index, (name, value)) in inputs.iter().take(INPUT_LIMIT).enumerate() {
            if index != 0 {
                rendering.output.push(", ");
            }
            rendering.output.push(name);
            rendering.output.push(" = ");
            rendering.value(value, 0);
        }
        if inputs.len() > INPUT_LIMIT {
            rendering.output.push(", ... (additional inputs omitted)");
        }
        rendering.output.text
    }
}

#[derive(Default)]
struct Output {
    text: String,
    full: bool,
}
impl Output {
    fn push(&mut self, text: &str) {
        if self.full {
            return;
        }
        if self.text.len() + text.len() <= BYTE_LIMIT - 3 {
            self.text.push_str(text);
        } else {
            let mut end = (BYTE_LIMIT - 3)
                .saturating_sub(self.text.len())
                .min(text.len());
            while !text.is_char_boundary(end) {
                end -= 1;
            }
            self.text.push_str(&text[..end]);
            self.text.push_str("...");
            self.full = true;
        }
    }
}

type Identity = (usize, Vec<(u8, usize)>);
struct Rendering<'a, 'p, 's> {
    engine: &'s Engine<'a, 'p>,
    model: &'s [bool],
    state: Option<&'s State>,
    identities: BTreeMap<Identity, usize>,
    nodes: usize,
    output: Output,
}

impl Rendering<'_, '_, '_> {
    fn word(&self, word: &Word) -> u128 {
        Circuit::value_in_model(word, self.model)
    }

    fn location(&self, place: &Location) -> Option<Identity> {
        let mut path = Vec::new();
        for segment in &place.path {
            path.push(match segment {
                Segment::Field(index) => (0, *index),
                Segment::Index(index) => (1, usize::try_from(self.word(index)).ok()?),
                Segment::Payload(index) => (2, *index),
            });
        }
        Some((place.root, path))
    }

    // Reading a witness must not create gates or mutate the checked state.
    fn read<'s>(&self, state: &'s State, place: &Location) -> Option<&'s Value> {
        let mut value = state.root_value(place.root)?;
        for segment in &place.path {
            value = match (segment, value) {
                (Segment::Field(index), Value::Record(_, fields)) => &fields.get(*index)?.1,
                (Segment::Field(index), Value::Tuple(values)) => values.get(*index)?,
                (Segment::Index(index), Value::Array(_, values)) => {
                    values.get(usize::try_from(self.word(index)).ok()?)?
                }
                (Segment::Payload(index), Value::Enum(_, tag, values))
                    if self.word(tag) == *index as u128 =>
                {
                    values.get(*index)?.as_ref()?
                }
                _ => return None,
            };
        }
        Some(value)
    }

    fn identity(&mut self, place: &Location) -> Option<(usize, bool)> {
        let key = self.location(place)?;
        if let Some(id) = self.identities.get(&key) {
            return Some((*id, true));
        }
        let id = self.identities.len();
        self.identities.insert(key, id);
        Some((id, false))
    }

    fn sequence(&mut self, values: &[Value], depth: usize) {
        for (index, value) in values.iter().take(ITEM_LIMIT).enumerate() {
            if index != 0 {
                self.output.push(", ");
            }
            self.value(value, depth + 1);
        }
        if values.len() > ITEM_LIMIT {
            self.output.push(&format!(
                ", ... ({} more elements)",
                values.len() - ITEM_LIMIT
            ));
        }
    }

    fn value(&mut self, value: &Value, depth: usize) {
        if self.output.full {
            return;
        }
        if depth >= DEPTH_LIMIT || self.nodes >= NODE_LIMIT {
            self.output.push("...");
            return;
        }
        self.nodes += 1;
        match value {
            Value::Unit => self.output.push("()"),
            Value::Bool(bit) => self
                .output
                .push(if Circuit::bit_in_model(*bit, self.model) {
                    "true"
                } else {
                    "false"
                }),
            Value::Claim(evidence) => {
                self.output
                    .push(if Circuit::bit_in_model(evidence.value, self.model) {
                        "true"
                    } else {
                        "false"
                    })
            }
            Value::Bits(word, ty) => {
                let number = self.word(word);
                if *ty == Type::Char {
                    if let Some(ch) = char::from_u32(number as u32) {
                        self.output.push(
                            &crate::expression_source(&Expr::Char(ch))
                                .unwrap_or_else(|_| "<character>".into()),
                        );
                    } else {
                        self.output.push("<invalid character>");
                    }
                } else if matches!(ty, Type::RawPointer { .. }) {
                    self.output.push(&format!("ptr(0x{number:x})"));
                } else {
                    let width = word.bits.len();
                    if word.signed {
                        let signed = if width < 128 && number & (1u128 << (width - 1)) != 0 {
                            (number | (!0u128 << width)) as i128
                        } else {
                            number as i128
                        };
                        self.output.push(&signed.to_string());
                    } else {
                        self.output.push(&number.to_string());
                    }
                    let spelling = crate::type_source(ty);
                    self.output
                        .push(spelling.strip_prefix('#').unwrap_or(&spelling));
                }
            }
            Value::Array(_, values) => {
                self.output.push("[");
                self.sequence(values, depth);
                self.output.push("]");
            }
            Value::Tuple(values) => {
                self.output.push("(");
                self.sequence(values, depth);
                self.output.push(")");
            }
            Value::Record(name, fields) => {
                self.output.push(crate::file_access::local_name(name));
                self.output.push(" { ");
                if self
                    .engine
                    .representation_at(name, true, self.engine.span)
                    .is_err()
                {
                    self.output.push("<private representation>");
                } else {
                    for (index, (field, value)) in fields.iter().take(ITEM_LIMIT).enumerate() {
                        if index != 0 {
                            self.output.push(", ");
                        }
                        self.output.push(field);
                        self.output.push(" = ");
                        self.value(value, depth + 1);
                    }
                    if fields.len() > ITEM_LIMIT {
                        self.output.push(", ... (additional fields omitted)");
                    }
                }
                self.output.push(" }");
            }
            Value::Enum(name, tag, values) => {
                let index = usize::try_from(self.word(tag)).ok();
                let variant = self
                    .engine
                    .enums
                    .get(name)
                    .and_then(|variants| variants.get(index?));
                if let Some(variant) = variant {
                    self.output
                        .push(crate::file_access::local_name(&variant.name));
                    if let Some(payload) = index
                        .and_then(|index| values.get(index))
                        .and_then(Option::as_ref)
                    {
                        self.output.push("(");
                        self.value(payload, depth + 1);
                        self.output.push(")");
                    }
                } else {
                    self.output.push("<invalid enum tag>");
                }
            }
            Value::Ref {
                place,
                mutable,
                pinned,
                ..
            } => {
                let Some((id, seen)) = self.identity(place) else {
                    self.output.push("<invalid reference>");
                    return;
                };
                let kind = match (*pinned, *mutable) {
                    (false, false) => "ref",
                    (false, true) => "mut-ref",
                    (true, false) => "pin-ref",
                    (true, true) => "pin-mut-ref",
                };
                self.output.push(&format!("{kind}#{id}"));
                if !seen {
                    self.output.push("(");
                    if let Some(value) = self.state.and_then(|state| self.read(state, place)) {
                        self.value(value, depth + 1);
                    } else {
                        self.output.push("<unavailable referent>");
                    }
                    self.output.push(")");
                }
            }
            Value::Slice(view) => {
                let Some((id, _)) = self.identity(&view.place) else {
                    self.output.push("<invalid slice>");
                    return;
                };
                let start = self.word(&view.start);
                let len = self.word(&view.len);
                self.output.push(&format!(
                    "{}slice#{id}(start={start}, len={len}, values=[",
                    if view.mutable { "mut-" } else { "" }
                ));
                let array = self.state.and_then(|state| self.read(state, &view.place));
                if let (Some(Value::Array(_, values)), Ok(start), Ok(len)) =
                    (array, usize::try_from(start), usize::try_from(len))
                {
                    if let Some(values) = start
                        .checked_add(len)
                        .and_then(|end| values.get(start..end))
                    {
                        self.sequence(values, depth);
                    } else {
                        self.output.push("<invalid range>");
                    }
                } else {
                    self.output.push("<unavailable backing>");
                }
                self.output.push("])");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aliases_use_the_same_identity_after_symbolic_projection_resolution() {
        let program = crate::parse_program("").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        engine
            .bind(
                &mut state,
                "values".into(),
                Type::Array(Box::new(Type::U8), 2),
                Value::Array(
                    Type::U8,
                    vec![
                        Value::Bits(Circuit::constant(7, 8, false), Type::U8),
                        Value::Bits(Circuit::constant(9, 8, false), Type::U8),
                    ],
                ),
            )
            .unwrap();
        let array = state.frames.last().unwrap().locals["values"].0.clone();
        let index = engine.circuit.word(64, false);
        let guard = engine
            .circuit
            .eq_word(&index, &Circuit::constant(1, 64, false));
        for (name, index) in [("first", index), ("alias", Circuit::constant(1, 64, false))] {
            let mut place = array.clone();
            place.path.push(Segment::Index(index));
            engine.inputs.push((
                name.into(),
                Value::Ref {
                    place,
                    target: Type::U8,
                    mutable: false,
                    pinned: false,
                },
            ));
        }
        engine.input_state = Some(state);
        let model = engine.circuit.satisfy(guard).unwrap().unwrap();
        assert_eq!(
            engine.render_inputs(0, &model),
            "first = ref#0(9u8), alias = ref#0"
        );
        assert_eq!(
            engine.circuit.satisfy(TRUE).unwrap().unwrap().len(),
            model.len(),
            "rendering must not create symbolic gates"
        );
    }

    #[test]
    fn cyclic_references_are_identified_without_recursive_expansion() {
        let program = crate::parse_program("(#struct Node () ((next (#ref Node))))").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        let reference = Value::Ref {
            place: Location {
                root: 0,
                path: Vec::new(),
            },
            target: Type::Named("Node".into()),
            mutable: false,
            pinned: false,
        };
        engine
            .bind(
                &mut state,
                "node".into(),
                Type::Named("Node".into()),
                Value::Record("Node".into(), vec![("next".into(), reference.clone())]),
            )
            .unwrap();
        engine.inputs.push(("node".into(), reference));
        engine.input_state = Some(state);
        let model = engine.circuit.satisfy(TRUE).unwrap().unwrap();
        assert_eq!(
            engine.render_inputs(0, &model),
            "node = ref#0(Node { next = ref#0 })"
        );
    }

    #[test]
    fn byte_limits_preserve_utf8_and_mark_truncated_output() {
        let mut output = Output::default();
        output.push(&"λ".repeat(BYTE_LIMIT));
        assert!(output.text.len() <= BYTE_LIMIT);
        assert!(output.text.ends_with("..."));
        assert!(std::str::from_utf8(output.text.as_bytes()).is_ok());
        let full = output.text.clone();
        output.push("another part");
        assert_eq!(output.text, full);
    }

    #[test]
    fn slices_display_the_selected_initial_elements_and_share_backing_identity() {
        let program = crate::parse_program("").unwrap();
        let checked = CheckedProgram::validate(&program).unwrap();
        let graph = Graph::new(checked.program(), checked.declarations());
        let mut engine = Engine::new(&checked, &graph, Span::new(0, 0, 1, 1));
        let mut state = State::new();
        engine
            .bind(
                &mut state,
                "values".into(),
                Type::Array(Box::new(Type::U8), 3),
                Value::Array(
                    Type::U8,
                    [7, 9, 11]
                        .into_iter()
                        .map(|value| Value::Bits(Circuit::constant(value, 8, false), Type::U8))
                        .collect(),
                ),
            )
            .unwrap();
        let place = state.frames.last().unwrap().locals["values"].0.clone();
        for (name, start, len) in [("suffix", 1, 2), ("empty", 3, 0)] {
            engine.inputs.push((
                name.into(),
                Value::Slice(symbolic::Slice {
                    place: place.clone(),
                    element: Type::U8,
                    start: Circuit::constant(start, 64, false),
                    len: Circuit::constant(len, 64, false),
                    mutable: false,
                }),
            ));
        }
        engine.input_state = Some(state);
        let model = engine.circuit.satisfy(TRUE).unwrap().unwrap();
        assert_eq!(engine.render_inputs(0, &model),
            "suffix = slice#0(start=1, len=2, values=[9u8, 11u8]), empty = slice#0(start=3, len=0, values=[])");
    }
}
