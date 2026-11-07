//! Bounded symbolic execution of checked Lim. Values keep machine widths and
//! references keep locations; the evaluator never executes native program code.
use super::validation::ValidationFact;
use super::*;
use crate::Statement;

#[path = "slices.rs"]
mod slices;

#[derive(Clone, Debug)]
pub(super) struct Slice {
    pub place: Location,
    pub element: Type,
    pub start: Word,
    pub len: Word,
    pub mutable: bool,
}

#[derive(Clone, Debug)]
pub(super) enum Value {
    Unit,
    Bool(Bit),
    Bits(Word, Type),
    Record(String, Vec<(String, Value)>),
    Array(Type, Vec<Value>),
    Tuple(Vec<Value>),
    Enum(String, Word, Vec<Option<Value>>),
    Slice(Slice),
    Ref {
        place: Location,
        target: Type,
        mutable: bool,
        pinned: bool,
    },
}

impl Value {
    pub fn boolean(&self) -> Result<Bit> {
        match self {
            Self::Bool(value) => Ok(*value),
            _ => Err("a proof proposition must have type #bool".into()),
        }
    }
    fn ty(&self) -> Type {
        match self {
            Self::Unit => Type::Unit,
            Self::Bool(_) => Type::Bool,
            Self::Bits(_, ty) => ty.clone(),
            Self::Record(name, _) | Self::Enum(name, _, _) => Type::Named(name.clone()),
            Self::Array(ty, values) => Type::Array(Box::new(ty.clone()), values.len()),
            Self::Tuple(values) => Type::Tuple(values.iter().map(Self::ty).collect()),
            Self::Slice(view) => {
                if view.mutable {
                    Type::MutableSlice(Box::new(view.element.clone()))
                } else {
                    Type::Slice(Box::new(view.element.clone()))
                }
            }
            Self::Ref {
                target,
                mutable,
                pinned,
                ..
            } => {
                if *pinned {
                    Type::PinnedReference {
                        mutable: *mutable,
                        target: Box::new(target.clone()),
                    }
                } else {
                    Type::Reference {
                        mutable: *mutable,
                        target: Box::new(target.clone()),
                    }
                }
            }
        }
    }
    fn contains_ref(&self) -> bool {
        match self {
            Self::Ref { .. } | Self::Slice(_) => true,
            Self::Record(_, fields) => fields.iter().any(|(_, value)| value.contains_ref()),
            Self::Array(_, values) | Self::Tuple(values) => values.iter().any(Self::contains_ref),
            Self::Enum(_, _, values) => values.iter().flatten().any(Self::contains_ref),
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum Segment {
    Field(usize),
    Index(Word),
    Payload(usize),
}
#[derive(Clone, Debug)]
pub(super) struct Location {
    pub root: usize,
    pub path: Vec<Segment>,
}
#[derive(Clone)]
pub(super) struct Frame {
    pub function: String,
    pub locals: BTreeMap<String, (Location, Type)>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Flow {
    Normal,
    Return,
    Break(Option<String>),
    Continue(Option<String>),
    Dead,
}
#[derive(Clone)]
pub(super) struct State {
    pub guard: Bit,
    heap: Vec<Value>,
    pub frames: Vec<Frame>,
    globals: BTreeMap<String, Location>,
    pub flow: Flow,
    pub value: Value,
    pub result: Option<Value>,
    observed: Bit,
    acted: Bit,
    required: Bit,
    pub validations: Vec<ValidationFact>,
}
impl State {
    pub fn new() -> Self {
        Self {
            guard: TRUE,
            heap: Vec::new(),
            frames: vec![Frame {
                function: String::new(),
                locals: BTreeMap::new(),
            }],
            globals: BTreeMap::new(),
            flow: Flow::Normal,
            value: Value::Unit,
            result: None,
            observed: FALSE,
            acted: FALSE,
            required: FALSE,
            validations: Vec::new(),
        }
    }
}

impl Engine<'_, '_> {
    fn allocate(&mut self, state: &mut State, value: Value) -> Result<Location> {
        if state.heap.len() >= 4096 {
            return Err("unproved: symbolic storage budget exhausted".into());
        }
        let place = Location {
            root: state.heap.len(),
            path: Vec::new(),
        };
        state.heap.push(value);
        Ok(place)
    }
    pub(super) fn bind(
        &mut self,
        state: &mut State,
        name: String,
        ty: Type,
        value: Value,
    ) -> Result<()> {
        self.compatible(&value, &ty)?;
        let place = self.allocate(state, value)?;
        state
            .frames
            .last_mut()
            .unwrap()
            .locals
            .insert(name, (place, ty));
        Ok(())
    }
    fn compatible(&self, value: &Value, ty: &Type) -> Result<()> {
        if self.resolve_type(&value.ty())? == self.resolve_type(ty)? {
            Ok(())
        } else {
            Err(format!(
                "proof value has type {:?}, expected {:?}",
                value.ty(),
                ty
            ))
        }
    }
    pub(super) fn fresh_value(
        &mut self,
        state: &mut State,
        ty: &Type,
        depth: usize,
    ) -> Result<Value> {
        self.tick()?;
        if depth > 32 {
            return Err("unproved: symbolic type nesting budget exhausted".into());
        }
        let ty = self.resolve_type(ty)?;
        if let Some((width, signed)) = scalar(&ty) {
            let word = self.circuit.word(width, signed);
            if ty == Type::Char {
                let end = Circuit::constant(0x110000, 32, false);
                let low = Circuit::constant(0xd800, 32, false);
                let high = Circuit::constant(0xe000, 32, false);
                let range = self.circuit.lt_word(&word, &end);
                let below = self.circuit.lt_word(&word, &low);
                let below_high = self.circuit.lt_word(&word, &high);
                let above = self.circuit.not(below_high);
                let scalar = self.circuit.or(below, above);
                let valid = self.circuit.and(range, scalar);
                state.guard = self.circuit.and(state.guard, valid);
            }
            return Ok(Value::Bits(word, ty));
        }
        match &ty {
            Type::Unit => Ok(Value::Unit),
            Type::Bool => Ok(Value::Bool(self.circuit.fresh())),
            Type::Tuple(types) => Ok(Value::Tuple(
                types
                    .iter()
                    .map(|ty| self.fresh_value(state, ty, depth + 1))
                    .collect::<Result<_>>()?,
            )),
            Type::Array(element, len) => {
                if *len > 64 {
                    return Err("unproved: symbolic arrays are limited to 64 elements".into());
                }
                let values = (0..*len)
                    .map(|_| self.fresh_value(state, element, depth + 1))
                    .collect::<Result<_>>()?;
                Ok(Value::Array((**element).clone(), values))
            }
            Type::Reference { target, mutable } | Type::PinnedReference { target, mutable } => {
                let value = self.fresh_value(state, target, depth + 1)?;
                let place = self.allocate(state, value)?;
                Ok(Value::Ref {
                    place,
                    target: (**target).clone(),
                    mutable: *mutable,
                    pinned: matches!(ty, Type::PinnedReference { .. }),
                })
            }
            Type::Named(name) if self.records.contains_key(name) => {
                let fields = self.records[name].clone();
                let mut values = Vec::new();
                for field in fields {
                    values.push((field.name, self.fresh_value(state, &field.ty, depth + 1)?));
                }
                Ok(Value::Record(name.clone(), values))
            }
            Type::Named(name) if self.enums.contains_key(name) => {
                let variants = self.enums[name].clone();
                if variants.is_empty() {
                    return Err("unproved: empty enum input has no inhabitable state".into());
                }
                let tag = self.circuit.word(64, false);
                let limit = Circuit::constant(variants.len() as u128, 64, false);
                let valid = self.circuit.lt_word(&tag, &limit);
                state.guard = self.circuit.and(state.guard, valid);
                let mut values = Vec::new();
                for variant in variants {
                    values.push(
                        variant
                            .fields
                            .first()
                            .map(|ty| self.fresh_value(state, ty, depth + 1))
                            .transpose()?,
                    );
                }
                Ok(Value::Enum(name.clone(), tag, values))
            }
            _ => Err(format!(
                "unproved: symbolic inputs of type {ty:?} are unsupported"
            )),
        }
    }

    pub(super) fn equal(&mut self, a: &Value, b: &Value) -> Result<Bit> {
        if self.resolve_type(&a.ty())? != self.resolve_type(&b.ty())? {
            return Err(format!(
                "proof equality compares incompatible types {:?} and {:?}",
                a.ty(),
                b.ty()
            ));
        }
        match(a,b){
            (Value::Unit,Value::Unit)=>Ok(TRUE),
            (Value::Bool(a),Value::Bool(b))=>{let different=self.circuit.xor(*a,*b);Ok(self.circuit.not(different))},
            (Value::Bits(a,_),Value::Bits(b,_))=>Ok(self.circuit.eq_word(a,b)),
            (Value::Record(_,a),Value::Record(_,b))=>{
                let mut equal=TRUE;for((_,a),(_,b))in a.iter().zip(b){let field=self.equal(a,b)?;equal=self.circuit.and(equal,field);}Ok(equal)
            }
            (Value::Array(_,a),Value::Array(_,b))|(Value::Tuple(a),Value::Tuple(b))=>{
                let mut equal=TRUE;for(a,b)in a.iter().zip(b){let item=self.equal(a,b)?;equal=self.circuit.and(equal,item);}Ok(equal)
            }
            (Value::Enum(_,at,a),Value::Enum(_,bt,b))=>{
                let mut equal=self.circuit.eq_word(at,bt);
                for(index,(a,b))in a.iter().zip(b).enumerate(){
                    if let(Some(a),Some(b))=(a,b){let field=self.equal(a,b)?;let tag=Circuit::constant(index as u128,64,false);let active=self.circuit.eq_word(at,&tag);let valid=self.circuit.or(self.circuit.not(active),field);equal=self.circuit.and(equal,valid);}
                    else if a.is_some()!=b.is_some(){let tag=Circuit::constant(index as u128,64,false);let active=self.circuit.eq_word(at,&tag);equal=self.circuit.and(equal,self.circuit.not(active));}
                }Ok(equal)
            }
            (Value::Ref{..},Value::Ref{..})=>Err("unproved: reference identity comparisons are not modeled; compare explicit referent values".into()),
            _=>Err("unproved: unsupported logical equality".into()),
        }
    }
    fn merge(&mut self, condition: Bit, a: &Value, b: &Value) -> Result<Value> {
        if condition == TRUE {
            return Ok(a.clone());
        }
        if condition == FALSE {
            return Ok(b.clone());
        }
        self.compatible(a, &b.ty())?;
        Ok(match (a, b) {
            (Value::Unit, Value::Unit) => Value::Unit,
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(self.circuit.ite(condition, *a, *b)),
            (Value::Bits(a, ty), Value::Bits(b, _)) => {
                Value::Bits(self.circuit.select(condition, a, b)?, ty.clone())
            }
            (Value::Array(ty, a), Value::Array(_, b)) => Value::Array(
                ty.clone(),
                a.iter()
                    .zip(b)
                    .map(|(a, b)| self.merge(condition, a, b))
                    .collect::<Result<_>>()?,
            ),
            (Value::Tuple(a), Value::Tuple(b)) => Value::Tuple(
                a.iter()
                    .zip(b)
                    .map(|(a, b)| self.merge(condition, a, b))
                    .collect::<Result<_>>()?,
            ),
            (Value::Record(name, a), Value::Record(_, b)) => Value::Record(
                name.clone(),
                a.iter()
                    .zip(b)
                    .map(|((field, a), (_, b))| Ok((field.clone(), self.merge(condition, a, b)?)))
                    .collect::<Result<_>>()?,
            ),
            _ => {
                return Err(
                    "unproved: conditional reference or enum storage requires path splitting"
                        .into(),
                )
            }
        })
    }
    fn lookup(&mut self, state: &mut State, name: &str) -> Result<Location> {
        if let Some((place, _)) = state.frames.last().unwrap().locals.get(name) {
            return Ok(place.clone());
        }
        if let Some(place) = state.globals.get(name) {
            return Ok(place.clone());
        }
        if let Some(ty) = self.globals.get(name).cloned() {
            let value = self.fresh_value(state, &ty, 0)?;
            let place = self.allocate(state, value)?;
            state.globals.insert(name.into(), place.clone());
            return Ok(place);
        }
        if let Some((ty, expr)) = self.constants.get(name).cloned() {
            let values = self.expr_as(state.clone(), &expr, true, &ty)?;
            if values.len() != 1 {
                return Err("unproved: branching global initialization".into());
            }
            let (updated, value) = values.into_iter().next().unwrap();
            *state = updated;
            let place = self.allocate(state, value)?;
            state.globals.insert(name.into(), place.clone());
            return Ok(place);
        }
        Err(format!("unknown proof value '{name}'"))
    }
    pub(super) fn read(&mut self, state: &State, place: &Location) -> Result<Value> {
        let value = state
            .heap
            .get(place.root)
            .ok_or("invalid symbolic reference")?
            .clone();
        self.read_path(value, &place.path)
    }
    fn read_path(&mut self, value: Value, path: &[Segment]) -> Result<Value> {
        let Some((first, rest)) = path.split_first() else {
            return Ok(value);
        };
        let next = match (first, value) {
            (Segment::Field(index), Value::Record(_, fields)) => fields
                .get(*index)
                .map(|(_, v)| v.clone())
                .ok_or("invalid proof field")?,
            (Segment::Field(index), Value::Tuple(values)) => values
                .get(*index)
                .cloned()
                .ok_or("invalid proof tuple field")?,
            (Segment::Payload(index), Value::Enum(_, _, values)) => values
                .get(*index)
                .cloned()
                .flatten()
                .ok_or("unproved: absent enum payload")?,
            (Segment::Index(index), Value::Array(_, values)) => {
                self.select_array(&values, index)?
            }
            _ => return Err("invalid symbolic projection".into()),
        };
        self.read_path(next, rest)
    }
    fn write(&mut self, state: &mut State, place: &Location, value: Value) -> Result<()> {
        self.invalidate_validations(state, place)?;
        let previous = state
            .heap
            .get(place.root)
            .ok_or("invalid symbolic reference")?
            .clone();
        state.heap[place.root] = self.write_path(previous, &place.path, &value)?;
        Ok(())
    }
    fn write_path(&mut self, mut old: Value, path: &[Segment], value: &Value) -> Result<Value> {
        let Some((first, rest)) = path.split_first() else {
            self.compatible(value, &old.ty())?;
            return Ok(value.clone());
        };
        match (first, &mut old) {
            (Segment::Field(index), Value::Record(_, fields)) => {
                let target = &mut fields.get_mut(*index).ok_or("invalid field")?.1;
                *target = self.write_path(target.clone(), rest, value)?;
            }
            (Segment::Field(index), Value::Tuple(values)) => {
                let target = values.get_mut(*index).ok_or("invalid tuple field")?;
                *target = self.write_path(target.clone(), rest, value)?;
            }
            (Segment::Payload(index), Value::Enum(_, _, values)) => {
                let target = values
                    .get_mut(*index)
                    .and_then(Option::as_mut)
                    .ok_or("invalid enum payload")?;
                *target = self.write_path(target.clone(), rest, value)?;
            }
            (Segment::Index(index), Value::Array(_, values)) => {
                for (i, target) in values.iter_mut().enumerate() {
                    let selected = Circuit::constant(i as u128, index.bits.len(), false);
                    let selected = self.circuit.eq_word(index, &selected);
                    let replacement = self.write_path(target.clone(), rest, value)?;
                    *target = self.merge(selected, &replacement, target)?;
                }
            }
            _ => return Err("unproved: unsupported write projection".into()),
        }
        Ok(old)
    }
    fn select_array(&mut self, values: &[Value], index: &Word) -> Result<Value> {
        let Some(mut result) = values.last().cloned() else {
            return Err("unproved: indexing an empty array".into());
        };
        for (i, value) in values.iter().enumerate().rev().skip(1) {
            let tag = Circuit::constant(i as u128, index.bits.len(), false);
            let selected = self.circuit.eq_word(index, &tag);
            result = self.merge(selected, value, &result)?;
        }
        Ok(result)
    }
    fn bounds(&mut self, state: &State, index: &Word, len: usize) -> Result<()> {
        let bound = Circuit::constant(len as u128, index.bits.len(), false);
        let valid = self.circuit.lt_word(index, &bound);
        let bad = self.circuit.and(state.guard, self.circuit.not(valid));
        self.require_unsat(bad, "an array index can be out of bounds")
    }
    fn representation(&self, name: &str, spec: bool) -> Result<()> {
        if !spec {
            return Ok(());
        }
        let program = self.checked.program();
        let Some(declaration) = program.declaration_spans.get(name) else {
            return Ok(());
        };
        let Some(source) = program.source_files.get(declaration.source_id as usize) else {
            return Err("missing proof declaration source".into());
        };
        let caller = program
            .source_files
            .get(self.span.source_id as usize)
            .ok_or("missing proof source")?;
        if self.opaque.contains(name) && source.path != caller.path {
            return Err(format!(
                "proof cannot inspect opaque representation '{name}'"
            ));
        }
        if let Some(owner) = crate::library::owner(&source.path) {
            if crate::library::owner(&caller.path).as_ref() != Some(&owner) {
                return Err(format!(
                    "proof cannot inspect private representation '{name}'"
                ));
            }
        }
        Ok(())
    }

    fn place(
        &mut self,
        mut state: State,
        expr: &Expr,
        spec: bool,
    ) -> Result<Vec<(State, Location)>> {
        if let Expr::Symbol(name) = expr {
            let place = self.lookup(&mut state, name)?;
            return Ok(vec![(state, place)]);
        }
        let (head, args) = form(expr).ok_or("proof borrow requires a checked place")?;
        if head == "deref" {
            arity(head, args, 1)?;
            return self
                .expr(state, &args[0], spec)?
                .into_iter()
                .map(|(state, value)| match value {
                    Value::Ref { place, .. } => Ok((state, place)),
                    _ => Err("#deref requires a reference".into()),
                })
                .collect();
        }
        if head == "get" {
            arity(head, args, 2)?;
            let mut output = Vec::new();
            for (state, mut place) in self.place(state, &args[0], spec)? {
                let mut base = self.read(&state, &place)?;
                if let Value::Ref {
                    place: referent, ..
                } = base
                {
                    place = referent;
                    base = self.read(&state, &place)?;
                }
                let index = match &base {
                    Value::Record(name, fields) => {
                        self.representation(name, spec)?;
                        let field = symbol(&args[1])?;
                        fields
                            .iter()
                            .position(|(name, _)| name == field)
                            .ok_or_else(|| format!("unknown proof field '{field}'"))?
                    }
                    Value::Tuple(values) => {
                        let index = literal_usize(&args[1])?;
                        if index >= values.len() {
                            return Err("tuple index out of bounds".into());
                        }
                        index
                    }
                    _ => return Err("#get requires a record or tuple".into()),
                };
                place.path.push(Segment::Field(index));
                output.push((state, place));
            }
            return Ok(output);
        }
        if head == "index" {
            arity(head, args, 2)?;
            let mut output = Vec::new();
            for (state, mut place) in self.place(state, &args[0], spec)? {
                let mut base = self.read(&state, &place)?;
                if let Value::Ref {
                    place: referent, ..
                } = base
                {
                    place = referent;
                    base = self.read(&state, &place)?;
                }
                let Value::Array(_, values) = base else {
                    return Err("proof indexing requires an array".into());
                };
                for (state, index) in self.expr_as(state, &args[1], spec, &Type::Usize)? {
                    let index = self.word_of(&index, &Type::Usize)?;
                    self.bounds(&state, &index, values.len())?;
                    let mut place = place.clone();
                    place.path.push(Segment::Index(index));
                    output.push((state, place));
                }
            }
            return Ok(output);
        }
        Err(format!("unproved: #{head} is not a modeled storage place"))
    }

    fn expr_as(
        &mut self,
        state: State,
        expr: &Expr,
        spec: bool,
        ty: &Type,
    ) -> Result<Vec<(State, Value)>> {
        if let Some((width, signed)) = scalar(&self.resolve_type(ty)?) {
            if let Expr::Integer(value) = expr {
                validate_integer(*value as u128, *value < 0, width, signed)?;
                return Ok(vec![(
                    state,
                    Value::Bits(
                        Circuit::constant(*value as u128, width, signed),
                        self.resolve_type(ty)?,
                    ),
                )]);
            }
            if let Expr::UnsignedInteger(value) = expr {
                validate_integer(*value, false, width, signed)?;
                return Ok(vec![(
                    state,
                    Value::Bits(
                        Circuit::constant(*value, width, signed),
                        self.resolve_type(ty)?,
                    ),
                )]);
            }
        }
        let output = self.expr(state, expr, spec)?;
        for (_, value) in &output {
            self.compatible(value, ty)?;
        }
        Ok(output)
    }

    pub(super) fn expr(
        &mut self,
        state: State,
        expr: &Expr,
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        if self.evaluation_depth >= 32 {
            return Err("unproved: proof evaluation nesting exceeds 32".into());
        }
        self.evaluation_depth += 1;
        let output = self.expr_inner(state, expr, spec);
        self.evaluation_depth -= 1;
        output
    }

    fn expr_inner(
        &mut self,
        mut state: State,
        expr: &Expr,
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        self.tick()?;
        match expr {
            Expr::Symbol(name) if name == "true" => return Ok(vec![(state, Value::Bool(TRUE))]),
            Expr::Symbol(name) if name == "false" => return Ok(vec![(state, Value::Bool(FALSE))]),
            Expr::Symbol(name) => {
                if let Some((owner, index)) = self.variant(name) {
                    return Ok(vec![(state, self.construct_enum(&owner, index, None)?)]);
                }
                let place = self.lookup(&mut state, name)?;
                let value = self.read(&state, &place)?;
                return Ok(vec![(state, value)]);
            }
            Expr::Char(value) => {
                return Ok(vec![(
                    state,
                    Value::Bits(Circuit::constant(*value as u128, 32, false), Type::Char),
                )])
            }
            Expr::Block(body) => {
                if spec {
                    return Err("specifications use expressions and pure function calls, not statement blocks".into());
                }
                return self.block_value(state, body);
            }
            Expr::Loop(body) => {
                if spec {
                    return Err(
                        "specifications cannot contain loops; call a checked function instead"
                            .into(),
                    );
                }
                return self.loop_value(state, None, None, body, None);
            }
            Expr::Labeled { label, expression } => {
                if let Expr::Loop(body) = expression.as_ref() {
                    return self.loop_value(state, Some(label), None, body, None);
                }
                return Err("unproved: unsupported labeled proof expression".into());
            }
            Expr::List(items) if items.is_empty() => return Ok(vec![(state, Value::Unit)]),
            Expr::List(items) if matches!(items.first(), Some(Expr::Function(_))) => {
                let Expr::Function(name) = &items[0] else {
                    unreachable!()
                };
                let function = self.function(name)?;
                if items.len() != function.parameters.len() + 1 {
                    return Err("invalid checked call arity".into());
                }
                return self.call_arguments(state, function, &items[1..], spec);
            }
            _ => {}
        }
        let (head, args) = form(expr)
            .ok_or("proof values require explicitly typed literals or modeled expressions")?;
        // Ordinary checking has already lowered #struct-literal to its ordered
        // internal constructor. Raw proof expressions still need the keyword.
        if !spec && self.records.contains_key(head) {
            return self.checked_record(state, head, args);
        }
        if head.starts_with("proof-") {
            match head {
                "proof-result" => {
                    arity(head, args, 0)?;
                    let value = state
                        .result
                        .clone()
                        .ok_or("#proof-result is only valid in a contract postcondition")?;
                    return Ok(vec![(state, value)]);
                }
                "proof-old" => {
                    arity(head, args, 1)?;
                    let mut old = self
                        .old
                        .clone()
                        .ok_or("#proof-old is only valid in a contract")?;
                    old.guard = state.guard;
                    let values = self.expr(old, &args[0], true)?;
                    let mut output = Vec::new();
                    for (old, value) in values {
                        let mut state = state.clone();
                        state.guard = old.guard;
                        output.push((state, value));
                    }
                    return Ok(output);
                }
                _ => return self.proposition(state, expr),
            }
        }
        if let Some(operation) = numeric(head) {
            return self.numeric_expr(state, expr, head, args, spec, operation);
        }
        self.builtin_expr(state, head, args, spec)
    }

    fn numeric_expr(
        &mut self,
        state: State,
        expr: &Expr,
        head: &str,
        args: &[Expr],
        spec: bool,
        operation: (Type, String, Option<String>),
    ) -> Result<Vec<(State, Value)>> {
        let (ty, op, mode) = operation;

        if spec
            && !matches!(expr,Expr::List(items) if items.first().is_some_and(|head| symbol(head).is_ok_and(|name| name.starts_with('#'))))
        {
            return Err("proof numeric operations require canonical # prefixed keywords".into());
        }
        if ty == Type::Char && !matches!(op.as_str(), "eq" | "ne" | "lt" | "le" | "gt" | "ge") {
            return Err("character operators only support comparisons".into());
        }

        if matches!(op.as_str(), "add" | "sub" | "mul" | "div" | "rem")
            && mode.is_none()
            && !matches!(ty, Type::F32 | Type::F64)
        {
            return Err(
                "integer arithmetic requires an explicit -wrap or -saturate operation".into(),
            );
        }
        if !matches!(op.as_str(), "add" | "sub" | "mul" | "div" | "rem") && mode.is_some() {
            return Err("non-arithmetic operations cannot have an overflow mode".into());
        }
        let boolean = ty == Type::Bool;
        if boolean {
            if op == "not" {
                arity(head, args, 1)?;
                return self
                    .expr(state, &args[0], spec)?
                    .into_iter()
                    .map(|(state, value)| {
                        Ok((state, Value::Bool(self.circuit.not(value.boolean()?))))
                    })
                    .collect();
            }
            arity(head, args, 2)?;
            let mut output = Vec::new();
            for (state, a) in self.expr(state, &args[0], spec)? {
                let a = a.boolean()?;
                if op == "and" || op == "or" {
                    let mut short = state.clone();
                    let short_condition = if op == "and" { self.circuit.not(a) } else { a };
                    short.guard = self.circuit.and(short.guard, short_condition);
                    output.push((short, Value::Bool(bit(op == "or"))));
                    let mut state = state;
                    let condition = if op == "and" { a } else { self.circuit.not(a) };
                    state.guard = self.circuit.and(state.guard, condition);
                    for (state, b) in self.expr(state, &args[1], spec)? {
                        output.push((state, Value::Bool(b.boolean()?)));
                    }
                } else {
                    for (state, b) in self.expr(state, &args[1], spec)? {
                        let b = b.boolean()?;
                        let different = self.circuit.xor(a, b);
                        let equal = self.circuit.not(different);
                        let value = match op.as_str() {
                            "eq" => equal,
                            "ne" => self.circuit.not(equal),
                            "bit-and" => self.circuit.and(a, b),
                            "bit-or" => self.circuit.or(a, b),
                            "bit-xor" => self.circuit.xor(a, b),
                            _ => return Err("unsupported boolean proof operator".into()),
                        };
                        output.push((state, Value::Bool(value)));
                    }
                }
            }
            return Ok(output);
        }
        if scalar(&ty).is_none() {
            return Err("unproved: floating point arithmetic is not modeled".into());
        }
        if op == "not" || op == "bit-not" {
            arity(head, args, 1)?;
            let mut output = Vec::new();
            for (state, value) in self.expr_as(state, &args[0], spec, &ty)? {
                let mut word = self.word_of(&value, &ty)?;
                for value in &mut word.bits {
                    *value = self.circuit.not(*value);
                }
                output.push((state, Value::Bits(word, ty.clone())));
            }
            return Ok(output);
        }
        arity(head, args, 2)?;
        let mut output = Vec::new();
        for (state, a) in self.expr_as(state, &args[0], spec, &ty)? {
            for (state, b) in self.expr_as(state, &args[1], spec, &ty)? {
                let a = self.word_of(&a, &ty)?;
                let b = self.word_of(&b, &ty)?;
                let result = if matches!(op.as_str(), "eq" | "ne" | "lt" | "le" | "gt" | "ge") {
                    let value = match op.as_str() {
                        "eq" => self.circuit.eq_word(&a, &b),
                        "ne" => {
                            let same = self.circuit.eq_word(&a, &b);
                            self.circuit.not(same)
                        }
                        "lt" => self.circuit.lt_word(&a, &b),
                        "le" => {
                            let greater = self.circuit.lt_word(&b, &a);
                            self.circuit.not(greater)
                        }
                        "gt" => self.circuit.lt_word(&b, &a),
                        "ge" => {
                            let less = self.circuit.lt_word(&a, &b);
                            self.circuit.not(less)
                        }
                        _ => unreachable!(),
                    };
                    Value::Bool(value)
                } else {
                    let (word, valid) = self.circuit.binary(&op, mode.as_deref(), &a, &b)?;
                    let bad = self.circuit.and(state.guard, self.circuit.not(valid));
                    self.require_unsat(bad, "arithmetic can trap")?;
                    Value::Bits(word, ty.clone())
                };
                output.push((state, result));
            }
        }
        return Ok(output);
    }

    fn builtin_expr(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        match head {
            "literal" | "if" | "call" | "unsafe-call" | "block" | "unsafe" | "as" => {
                self.control_expr(state, head, args, spec)
            }
            "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" | "deref" | "pin-read"
            | "deref-set" | "get" | "index" => self.reference_expr(state, head, args, spec),
            "borrow-slice" | "borrow-slice-mut" | "slice-of" | "slice-mut-of" | "slice-range"
            | "slice-mut-range" | "slice-len" | "slice-mut-len" | "slice-idx" | "slice-mut-idx"
            | "slice-mut-split" => self.slice_expr(state, head, args, spec),
            _ => self.data_expr(state, head, args, spec),
        }
    }
    fn control_expr(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        match head {
            "literal" => {
                arity(head, args, 2)?;
                let ty = proof_type(&args[0], spec)?;
                let value = match &args[1] {
                    Expr::Integer(n) => *n as u128,
                    Expr::UnsignedInteger(n) => *n,
                    _ => return Err("integer proof literal requires integer digits".into()),
                };
                let (width, signed) = scalar(&self.resolve_type(&ty)?)
                    .ok_or("unproved: this literal type is unsupported")?;
                if matches!(ty, Type::Char | Type::RawPointer { .. }) {
                    return Err("typed literals require an integer type".into());
                }
                validate_integer(
                    value,
                    matches!(&args[1],Expr::Integer(n) if *n<0),
                    width,
                    signed,
                )?;
                Ok(vec![(
                    state,
                    Value::Bits(
                        Circuit::constant(value, width, signed),
                        self.resolve_type(&ty)?,
                    ),
                )])
            }
            "if" => {
                if !matches!(args.len(), 2 | 3) {
                    return Err("#if requires a condition and branches".into());
                }
                let mut output = Vec::new();
                for (state, condition) in self.expr(state, &args[0], spec)? {
                    let condition = condition.boolean()?;
                    let mut yes = state.clone();
                    yes.guard = self.circuit.and(yes.guard, condition);
                    output.extend(self.expr(yes, &args[1], spec)?);
                    let mut no = state;
                    no.guard = self.circuit.and(no.guard, self.circuit.not(condition));
                    if let Some(other) = args.get(2) {
                        output.extend(self.expr(no, other, spec)?);
                    } else {
                        output.push((no, Value::Unit));
                    }
                }
                self.limit_paths(output.len())?;
                Ok(output)
            }
            "call" | "unsafe-call" => {
                arity(head, args, 2)?;
                let function = self.function(symbol(&args[0])?)?;
                if (head == "unsafe-call") != function.unsafe_call {
                    return Err("proof call must use the callee's actual safety spelling".into());
                }
                let mut named = HashMap::new();
                for argument in list(&args[1])? {
                    let pair = list(argument)?;
                    if pair.len() != 2 {
                        return Err("proof calls require named argument pairs".into());
                    }
                    let name = symbol(&pair[0])?;
                    if named.insert(name, &pair[1]).is_some() {
                        return Err("duplicate named proof argument".into());
                    }
                }
                if named.len() != function.parameters.len() {
                    return Err("proof call has missing or unknown named parameters".into());
                }
                let values = function
                    .parameters
                    .iter()
                    .map(|parameter| {
                        named
                            .get(parameter.name.as_str())
                            .copied()
                            .cloned()
                            .ok_or_else(|| format!("missing proof parameter '{}'", parameter.name))
                    })
                    .collect::<Result<Vec<_>>>()?;
                self.call_arguments(state, function, &values, spec)
            }
            "block" | "unsafe" => {
                let statements = args
                    .iter()
                    .map(crate::parse_statement)
                    .collect::<Result<Vec<_>>>()?;
                if spec {
                    return Err("specifications use expressions and pure function calls, not statement blocks".into());
                }
                self.block_value(state, &statements)
            }
            "as" => {
                arity(head, args, 2)?;
                let ty = proof_type(&args[1], spec)?;
                let resolved = self.resolve_type(&ty)?;
                if matches!(resolved, Type::Char | Type::RawPointer { .. }) {
                    return Err("unproved: only integer-to-integer casts are modeled".into());
                }
                let (width, signed) = scalar(&resolved).ok_or("unproved: noninteger cast")?;
                let mut output = Vec::new();
                for (state, value) in self.expr(state, &args[0], spec)? {
                    let Value::Bits(word, _) = value else {
                        return Err("integer cast requires an integer".into());
                    };
                    output.push((
                        state,
                        Value::Bits(self.circuit.cast(&word, width, signed), ty.clone()),
                    ));
                }
                Ok(output)
            }
            _ => Err(format!("unproved: unsupported proof operation #{head}")),
        }
    }
    fn reference_expr(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        match head {
            "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" => {
                arity(head, args, 1)?;
                if spec && head.ends_with("-mut") {
                    return Err("mutable borrowing is not a specification operation".into());
                }
                let mut output = Vec::new();
                for (state, place) in self.place(state, &args[0], spec)? {
                    let target = self.read(&state, &place)?.ty();
                    output.push((
                        state,
                        Value::Ref {
                            place,
                            target,
                            mutable: head.ends_with("-mut"),
                            pinned: head.starts_with("pin-"),
                        },
                    ));
                }
                Ok(output)
            }
            "deref" | "pin-read" => {
                arity(head, args, 1)?;
                let mut output = Vec::new();
                for (state, value) in self.expr(state, &args[0], spec)? {
                    let Value::Ref { place, .. } = value else {
                        return Err("reference required".into());
                    };
                    let value = self.read(&state, &place)?;
                    output.push((state, value));
                }
                Ok(output)
            }
            "deref-set" => {
                arity(head, args, 2)?;
                if spec {
                    return Err("specifications cannot write through references".into());
                }
                let mut output = Vec::new();
                for (state, reference) in self.expr(state, &args[0], spec)? {
                    let Value::Ref {
                        place,
                        target,
                        mutable: true,
                        ..
                    } = reference
                    else {
                        return Err("mutable reference required".into());
                    };
                    for (mut state, value) in self.expr_as(state, &args[1], spec, &target)? {
                        self.write(&mut state, &place, value)?;
                        output.push((state, Value::Unit));
                    }
                }
                Ok(output)
            }
            "get" => {
                arity(head, args, 2)?;
                let mut output = Vec::new();
                for (state, mut value) in self.expr(state, &args[0], spec)? {
                    if let Value::Ref { place, .. } = value {
                        value = self.read(&state, &place)?;
                    }
                    let value = match value {
                        Value::Record(name, fields) => {
                            self.representation(&name, spec)?;
                            fields
                                .into_iter()
                                .find(|(name, _)| Some(name.as_str()) == symbol(&args[1]).ok())
                                .map(|(_, value)| value)
                                .ok_or("unknown record field")?
                        }
                        Value::Tuple(values) => values
                            .get(literal_usize(&args[1])?)
                            .cloned()
                            .ok_or("tuple index out of bounds")?,
                        _ => return Err("#get requires record or tuple".into()),
                    };
                    output.push((state, value));
                }
                Ok(output)
            }
            "index" => {
                arity(head, args, 2)?;
                let mut output = Vec::new();
                for (state, mut value) in self.expr(state, &args[0], spec)? {
                    if let Value::Ref { place, .. } = value {
                        value = self.read(&state, &place)?;
                    }
                    let Value::Array(_, values) = value else {
                        return Err("proof indexing requires fixed arrays".into());
                    };
                    for (state, index) in self.expr_as(state, &args[1], spec, &Type::Usize)? {
                        let index = self.word_of(&index, &Type::Usize)?;
                        self.bounds(&state, &index, values.len())?;
                        let value = self.select_array(&values, &index)?;
                        output.push((state, value));
                    }
                }
                Ok(output)
            }
            _ => Err(format!("unproved: unsupported proof operation #{head}")),
        }
    }
    fn data_expr(
        &mut self,
        mut state: State,
        head: &str,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        match head {
            "tuple-of" | "array-of" | "array" | "tuple" => {
                if args.is_empty() {
                    return Err("aggregate construction needs an explicit type".into());
                }
                let ty = proof_type(&args[0], spec)?;
                let types = match self.resolve_type(&ty)? {
                    Type::Tuple(types) => types,
                    Type::Array(element, len) => vec![*element; len],
                    _ => return Err("proof aggregate type is not tuple or array".into()),
                };
                if types.len() != args.len() - 1 {
                    return Err("aggregate element count mismatch".into());
                }
                let mut runs = vec![(state, Vec::new())];
                for (ty, expr) in types.iter().zip(&args[1..]) {
                    let mut next = Vec::new();
                    for (state, previous) in runs {
                        for (state, value) in self.expr_as(state, expr, spec, ty)? {
                            let mut values = previous.clone();
                            values.push(value);
                            next.push((state, values));
                        }
                    }
                    runs = next;
                }
                Ok(runs
                    .into_iter()
                    .map(|(state, values)| {
                        (
                            state,
                            if let Type::Array(element, _) = &ty {
                                Value::Array((**element).clone(), values)
                            } else {
                                Value::Tuple(values)
                            },
                        )
                    })
                    .collect())
            }
            "array-repeat" => Err(
                "unproved: use #array-of in symbolic code instead of context-dependent repetition"
                    .into(),
            ),
            "struct-literal" => self.record_literal(state, args, spec),
            "enum-literal" => {
                if args.is_empty() || args.len() > 2 {
                    return Err("invalid enum literal".into());
                }
                self.enum_literal(state, symbol(&args[0])?, &args[1..], spec)
            }
            "match" => self.match_expr(state, args, spec),
            "clone" => {
                arity(head, args, 1)?;
                let mut output = Vec::new();
                for (state, value) in self.expr(state, &args[0], spec)? {
                    if let Value::Record(name, _) | Value::Enum(name, _, _) = &value {
                        if let Some(function) =
                            self.functions.get(&format!("{name}::clone")).copied()
                        {
                            output.extend(self.call(state, function, vec![value], spec)?);
                            continue;
                        }
                    }
                    output.push((state, value));
                }
                Ok(output)
            }
            "forget" | "drop" => {
                arity(head, args, 1)?;
                Ok(self
                    .expr(state, &args[0], spec)?
                    .into_iter()
                    .map(|(state, _)| (state, Value::Unit))
                    .collect())
            }
            "assert" | "debug-assert" => {
                arity(head, args, 1)?;
                let mut output = Vec::new();
                for (state, condition) in self.expr(state, &args[0], spec)? {
                    let condition = condition.boolean()?;
                    let bad = self.circuit.and(state.guard, self.circuit.not(condition));
                    self.require_unsat(bad, "a program assertion can fail")?;
                    output.push((state, Value::Unit));
                }
                Ok(output)
            }
            "panic" | "unreachable" => {
                arity(head, args, 0)?;
                self.require_unsat(state.guard, "a program can trap or reach #unreachable")?;
                state.guard = FALSE;
                state.flow = Flow::Dead;
                Ok(vec![(state, Value::Unit)])
            }
            "variant-is" => {
                arity(head, args, 2)?;
                let (owner, index) = self
                    .variant(symbol(&args[1])?)
                    .ok_or("unknown proof variant")?;
                let mut output = Vec::new();
                for (state, mut value) in self.expr(state, &args[0], spec)? {
                    if let Value::Ref { place, .. } = value {
                        value = self.read(&state, &place)?;
                    }
                    let Value::Enum(actual, tag, _) = value else {
                        return Err("variant test requires enum".into());
                    };
                    if actual != owner {
                        return Err("variant belongs to another enum".into());
                    }
                    let expected = Circuit::constant(index as u128, 64, false);
                    output.push((state, Value::Bool(self.circuit.eq_word(&tag, &expected))));
                }
                Ok(output)
            }
            _ if self.variant(head).is_some() => self.enum_literal(state, head, args, spec),
            _ => Err(format!("unproved: unsupported proof operation '#{head}'")),
        }
    }

    fn call_arguments(
        &mut self,
        state: State,
        function: &Function,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        if args.len() != function.parameters.len() {
            return Err("proof call arity mismatch".into());
        }
        let mut runs = vec![(state, Vec::new())];
        for (argument, parameter) in args.iter().zip(&function.parameters) {
            let mut next = Vec::new();
            for (state, previous) in runs {
                for (state, value) in self.expr_as(state, argument, spec, &parameter.ty)? {
                    let mut values = previous.clone();
                    values.push(value);
                    next.push((state, values));
                }
            }
            self.limit_paths(next.len())?;
            runs = next;
        }
        let mut output = Vec::new();
        for (state, values) in runs {
            output.extend(self.call(state, function, values, spec)?);
        }
        Ok(output)
    }

    pub(super) fn call(
        &mut self,
        mut state: State,
        function: &Function,
        arguments: Vec<Value>,
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        self.tick()?;
        if self.depth >= 128 {
            return Err("unproved: symbolic call depth budget exhausted".into());
        }
        if arguments.len() != function.parameters.len() {
            return Err("proof call arity mismatch".into());
        }
        for (value, parameter) in arguments.iter().zip(&function.parameters) {
            self.compatible(value, &parameter.ty)?;
        }
        if state.guard == FALSE {
            let value = self.fresh_value(&mut state, &function.return_type, 0)?;
            return Ok(vec![(state, value)]);
        }
        let validating = self.validation_argument(&function.name, &arguments)?;
        if let Some(trace) = self.trace.clone() {
            if trace.action() == function.name {
                let violation = match &trace {
                    Trace::When { .. } => state.observed,
                    Trace::Before { .. } => self.circuit.not(state.required),
                    Trace::Validated(rule) => {
                        let valid =
                            self.validated_argument(&state, &arguments[rule.action_parameter])?;
                        self.circuit.not(valid)
                    }
                };
                let violation = self.circuit.and(state.guard, violation);
                self.trace_violation = self.circuit.or(self.trace_violation, violation);
                state.acted = TRUE;
            }
        }
        if spec {
            for effect in ["global-write", "io", "allocation", "external", "asm"] {
                if self
                    .graph
                    .forbidden_effect(&function.name, effect)?
                    .is_some()
                {
                    return Err(format!(
                        "unproved: specification function '{}' may have {effect} effects",
                        function.name
                    ));
                }
            }
        }
        if function.external {
            return Err(format!(
                "unproved: external function '{}' has no checked implementation",
                function.name
            ));
        }
        let existing = state.heap.len();
        let before = state.heap.clone();
        state.frames.push(Frame {
            function: function.name.clone(),
            locals: BTreeMap::new(),
        });
        for (parameter, value) in function.parameters.iter().zip(arguments) {
            self.bind(
                &mut state,
                parameter.name.clone(),
                parameter.ty.clone(),
                value,
            )?;
        }
        self.depth += 1;
        let runs = self.statements(vec![state], &function.body);
        self.depth -= 1;
        let runs = runs?;
        let mut output = Vec::new();
        for mut state in runs {
            let value = match state.flow {
                Flow::Return => state.value.clone(),
                Flow::Dead => self.fresh_value(&mut state, &function.return_type, 0)?,
                _ => {
                    return Err(format!(
                        "unproved: function '{}' did not reach an explicit return",
                        function.name
                    ))
                }
            };
            self.compatible(&value, &function.return_type)?;
            state.flow = Flow::Normal;
            state.frames.pop();
            if spec {
                for (index, old) in before.iter().enumerate().take(existing) {
                    let same = self.equal_observable(old, &state.heap[index])?;
                    let bad = self.circuit.and(state.guard, self.circuit.not(same));
                    self.require_unsat(bad, "a specification call can mutate observable storage")?;
                }
            }
            if let Some(Trace::When {
                observed, expected, ..
            }) = &self.trace
            {
                if observed == &function.name {
                    let observed = value.boolean()?;
                    let selected = if *expected {
                        observed
                    } else {
                        self.circuit.not(observed)
                    };
                    state.observed = self.circuit.or(state.observed, selected);
                    let violation = self.circuit.and(state.acted, selected);
                    let violation = self.circuit.and(state.guard, violation);
                    self.trace_violation = self.circuit.or(self.trace_violation, violation);
                }
            }
            if let Some(Trace::Before { required, .. }) = &self.trace {
                if required == &function.name {
                    state.required = TRUE;
                }
            }
            if let Some(subject) = &validating {
                self.complete_validation(&mut state, subject, value.boolean()?)?;
            }
            output.push((state, value));
        }
        self.limit_paths(output.len())?;
        Ok(output)
    }

    fn equal_observable(&mut self, a: &Value, b: &Value) -> Result<Bit> {
        self.compatible(a, &b.ty())?;
        if let (Value::Slice(a), Value::Slice(b)) = (a, b) {
            let same = self.same_location(&a.place, &b.place);
            let start = self.circuit.eq_word(&a.start, &b.start);
            let len = self.circuit.eq_word(&a.len, &b.len);
            let same = self.circuit.and(same, start);
            return Ok(self.circuit.and(same, len));
        }
        if let (Value::Ref { place: a, .. }, Value::Ref { place: b, .. }) = (a, b) {
            return Ok(self.same_location(a, b));
        }
        if let (Value::Record(_, a), Value::Record(_, b)) = (a, b) {
            let mut equal = TRUE;
            for ((_, a), (_, b)) in a.iter().zip(b) {
                let same = self.equal_observable(a, b)?;
                equal = self.circuit.and(equal, same);
            }
            return Ok(equal);
        }
        if let (Value::Array(_, a), Value::Array(_, b)) | (Value::Tuple(a), Value::Tuple(b)) =
            (a, b)
        {
            let mut equal = TRUE;
            for (a, b) in a.iter().zip(b) {
                let same = self.equal_observable(a, b)?;
                equal = self.circuit.and(equal, same);
            }
            return Ok(equal);
        }
        if let (Value::Enum(_, at, a), Value::Enum(_, bt, b)) = (a, b) {
            let mut equal = self.circuit.eq_word(at, bt);
            for (index, (a, b)) in a.iter().zip(b).enumerate() {
                if let (Some(a), Some(b)) = (a, b) {
                    let same = self.equal_observable(a, b)?;
                    let selected = Circuit::constant(index as u128, 64, false);
                    let selected = self.circuit.eq_word(at, &selected);
                    let valid = self.circuit.or(self.circuit.not(selected), same);
                    equal = self.circuit.and(equal, valid);
                }
            }
            return Ok(equal);
        }
        self.equal(a, b)
    }
    fn block_value(&mut self, state: State, body: &[Statement]) -> Result<Vec<(State, Value)>> {
        let locals = state.frames.last().unwrap().locals.clone();
        let states = self.statements(vec![state], body)?;
        Ok(states
            .into_iter()
            .map(|mut state| {
                state.frames.last_mut().unwrap().locals = locals.clone();
                let value = state.value.clone();
                (state, value)
            })
            .collect())
    }
    fn statements(&mut self, mut states: Vec<State>, body: &[Statement]) -> Result<Vec<State>> {
        for statement in body {
            let mut output = Vec::new();
            for state in states {
                if state.flow == Flow::Normal {
                    output.extend(self.statement(state, statement)?);
                } else {
                    output.push(state);
                }
            }
            self.limit_paths(output.len())?;
            states = output;
        }
        Ok(states)
    }
    fn statement(&mut self, mut state: State, statement: &Statement) -> Result<Vec<State>> {
        self.tick()?;
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                let mut output = Vec::new();
                for (mut state, value) in self.expr_as(state, value, false, ty)? {
                    self.bind(&mut state, name.clone(), ty.clone(), value)?;
                    state.value = Value::Unit;
                    output.push(state);
                }
                Ok(output)
            }
            Statement::Assign { name, value } => {
                let place = self.lookup(&mut state, name)?;
                let ty = self.read(&state, &place)?.ty();
                let mut output = Vec::new();
                for (mut state, value) in self.expr_as(state, value, false, &ty)? {
                    self.write(&mut state, &place, value)?;
                    state.value = Value::Unit;
                    output.push(state);
                }
                Ok(output)
            }
            Statement::ArrayAssign { name, index, value } => {
                let target = Expr::List(
                    vec![
                        Expr::Symbol("index".into()),
                        Expr::Symbol(name.clone()),
                        index.clone(),
                    ]
                    .into(),
                );
                self.assign_place(state, &target, value)
            }
            Statement::FieldAssign { name, field, value } => {
                let target = Expr::List(
                    vec![
                        Expr::Symbol("get".into()),
                        Expr::Symbol(name.clone()),
                        Expr::Symbol(field.clone()),
                    ]
                    .into(),
                );
                self.assign_place(state, &target, value)
            }
            Statement::TupleAssign { name, index, value } => {
                let target = Expr::List(
                    vec![
                        Expr::Symbol("get".into()),
                        Expr::Symbol(name.clone()),
                        Expr::Integer(*index as i128),
                    ]
                    .into(),
                );
                self.assign_place(state, &target, value)
            }
            Statement::While { condition, body } => self
                .loop_value(state, None, Some(condition), body, None)
                .map(|runs| runs.into_iter().map(|(s, _)| s).collect()),
            Statement::Loop { body } => self
                .loop_value(state, None, None, body, None)
                .map(|runs| runs.into_iter().map(|(s, _)| s).collect()),
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                let mut output = Vec::new();
                for state in self.statement(state, init)? {
                    output.extend(
                        self.loop_value(state, None, Some(condition), body, Some(step))?
                            .into_iter()
                            .map(|(s, _)| s),
                    );
                }
                Ok(output)
            }
            Statement::Labeled { label, statement } => {
                let runs = match statement.as_ref() {
                    Statement::While { condition, body } => {
                        self.loop_value(state, Some(label), Some(condition), body, None)?
                    }
                    Statement::Loop { body } => {
                        self.loop_value(state, Some(label), None, body, None)?
                    }
                    Statement::For {
                        init,
                        condition,
                        step,
                        body,
                    } => {
                        let mut output = Vec::new();
                        for state in self.statement(state, init)? {
                            output.extend(self.loop_value(
                                state,
                                Some(label),
                                Some(condition),
                                body,
                                Some(step),
                            )?);
                        }
                        output
                    }
                    _ => return Err("unproved: only loop labels are modeled".into()),
                };
                Ok(runs.into_iter().map(|(s, _)| s).collect())
            }
            Statement::Return(value) => {
                let function = state.frames.last().unwrap().function.clone();
                let ty = self.function(&function)?.return_type.clone();
                let runs = if let Some(value) = value {
                    self.expr_as(state, value, false, &ty)?
                } else {
                    vec![(state, Value::Unit)]
                };
                Ok(runs
                    .into_iter()
                    .map(|(mut state, value)| {
                        state.flow = Flow::Return;
                        state.value = value;
                        state
                    })
                    .collect())
            }
            Statement::Expr(expr) => Ok(self
                .expr(state, expr, false)?
                .into_iter()
                .map(|(mut state, value)| {
                    state.value = value;
                    state
                })
                .collect()),
            Statement::Break
            | Statement::BreakTo(_)
            | Statement::Continue
            | Statement::ContinueTo(_) => {
                state.value = Value::Unit;
                state.flow = match statement {
                    Statement::Break => Flow::Break(None),
                    Statement::BreakTo(label) => Flow::Break(Some(label.clone())),
                    Statement::Continue => Flow::Continue(None),
                    Statement::ContinueTo(label) => Flow::Continue(Some(label.clone())),
                    _ => unreachable!(),
                };
                Ok(vec![state])
            }
            Statement::BreakValue(value) | Statement::BreakToValue { value, .. } => {
                let target = match statement {
                    Statement::BreakToValue { label, .. } => Some(label.clone()),
                    _ => None,
                };
                Ok(self
                    .expr(state, value, false)?
                    .into_iter()
                    .map(|(mut state, value)| {
                        state.flow = Flow::Break(target.clone());
                        state.value = value;
                        state
                    })
                    .collect())
            }
            Statement::Destructure { pattern, value, .. } => {
                let mut output = Vec::new();
                for (mut state, value) in self.expr(state, value, false)? {
                    let (matches, bindings) = self.pattern(&state, pattern, &value, None, false)?;
                    let bad = self.circuit.and(state.guard, self.circuit.not(matches));
                    self.require_unsat(bad, "a destructuring pattern can fail")?;
                    for (name, value) in bindings {
                        self.bind(&mut state, name, value.ty(), value)?;
                    }
                    state.value = Value::Unit;
                    output.push(state);
                }
                Ok(output)
            }
            Statement::LetElse {
                pattern,
                value,
                else_body,
                failure_pattern,
                ..
            } => {
                let mut output = Vec::new();
                for (state, value) in self.expr(state, value, false)? {
                    let (matches, bindings) = self.pattern(&state, pattern, &value, None, false)?;
                    let mut yes = state.clone();
                    yes.guard = self.circuit.and(yes.guard, matches);
                    for (name, value) in bindings {
                        self.bind(&mut yes, name, value.ty(), value)?;
                    }
                    yes.value = Value::Unit;
                    output.push(yes);
                    let mut no = state;
                    no.guard = self.circuit.and(no.guard, self.circuit.not(matches));
                    if let Some(pattern) = failure_pattern {
                        let (_, bindings) = self.pattern(&no, pattern, &value, None, false)?;
                        for (name, value) in bindings {
                            self.bind(&mut no, name, value.ty(), value)?;
                        }
                    }
                    output.extend(self.statements(vec![no], else_body)?);
                }
                Ok(output)
            }
            _ => Err("unproved: unsupported checked statement in symbolic execution".into()),
        }
    }
    fn assign_place(&mut self, state: State, target: &Expr, value: &Expr) -> Result<Vec<State>> {
        let mut output = Vec::new();
        for (state, place) in self.place(state, target, false)? {
            let ty = self.read(&state, &place)?.ty();
            for (mut state, value) in self.expr_as(state, value, false, &ty)? {
                self.write(&mut state, &place, value)?;
                state.value = Value::Unit;
                output.push(state);
            }
        }
        Ok(output)
    }

    fn loop_value(
        &mut self,
        state: State,
        label: Option<&str>,
        condition: Option<&Expr>,
        body: &[Statement],
        step: Option<&Statement>,
    ) -> Result<Vec<(State, Value)>> {
        let function = state.frames.last().unwrap().function.clone();
        if let Some(invariant) = label.and_then(|label| {
            self.invariants
                .get(&(function.clone(), label.into()))
                .cloned()
        }) {
            return self.inductive_loop(state, label, condition, body, step, &invariant);
        }
        let mut pending = vec![state];
        let mut output = Vec::new();
        for _ in 0..self.loop_limit {
            let mut next = Vec::new();
            for state in pending {
                let locals = state.frames.last().unwrap().locals.clone();
                let conditions = if let Some(condition) = condition {
                    self.expr(state, condition, false)?
                } else {
                    vec![(state, Value::Bool(TRUE))]
                };
                for (state, test) in conditions {
                    let test = test.boolean()?;
                    if condition.is_some() {
                        let mut exit = state.clone();
                        exit.guard = self.circuit.and(exit.guard, self.circuit.not(test));
                        exit.value = Value::Unit;
                        output.push((exit, Value::Unit));
                    }
                    let mut enter = state;
                    enter.guard = self.circuit.and(enter.guard, test);
                    if self.circuit.satisfy(enter.guard)?.is_none() {
                        continue;
                    }
                    for mut state in self.statements(vec![enter], body)? {
                        let continues = state.flow == Flow::Normal
                            || matches!(&state.flow,Flow::Continue(target)if target.is_none()||target.as_deref()==label);
                        if continues {
                            state.flow = Flow::Normal;
                            let runs = if let Some(step) = step {
                                self.statement(state, step)?
                            } else {
                                vec![state]
                            };
                            for mut state in runs {
                                state.frames.last_mut().unwrap().locals = locals.clone();
                                next.push(state);
                            }
                        } else if matches!(&state.flow,Flow::Break(target)if target.is_none()||target.as_deref()==label)
                        {
                            state.flow = Flow::Normal;
                            state.frames.last_mut().unwrap().locals = locals.clone();
                            let value = state.value.clone();
                            output.push((state, value));
                        } else {
                            state.frames.last_mut().unwrap().locals = locals.clone();
                            let value = state.value.clone();
                            output.push((state, value));
                        }
                    }
                }
            }
            self.limit_paths(next.len() + output.len())?;
            pending = next;
            if pending.is_empty() {
                return Ok(output);
            }
        }
        for state in pending {
            if self.circuit.satisfy(state.guard)?.is_some() {
                return Err(format!("unproved: loop exceeds {} symbolic iterations; supply a checked invariant and rank or increase #proof-loop-limit",self.loop_limit));
            }
        }
        Ok(output)
    }

    fn inductive_loop(
        &mut self,
        mut state: State,
        label: Option<&str>,
        condition: Option<&Expr>,
        body: &[Statement],
        step: Option<&Statement>,
        invariant: &Invariant,
    ) -> Result<Vec<(State, Value)>> {
        // Specification evaluation must not run ordinary statements, introduce
        // bindings, call user code, or alter guards except by pure branching.
        // In particular Expr::Block bypasses expr's `spec` flag today.
        fn pure(
            expr: &Expr,
            locals: &BTreeMap<String, (Location, Type)>,
            depth: usize,
        ) -> Result<()> {
            if depth > 64 {
                return Err("unproved: induction expression nesting exceeds 64".into());
            }
            match expr {
                Expr::Symbol(name) if matches!(name.as_str(),"true"|"false")||locals.contains_key(name)=>Ok(()),
                Expr::Integer(_)|Expr::UnsignedInteger(_)|Expr::Char(_)=>Ok(()),
                Expr::List(items) if matches!(items.first(),Some(Expr::Function(_)))=>Err("unproved: induction specifications cannot call user functions".into()),
                Expr::List(items) if items.is_empty()=>Ok(()),
                Expr::List(_)=>{
                    let(head,args)=form(expr).ok_or("unproved: induction specifications cannot call user functions")?;
                    if numeric(head).is_some()||matches!(head,"proof-and"|"proof-or"|"proof-not"|"proof-implies"|"proof-eq"|"if"|"index"|"deref") {
                        for arg in args{pure(arg,locals,depth+1)?;}return Ok(());
                    }
                    match head {
                        "literal"=>{arity(head,args,2)?;if !matches!(args[1],Expr::Integer(_)|Expr::UnsignedInteger(_)){return Err("unproved: nonliteral induction literal".into());}Ok(())},
                        "as"|"get"=>{arity(head,args,2)?;pure(&args[0],locals,depth+1)},
                        "proof-no-overflow"=>{arity(head,args,3)?;numeric(symbol(&args[0])?).ok_or("unproved: invalid induction overflow operation")?;pure(&args[1],locals,depth+1)?;pure(&args[2],locals,depth+1)},
                        _=>Err(format!("unproved: #{head} is not a supported pure induction expression")),
                    }
                }
                _=>Err("unproved: induction expressions require pure local values; blocks, calls, bindings and global initializers are unsupported".into()),
            }
        }
        if self.trace.is_some() {
            return Err("unproved: trace claims require complete loop exploration".into());
        }
        let function = state.frames.last().unwrap().function.clone();
        if self
            .graph
            .forbidden_effect(&function, "global-write")?
            .is_some()
        {
            return Err("unproved: induction over global mutation is unsupported".into());
        }
        let locals = state.frames.last().unwrap().locals.clone();
        // No alias can be carried through havoc, even via an unmodified
        // reference copied into a new iteration-local binding.
        if state.heap.iter().any(Value::contains_ref) {
            return Err(
                "unproved: induction over aliased or reference-bearing storage is unsupported"
                    .into(),
            );
        }
        // Lazy lookup of a global/constant can execute an initializer and can
        // introduce references not present in the entry heap. Reject such reads.
        enum Visit<'a> {
            Statement(&'a Statement),
            Expression(&'a Expr),
        }
        let mut pending: Vec<_> = body.iter().map(Visit::Statement).collect();
        if let Some(step) = step {
            pending.push(Visit::Statement(step));
        }
        while let Some(node) = pending.pop() {
            self.tick()?;
            match node {
                Visit::Statement(statement) => match statement {
                    Statement::Let { value, .. }
                    | Statement::Assign { value, .. }
                    | Statement::FieldAssign { value, .. }
                    | Statement::TupleAssign { value, .. }
                    | Statement::EnumPayloadAssign { value, .. }
                    | Statement::Destructure { value, .. }
                    | Statement::Expr(value)
                    | Statement::Return(Some(value))
                    | Statement::BreakValue(value)
                    | Statement::BreakToValue { value, .. } => {
                        pending.push(Visit::Expression(value))
                    }
                    Statement::ArrayAssign { index, value, .. } => {
                        pending.push(Visit::Expression(index));
                        pending.push(Visit::Expression(value));
                    }
                    Statement::While { condition, body } => {
                        pending.push(Visit::Expression(condition));
                        pending.extend(body.iter().map(Visit::Statement));
                    }
                    Statement::Loop { body } => pending.extend(body.iter().map(Visit::Statement)),
                    Statement::For {
                        init,
                        condition,
                        step,
                        body,
                    } => {
                        pending.push(Visit::Statement(init));
                        pending.push(Visit::Expression(condition));
                        pending.push(Visit::Statement(step));
                        pending.extend(body.iter().map(Visit::Statement));
                    }
                    Statement::Labeled { statement, .. } => {
                        pending.push(Visit::Statement(statement))
                    }
                    Statement::LetElse {
                        value, else_body, ..
                    } => {
                        pending.push(Visit::Expression(value));
                        pending.extend(else_body.iter().map(Visit::Statement));
                    }
                    _ => {}
                },
                Visit::Expression(expr) => match expr {
                    Expr::Symbol(name)
                        if !locals.contains_key(name)
                            && (self.globals.contains_key(name)
                                || self.constants.contains_key(name)) =>
                    {
                        return Err(
                            "unproved: induction cannot summarize lazy global or constant reads"
                                .into(),
                        )
                    }
                    Expr::List(items) => pending.extend(items.iter().map(Visit::Expression)),
                    Expr::Block(body) | Expr::Loop(body) => {
                        pending.extend(body.iter().map(Visit::Statement))
                    }
                    Expr::Labeled { expression, .. } => pending.push(Visit::Expression(expression)),
                    _ => {}
                },
            }
        }
        pure(&invariant.predicate, &locals, 0)?;
        pure(&invariant.rank, &locals, 0)?;
        // Keep the loop test pure too: otherwise a terminating test can mutate
        // untracked storage, transfer control, or invalidate the loop-head rank.
        if let Some(condition) = condition {
            pure(condition, &locals, 0)?;
        }
        let mut modified = BTreeSet::new();
        collect_modified(body, &mut modified)?;
        if let Some(step) = step {
            collect_modified(std::slice::from_ref(step), &mut modified)?;
        }
        let entry = self.proposition(state.clone(), &invariant.predicate)?;
        self.establish(entry, "loop invariant fails on entry")?;
        for name in modified {
            let Some((place, ty)) = locals.get(&name).cloned() else {
                if self.globals.contains_key(&name)
                    || state.globals.contains_key(&name)
                    || self.constants.contains_key(&name)
                {
                    return Err("unproved: induction cannot havoc global storage".into());
                }
                // An iteration-local binding is recreated by the body.
                continue;
            };
            if !place.path.is_empty() {
                return Err("unproved: induction requires owned root bindings".into());
            }
            let previous = self.read(&state, &place)?;
            if previous.contains_ref() {
                return Err("unproved: induction cannot havoc reference-bearing state".into());
            }
            let value = self.fresh_value(&mut state, &ty, 0)?;
            self.write(&mut state, &place, value)?;
        }
        let mut output = Vec::new();
        for (mut state, predicate) in self.proposition(state, &invariant.predicate)? {
            if state.flow != Flow::Normal {
                return Err("unproved: invariant transfers control".into());
            }
            state.guard = self.circuit.and(state.guard, predicate.boolean()?);
            for (state, rank) in self.expr(state, &invariant.rank, true)? {
                let Value::Bits(old_rank, old_type) = rank else {
                    return Err("loop rank must be an unsigned integer".into());
                };
                if old_rank.signed || state.flow != Flow::Normal {
                    return Err("loop rank must be a pure unsigned integer".into());
                }
                let tests = if let Some(condition) = condition {
                    self.expr(state, condition, false)?
                } else {
                    vec![(state, Value::Bool(TRUE))]
                };
                for (state, test) in tests {
                    if state.flow != Flow::Normal {
                        return Err("unproved: induction condition transfers control".into());
                    }
                    let test = test.boolean()?;
                    if condition.is_some() {
                        let mut exit = state.clone();
                        exit.guard = self.circuit.and(exit.guard, self.circuit.not(test));
                        exit.value = Value::Unit;
                        exit.frames.last_mut().unwrap().locals = locals.clone();
                        output.push((exit, Value::Unit));
                    }
                    let mut enter = state;
                    enter.guard = self.circuit.and(enter.guard, test);
                    if self.circuit.satisfy(enter.guard)?.is_none() {
                        continue;
                    }
                    for mut state in self.statements(vec![enter], body)? {
                        if state.flow == Flow::Normal
                            || matches!(&state.flow,Flow::Continue(target)if target.is_none()||target.as_deref()==label)
                        {
                            state.flow = Flow::Normal;
                            // The for-step and invariant use the loop's outer
                            // bindings, not locals declared during this iteration.
                            state.frames.last_mut().unwrap().locals = locals.clone();
                            let runs = if let Some(step) = step {
                                self.statement(state, step)?
                            } else {
                                vec![state]
                            };
                            for mut state in runs {
                                if state.flow != Flow::Normal {
                                    return Err("unproved: induction step transfers control".into());
                                }
                                state.frames.last_mut().unwrap().locals = locals.clone();
                                let preserved =
                                    self.proposition(state.clone(), &invariant.predicate)?;
                                self.establish(preserved, "loop invariant is not preserved")?;
                                for (state, rank) in self.expr(state, &invariant.rank, true)? {
                                    let Value::Bits(rank, ty) = rank else {
                                        return Err("loop rank is not numeric".into());
                                    };
                                    if state.flow != Flow::Normal
                                        || rank.signed
                                        || rank.bits.len() != old_rank.bits.len()
                                        || ty != old_type
                                    {
                                        return Err(
                                            "loop rank type changed or transfers control".into()
                                        );
                                    }
                                    let decreases = self.circuit.lt_word(&rank, &old_rank);
                                    let bad =
                                        self.circuit.and(state.guard, self.circuit.not(decreases));
                                    self.require_unsat(
                                        bad,
                                        "loop rank does not strictly decrease",
                                    )?;
                                }
                            }
                        } else {
                            if matches!(&state.flow,Flow::Break(target)if target.is_none()||target.as_deref()==label)
                            {
                                state.flow = Flow::Normal;
                            }
                            state.frames.last_mut().unwrap().locals = locals.clone();
                            let value = state.value.clone();
                            output.push((state, value));
                        }
                    }
                    self.limit_paths(output.len())?;
                }
            }
        }
        Ok(output)
    }
    fn variant(&self, name: &str) -> Option<(String, usize)> {
        self.enums.iter().find_map(|(owner, variants)| {
            variants
                .iter()
                .position(|variant| variant.name == name)
                .map(|index| (owner.clone(), index))
        })
    }
    fn construct_enum(&self, owner: &str, index: usize, payload: Option<Value>) -> Result<Value> {
        let variants = self.enums.get(owner).ok_or("unknown enum type")?;
        let variant = &variants[index];
        if let Some(ty) = variant.fields.first() {
            self.compatible(payload.as_ref().ok_or("missing enum payload")?, ty)?;
        } else if payload.is_some() {
            return Err("unexpected enum payload".into());
        }
        let mut values = vec![None; variants.len()];
        values[index] = payload;
        Ok(Value::Enum(
            owner.into(),
            Circuit::constant(index as u128, 64, false),
            values,
        ))
    }
    fn enum_literal(
        &mut self,
        state: State,
        name: &str,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        let (owner, index) = self
            .variant(name)
            .ok_or_else(|| format!("unknown enum variant '{name}'"))?;
        let ty = self.enums[&owner][index].fields.first().cloned();
        match ty {
            Some(ty) => {
                if args.len() != 1 {
                    return Err("enum constructor requires one payload".into());
                }
                let mut output = Vec::new();
                for (state, value) in self.expr_as(state, &args[0], spec, &ty)? {
                    output.push((state, self.construct_enum(&owner, index, Some(value))?));
                }
                Ok(output)
            }
            None => {
                if !args.is_empty() {
                    return Err("fieldless enum constructor takes no payload".into());
                }
                Ok(vec![(state, self.construct_enum(&owner, index, None)?)])
            }
        }
    }
    fn record_literal(
        &mut self,
        state: State,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        arity("struct-literal", args, 2)?;
        let name = symbol(&args[0])?.to_owned();
        let Type::Named(owner) = self.resolve_type(&Type::Named(name.clone()))? else {
            return Err("record construction requires named type".into());
        };
        self.representation(&owner, spec)?;
        let fields = self
            .records
            .get(&owner)
            .cloned()
            .ok_or("unknown proof record type")?;
        let mut provided = HashMap::new();
        for value in list(&args[1])? {
            let pair = list(value)?;
            if pair.len() != 2 {
                return Err("record construction requires (field value) pairs".into());
            }
            if provided.insert(symbol(&pair[0])?, &pair[1]).is_some() {
                return Err("duplicate record field".into());
            }
        }
        if provided.len() != fields.len() {
            return Err("missing or unknown record field".into());
        }
        let mut states = vec![(state, Vec::new())];
        for field in fields {
            let expr = provided
                .get(field.name.as_str())
                .copied()
                .ok_or("missing record field")?;
            let mut next = Vec::new();
            for (state, previous) in states {
                for (state, value) in self.expr_as(state, expr, spec, &field.ty)? {
                    let mut fields = previous.clone();
                    fields.push((field.name.clone(), value));
                    next.push((state, fields));
                }
            }
            states = next;
        }
        Ok(states
            .into_iter()
            .map(|(state, fields)| (state, Value::Record(owner.clone(), fields)))
            .collect())
    }
    fn checked_record(
        &mut self,
        state: State,
        owner: &str,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        let fields = self
            .records
            .get(owner)
            .cloned()
            .ok_or("unknown checked record type")?;
        if args.len() != fields.len() {
            return Err("checked record constructor arity mismatch".into());
        }
        let mut states = vec![(state, Vec::new())];
        for (field, expr) in fields.iter().zip(args) {
            let mut next = Vec::new();
            for (state, previous) in states {
                for (state, value) in self.expr_as(state, expr, false, &field.ty)? {
                    let mut fields = previous.clone();
                    fields.push((field.name.clone(), value));
                    next.push((state, fields));
                    self.limit_paths(next.len())?;
                }
            }
            states = next;
        }
        Ok(states
            .into_iter()
            .map(|(state, fields)| (state, Value::Record(owner.to_owned(), fields)))
            .collect())
    }
    fn pattern(
        &mut self,
        state: &State,
        pattern: &Expr,
        value: &Value,
        location: Option<Location>,
        spec: bool,
    ) -> Result<(Bit, Vec<(String, Value)>)> {
        if let Expr::Symbol(name) = pattern {
            if name == "_" {
                return Ok((TRUE, Vec::new()));
            }
            if let Some((owner, index)) = self.variant(name) {
                let Value::Enum(actual, tag, _) = value else {
                    return Err("enum pattern requires enum value".into());
                };
                if actual != &owner {
                    return Err("enum pattern type mismatch".into());
                }
                let expected = Circuit::constant(index as u128, 64, false);
                return Ok((self.circuit.eq_word(tag, &expected), Vec::new()));
            }
            if matches!(name.as_str(), "true" | "false") {
                let equal = self.equal(value, &Value::Bool(bit(name == "true")))?;
                return Ok((equal, Vec::new()));
            }
            return Ok((TRUE, vec![(name.clone(), value.clone())]));
        }
        let (head, args) = form(pattern).ok_or("unsupported proof pattern")?;
        if matches!(head, "ref" | "ref-mut" | "pin-ref" | "pin-ref-mut") {
            let Value::Ref {
                place,
                mutable,
                pinned,
                ..
            } = value
            else {
                return Err("borrowed pattern requires a reference".into());
            };
            if head.ends_with("-mut") && !mutable {
                return Err("mutable borrowed patterns require mutable references".into());
            }
            if head.starts_with("pin-") && !pinned {
                return Err("pinned patterns require pinned references".into());
            }
            let value = self.read(state, place)?;
            let pattern = args.first().ok_or("borrow pattern missing variant")?;
            let (condition, bindings) =
                self.pattern(state, pattern, &value, Some(place.clone()), spec)?;
            let mut output = Vec::new();
            for (name, mut value) in bindings {
                if let Value::Ref {
                    mutable, pinned, ..
                } = &mut value
                {
                    *mutable = head.ends_with("-mut");
                    *pinned = head.starts_with("pin-");
                    output.push((name, value));
                } else {
                    return Err("unproved: borrowed pattern binding could not be projected".into());
                }
            }
            return Ok((condition, output));
        }
        if head == "or" {
            let mut condition = FALSE;
            for pattern in args {
                let (matched, bindings) =
                    self.pattern(state, pattern, value, location.clone(), spec)?;
                if !bindings.is_empty() {
                    return Err("unproved: binding or-pattern".into());
                }
                condition = self.circuit.or(condition, matched);
            }
            return Ok((condition, Vec::new()));
        }
        if head == "tuple" || head == "tuple-of" {
            let Value::Tuple(values) = value else {
                return Err("tuple pattern requires tuple value".into());
            };
            if args.len() != values.len() {
                return Err("tuple pattern arity mismatch".into());
            }
            let mut condition = TRUE;
            let mut bindings = Vec::new();
            for (pattern, value) in args.iter().zip(values) {
                let (matched, children) = self.pattern(state, pattern, value, None, spec)?;
                condition = self.circuit.and(condition, matched);
                bindings.extend(children);
            }
            return Ok((condition, bindings));
        }
        if let Some((owner, index)) = self.variant(head) {
            let Value::Enum(actual, tag, values) = value else {
                return Err("enum pattern requires enum value".into());
            };
            if &owner != actual {
                return Err("enum pattern type mismatch".into());
            }
            let expected = Circuit::constant(index as u128, 64, false);
            let condition = self.circuit.eq_word(tag, &expected);
            if args.is_empty() {
                return Ok((condition, Vec::new()));
            }
            if args.len() != 1 {
                return Err("enum pattern has one payload".into());
            }
            let Some(payload) = values[index].as_ref() else {
                if condition == FALSE {
                    return Ok((FALSE, Vec::new()));
                }
                return Err("unproved: enum payload has no symbolic representation".into());
            };
            let payload = if let Some(mut place) = location {
                place.path.push(Segment::Payload(index));
                Value::Ref {
                    place,
                    target: payload.ty(),
                    mutable: true,
                    pinned: false,
                }
            } else {
                payload.clone()
            };
            let (matched, bindings) = self.pattern(state, &args[0], &payload, None, spec)?;
            return Ok((self.circuit.and(condition, matched), bindings));
        }
        let values = self.expr_as(state.clone(), pattern, spec, &value.ty())?;
        if values.len() != 1 {
            return Err("unproved: nonliteral match pattern".into());
        }
        Ok((self.equal(value, &values[0].1)?, Vec::new()))
    }
    fn check_match_guard(&self, expr: &Expr, depth: usize) -> Result<()> {
        if depth > 64 {
            return Err("unproved: match guard nesting exceeds 64".into());
        }
        match expr {
            Expr::Symbol(name) if !self.constants.contains_key(name) && !self.globals.contains_key(name)=>Ok(()),
            Expr::Integer(_)|Expr::UnsignedInteger(_)|Expr::Char(_)=>Ok(()),
            Expr::List(_) => {
                let (head,args)=form(expr).ok_or("unproved: unsupported match guard")?;
                match head {
                    "literal"=>Ok(()),
                    "get"|"as"|"variant-is"=> { arity(head,args,2)?; self.check_match_guard(&args[0],depth+1) },
                    "deref"|"index"|"if"=> { for arg in args {self.check_match_guard(arg,depth+1)?;} Ok(()) },
                    _ if numeric(head).is_some()=>{for arg in args {self.check_match_guard(arg,depth+1)?;} Ok(())},
                    _=>Err("unproved: match guards require pure builtin expressions; calls and blocks are unsupported".into()),
                }
            }
            _=>Err("unproved: match guards require pure builtin expressions; calls and blocks are unsupported".into()),
        }
    }
    fn match_expr(
        &mut self,
        state: State,
        args: &[Expr],
        spec: bool,
    ) -> Result<Vec<(State, Value)>> {
        if args.len() < 2 {
            return Err("match needs a value and cases".into());
        }
        let mut output = Vec::new();
        for (state, value) in self.expr(state, &args[0], spec)? {
            let mut remaining = state.guard;
            for arm in &args[1..] {
                let mut parts = list(arm)?;
                if parts
                    .first()
                    .and_then(|head| symbol(head).ok())
                    .is_some_and(|head| head.trim_start_matches('#') == "case")
                {
                    parts = &parts[1..];
                }
                if parts.len() < 2 {
                    return Err("match arm needs pattern and value".into());
                }
                let (matched, bindings) = self.pattern(&state, &parts[0], &value, None, spec)?;
                let mut arm = state.clone();
                arm.guard = self.circuit.and(remaining, matched);
                let old_locals = arm.frames.last().unwrap().locals.clone();
                for (name, value) in bindings {
                    self.bind(&mut arm, name, value.ty(), value)?;
                }
                let mut start = 1;
                if let Some(("when", guard)) = form(&parts[1]) {
                    if guard.len() != 1 {
                        return Err("guard needs one condition".into());
                    }
                    self.check_match_guard(&guard[0], 0)?;
                    let guards = self.expr(arm, &guard[0], spec)?;
                    if guards.len() != 1 {
                        return Err("unproved: branching match guard".into());
                    }
                    let (mut guarded, value) = guards.into_iter().next().unwrap();
                    let accepted = value.boolean()?;
                    let condition = self.circuit.and(matched, accepted);
                    remaining = self.circuit.and(remaining, self.circuit.not(condition));
                    guarded.guard = self.circuit.and(guarded.guard, accepted);
                    arm = guarded;
                    start = 2;
                } else {
                    remaining = self.circuit.and(remaining, self.circuit.not(matched));
                }
                let mut runs = vec![(arm, Value::Unit)];
                for expr in &parts[start..] {
                    let mut next = Vec::new();
                    for (state, previous) in runs {
                        if state.flow != Flow::Normal {
                            next.push((state, previous));
                        } else {
                            next.extend(self.expr(state, expr, spec)?);
                        }
                    }
                    runs = next;
                }
                for (mut state, value) in runs {
                    state.frames.last_mut().unwrap().locals = old_locals.clone();
                    output.push((state, value));
                }
            }
            self.require_unsat(remaining, "a match can be nonexhaustive")?;
        }
        self.limit_paths(output.len())?;
        Ok(output)
    }

    pub(super) fn array_property(
        &mut self,
        state: State,
        head: &str,
        args: &[Expr],
    ) -> Result<Vec<(State, Value)>> {
        arity(head, args, 2)?;
        let mut output = Vec::new();
        for (state, a) in self.expr(state, &args[0], true)? {
            let Value::Array(element_type, a) = a else {
                return Err("array theorem requires a fixed array value".into());
            };
            if a.len() > 64 {
                return Err("unproved: array properties support at most 64 elements".into());
            }
            if head == "proof-sorted" {
                let comparator = self.function(symbol(&args[1])?)?;
                if self.resolve_type(&comparator.return_type)? != Type::Bool
                    || comparator.parameters.len() != 2
                {
                    return Err(
                        "sort comparator must take two explicit values and return #bool".into(),
                    );
                }
                for parameter in &comparator.parameters {
                    if self.resolve_type(&parameter.ty)? != self.resolve_type(&element_type)? {
                        return Err(
                            "sort comparator parameter types must match the array element type"
                                .into(),
                        );
                    }
                }
                let mut result = TRUE;
                let mut state = state;
                for pair in a.windows(2) {
                    let calls = self.call(
                        state.clone(),
                        comparator,
                        vec![pair[1].clone(), pair[0].clone()],
                        true,
                    )?;
                    let mut pair_ok = TRUE;
                    for (run, value) in calls {
                        let condition = self.circuit.or(
                            self.circuit.not(run.guard),
                            self.circuit.not(value.boolean()?),
                        );
                        pair_ok = self.circuit.and(pair_ok, condition);
                    }
                    result = self.circuit.and(result, pair_ok);
                    state.value = Value::Unit;
                }
                output.push((state, Value::Bool(result)));
            } else {
                for (state, b) in self.expr(state, &args[1], true)? {
                    let Value::Array(other_type, b) = b else {
                        return Err("permutation theorem requires two arrays".into());
                    };
                    if b.len() > 64 {
                        return Err("unproved: array properties support at most 64 elements".into());
                    }
                    if self.resolve_type(&element_type)? != self.resolve_type(&other_type)? {
                        return Err("permutation arrays must have the same element type".into());
                    }
                    if a.len() != b.len() {
                        output.push((state, Value::Bool(FALSE)));
                        continue;
                    }
                    let mut equal = TRUE;
                    let width = 8;
                    for element in &a {
                        let mut left = Circuit::constant(0, width, false);
                        let mut right = Circuit::constant(0, width, false);
                        for value in &a {
                            let condition = self.equal(element, value)?;
                            let add = Word {
                                bits: std::iter::once(condition)
                                    .chain(std::iter::repeat(FALSE).take(width - 1))
                                    .collect(),
                                signed: false,
                            };
                            left = self.circuit.binary("add", Some("wrap"), &left, &add)?.0;
                        }
                        for value in &b {
                            let condition = self.equal(element, value)?;
                            let add = Word {
                                bits: std::iter::once(condition)
                                    .chain(std::iter::repeat(FALSE).take(width - 1))
                                    .collect(),
                                signed: false,
                            };
                            right = self.circuit.binary("add", Some("wrap"), &right, &add)?.0;
                        }
                        let counts = self.circuit.eq_word(&left, &right);
                        equal = self.circuit.and(equal, counts);
                    }
                    output.push((state, Value::Bool(equal)));
                }
            }
        }
        Ok(output)
    }
}

fn collect_modified(body: &[Statement], names: &mut BTreeSet<String>) -> Result<()> {
    fn expression(expr: &Expr, names: &mut BTreeSet<String>, depth: usize) -> Result<()> {
        if depth > 64 {
            return Err("unproved: induction effect nesting exceeds 64".into());
        }
        match expr {
            Expr::Block(body) | Expr::Loop(body) => statements(body, names, depth + 1),
            Expr::Labeled {
                expression: inner, ..
            } => expression(inner, names, depth + 1),
            Expr::Function(_) => {
                Err("unproved: induction cannot summarize user-call effects".into())
            }
            Expr::List(items) if matches!(items.first(), Some(Expr::Function(_))) => {
                Err("unproved: induction cannot summarize user-call effects".into())
            }
            Expr::List(items) if items.is_empty() => Ok(()),
            Expr::List(_) => {
                let (head, args) = form(expr)
                    .ok_or("unproved: induction cannot summarize indirect or user calls")?;
                if matches!(head, "block") {
                    let body = args
                        .iter()
                        .map(crate::parse_statement)
                        .collect::<Result<Vec<_>>>()?;
                    return statements(&body, names, depth + 1);
                }
                // Fail closed on new builtins, calls (including clone hooks),
                // mutable borrowing, raw/atomic/pinned writes and unsafe code.
                if numeric(head).is_none()
                    && !matches!(
                        head,
                        "if" | "literal"
                            | "as"
                            | "get"
                            | "index"
                            | "deref"
                            | "tuple-of"
                            | "array-of"
                            | "tuple"
                            | "struct-literal"
                            | "enum-literal"
                            | "variant-is"
                            | "assert"
                            | "debug-assert"
                    )
                {
                    return Err(format!(
                        "unproved: induction cannot summarize alias or effect operation #{head}"
                    ));
                }
                // Type/field/constructor metadata is not evaluated. Traverse
                // executable operands, including dynamic array indices.
                match head {
                    "literal" => Ok(()),
                    "as" | "get" | "variant-is" => {
                        arity(head, args, 2)?;
                        expression(&args[0], names, depth + 1)
                    }
                    "tuple-of" | "array-of" | "tuple" | "enum-literal" => {
                        for arg in args.iter().skip(1) {
                            expression(arg, names, depth + 1)?;
                        }
                        Ok(())
                    }
                    "struct-literal" => {
                        arity(head, args, 2)?;
                        for field in list(&args[1])? {
                            let pair = list(field)?;
                            if pair.len() != 2 {
                                return Err("invalid induction record literal".into());
                            }
                            expression(&pair[1], names, depth + 1)?;
                        }
                        Ok(())
                    }
                    _ => {
                        for arg in args {
                            expression(arg, names, depth + 1)?;
                        }
                        Ok(())
                    }
                }
            }
            Expr::Symbol(_) | Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Char(_) => Ok(()),
            _ => Err("unproved: unsupported induction effect syntax".into()),
        }
    }
    fn statements(body: &[Statement], names: &mut BTreeSet<String>, depth: usize) -> Result<()> {
        if depth > 64 {
            return Err("unproved: induction statement nesting exceeds 64".into());
        }
        for statement in body {
            match statement {
                Statement::Assign { name, value }
                | Statement::FieldAssign { name, value, .. }
                | Statement::TupleAssign { name, value, .. } => {
                    names.insert(name.clone());
                    expression(value, names, depth + 1)?;
                }
                Statement::ArrayAssign { name, index, value } => {
                    names.insert(name.clone());
                    expression(index, names, depth + 1)?;
                    expression(value, names, depth + 1)?;
                }
                Statement::Let { value, .. }
                | Statement::Expr(value)
                | Statement::Return(Some(value))
                | Statement::BreakValue(value)
                | Statement::BreakToValue { value, .. } => expression(value, names, depth + 1)?,
                Statement::While { condition, body } => {
                    expression(condition, names, depth + 1)?;
                    statements(body, names, depth + 1)?;
                }
                Statement::Loop { body } => statements(body, names, depth + 1)?,
                Statement::For {
                    init,
                    condition,
                    step,
                    body,
                } => {
                    statements(std::slice::from_ref(init.as_ref()), names, depth + 1)?;
                    expression(condition, names, depth + 1)?;
                    statements(std::slice::from_ref(step.as_ref()), names, depth + 1)?;
                    statements(body, names, depth + 1)?;
                }
                Statement::Labeled { statement, .. } => {
                    statements(std::slice::from_ref(statement.as_ref()), names, depth + 1)?
                }
                // Pattern evaluation and payload projections can introduce aliases
                // or execute specification expressions; no ownership summary yet.
                Statement::Destructure { .. }
                | Statement::LetElse { .. }
                | Statement::EnumPayloadAssign { .. } => {
                    return Err(
                        "unproved: induction over patterns or enum payload writes is unsupported"
                            .into(),
                    )
                }
                Statement::Return(None)
                | Statement::Break
                | Statement::BreakTo(_)
                | Statement::Continue
                | Statement::ContinueTo(_) => {}
            }
        }
        Ok(())
    }
    statements(body, names, 0)
}

fn validate_integer(value: u128, negative: bool, width: usize, signed: bool) -> Result<()> {
    let fits = if negative {
        signed && (width == 128 || (value as i128) >= -(1i128 << (width - 1)))
    } else if signed {
        value <= ((1u128 << (width - 1)) - 1)
    } else {
        width == 128 || value < (1u128 << width)
    };
    if fits {
        Ok(())
    } else {
        Err("proof integer literal is out of range for its explicit type".into())
    }
}
