use super::summaries::{Location, Summary};
use super::*;
use crate::typecheck::{AnalysisError, CheckedProgram};
use std::collections::{BTreeSet, HashSet};

const FACT_LIMIT: usize = 4096;
const STEP_LIMIT: usize = 200_000;
const IDENTITY_LIMIT: usize = 16 * 1024;
const SNAPSHOT_WORK_LIMIT: usize = 64 * 1024 * 1024;

fn comparison_type(expression: &Expr) -> Option<Type> {
    let (name, operator) = head(expression).split_once('.')?;
    if !matches!(operator, "<" | "<=" | ">" | ">=" | "==" | "!=") {
        return None;
    }
    let ty = crate::parse_type(Some(&symbol(name))).ok()?;
    matches!(
        ty,
        Type::Bool
            | Type::Char
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::Usize
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Isize
            | Type::F32
            | Type::F64
    )
    .then_some(ty)
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct Fact {
    key: String,
    dependencies: Vec<Location>,
    assumed: bool,
    span: Option<crate::Span>,
    epoch: usize,
}
#[derive(Clone, Debug)]
struct Value {
    key: String,
    ty: Type,
    place: Option<Location>,
    targets: Vec<Location>,
    fields: BTreeMap<String, Value>,
    truth: Vec<Fact>,
}
impl Value {
    fn plain(key: String, ty: Type) -> Self {
        Self {
            key,
            ty,
            place: None,
            targets: Vec::new(),
            fields: BTreeMap::new(),
            truth: Vec::new(),
        }
    }
}
#[derive(Clone, Debug)]
struct Loan {
    places: Vec<Location>,
    facts: Vec<Fact>,
}
#[derive(Clone, Default)]
struct State {
    values: HashMap<String, Value>,
    cells: HashMap<Location, Value>,
    facts: Vec<Fact>,
    fixed: Vec<(Expr, Location)>,
    loans: HashMap<String, Loan>,
    epochs: HashMap<Location, usize>,
    invalidated: HashMap<String, crate::Span>,
    mutable_bindings: HashSet<String>,
    dead: bool,
}
struct Engine<'a, 'p> {
    checked: &'a CheckedProgram<'p>,
    summaries: HashMap<String, Summary>,
    function: String,
    span: Option<crate::Span>,
    serial: usize,
    steps: usize,
    entry: State,
    spec_depth: usize,
    validation_depth: usize,
    linear: crate::linearcheck::LinearTypes,
    identity_work: usize,
}
impl Engine<'_, '_> {
    fn program(&self) -> &Program {
        self.checked.program()
    }
    fn error(&self, message: impl Into<String>) -> AnalysisError {
        (
            format!("contract in '{}': {}", self.function, message.into()),
            crate::DiagnosticCode::Contract,
            self.span,
            Vec::new(),
        )
    }
    fn tick(&mut self) -> Result<(), AnalysisError> {
        self.steps += 1;
        if self.steps > STEP_LIMIT {
            Err(self
                .error("local evidence work budget exhausted; no partial analysis was accepted"))
        } else {
            Ok(())
        }
    }
    fn charge(&mut self, bytes: usize) -> Result<(), AnalysisError> {
        self.identity_work = self.identity_work.saturating_add(bytes);
        if self.identity_work > SNAPSHOT_WORK_LIMIT {
            Err(self.error(
                "local identity/snapshot work budget exhausted; no partial analysis was accepted",
            ))
        } else {
            Ok(())
        }
    }
    fn check_key(&mut self, key: &str) -> Result<(), AnalysisError> {
        if key.len() > IDENTITY_LIMIT {
            return Err(self.error("predicate value identity exceeds 16 KiB; split the expression into a function boundary"));
        }
        self.charge(key.len())
    }
    fn check_value(&mut self, value: &Value) -> Result<(), AnalysisError> {
        self.check_key(&value.key)?;
        self.charge(value_weight(value).saturating_sub(value.key.len()))
    }
    fn snapshot(&mut self, state: &State) -> Result<State, AnalysisError> {
        self.charge(state_weight(state))?;
        Ok(state.clone())
    }
    fn entry_snapshot(&mut self) -> Result<State, AnalysisError> {
        let bytes = state_weight(&self.entry);
        self.charge(bytes)?;
        Ok(self.entry.clone())
    }
    fn fresh(&mut self, prefix: &str) -> String {
        self.serial += 1;
        format!("{prefix}@{}", self.serial)
    }
    fn resolve(&self, ty: &Type) -> Type {
        crate::typed_ir::resolve_type(ty, &self.checked.declarations().aliases)
            .expect("ordinary type checking resolved aliases")
    }
    fn types(&self, s: &State) -> HashMap<String, Type> {
        s.values
            .iter()
            .map(|(n, v)| (n.clone(), v.ty.clone()))
            .collect()
    }
    fn loc_key(loc: &Location) -> String {
        format!("{}{}", loc.root, loc.path.join(""))
    }
    fn reference(&mut self, mut locations: Vec<Location>, ty: Type, key: Option<String>) -> Value {
        if locations.is_empty() {
            locations.push(Location::root(self.fresh("unknown:reference")));
        }
        locations.sort();
        locations.dedup();
        let key = key.unwrap_or_else(|| format!("&{:?}", locations));
        let mut v = Value::plain(key, ty);
        v.targets = locations;
        v
    }
    fn unknown(&mut self, ty: Type) -> Value {
        if matches!(
            self.resolve(&ty),
            Type::Reference { .. }
                | Type::PinnedReference { .. }
                | Type::Slice(_)
                | Type::MutableSlice(_)
        ) {
            let root = Location::root(self.fresh("unknown:value"));
            return self.reference(vec![root], ty, None);
        }
        Value::plain(self.fresh("value"), ty)
    }
    fn equivalent(&self, a: &Type, b: &Type) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        a == b
            || matches!((&a,&b),(Type::Reference{target:a,..},Type::Reference{target:b,mutable:false})if a==b)
    }
    fn may_overlap(a: &Location, b: &Location) -> bool {
        if a.root.starts_with("unknown:")
            || b.root.starts_with("unknown:")
            || a.path.contains(&"^".into())
            || b.path.contains(&"^".into())
        {
            return true;
        }
        if a.root.starts_with("parameter:") && b.root.starts_with("parameter:") && a.root != b.root
        {
            return true;
        }
        a.overlaps(b)
    }
    fn invalidate(&mut self, s: &mut State, places: &[Location], unknown: bool) {
        let invalid = |f: &Fact| {
            unknown && !f.dependencies.is_empty()
                || f.dependencies
                    .iter()
                    .any(|d| places.iter().any(|w| Self::may_overlap(d, w)))
        };
        if let Some(span) = self.span {
            for fact in s.facts.iter().filter(|f| invalid(f)) {
                s.invalidated.insert(fact.key.clone(), span);
            }
        }
        s.facts.retain(|f| !invalid(f));
        fn captured(v: &mut Value, invalid: &impl Fn(&Fact) -> bool) {
            v.truth.retain(|f| !invalid(f));
            for field in v.fields.values_mut() {
                captured(field, invalid);
            }
        }
        for v in s.values.values_mut() {
            captured(v, &invalid)
        }
        for v in s.cells.values_mut() {
            captured(v, &invalid)
        }
        s.cells
            .retain(|p, _| !(unknown || places.iter().any(|w| Self::may_overlap(p, w))));
        self.serial += 1;
        if unknown {
            s.epochs
                .insert(Location::root("unknown:write"), self.serial);
        }
        for place in places {
            s.epochs.insert(place.clone(), self.serial);
        }
        if unknown {
            let handles = s
                .values
                .iter()
                .filter(|(name, value)| {
                    s.mutable_bindings.contains(*name)
                        && matches!(
                            self.resolve(&value.ty),
                            Type::Reference { .. } | Type::PinnedReference { .. }
                        )
                })
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>();
            for name in handles {
                let target = Location::root(self.fresh("unknown:reference-write"));
                let value = s.values.get_mut(&name).unwrap();
                value.targets = vec![target];
                value.key = format!("&{:?}", value.targets);
            }
        }
    }
    fn current(&self, s: &State, fact: &Fact) -> bool {
        !fact.dependencies.iter().any(|dep| {
            s.epochs
                .iter()
                .any(|(place, epoch)| *epoch > fact.epoch && Self::may_overlap(dep, place))
        })
    }
    fn add(&self, s: &mut State, fact: Fact) -> Result<(), AnalysisError> {
        if !self.current(s, &fact) {
            return Ok(());
        }
        if let Some(old) = s.facts.iter_mut().find(|f| f.key == fact.key) {
            if !fact.assumed {
                *old = fact
            }
            return Ok(());
        }
        if s.facts.len() >= FACT_LIMIT {
            return Err(self.error("predicate evidence budget exhausted"));
        }
        s.facts.push(fact);
        Ok(())
    }
    fn require(&self, s: &State, fact: &Fact) -> Result<(), AnalysisError> {
        if s.facts.iter().any(|f| f.key == fact.key) {
            return Ok(());
        }
        let mut error=self.error(format!("missing evidence for {}; declare #requires, validate with #if-valid, or use an explicit #assume",fact.key));
        if let Some(span) = s.invalidated.get(&fact.key) {
            error.3.push((
                *span,
                "evidence became unavailable after this possible write".into(),
            ));
        }
        Err(error)
    }
    fn read(&mut self, s: &mut State, place: &Location, ty: Type) -> Value {
        if let Some(v) = s.cells.get(place) {
            let mut v = v.clone();
            v.place = Some(place.clone());
            v.ty = ty;
            return v;
        }
        let epoch = s
            .epochs
            .iter()
            .filter(|(p, _)| Self::may_overlap(p, place))
            .map(|(_, n)| *n)
            .max()
            .unwrap_or(0);
        let mut value = Value::plain(
            format!("read:{}:{}", Self::loc_key(place), epoch),
            ty.clone(),
        );
        value.place = Some(place.clone());
        if matches!(
            self.resolve(&ty),
            Type::Reference { .. }
                | Type::PinnedReference { .. }
                | Type::Slice(_)
                | Type::MutableSlice(_)
        ) {
            value.targets.push(Location::root(format!(
                "unknown:loaded:{}:{}",
                Self::loc_key(place),
                epoch
            )));
            value.key = format!("&{:?}", value.targets);
        }
        s.cells.insert(place.clone(), value.clone());
        value
    }
    fn store(
        &mut self,
        s: &mut State,
        place: &Location,
        value: &Value,
        write: bool,
    ) -> Result<(), AnalysisError> {
        if write {
            self.invalidate(s, std::slice::from_ref(place), false);
            self.serial += 1;
        }
        if value.targets.is_empty() {
            if let Some(previous) = &value.place {
                self.relocate(s, previous, place)?;
            }
        }
        if let Some(previous) = &value.place {
            if previous != place && value.targets.is_empty() {
                let cells = s
                    .cells
                    .iter()
                    .filter(|(location, _)| {
                        location.root == previous.root
                            && location.path.starts_with(&previous.path)
                            && location.path.len() > previous.path.len()
                    })
                    .map(|(location, value)| (location.clone(), value.clone()))
                    .collect::<Vec<_>>();
                for (location, mut cell) in cells {
                    let mut target = place.clone();
                    target
                        .path
                        .extend_from_slice(&location.path[previous.path.len()..]);
                    cell.place = Some(target.clone());
                    s.cells.insert(target, cell);
                }
            }
        }
        let mut value = value.clone();
        value.place = Some(place.clone());
        s.cells.insert(place.clone(), value.clone());
        for (field, v) in &value.fields {
            self.store(s, &place.child(field), v, false)?;
        }
        Ok(())
    }
    fn materialize(&mut self, value: &mut Value, s: &mut State) -> Result<(), AnalysisError> {
        if value.place.is_none()
            && value.targets.is_empty()
            && matches!(
                self.resolve(&value.ty),
                Type::Named(_) | Type::Array(..) | Type::Tuple(_)
            )
        {
            let place = Location::root(self.fresh("temporary"));
            self.store(s, &place, value, false)?;
            value.place = Some(place);
        }
        Ok(())
    }
    fn consume_owner(&self, value: &Value, s: &mut State) {
        if value.targets.is_empty() && self.linear.is_linear(&value.ty) {
            if let Some(place) = &value.place {
                if place.path.is_empty() {
                    s.fixed.retain(|(_, root)| root.root != place.root);
                }
            }
        }
    }
    fn places(&mut self, e: &Expr, s: &mut State) -> Result<Vec<Location>, AnalysisError> {
        self.tick()?;
        match e {
            Expr::Symbol(_) => Ok(self.eval(e, s)?.place.into_iter().collect()),
            Expr::List(xs) => match head(e) {
                "deref" => Ok(self.eval(&xs[1], s)?.targets),
                "get" | "index" | "index-proven" | "slice-idx" | "slice-mut-idx" => {
                    let base = self.eval(&xs[1], s)?;
                    let mut roots = if base.targets.is_empty() {
                        base.place.into_iter().collect()
                    } else {
                        base.targets
                    };
                    let segment = if head(e) == "get" {
                        match &xs[2] {
                            Expr::Symbol(n) => format!(".{n}"),
                            Expr::Integer(n) => format!(".{n}"),
                            _ => return Err(self.error("invalid field in contract place")),
                        }
                    } else {
                        let mut index = self.eval(&xs[2], s)?;
                        if head(e) == "index-proven" {
                            if matches!(xs[2], Expr::Integer(_) | Expr::UnsignedInteger(_)) {
                                index.ty = Type::Usize;
                            }
                            if !self.equivalent(&index.ty, &Type::Usize) {
                                return Err(self.error("#index-proven requires a #usize index"));
                            }
                            let (Type::Reference { target, .. }
                            | Type::PinnedReference { target, .. }) = self.resolve(&base.ty)
                            else {
                                return Err(self.error("#index-proven requires an array reference"));
                            };
                            let Type::Array(_, length) = *target else {
                                return Err(self.error("#index-proven requires a fixed array"));
                            };
                            let length = Value::plain(length.to_string(), Type::Usize);
                            let fact = self.comparison_fact(
                                "usize.<",
                                &[index.clone(), length],
                                false,
                                self.serial,
                            )?;
                            self.require(s, &fact)?;
                        }
                        format!("[{}]", index.key)
                    };
                    for root in &mut roots {
                        root.path.push(segment.clone());
                    }
                    Ok(roots)
                }
                "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" => self.places(&xs[1], s),
                _ => Ok(Vec::new()),
            },
            _ => Ok(Vec::new()),
        }
    }
    fn expr_type(&self, e: &Expr, s: &State) -> Result<Type, AnalysisError> {
        fn observation(e: &Expr) -> Expr {
            if head(e) == "result" {
                return symbol("__lim_contract_result");
            }
            match e {
                Expr::List(xs) => Expr::List(xs.iter().map(observation).collect::<Vec<_>>().into()),
                _ => e.clone(),
            }
        }
        crate::typecheck::contract_expression_type(
            &observation(e),
            &self.types(s),
            self.program(),
            self.checked.declarations(),
        )
        .map_err(|e| self.error(e))
    }
    fn predicate_requirements(
        &mut self,
        e: &Expr,
        s: &mut State,
    ) -> Result<Option<(prerequisites::Requirements, State)>, AnalysisError> {
        let Some(Expr::Function(name)) = parts(e).first() else {
            return Ok(None);
        };
        let requirements = self.program().contracts.effective_requires[name].clone();
        if requirements.nodes.is_empty() {
            return Ok(None);
        }
        let f = self.program().contracts.originals[name].clone();
        let mut interface = self.snapshot(s)?;
        for (parameter, expression) in f.parameters.iter().zip(&parts(e)[1..]) {
            let mut value = self.spec_value(expression, s)?;
            if matches!(
                expression,
                Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_)
            ) {
                value.ty = parameter.ty.clone();
            }
            interface.values.insert(parameter.name.clone(), value);
        }
        Ok(Some((requirements, interface)))
    }
    fn predicate(&mut self, e: &Expr, s: &mut State, assumed: bool) -> Result<Fact, AnalysisError> {
        let mut fact = self.predicate_base(e, s, assumed)?;
        if let Some((requirements, mut interface)) = self.predicate_requirements(e, s)? {
            // A predicate's validity also depends on the observations that
            // keep its declared prerequisites valid. Never infer facts from
            // predicate bodies, and never recursively enumerate DAG paths.
            let mut dependencies = std::mem::take(&mut fact.dependencies)
                .into_iter().collect::<BTreeSet<_>>();
            for expression in requirements.ordered() {
                let prerequisite = self.predicate_base(expression, &mut interface, assumed)?;
                for dependency in prerequisite.dependencies {
                    self.charge(location_weight(&dependency))?;
                    dependencies.insert(dependency);
                }
            }
            fact.dependencies = dependencies.into_iter().collect();
        }
        Ok(fact)
    }
    fn constraint_facts(&mut self, e: &Expr, s: &mut State) -> Result<Vec<Fact>, AnalysisError> {
        let root = self.predicate(e, s, false)?;
        let mut facts = Vec::new();
        if let Some((requirements, mut interface)) = self.predicate_requirements(e, s)? {
            for expression in requirements.ordered() {
                facts.push(self.predicate(expression, &mut interface, false)?);
            }
        }
        facts.push(root);
        Ok(facts)
    }
    fn require_constraint(&mut self, e: &Expr, s: &mut State) -> Result<Vec<Fact>, AnalysisError> {
        // #where is an implicit checked obligation. A promise/assumption of P
        // remains only P; consuming it as a constraint also needs P's domain.
        let facts = self.constraint_facts(e, s)?;
        for fact in &facts {
            self.require(s, fact)?;
        }
        Ok(facts)
    }
    fn predicate_base(&mut self, e: &Expr, s: &mut State, assumed: bool) -> Result<Fact, AnalysisError> {
        self.validate_spec(e)?;
        let xs = parts(e);
        if let Some(input_type) = comparison_type(e) {
            self.expr_type(e, s)?;
            let mut args = Vec::new();
            for expression in &xs[1..] {
                let mut value = self.spec_value(expression, s)?;
                if matches!(
                    expression,
                    Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_)
                ) {
                    value.ty = input_type.clone();
                }
                if !self.equivalent(&value.ty, &input_type) {
                    return Err(self.error("incorrect comparison argument type in contract"));
                }
                args.push(value);
            }
            return self.comparison_fact(head(e), &args, assumed, self.serial);
        }
        let Some(Expr::Function(name)) = xs.first() else {
            return Err(self.error("evidence must be a named Boolean predicate or typed comparison; requirements have AND semantics"));
        };
        let f = self
            .program()
            .contracts
            .originals
            .get(name)
            .cloned()
            .ok_or_else(|| self.error(format!("unknown predicate '{name}'")))?;
        if self.resolve(&f.return_type) != Type::Bool {
            return Err(self.error(format!("predicate '{name}' must return #bool")));
        }
        let summary = self.summaries.get(name).cloned().unwrap_or_default();
        if !summary.pure || summary.unknown_write {
            return Err(self.error(format!(
                "predicate '{name}' must be pure, with explicit stable read dependencies"
            )));
        }
        if xs.len() != f.parameters.len() + 1 {
            return Err(self.error(format!("predicate '{name}' has incorrect arity")));
        }
        let mut args = Vec::new();
        for (p, a) in f.parameters.iter().zip(&xs[1..]) {
            let mut v = self.spec_value(a, s)?;
            if matches!(
                a,
                Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_)
            ) {
                v.ty = p.ty.clone();
            }
            if !self.equivalent(&v.ty, &p.ty) {
                return Err(self.error(format!(
                    "predicate '{name}' argument '{}' has type {:?}, expected {:?}",
                    p.name, v.ty, p.ty
                )));
            }
            args.push(v);
        }
        let mut dependencies = Vec::new();
        for read in &summary.reads {
            for location in self.map_location(read, &f, &args, false, s) {
                self.charge(location_weight(&location))?;
                dependencies.push(location);
            }
        }
        if summary.unknown_read {
            dependencies.push(Location::root("unknown:heap"));
        }
        dependencies.sort();
        dependencies.dedup();
        let fact = Fact {
            key: format!(
                "{}({})",
                name,
                args.iter()
                    .map(|v| v.key.clone())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            dependencies,
            assumed,
            span: self.span,
            epoch: self.serial,
        };
        self.check_key(&fact.key)?;
        Ok(fact)
    }
    fn comparison_fact(
        &mut self,
        operator: &str,
        args: &[Value],
        assumed: bool,
        epoch: usize,
    ) -> Result<Fact, AnalysisError> {
        let mut dependencies = args
            .iter()
            .filter_map(|value| value.place.clone())
            .collect::<Vec<_>>();
        dependencies.sort();
        dependencies.dedup();
        let fact = Fact {
            key: format!(
                "builtin:{operator}({})",
                args.iter()
                    .map(|value| value.key.as_str())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            dependencies,
            assumed,
            span: self.span,
            epoch,
        };
        self.check_key(&fact.key)?;
        Ok(fact)
    }
    fn validate_spec(&self, e: &Expr) -> Result<(), AnalysisError> {
        if let Expr::List(xs) = e {
            let arity = if comparison_type(e).is_some() {
                Some(3)
            } else {
                match head(e) {
                    "borrow" | "borrow-mut" | "deref" | "clone" | "old" | "slice-len"
                    | "slice-mut-len" => Some(2),
                    "get" | "index" | "index-proven" | "slice-idx" | "slice-mut-idx" | "as"
                    | "literal" => Some(3),
                    "result" => Some(1),
                    _ => None,
                }
            };
            if arity.is_some_and(|arity| xs.len() != arity) {
                return Err(self.error(format!(
                    "incorrect argument count for #{} in specification",
                    head(e)
                )));
            }
            if head(e) == "result" && xs.len() != 1 {
                return Err(self.error("#result takes no operands"));
            }
            if let Some(Expr::Function(name)) = xs.first() {
                if self
                    .summaries
                    .get(name)
                    .is_none_or(|s| !s.pure || s.unknown_write)
                {
                    return Err(self.error(format!("specification calls impure function '{name}'")));
                }
            } else {
                let h = head(e);
                if !(h.contains('.')
                    || matches!(
                        h,
                        "literal"
                            | "borrow"
                            | "borrow-mut"
                            | "deref"
                            | "get"
                            | "index"
                            | "index-proven"
                            | "slice-idx"
                            | "slice-mut-idx"
                            | "slice-len"
                            | "slice-mut-len"
                            | "clone"
                            | "as"
                            | "old"
                            | "result"
                            | "ref"
                            | "ref-mut"
                            | "array"
                            | "tuple"
                            | ""
                    ))
                {
                    return Err(
                        self.error(format!("effectful or unsupported specification form '{h}'"))
                    );
                }
            }
            for x in xs.iter().skip(1) {
                self.validate_spec(x)?;
            }
        } else if matches!(
            e,
            Expr::Block(_)
                | Expr::Loop(_)
                | Expr::Labeled { .. }
                | Expr::Quote(_)
                | Expr::QuasiQuote(_)
                | Expr::Unquote(_)
                | Expr::UnquoteSplicing(_)
        ) {
            return Err(self.error("specification expressions must be pure observations"));
        }
        Ok(())
    }
    fn freeze_old(
        &mut self,
        e: &Expr,
        entry: &State,
        post: &mut State,
    ) -> Result<Expr, AnalysisError> {
        if head(e) == "old" {
            if parts(e).len() != 2 {
                return Err(self.error("#old requires one entry observation"));
            }
            let mut observed = self.snapshot(entry)?;
            let mut value = self.spec_value(&parts(e)[1], &mut observed)?;
            if !lowering::snapshot_type(&value.ty, self.program()) {
                return Err(self.error("#old requires a scalar entry observation; reference handles and aggregates are not snapshots"));
            }
            value.place = None;
            let name = self.fresh("__lim_contract_snapshot");
            post.values.insert(name.clone(), value);
            return Ok(symbol(&name));
        }
        match e {
            Expr::List(xs) => Ok(Expr::List(
                xs.iter()
                    .map(|x| self.freeze_old(x, entry, post))
                    .collect::<Result<Vec<_>, _>>()?
                    .into(),
            )),
            _ => Ok(e.clone()),
        }
    }
    fn spec_value(&mut self, e: &Expr, s: &mut State) -> Result<Value, AnalysisError> {
        self.spec_depth += 1;
        let result = self.spec_value_inner(e, s);
        self.spec_depth -= 1;
        let value = result?;
        self.check_value(&value)?;
        Ok(value)
    }
    fn spec_value_inner(&mut self, e: &Expr, s: &mut State) -> Result<Value, AnalysisError> {
        // Specification expressions are interpreted only as identities. Their
        // function bodies never execute in this checker or in an #assume.
        let xs = parts(e);
        if let Some(Expr::Function(name)) = xs.first() {
            let summary = self.summaries.get(name).cloned().unwrap_or_default();
            if !summary.pure || summary.unknown_write {
                return Err(self.error(format!(
                    "specification argument calls impure function '{name}'"
                )));
            }
            let f = self.program().contracts.originals[name].clone();
            if self
                .program()
                .contracts
                .clauses
                .get(name)
                .is_some_and(|c| !c.requires.is_empty())
            {
                return Err(self.error(
                    "specification observations must accept base inputs without requirements",
                ));
            }
            if xs.len() != f.parameters.len() + 1 {
                return Err(self.error("incorrect specification argument count"));
            }
            let mut args = xs[1..]
                .iter()
                .map(|a| self.spec_value(a, s))
                .collect::<Result<Vec<_>, _>>()?;
            for ((expression, parameter), value) in xs[1..].iter().zip(&f.parameters).zip(&mut args)
            {
                if matches!(
                    expression,
                    Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_)
                ) {
                    value.ty = parameter.ty.clone();
                }
            }
            for (p, a) in f.parameters.iter().zip(&args) {
                if !self.equivalent(&a.ty, &p.ty) {
                    return Err(self.error(format!("incorrect argument type for '{}'", p.name)));
                }
            }
            let mut v = Value::plain(
                self.pure_key(name, &f, &args, &summary, s)?,
                f.return_type.clone(),
            );
            if matches!(
                self.resolve(&v.ty),
                Type::Reference { .. } | Type::PinnedReference { .. }
            ) {
                for loc in &summary.returns {
                    v.targets.extend(self.map_location(loc, &f, &args, true, s));
                }
                if v.targets.len() != 1 {
                    v.key = self.fresh("spec-reference");
                }
            }
            return Ok(v);
        }
        match head(e) {
            "old" => {
                if xs.len() != 2 {
                    return Err(self.error("#old requires one observation"));
                }
                self.spec_value(&xs[1], s)
            }
            "result" => s
                .values
                .get("__lim_contract_result")
                .cloned()
                .ok_or_else(|| self.error("#result is only available in a postcondition")),
            "literal" | "borrow" | "borrow-mut" | "deref" | "get" | "index" | "index-proven"
            | "slice-idx" | "slice-mut-idx" | "slice-len" | "slice-mut-len" | "clone" | "as" => {
                self.eval_pure_builtin(e, s)
            }
            h if h.contains('.') => {
                let args = xs[1..]
                    .iter()
                    .map(|a| self.spec_value(a, s))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = self.expr_type(e, s)?;
                Ok(Value::plain(
                    format!(
                        "{h}({})",
                        args.iter()
                            .map(|v| v.key.clone())
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                    ty,
                ))
            }
            "" => self.eval(e, s),
            _ => Err(self.error("specification arguments must be pure observations")),
        }
    }
    fn eval_pure_builtin(&mut self, e: &Expr, s: &mut State) -> Result<Value, AnalysisError> {
        self.eval(e, s)
    }
    fn pure_key(
        &mut self,
        name: &str,
        f: &Function,
        args: &[Value],
        summary: &Summary,
        s: &State,
    ) -> Result<String, AnalysisError> {
        let mut deps = Vec::new();
        for read in &summary.reads {
            for location in self.map_location(read, f, args, false, s) {
                self.charge(location_weight(&location))?;
                deps.push(location);
            }
        }
        if summary.unknown_read {
            deps.push(Location::root("unknown:heap"));
        }
        let epoch = s
            .epochs
            .iter()
            .filter(|(place, _)| deps.iter().any(|d| Self::may_overlap(d, place)))
            .map(|(_, epoch)| *epoch)
            .max()
            .unwrap_or(0);
        let key = format!(
            "{}({}):{epoch}",
            name,
            args.iter()
                .map(|v| v.key.clone())
                .collect::<Vec<_>>()
                .join(",")
        );
        self.check_key(&key)?;
        Ok(key)
    }
    fn map_location(
        &mut self,
        loc: &Location,
        f: &Function,
        args: &[Value],
        returning: bool,
        s: &State,
    ) -> Vec<Location> {
        let Some(i) = f.parameters.iter().position(|p| p.name == loc.root) else {
            return Vec::new();
        };
        let Some(arg) = args.get(i) else {
            return Vec::new();
        };
        let mut roots = arg.targets.clone();
        if roots.is_empty() {
            if let Some(p) = &arg.place {
                roots.push(p.clone());
            }
        }
        for segment in &loc.path {
            if segment == "^" {
                roots = roots
                    .into_iter()
                    .flat_map(|root| {
                        s.cells
                            .get(&root)
                            .filter(|v| !v.targets.is_empty())
                            .map_or_else(|| vec![root.child("^")], |v| v.targets.clone())
                    })
                    .collect();
            } else {
                for root in &mut roots {
                    if let Some(param) =
                        segment.strip_prefix("[@").and_then(|s| s.strip_suffix(']'))
                    {
                        if let Some(i) = f.parameters.iter().position(|p| p.name == param) {
                            root.path.push(format!("[{}]", args[i].key));
                        } else {
                            root.path.push("*".into());
                        }
                    } else {
                        root.path.push(segment.clone());
                    }
                }
            }
            roots.sort();
            roots.dedup();
        }
        if returning {
            for root in &mut roots {
                if root.path.iter().any(|s| s == "*") {
                    root.root = self.fresh("unknown:return");
                    root.path.clear();
                }
            }
        }
        roots
    }
    fn call(
        &mut self,
        name: &str,
        expressions: &[Expr],
        s: &mut State,
        order: Option<&[usize]>,
    ) -> Result<Value, AnalysisError> {
        let f = self
            .program()
            .contracts
            .originals
            .get(name)
            .cloned()
            .ok_or_else(|| self.error(format!("missing function interface for '{name}'")))?;
        let validates = self.resolve(&f.return_type) == Type::Bool
            && self.summaries.get(name).is_some_and(|s| s.pure);
        if validates {
            self.validation_depth += 1;
        }
        let arguments = (|| {
            let mut values = vec![None; expressions.len()];
            for index in 0..expressions.len() {
                let index = order.map_or(index, |order| order[index]);
                values[index] =
                    Some(self.eval_expected(&expressions[index], &f.parameters[index].ty, s)?);
            }
            Ok::<_, AnalysisError>(values.into_iter().map(Option::unwrap).collect::<Vec<_>>())
        })();
        if validates {
            self.validation_depth -= 1;
        }
        let mut args = arguments?;
        for ((expression, parameter), value) in expressions.iter().zip(&f.parameters).zip(&mut args)
        {
            if matches!(
                expression,
                Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_)
            ) {
                value.ty = parameter.ty.clone();
            }
        }
        for argument in &mut args {
            self.materialize(argument, s)?;
        }
        let clauses = self
            .program()
            .contracts
            .clauses
            .get(name)
            .cloned()
            .unwrap_or_default();
        let mut interface = self.snapshot(s)?;
        for (param, arg) in f.parameters.iter().zip(&args) {
            interface.values.insert(param.name.clone(), arg.clone());
        }
        let requirements = self.program().contracts.effective_requires[name].clone();
        for &node in &requirements.order {
            let fact = self.predicate(&requirements.nodes[node].expression, &mut interface, false)?;
            if let Err(mut error) = self.require(s, &fact) {
                let call = Expr::List(
                    std::iter::once(Expr::Function(name.into()))
                        .chain(expressions.iter().cloned())
                        .collect::<Vec<_>>()
                        .into(),
                );
                error.2 = super::prerequisites::call_span(
                    self.program(), &self.function, self.span, &call,
                ).or(error.2);
                error.0.push_str(&format!(
                    "; call '{name}' -> root requirement -> prerequisite -> missing fact"
                ));
                error.3.extend(requirements.trace(node));
                return Err(error);
            }
        }
        let entry = self.snapshot(&interface)?;
        let mut preserved = Vec::new();
        for p in &clauses.preserves {
            let fact = self.predicate(p, &mut interface, false)?;
            if s.facts.iter().any(|f| f.key == fact.key) {
                preserved.push(p.clone());
            }
        }
        for argument in &args {
            self.consume_owner(argument, s);
        }
        let summary = self.summaries.get(name).cloned().unwrap_or_default();
        let writes = summary
            .writes
            .iter()
            .flat_map(|loc| self.map_location(loc, &f, &args, false, s))
            .collect::<Vec<_>>();
        self.invalidate(s, &writes, summary.unknown_write);
        self.serial += 1;
        let mut result = self.unknown(f.return_type.clone());
        if matches!(
            self.resolve(&f.return_type),
            Type::Reference { .. }
                | Type::PinnedReference { .. }
                | Type::Slice(_)
                | Type::MutableSlice(_)
        ) {
            result.targets.clear();
            for loc in &summary.returns {
                result
                    .targets
                    .extend(self.map_location(loc, &f, &args, true, s));
            }
            result.targets.sort();
            result.targets.dedup();
            if result.targets.is_empty() {
                result
                    .targets
                    .push(Location::root(self.fresh("unknown:return")));
            }
            if result.targets.len() == 1 {
                result.key = format!("&{:?}", result.targets);
            }
        } else if summary.pure {
            result.key = self.pure_key(name, &f, &args, &summary, s)?;
        }
        self.materialize(&mut result, s)?;
        interface.cells = s.cells.clone();
        interface.facts = s.facts.clone();
        interface.epochs = s.epochs.clone();
        interface
            .values
            .insert("__lim_contract_result".into(), result.clone());
        let lends_mutably = matches!(
            self.resolve(&f.return_type),
            Type::Reference { mutable: true, .. }
                | Type::PinnedReference { mutable: true, .. }
                | Type::MutableSlice(_)
        );
        for p in clauses.ensures.iter().chain(preserved.iter()) {
            let predicate = self.freeze_old(p, &entry, &mut interface)?;
            let fact = self.predicate(&predicate, &mut interface, true)?;
            self.add(s, fact)?;
        }
        // These are checked type guarantees, rather than explicit promises.
        // Export the same closure that result/restoration checking requires.
        for p in clauses.restores.iter().filter(|_| !lends_mutably)
            .chain(&clauses.result_constraints)
        {
            let predicate = self.freeze_old(p, &entry, &mut interface)?;
            for mut fact in self.constraint_facts(&predicate, &mut interface)? {
                fact.assumed = true;
                self.add(s, fact)?;
            }
        }
        for (place, value) in interface.cells {
            s.cells.entry(place).or_insert(value);
        }
        if self.resolve(&f.return_type) == Type::Bool && summary.pure {
            let mut evidence_state = self.snapshot(s)?;
            for (param, arg) in f.parameters.iter().zip(&args) {
                evidence_state
                    .values
                    .insert(param.name.clone(), arg.clone());
            }
            let predicate = Expr::List(
                std::iter::once(Expr::Function(name.into()))
                    .chain(f.parameters.iter().map(|p| symbol(&p.name)))
                    .collect::<Vec<_>>()
                    .into(),
            );
            // The call has checked its prerequisites. Only #if-valid consumes
            // this truth evidence, after the actual predicate succeeds.
            result
                .truth
                .push(self.predicate(&predicate, &mut evidence_state, false)?);
        }
        Ok(result)
    }
    fn eval(&mut self, e: &Expr, s: &mut State) -> Result<Value, AnalysisError> {
        let value = self.eval_inner(e, s)?;
        self.check_value(&value)?;
        Ok(value)
    }
    fn eval_expected(
        &mut self,
        expression: &Expr,
        expected: &Type,
        s: &mut State,
    ) -> Result<Value, AnalysisError> {
        if head(expression) == "array" {
            if let Type::Array(element, length) = self.resolve(expected) {
                self.tick()?;
                let parts = parts(expression);
                let explicit = crate::parse_type(parts.get(1))
                    .ok()
                    .is_some_and(|ty| self.resolve(&ty) == Type::Array(element.clone(), length));
                let mut value = self.unknown(expected.clone());
                for (index, expression) in
                    parts.iter().skip(if explicit { 2 } else { 1 }).enumerate()
                {
                    value.fields.insert(
                        format!("[{index}]"),
                        self.eval_expected(expression, &element, s)?,
                    );
                }
                self.check_value(&value)?;
                return Ok(value);
            }
        }
        self.eval(expression, s)
    }
    fn eval_inner(&mut self, e: &Expr, s: &mut State) -> Result<Value, AnalysisError> {
        self.tick()?;
        match e {
            Expr::Symbol(name) => {
                if let Some(value) = s.values.get(name).cloned() {
                    if self.spec_depth == 0 && !s.loans.contains_key(name) {
                        let places = if value.targets.is_empty() {
                            value.place.clone().into_iter().collect::<Vec<_>>()
                        } else {
                            value.targets.clone()
                        };
                        let ended = s
                            .loans
                            .iter()
                            .filter(|(_, loan)| {
                                loan.places
                                    .iter()
                                    .any(|p| places.iter().any(|q| Self::may_overlap(p, q)))
                            })
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>();
                        let closed = !ended.is_empty();
                        for loan in ended {
                            self.end_loan(s, &loan)?;
                        }
                        let exclusive_parameter = self
                            .program()
                            .contracts
                            .originals
                            .get(&self.function)
                            .is_some_and(|f| {
                                f.parameters.iter().any(|p| {
                                    p.name == *name
                                        && matches!(
                                            self.resolve(&p.ty),
                                            Type::Reference { mutable: true, .. }
                                                | Type::PinnedReference { mutable: true, .. }
                                                | Type::MutableSlice(_)
                                        )
                                })
                            });
                        if self.validation_depth == 0
                            && (closed || !exclusive_parameter)
                            && s.fixed
                                .iter()
                                .any(|(_, root)| places.iter().any(|q| Self::may_overlap(root, q)))
                        {
                            self.restore(s, &places)?;
                        }
                    }
                    if value.targets.is_empty() {
                        if let Some(place) = &value.place {
                            return Ok(self.read(s, place, value.ty.clone()));
                        }
                    }
                    return Ok(value);
                }
                if matches!(name.as_str(), "true" | "false") {
                    return Ok(Value::plain(name.clone(), Type::Bool));
                }
                if let Some(ty) = self.checked.declarations().globals.get(name).cloned() {
                    let mut v = Value::plain(format!("global:{name}"), ty);
                    v.place = Some(Location::root(format!("global:{name}")));
                    return Ok(v);
                }
                if let Some(owner) =
                    self.checked
                        .declarations()
                        .enums
                        .iter()
                        .find_map(|(owner, variants)| {
                            variants
                                .iter()
                                .any(|v| v.name == *name && v.fields.is_empty())
                                .then_some(owner.clone())
                        })
                {
                    return Ok(Value::plain(name.clone(), Type::Named(owner)));
                }
                return Err(self.error(format!("unknown contract value '{name}'")));
            }
            Expr::Integer(n) => return Ok(Value::plain(n.to_string(), Type::I64)),
            Expr::UnsignedInteger(n) => return Ok(Value::plain(n.to_string(), Type::U64)),
            Expr::Float(n) => return Ok(Value::plain(format!("float:{n}"), Type::F64)),
            Expr::Char(c) => return Ok(Value::plain(format!("{c:?}"), Type::Char)),
            Expr::String(text) => {
                return Ok(Value::plain(
                    format!("{text:?}"),
                    Type::Array(Box::new(Type::Char), text.chars().count()),
                ))
            }
            Expr::Block(body) => return self.statements(body, s, false),
            Expr::Loop(body) => {
                self.loop_body(body, s)?;
                return Ok(self.unknown(Type::Unit));
            }
            Expr::Labeled { expression, .. } => return self.eval(expression, s),
            _ => {}
        }
        let xs = parts(e);
        if xs.is_empty() {
            return Ok(Value::plain("()".into(), Type::Unit));
        }
        if let Some(Expr::Function(f)) = xs.first() {
            if self.spec_depth > 0 {
                return self.spec_value_inner(e, s);
            }
            return self.call(
                f,
                &xs[1..],
                s,
                match e {
                    Expr::List(items) => items.argument_order(),
                    _ => None,
                },
            );
        }
        let h = head(e);
        if comparison_type(e).is_some() {
            let epoch = self.serial;
            let order = match e {
                Expr::List(items) => items.argument_indices().collect::<Vec<_>>(),
                _ => Vec::new(),
            };
            let mut args = vec![None; xs.len() - 1];
            for index in order {
                args[index] = Some(self.eval(&xs[index + 1], s)?);
            }
            let args = args.into_iter().map(Option::unwrap).collect::<Vec<_>>();
            let fact = self.comparison_fact(h, &args, false, epoch)?;
            let mut value = Value::plain(fact.key.clone(), Type::Bool);
            value.truth.push(fact);
            return Ok(value);
        }
        if let Some(fields) = self.checked.declarations().structs.get(h).cloned() {
            let mut value = self.unknown(Type::Named(h.into()));
            let order = match e {
                Expr::List(items) => items.argument_indices().collect::<Vec<_>>(),
                _ => Vec::new(),
            };
            for index in order {
                let field = &fields[index];
                let argument = &xs[index + 1];
                value
                    .fields
                    .insert(format!(".{}", field.name), self.eval(argument, s)?);
            }
            return Ok(value);
        }
        if let Some((name, variant)) =
            self.checked
                .declarations()
                .enums
                .iter()
                .find_map(|(name, variants)| {
                    variants
                        .iter()
                        .find(|v| v.name == h)
                        .map(|v| (name.clone(), v.clone()))
                })
        {
            let mut value = self.unknown(Type::Named(name));
            for (i, argument) in xs[1..].iter().enumerate() {
                value
                    .fields
                    .insert(format!(".{}.{}", variant.name, i), self.eval(argument, s)?);
            }
            return Ok(value);
        }
        match h {
            "requires" | "ensures" | "preserves" => Ok(Value::plain("()".into(), Type::Unit)),
            "assume" => {
                if xs.len() != 2 {
                    return Err(
                        self.error("#assume requires one predicate or explicit conjunction")
                    );
                }
                if super::contains_form(&xs[1], "old") || super::contains_form(&xs[1], "result") {
                    return Err(self.error("#old and #result are only available in #ensures"));
                }
                for p in split_and(&xs[1]) {
                    let fact = self.predicate(&p, s, true)?;
                    self.add(s, fact)?;
                }
                Ok(Value::plain("()".into(), Type::Unit))
            }
            "if" | "if-valid" => {
                if !matches!(xs.len(), 3 | 4) {
                    return Err(self.error("conditional requires a condition, success branch and optional failure branch"));
                }
                if h == "if-valid" {
                    self.validation_depth += 1;
                }
                let condition = self.eval(&xs[1], s);
                if h == "if-valid" {
                    self.validation_depth -= 1;
                }
                let condition = condition?;
                let mut yes = self.snapshot(s)?;
                let mut no = self.snapshot(s)?;
                if h == "if-valid" {
                    for fact in condition.truth {
                        self.add(&mut yes, fact)?;
                    }
                }
                let y = self.eval(&xs[2], &mut yes)?;
                let n = if let Some(e) = xs.get(3) {
                    self.eval(e, &mut no)?
                } else {
                    Value::plain("()".into(), Type::Unit)
                };
                if condition.key == "true" {
                    *s = yes;
                    return Ok(y);
                }
                if condition.key == "false" {
                    *s = no;
                    return Ok(n);
                }
                *s = self.join(yes, no);
                if y.key == n.key {
                    Ok(y)
                } else {
                    Ok(self.unknown(y.ty))
                }
            }
            "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" => {
                if xs.len() > 2 {
                    let places = self.places(&xs[1], s)?;
                    let mutable = h.contains("mut");
                    if mutable {
                        self.invalidate(s, &places, false)
                    }
                    let result = self.eval(&xs[2], s)?;
                    if mutable {
                        self.restore(s, &places)?;
                    }
                    return Ok(result);
                }
                let places = self.places(&xs[1], s)?;
                let target = self.expr_type(&xs[1], s)?;
                // An immediate call transfers evidence with the exclusive borrow. A
                // stored/returned unrestricted loan suspends it at that boundary.
                Ok(self.reference(
                    places,
                    Type::Reference {
                        mutable: h.contains("mut"),
                        target: Box::new(target),
                    },
                    None,
                ))
            }
            "literal" => {
                if xs.len() != 3 {
                    return Err(self.error("a typed literal needs its type and value"));
                }
                let mut value = self.eval(&xs[2], s)?;
                value.ty = crate::parse_type(xs.get(1)).map_err(|e| self.error(e))?;
                Ok(value)
            }
            "clone" => {
                let ty = self.expr_type(&xs[1], s)?;
                if let Type::Named(owner) = self.resolve(&ty) {
                    let hook = format!("{owner}::clone");
                    if self.program().contracts.originals.contains_key(&hook) {
                        if self.spec_depth > 0 {
                            let expression = Expr::List(
                                std::iter::once(Expr::Function(hook))
                                    .chain(xs[1..].iter().cloned())
                                    .collect::<Vec<_>>()
                                    .into(),
                            );
                            return self.spec_value_inner(&expression, s);
                        }
                        return self.call(&hook, &xs[1..], s, None);
                    }
                }
                self.eval(&xs[1], s)
            }
            "deref" | "get" | "index" | "index-proven" | "slice-idx" | "slice-mut-idx" => {
                let places = self.places(e, s)?;
                let ty = self.expr_type(e, s)?;
                if places.len() == 1 {
                    Ok(self.read(s, &places[0], ty))
                } else {
                    Ok(self.unknown(ty))
                }
            }
            "as" => {
                let mut v = self.eval(&xs[1], s)?;
                let ty = crate::parse_type(xs.get(2)).map_err(|e| self.error(e))?;
                if self.resolve(&v.ty) != self.resolve(&ty) {
                    v.key = format!("as:{ty:?}({})", v.key);
                    v.place = None;
                    v.truth.clear();
                    v.fields.clear();
                    v.targets.clear();
                }
                v.ty = ty;
                Ok(v)
            }
            "deref-set" => {
                let target = self.eval(&xs[1], s)?;
                let value = self.eval(&xs[2], s)?;
                for place in target.targets {
                    self.store(s, &place, &value, true)?;
                }
                Ok(Value::plain("()".into(), Type::Unit))
            }
            "struct-literal" | "struct" => {
                let ty = crate::parse_type(xs.get(1)).map_err(|e| self.error(e))?;
                let mut v = self.unknown(ty);
                if let Some(Expr::List(fields)) = xs.get(2) {
                    for field in fields.iter() {
                        let pair = parts(field);
                        if let (Some(Expr::Symbol(name)), Some(value)) = (pair.first(), pair.get(1))
                        {
                            v.fields.insert(format!(".{name}"), self.eval(value, s)?);
                        }
                    }
                }
                Ok(v)
            }
            "tuple" => {
                let ty = crate::parse_type(xs.get(1)).map_err(|e| self.error(e))?;
                let mut v = self.unknown(ty);
                for (i, e) in xs.iter().skip(2).enumerate() {
                    v.fields.insert(format!(".{i}"), self.eval(e, s)?);
                }
                Ok(v)
            }
            "array" => {
                let ty = self.expr_type(e, s)?;
                let mut v = self.unknown(ty);
                for (i, e) in xs.iter().skip(2).enumerate() {
                    v.fields.insert(format!("[{i}]"), self.eval(e, s)?);
                }
                Ok(v)
            }
            "bool.&&" | "&&" => {
                let mut out = Value::plain(self.fresh("and"), Type::Bool);
                let order = match e {
                    Expr::List(items) => items.argument_indices().collect::<Vec<_>>(),
                    _ => (0..xs.len().saturating_sub(1)).collect(),
                };
                for index in order {
                    let e = &xs[index + 1];
                    out.truth.extend(self.eval(e, s)?.truth);
                }
                Ok(out)
            }
            "bool.||" | "||" => {
                for e in &xs[1..] {
                    self.eval(e, s)?;
                }
                Ok(self.unknown(Type::Bool))
            }
            "old" | "result" => {
                if self.spec_depth > 0 {
                    return self.spec_value_inner(e, s);
                }
                Err(self.error("#old and #result are restricted to postconditions"))
            }
            "forget" | "drop" => {
                let value = self.eval(&xs[1], s)?;
                if let Some(place) = value.place {
                    s.fixed.retain(|(_, root)| !root.overlaps(&place));
                }
                Ok(Value::plain("()".into(), Type::Unit))
            }
            "panic" | "unreachable" => {
                s.dead = true;
                Ok(self.unknown(Type::Never))
            }
            "match" => {
                self.eval(&xs[1], s)?;
                let mut branches = Vec::new();
                for arm in &xs[2..] {
                    let arm = parts(arm);
                    let mut branch = self.snapshot(s)?;
                    // Typed pattern binding is supplied below for constructor payloads.
                    self.bind_pattern(arm.first(), &xs[1], &mut branch)?;
                    for e in arm.iter().skip(1) {
                        self.eval(e, &mut branch)?;
                    }
                    branches.push(branch);
                }
                if let Some(first) = branches.into_iter().reduce(|a, b| self.join(a, b)) {
                    *s = first;
                }
                Ok(self.unknown(Type::Unit))
            }
            "unsafe" => {
                self.invalidate(s, &[], true);
                for e in &xs[1..] {
                    self.eval(e, s)?;
                }
                Ok(self.unknown(self.expr_type(e, s).unwrap_or(Type::Unit)))
            }
            _ => {
                // Ordinary primitives are already type/ownership checked.
                // Conservatively forget heap evidence around unmodelled mutation.
                if !super::summaries::observational(h) {
                    self.invalidate(s, &[], true);
                }
                let mut keys = BTreeMap::new();
                let order = match e {
                    Expr::List(items) => items.argument_indices().collect::<Vec<_>>(),
                    _ => Vec::new(),
                };
                for index in order {
                    let e = &xs[index + 1];
                    if matches!(e,Expr::Symbol(n)if !s.values.contains_key(n)&&!matches!(n.as_str(),"true"|"false"))
                    {
                        continue;
                    }
                    if matches!(e,Expr::List(p)if p.is_empty()) {
                        continue;
                    }
                    let v = self.eval(e, s)?;
                    keys.insert(index, v.key);
                }
                let keys = keys.into_values().collect::<Vec<_>>();
                let ty = self.expr_type(e, s).unwrap_or(Type::Unit);
                if matches!(
                    self.resolve(&ty),
                    Type::Reference { .. }
                        | Type::PinnedReference { .. }
                        | Type::Slice(_)
                        | Type::MutableSlice(_)
                ) {
                    Ok(self.unknown(ty))
                } else {
                    Ok(Value::plain(format!("{h}({})", keys.join(",")), ty))
                }
            }
        }
    }
    fn bind_pattern(
        &mut self,
        pattern: Option<&Expr>,
        value: &Expr,
        s: &mut State,
    ) -> Result<(), AnalysisError> {
        let Some(pattern) = pattern else {
            return Ok(());
        };
        let ty = self.expr_type(value, s).unwrap_or(Type::Unit);
        if let Expr::Symbol(name) = pattern {
            if name != "_"
                && !self
                    .checked
                    .declarations()
                    .enums
                    .values()
                    .flatten()
                    .any(|v| &v.name == name)
            {
                let v = self.unknown(ty);
                s.values.insert(name.clone(), v);
            }
            return Ok(());
        }
        let xs = parts(pattern);
        if let Some(Expr::Symbol(variant)) = xs.first() {
            if let Some(fields) = self
                .checked
                .declarations()
                .enums
                .values()
                .flatten()
                .find(|v| &v.name == variant)
                .map(|v| v.fields.clone())
            {
                for (p, t) in xs[1..].iter().zip(fields) {
                    if let Expr::Symbol(name) = p {
                        let v = self.unknown(t);
                        s.values.insert(name.clone(), v);
                    }
                }
            }
        }
        Ok(())
    }
    fn bind(
        &mut self,
        name: &str,
        ty: &Type,
        mut value: Value,
        s: &mut State,
    ) -> Result<(), AnalysisError> {
        value.ty = ty.clone();
        let place = Location::root(self.fresh(&format!("local:{name}")));
        // Moving a checked value preserves its semantic facts. Reference aliases
        // retain their referent identity; they never acquire a new proof subject.
        self.store(s, &place, &value, false)?;
        let mut value = value;
        value.place = Some(place.clone());
        value.ty = ty.clone();
        s.values.insert(name.into(), value);
        let mut fixed_evidence = HashSet::new();
        for predicate in lowering::predicates_for(ty, &symbol(name), self.program())
            .map_err(|e| self.error(e))?
        {
            for fact in self.require_constraint(&predicate, s)? {
                fixed_evidence.insert(fact.key);
            }
            let root = s.values[name]
                .targets
                .first()
                .cloned()
                .unwrap_or_else(|| place.clone());
            s.fixed.push((predicate, root));
        }
        let value = s.values[name].clone();
        if matches!(
            self.resolve(ty),
            Type::Reference { mutable: true, .. }
                | Type::PinnedReference { mutable: true, .. }
                | Type::MutableSlice(_)
        ) {
            let facts = s
                .facts
                .iter()
                .filter(|f| {
                    f.dependencies
                        .iter()
                        .any(|d| value.targets.iter().any(|p| Self::may_overlap(d, p)))
                })
                .cloned()
                .collect::<Vec<_>>();
            s.facts.retain(|f| {
                fixed_evidence.contains(&f.key) || !facts.iter().any(|g| g.key == f.key)
            });
            s.loans.insert(
                name.into(),
                Loan {
                    places: value.targets.clone(),
                    facts,
                },
            );
        }
        Ok(())
    }
    fn relocate(
        &mut self,
        s: &mut State,
        from: &Location,
        to: &Location,
    ) -> Result<(), AnalysisError> {
        if from == to {
            return Ok(());
        }

        self.charge(s.facts.iter().map(fact_weight).sum())?;
        for mut fact in s.facts.clone() {
            let previous = fact.clone();
            fact.key = relocated_key(&fact.key, from, to);
            for dep in &mut fact.dependencies {
                if dep.root == from.root && dep.path.starts_with(&from.path) {
                    let tail = dep.path[from.path.len()..].to_vec();
                    *dep = to.clone();
                    dep.path.extend(tail);
                }
            }
            if fact != previous {
                fact.epoch = self.serial;
                self.add(s, fact)?;
            }
        }
        Ok(())
    }
    fn end_loan(&mut self, s: &mut State, name: &str) -> Result<(), AnalysisError> {
        let Some(loan) = s.loans.remove(name) else {
            return Ok(());
        };
        for fact in loan.facts {
            if self.current(s, &fact) {
                self.add(s, fact)?;
            }
        }
        // The owner remains unavailable until its fixed predicates hold. A
        // subsequent validator or assumption can close that obligation after
        // the element reference's physical lifetime has ended.
        Ok(())
    }
    fn restore(&mut self, s: &mut State, places: &[Location]) -> Result<(), AnalysisError> {
        for (predicate, root) in s.fixed.clone() {
            if places.is_empty() || places.iter().any(|p| Self::may_overlap(p, &root)) {
                self.require_constraint(&predicate, s).map_err(|mut error| {
                    error.0.push_str("; fixed storage invariant must be restored before its owner is available again");
                    error
                })?;
            }
        }
        Ok(())
    }
    fn statements(
        &mut self,
        body: &[Statement],
        s: &mut State,
        top: bool,
    ) -> Result<Value, AnalysisError> {
        let old_names = s.values.keys().cloned().collect::<HashSet<_>>();
        let mut result = Value::plain("()".into(), Type::Unit);
        for (index, statement) in body.iter().enumerate() {
            if s.dead {
                break;
            }
            if top {
                self.span = self
                    .program()
                    .statement_spans
                    .get(&(self.function.clone(), index))
                    .copied()
                    .or_else(|| {
                        self.program()
                            .declaration_spans
                            .get(&self.function)
                            .copied()
                    });
            }
            result = self.statement(statement, s)?;
            // End local reference loans at their last use. Fixed owner obligations
            // survive aliases and are checked before access can be returned.
            let remaining = format!("{:?}", &body[index + 1..]);
            let used = |name: &str| {
                remaining.contains(&format!("Symbol({name:?})"))
                    || remaining.contains(&format!("name: {name:?}"))
            };
            let mut active = s
                .values
                .iter()
                .filter(|(name, v)| !v.targets.is_empty() && used(name))
                .flat_map(|(_, v)| v.targets.clone())
                .collect::<Vec<_>>();
            active.extend(result.targets.iter().cloned());
            let ended = s
                .loans
                .iter()
                .filter(|(name, loan)| {
                    !used(name)
                        && !loan
                            .places
                            .iter()
                            .any(|p| active.iter().any(|q| Self::may_overlap(p, q)))
                })
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>();
            for name in ended {
                self.end_loan(s, &name)?;
            }
        }
        if !top {
            let local_roots = s
                .values
                .iter()
                .filter(|(name, _)| !old_names.contains(*name))
                .filter_map(|(_, v)| v.place.clone())
                .collect::<Vec<_>>();
            if !s.dead {
                self.restore(s, &local_roots)?;
            }
            s.fixed
                .retain(|(_, root)| !local_roots.iter().any(|p| p.root == root.root));
            s.values.retain(|name, _| old_names.contains(name));
        }
        Ok(result)
    }
    fn statement(&mut self, statement: &Statement, s: &mut State) -> Result<Value, AnalysisError> {
        self.tick()?;
        match statement {
            Statement::Let {
                name,
                ty,
                value,
                mutable,
            } => {
                if *mutable {
                    s.mutable_bindings.insert(name.clone());
                }
                let value = self.eval_expected(value, ty, s)?;
                self.bind(name, ty, value, s)?;
            }
            Statement::Assign { name, value } => {
                let Some(old) = s.values.get(name).cloned() else {
                    return Err(self.error("assignment to missing contract binding"));
                };
                let value = self.eval_expected(value, &old.ty, s)?;
                if let Some(place) = &old.place {
                    self.store(s, place, &value, true)?;
                }
                let mut value = value;
                value.place = old.place;
                value.ty = old.ty;
                s.values.insert(name.clone(), value);
            }
            Statement::ArrayAssign { name, index, value } => {
                let target = form("index", [symbol(name), index.clone()]);
                let places = self.places(&target, s)?;
                let value = self.eval(value, s)?;
                for place in places {
                    self.store(s, &place, &value, true)?;
                }
            }
            Statement::FieldAssign { name, field, value } => {
                let places = self.places(&form("get", [symbol(name), symbol(field)]), s)?;
                let value = self.eval(value, s)?;
                for place in places {
                    self.store(s, &place, &value, true)?;
                }
            }
            Statement::TupleAssign { name, index, value } => {
                let places = self.places(
                    &form("get", [symbol(name), Expr::Integer(*index as i128)]),
                    s,
                )?;
                let value = self.eval(value, s)?;
                for place in places {
                    self.store(s, &place, &value, true)?;
                }
            }
            Statement::EnumPayloadAssign { name, value, .. } => {
                self.eval(value, s)?;
                let places = self.places(&symbol(name), s)?;
                self.invalidate(s, &places, false);
            }
            Statement::Expr(e) => return self.eval(e, s),
            Statement::Return(value) => {
                let expected = self.program().contracts.originals[&self.function]
                    .return_type
                    .clone();
                let mut value = if let Some(e) = value {
                    self.eval_expected(e, &expected, s)?
                } else {
                    Value::plain("()".into(), Type::Unit)
                };
                if let Some(function) = self.program().contracts.originals.get(&self.function) {
                    value.ty = function.return_type.clone();
                }
                self.materialize(&mut value, s)?;
                s.values
                    .insert("__lim_contract_result".into(), value.clone());
                // Explicit postconditions are programmer promises in this system.
                let clauses = self
                    .program()
                    .contracts
                    .clauses
                    .get(&self.function)
                    .cloned()
                    .unwrap_or_default();
                let mut promises = clauses.ensures.clone();
                let mut entry = self.entry_snapshot()?;
                for p in &clauses.preserves {
                    let fact = self.predicate(p, &mut entry, false)?;
                    if entry.facts.iter().any(|f| f.key == fact.key) {
                        promises.push(p.clone());
                    }
                }
                for p in &promises {
                    let predicate = self.freeze_old(p, &entry, s)?;
                    let fact = self.predicate(&predicate, s, true)?;
                    self.add(s, fact)?;
                }
                for p in &clauses.result_constraints {
                    self.require_constraint(p, s)?;
                }
                self.consume_owner(&value, s);
                if !matches!(
                    self.resolve(&value.ty),
                    Type::Reference { mutable: true, .. }
                        | Type::PinnedReference { mutable: true, .. }
                        | Type::MutableSlice(_)
                ) {
                    self.restore(s, &[])?;
                } else {
                    let retained = s.fixed.clone();
                    s.fixed.retain(|(_, root)| {
                        !value.targets.iter().any(|p| Self::may_overlap(p, root))
                    });
                    self.restore(s, &[])?;
                    s.fixed = retained;
                }
                s.dead = true;
                return Ok(value);
            }
            Statement::While { condition, body } => {
                self.eval(condition, s)?;
                let mut iteration = vec![Statement::Expr(condition.clone())];
                iteration.extend(body.clone());
                self.loop_body(&iteration, s)?;
            }
            Statement::Loop { body } => {
                self.loop_body(body, s)?;
            }
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                self.statement(init, s)?;
                self.eval(condition, s)?;
                let mut iteration = vec![Statement::Expr(condition.clone())];
                iteration.extend(body.clone());
                iteration.push((**step).clone());
                self.loop_body(&iteration, s)?;
            }
            Statement::Labeled { statement, .. } => return self.statement(statement, s),
            Statement::LetElse {
                pattern,
                value,
                else_body,
                ..
            } => {
                self.eval(value, s)?;
                let mut failed = self.snapshot(s)?;
                self.statements(else_body, &mut failed, false)?;
                self.bind_pattern(Some(pattern), value, s)?;
            }
            Statement::Destructure {
                pattern, ty, value, ..
            } => {
                let value = self.eval(value, s)?;
                fn names(p: &Expr, out: &mut Vec<String>) {
                    match p {
                        Expr::Symbol(n) if n != "_" => out.push(n.clone()),
                        Expr::List(xs) => {
                            for p in xs.iter().skip(1) {
                                names(p, out)
                            }
                        }
                        _ => {}
                    }
                }
                let mut bound = Vec::new();
                names(pattern, &mut bound);
                let fields = match self.resolve(ty) {
                    Type::Tuple(fields) => fields,
                    _ => Vec::new(),
                };
                for (i, name) in bound.iter().enumerate() {
                    let ty = fields.get(i).cloned().unwrap_or(Type::Unit);
                    let val = value
                        .fields
                        .get(&format!(".{i}"))
                        .cloned()
                        .unwrap_or_else(|| self.unknown(ty.clone()));
                    self.bind(name, &ty, val, s)?;
                }
            }
            Statement::Break
            | Statement::BreakTo(_)
            | Statement::Continue
            | Statement::ContinueTo(_) => {
                s.dead = true;
            }
            Statement::BreakValue(v) | Statement::BreakToValue { value: v, .. } => {
                self.eval(v, s)?;
                s.dead = true;
            }
        }
        Ok(Value::plain("()".into(), Type::Unit))
    }
    fn join(&mut self, mut a: State, b: State) -> State {
        if a.dead {
            return b;
        }
        if b.dead {
            return a;
        }
        a.facts
            .retain(|f| b.facts.iter().any(|other| other.key == f.key));
        for fact in &mut a.facts {
            if let Some(other) = b.facts.iter().find(|g| g.key == fact.key) {
                fact.dependencies.extend(other.dependencies.clone());
                fact.dependencies.sort();
                fact.dependencies.dedup();
                fact.assumed |= other.assumed;
                fact.epoch = self.serial;
            }
        }
        for (name, value) in &mut a.values {
            if let Some(other) = b.values.get(name) {
                if value.key != other.key {
                    value.key = self.fresh("join");
                    value.truth.clear();
                }
                value.targets.extend(other.targets.iter().cloned());
                value.targets.sort();
                value.targets.dedup();
            }
        }
        a.values.retain(|n, _| b.values.contains_key(n));
        a.cells
            .retain(|p, v| b.cells.get(p).is_some_and(|other| other.key == v.key));
        a.invalidated.extend(b.invalidated);
        a.mutable_bindings.extend(b.mutable_bindings);
        for (place, epoch) in b.epochs {
            a.epochs
                .entry(place)
                .and_modify(|old| *old = (*old).max(epoch))
                .or_insert(epoch);
        }
        a
    }
    fn loop_body(&mut self, body: &[Statement], s: &mut State) -> Result<(), AnalysisError> {
        // Compute a conservative loop entry. Loops never gain facts from a
        // single iteration or from the zero-iteration path.
        let effects =
            super::summaries::local_effects(body, &self.types(s), self.program(), &self.summaries);
        let mut assignments = false;
        super::visit_body(body, &mut |_| {}, &mut |statement| {
            assignments |= matches!(
                statement,
                Statement::Assign { .. }
                    | Statement::ArrayAssign { .. }
                    | Statement::FieldAssign { .. }
                    | Statement::TupleAssign { .. }
                    | Statement::EnumPayloadAssign { .. }
            )
        });
        let may_mutate = effects.unknown_write || !effects.writes.is_empty() || assignments;
        if may_mutate {
            self.invalidate(s, &[], true);
            for value in s.values.values_mut() {
                value.truth.clear();
                if value.targets.is_empty() {
                    value.key = self.fresh("loop");
                } else {
                    value
                        .targets
                        .push(Location::root(self.fresh("unknown:loop")));
                    value.key = self.fresh("loop-reference");
                }
            }
        }
        let mut iteration = self.snapshot(s)?;
        self.statements(body, &mut iteration, false)?;
        // Even an infinite loop may contain breaks. Preserve only entry facts;
        // mutations have already been accounted for conservatively.
        Ok(())
    }
}

fn location_weight(location: &Location) -> usize {
    64 + location.root.len() + location.path.iter().map(|p| 24 + p.len()).sum::<usize>()
}
fn fact_weight(fact: &Fact) -> usize {
    96 + fact.key.len() + fact.dependencies.iter().map(location_weight).sum::<usize>()
}
fn value_weight(value: &Value) -> usize {
    128 + value.key.len()
        + match &value.ty {
            Type::Named(name) | Type::Generic(name) => name.len(),
            _ => 0,
        }
        + value.place.as_ref().map_or(0, location_weight)
        + value.targets.iter().map(location_weight).sum::<usize>()
        + value
            .fields
            .iter()
            .map(|(name, value)| name.len() + value_weight(value))
            .sum::<usize>()
        + value.truth.iter().map(fact_weight).sum::<usize>()
}
fn state_weight(state: &State) -> usize {
    state
        .values
        .iter()
        .map(|(name, value)| name.len() + value_weight(value))
        .sum::<usize>()
        + state
            .cells
            .iter()
            .map(|(place, value)| location_weight(place) + value_weight(value))
            .sum::<usize>()
        + state.facts.iter().map(fact_weight).sum::<usize>()
        + state
            .fixed
            .iter()
            .map(|(_, place)| 64 + location_weight(place))
            .sum::<usize>()
        + state
            .loans
            .values()
            .map(|loan| {
                loan.places.iter().map(location_weight).sum::<usize>()
                    + loan.facts.iter().map(fact_weight).sum::<usize>()
            })
            .sum::<usize>()
        + state.epochs.keys().map(location_weight).sum::<usize>()
}

// Keys contain canonical Debug-encoded Location tokens. Respect quoted path
// strings when replacing a storage prefix, so nested observations and indices
// cannot be mistaken for an enclosing location.
fn relocated_key(key: &str, from: &Location, to: &Location) -> String {
    let prefix = format!("Location {{ root: {:?}, path: [", from.root);
    let old_path = from
        .path
        .iter()
        .map(|s| format!("{s:?}"))
        .collect::<Vec<_>>()
        .join(", ");
    let new_path = to
        .path
        .iter()
        .map(|s| format!("{s:?}"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut out = String::new();
    let mut rest = key;
    while let Some(start) = rest.find(&prefix) {
        out.push_str(&rest[..start]);
        let content = &rest[start + prefix.len()..];
        let mut quoted = false;
        let mut escaped = false;
        let mut end = None;
        for (index, ch) in content.char_indices() {
            if escaped {
                escaped = false;
                continue;
            }
            if quoted && ch == '\\' {
                escaped = true;
                continue;
            }
            if ch == '"' {
                quoted = !quoted;
                continue;
            }
            if !quoted && ch == ']' && content[index..].starts_with("] }") {
                end = Some(index);
                break;
            }
        }
        let Some(end) = end else {
            out.push_str(&rest[start..]);
            return out;
        };
        let path = &content[..end];
        let suffix = if old_path.is_empty() {
            Some(path)
        } else if path == old_path {
            Some("")
        } else {
            path.strip_prefix(&format!("{old_path}, "))
        };
        if let Some(suffix) = suffix {
            let comma = if !new_path.is_empty() && !suffix.is_empty() {
                ", "
            } else {
                ""
            };
            out.push_str(&format!(
                "Location {{ root: {:?}, path: [{new_path}{comma}{suffix}] }}",
                to.root
            ));
        } else {
            out.push_str(&rest[start..start + prefix.len() + end + 3]);
        }
        rest = &content[end + 3..];
    }
    out.push_str(rest);
    out
}

pub(super) fn check(checked: &CheckedProgram<'_>) -> Result<(), AnalysisError> {
    let p = checked.program();
    let summaries = super::summaries::all(p);
    let mut engine = Engine {
        checked,
        summaries,
        function: String::new(),
        span: None,
        serial: 0,
        steps: 0,
        entry: State::default(),
        spec_depth: 0,
        validation_depth: 0,
        linear: crate::linearcheck::LinearTypes::from_program(p),
        identity_work: 0,
    };
    for (name, refinement) in &p.contracts.refinements {
        engine.function = format!("#where {name}");
        let mut state = State::default();
        let mut value = engine.unknown(refinement.base.clone());
        value.place = Some(Location::root(engine.fresh("refinement-binder")));
        state.values.insert(refinement.binder.clone(), value);
        for predicate in &refinement.predicates {
            if super::contains_form(predicate, "old") || super::contains_form(predicate, "result") {
                return Err(engine.error("#old and #result are only available in #ensures"));
            }
            engine.predicate(predicate, &mut state, false)?;
        }
    }
    let mut constrained_constructors = HashSet::new();
    for name in checked.declarations().structs.keys() {
        if !lowering::predicates_for(&Type::Named(name.clone()), &symbol("value"), p)
            .map_err(|e| engine.error(e))?
            .is_empty()
        {
            constrained_constructors.insert(name.clone());
        }
    }
    for (name, f) in &p.contracts.originals {
        if f.external {
            continue;
        }
        engine.function = name.clone();
        engine.span = p.declaration_spans.get(name).copied();
        let clauses = p.contracts.clauses.get(name).cloned().unwrap_or_default();
        let mut relevant = !clauses.requires.is_empty()
            || !clauses.ensures.is_empty()
            || !clauses.preserves.is_empty()
            || !clauses.result_constraints.is_empty();
        let mut local_types = Vec::new();
        super::visit_body(
            &f.body,
            &mut |expression| {
                relevant |= matches!(head(expression), "if-valid" | "assume" | "index-proven")
                    || constrained_constructors.contains(head(expression));
                if let Some(Expr::Function(callee)) = parts(expression).first() {
                    relevant |= p
                        .contracts
                        .clauses
                        .get(callee)
                        .is_some_and(|c| !c.requires.is_empty());
                }
            },
            &mut |statement| {
                if let Statement::Let { ty, .. }
                | Statement::Destructure { ty, .. }
                | Statement::LetElse { ty, .. } = statement
                {
                    local_types.push(ty.clone());
                }
            },
        );
        for ty in local_types {
            relevant |= !lowering::predicates_for(&ty, &symbol("value"), p)
                .map_err(|e| engine.error(e))?
                .is_empty();
        }
        if !relevant {
            continue;
        }
        let mut s = State::default();
        for param in &f.parameters {
            if param.mutable {
                s.mutable_bindings.insert(param.name.clone());
            }
            let place = Location::root(format!("parameter:{name}:{}", param.name));
            let mut value = engine.unknown(param.ty.clone());
            value.place = Some(Location::root(format!("handle:{name}:{}", param.name)));
            if matches!(
                engine.resolve(&param.ty),
                Type::Reference { .. }
                    | Type::PinnedReference { .. }
                    | Type::Slice(_)
                    | Type::MutableSlice(_)
            ) {
                value.targets = vec![place.clone()];
                value.key = format!("&{:?}", value.targets);
            }
            engine.check_value(&value)?;
            s.values.insert(param.name.clone(), value);
        }
        let clauses = p.contracts.clauses.get(name).cloned().unwrap_or_default();
        for pred in p.contracts.effective_requires[name].ordered() {
            let fact = engine.predicate(pred, &mut s, false)?;
            engine.add(&mut s, fact)?;
        }
        // Validate promises independently of runtime instrumentation, including
        // production-only compilation where their expressions are erased.
        let mut post = engine.snapshot(&s)?;
        let result = engine.unknown(f.return_type.clone());
        post.values.insert("__lim_contract_result".into(), result);
        for pred in clauses.ensures.iter().chain(&clauses.preserves) {
            let pred = engine.freeze_old(pred, &s, &mut post)?;
            engine.predicate(&pred, &mut post, true)?;
        }
        for param in &f.parameters {
            for pred in lowering::predicates_for(&param.ty, &symbol(&param.name), p)
                .map_err(|e| engine.error(e))?
            {
                let value = &s.values[&param.name];
                let root = value
                    .targets
                    .first()
                    .cloned()
                    .or_else(|| value.place.clone())
                    .unwrap();
                s.fixed.push((pred, root));
            }
        }
        engine.entry = engine.snapshot(&s)?;
        engine.statements(&f.body, &mut s, true)?;
    }
    Ok(())
}
