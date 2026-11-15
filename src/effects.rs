//! Explicit static permissions, independent of predicate evidence and memory
//! invalidation. No permission here establishes purity, visibility, or safety.
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use crate::typed_body::{Body, NodeId, NodeKind, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowLoanOrigins, FlowNodeId};
use crate::typed_ir::{DeclarationId, Declarations, FunctionId, GlobalId};
use crate::{Expr, Item, Program, SourceError, Span};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Qualification {
    Io,
    Input,
    Output,
    GlobalAccess,
    Read(String),
    Write(String),
    Of(String),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Declaration {
    qualifications: BTreeSet<Qualification>,
    /// Canonical names identify declarations; authored target spans identify
    /// the actual use, including an alias or its explicit @ qualification.
    origins: BTreeMap<Qualification, Span>,
}

fn symbol(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Symbol(name) => Some(name.strip_prefix('#').unwrap_or(name)),
        _ => None,
    }
}

pub(crate) fn is_clause(expr: &Expr) -> bool {
    matches!(expr, Expr::List(xs) if xs.first().and_then(symbol) == Some("effects"))
}

struct ParseError {
    message: &'static str,
    /// Child indices relative to the qualification list, not source offsets.
    path: Vec<usize>,
}
impl ParseError {
    fn new(message: &'static str, path: &[usize]) -> Self {
        Self {
            message,
            path: path.to_vec(),
        }
    }
}
struct Parsed {
    declaration: Declaration,
    targets: BTreeMap<Qualification, Vec<usize>>,
}

fn span_at(source: &crate::SpannedExpr, path: &[usize]) -> Span {
    let mut node = source;
    for &index in path {
        let Some(child) = node.children.get(index) else {
            // Synthesized literal nodes may share one authored token and have
            // no source children. Its enclosing value is the precise span.
            break;
        };
        node = child;
    }
    node.span
}

impl Declaration {
    /// The grammar is shared by AST parsing and spanned source validation.
    /// Function parsing keeps its existing String error interface.
    pub(crate) fn parse(value: &Expr) -> Result<Self, String> {
        Self::parse_value(value)
            .map(|parsed| parsed.declaration)
            .map_err(|error| error.message.to_owned())
    }

    fn parse_value(value: &Expr) -> Result<Parsed, ParseError> {
        let Expr::List(entries) = value else {
            return Err(ParseError::new(
                "#effects requires a list of effect qualifications",
                &[],
            ));
        };
        let mut declaration = Self::default();
        let mut targets = BTreeMap::new();
        for (index, entry) in entries.iter().enumerate() {
            // Callback groups explicitly union written declaration names.
            // Remember the first authored leaf for each named callback.
            if let Expr::List(parts) = entry {
                if parts.first().and_then(symbol) == Some("effects-of") && parts.len() == 2 {
                    if let Expr::List(_) = &parts[1] {
                        fn group_targets(
                            value: &Expr,
                            depth: usize,
                            path: &mut Vec<usize>,
                            output: &mut BTreeMap<String, Vec<usize>>,
                        ) -> Result<(), ParseError> {
                            if depth > 128 {
                                return Err(ParseError::new(
                                    "#effects-of callback groups exceed nesting limit",
                                    path,
                                ));
                            }
                            match value {
                                Expr::List(values) => {
                                    for (index, value) in values.iter().enumerate() {
                                        path.push(index);
                                        group_targets(value, depth + 1, path, output)?;
                                        path.pop();
                                    }
                                }
                                Expr::Symbol(name) | Expr::Function(name)
                                    if !name.starts_with('#')
                                        && !name.trim_start_matches('@').is_empty() =>
                                {
                                    output
                                        .entry(name.trim_start_matches('@').to_owned())
                                        .or_insert_with(|| path.clone());
                                }
                                _ => {
                                    return Err(ParseError::new(
                                        "#effects-of groups contain only function declaration names",
                                        path,
                                    ));
                                }
                            }
                            Ok(())
                        }
                        let mut names = BTreeMap::new();
                        group_targets(&parts[1], 0, &mut vec![index, 1], &mut names)?;
                        for (name, path) in names {
                            let qualification = Qualification::Of(name);
                            declaration.qualifications.insert(qualification.clone());
                            targets.entry(qualification).or_insert(path);
                        }
                        continue;
                    }
                }
            }
            let qualification = match symbol(entry) {
                Some("io") => Qualification::Io,
                Some("io-input") => Qualification::Input,
                Some("io-output") => Qualification::Output,
                Some("global-access") => Qualification::GlobalAccess,
                _ => {
                    let Expr::List(parts) = entry else {
                        return Err(ParseError::new("expected #io, #io-input, #io-output, #global-access, (#read-global name), (#write-global name), or (#effects-of function) in #effects", &[index]));
                    };
                    if parts.len() != 2 {
                        return Err(ParseError::new(
                            "global and function effect qualifications require exactly one declaration name",
                            &[index],
                        ));
                    }
                    let name = match &parts[1] {
                        Expr::Symbol(name) | Expr::Function(name) if !name.starts_with('#') => {
                            name.trim_start_matches('@').to_owned()
                        }
                        _ => {
                            return Err(ParseError::new(
                                "effect targets must be declaration names",
                                &[index, 1],
                            ));
                        }
                    };
                    if name.is_empty() {
                        return Err(ParseError::new(
                            "effect targets must be non-empty declaration names",
                            &[index, 1],
                        ));
                    }
                    match parts.first().and_then(symbol) {
                        Some("read-global") => Qualification::Read(name),
                        Some("write-global") => Qualification::Write(name),
                        Some("effects-of") => Qualification::Of(name),
                        _ => {
                            return Err(ParseError::new("unknown effect qualification", &[index, 0]));
                        }
                    }
                }
            };
            if !declaration.qualifications.insert(qualification.clone()) {
                return Err(ParseError::new("duplicate effect qualification", &[index]));
            }
            if matches!(
                &qualification,
                Qualification::Read(_) | Qualification::Write(_) | Qualification::Of(_)
            ) {
                targets.insert(qualification, vec![index, 1]);
            }
        }
        Ok(Parsed {
            declaration,
            targets,
        })
    }

    fn from_clause(clause: &crate::SpannedExpr) -> Result<Self, SourceError> {
        let Expr::List(parts) = &clause.expr else {
            unreachable!("source effect clause has a list head")
        };
        if parts.len() != 2 {
            return Err(SourceError::new(
                "#effects requires exactly one qualification list",
                crate::DiagnosticCode::Parse,
            ).at(clause.span));
        }
        let source = clause.children.get(1).unwrap_or(clause);
        let mut parsed = Self::parse_value(&parts[1]).map_err(|error| {
            SourceError::new(error.message, crate::DiagnosticCode::Parse)
                .at(span_at(source, &error.path))
        })?;
        for (qualification, path) in parsed.targets {
            parsed.declaration.origins.insert(qualification, span_at(source, &path));
        }
        Ok(parsed.declaration)
    }
}

/// Validate while the ordinary frontend still has exact source structure,
/// before parse_item's legacy String errors can discard the offending span.
pub(crate) fn validate_source_declaration(source: &crate::SpannedExpr) -> Result<(), SourceError> {
    let Expr::List(parts) = &source.expr else {
        return Ok(());
    };
    let index = match parts.first().and_then(symbol) {
        Some("fn" | "unsafe-fn") => 4,
        Some("extern-fn") => 5,
        _ => return Ok(()),
    };
    if let Some(clause) = source.children.get(index)
        .filter(|clause| is_clause(&clause.expr))
    {
        Declaration::from_clause(clause)?;
    }
    Ok(())
}

/// Collect signature-only clauses from canonical source declarations. Keeping
/// this outside Function avoids changing the runtime ABI or generated function
/// records. Constructed AST functions with no source have empty permissions.
pub(crate) fn collect(program: &Program) -> Result<BTreeMap<String, Declaration>, SourceError> {
    let mut result = BTreeMap::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let Some(source) = program.declaration_expressions.get(&function.name) else {
            continue;
        };
        let index = if function.external { 5 } else { 4 };
        let Some(clause) = source.children.get(index).filter(|c| is_clause(&c.expr)) else {
            continue;
        };
        result.insert(function.name.clone(), Declaration::from_clause(clause)?);
    }
    Ok(result)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Effect {
    Io,
    Input,
    Output,
    GlobalAccess,
    Read(GlobalId),
    Write(GlobalId),
}
type Permissions = BTreeSet<Effect>;

fn error(message: String, span: Option<Span>) -> crate::typecheck::AnalysisError {
    (message, crate::DiagnosticCode::Contract, span, Vec::new())
}

fn name(declarations: &Declarations, id: FunctionId) -> &str {
    declarations.declaration_name(DeclarationId::Function(id))
}

fn describe(effect: Effect, declarations: &Declarations) -> String {
    match effect {
        Effect::Io => "#io".into(),
        Effect::Input => "#io-input".into(),
        Effect::Output => "#io-output".into(),
        Effect::GlobalAccess => "#global-access".into(),
        Effect::Read(id) => format!(
            "(#read-global {})",
            declarations.declaration_name(DeclarationId::Global(id))
        ),
        Effect::Write(id) => format!(
            "(#write-global {})",
            declarations.declaration_name(DeclarationId::Global(id))
        ),
    }
}

fn permits(permissions: &Permissions, effect: Effect) -> bool {
    permissions.contains(&effect)
        || matches!(effect, Effect::Input | Effect::Output if permissions.contains(&Effect::Io))
        || matches!(effect, Effect::Read(_) | Effect::Write(_) if permissions.contains(&Effect::GlobalAccess))
        || matches!(effect, Effect::Read(id) if permissions.contains(&Effect::Write(id)))
}

/// Expand *declared* inclusions only. This least fixed point handles cycles
/// without recursive traversal or inferring qualifications from function bodies.
fn resolve(
    program: &Program,
    declarations: &Declarations,
) -> Result<HashMap<FunctionId, Permissions>, crate::typecheck::AnalysisError> {
    let mut resolved = HashMap::new();
    let mut dependents: HashMap<FunctionId, Vec<FunctionId>> = HashMap::new();
    let function_names = program
        .items
        .iter()
        .filter_map(|item| {
            if let Item::Function(function) = item {
                Some(function.name.as_str())
            } else {
                None
            }
        })
        .collect::<BTreeSet<_>>();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let id = declarations.function_id(&function.name).ok_or_else(|| {
            error(
                format!("missing typed effect interface for '{}'", function.name),
                program.declaration_spans.get(&function.name).copied(),
            )
        })?;
        let mut permissions = Permissions::new();
        if let Some(declaration) = program.contracts.effects.get(&function.name) {
            for qualification in &declaration.qualifications {
                let target_span = declaration.origins.get(qualification).copied()
                    .or_else(|| program.declaration_spans.get(&function.name).copied());
                let effect = match qualification {
                    Qualification::Io => Effect::Io,
                    Qualification::Input => Effect::Input,
                    Qualification::Output => Effect::Output,
                    Qualification::GlobalAccess => Effect::GlobalAccess,
                    Qualification::Read(target) | Qualification::Write(target) => {
                        let global = declarations.global_id(target).ok_or_else(|| {
                            error(
                                format!("effect target '{target}' is not a global declaration"),
                                target_span,
                            )
                        })?;
                        if matches!(qualification, Qualification::Read(_)) {
                            Effect::Read(global)
                        } else {
                            Effect::Write(global)
                        }
                    }
                    Qualification::Of(target) => {
                        let callee = declarations.function_id(target).ok_or_else(|| {
                            error(
                                format!("#effects-of target '{target}' is not a function declaration"),
                                target_span,
                            )
                        })?;
                        // Signature-only compiler interfaces have no checked
                        // source body or declaration that can promise purity.
                        if !function_names.contains(target.as_str()) {
                            return Err(error(
                                format!("#effects-of target '{target}' has no explicit function effect interface"),
                                target_span,
                            ));
                        }
                        dependents.entry(callee).or_default().push(id);
                        continue;
                    }
                };
                permissions.insert(effect);
            }
        }
        resolved.insert(id, permissions);
    }
    let mut pending: VecDeque<_> = resolved.keys().copied().collect();
    while let Some(callee) = pending.pop_front() {
        let inherited = resolved[&callee].clone();
        for &caller in dependents.get(&callee).into_iter().flatten() {
            let permissions = resolved.get_mut(&caller).expect("declared caller");
            let before = permissions.len();
            permissions.extend(inherited.iter().copied());
            if permissions.len() != before {
                pending.push_back(caller);
            }
        }
    }
    Ok(resolved)
}

struct Accesses<'a> {
    body: &'a Body,
    flow: &'a FlowGraph,
    origins: &'a FlowLoanOrigins,
    constants: &'a BTreeSet<GlobalId>,
    required: Vec<(Effect, Option<Span>, String)>,
}

impl Accesses<'_> {
    fn require(&mut self, effect: Effect, span: Option<Span>, reason: &str) {
        if matches!(effect, Effect::Read(id) if self.constants.contains(&id)) {
            return;
        }
        self.required.push((effect, span, reason.into()));
    }

    fn root(&mut self, root: &PlaceRoot, write: bool, span: Option<Span>) {
        if let PlaceRoot::Global(global) = root {
            self.require(
                if write {
                    Effect::Write(*global)
                } else {
                    Effect::Read(*global)
                },
                span,
                "global access",
            );
        }
    }

    fn referents(&mut self, event: FlowNodeId, value: NodeId, write: bool, span: Option<Span>) {
        let targets = self
            .origins
            .value_before(self.body, self.flow, event, value);
        if targets.is_empty() {
            self.require(Effect::GlobalAccess, span, "unresolved memory access");
        }
        for target in targets {
            if target.lifetime_only {
                self.require(Effect::GlobalAccess, span, "raw memory access");
            }
            self.root(&target.place.root, write, span);
        }
    }

    fn place(
        &mut self,
        event: FlowNodeId,
        place: &crate::typed_place::Place,
        write: bool,
        span: Option<Span>,
    ) {
        self.root(&place.root, write, span);
        if let PlaceRoot::Local(binding) = place.root {
            // Assigning a local reference slot does not write its referent.
            if !place.segments.is_empty() {
                for target in self
                    .origins
                    .projected_referents(event, binding, &place.segments)
                {
                    self.root(&target.root, write, span);
                }
            }
        }
    }

    fn call(
        &mut self,
        event: FlowNodeId,
        callee: FunctionId,
        children: &[NodeId],
        declared: &HashMap<FunctionId, Permissions>,
        declarations: &Declarations,
        span: Option<Span>,
    ) {
        let reason = format!("call to '{}'", name(declarations, callee));
        if let Some(permissions) = declared.get(&callee) {
            for &effect in permissions {
                self.require(effect, span, &reason);
            }
        } else {
            self.require(Effect::Io, span, &reason);
            self.require(Effect::GlobalAccess, span, &reason);
        }
        // Passing a global reference is an observation even when the callee's
        // eventual read cannot be narrowed. Mutations use the existing complete
        // byte-write summaries, never the weaker tag-preserving shortcut.
        for &argument in children.iter().skip(1) {
            for origin in self
                .origins
                .value_before(self.body, self.flow, event, argument)
            {
                self.root(&origin.place.root, false, span);
            }
        }
        if let Some(summaries) = self.body.call_tag_mutations.get(&callee) {
            for summary in summaries {
                if let Some(global) = summary.global {
                    self.root(&PlaceRoot::Global(global), true, span);
                } else if let Some(&argument) = children.get(summary.parameter + 1) {
                    for origin in self
                        .origins
                        .apply_summary_before(self.body, self.flow, event, argument, summary)
                    {
                        self.root(&origin.place.root, true, span);
                    }
                }
            }
        } else {
            // Recursive/opaque summaries must not silently erase global writes
            // through arguments (including shared references to atomics).
            for &argument in children.iter().skip(1) {
                for origin in self
                    .origins
                    .value_before(self.body, self.flow, event, argument)
                {
                    self.root(&origin.place.root, true, span);
                }
            }
        }
    }
}

/// Audited operations whose own execution has no IO or hidden memory effects.
/// Their operands and resolved flow accesses are checked independently. New
/// primitives default to broad IO/global access until classified here.
fn local_primitive(head: &str) -> bool {
    matches!(
        head,
        "literal"
            | "if"
            | "match"
            | "unsafe"
            | "as"
            | "array"
            | "array-repeat"
            | "tuple"
            | "struct"
            | "struct-literal"
            | "enum-literal"
            | "index"
            | "index-proven"
            | "get"
            | "get-payload"
            | "#variant-is"
            | "borrow"
            | "borrow-mut"
            | "borrow-slice"
            | "borrow-slice-mut"
            | "slice-of"
            | "slice-mut-of"
            | "slice-len"
            | "slice-mut-len"
            | "slice-idx"
            | "slice-mut-idx"
            | "slice-range"
            | "slice-mut-range"
            | "slice-mut-split"
            | "deref"
            | "deref-set"
            | "clone"
            | "drop"
            | "forget"
            | "pin"
            | "pin-shared"
            | "pin-borrow"
            | "pin-borrow-mut"
            | "pin-read"
            | "pin-write"
            | "pin-set-field"
            | "pin-get-payload"
            | "pin-get-payload-mut"
            | "pin-get-payload-unchecked"
            | "pin-get-payload-unchecked-mut"
            | "pin-own-of"
            | "pin-share"
            | "pin-share-clone"
            | "pin-own-borrow"
            | "pin-own-borrow-mut"
            | "pin-release"
            | "atomic-init"
            | "atomic-load"
            | "atomic-store"
            | "atomic-fetch-add"
            | "atomic-exchange"
            | "atomic-compare-exchange"
            | "atomic-compare-exchange-weak"
            | "size-of"
            | "align-of"
            | "offset-of"
            | "assert"
            | "debug-assert"
            | "unreachable"
            | "panic"
            | "ptr-null"
            | "ptr-is-null"
            | "ptr-address"
            | "ref-ptr"
            | "addr-of"
            | "addr-of-mut"
            | "ptr-offset"
            | "requires"
            | "ensures"
            | "preserves"
            | "assume"
            | "if-valid"
            | "old"
            | "result"
    )
}

fn check_initializers(
    program: &Program,
    declarations: &Declarations,
    declared: &HashMap<FunctionId, Permissions>,
) -> Result<(), crate::typecheck::AnalysisError> {
    for item in &program.items {
        let (name, value) = match item {
            Item::Let { name, value, .. } | Item::Static { name, value, .. } => (name, value),
            _ => continue,
        };
        let mut required = None;
        // Initializers have no ambient capabilities. This walk checks call
        // interfaces, including nested blocks; it does not evaluate constants.
        crate::contracts::visit_statement(&crate::Statement::Expr(value.clone()), &mut |expr| {
            if required.is_some() {
                return;
            }
            let Expr::List(parts) = expr else { return };
            match parts.first() {
                Some(Expr::Function(target)) => {
                    required = declarations
                        .function_id(target)
                        .and_then(|id| declared.get(&id))
                        .map_or(Some(Effect::Io), |permissions| permissions.first().copied());
                }
                Some(Expr::Symbol(head))
                    if crate::is_builtin_head(head)
                        && crate::typed_body::NumericOperation::parse(head).is_none()
                        && !local_primitive(head)
                        // Explicit constructor operands can contain type
                        // syntax such as (#atomic #usize). These are not
                        // executed operations. Their children still undergo
                        // this walk, so runtime operands remain checked.
                        && crate::parse_type(Some(expr)).is_err() =>
                {
                    required = Some(Effect::Io)
                }
                _ => {}
            }
        });
        if let Some(effect) = required {
            return Err(error(format!("global initializer '{name}' requires effect {}; perform effectful initialization in an explicitly qualified function called from main", describe(effect, declarations)), program.declaration_spans.get(name).copied()));
        }
    }
    Ok(())
}

fn immutable_constant(
    ty: &crate::Type,
    declarations: &Declarations,
    active: &mut BTreeSet<String>,
) -> bool {
    use crate::Type;
    match ty {
        Type::Atomic(_)
        | Type::Reference { .. }
        | Type::PinnedReference { .. }
        | Type::RawPointer { .. }
        | Type::PinOwned(_)
        | Type::PinShared(_)
        | Type::Slice(_)
        | Type::MutableSlice(_)
        | Type::Generic(_) => false,
        Type::Tuple(fields) => fields
            .iter()
            .all(|ty| immutable_constant(ty, declarations, active)),
        Type::Array(ty, _) => immutable_constant(ty, declarations, active),
        Type::Named(name) => {
            if !active.insert(name.clone()) {
                return false;
            }
            let immutable = declarations
                .structs
                .get(name)
                .map(|fields| {
                    fields
                        .iter()
                        .all(|field| immutable_constant(&field.ty, declarations, active))
                })
                .or_else(|| {
                    declarations.enums.get(name).map(|variants| {
                        variants.iter().all(|variant| {
                            variant
                                .fields
                                .iter()
                                .all(|ty| immutable_constant(ty, declarations, active))
                        })
                    })
                })
                .unwrap_or(false);
            active.remove(name);
            immutable
        }
        _ => true,
    }
}

pub(crate) fn check(
    checked: &crate::typecheck::CheckedProgram<'_>,
) -> Result<(), crate::typecheck::AnalysisError> {
    check_resolved(checked.program(), checked.declarations())
}

/// Also used for retained source witnesses before generator erasure. Witness
/// permissions remain their written source interfaces, independently of any
/// broad grants needed by generated representation helpers.
pub(crate) fn check_resolved(
    program: &Program,
    declarations: &Declarations,
) -> Result<(), crate::typecheck::AnalysisError> {
    let declared = resolve(program, declarations)?;
    check_initializers(program, declarations, &declared)?;
    let constants = program
        .items
        .iter()
        .filter_map(|item| {
            let Item::Let {
                name,
                mutable: false,
                ..
            } = item
            else {
                return None;
            };
            let source = program.declaration_expressions.get(name)?;
            let Expr::List(parts) = &source.expr else {
                return None;
            };
            (parts.first().and_then(symbol) == Some("const"))
                .then(|| declarations.global_id(name))
                .flatten()
                .filter(|id| {
                    immutable_constant(
                        declarations.global_type(*id),
                        declarations,
                        &mut BTreeSet::new(),
                    )
                })
        })
        .collect::<BTreeSet<_>>();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let id = declarations.function_id(&function.name).ok_or_else(|| {
            error(
                format!("missing typed effect interface for '{}'", function.name),
                program.declaration_spans.get(&function.name).copied(),
            )
        })?;
        let permissions = &declared[&id];
        let declaration_span = program.declaration_spans.get(&function.name).copied();
        let mut required = Vec::new();
        if function.external {
            required.push((
                Effect::Io,
                declaration_span,
                "external function boundary".into(),
            ));
            required.push((
                Effect::GlobalAccess,
                declaration_span,
                "external function boundary".into(),
            ));
        } else {
            let body = declarations.bodies.get(&function.name).ok_or_else(|| {
                error(
                    format!("missing typed effect body for '{}'", function.name),
                    declaration_span,
                )
            })?;
            let flow = &declarations.flows[&function.name];
            let origins = flow.loan_origins(body);
            let mut accesses = Accesses {
                body,
                flow,
                origins: &origins,
                constants: &constants,
                required: Vec::new(),
            };
            for event in flow.reachable() {
                let node = &flow.nodes[event.0];
                let span = node.span.or(declaration_span);
                match &node.action {
                    FlowAction::Read { place, .. } | FlowAction::Clone { place, .. } => {
                        accesses.place(event, place, false, span)
                    }
                    FlowAction::Borrow { place, mutable, .. } => {
                        accesses.place(event, place, *mutable, span)
                    }
                    FlowAction::Assign { place, .. }
                    | FlowAction::Write { place, .. }
                    | FlowAction::Release { place, .. } => accesses.place(event, place, true, span),
                    _ => {}
                }
                let Some(value) = node.action.value() else {
                    continue;
                };
                let NodeKind::Form {
                    head,
                    children,
                    numeric,
                    callee,
                    ..
                } = &body.nodes[value.0].kind
                else {
                    continue;
                };
                if let Some(callee) = callee {
                    accesses.call(event, *callee, children, &declared, declarations, span);
                    continue;
                }
                // #clone can invoke an ordinary user-defined helper without
                // appearing as a syntactic call in the typed body.
                if head == "clone" {
                    if let Some(crate::Type::Named(owner)) =
                        children.get(1).and_then(|id| body.nodes[id.0].ty.as_ref())
                    {
                        if let Some(callee) = declarations.function_id(&format!("{owner}::clone")) {
                            accesses.call(event, callee, children, &declared, declarations, span);
                            continue;
                        }
                    }
                }
                if numeric.is_some() {
                    continue;
                }
                if children.first().is_some_and(|child| {
                    matches!(
                        body.nodes[child.0].kind,
                        NodeKind::Declaration(
                            DeclarationId::Aggregate(_) | DeclarationId::Variant(_)
                        )
                    )
                }) {
                    continue;
                }
                if head == "io-input-byte" {
                    accesses.require(Effect::Input, span, head);
                } else if head == "io-output-byte" {
                    accesses.require(Effect::Output, span, head);
                } else if !local_primitive(head) {
                    accesses.require(Effect::Io, span, head);
                    accesses.require(Effect::GlobalAccess, span, head);
                }
                if matches!(
                    head.as_str(),
                    "atomic-load"
                        | "atomic-store"
                        | "atomic-fetch-add"
                        | "atomic-exchange"
                        | "atomic-compare-exchange"
                        | "atomic-compare-exchange-weak"
                        | "deref-set"
                        | "pin-read"
                        | "pin-write"
                        | "pin-set-field"
                ) {
                    if let Some(&target) = children.get(1) {
                        accesses.referents(
                            event,
                            target,
                            !matches!(head.as_str(), "atomic-load" | "pin-read"),
                            span,
                        );
                    }
                }
            }
            required = accesses.required;
        }
        for (effect, span, reason) in required {
            if !permits(permissions, effect) {
                return Err(error(format!("function '{}' requires explicit effect qualification {} in #effects for {reason}", function.name, describe(effect, declarations)), span));
            }
        }
    }
    Ok(())
}
