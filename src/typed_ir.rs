//! Retained semantic information. This is the first stage of the typed IR:
//! declarations are resolved once by validation, not rediscovered by emission.
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use crate::{EnumVariant, Field, Span, Type};

#[derive(Clone, Debug)]
pub(crate) struct Signature {
    pub type_parameters: Vec<String>,
    pub parameters: Vec<Type>,
    pub parameter_names: Vec<String>,
    pub return_type: Type,
}

/// Dense identities are deterministic within a checked program. They are not
/// persistent cache keys and do not encode addresses of AST allocations.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct FunctionId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct GlobalId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct AggregateId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct FieldId {
    pub owner: AggregateId,
    pub index: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct VariantId {
    pub owner: AggregateId,
    pub index: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum DeclarationId {
    Global(GlobalId),
    Aggregate(AggregateId),
    Field(FieldId),
    Variant(VariantId),
}

/// Deterministic identity assigned by source-order traversal before checking.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ExpressionId(pub usize);

/// Deterministic identity assigned by source-order traversal to statements.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct StatementId(pub usize);

pub(crate) fn expression_ids(program: &crate::Program) -> HashMap<usize, ExpressionId> {
    fn expression(value: &crate::Expr, ids: &mut HashMap<usize, ExpressionId>, next: &mut usize) {
        ids.insert(std::ptr::from_ref(value) as usize, ExpressionId(*next));
        *next += 1;
        match value {
            crate::Expr::List(items) => {
                for item in items {
                    expression(item, ids, next);
                }
            }
            crate::Expr::Block(statements) | crate::Expr::Loop(statements) => {
                for statement_value in statements {
                    statement(statement_value, ids, next);
                }
            }
            crate::Expr::Labeled {
                expression: inner, ..
            }
            | crate::Expr::Quote(inner)
            | crate::Expr::QuasiQuote(inner)
            | crate::Expr::Unquote(inner)
            | crate::Expr::UnquoteSplicing(inner) => expression(inner, ids, next),
            crate::Expr::Symbol(_)
            | crate::Expr::Integer(_)
            | crate::Expr::UnsignedInteger(_)
            | crate::Expr::Float(_)
            | crate::Expr::Char(_)
            | crate::Expr::String(_)
            | crate::Expr::At => {}
        }
    }

    fn statement(
        value: &crate::Statement,
        ids: &mut HashMap<usize, ExpressionId>,
        next: &mut usize,
    ) {
        use crate::Statement as S;
        match value {
            S::Let { value, .. }
            | S::Assign { value, .. }
            | S::FieldAssign { value, .. }
            | S::TupleAssign { value, .. }
            | S::EnumPayloadAssign { value, .. }
            | S::BreakValue(value)
            | S::Return(Some(value))
            | S::Expr(value) => expression(value, ids, next),
            S::Destructure { pattern, value, .. } => {
                expression(pattern, ids, next);
                expression(value, ids, next);
            }
            S::LetElse {
                pattern,
                value,
                else_body,
                ..
            } => {
                expression(pattern, ids, next);
                expression(value, ids, next);
                for statement_value in else_body {
                    statement(statement_value, ids, next);
                }
            }
            S::ArrayAssign { index, value, .. } => {
                expression(index, ids, next);
                expression(value, ids, next);
            }
            S::While { condition, body } => {
                expression(condition, ids, next);
                for statement_value in body {
                    statement(statement_value, ids, next);
                }
            }
            S::Loop { body } => {
                for statement_value in body {
                    statement(statement_value, ids, next);
                }
            }
            S::For {
                init,
                condition,
                step,
                body,
            } => {
                statement(init, ids, next);
                expression(condition, ids, next);
                statement(step, ids, next);
                for statement_value in body {
                    statement(statement_value, ids, next);
                }
            }
            S::Labeled {
                statement: inner, ..
            } => statement(inner, ids, next),
            S::BreakToValue { value, .. } => expression(value, ids, next),
            S::Break | S::BreakTo(_) | S::Continue | S::ContinueTo(_) | S::Return(None) => {}
        }
    }

    let mut ids = HashMap::new();
    let mut next = 0;
    for item in &program.items {
        match item {
            crate::Item::Function(function) => {
                for statement_value in &function.body {
                    statement(statement_value, &mut ids, &mut next);
                }
            }
            crate::Item::Let { value, .. } | crate::Item::Static { value, .. } => {
                expression(value, &mut ids, &mut next);
            }
            _ => {}
        }
    }
    ids
}

pub(crate) fn statement_ids(program: &crate::Program) -> HashMap<usize, StatementId> {
    fn expression(value: &crate::Expr, ids: &mut HashMap<usize, StatementId>, next: &mut usize) {
        match value {
            crate::Expr::List(items) => {
                for item in items {
                    expression(item, ids, next);
                }
            }
            crate::Expr::Block(statements) | crate::Expr::Loop(statements) => {
                for item in statements {
                    statement(item, ids, next);
                }
            }
            crate::Expr::Labeled {
                expression: inner, ..
            }
            | crate::Expr::Quote(inner)
            | crate::Expr::QuasiQuote(inner)
            | crate::Expr::Unquote(inner)
            | crate::Expr::UnquoteSplicing(inner) => expression(inner, ids, next),
            _ => {}
        }
    }

    fn statements(
        values: &[crate::Statement],
        ids: &mut HashMap<usize, StatementId>,
        next: &mut usize,
    ) {
        for value in values {
            statement(value, ids, next);
        }
    }

    fn statement(
        value: &crate::Statement,
        ids: &mut HashMap<usize, StatementId>,
        next: &mut usize,
    ) {
        use crate::Statement as S;
        ids.insert(std::ptr::from_ref(value) as usize, StatementId(*next));
        *next += 1;
        match value {
            S::Let { value, .. }
            | S::Assign { value, .. }
            | S::FieldAssign { value, .. }
            | S::TupleAssign { value, .. }
            | S::EnumPayloadAssign { value, .. }
            | S::BreakValue(value)
            | S::BreakToValue { value, .. }
            | S::Return(Some(value))
            | S::Expr(value) => expression(value, ids, next),
            S::Destructure { pattern, value, .. } => {
                expression(pattern, ids, next);
                expression(value, ids, next);
            }
            S::LetElse {
                pattern,
                value,
                else_body,
                ..
            } => {
                expression(pattern, ids, next);
                expression(value, ids, next);
                statements(else_body, ids, next);
            }
            S::ArrayAssign { index, value, .. } => {
                expression(index, ids, next);
                expression(value, ids, next);
            }
            S::While { condition, body } => {
                expression(condition, ids, next);
                statements(body, ids, next);
            }
            S::Loop { body } => statements(body, ids, next),
            S::For {
                init,
                condition,
                step,
                body,
            } => {
                statement(init, ids, next);
                expression(condition, ids, next);
                statement(step, ids, next);
                statements(body, ids, next);
            }
            S::Labeled {
                statement: inner, ..
            } => statement(inner, ids, next),
            S::Break | S::BreakTo(_) | S::Continue | S::ContinueTo(_) | S::Return(None) => {}
        }
    }

    let mut ids = HashMap::new();
    let mut next = 0;
    for item in &program.items {
        if let crate::Item::Function(function) = item {
            statements(&function.body, &mut ids, &mut next);
        }
    }
    ids
}

pub(crate) struct FunctionDeclaration {
    pub signature: Signature,
    pub span: Option<Span>,
}

#[cfg(test)]
#[derive(Debug)]
pub(crate) enum StagedReferentError {
    Dependency,
    Use {
        function: String,
        conflict: crate::typed_flow::ReleaseConflict,
    },
    Replacement {
        function: String,
        conflict: crate::typed_flow::ReleaseConflict,
    },
}

pub(crate) struct Declarations {
    pub bodies: HashMap<String, crate::typed_body::Body>,
    pub flows: HashMap<String, crate::typed_flow::FlowGraph>,
    pub liveness: HashMap<String, crate::typed_flow::FlowLiveness>,
    pub aliases: HashMap<String, Type>,
    pub structs: HashMap<String, Vec<Field>>,
    pub enums: HashMap<String, Vec<EnumVariant>>,
    pub globals: HashMap<String, Type>,
    functions: Vec<FunctionDeclaration>,
    function_ids: HashMap<String, FunctionId>,
    global_names: Vec<String>,
    global_ids: HashMap<String, GlobalId>,
    aggregate_names: Vec<String>,
    aggregate_ids: HashMap<String, AggregateId>,
}

fn source_with_span<'a>(
    source: Option<&'a crate::SpannedExpr>,
    span: Span,
) -> Option<&'a crate::SpannedExpr> {
    fn find(source: &crate::SpannedExpr, span: Span) -> Option<&crate::SpannedExpr> {
        if source.span == span {
            return Some(source);
        }
        source.children.iter().find_map(|child| find(child, span))
    }
    source.and_then(|source| find(source, span)).or(source)
}

fn source_child(source: Option<&crate::SpannedExpr>, index: usize) -> Option<&crate::SpannedExpr> {
    source?.children.get(index)
}

fn collect_simple_local_binding_spans(
    function: &crate::Function,
    program: &crate::Program,
    expression_spans_by_address: &HashMap<usize, Span>,
) -> Vec<Option<Span>> {
    let mut output = Vec::new();
    for (index, statement) in function.body.iter().enumerate() {
        let source = program
            .statement_expressions
            .get(&(function.name.clone(), index));
        collect_statement_binding_spans(
            statement,
            source,
            expression_spans_by_address,
            &mut output,
        );
    }
    output
}

fn collect_statement_binding_spans(
    statement: &crate::Statement,
    source: Option<&crate::SpannedExpr>,
    expression_spans: &HashMap<usize, Span>,
    output: &mut Vec<Option<Span>>,
) {
    use crate::Statement as S;
    match statement {
        S::Let { value, .. } => {
            collect_expression_binding_spans(
                value,
                source_child(source, 3),
                expression_spans,
                output,
            );
            let span = source_child(source, 1)
                .filter(|identifier| matches!(identifier.expr, crate::Expr::Symbol(_)))
                .map(|identifier| identifier.span);
            output.push(span);
        }
        S::Destructure { value, .. } => collect_expression_binding_spans(
            value,
            source_child(source, 3),
            expression_spans,
            output,
        ),
        S::LetElse {
            value, else_body, ..
        } => {
            collect_expression_binding_spans(
                value,
                source_child(source, 3),
                expression_spans,
                output,
            );
            collect_statement_list_binding_spans(else_body, source, 4, expression_spans, output);
        }
        S::Assign { value, .. }
        | S::FieldAssign { value, .. }
        | S::TupleAssign { value, .. }
        | S::EnumPayloadAssign { value, .. }
        | S::BreakValue(value)
        | S::Return(Some(value))
        | S::Expr(value) => {
            let child = match statement {
                S::Assign { .. } => 2,
                S::FieldAssign { .. } | S::TupleAssign { .. } | S::EnumPayloadAssign { .. } => 3,
                S::BreakValue(_) | S::Return(Some(_)) => 1,
                S::Expr(_) => {
                    return collect_expression_binding_spans(
                        value,
                        source,
                        expression_spans,
                        output,
                    )
                }
                _ => unreachable!(),
            };
            collect_expression_binding_spans(
                value,
                source_child(source, child),
                expression_spans,
                output,
            );
        }
        S::ArrayAssign { index, value, .. } => {
            collect_expression_binding_spans(
                index,
                source_child(source, 2),
                expression_spans,
                output,
            );
            collect_expression_binding_spans(
                value,
                source_child(source, 3),
                expression_spans,
                output,
            );
        }
        S::While { condition, body } => {
            collect_expression_binding_spans(
                condition,
                source_child(source, 1),
                expression_spans,
                output,
            );
            collect_statement_list_binding_spans(body, source, 2, expression_spans, output);
        }
        S::Loop { body } => {
            collect_statement_list_binding_spans(body, source, 1, expression_spans, output)
        }
        S::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_statement_binding_spans(
                init,
                source_child(source, 1),
                expression_spans,
                output,
            );
            collect_expression_binding_spans(
                condition,
                source_child(source, 2),
                expression_spans,
                output,
            );
            collect_statement_binding_spans(
                step,
                source_child(source, 3),
                expression_spans,
                output,
            );
            collect_statement_list_binding_spans(body, source, 4, expression_spans, output);
        }
        S::Labeled { statement, .. } => collect_statement_binding_spans(
            statement,
            source.and_then(|source| source.children.last()),
            expression_spans,
            output,
        ),
        S::Break
        | S::BreakTo(_)
        | S::BreakToValue { .. }
        | S::Continue
        | S::ContinueTo(_)
        | S::Return(None) => {
            if let S::BreakToValue { value, .. } = statement {
                collect_expression_binding_spans(
                    value,
                    source_child(source, 2),
                    expression_spans,
                    output,
                );
            }
        }
    }
}

fn collect_statement_list_binding_spans(
    statements: &[crate::Statement],
    source: Option<&crate::SpannedExpr>,
    start: usize,
    expression_spans: &HashMap<usize, Span>,
    output: &mut Vec<Option<Span>>,
) {
    let sources = source.and_then(|source| source.children.get(start..));
    for (index, statement) in statements.iter().enumerate() {
        collect_statement_binding_spans(
            statement,
            sources.and_then(|sources| sources.get(index)),
            expression_spans,
            output,
        );
    }
}

fn collect_expression_binding_spans(
    expression: &crate::Expr,
    source: Option<&crate::SpannedExpr>,
    expression_spans: &HashMap<usize, Span>,
    output: &mut Vec<Option<Span>>,
) {
    use crate::Expr as E;
    let span = expression_spans.get(&(std::ptr::from_ref(expression) as usize));
    let source = span
        .and_then(|span| source_with_span(source, *span))
        .or(source);
    match expression {
        E::List(items) => {
            for item in items {
                let item_source = expression_spans
                    .get(&(std::ptr::from_ref(item) as usize))
                    .and_then(|item_span| source_with_span(source, *item_span));
                collect_expression_binding_spans(item, item_source, expression_spans, output);
            }
        }
        E::Block(statements) | E::Loop(statements) => {
            collect_statement_list_binding_spans(statements, source, 1, expression_spans, output);
        }
        E::Labeled { expression, .. }
        | E::Quote(expression)
        | E::QuasiQuote(expression)
        | E::Unquote(expression)
        | E::UnquoteSplicing(expression) => collect_expression_binding_spans(
            expression,
            source.and_then(|source| source.children.last()),
            expression_spans,
            output,
        ),
        E::Symbol(_)
        | E::Integer(_)
        | E::UnsignedInteger(_)
        | E::Float(_)
        | E::Char(_)
        | E::String(_)
        | E::At => {}
    }
}

impl Declarations {
    pub fn new(
        aliases: HashMap<String, Type>,
        structs: HashMap<String, Vec<Field>>,
        enums: HashMap<String, Vec<EnumVariant>>,
        globals: HashMap<String, Type>,
        functions: HashMap<String, Signature>,
        spans: &HashMap<String, Span>,
    ) -> Self {
        let mut global_names: Vec<_> = globals.keys().cloned().collect();
        global_names.sort();
        let global_ids = global_names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), GlobalId(index)))
            .collect();
        let mut aggregate_names: Vec<_> = structs.keys().chain(enums.keys()).cloned().collect();
        aggregate_names.sort();
        let aggregate_ids = aggregate_names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), AggregateId(index)))
            .collect();
        let mut functions: Vec<_> = functions.into_iter().collect();
        functions.sort_by(|a, b| a.0.cmp(&b.0));
        let function_ids = functions
            .iter()
            .enumerate()
            .map(|(index, (name, _))| (name.clone(), FunctionId(index)))
            .collect();
        let functions = functions
            .into_iter()
            .map(|(name, signature)| FunctionDeclaration {
                signature,
                span: spans.get(&name).copied(),
            })
            .collect();
        Self {
            bodies: HashMap::new(),
            flows: HashMap::new(),
            liveness: HashMap::new(),
            aliases,
            structs,
            enums,
            globals,
            functions,
            function_ids,
            global_names,
            global_ids,
            aggregate_names,
            aggregate_ids,
        }
    }

    pub fn global_id(&self, name: &str) -> Option<GlobalId> {
        self.global_ids.get(name).copied()
    }

    pub fn aggregate_id(&self, ty: &Type) -> Option<AggregateId> {
        let mut ty = resolve_type(ty, &self.aliases).ok()?;
        loop {
            ty = match ty {
                Type::Reference { target, .. } | Type::PinnedReference { target, .. } => *target,
                _ => break,
            };
        }
        let Type::Named(name) = ty else {
            return None;
        };
        self.aggregate_ids.get(&name).copied()
    }

    pub fn field_id(&self, ty: &Type, name: &str) -> Option<FieldId> {
        let owner = self.aggregate_id(ty)?;
        let index = self
            .structs
            .get(&self.aggregate_names[owner.0])?
            .iter()
            .position(|field| field.name == name)?;
        Some(FieldId { owner, index })
    }

    pub fn variant_id(&self, ty: &Type, name: &str) -> Option<VariantId> {
        let owner = self.aggregate_id(ty)?;
        let index = self
            .enums
            .get(&self.aggregate_names[owner.0])?
            .iter()
            .position(|variant| variant.name == name)?;
        Some(VariantId { owner, index })
    }

    pub fn declaration_name(&self, id: DeclarationId) -> &str {
        match id {
            DeclarationId::Global(id) => &self.global_names[id.0],
            DeclarationId::Aggregate(id) => &self.aggregate_names[id.0],
            DeclarationId::Field(id) => &self.field(id).name,
            DeclarationId::Variant(id) => &self.variant(id).name,
        }
    }

    pub fn global_type(&self, id: GlobalId) -> &Type {
        &self.globals[&self.global_names[id.0]]
    }

    pub fn field(&self, id: FieldId) -> &Field {
        &self.structs[&self.aggregate_names[id.owner.0]][id.index]
    }

    pub fn variant(&self, id: VariantId) -> &EnumVariant {
        &self.enums[&self.aggregate_names[id.owner.0]][id.index]
    }

    pub fn function_id(&self, name: &str) -> Option<FunctionId> {
        self.function_ids.get(name).copied()
    }

    pub fn function(&self, id: FunctionId) -> &FunctionDeclaration {
        &self.functions[id.0]
    }

    pub fn lower_bodies(
        &mut self,
        program: &crate::Program,
        types: &HashMap<ExpressionId, Type>,
        expression_ids: &HashMap<usize, ExpressionId>,
        expression_spans: &HashMap<ExpressionId, Span>,
        statement_spans: &HashMap<StatementId, Span>,
        statement_ids: &HashMap<usize, StatementId>,
    ) -> Result<(), String> {
        // This whole-program adapter is identical for every function. Building
        // it per body made lowering quadratic in the imported program size.
        let expression_spans_by_address = expression_ids
            .iter()
            .filter_map(|(address, id)| expression_spans.get(id).map(|span| (*address, *span)))
            .collect::<HashMap<_, _>>();
        self.bodies = program
            .items
            .iter()
            .filter_map(|item| match item {
                crate::Item::Function(function) if !function.external => {
                    let parameter_source = program
                        .declaration_expressions
                        .get(&function.name)
                        .and_then(|source| source.children.get(2));
                    let parameter_spans = function
                        .parameters
                        .iter()
                        .enumerate()
                        .map(|(index, parameter)| {
                            let identifier = parameter_source?
                                .children
                                .get(index)?
                                .children
                                .first()?;
                            matches!(&identifier.expr, crate::Expr::Symbol(symbol) if symbol == &parameter.name)
                                .then_some(identifier.span)
                        })
                        .collect::<Vec<_>>();
                    let binding_spans = collect_simple_local_binding_spans(
                        function,
                        program,
                        &expression_spans_by_address,
                    );
                    Some((
                        function.name.clone(),
                        crate::typed_body::Body::lower(
                            function,
                            self,
                            types,
                            expression_ids,
                            expression_spans,
                            statement_spans,
                            statement_ids,
                            &binding_spans,
                            &parameter_spans,
                        ),
                    ))
                }
                _ => None,
            })
            .collect();
        self.flows = self
            .bodies
            .iter()
            .map(|(name, body)| {
                crate::typed_flow::FlowGraph::lower(body).map(|flow| (name.clone(), flow))
            })
            .collect::<Result<_, _>>()?;
        self.summarize_returned_parameter_loans();
        self.liveness = self
            .flows
            .iter()
            .map(|(name, flow)| (name.clone(), flow.liveness(&self.bodies[name])))
            .collect();
        for item in &program.items {
            if let crate::Item::Function(function) = item {
                if !function.external {
                    self.flows[&function.name].check_definite_bindings(
                        &self.bodies[&function.name],
                        function.parameters.len(),
                    )?;
                }
            }
        }
        Ok(())
    }

    /// Staged ownership summaries over the complete acyclic body call graph.
    /// Missing external bodies remain unresolved rather than implying no effect.
    #[cfg(test)]
    pub fn staged_referent_function_effects(
        &self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>, &'static str> {
        self.staged_referent_analysis(types, false, false)
            .map_err(|_| "cyclic or unresolved internal ownership summary dependencies")
    }

    #[cfg(test)]
    pub fn staged_validate_referent_replacements(
        &self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<(), StagedReferentError> {
        self.staged_referent_analysis(types, true, false)
            .map(|_| ())
    }

    #[cfg(test)]
    pub fn staged_validate_referent_uses_and_replacements(
        &self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<(), StagedReferentError> {
        self.staged_referent_analysis(types, true, true).map(|_| ())
    }

    #[cfg(test)]
    fn staged_referent_analysis(
        &self,
        types: &crate::linearcheck::LinearTypes,
        validate_replacements: bool,
        validate_uses: bool,
    ) -> Result<HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>, StagedReferentError>
    {
        use crate::typed_body::NodeKind;
        use crate::typed_flow::{FlowAction, FlowNodeId};
        let body_ids = self
            .bodies
            .keys()
            .filter_map(|name| self.function_id(name))
            .collect::<HashSet<_>>();
        let mut pending = self.bodies.keys().cloned().collect::<Vec<_>>();
        pending.sort();
        let mut summaries = HashMap::new();
        while !pending.is_empty() {
            let previous = pending.len();
            let mut failure = None;
            pending.retain(|name| {
                if failure.is_some() {
                    return true;
                }
                let body = &self.bodies[name];
                if body.nodes.iter().any(|node| {
                    matches!(&node.kind,
                    NodeKind::Form { callee: Some(callee), .. }
                    if body_ids.contains(callee) && !summaries.contains_key(callee))
                }) {
                    return true;
                }
                // A callee with no normal return terminates this path. Keep
                // original event IDs/spans while excluding its continuation
                // from loan snapshots, ownership facts, and exit summaries.
                let mut flow = self.flows[name].clone();
                for node in &mut flow.nodes {
                    let FlowAction::Evaluate(value) = node.action else {
                        continue;
                    };
                    let NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } = &body.nodes[value.0].kind
                    else {
                        continue;
                    };
                    if summaries.get(callee).is_some_and(
                        |summary: &crate::typed_flow::ReferentFunctionEffects| {
                            !summary.has_normal_return
                        },
                    ) {
                        node.successors.clear();
                    }
                }
                // All call arguments must use snapshots from this same
                // divergence-adjusted graph. Solve provenance once per body,
                // not once for every invocation in the body.
                let origins = flow.loan_origins(body);
                let mut calls = Vec::new();
                let reachable = flow.reachable();
                let mut call_reads = Vec::new();
                let mut unresolved_reads = Vec::new();
                for (index, node) in flow.nodes.iter().enumerate() {
                    let FlowAction::Evaluate(value) = node.action else {
                        continue;
                    };
                    let NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } = &body.nodes[value.0].kind
                    else {
                        continue;
                    };
                    let event = FlowNodeId(index);
                    if !reachable.contains(&event) {
                        continue;
                    }
                    let (effects, unknown) = match summaries.get(callee) {
                        Some(summary) => flow.map_referent_call_effects_with_origins(
                            body, event, value, summary, &origins,
                        ),
                        None => (Vec::new(), true),
                    };
                    calls.push((event, effects, unknown));
                    match summaries.get(callee) {
                        Some(summary) => {
                            let (mapped, unknown) = flow.map_referent_call_reads_with_origins(
                                body,
                                event,
                                value,
                                &summary.reads,
                                &origins,
                            );
                            call_reads.extend(mapped);
                            if unknown || !summary.unresolved_reads.is_empty() {
                                unresolved_reads.push(event);
                            }
                        }
                        None => unresolved_reads.push(event),
                    }
                }
                if validate_uses {
                    if let Err(conflict) =
                        flow.check_owner_consumptions_with_calls(body, types, &calls)
                    {
                        failure = Some(StagedReferentError::Use {
                            function: name.clone(),
                            conflict,
                        });
                        return true;
                    }
                }
                if validate_replacements {
                    if let Err(conflict) =
                        flow.check_referent_replacements_with_calls(body, types, self, &calls)
                    {
                        failure = Some(StagedReferentError::Replacement {
                            function: name.clone(),
                            conflict,
                        });
                        return true;
                    }
                }
                let mut summary = flow.referent_function_effects_with_calls(body, types, &calls);
                summary.reads.extend(call_reads);
                summary.unresolved_reads.extend(unresolved_reads);
                summaries.insert(self.function_id(name).unwrap(), summary);
                false
            });
            if let Some(failure) = failure {
                return Err(failure);
            }
            if pending.len() == previous {
                return Err(StagedReferentError::Dependency);
            }
        }
        Ok(summaries)
    }

    /// Compute interprocedural loan summaries over the acyclic checked call
    /// graph. Process callees before callers so each body is analyzed once,
    /// preserving parameter and aggregate-slot identities without a repeated
    /// whole-program fixed-point pass.
    fn summarize_returned_parameter_loans(&mut self) {
        let mut names = self.bodies.keys().cloned().collect::<Vec<_>>();
        names.sort();
        let mut parameter_slots = HashMap::new();
        for name in &names {
            let body = &self.bodies[name];
            let mut slots = vec![Vec::new(); body.bindings.len()];
            for (index, binding) in body.bindings.iter().take(body.parameter_count).enumerate() {
                self.collect_parameter_loan_slots(
                    &binding.ty,
                    &mut Vec::new(),
                    &mut HashSet::new(),
                    &mut slots[index],
                );
            }
            parameter_slots.insert(name.clone(), slots);
        }
        for (name, slots) in parameter_slots {
            self.bodies.get_mut(&name).unwrap().parameter_loan_slots = slots;
        }

        let names_by_id = self
            .function_ids
            .iter()
            .map(|(name, id)| (*id, name.clone()))
            .collect::<HashMap<_, _>>();
        let mut remaining_dependencies = HashMap::new();
        let mut callers = HashMap::<String, Vec<String>>::new();
        for name in &names {
            let body = &self.bodies[name];
            let dependencies = body
                .nodes
                .iter()
                .filter_map(|node| match &node.kind {
                    crate::typed_body::NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } => names_by_id
                        .get(callee)
                        .filter(|name| self.bodies.contains_key(*name)),
                    _ => None,
                })
                .cloned()
                .collect::<HashSet<_>>();
            for dependency in &dependencies {
                callers
                    .entry(dependency.clone())
                    .or_default()
                    .push(name.clone());
            }
            remaining_dependencies.insert(name.clone(), dependencies.len());
        }
        for users in callers.values_mut() {
            users.sort();
            users.dedup();
        }
        let mut ready = names
            .iter()
            .filter(|name| remaining_dependencies[*name] == 0)
            .cloned()
            .collect::<VecDeque<_>>();
        let mut order = Vec::with_capacity(names.len());
        while let Some(name) = ready.pop_front() {
            order.push(name.clone());
            if let Some(users) = callers.get(&name) {
                for user in users {
                    let remaining = remaining_dependencies.get_mut(user).unwrap();
                    *remaining -= 1;
                    if *remaining == 0 {
                        ready.push_back(user.clone());
                    }
                }
            }
        }
        // Recursive calls are rejected before typed body lowering. Keep a
        // deterministic fallback order so malformed internal states cannot
        // panic while constructing diagnostics.
        if order.len() != names.len() {
            let unresolved = names
                .iter()
                .filter(|name| !order.contains(name))
                .cloned()
                .collect::<Vec<_>>();
            order.extend(unresolved);
        }

        let mut summaries = HashMap::new();
        for name in order {
            // Loan transfer only consults direct callees. Copying every summary
            // accumulated so far for every body was another quadratic pass.
            let needed = self.bodies[&name]
                .nodes
                .iter()
                .filter_map(|node| match &node.kind {
                    crate::typed_body::NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } => summaries.get(callee).map(
                        |summary: &Vec<crate::typed_body::ParameterLoanSummary>| {
                            (*callee, summary.clone())
                        },
                    ),
                    _ => None,
                })
                .collect();
            self.bodies.get_mut(&name).unwrap().call_return_origins = Arc::new(needed);
            let body = &self.bodies[&name];
            let flow = &self.flows[&name];
            let origins = flow.loan_origins(body);
            let mut returned = Vec::new();
            for (index, node) in flow.nodes.iter().enumerate() {
                let crate::typed_flow::FlowAction::Return(Some(value)) = &node.action else {
                    continue;
                };
                for origin in
                    origins.value_before(body, flow, crate::typed_flow::FlowNodeId(index), *value)
                {
                    let (parameter, global) = match origin.place.root {
                        crate::typed_body::PlaceRoot::Parameter(binding) => (binding.0, None),
                        crate::typed_body::PlaceRoot::Global(global) => (0, Some(global)),
                        _ => continue,
                    };
                    let summary = crate::typed_body::ParameterLoanSummary {
                        parameter,
                        global,
                        mutable: origin.mutable,
                        pinned: origin.pinned,
                        lifetime_only: origin.lifetime_only,
                        referent_projection: origin.place.segments,
                        input_storage: origin.parameter_storage.unwrap_or_default(),
                        storage: origin.storage,
                    };
                    if !returned.contains(&summary) {
                        returned.push(summary);
                    }
                }
            }
            if let Some(id) = self.function_id(&name) {
                // An empty summary distinguishes a known body with no
                // parameter-derived loans from an unavailable external body.
                summaries.insert(id, returned);
            }
        }
        let shared = Arc::new(summaries);
        for body in self.bodies.values_mut() {
            body.call_return_origins = shared.clone();
        }
    }

    fn collect_parameter_loan_slots(
        &self,
        ty: &Type,
        path: &mut Vec<crate::typed_place::Segment>,
        seen: &mut HashSet<String>,
        output: &mut Vec<crate::typed_body::ParameterLoanSeed>,
    ) {
        use crate::typed_place::Segment;
        match ty {
            Type::Reference { mutable, .. } | Type::PinnedReference { mutable, .. } => {
                output.push(crate::typed_body::ParameterLoanSeed {
                    mutable: *mutable,
                    pinned: matches!(ty, Type::PinnedReference { .. }),
                    storage: path.clone(),
                })
            }
            Type::Slice(_) | Type::MutableSlice(_) => {
                output.push(crate::typed_body::ParameterLoanSeed {
                    mutable: matches!(ty, Type::MutableSlice(_)),
                    pinned: false,
                    storage: path.clone(),
                });
            }
            Type::Array(element, length) if *length > 0 => {
                path.push(if *length == 1 {
                    Segment::Index(0)
                } else {
                    Segment::DynamicIndex
                });
                self.collect_parameter_loan_slots(element, path, seen, output);
                path.pop();
            }
            Type::Tuple(elements) => {
                for (index, element) in elements.iter().enumerate() {
                    path.push(Segment::Tuple(index));
                    self.collect_parameter_loan_slots(element, path, seen, output);
                    path.pop();
                }
            }
            Type::Named(name) if seen.insert(name.clone()) => {
                if let Some(fields) = self.structs.get(name) {
                    if let Some(owner) = self.aggregate_ids.get(name).copied() {
                        for (index, field) in fields.iter().enumerate() {
                            path.push(Segment::Field(FieldId { owner, index }));
                            self.collect_parameter_loan_slots(&field.ty, path, seen, output);
                            path.pop();
                        }
                    }
                }
                if let Some(variants) = self.enums.get(name) {
                    let owner = self.aggregate_ids.get(name).copied();
                    for (variant_index, variant) in variants.iter().enumerate() {
                        let Some(owner) = owner else { continue };
                        let id = VariantId {
                            owner,
                            index: variant_index,
                        };
                        for (index, field) in variant.fields.iter().enumerate() {
                            path.push(Segment::Payload(id, index));
                            self.collect_parameter_loan_slots(field, path, seen, output);
                            path.pop();
                        }
                    }
                }
                seen.remove(name);
            }
            _ => {}
        }
    }
}

/// Shared by validation and the not-yet-migrated AST lowering paths. In
/// particular, aliases must resolve inside *every* type constructor.
pub(crate) fn resolve_type(ty: &Type, aliases: &HashMap<String, Type>) -> Result<Type, String> {
    fn resolve(
        ty: &Type,
        aliases: &HashMap<String, Type>,
        seen: &mut HashSet<String>,
    ) -> Result<Type, String> {
        Ok(match ty {
            Type::Named(name) => {
                let Some(target) = aliases.get(name) else {
                    return Ok(ty.clone());
                };
                if !seen.insert(name.clone()) {
                    return Err(format!("type alias '{name}' is recursive"));
                }
                let result = resolve(target, aliases, seen);
                seen.remove(name);
                return result;
            }
            Type::Array(element, length) => {
                Type::Array(Box::new(resolve(element, aliases, seen)?), *length)
            }
            Type::Tuple(fields) => Type::Tuple(
                fields
                    .iter()
                    .map(|field| resolve(field, aliases, seen))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Slice(element) => Type::Slice(Box::new(resolve(element, aliases, seen)?)),
            Type::MutableSlice(element) => {
                Type::MutableSlice(Box::new(resolve(element, aliases, seen)?))
            }
            Type::Atomic(element) => Type::Atomic(Box::new(resolve(element, aliases, seen)?)),
            Type::Reference { mutable, target } => Type::Reference {
                mutable: *mutable,
                target: Box::new(resolve(target, aliases, seen)?),
            },
            Type::PinnedReference { mutable, target } => Type::PinnedReference {
                mutable: *mutable,
                target: Box::new(resolve(target, aliases, seen)?),
            },
            Type::RawPointer { mutable, target } => Type::RawPointer {
                mutable: *mutable,
                target: Box::new(resolve(target, aliases, seen)?),
            },
            _ => ty.clone(),
        })
    }
    resolve(ty, aliases, &mut HashSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expression_ids_are_dense_and_stable_across_fresh_parses() {
        let source = "(#fn main () u64
          (#let value u64 1u64)
          (#return (#u64.+.wrap value 2u64)))";
        let first = crate::parse_program(source).unwrap();
        let second = crate::parse_program(source).unwrap();
        let first_ids = expression_ids(&first);
        let second_ids = expression_ids(&second);
        fn returned(program: &crate::Program) -> &crate::Expr {
            let crate::Item::Function(function) = &program.items[0] else {
                unreachable!()
            };
            let crate::Statement::Return(Some(value)) = function.body.last().unwrap() else {
                unreachable!()
            };
            value
        }
        let first_return = returned(&first);
        let second_return = returned(&second);
        assert_eq!(
            first_ids[&(std::ptr::from_ref(first_return) as usize)],
            second_ids[&(std::ptr::from_ref(second_return) as usize)]
        );
        let mut dense = first_ids.values().map(|id| id.0).collect::<Vec<_>>();
        dense.sort_unstable();
        assert_eq!(dense, (0..dense.len()).collect::<Vec<_>>());
    }

    #[test]
    fn statement_ids_are_dense_and_stable_across_nested_control_flow() {
        let source = "(#fn main () u64
          (#let value u64 (#block (#let nested u64 1u64) nested))
          (#let result u64 (#label outer (#loop (#break-to outer 2u64))))
          (#return (#u64.+.wrap value result)))";
        let first = crate::parse_program(source).unwrap();
        let second = crate::parse_program(source).unwrap();
        let first_ids = statement_ids(&first);
        let second_ids = statement_ids(&second);
        let crate::Item::Function(first_function) = &first.items[0] else {
            unreachable!()
        };
        let crate::Item::Function(second_function) = &second.items[0] else {
            unreachable!()
        };
        assert_eq!(
            first_ids[&(std::ptr::from_ref(&first_function.body[0]) as usize)],
            second_ids[&(std::ptr::from_ref(&second_function.body[0]) as usize)]
        );
        assert_eq!(
            first_ids[&(std::ptr::from_ref(&first_function.body[1]) as usize)],
            second_ids[&(std::ptr::from_ref(&second_function.body[1]) as usize)]
        );
        let mut dense = first_ids.values().map(|id| id.0).collect::<Vec<_>>();
        dense.sort_unstable();
        assert_eq!(dense, (0..dense.len()).collect::<Vec<_>>());
        assert!(
            dense.len() >= 6,
            "nested block/loop statements must receive IDs"
        );
    }

    #[test]
    fn declaration_ids_resolve_metadata_and_ignore_top_level_declaration_order() {
        let forms = [
            "(#struct Z ((z u64) (a u32)))",
            "(#struct A.Type ((a u8)))",
            "(#enum M ((Second u16) First))",
            "(#const Zed u64 7u64)",
            "(#const Alpha.answer u64 42u64)",
            "(#type ZAlias Z)",
        ];
        for forms in [forms.to_vec(), forms.into_iter().rev().collect()] {
            let source = format!(
                "{} (#fn main () u64 (#return Alpha.answer))",
                forms.join(" ")
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let declarations = checked.declarations();
            assert_eq!(declarations.global_id("Alpha.answer"), Some(GlobalId(0)));
            assert_eq!(declarations.global_id("Zed"), Some(GlobalId(1)));
            assert_eq!(declarations.global_type(GlobalId(0)), &Type::U64);
            let alias = Type::Reference {
                mutable: true,
                target: Box::new(Type::Named("ZAlias".into())),
            };
            let field = declarations.field_id(&alias, "a").unwrap();
            assert_eq!(
                field,
                FieldId {
                    owner: AggregateId(2),
                    index: 1
                }
            );
            assert_eq!(declarations.field(field).ty, Type::U32);
            assert_eq!(
                declarations.declaration_name(DeclarationId::Field(field)),
                "a"
            );
            let other = declarations
                .field_id(&Type::Named("A.Type".into()), "a")
                .unwrap();
            assert_ne!(field, other);
            assert_eq!(declarations.field(other).ty, Type::U8);
            let variant = declarations
                .variant_id(&Type::Named("M".into()), "Second")
                .unwrap();
            assert_eq!(
                variant,
                VariantId {
                    owner: AggregateId(1),
                    index: 0
                }
            );
            assert_eq!(declarations.variant(variant).fields, vec![Type::U16]);
            assert_eq!(
                declarations.declaration_name(DeclarationId::Variant(variant)),
                "Second"
            );
        }
    }

    fn containers(ty: Type) -> Vec<Type> {
        vec![
            Type::Array(Box::new(ty.clone()), 2),
            Type::Tuple(vec![ty.clone(), ty.clone()]),
            Type::Slice(Box::new(ty.clone())),
            Type::MutableSlice(Box::new(ty.clone())),
            Type::Atomic(Box::new(ty.clone())),
            Type::Reference {
                mutable: false,
                target: Box::new(ty.clone()),
            },
            Type::Reference {
                mutable: true,
                target: Box::new(ty.clone()),
            },
            Type::RawPointer {
                mutable: false,
                target: Box::new(ty.clone()),
            },
            Type::RawPointer {
                mutable: true,
                target: Box::new(ty),
            },
        ]
    }

    #[test]
    fn aliases_resolve_inside_every_container_and_reject_nested_cycles() {
        let alias = Type::Named("Word".into());
        let aliases = HashMap::from([
            ("Word".into(), Type::Named("Base".into())),
            ("Base".into(), Type::U64),
        ]);
        for (input, expected) in containers(alias.clone()).iter().zip(containers(Type::U64)) {
            assert_eq!(resolve_type(input, &aliases).unwrap(), expected);
        }
        for container in containers(alias.clone()) {
            let aliases = HashMap::from([("Word".into(), container)]);
            assert_eq!(
                resolve_type(&alias, &aliases).unwrap_err(),
                "type alias 'Word' is recursive"
            );
        }
    }

    #[test]
    fn checked_declarations_retain_types_spans_and_deterministic_function_ids() {
        let source = "(#type Word u64)
            (#struct Pair ((left Word) (right (#ref Word))))
            (#const Answer Word 42u64)
            (#fn z ((value (#ref Word))) Word (#return (#deref value)))
            (#fn main () Word (#return Answer))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        assert_eq!(declarations.globals["Answer"], Type::U64);
        assert_eq!(declarations.structs["Pair"][0].ty, Type::U64);
        assert_eq!(
            declarations.structs["Pair"][1].ty,
            Type::Reference {
                mutable: false,
                target: Box::new(Type::U64)
            }
        );
        assert_eq!(declarations.function_id("main"), Some(FunctionId(0)));
        let id = declarations.function_id("z").unwrap();
        let function = declarations.function(id);
        assert_eq!(function.signature.return_type, Type::U64);
        assert_eq!(
            function.signature.parameters,
            vec![Type::Reference {
                mutable: false,
                target: Box::new(Type::U64)
            }]
        );
        let span = function.span.unwrap();
        assert!(source[span.start..span.end].contains("z"));
        let independent = crate::parse_program(source).unwrap();
        let checked_again = crate::CheckedProgram::validate(&independent).unwrap();
        assert_eq!(checked_again.declarations().function_id("z"), Some(id));
        let target = crate::TargetDescription::X86_64_SYSTEM_V;
        assert_eq!(
            checked.generate_assembly(target).unwrap(),
            checked_again.generate_assembly(target).unwrap()
        );
    }
}
