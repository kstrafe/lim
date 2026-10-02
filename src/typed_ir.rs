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

pub(crate) struct ThreadCaptureSchema {
    pub worker: FunctionId,
    pub worker_name: String,
    pub parameters: Vec<Type>,
}

fn referent_free_abi_value(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Unit
            | Type::Bool
            | Type::Char
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Isize
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::Usize
            | Type::F32
            | Type::F64
            | Type::RawPointer { .. }
    )
}

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
    external_function_ids: HashSet<FunctionId>,
    pub thread_capture_schemas: HashMap<String, ThreadCaptureSchema>,
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
            external_function_ids: HashSet::new(),
            thread_capture_schemas: HashMap::new(),
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
        {
            self.thread_capture_schemas = program
                .items
                .iter()
                .filter_map(|item| {
                    let crate::Item::ThreadTask { name, worker, .. } = item else {
                        return None;
                    };
                    let worker_name = worker.clone();
                    let worker = self.function_id(worker)?;
                    Some((
                        name.clone(),
                        ThreadCaptureSchema {
                            worker,
                            worker_name,
                            parameters: self.function(worker).signature.parameters.clone(),
                        },
                    ))
                })
                .collect();
            self.external_function_ids = program
                .items
                .iter()
                .filter_map(|item| match item {
                    crate::Item::Function(function) if function.external => {
                        self.function_id(&function.name)
                    }
                    _ => None,
                })
                .collect();
        }
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
        {
            let linear = crate::linearcheck::LinearTypes::from_program(program);
            for body in self.bodies.values_mut() {
                body.consuming_pin_reads = body.nodes.iter().enumerate().filter_map(|(index, node)| {
                    (matches!(&node.kind, crate::typed_body::NodeKind::Form { head, .. } if head == "pin-read")
                        && node.ty.as_ref().is_some_and(|ty| linear.is_linear(ty)))
                        .then_some(crate::typed_body::NodeId(index))
                }).collect();
                body.consuming_releases = body
                    .nodes
                    .iter()
                    .enumerate()
                    .filter_map(|(index, node)| match &node.kind {
                        crate::typed_body::NodeKind::Form { head, children, .. }
                            if matches!(head.as_str(), "drop" | "forget")
                                && children.len() == 2 =>
                        {
                            body.nodes[children[1].0]
                                .ty
                                .as_ref()
                                .is_some_and(|ty| linear.is_linear(ty))
                                .then_some(crate::typed_body::NodeId(index))
                        }
                        _ => None,
                    })
                    .collect();
            }
        }
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
    /// Opaque checked-reference-bearing external bodies remain unresolved.
    #[cfg(test)]
    pub fn staged_referent_function_effects(
        &self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>, &'static str> {
        self.staged_referent_analysis(types, false, false, false, None)
            .map_err(|_| "cyclic or unresolved internal ownership summary dependencies")
    }

    #[cfg(test)]
    pub fn staged_validate_referent_replacements(
        &self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<(), StagedReferentError> {
        self.staged_referent_analysis(types, true, false, false, None)
            .map(|_| ())
    }

    #[cfg(test)]
    pub fn staged_validate_referent_uses_and_replacements(
        &self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<(), StagedReferentError> {
        self.staged_referent_analysis(types, true, true, false, None)
            .map(|_| ())
    }

    /// Infer initializer entry requirements bottom-up. This staging API does
    /// not establish owned exits or initialized escaping-reference contracts.
    #[cfg(test)]
    pub fn staged_referent_entry_contracts(
        &self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>, StagedReferentError>
    {
        self.staged_referent_analysis(types, false, false, true, None)
    }

    /// Prepare actual parameter contents and interprocedural store/clear
    /// summaries before enforcing initialized entry and escape contracts.
    /// Keeping these phases together avoids validating later calls against
    /// the legacy symbolic-load summaries. Legacy ownership and borrowing
    /// validation remain independent gates during the frontend migration.
    pub fn check_referent_entry_contracts(
        &mut self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>, StagedReferentError>
    {
        self.summarize_parameter_loans_with_contents(true);
        self.staged_referent_analysis(types, false, false, true, None)
    }

    #[cfg(test)]
    pub fn staged_contents_referent_entry_contracts(
        &mut self,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>, StagedReferentError>
    {
        self.check_referent_entry_contracts(types)
    }

    /// Reuse ordinary contents-aware call staging for suspension storage.
    /// Snapshot selection is not a successful program-validation boundary;
    /// callers must still enforce the ordinary ownership and borrowing gates.
    /// Collect only requested bodies, avoiding a new per-body storage solve
    /// for unrelated imports or ordinary compilation without async lowering.
    #[cfg_attr(not(test), allow(dead_code))] // General frame emission will consume these facts.
    pub fn suspension_storage_facts(
        &mut self,
        types: &crate::linearcheck::LinearTypes,
        names: &HashSet<String>,
    ) -> Result<HashMap<String, crate::typed_flow::StorageFacts>, StagedReferentError> {
        self.summarize_parameter_loans_with_contents(true);
        let mut storage = HashMap::new();
        self.staged_referent_analysis(types, false, false, true, Some((names, &mut storage)))?;
        Ok(storage)
    }

    fn staged_referent_analysis(
        &self,
        types: &crate::linearcheck::LinearTypes,
        validate_replacements: bool,
        validate_uses: bool,
        infer_entry_contracts: bool,
        mut storage: Option<(
            &HashSet<String>,
            &mut HashMap<String, crate::typed_flow::StorageFacts>,
        )>,
    ) -> Result<HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>, StagedReferentError>
    {
        use crate::typed_body::NodeKind;
        use crate::typed_flow::{FlowAction, FlowNodeId};
        // Clear every cache before inference, including callers we may never
        // reach if a callee fails in this entry-assumption mode.
        for body in self.bodies.values() {
            body.call_variant_exits.borrow_mut().clear();
            body.call_output_variant_exits.borrow_mut().clear();
        }
        let body_ids = self
            .bodies
            .keys()
            .filter_map(|name| self.function_id(name))
            .collect::<HashSet<_>>();
        let mut pending = self.bodies.keys().cloned().collect::<Vec<_>>();
        pending.sort();
        let mut names_by_id = pending
            .iter()
            .map(|name| (self.function_id(name).unwrap(), name.clone()))
            .collect::<HashMap<_, _>>();
        let thread_workers = self.thread_operation_workers();
        // Spawn parameters have the worker's exact signature. Reuse its
        // checked referent schema for entry obligations, never for join.
        for (task, captures) in &self.thread_capture_schemas {
            if self.bodies.contains_key(&captures.worker_name) {
                if let Some(spawn) = self.function_id(&format!("{task}-spawn")) {
                    names_by_id.insert(spawn, captures.worker_name.clone());
                }
            }
        }
        let mut summaries = HashMap::new();
        // This is a referent contract, not a purity claim about unsafe code.
        let mut output_summaries = crate::typed_body::OutputVariantMap::new();
        // Scalars and raw pointers carry no checked parameter referents. Raw
        // memory validity remains the caller's explicit unsafe obligation;
        // these summaries cannot initialize storage or manufacture safe loans.
        // Checked-reference-bearing boundaries still require a real contract.
        for (name, id) in &self.function_ids {
            let signature = &self.functions[id.0].signature;
            if self.external_function_ids.contains(id)
                && !self.bodies.contains_key(name)
                && signature.type_parameters.is_empty()
                && signature.parameters.iter().all(referent_free_abi_value)
                && referent_free_abi_value(&signature.return_type)
            {
                summaries.insert(
                    *id,
                    crate::typed_flow::ReferentFunctionEffects {
                        has_normal_return: true,
                        effects: Vec::new(),
                        unresolved: Vec::new(),
                        reads: Vec::new(),
                        unresolved_reads: Vec::new(),
                        entry_reads: Vec::new(),
                        consuming_accesses: Vec::new(),
                        restored_from_consumed_entry: Vec::new(),
                        consumed_entry: Vec::new(),
                        effects_from_consumed_entry: Vec::new(),
                        variant_exits: HashMap::new(),
                    },
                );
            }
        }
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
                    if {
                        let dependency = thread_workers.get(callee).unwrap_or(callee);
                        body_ids.contains(dependency) && !summaries.contains_key(dependency)
                    })
                }) {
                    return true;
                }
                self.staged_add_thread_operation_contracts(&mut summaries, infer_entry_contracts);
                let mut output_contracts = body.nodes.iter().filter_map(|node| {
                    let NodeKind::Form { callee: Some(callee), .. } = node.kind else { return None; };
                    output_summaries.get(&callee).map(|groups| (callee, groups.clone()))
                }).collect::<HashMap<_, _>>();
                for (task, captures) in &self.thread_capture_schemas {
                    let (
                        Some(worker_body),
                        Some(worker_outputs),
                        Some(join),
                        Some(owner),
                        Some(join_ok),
                    ) = (
                        self.bodies.get(&captures.worker_name),
                        output_summaries.get(&captures.worker),
                        self.function_id(&format!("{task}-join")),
                        self.aggregate_id(&Type::Named(task.clone())),
                        self.variant_id(
                            &Type::Named(format!("{task}-join-result")),
                            &format!("{task}-join-ok"),
                        ),
                    )
                    else {
                        continue;
                    };
                    // Require the same actual-worker operation contract as the
                    // outer join. A missing worker never grants completion.
                    if !summaries.contains_key(&join) || !body.nodes.iter().any(|node| {
                        matches!(node.kind, NodeKind::Form { callee: Some(callee), .. } if callee == join)
                    }) {
                        continue;
                    }
                    let captured = worker_outputs.iter().map(|((path, variant), exit)| {
                        let mut nested = vec![crate::typed_place::Segment::Payload(join_ok, 0)];
                        nested.extend_from_slice(path);
                        Some(((nested, *variant), crate::thread_contract::capture_variant_exit(
                            owner, worker_body.parameter_count, exit,
                        )?))
                    }).collect::<Option<HashMap<_, _>>>();
                    let Some(captured) = captured else {
                        continue;
                    };
                    output_contracts.insert(join, captured);
                }
                *body.call_output_variant_exits.borrow_mut() = output_contracts;
                *body.call_variant_exits.borrow_mut() = body
                    .nodes
                    .iter()
                    .filter_map(|node| {
                        let NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } = &node.kind
                        else {
                            return None;
                        };
                        summaries.get(callee).map(
                            |summary: &crate::typed_flow::ReferentFunctionEffects| {
                                (*callee, summary.variant_exits.clone())
                            },
                        )
                    })
                    .collect();
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
                flow.prepare_storage_variant_bounds(body, &origins);
                let mut calls = Vec::new();
                let reachable = flow.reachable();
                let mut call_reads = Vec::new();
                let mut call_entry_reads = Vec::new();
                let mut consuming_accesses = Vec::new();
                let mut restorations = Vec::new();
                let mut consumed_inputs = Vec::new();
                let mut possible_restorations = Vec::new();
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
                            if let Some(callee_name) = names_by_id.get(callee) {
                                if infer_entry_contracts {
                                    let (mapped, unknown) = flow.map_referent_call_consumed_entry(
                                        body,
                                        event,
                                        value,
                                        &self.bodies[callee_name],
                                        &summary.consumed_entry,
                                    );
                                    consumed_inputs.push((event, mapped, unknown));
                                    let (mapped, unknown) = flow.map_referent_call_consumed_entry(
                                        body,
                                        event,
                                        value,
                                        &self.bodies[callee_name],
                                        &summary.possibly_initialized_inputs(),
                                    );
                                    possible_restorations.push((event, mapped));
                                    if unknown {
                                        unresolved_reads.push(event);
                                    }
                                }
                                let (mapped, unknown) = flow.map_referent_call_restorations(
                                    body,
                                    event,
                                    value,
                                    &self.bodies[callee_name],
                                    &summary.restored_from_consumed_entry,
                                );
                                if !unknown {
                                    restorations.push((event, mapped));
                                }
                            }
                            let (mapped, unknown) = flow
                                .map_initialized_referent_call_reads_with_origins(
                                    body,
                                    event,
                                    value,
                                    &summary.reads,
                                    &origins,
                                );
                            call_reads.extend(mapped);
                            let (entry_reads, entry_unknown) = flow
                                .map_initialized_referent_call_reads_with_origins(
                                    body,
                                    event,
                                    value,
                                    &summary.entry_reads,
                                    &origins,
                                );
                            call_entry_reads.extend(entry_reads);
                            let (mapped_accesses, access_unknown) = flow
                                .map_referent_call_reads_with_origins(
                                    body,
                                    event,
                                    value,
                                    &summary.consuming_accesses,
                                    &origins,
                                );
                            consuming_accesses.extend(mapped_accesses);
                            if access_unknown {
                                unresolved_reads.push(event);
                            }
                            if unknown || entry_unknown || !summary.unresolved_reads.is_empty() {
                                unresolved_reads.push(event);
                            }
                        }
                        None => unresolved_reads.push(event),
                    }
                }
                if validate_uses || infer_entry_contracts {
                    if let Err(conflict) = flow.check_pending_task_loans(
                        body,
                        types,
                        &origins,
                        &call_reads,
                        &consuming_accesses,
                    ) {
                        failure = Some(StagedReferentError::Use {
                            function: name.clone(),
                            conflict,
                        });
                        return true;
                    }
                }
                let consumed_entry = if infer_entry_contracts {
                    let facts = crate::typed_flow::ReferentCallFacts {
                        effects: calls,
                        restorations,
                        consumed_inputs,
                        read_inputs: call_entry_reads,
                        consuming_accesses,
                        unresolved_inputs: unresolved_reads.clone(),
                        possible_restorations: Some(possible_restorations),
                    };
                    let result = flow
                        .infer_referent_consumed_entry_with_call_facts(body, types, self, &facts);
                    calls = facts.effects;
                    restorations = facts.restorations;
                    consumed_inputs = facts.consumed_inputs;
                    possible_restorations = facts.possible_restorations.unwrap();
                    call_entry_reads = facts.read_inputs;
                    consuming_accesses = facts.consuming_accesses;
                    match result {
                        Ok(entry) => entry,
                        Err(conflict) => {
                            failure = Some(StagedReferentError::Use {
                                function: name.clone(),
                                conflict,
                            });
                            return true;
                        }
                    }
                } else {
                    Vec::new()
                };
                if validate_uses {
                    if let Err(conflict) = flow
                        .check_owner_consumptions_with_calls(body, types, &calls)
                        .and_then(|_| {
                            flow.check_referent_call_entry_reads(
                                body,
                                types,
                                &calls,
                                &call_entry_reads,
                            )
                        })
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
                let mut summary = flow.referent_function_effects_with_restorations(
                    body,
                    types,
                    &calls,
                    &restorations,
                );
                let (mut entry_reads, _) = flow.referent_reads(body);
                // Consuming an entry value also requires initialized storage,
                // even when a later trap or restoration erases exit effects.
                // The filter below excludes accesses preceded by proven
                // initialization, so initializer-consumer helpers stay valid.
                entry_reads.extend(summary.consuming_accesses.iter().map(|access| {
                    crate::typed_flow::ReferentRead {
                        event: access.event,
                        place: access.place.clone(),
                        input_storage: access.input_storage.clone(),
                        referent_projection: access.referent_projection.clone(),
                        span: access.span,
                    }
                }));
                entry_reads.extend(call_entry_reads);
                summary.entry_reads = flow.filter_referent_entry_reads_with_restorations(
                    body,
                    types,
                    entry_reads,
                    &calls,
                    &restorations,
                );
                summary.restored_from_consumed_entry = flow
                    .referent_restoration_guarantees_with_calls(body, types, &calls, &restorations);
                if infer_entry_contracts {
                    summary.effects_from_consumed_entry = flow.referent_exit_state_from_entry(
                        body,
                        types,
                        &calls,
                        &restorations,
                        &consumed_entry,
                        &possible_restorations,
                    );
                }
                if body.staged_parameter_contents {
                    let outcomes = flow.referent_output_variant_exit_effects(
                        body,
                        types,
                        &calls,
                        &restorations,
                        infer_entry_contracts.then_some(consumed_entry.as_slice()),
                        &possible_restorations,
                    );
                    summary.variant_exits = outcomes.iter().filter_map(|((path, variant), exit)| {
                        path.is_empty().then_some((*variant, exit.clone()))
                    }).collect();
                    output_summaries.insert(self.function_id(name).unwrap(), outcomes);
                }
                summary.consumed_entry = consumed_entry;
                summary.reads.extend(call_reads);
                summary.consuming_accesses.extend(consuming_accesses);
                summary.unresolved_reads.extend(unresolved_reads);
                if let Some((requested, snapshots)) = storage.as_mut() {
                    if requested.contains(name) {
                        let moves = flow.referent_consumptions_with_partial_restorations(
                            body,
                            types,
                            &calls,
                            &restorations,
                            &summary.consumed_entry,
                            &possible_restorations,
                        );
                        snapshots.insert(name.clone(), crate::typed_flow::StorageFacts {
                            flow,
                            origins,
                            moves,
                            entry_only: false,
                        });
                    }
                }
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
        self.summarize_parameter_loans_with_contents(false);
    }

    /// Test entry point for recomputing actual parameter-content summaries
    /// independently of the production initialization/restoration gate.
    #[cfg(test)]
    pub fn staged_parameter_contents_summaries(&mut self) {
        self.summarize_parameter_loans_with_contents(true);
    }

    fn summarize_parameter_loans_with_contents(&mut self, include_parameter_contents: bool) {
        let mut preserves_tags = HashSet::new();
        for flow in self.flows.values_mut() {
            flow.restore_variant_paths();
        }
        if include_parameter_contents {
            loop {
                let count = preserves_tags.len();
                for (name, body) in &self.bodies {
                    let id = self.function_id(name).unwrap();
                    if !preserves_tags.contains(&id)
                        && self.flows[name].preserves_variant_tags(body, &preserves_tags)
                    {
                        preserves_tags.insert(id);
                    }
                }
                if preserves_tags.len() == count {
                    break;
                }
            }
        }
        for body in self.bodies.values_mut() {
            body.staged_parameter_contents = include_parameter_contents;
            body.call_preserves_variant_tags = Arc::new(
                body.nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        crate::typed_body::NodeKind::Form {
                            callee: Some(id), ..
                        } if preserves_tags.contains(id) => Some(*id),
                        _ => None,
                    })
                    .collect(),
            );
        }
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
                    false,
                    false,
                );
            }
            parameter_slots.insert(name.clone(), slots);
        }
        for (name, slots) in parameter_slots {
            self.bodies.get_mut(&name).unwrap().parameter_loan_slots = slots;
        }
        for name in &names {
            let body = &self.bodies[name];
            let mut schema = vec![Vec::new(); body.bindings.len()];
            for (index, binding) in body.bindings.iter().take(body.parameter_count).enumerate() {
                self.collect_parameter_loan_slots(
                    &binding.ty,
                    &mut Vec::new(),
                    &mut HashSet::new(),
                    &mut schema[index],
                    false,
                    true,
                );
            }
            self.bodies
                .get_mut(name)
                .unwrap()
                .parameter_referent_loan_slots = schema;
        }

        let names_by_id = self
            .function_ids
            .iter()
            .map(|(name, id)| (*id, name.clone()))
            .collect::<HashMap<_, _>>();
        let mut remaining_dependencies = HashMap::new();
        let mut callers = HashMap::<String, Vec<String>>::new();
        let thread_workers = self.thread_operation_workers();
        for name in &names {
            let body = &self.bodies[name];
            let dependencies = body
                .nodes
                .iter()
                .filter_map(|node| match &node.kind {
                    crate::typed_body::NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } => {
                        let callee = thread_workers.get(callee).unwrap_or(callee);
                        names_by_id
                            .get(callee)
                            .filter(|name| self.bodies.contains_key(*name))
                    }
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
        let mut store_summaries = HashMap::new();
        let mut clear_summaries =
            HashMap::<FunctionId, Vec<crate::typed_body::ParameterLoanSummary>>::new();
        let mut clear_variants = HashMap::<
            FunctionId,
            HashMap<VariantId, Vec<crate::typed_body::ParameterLoanSummary>>,
        >::new();
        let mut return_variants =
            HashMap::<FunctionId, HashMap<Vec<crate::typed_place::Segment>, VariantId>>::new();
        let mut return_bounds = HashMap::<FunctionId, crate::typed_flow::VariantBounds>::new();
        let mut store_variants = HashMap::<
            FunctionId,
            HashMap<VariantId, Vec<crate::typed_body::ParameterStoreSummary>>,
        >::new();
        let mut output_store_variants = crate::typed_body::OutputVariantMap::new();
        let mut output_clear_variants = crate::typed_body::OutputVariantMap::new();
        {
            let (origins, bounds) = self.thread_call_return_metadata();
            summaries.extend(origins);
            return_bounds.extend(bounds);
        }
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
            let reference_slots = if include_parameter_contents {
                self.bodies[&name]
                    .nodes
                    .iter()
                    .filter_map(|node| {
                        let crate::typed_body::NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } = node.kind
                        else {
                            return None;
                        };
                        if !names_by_id
                            .get(&callee)
                            .is_some_and(|name| self.bodies.contains_key(name))
                        {
                            return None;
                        }
                        let ty = node.ty.as_ref()?;
                        Some((
                            callee,
                            self.reference_storage_slots(ty)
                                .into_iter()
                                .map(|slot| slot.storage)
                                .collect(),
                        ))
                    })
                    .collect()
            } else {
                HashMap::new()
            };
            self.bodies
                .get_mut(&name)
                .unwrap()
                .call_return_reference_slots = Arc::new(reference_slots);
            let needed_stores = self.bodies[&name]
                .nodes
                .iter()
                .filter_map(|node| match &node.kind {
                    crate::typed_body::NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } => store_summaries.get(callee).map(
                        |summary: &Vec<crate::typed_body::ParameterStoreSummary>| {
                            (*callee, summary.clone())
                        },
                    ),
                    _ => None,
                })
                .collect();
            {
                self.bodies.get_mut(&name).unwrap().call_store_origins = Arc::new(needed_stores);
                let needed_variants = self.bodies[&name]
                    .nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        crate::typed_body::NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } => store_variants
                            .get(callee)
                            .map(|summary| (*callee, summary.clone())),
                        _ => None,
                    })
                    .collect();
                self.bodies.get_mut(&name).unwrap().call_store_variants = Arc::new(needed_variants);
                let needed_clears = self.bodies[&name]
                    .nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        crate::typed_body::NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } => clear_summaries
                            .get(callee)
                            .map(|summary| (*callee, summary.clone())),
                        _ => None,
                    })
                    .collect();
                self.bodies.get_mut(&name).unwrap().call_parameter_clears = Arc::new(needed_clears);
                let needed = self.bodies[&name]
                    .nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        crate::typed_body::NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } => clear_variants
                            .get(callee)
                            .map(|summary| (*callee, summary.clone())),
                        _ => None,
                    })
                    .collect();
                self.bodies.get_mut(&name).unwrap().call_clear_variants = Arc::new(needed);
                let callees = self.bodies[&name]
                    .nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        crate::typed_body::NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } => Some(*callee),
                        _ => None,
                    })
                    .collect::<HashSet<_>>();
                self.bodies
                    .get_mut(&name)
                    .unwrap()
                    .call_output_store_variants = Arc::new(
                    callees
                        .iter()
                        .filter_map(|callee| {
                            output_store_variants
                                .get(callee)
                                .map(|groups| (*callee, groups.clone()))
                        })
                        .collect(),
                );
                self.bodies
                    .get_mut(&name)
                    .unwrap()
                    .call_output_clear_variants = Arc::new(
                    callees
                        .iter()
                        .filter_map(|callee| {
                            output_clear_variants
                                .get(callee)
                                .map(|groups| (*callee, groups.clone()))
                        })
                        .collect(),
                );
                let needed = self.bodies[&name]
                    .nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        crate::typed_body::NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } => return_variants
                            .get(callee)
                            .map(|summary| (*callee, summary.clone())),
                        _ => None,
                    })
                    .collect();
                self.bodies.get_mut(&name).unwrap().call_return_variants = Arc::new(needed);
                let needed = self.bodies[&name]
                    .nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        crate::typed_body::NodeKind::Form {
                            callee: Some(callee),
                            ..
                        } => return_bounds
                            .get(callee)
                            .map(|bounds| (*callee, bounds.clone())),
                        _ => None,
                    })
                    .collect();
                self.bodies
                    .get_mut(&name)
                    .unwrap()
                    .call_return_variant_bounds = Arc::new(needed);
            }
            if include_parameter_contents {
                self.flows
                    .get_mut(&name)
                    .unwrap()
                    .prune_impossible_variant_patterns(&self.bodies[&name]);
            }
            let body = &self.bodies[&name];
            let flow = &self.flows[&name];
            let origins = if include_parameter_contents {
                flow.staged_parameter_store_loan_origins(body)
            } else {
                flow.loan_origins(body)
            };
            let mut returned = Vec::new();
            let store_origins = if include_parameter_contents {
                flow.staged_parameter_store_loan_origins(body)
            } else {
                flow.staged_store_loan_origins(body)
            };
            let stores = flow.parameter_store_summaries(body, &store_origins);
            let output_stores = flow.parameter_output_store_variant_summaries(body, &store_origins);
            let variants = output_stores
                .iter()
                .filter_map(|((path, variant), stores)| {
                    path.is_empty().then_some((*variant, stores.clone()))
                })
                .collect();
            let clears = if include_parameter_contents {
                flow.parameter_clear_summaries(body, &store_origins)
            } else {
                Vec::new()
            };
            let returned_bounds = flow.returned_variant_bounds(body, &store_origins);
            let returned_variants = returned_bounds
                .iter()
                .filter_map(|(path, variants)| {
                    (variants.len() == 1).then(|| (path.clone(), *variants.iter().next().unwrap()))
                })
                .collect();
            let output_clears = if include_parameter_contents {
                flow.parameter_output_clear_variant_summaries(body, &store_origins)
            } else {
                HashMap::new()
            };
            let conditional_clears = output_clears
                .iter()
                .filter_map(|((path, variant), clears)| {
                    path.is_empty().then_some((*variant, clears.clone()))
                })
                .collect();
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
                        storage_inputs: origin.storage_inputs,
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
                store_summaries.insert(id, stores);
                store_variants.insert(id, variants);
                clear_summaries.insert(id, clears);
                clear_variants.insert(id, conditional_clears);
                output_store_variants.insert(id, output_stores);
                output_clear_variants.insert(id, output_clears);
                for (task, captures) in &self.thread_capture_schemas {
                    if captures.worker != id {
                        continue;
                    }
                    let (Some(owner), Some(spawn), Some(join), Some(join_ok), Some(join_error)) = (
                        self.aggregate_id(&Type::Named(task.clone())),
                        self.function_id(&format!("{task}-spawn")),
                        self.function_id(&format!("{task}-join")),
                        self.variant_id(
                            &Type::Named(format!("{task}-join-result")),
                            &format!("{task}-join-ok"),
                        ),
                        self.variant_id(
                            &Type::Named(format!("{task}-join-result")),
                            &format!("{task}-join-error"),
                        ),
                    ) else {
                        continue;
                    };
                    let Some(captured_stores) = crate::thread_contract::capture_store_summaries(
                        owner,
                        captures.parameters.len(),
                        &store_summaries[&id],
                    ) else {
                        continue;
                    };
                    let Some(captured_clears) = clear_summaries[&id]
                        .iter()
                        .map(|clear| {
                            crate::thread_contract::capture_loan_summary(
                                owner,
                                captures.parameters.len(),
                                clear,
                            )
                        })
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    // Neither spawn nor a retrying join proves worker completion.
                    // Install final storage only under the successful join tag.
                    store_summaries.insert(spawn, Vec::new());
                    store_summaries.insert(join, Vec::new());
                    clear_summaries.insert(spawn, Vec::new());
                    clear_summaries.insert(join, Vec::new());
                    store_variants.insert(
                        join,
                        HashMap::from([(join_ok, captured_stores), (join_error, Vec::new())]),
                    );
                    clear_variants.insert(
                        join,
                        HashMap::from([(join_ok, captured_clears), (join_error, Vec::new())]),
                    );
                    let selected_stores = output_store_variants[&id]
                        .iter()
                        .map(|((path, variant), stores)| {
                            let mut nested = vec![crate::typed_place::Segment::Payload(join_ok, 0)];
                            nested.extend_from_slice(path);
                            Some((
                                (nested, *variant),
                                crate::thread_contract::capture_store_summaries(
                                    owner,
                                    captures.parameters.len(),
                                    stores,
                                )?,
                            ))
                        })
                        .collect::<Option<HashMap<_, _>>>();
                    let selected_clears = output_clear_variants[&id]
                        .iter()
                        .map(|((path, variant), clears)| {
                            let mut nested = vec![crate::typed_place::Segment::Payload(join_ok, 0)];
                            nested.extend_from_slice(path);
                            Some((
                                (nested, *variant),
                                clears
                                    .iter()
                                    .map(|clear| {
                                        crate::thread_contract::capture_loan_summary(
                                            owner,
                                            captures.parameters.len(),
                                            clear,
                                        )
                                    })
                                    .collect::<Option<Vec<_>>>()?,
                            ))
                        })
                        .collect::<Option<HashMap<_, _>>>();
                    if let (Some(stores), Some(clears)) = (selected_stores, selected_clears) {
                        output_store_variants.insert(join, stores);
                        output_clear_variants.insert(join, clears);
                    }
                    // Worker output lives inside the successful join payload,
                    // not in task capture storage. Preserve full paths so two
                    // fields of the same enum type cannot share a selector.
                    let mut joined_bounds = return_bounds.get(&join).cloned().unwrap_or_default();
                    for (path, variants) in &returned_bounds {
                        let mut nested = vec![crate::typed_place::Segment::Payload(join_ok, 0)];
                        nested.extend_from_slice(path);
                        joined_bounds.insert(nested, variants.clone());
                    }
                    let joined_variants = joined_bounds
                        .iter()
                        .filter_map(|(path, variants)| {
                            (variants.len() == 1)
                                .then(|| (path.clone(), *variants.iter().next().unwrap()))
                        })
                        .collect();
                    return_variants.insert(join, joined_variants);
                    return_bounds.insert(join, joined_bounds);
                }
                return_variants.insert(id, returned_variants);
                return_bounds.insert(id, returned_bounds);
            }
        }
        let shared = Arc::new(summaries);
        let shared_stores = Arc::new(store_summaries);
        let shared_variants = Arc::new(store_variants);
        let shared_clears = Arc::new(clear_summaries);
        let shared_clear_variants = Arc::new(clear_variants);
        let shared_output_store_variants = Arc::new(output_store_variants);
        let shared_output_clear_variants = Arc::new(output_clear_variants);
        let shared_return_variants = Arc::new(return_variants);
        let shared_return_bounds = Arc::new(return_bounds);
        for body in self.bodies.values_mut() {
            body.call_return_origins = shared.clone();
            {
                body.call_store_origins = shared_stores.clone();
                body.call_store_variants = shared_variants.clone();
                body.call_parameter_clears = shared_clears.clone();
                body.call_clear_variants = shared_clear_variants.clone();
                body.call_output_store_variants = shared_output_store_variants.clone();
                body.call_output_clear_variants = shared_output_clear_variants.clone();
                body.call_return_variants = shared_return_variants.clone();
                body.call_return_variant_bounds = shared_return_bounds.clone();
            }
        }
    }

    fn staged_add_thread_operation_contracts(
        &self,
        summaries: &mut HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>,
        infer_entry_contracts: bool,
    ) {
        for (task, captures) in &self.thread_capture_schemas {
            let Some(worker_body) = self.bodies.get(&captures.worker_name) else {
                continue;
            };
            let Some(worker_summary) = summaries.get(&captures.worker) else {
                continue;
            };
            let (
                Some(spawn),
                Some(join),
                Some(owner),
                Some(spawn_ok),
                Some(spawn_error),
                Some(join_ok),
                Some(join_error),
            ) = (
                self.function_id(&format!("{task}-spawn")),
                self.function_id(&format!("{task}-join")),
                self.aggregate_id(&Type::Named(task.clone())),
                self.variant_id(
                    &Type::Named(format!("{task}-spawn-result")),
                    &format!("{task}-spawn-ok"),
                ),
                self.variant_id(
                    &Type::Named(format!("{task}-spawn-result")),
                    &format!("{task}-spawn-error"),
                ),
                self.variant_id(
                    &Type::Named(format!("{task}-join-result")),
                    &format!("{task}-join-ok"),
                ),
                self.variant_id(
                    &Type::Named(format!("{task}-join-result")),
                    &format!("{task}-join-error"),
                ),
            )
            else {
                continue;
            };
            if summaries.contains_key(&spawn) && summaries.contains_key(&join) {
                continue;
            }
            if worker_body
                .call_store_variants
                .get(&join)
                .and_then(|variants| variants.get(&join_ok))
                .is_none()
                || worker_body
                    .call_clear_variants
                    .get(&join)
                    .and_then(|variants| variants.get(&join_ok))
                    .is_none()
            {
                continue;
            }
            if let Some((spawn_summary, join_summary)) = crate::thread_contract::operation_summaries(
                captures.worker,
                owner,
                worker_body,
                worker_summary,
                infer_entry_contracts,
                spawn_ok,
                spawn_error,
                join_ok,
                join_error,
            ) {
                summaries.insert(spawn, spawn_summary);
                summaries.insert(join, join_summary);
            }
        }
    }

    #[cfg(test)]
    pub fn staged_captured_thread_worker_contract(
        &self,
        task: &str,
        summaries: &HashMap<FunctionId, crate::typed_flow::ReferentFunctionEffects>,
    ) -> Option<crate::thread_contract::CapturedWorkerContract> {
        let captures = self.thread_capture_schemas.get(task)?;
        if !self.bodies.contains_key(&captures.worker_name) {
            return None;
        }
        crate::thread_contract::capture_worker_contract(
            captures.worker,
            self.aggregate_id(&Type::Named(task.into()))?,
            captures.parameters.len(),
            summaries.get(&captures.worker)?,
        )
    }

    fn thread_operation_workers(&self) -> HashMap<FunctionId, FunctionId> {
        self.thread_capture_schemas
            .iter()
            .flat_map(|(name, captures)| {
                ["spawn", "join"].into_iter().filter_map(move |operation| {
                    self.function_id(&format!("{name}-{operation}"))
                        .map(|id| (id, captures.worker))
                })
            })
            .collect()
    }

    fn thread_call_return_metadata(
        &self,
    ) -> (
        HashMap<FunctionId, Vec<crate::typed_body::ParameterLoanSummary>>,
        HashMap<FunctionId, crate::typed_flow::VariantBounds>,
    ) {
        use crate::typed_body::ParameterLoanSummary;
        use crate::typed_place::Segment;
        let mut origins = HashMap::new();
        let mut bounds = HashMap::new();
        let available_workers = self
            .bodies
            .keys()
            .filter_map(|name| self.function_id(name))
            .collect::<HashSet<_>>();
        for (name, captures) in &self.thread_capture_schemas {
            // Metadata cannot make an unavailable worker implementation real.
            if !available_workers.contains(&captures.worker) {
                continue;
            }
            let Some(owner) = self.aggregate_id(&Type::Named(name.clone())) else {
                continue;
            };
            let mut spawned = Vec::new();
            let mut retried = Vec::new();
            let spawn_type = Type::Named(format!("{name}-spawn-result"));
            let join_type = Type::Named(format!("{name}-join-result"));
            let (Some(spawn_ok), Some(spawn_error), Some(join_ok), Some(join_error)) = (
                self.variant_id(&spawn_type, &format!("{name}-spawn-ok")),
                self.variant_id(&spawn_type, &format!("{name}-spawn-error")),
                self.variant_id(&join_type, &format!("{name}-join-ok")),
                self.variant_id(&join_type, &format!("{name}-join-error")),
            ) else {
                continue;
            };
            for (parameter, ty) in captures.parameters.iter().enumerate() {
                let mut slots = Vec::new();
                self.collect_parameter_loan_slots(
                    ty,
                    &mut Vec::new(),
                    &mut HashSet::new(),
                    &mut slots,
                    false,
                    false,
                );
                for seed in slots {
                    let mut captured_slot = vec![Segment::ThreadCapture(owner, parameter)];
                    captured_slot.extend(seed.storage.iter().cloned());
                    let mut spawn_storage = vec![Segment::Payload(spawn_ok, 0)];
                    spawn_storage.extend(captured_slot.iter().cloned());
                    let mut spawn_inputs = vec![None, None];
                    spawn_inputs.extend((0..seed.storage.len()).map(Some));
                    spawned.push(ParameterLoanSummary {
                        parameter,
                        global: None,
                        mutable: seed.mutable,
                        pinned: seed.pinned,
                        lifetime_only: false,
                        referent_projection: Vec::new(),
                        input_storage: seed.storage,
                        storage: spawn_storage,
                        storage_inputs: spawn_inputs,
                    });
                    let mut retry_storage =
                        vec![Segment::Payload(join_error, 0), Segment::Tuple(0)];
                    retry_storage.extend(captured_slot.iter().cloned());
                    let mut retry_inputs = vec![None, None];
                    retry_inputs.extend((0..captured_slot.len()).map(Some));
                    retried.push(ParameterLoanSummary {
                        parameter: 0,
                        global: None,
                        mutable: seed.mutable,
                        pinned: seed.pinned,
                        lifetime_only: false,
                        referent_projection: Vec::new(),
                        storage: retry_storage,
                        storage_inputs: retry_inputs,
                        input_storage: captured_slot,
                    });
                }
            }
            for (operation, loans, alternatives) in [
                ("spawn", spawned, HashSet::from([spawn_ok, spawn_error])),
                ("join", retried, HashSet::from([join_ok, join_error])),
            ] {
                if let Some(id) = self.function_id(&format!("{name}-{operation}")) {
                    origins.insert(id, loans);
                    bounds.insert(id, HashMap::from([(Vec::new(), alternatives)]));
                }
            }
        }
        (origins, bounds)
    }

    pub fn reference_storage_slots(&self, ty: &Type) -> Vec<crate::typed_body::ParameterLoanSeed> {
        let mut slots = Vec::new();
        self.collect_parameter_loan_slots(
            ty,
            &mut Vec::new(),
            &mut HashSet::new(),
            &mut slots,
            true,
            false,
        );
        slots
    }

    fn collect_parameter_loan_slots(
        &self,
        ty: &Type,
        path: &mut Vec<crate::typed_place::Segment>,
        seen: &mut HashSet<String>,
        output: &mut Vec<crate::typed_body::ParameterLoanSeed>,
        expand_arrays: bool,
        include_referents: bool,
    ) {
        use crate::typed_place::Segment;
        match ty {
            Type::Reference { mutable, target } | Type::PinnedReference { mutable, target } => {
                output.push(crate::typed_body::ParameterLoanSeed {
                    mutable: *mutable,
                    pinned: matches!(ty, Type::PinnedReference { .. }),
                    storage: path.clone(),
                });
                if include_referents {
                    path.push(Segment::Dereference);
                    self.collect_parameter_loan_slots(
                        target,
                        path,
                        seen,
                        output,
                        expand_arrays,
                        true,
                    );
                    path.pop();
                }
            }
            Type::Slice(element) | Type::MutableSlice(element) => {
                output.push(crate::typed_body::ParameterLoanSeed {
                    mutable: matches!(ty, Type::MutableSlice(_)),
                    pinned: false,
                    storage: path.clone(),
                });
                if include_referents {
                    path.push(Segment::Dereference);
                    path.push(Segment::DynamicIndex);
                    self.collect_parameter_loan_slots(
                        element,
                        path,
                        seen,
                        output,
                        expand_arrays,
                        true,
                    );
                    path.pop();
                    path.pop();
                }
            }
            Type::Array(element, length) if *length > 0 => {
                if expand_arrays {
                    for index in 0..*length {
                        path.push(Segment::Index(index as u128));
                        self.collect_parameter_loan_slots(
                            element,
                            path,
                            seen,
                            output,
                            true,
                            include_referents,
                        );
                        path.pop();
                    }
                    return;
                }
                path.push(if *length == 1 {
                    Segment::Index(0)
                } else {
                    Segment::DynamicIndex
                });
                self.collect_parameter_loan_slots(
                    element,
                    path,
                    seen,
                    output,
                    expand_arrays,
                    include_referents,
                );
                path.pop();
            }
            Type::Tuple(elements) => {
                for (index, element) in elements.iter().enumerate() {
                    path.push(Segment::Tuple(index));
                    self.collect_parameter_loan_slots(
                        element,
                        path,
                        seen,
                        output,
                        expand_arrays,
                        include_referents,
                    );
                    path.pop();
                }
            }
            Type::Named(name) if seen.insert(name.clone()) => {
                if let Some(captures) = self.thread_capture_schemas.get(name) {
                    if let Some(owner) = self.aggregate_ids.get(name).copied() {
                        for (index, ty) in captures.parameters.iter().enumerate() {
                            path.push(Segment::ThreadCapture(owner, index));
                            self.collect_parameter_loan_slots(
                                ty,
                                path,
                                seen,
                                output,
                                expand_arrays,
                                include_referents,
                            );
                            path.pop();
                        }
                    }
                }
                if let Some(fields) = self.structs.get(name) {
                    if let Some(owner) = self.aggregate_ids.get(name).copied() {
                        for (index, field) in fields.iter().enumerate() {
                            path.push(Segment::Field(FieldId { owner, index }));
                            self.collect_parameter_loan_slots(
                                &field.ty,
                                path,
                                seen,
                                output,
                                expand_arrays,
                                include_referents,
                            );
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
                            self.collect_parameter_loan_slots(
                                field,
                                path,
                                seen,
                                output,
                                expand_arrays,
                                include_referents,
                            );
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
