//! Ordinary source rendering for the typed executable async graph.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! This boundary substitutes already evaluated operands. It does not choose
//! Copy/move/reborrow access, allocate frame slots, or authorize emission. The
//! caller must supply expressions referencing storage using its checked access
//! plan, retain unsafe context, and validate the final ordinary program.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::generator::async_exec::Error as NodeError;
use crate::generator::async_exec::{Action, Compute, Graph, Operation, Terminator, ValueId};
use crate::typed_body::{BindingId, Body, Node, NodeId, NodeKind};
use crate::typed_ir::{DeclarationId, Declarations, FieldId};
use crate::{Expr, Span, Type};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Error {
    pub message: String,
    pub span: Option<Span>,
}

fn error(source: Option<NodeId>, message: impl Into<String>) -> NodeError {
    NodeError {
        source,
        message: message.into(),
    }
}

fn attach(body: &Body, error: NodeError) -> Error {
    Error {
        message: error.message,
        span: error
            .source
            .and_then(|source| body.nodes.get(source.0))
            .and_then(|node| node.span),
    }
}

/// Construct with `new`; checked identities must belong to this declaration
/// context. Immutable borrows keep the validated graph/body unchanged.
pub(crate) struct RenderContext<'a> {
    body: &'a Body,
    declarations: &'a Declarations,
    graph: &'a Graph,
    operations: HashMap<NodeId, &'a Operation>,
    atoms: HashSet<NodeId>,
    patterns: HashSet<NodeId>,
    // Call normalization erases the source keyword. Recover it from the
    // declaration interfaces, independently of the enclosing unsafe region.
    unsafe_functions: HashSet<String>,
}

impl<'a> RenderContext<'a> {
    pub(crate) fn new(
        body: &'a Body,
        declarations: &'a Declarations,
        graph: &'a Graph,
        functions: impl IntoIterator<Item = &'a crate::Function>,
    ) -> Result<Self, Error> {
        let mut context = Self {
            body,
            declarations,
            graph,
            operations: HashMap::new(),
            atoms: HashSet::new(),
            patterns: HashSet::new(),
            unsafe_functions: functions
                .into_iter()
                .filter(|function| function.unsafe_call || function.external)
                .map(|function| function.name.clone())
                .collect(),
        };
        context.validate().map_err(|error| attach(body, error))?;
        for block in &graph.blocks {
            if let Terminator::PatternTest { pattern, .. } = &block.terminator {
                context.patterns.insert(pattern.source);
            }
            for located in &block.actions {
                match &located.action {
                    Action::Compute {
                        operation: Compute::Checked(operation),
                        ..
                    } => {
                        context.operations.insert(operation.source, operation);
                    }
                    Action::Compute {
                        operation: Compute::Atom { source, .. },
                        ..
                    } => {
                        context.atoms.insert(*source);
                    }
                    Action::Preview(pattern)
                    | Action::Commit(pattern)
                    | Action::EndPreview(pattern) => {
                        context.patterns.insert(pattern.source);
                    }
                    _ => {}
                }
            }
        }
        Ok(context)
    }

    fn validate(&self) -> Result<(), NodeError> {
        self.graph.validate()?;
        self.graph.validate_against(self.body)?;
        for block in &self.graph.blocks {
            for action in &block.actions {
                if let Action::Compute {
                    operation: Compute::Checked(operation),
                    ..
                } = &action.action
                {
                    if let Some(callee) = operation.callee {
                        if self
                            .body
                            .declaration_name(DeclarationId::Function(callee))
                            .and_then(|name| self.declarations.function_id(name))
                            != Some(callee)
                        {
                            return Err(error(
                                Some(operation.source),
                                "callee belongs to a different declaration context",
                            ));
                        }
                        let signature = &self.declarations.function(callee).signature;
                        if signature.parameter_names.len() != signature.parameters.len()
                            || signature.parameters.len() != operation.operands.len()
                        {
                            return Err(error(
                                Some(operation.source),
                                "checked call/signature arity mismatch",
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// The map contains access expressions, not source subtrees. Cloning an
    /// Expr here copies syntax only: no `#clone`, borrow, or slot take is added.
    /// Unsafe wrapping remains the caller's LocatedAction responsibility.
    pub(crate) fn render_compute(
        &self,
        compute: &Compute,
        values: &HashMap<ValueId, Expr>,
    ) -> Result<Expr, Error> {
        self.compute(compute, values)
            .map_err(|error| attach(self.body, error))
    }

    fn compute(
        &self,
        compute: &Compute,
        values: &HashMap<ValueId, Expr>,
    ) -> Result<Expr, NodeError> {
        match compute {
            Compute::Checked(operation) => self.render_operation(operation, values),
            Compute::Identity(value) => self.replacement(*value, values, None),
            Compute::Unit => Ok(Expr::List(Vec::new().into())),
            Compute::Bool(value) => Ok(symbol(if *value { "true" } else { "false" })),
            Compute::Atom { source, kind } => {
                let node = self.node(*source)?;
                let same = match (&node.kind, kind) {
                    (NodeKind::Literal(left), NodeKind::Literal(right)) => left == right,
                    (NodeKind::Declaration(left), NodeKind::Declaration(right)) => left == right,
                    (
                        NodeKind::Symbol {
                            name: left,
                            binding: a,
                        },
                        NodeKind::Symbol {
                            name: right,
                            binding: b,
                        },
                    ) => left == right && a == b,
                    _ => false,
                };
                if !same || !self.atoms.contains(source) {
                    return Err(error(
                        Some(*source),
                        "atom is not its checked graph computation",
                    ));
                }
                match kind {
                    NodeKind::Literal(value) => self.literal(*source, value),
                    NodeKind::Declaration(id) => Ok(symbol(self.declaration(*source, *id)?)),
                    NodeKind::Symbol {
                        name,
                        binding: None,
                    } if matches!(name.as_str(), "true" | "false")
                        && node.ty == Some(Type::Bool) =>
                    {
                        Ok(symbol(name))
                    }
                    _ => Err(error(
                        Some(*source),
                        "runtime symbol requires an evaluated replacement, not a new owner read",
                    )),
                }
            }
        }
    }

    fn node(&self, source: NodeId) -> Result<&Node, NodeError> {
        self.body
            .nodes
            .get(source.0)
            .ok_or_else(|| error(Some(source), "node is outside the checked body"))
    }

    fn declaration(&self, source: NodeId, id: DeclarationId) -> Result<&str, NodeError> {
        let checked = self
            .body
            .declaration_name(id)
            .ok_or_else(|| error(Some(source), "declaration lacks a checked body identity"))?;
        let current = self.declarations.declaration_name(id);
        if checked != current {
            return Err(error(
                Some(source),
                "declaration name disagrees with the checked context",
            ));
        }
        Ok(current)
    }

    fn replacement(
        &self,
        value: ValueId,
        values: &HashMap<ValueId, Expr>,
        source: Option<NodeId>,
    ) -> Result<Expr, NodeError> {
        if self.graph.values.get(value.0).is_none() {
            return Err(error(
                source,
                "replacement references an unknown graph value",
            ));
        }
        values.get(&value).cloned().ok_or_else(|| {
            error(
                source,
                format!("missing evaluated replacement for ValueId({})", value.0),
            )
        })
    }

    fn literal(&self, source: NodeId, value: &Expr) -> Result<Expr, NodeError> {
        if matches!(
            value,
            Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_)
        ) {
            let ty = self
                .node(source)?
                .ty
                .as_ref()
                .ok_or_else(|| error(Some(source), "numeric value lacks its checked type"))?;
            if !numeric_type(ty) {
                return Err(error(
                    Some(source),
                    "numeric literal has a nonnumeric checked type",
                ));
            }
            Ok(Expr::List(
                vec![symbol("#literal"), type_expr(ty)?, value.clone()].into(),
            ))
        } else if matches!(value, Expr::Char(_) | Expr::String(_)) {
            Ok(value.clone())
        } else {
            Err(error(
                Some(source),
                "nonliteral syntax in a checked literal",
            ))
        }
    }

    fn render_operation(
        &self,
        operation: &Operation,
        values: &HashMap<ValueId, Expr>,
    ) -> Result<Expr, NodeError> {
        // Do not allow a caller-created Operation to bypass the graph's complete
        // operand schema. The context has already validated the registered one.
        let registered = self.operations.get(&operation.source).ok_or_else(|| {
            error(
                Some(operation.source),
                "operation is not registered in the checked graph",
            )
        })?;
        if operation.head != registered.head
            || operation.callee != registered.callee
            || operation.numeric != registered.numeric
            || operation.metadata != registered.metadata
            || operation.operands.len() != registered.operands.len()
            || operation
                .operands
                .iter()
                .zip(&registered.operands)
                .any(|(a, b)| a.position != b.position || a.value != b.value)
        {
            return Err(error(
                Some(operation.source),
                "operation changed its validated operand/metadata schema",
            ));
        }
        let NodeKind::Form { children, .. } = &self.node(operation.source)?.kind else {
            return Err(error(
                Some(operation.source),
                "checked operation is not a form",
            ));
        };
        let mut replacements = HashMap::new();
        for operand in &operation.operands {
            let value = self.replacement(operand.value, values, Some(operation.source))?;
            if replacements
                .insert(operand.position.clone(), value)
                .is_some()
            {
                return Err(error(
                    Some(operation.source),
                    "duplicate runtime operand position",
                ));
            }
        }
        if let Some(callee) = operation.callee {
            let signature = &self.declarations.function(callee).signature;
            let mut arguments = Vec::new();
            for (index, name) in signature.parameter_names.iter().enumerate() {
                let value = replacements.get(&vec![index + 1]).ok_or_else(|| {
                    error(
                        Some(operation.source),
                        "call operand is not a direct declaration-order argument",
                    )
                })?;
                arguments.push(Expr::List(vec![symbol(name), value.clone()].into()));
            }
            return Ok(Expr::List(
                vec![
                    symbol(
                        if self
                            .unsafe_functions
                            .contains(&self.declarations.function(callee).name)
                        {
                            "#unsafe-call"
                        } else {
                            "#call"
                        },
                    ),
                    symbol(&self.declarations.function(callee).name),
                    Expr::List(arguments.into()),
                ]
                .into(),
            ));
        }
        let head = *children
            .first()
            .ok_or_else(|| error(Some(operation.source), "empty checked operation"))?;
        if let NodeKind::Declaration(DeclarationId::Aggregate(owner)) = self.node(head)?.kind {
            let name = self.declaration(head, DeclarationId::Aggregate(owner))?;
            let fields = self.declarations.structs.get(name).ok_or_else(|| {
                error(Some(head), "aggregate constructor is not a checked struct")
            })?;
            if fields.len() + 1 != children.len() || fields.len() != replacements.len() {
                return Err(error(
                    Some(operation.source),
                    "struct constructor lacks complete evaluated fields",
                ));
            }
            let mut entries = Vec::new();
            for (index, _) in fields.iter().enumerate() {
                let field = self
                    .declarations
                    .declaration_name(DeclarationId::Field(FieldId { owner, index }));
                let value = replacements.get(&vec![index + 1]).ok_or_else(|| {
                    error(
                        Some(operation.source),
                        "struct field is not an evaluated direct operand",
                    )
                })?;
                entries.push(Expr::List(vec![symbol(field), value.clone()].into()));
            }
            return Ok(Expr::List(
                vec![
                    symbol("#struct-literal"),
                    symbol(name),
                    Expr::List(entries.into()),
                ]
                .into(),
            ));
        }
        if operation.head == "literal" {
            // The ordinary checker accepts contextual expressions here. Those
            // are NOT static literal data and the graph's static-only schema
            // cannot authorize reevaluating them.
            if children.len() != 3 {
                return Err(error(
                    Some(operation.source),
                    "invalid checked literal form",
                ));
            }
            let NodeKind::Literal(value) = &self.node(children[2])?.kind else {
                return Err(error(
                    Some(children[2]),
                    "typed literal contains executable metadata",
                ));
            };
            return self.literal(operation.source, value);
        }
        let mut items = Vec::new();
        let mut used = HashSet::new();
        for (index, child) in children.iter().enumerate() {
            let item = if index == 0 {
                if let NodeKind::Declaration(id) = self.node(*child)?.kind {
                    symbol(self.declaration(*child, id)?)
                } else if let Some(numeric) = &operation.numeric {
                    let mode = numeric
                        .overflow_mode()
                        .map_or(String::new(), |mode| format!(".{mode}"));
                    let internal = format!(
                        "{}.{}{mode}",
                        numeric.scalar_name().trim_start_matches('#'),
                        numeric.operation.as_str()
                    );
                    symbol(crate::names::numeric_source(&internal).ok_or_else(|| {
                        error(Some(operation.source), "unknown checked numeric operation")
                    })?)
                } else if operation.head.starts_with('#') {
                    symbol(&operation.head)
                } else if operation.head == "array" {
                    // Runtime creation and type/pattern metadata have distinct
                    // canonical spellings even though lowering shares a stem.
                    symbol("#array-of")
                } else {
                    symbol(format!("#{}", operation.head))
                }
            } else if index == 1
                && matches!(operation.head.as_str(), "tuple" | "array" | "array-repeat")
                && operation.metadata.contains(child)
            {
                // Constructors spell their fully resolved checked type. In
                // particular an alias is not a runtime first argument, and
                // native aggregate staging must see the concrete shape.
                let ty = self.node(operation.source)?.ty.as_ref().ok_or_else(|| {
                    error(
                        Some(operation.source),
                        "constructor has no checked result type",
                    )
                })?;
                if !matches!(
                    (operation.head.as_str(), ty),
                    ("tuple", Type::Tuple(_)) | ("array" | "array-repeat", Type::Array(..))
                ) {
                    return Err(error(
                        Some(operation.source),
                        "constructor result shape changed",
                    ));
                }
                type_expr(ty)?
            } else {
                self.metadata(
                    *child,
                    &mut vec![index],
                    &replacements,
                    &mut used,
                    &mut HashSet::new(),
                )?
            };
            items.push(item);
        }
        if used.len() != replacements.len() {
            return Err(error(
                Some(operation.source),
                "unused runtime replacement in operation reconstruction",
            ));
        }
        Ok(Expr::List(items.into()))
    }

    /// Recurse only through static data. Runtime nodes must be intercepted at
    /// their exact schema path before this function considers their kind.
    fn metadata(
        &self,
        source: NodeId,
        path: &mut Vec<usize>,
        replacements: &HashMap<Vec<usize>, Expr>,
        used: &mut HashSet<Vec<usize>>,
        active: &mut HashSet<NodeId>,
    ) -> Result<Expr, NodeError> {
        if let Some(value) = replacements.get(path) {
            used.insert(path.clone());
            return Ok(value.clone());
        }
        if !active.insert(source) {
            return Err(error(Some(source), "cyclic checked metadata"));
        }
        let node = self.node(source)?;
        let result = match &node.kind {
            NodeKind::Literal(value)
                if matches!(
                    value,
                    Expr::Integer(_)
                        | Expr::UnsignedInteger(_)
                        | Expr::Float(_)
                        | Expr::Char(_)
                        | Expr::String(_)
                        | Expr::Generate
                ) =>
            {
                Ok(value.clone())
            }
            NodeKind::Declaration(id) if node.ty.is_none() => {
                Ok(symbol(self.declaration(source, *id)?))
            }
            NodeKind::Symbol {
                name,
                binding: None,
            } if node.ty.is_none() => Ok(symbol(name)),
            NodeKind::Syntax(children) | NodeKind::Form { children, .. } if node.ty.is_none() => {
                let mut items = Vec::new();
                for (index, child) in children.iter().enumerate() {
                    path.push(index);
                    let mut value = self.metadata(*child, path, replacements, used, active)?;
                    path.pop();
                    if index == 0
                        && matches!(&node.kind, NodeKind::Form { .. })
                        && matches!(
                            &self.node(*child)?.kind,
                            NodeKind::Symbol { binding: None, .. }
                        )
                    {
                        if let Expr::Symbol(name) = &mut value {
                            if crate::is_builtin_form(name) {
                                *name = format!("#{name}");
                            }
                        }
                    }
                    items.push(value);
                }
                Ok(Expr::List(items.into()))
            }
            _ => Err(error(
                Some(source),
                "unreplaced executable node in static metadata",
            )),
        };
        active.remove(&source);
        result
    }

    /// Render retained pattern syntax with structurally checked BindingIds.
    /// The caller supplies names for Test or Commit; this emits neither phase's
    /// effects. In particular it does not manufacture preview alias owners.
    pub(crate) fn render_pattern(
        &self,
        source: NodeId,
        names: &HashMap<BindingId, String>,
    ) -> Result<Expr, Error> {
        self.pattern_impl(source, names)
            .map_err(|error| attach(self.body, error))
    }

    fn pattern_impl(
        &self,
        source: NodeId,
        names: &HashMap<BindingId, String>,
    ) -> Result<Expr, NodeError> {
        if !self.patterns.contains(&source) || !self.graph.metadata.contains_key(&source) {
            return Err(error(
                Some(source),
                "pattern is not retained checked graph pattern metadata",
            ));
        }
        self.pattern(source, names, &mut HashSet::new())
    }

    fn pattern(
        &self,
        source: NodeId,
        names: &HashMap<BindingId, String>,
        active: &mut HashSet<NodeId>,
    ) -> Result<Expr, NodeError> {
        if !active.insert(source) {
            return Err(error(Some(source), "cyclic checked pattern"));
        }
        let result = match &self.node(source)?.kind {
            NodeKind::Declaration(id) => Ok(symbol(self.declaration(source, *id)?)),
            NodeKind::Symbol {
                binding: Some(binding),
                ..
            } => {
                if self.body.bindings.get(binding.0).is_none() {
                    return Err(error(Some(source), "unknown pattern binding"));
                }
                names.get(binding).map(symbol).ok_or_else(|| {
                    error(
                        Some(source),
                        format!("missing pattern name for BindingId({})", binding.0),
                    )
                })
            }
            NodeKind::Symbol {
                name,
                binding: None,
            } => Ok(symbol(name)),
            NodeKind::Literal(value)
                if matches!(
                    value,
                    Expr::Integer(_)
                        | Expr::UnsignedInteger(_)
                        | Expr::Float(_)
                        | Expr::Char(_)
                        | Expr::String(_)
                ) =>
            {
                Ok(value.clone())
            }
            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                let mut items = Vec::new();
                for (index, child) in children.iter().enumerate() {
                    let mut value = self.pattern(*child, names, active)?;
                    if index == 0
                        && matches!(
                            &self.node(*child)?.kind,
                            NodeKind::Symbol { binding: None, .. }
                        )
                    {
                        if let Expr::Symbol(name) = &mut value {
                            if crate::is_builtin_form(name) {
                                *name = format!("#{name}");
                            }
                        }
                    }
                    items.push(value);
                }
                Ok(Expr::List(items.into()))
            }
            _ => Err(error(
                Some(source),
                "unsupported executable/quoted pattern node",
            )),
        };
        active.remove(&source);
        result
    }
}

fn symbol(value: impl AsRef<str>) -> Expr {
    Expr::Symbol(value.as_ref().to_owned())
}

fn numeric_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8
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
    )
}

fn type_expr(ty: &Type) -> Result<Expr, NodeError> {
    // Reuse the ordinary canonical type spelling, never runtime Body::syntax.
    let mut parsed = crate::parse(&crate::type_source(ty))
        .map_err(|cause| error(None, format!("cannot render checked type: {cause}")))?;
    if parsed.len() != 1 {
        return Err(error(None, "checked type spelling is not one expression"));
    }
    Ok(parsed.remove(0).expr)
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    fn prepare(source: &str, function: &str) -> (Declarations, Graph) {
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let graph =
            crate::generator::async_exec::build(&declarations.bodies[function], &[]).unwrap();
        (declarations, graph)
    }

    fn operation<'a>(graph: &'a Graph, head: &str) -> &'a Compute {
        graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| match &action.action {
                Action::Compute {
                    operation: compute @ Compute::Checked(Operation { head: name, .. }),
                    ..
                } if name == head => Some(compute),
                _ => None,
            })
            .unwrap()
    }

    fn stored(compute: &Compute, prefix: &str) -> HashMap<ValueId, Expr> {
        let Compute::Checked(operation) = compute else {
            panic!("checked operation expected")
        };
        operation
            .operands
            .iter()
            .enumerate()
            .map(|(index, operand)| (operand.value, symbol(format!("{prefix}{index}"))))
            .collect()
    }

    fn text(expr: &Expr) -> String {
        crate::expression_source(expr).unwrap()
    }

    fn check(source: &str) {
        let program = crate::parse_program(source).unwrap();
        crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
    }

    #[test]
    fn calls_restore_safety_from_declarations_without_widening_unsafe_scope() {
        for (declaration, keyword) in [
            ("(#fn target () #u64 (#return 42u64))", "#call"),
            (
                "(#unsafe-fn target () #u64 (#return 42u64))",
                "#unsafe-call",
            ),
            ("(#extern-fn #abi-c target () #u64)", "#unsafe-call"),
        ] {
            let source = format!(
                "{declaration}\n(#fn main () #u64 (#return (#unsafe ({keyword} target (:)))))"
            );
            let program = crate::parse_program(&source).unwrap();
            let (declarations, graph) = prepare(&source, "main");
            let context = RenderContext::new(
                &declarations.bodies["main"],
                &declarations,
                &graph,
                program.items.iter().filter_map(|item| match item {
                    crate::Item::Function(function) => Some(function),
                    _ => None,
                }),
            )
            .unwrap();
            let compute = graph
                .blocks
                .iter()
                .flat_map(|block| &block.actions)
                .find_map(|located| match &located.action {
                    Action::Compute {
                        operation: compute @ Compute::Checked(operation),
                        ..
                    } if operation.callee == declarations.function_id("target") => Some(compute),
                    _ => None,
                })
                .unwrap();
            let rendered = context.render_compute(compute, &HashMap::new()).unwrap();
            assert_eq!(text(&rendered), format!("({keyword} target ())"));
            check(&format!(
                "{declaration}\n(#fn again () #u64 (#return (#unsafe {})))",
                text(&rendered)
            ));
        }
    }

    #[test]
    fn named_calls_restore_signature_order_without_evaluating_arguments() {
        let declarations_source = "
          (#fn effect () #u32 (#return 7))
          (#fn combine ((first #u32) (second #u32)) #u32
            (#return (#u32::add-saturate first second)))";
        let source = format!(
            "{declarations_source}
          (#fn main () #u32 (#return (#call combine
            (: second (#call effect (:)) : first 3))))"
        );
        let (declarations, graph) = prepare(&source, "main");
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let compute = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| match &action.action {
                Action::Compute {
                    operation: compute @ Compute::Checked(operation),
                    ..
                } if operation.callee == declarations.function_id("combine") => Some(compute),
                _ => None,
            })
            .unwrap();
        let mut values = stored(compute, "stored");
        let rendered = context.render_compute(compute, &values).unwrap();
        assert_eq!(
            text(&rendered),
            "(#call combine ((first stored0) (second stored1)))"
        );
        assert!(!text(&rendered).contains("effect"));
        check(&format!(
            "{declarations_source} (#fn again ((stored0 #u32) (stored1 #u32)) #u32 (#return {}))",
            text(&rendered)
        ));
        values.clear();
        let missing = context.render_compute(compute, &values).unwrap_err();
        assert!(missing.message.contains("missing evaluated"));
        let Compute::Checked(checked) = compute else {
            unreachable!()
        };
        assert_eq!(
            missing.span,
            declarations.bodies["main"].nodes[checked.source.0].span
        );
        let Compute::Checked(original) = compute else {
            unreachable!()
        };
        let mut changed = original.clone();
        changed.operands.pop();
        assert!(context
            .render_compute(&Compute::Checked(changed), &HashMap::new())
            .unwrap_err()
            .message
            .contains("schema"));
    }

    #[test]
    fn assembly_replaces_nested_operands_and_keeps_static_data() {
        let (declarations, graph) = prepare(
            "
          (#fn effect () #u64 (#return 7u64))
          (#fn main () #u64 (#return (#unsafe (#asm #u64
            ((rax (#call effect (:))) (rdi 4u64)) \"add rax, rdi\"))))",
            "main",
        );
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let compute = operation(&graph, "asm");
        let rendered = context
            .render_compute(compute, &stored(compute, "stored"))
            .unwrap();
        assert_eq!(
            text(&rendered),
            "(#asm #u64 ((rax stored0) (rdi stored1)) \"add rax, rdi\")"
        );
        check(&format!(
            "(#fn again ((stored0 #u64) (stored1 #u64)) #u64 (#return (#unsafe {})))",
            text(&rendered)
        ));
    }

    #[test]
    fn static_layout_forms_and_checked_numeric_spelling_are_canonical() {
        let (declarations, graph) = prepare(
            "
          (#fn main ((count #usize)) #usize
            (#return (#usize::add-wrap count (#size-of (#tuple #u64 (#ref #u32))))))",
            "main",
        );
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let layout = operation(&graph, "size-of");
        let rendered = context.render_compute(layout, &HashMap::new()).unwrap();
        assert_eq!(text(&rendered), "(#size-of (#tuple #u64 (#ref #u32)))");
        check(&format!(
            "(#fn again () #usize (#return {}))",
            text(&rendered)
        ));
        let numeric = operation(&graph, "usize.+.wrap");
        assert_eq!(
            text(
                &context
                    .render_compute(numeric, &stored(numeric, "stored"))
                    .unwrap()
            ),
            "(#usize::add-wrap stored0 stored1)"
        );
    }

    #[test]
    fn contextual_literals_keep_their_checked_type_in_a_different_context() {
        let (declarations, graph) = prepare("(#fn main () #u32 (#return 42))", "main");
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let atom = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| match &action.action {
                Action::Compute {
                    operation:
                        compute @ Compute::Atom {
                            kind: NodeKind::Literal(Expr::Integer(42)),
                            ..
                        },
                    ..
                } => Some(compute),
                _ => None,
            })
            .unwrap();
        let rendered = context.render_compute(atom, &HashMap::new()).unwrap();
        assert_eq!(text(&rendered), "(#literal #u32 42)");
        let source = format!(
            "(#fn again () #u64 (#return (#as {} #u64)))",
            text(&rendered)
        );
        let (again, _) = prepare(&source, "again");
        assert!(again.bodies["again"].nodes.iter().any(|node| matches!(
            &node.kind,
            NodeKind::Literal(Expr::Integer(42))
        ) && node.ty == Some(Type::U32)));
        let (other, _) = prepare("(#fn main () #u64 (#return 42))", "main");
        assert!(RenderContext::new(&other.bodies["main"], &other, &graph, []).is_err());

        let (declarations, graph) = prepare("(#fn main () #f32 (#return 1.5))", "main");
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let atom = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| match &action.action {
                Action::Compute {
                    operation:
                        compute @ Compute::Atom {
                            kind: NodeKind::Literal(Expr::Float(_)),
                            ..
                        },
                    ..
                } => Some(compute),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            text(&context.render_compute(atom, &HashMap::new()).unwrap()),
            "(#literal #f32 1.5)"
        );
    }

    #[test]
    fn normalized_structs_render_explicit_keyed_literals_and_variants_stay_direct() {
        let declarations_source =
            "(#struct Pair () ((left #u32) (right #u64))) (#enum Choice () ((Choice.Some Pair) Choice.Empty))";
        let source = format!(
            "{declarations_source}
          (#fn main () Choice (#return (Choice.Some
            (#struct-literal Pair ((right 4u64) (left 3u32))))))"
        );
        let (declarations, graph) = prepare(&source, "main");
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let compute = operation(&graph, "Pair");
        let rendered = context
            .render_compute(compute, &stored(compute, "stored"))
            .unwrap();
        assert_eq!(
            text(&rendered),
            "(#struct-literal Pair ((left stored0) (right stored1)))"
        );
        check(&format!(
            "{declarations_source} (#fn again ((stored0 #u32) (stored1 #u64)) Pair (#return {}))",
            text(&rendered)
        ));
        let compute = operation(&graph, "Choice.Some");
        let rendered = context
            .render_compute(compute, &stored(compute, "stored"))
            .unwrap();
        assert_eq!(text(&rendered), "(Choice.Some stored0)");
        check(&format!(
            "{declarations_source} (#fn again ((stored0 Pair)) Choice (#return {}))",
            text(&rendered)
        ));
    }

    #[test]
    fn patterns_rename_even_unused_checked_binding_ids_without_preview_copies() {
        let (declarations, graph) = prepare(
            "
          (#enum Choice () ((Choice.Some #u64) Choice.Empty))
          (#fn main ((choice Choice)) #u64 (#return (#match choice
            (#case (Choice.Some unused) 1u64) (#case Choice.Empty 0u64))))",
            "main",
        );
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let pattern = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|action| match &action.action {
                Action::Commit(pattern) if !pattern.bindings.is_empty() => Some(pattern),
                _ => None,
            })
            .unwrap();
        assert!(context
            .render_pattern(pattern.source, &HashMap::new())
            .is_err());
        let mut names = HashMap::from([(pattern.bindings[0], "committed".to_owned())]);
        assert_eq!(
            text(&context.render_pattern(pattern.source, &names).unwrap()),
            "(Choice.Some committed)"
        );
        names.insert(pattern.bindings[0], "_".to_owned());
        assert_eq!(
            text(&context.render_pattern(pattern.source, &names).unwrap()),
            "(Choice.Some _)"
        );
    }

    #[test]
    fn aggregate_constructor_aliases_render_the_checked_concrete_type() {
        for (ty, constructor, head, canonical) in [
            ("(#tuple #u64 #u64)", "#tuple", "tuple", "#tuple"),
            ("(#array #u64 2)", "#array-of", "array", "#array-of"),
        ] {
            let source = format!(
                "(#type Pair {ty})
              (#fn make ((a #u64) (b #u64)) Pair
                (#return ({constructor} Pair a b)))"
            );
            let (declarations, graph) = prepare(&source, "make");
            let compute = operation(&graph, head);
            let context =
                RenderContext::new(&declarations.bodies["make"], &declarations, &graph, [])
                    .unwrap();
            let rendered = context
                .render_compute(compute, &stored(compute, "stored"))
                .unwrap();
            let rendered = text(&rendered);
            assert_eq!(rendered, format!("({canonical} {ty} stored0 stored1)"));
            check(&format!(
                "{source}
              (#fn again ((stored0 #u64) (stored1 #u64)) Pair (#return {rendered}))"
            ));
        }
    }

    #[test]
    fn enum_tag_test_replaces_only_the_handle_and_retains_variant_identity() {
        let (declarations, graph) = prepare(
            "(#enum Choice (#linear) ((Choice.Some #u64) Choice.Empty))
             (#fn inspect ((value (#pin-ref Choice))) #bool
               (#return (#variant-is value Choice.Some)))",
            "inspect",
        );
        let compute = operation(&graph, "#variant-is");
        let Compute::Checked(operation) = compute else {
            unreachable!()
        };
        assert_eq!(operation.operands.len(), 1);
        let context =
            RenderContext::new(&declarations.bodies["inspect"], &declarations, &graph, []).unwrap();
        let rendered = context
            .render_compute(compute, &stored(compute, "stored"))
            .unwrap();
        assert_eq!(text(&rendered), "(#variant-is stored0 Choice.Some)");
        check(&format!(
            "(#enum Choice (#linear) ((Choice.Some #u64) Choice.Empty))
          (#fn again ((stored0 (#pin-ref Choice))) #bool (#return {}))",
            text(&rendered)
        ));
    }

    #[test]
    fn executable_literal_metadata_fails_closed_instead_of_replaying_a_call() {
        let (declarations, graph) = prepare(
            "
          (#fn effect () #u64 (#return 7u64))
          (#fn main () #u64 (#return (#literal #u64 (#call effect (:)))))",
            "main",
        );
        let context =
            RenderContext::new(&declarations.bodies["main"], &declarations, &graph, []).unwrap();
        let compute = operation(&graph, "literal");
        assert!(context
            .render_compute(compute, &HashMap::new())
            .unwrap_err()
            .message
            .contains("executable metadata"));
    }
}
