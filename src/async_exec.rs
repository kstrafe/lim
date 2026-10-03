//! Executable control flow lowered from an ordinary checked async witness.
//!
//! This graph is neither a frame emitter nor an ownership proof. All runtime
//! operands are evaluated explicitly; operations refer to those values, never
//! to syntax to be evaluated again. Checked identities belong to the same
//! declaration context as the source witness and its suspension storage facts.
//! Place descriptors are address recipes, not moved copies of their owners.
//! Scope exits invalidate storage/loans; they do not invent destructors.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::async_source::CheckedAwait;
use crate::typed_body::{
    Binding, BindingId, Body, Control, Instruction, Node, NodeId, NodeKind, NumericOpcode,
    NumericOperation, PlaceRoot, Projection,
};
use crate::typed_flow::FlowNodeId;
use crate::typed_ir::{DeclarationId, FieldId, FunctionId, GlobalId, VariantId};
use crate::{Expr, Span, Type};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct BlockId(pub usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ValueId(pub usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct PlaceId(pub usize);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Error {
    pub source: Option<NodeId>,
    pub message: String,
}

fn error(source: Option<NodeId>, message: impl Into<String>) -> Error {
    Error {
        source,
        message: message.into(),
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Value {
    /// None only for semantic Unit/Bool constants introduced by lowering.
    pub source: Option<NodeId>,
    pub ty: Type,
    pub span: Option<Span>,
}

#[derive(Clone, Debug)]
pub(crate) struct Await {
    pub site_index: usize,
    pub source_path: Vec<usize>,
    pub span: Span,
    pub result_node: NodeId,
    pub child_node: NodeId,
    /// Correlation only: this ID never determines executable ordering.
    pub fact_event: FlowNodeId,
    pub driver: FunctionId,
    pub context_node: NodeId,
    pub child_type: Type,
    pub result_type: Type,
}

#[derive(Clone, Debug)]
pub(crate) struct Operand {
    /// Path beneath the checked operation, including nested asm operands.
    pub position: Vec<usize>,
    pub value: ValueId,
}

#[derive(Clone, Debug)]
pub(crate) struct Operation {
    pub source: NodeId,
    pub head: String,
    pub callee: Option<FunctionId>,
    pub numeric: Option<NumericOperation>,
    pub operands: Vec<Operand>,
    /// Reconstruction metadata. Nested containers (asm) can include original
    /// runtime nodes, but the complete operand schema MUST replace all runtime
    /// positions; an emitter must never evaluate the original operation tree.
    pub metadata: Vec<NodeId>,
}

#[derive(Clone, Debug)]
pub(crate) enum Compute {
    Checked(Operation),
    Atom { source: NodeId, kind: NodeKind },
    Identity(ValueId),
    Unit,
    Bool(bool),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AddressRoot {
    Local(BindingId),
    Global(GlobalId),
    /// An already loaded reference/pointer/slice, or an owned computed value.
    /// Handle projections snapshot the handle BEFORE a subsequent index.
    Value(ValueId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AddressProjection {
    Dereference,
    Field(FieldId),
    Tuple(usize),
    Payload(VariantId, usize),
    Index(ValueId),
    SliceIndex(ValueId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PlaceCheck {
    Bounds {
        projection: usize,
        index: ValueId,
    },
    ActivePayload {
        projection: usize,
        variant: VariantId,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PlaceDescriptor {
    pub source: Option<NodeId>,
    /// Checked access type; assignment descriptors use the checked RHS type.
    pub ty: Type,
    pub root: AddressRoot,
    pub projections: Vec<AddressProjection>,
    /// A previously formed address, whose prefix checks have already run.
    pub parent: Option<PlaceId>,
    pub checked_prefix: usize,
}

impl PlaceDescriptor {
    /// Mandatory, effectful checks executed BY Action::Place, in projection
    /// order, before subsequent operands/RHS/awaits. Load/Store must not defer
    /// or replay them. Parent prefix checks stay at the parent's action.
    pub(crate) fn checks(&self) -> Vec<PlaceCheck> {
        self.projections
            .iter()
            .enumerate()
            .skip(self.checked_prefix)
            .filter_map(|(projection, step)| match step {
                AddressProjection::Index(index) | AddressProjection::SliceIndex(index) => {
                    Some(PlaceCheck::Bounds {
                        projection,
                        index: *index,
                    })
                }
                AddressProjection::Payload(variant, _) => Some(PlaceCheck::ActivePayload {
                    projection,
                    variant: *variant,
                }),
                _ => None,
            })
            .collect()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Pattern {
    pub source: NodeId,
    pub scrutinee: ValueId,
    /// Typed lexical identities, not independently owned preview copies.
    /// Together with retained pattern metadata these describe preview aliases.
    pub bindings: Vec<BindingId>,
    /// Match payload bindings are immutable; destructuring declarations retain
    /// their checked Control::Destructure mutability, including unused names.
    pub mutable: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LoadKind {
    Read,
    Clone,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ReleaseKind {
    Drop,
    Forget,
}

#[derive(Clone, Debug)]
pub(crate) enum Action {
    Compute {
        dst: ValueId,
        operation: Compute,
    },
    /// Forms the address and executes descriptor.checks() immediately. This
    /// action is effectful even if its resulting address is otherwise unused.
    Place {
        dst: PlaceId,
        descriptor: PlaceDescriptor,
    },
    /// Read/move classification remains the checked ownership pass's job.
    Load {
        dst: ValueId,
        place: PlaceId,
        kind: LoadKind,
    },
    Bind {
        binding: BindingId,
        value: ValueId,
        mutable: bool,
    },
    Store {
        place: PlaceId,
        value: ValueId,
    },
    Borrow {
        dst: Option<ValueId>,
        place: PlaceId,
        mutable: bool,
        pinned: bool,
        scope: Option<NodeId>,
    },
    Release {
        place: PlaceId,
        kind: ReleaseKind,
    },
    Preview(Pattern),
    Commit(Pattern),
    EndPreview(Pattern),
    EndBorrow {
        scope: NodeId,
    },
    ScopeEnter(Vec<BindingId>),
    ScopeExit(Vec<BindingId>),
}

#[derive(Clone, Debug)]
pub(crate) struct LocatedAction {
    pub source: Option<NodeId>,
    pub span: Option<Span>,
    pub unsafe_context: bool,
    pub action: Action,
}

#[derive(Clone, Debug)]
pub(crate) enum Argument {
    Value(ValueId),
    /// Produced only on this await's Ready edge, never on Pending.
    Ready(usize),
}

#[derive(Clone, Debug)]
pub(crate) struct Edge {
    pub target: BlockId,
    pub arguments: Vec<Argument>,
}

#[derive(Clone, Debug)]
pub(crate) enum Terminator {
    Goto(Edge),
    Branch {
        condition: ValueId,
        yes: Edge,
        no: Edge,
    },
    PatternTest {
        pattern: Pattern,
        yes: Edge,
        no: Edge,
    },
    /// Pending replaces the child slot with the protocol's returned child,
    /// then returns to the caller. Resume retries this block, not its incoming
    /// construction path. Ready alone initializes its edge's result parameter.
    Await {
        site: usize,
        child: ValueId,
        ready: Edge,
        pending: BlockId,
    },
    Return(Option<ValueId>),
    Diverge,
}

#[derive(Clone, Debug)]
pub(crate) struct Block {
    pub parameters: Vec<ValueId>,
    pub actions: Vec<LocatedAction>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug)]
pub(crate) struct Graph {
    pub bindings: Vec<Binding>,
    pub parameter_count: usize,
    pub values: Vec<Value>,
    pub places: Vec<PlaceDescriptor>,
    pub awaits: Vec<Await>,
    /// Owned checked metadata/pattern nodes; not executable subtrees.
    pub metadata: HashMap<NodeId, Node>,
    pub blocks: Vec<Block>,
    pub entry: BlockId,
    pub values_by_node: HashMap<NodeId, ValueId>,
    operation_schemas: HashMap<NodeId, OperationSchema>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OperationSchema {
    runtime: Vec<(Vec<usize>, NodeId)>,
    metadata: Vec<NodeId>,
}

/// Single schema used by lowering AND boundary validation. Types come only
/// from checked nodes; operator structure selects evaluation/metadata roles.
fn operation_schema(body: &Body, source: NodeId) -> Result<OperationSchema, Error> {
    let node = body
        .nodes
        .get(source.0)
        .ok_or_else(|| error(Some(source), "operation outside checked body"))?;
    let NodeKind::Form {
        head,
        children,
        callee,
        ..
    } = &node.kind
    else {
        return Err(error(Some(source), "operation has no checked form"));
    };
    let get = |id: NodeId| {
        body.nodes
            .get(id.0)
            .ok_or_else(|| error(Some(id), "operand outside checked body"))
    };
    let mut runtime = Vec::new();
    if callee.is_none() && head == "asm" {
        if children.len() != 4 {
            return Err(error(Some(source), "invalid checked assembly form"));
        }
        let pairs = match &get(children[2])?.kind {
            NodeKind::Syntax(children) | NodeKind::Form { children, .. } => children,
            _ => return Err(error(Some(source), "unstructured assembly operands")),
        };
        for (index, &pair) in pairs.iter().enumerate() {
            let parts = match &get(pair)?.kind {
                NodeKind::Syntax(children) | NodeKind::Form { children, .. } => children,
                _ => return Err(error(Some(pair), "unstructured assembly operand")),
            };
            if parts.len() != 2 || get(parts[1])?.ty.is_none() {
                return Err(error(
                    Some(pair),
                    "assembly operand lacks a checked runtime value",
                ));
            }
            runtime.push((vec![2, index, 1], parts[1]));
        }
        return Ok(OperationSchema {
            runtime,
            metadata: children.clone(),
        });
    }
    let static_only = callee.is_none()
        && matches!(
            head.as_str(),
            "literal" | "size-of" | "align-of" | "offset-of"
        );
    let mut metadata = Vec::new();
    for (position, &child) in children.iter().enumerate() {
        if position != 0 && !static_only && get(child)?.ty.is_some() {
            runtime.push((vec![position], child));
        } else {
            if position != 0 && callee.is_some() {
                return Err(error(
                    Some(child),
                    "call operand has no checked runtime type",
                ));
            }
            metadata.push(child);
        }
    }
    Ok(OperationSchema { runtime, metadata })
}

#[derive(Clone)]
enum Scope {
    Bindings(Vec<BindingId>),
    Borrow(NodeId),
    Preview(Pattern),
}

#[derive(Clone)]
struct Target {
    name: Option<String>,
    break_to: BlockId,
    break_result: Option<ValueId>,
    continue_to: Option<BlockId>,
    scope_depth: usize,
}

struct Builder<'a> {
    body: &'a Body,
    graph: Graph,
    sites: HashMap<NodeId, usize>,
    scopes: Vec<Scope>,
    targets: Vec<Target>,
    active: HashSet<NodeId>,
    unsafe_context: bool,
}

/// Lower a checked ordinary witness. The input sites are authoritative await
/// identities, not spans/callee names or an independent source CFG. Poll/cancel
/// protocol names remain in Lowered.awaits[site_index], in the same context.
pub(crate) fn build(body: &Body, sites: &[CheckedAwait]) -> Result<Graph, Error> {
    if body.parameter_count > body.bindings.len() {
        return Err(error(None, "invalid checked parameter boundary"));
    }
    let mut awaits = Vec::new();
    let mut by_node = HashMap::new();
    let mut paths = HashSet::new();
    for (index, site) in sites.iter().enumerate() {
        let result = body.nodes.get(site.result_value.0).ok_or_else(|| {
            error(
                Some(site.result_value),
                "await result is outside the checked body",
            )
        })?;
        let NodeKind::Form {
            callee: Some(driver),
            children,
            ..
        } = &result.kind
        else {
            return Err(error(
                Some(site.result_value),
                "await is not a checked driver call",
            ));
        };
        if children.len() != 3
            || children[1] != site.child_value
            || result.ty.as_ref() != Some(&site.result_type)
            || body
                .nodes
                .get(site.child_value.0)
                .and_then(|node| node.ty.as_ref())
                != Some(&site.child_type)
        {
            return Err(error(
                Some(site.result_value),
                "await mapping disagrees with checked operands/types",
            ));
        }
        if by_node.insert(site.result_value, index).is_some()
            || !paths.insert(site.source_path.clone())
        {
            return Err(error(
                Some(site.result_value),
                "duplicate checked await identity or source path",
            ));
        }
        awaits.push(Await {
            site_index: index,
            source_path: site.source_path.clone(),
            span: site.span,
            result_node: site.result_value,
            child_node: site.child_value,
            fact_event: site.call,
            driver: *driver,
            context_node: children[2],
            child_type: site.child_type.clone(),
            result_type: site.result_type.clone(),
        });
    }
    let mut builder = Builder {
        body,
        sites: by_node,
        scopes: Vec::new(),
        targets: Vec::new(),
        active: HashSet::new(),
        unsafe_context: false,
        graph: Graph {
            bindings: body.bindings.clone(),
            parameter_count: body.parameter_count,
            values: Vec::new(),
            places: Vec::new(),
            awaits,
            metadata: HashMap::new(),
            blocks: Vec::new(),
            entry: BlockId(0),
            values_by_node: HashMap::new(),
            operation_schemas: HashMap::new(),
        },
    };
    let entry = builder.block(Vec::new());
    builder.graph.entry = entry;
    if let Some(end) = builder.scoped(&body.instructions, entry)? {
        builder.graph.blocks[end.0].terminator = Terminator::Return(None);
    }
    builder.graph.validate()?;
    builder.graph.validate_against(body)?;
    Ok(builder.graph)
}

impl Builder<'_> {
    fn node(&self, id: NodeId) -> Result<&Node, Error> {
        self.body
            .nodes
            .get(id.0)
            .ok_or_else(|| error(Some(id), "node is outside the checked body"))
    }

    fn ty(&self, id: NodeId) -> Result<Type, Error> {
        self.node(id)?
            .ty
            .clone()
            .ok_or_else(|| error(Some(id), "runtime node has no checked type"))
    }

    fn value(&mut self, id: NodeId) -> Result<ValueId, Error> {
        if let Some(value) = self.graph.values_by_node.get(&id) {
            return Ok(*value);
        }
        let ty = self.ty(id)?;
        let span = self.node(id)?.span;
        let value = ValueId(self.graph.values.len());
        self.graph.values.push(Value {
            source: Some(id),
            ty,
            span,
        });
        self.graph.values_by_node.insert(id, value);
        Ok(value)
    }

    fn constant(&mut self, block: BlockId, boolean: Option<bool>) -> ValueId {
        let value = ValueId(self.graph.values.len());
        self.graph.values.push(Value {
            source: None,
            ty: if boolean.is_some() {
                Type::Bool
            } else {
                Type::Unit
            },
            span: None,
        });
        self.action(
            block,
            None,
            Action::Compute {
                dst: value,
                operation: boolean.map_or(Compute::Unit, Compute::Bool),
            },
        );
        value
    }

    fn block(&mut self, parameters: Vec<ValueId>) -> BlockId {
        let id = BlockId(self.graph.blocks.len());
        self.graph.blocks.push(Block {
            parameters,
            actions: Vec::new(),
            terminator: Terminator::Diverge,
        });
        id
    }

    fn edge(target: BlockId) -> Edge {
        Edge {
            target,
            arguments: Vec::new(),
        }
    }

    fn goto(&mut self, block: BlockId, target: BlockId) {
        self.graph.blocks[block.0].terminator = Terminator::Goto(Self::edge(target));
    }

    fn select(&mut self, block: BlockId, target: BlockId, value: ValueId) {
        self.graph.blocks[block.0].terminator = Terminator::Goto(Edge {
            target,
            arguments: vec![Argument::Value(value)],
        });
    }

    fn action(&mut self, block: BlockId, source: Option<NodeId>, action: Action) {
        let span = source.and_then(|id| self.body.nodes.get(id.0).and_then(|node| node.span));
        self.graph.blocks[block.0].actions.push(LocatedAction {
            source,
            span,
            unsafe_context: self.unsafe_context,
            action,
        });
    }

    fn metadata(&mut self, source: NodeId) -> Result<(), Error> {
        if self.graph.metadata.contains_key(&source) {
            return Ok(());
        }
        let node = self.node(source)?.clone();
        self.graph.metadata.insert(source, node.clone());
        match node.kind {
            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                for child in children {
                    self.metadata(child)?;
                }
            }
            NodeKind::Labeled(_, child) | NodeKind::Quoted(_, child) => self.metadata(child)?,
            _ => {}
        }
        Ok(())
    }

    fn pattern(
        &mut self,
        source: NodeId,
        scrutinee: ValueId,
        mutable: bool,
    ) -> Result<Pattern, Error> {
        let mut pending = vec![source];
        let mut seen = HashSet::new();
        let mut bindings = HashSet::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            match self.node(id)?.kind.clone() {
                NodeKind::Symbol {
                    binding: Some(binding),
                    ..
                } => {
                    if self.body.bindings.get(binding.0).is_none() {
                        return Err(error(Some(id), "pattern has no checked binding"));
                    }
                    bindings.insert(binding);
                }
                NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                    pending.extend(children)
                }
                NodeKind::Labeled(_, child) => pending.push(child),
                NodeKind::Declaration(_) | NodeKind::Literal(_) | NodeKind::Symbol { .. } => {}
                _ => return Err(error(Some(id), "unsupported checked pattern structure")),
            }
        }
        self.metadata(source)?;
        let mut bindings = bindings.into_iter().collect::<Vec<_>>();
        bindings.sort_by_key(|id| id.0);
        Ok(Pattern {
            source,
            scrutinee,
            bindings,
            mutable,
        })
    }

    fn direct_bindings(&mut self, instructions: &[Instruction]) -> Result<Vec<BindingId>, Error> {
        let mut bindings = HashSet::new();
        let mut pending = instructions.iter().collect::<Vec<_>>();
        while let Some(instruction) = pending.pop() {
            match &instruction.control {
                Control::Bind(binding, _, _) => {
                    bindings.insert(*binding);
                }
                Control::Destructure { pattern, .. } => {
                    // Pattern collection only; no execution or synthetic value.
                    let mut nodes = vec![*pattern];
                    let mut seen = HashSet::new();
                    while let Some(id) = nodes.pop() {
                        if !seen.insert(id) {
                            continue;
                        }
                        match &self.node(id)?.kind {
                            NodeKind::Symbol {
                                binding: Some(binding),
                                ..
                            } => {
                                bindings.insert(*binding);
                            }
                            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                                nodes.extend(children.iter().copied())
                            }
                            NodeKind::Labeled(_, child) => nodes.push(*child),
                            _ => {}
                        }
                    }
                }
                Control::Labeled(_, inner) => pending.push(inner),
                _ => {}
            }
        }
        let mut bindings = bindings.into_iter().collect::<Vec<_>>();
        bindings.sort_by_key(|id| id.0);
        Ok(bindings)
    }

    fn enter(&mut self, block: BlockId, bindings: Vec<BindingId>) {
        self.action(block, None, Action::ScopeEnter(bindings.clone()));
        self.scopes.push(Scope::Bindings(bindings));
    }

    fn cleanup(&mut self, block: BlockId, depth: usize) {
        for scope in self.scopes[depth..]
            .iter()
            .rev()
            .cloned()
            .collect::<Vec<_>>()
        {
            match scope {
                Scope::Bindings(bindings) => self.action(block, None, Action::ScopeExit(bindings)),
                Scope::Borrow(scope) => {
                    self.action(block, Some(scope), Action::EndBorrow { scope })
                }
                Scope::Preview(pattern) => {
                    self.action(block, Some(pattern.source), Action::EndPreview(pattern))
                }
            }
        }
    }

    fn instructions(
        &mut self,
        instructions: &[Instruction],
        start: BlockId,
    ) -> Result<Option<BlockId>, Error> {
        let mut current = Some(start);
        for instruction in instructions {
            let Some(block) = current else {
                break;
            };
            current = self.instruction(instruction, block, None)?;
        }
        Ok(current)
    }

    fn scoped(
        &mut self,
        instructions: &[Instruction],
        start: BlockId,
    ) -> Result<Option<BlockId>, Error> {
        let depth = self.scopes.len();
        let bindings = self.direct_bindings(instructions)?;
        self.enter(start, bindings);
        let end = self.instructions(instructions, start)?;
        if let Some(end) = end {
            self.cleanup(end, depth);
        }
        self.scopes.truncate(depth);
        Ok(end)
    }

    fn instruction(
        &mut self,
        instruction: &Instruction,
        block: BlockId,
        label: Option<&str>,
    ) -> Result<Option<BlockId>, Error> {
        match &instruction.control {
            Control::Bind(binding, source, mutable) => {
                let (end, value) = self.expression(*source, block)?;
                if let Some(end) = end {
                    self.action(
                        end,
                        Some(*source),
                        Action::Bind {
                            binding: *binding,
                            value,
                            mutable: *mutable,
                        },
                    );
                }
                Ok(end)
            }
            Control::Evaluate(source) => self.expression(*source, block).map(|(end, _)| end),
            Control::Assign(root, projection, source) => {
                let (end, place) = self.assignment_place(root, projection, *source, block)?;
                let Some(end) = end else {
                    return Ok(None);
                };
                let (end, value) = self.expression(*source, end)?;
                if let Some(end) = end {
                    self.action(end, Some(*source), Action::Store { place, value });
                }
                Ok(end)
            }
            Control::Destructure {
                pattern,
                value: source,
                otherwise,
                mutable,
                ..
            } => {
                let (end, value) = self.expression(*source, block)?;
                let Some(end) = end else {
                    return Ok(None);
                };
                let pattern = self.pattern(*pattern, value, *mutable)?;
                if let Some(otherwise) = otherwise {
                    let yes = self.block(Vec::new());
                    let no = self.block(Vec::new());
                    let join = self.block(Vec::new());
                    self.graph.blocks[end.0].terminator = Terminator::PatternTest {
                        pattern: pattern.clone(),
                        yes: Self::edge(yes),
                        no: Self::edge(no),
                    };
                    self.action(yes, Some(pattern.source), Action::Commit(pattern));
                    self.goto(yes, join);
                    if let Some(end) = self.scoped(otherwise, no)? {
                        self.goto(end, join);
                    }
                    Ok(Some(join))
                } else {
                    self.action(end, Some(pattern.source), Action::Commit(pattern));
                    Ok(Some(end))
                }
            }
            Control::While(condition, body) => self.while_loop(*condition, body, block, label),
            Control::Loop(body) => self.loop_body(body, block, label, None),
            Control::For(init, condition, step, body) => {
                self.for_loop(init, *condition, step, body, block, label)
            }
            Control::Labeled(name, inner) => {
                if matches!(
                    inner.control,
                    Control::While(..) | Control::Loop(..) | Control::For(..)
                ) {
                    self.instruction(inner, block, Some(name))
                } else {
                    let exit = self.block(Vec::new());
                    self.targets.push(Target {
                        name: Some(name.clone()),
                        break_to: exit,
                        break_result: None,
                        continue_to: None,
                        scope_depth: self.scopes.len(),
                    });
                    let end = self.instruction(inner, block, None)?;
                    self.targets.pop();
                    if let Some(end) = end {
                        self.goto(end, exit);
                    }
                    Ok(Some(exit))
                }
            }
            Control::Return(source) => {
                let (end, value) = match source {
                    Some(source) => {
                        let (end, value) = self.expression(*source, block)?;
                        (end, Some(value))
                    }
                    None => (Some(block), None),
                };
                if let Some(end) = end {
                    self.cleanup(end, 0);
                    self.graph.blocks[end.0].terminator = Terminator::Return(value);
                }
                Ok(None)
            }
            Control::Break(label, source) => {
                let target = self.target(label.as_deref(), false)?;
                let (end, value) = match source {
                    Some(source) => {
                        let (end, value) = self.expression(*source, block)?;
                        (end, Some(value))
                    }
                    None => (Some(block), None),
                };
                if let Some(end) = end {
                    let value = if target.break_result.is_some() {
                        Some(value.unwrap_or_else(|| self.constant(end, None)))
                    } else {
                        if let Some(value) = value {
                            if self.graph.values[value.0].ty != Type::Unit {
                                return Err(error(
                                    source.as_ref().copied(),
                                    "value break has no result destination",
                                ));
                            }
                        }
                        None
                    };
                    self.cleanup(end, target.scope_depth);
                    if let Some(value) = value {
                        self.select(end, target.break_to, value);
                    } else {
                        self.goto(end, target.break_to);
                    }
                }
                Ok(None)
            }
            Control::Continue(label) => {
                let target = self.target(label.as_deref(), true)?;
                self.cleanup(block, target.scope_depth);
                self.goto(block, target.continue_to.expect("continue target checked"));
                Ok(None)
            }
        }
    }

    fn target(&self, label: Option<&str>, continuing: bool) -> Result<Target, Error> {
        let target = self
            .targets
            .iter()
            .rev()
            .find(|target| match label {
                Some(label) => target.name.as_deref() == Some(label),
                None => target.continue_to.is_some(),
            })
            .ok_or_else(|| error(None, format!("no executable transfer target for {label:?}")))?;
        if continuing && target.continue_to.is_none() {
            return Err(error(None, "continue targets a non-loop label"));
        }
        Ok(target.clone())
    }

    fn while_loop(
        &mut self,
        condition: NodeId,
        body: &[Instruction],
        block: BlockId,
        label: Option<&str>,
    ) -> Result<Option<BlockId>, Error> {
        let header = self.block(Vec::new());
        let start = self.block(Vec::new());
        let exit = self.block(Vec::new());
        self.goto(block, header);
        let (end, condition) = self.expression(condition, header)?;
        if let Some(end) = end {
            self.graph.blocks[end.0].terminator = Terminator::Branch {
                condition,
                yes: Self::edge(start),
                no: Self::edge(exit),
            };
        }
        self.targets.push(Target {
            name: label.map(str::to_owned),
            break_to: exit,
            break_result: None,
            continue_to: Some(header),
            scope_depth: self.scopes.len(),
        });
        if let Some(end) = self.scoped(body, start)? {
            self.goto(end, header);
        }
        self.targets.pop();
        Ok(Some(exit))
    }

    fn loop_body(
        &mut self,
        body: &[Instruction],
        block: BlockId,
        label: Option<&str>,
        result: Option<ValueId>,
    ) -> Result<Option<BlockId>, Error> {
        let header = self.block(Vec::new());
        let exit = self.block(result.into_iter().collect());
        self.goto(block, header);
        self.targets.push(Target {
            name: label.map(str::to_owned),
            break_to: exit,
            break_result: result,
            continue_to: Some(header),
            scope_depth: self.scopes.len(),
        });
        if let Some(end) = self.scoped(body, header)? {
            self.goto(end, header);
        }
        self.targets.pop();
        Ok(Some(exit))
    }

    fn for_loop(
        &mut self,
        init: &Instruction,
        condition: NodeId,
        step: &Instruction,
        body: &[Instruction],
        block: BlockId,
        label: Option<&str>,
    ) -> Result<Option<BlockId>, Error> {
        let depth = self.scopes.len();
        let bindings = self.direct_bindings(std::slice::from_ref(init))?;
        self.enter(block, bindings);
        let init_end = self.instruction(init, block, None)?;
        let header = self.block(Vec::new());
        let body_start = self.block(Vec::new());
        let step_start = self.block(Vec::new());
        let exit = self.block(Vec::new());
        if let Some(end) = init_end {
            self.goto(end, header);
        }
        let (end, condition) = self.expression(condition, header)?;
        if let Some(end) = end {
            self.graph.blocks[end.0].terminator = Terminator::Branch {
                condition,
                yes: Self::edge(body_start),
                no: Self::edge(exit),
            };
        }
        // Match ordinary flow: the step is lowered outside this loop's
        // transfer-target context; body continue enters the step, not header.
        if let Some(end) = self.instruction(step, step_start, None)? {
            self.goto(end, header);
        }
        self.targets.push(Target {
            name: label.map(str::to_owned),
            break_to: exit,
            break_result: None,
            continue_to: Some(step_start),
            scope_depth: self.scopes.len(),
        });
        if let Some(end) = self.scoped(body, body_start)? {
            self.goto(end, step_start);
        }
        self.targets.pop();
        self.cleanup(exit, depth);
        self.scopes.truncate(depth);
        Ok(Some(exit))
    }

    fn expression(
        &mut self,
        source: NodeId,
        block: BlockId,
    ) -> Result<(Option<BlockId>, ValueId), Error> {
        if !self.active.insert(source) {
            return Err(error(Some(source), "cyclic checked expression"));
        }
        let result = self.expression_inner(source, block).map(|(end, value)| {
            // Structured Never expressions may have an unreachable join/loop
            // exit, but must never supply a normal-return operand or binding.
            if self.graph.values[value.0].ty == Type::Never {
                (None, value)
            } else {
                (end, value)
            }
        });
        self.active.remove(&source);
        result
    }

    fn expression_inner(
        &mut self,
        source: NodeId,
        block: BlockId,
    ) -> Result<(Option<BlockId>, ValueId), Error> {
        let node = self.node(source)?.clone();
        let dst = self.value(source)?;
        if let Some(&site) = self.sites.get(&source) {
            let child_node = self.graph.awaits[site].child_node;
            let (end, child) = self.expression(child_node, block)?;
            let Some(end) = end else {
                return Ok((None, dst));
            };
            let poll = self.block(Vec::new());
            let ready = self.block(vec![dst]);
            self.goto(end, poll);
            self.graph.blocks[poll.0].terminator = Terminator::Await {
                site,
                child,
                ready: Edge {
                    target: ready,
                    arguments: vec![Argument::Ready(site)],
                },
                pending: poll,
            };
            return Ok((Some(ready), dst));
        }
        match node.kind {
            NodeKind::If {
                condition,
                then_value,
                else_value,
                ..
            } => {
                let (end, condition) = self.expression(condition, block)?;
                let Some(end) = end else {
                    return Ok((None, dst));
                };
                let yes = self.block(Vec::new());
                let no = self.block(Vec::new());
                let join = self.block(vec![dst]);
                self.graph.blocks[end.0].terminator = Terminator::Branch {
                    condition,
                    yes: Self::edge(yes),
                    no: Self::edge(no),
                };
                let (end, value) = self.expression(then_value, yes)?;
                if let Some(end) = end {
                    self.select(end, join, value);
                }
                if let Some(otherwise) = else_value {
                    let (end, value) = self.expression(otherwise, no)?;
                    if let Some(end) = end {
                        self.select(end, join, value);
                    }
                } else {
                    let unit = self.constant(no, None);
                    self.select(no, join, unit);
                }
                Ok((Some(join), dst))
            }
            NodeKind::Match { value, arms, .. } => {
                self.match_value(source, dst, value, &arms, block)
            }
            NodeKind::Block(instructions) => {
                let depth = self.scopes.len();
                let bindings = self.direct_bindings(&instructions)?;
                self.enter(block, bindings);
                let (prefix, tail) = match instructions.split_last() {
                    Some((
                        Instruction {
                            control: Control::Evaluate(value),
                            ..
                        },
                        prefix,
                    )) => (prefix, Some(*value)),
                    _ => (instructions.as_slice(), None),
                };
                let mut end = self.instructions(prefix, block)?;
                let mut result = None;
                if let Some(current) = end {
                    if let Some(tail) = tail {
                        let (tail_end, value) = self.expression(tail, current)?;
                        end = tail_end;
                        result = Some(value);
                    }
                }
                if let Some(current) = end {
                    self.cleanup(current, depth);
                    let operation = result.map_or(Compute::Unit, Compute::Identity);
                    self.action(current, Some(source), Action::Compute { dst, operation });
                }
                self.scopes.truncate(depth);
                Ok((end, dst))
            }
            NodeKind::Loop(instructions) => {
                let end = self.loop_body(&instructions, block, None, Some(dst))?;
                Ok((end, dst))
            }
            NodeKind::Labeled(label, child) => {
                if let NodeKind::Loop(instructions) = self.node(child)?.kind.clone() {
                    let inner = self.value(child)?;
                    let end = self.loop_body(&instructions, block, Some(&label), Some(inner))?;
                    if let Some(end) = end {
                        self.action(
                            end,
                            Some(source),
                            Action::Compute {
                                dst,
                                operation: Compute::Identity(inner),
                            },
                        );
                    }
                    Ok((end, dst))
                } else {
                    let join = self.block(vec![dst]);
                    self.targets.push(Target {
                        name: Some(label),
                        break_to: join,
                        break_result: Some(dst),
                        continue_to: None,
                        scope_depth: self.scopes.len(),
                    });
                    let (end, value) = self.expression(child, block)?;
                    self.targets.pop();
                    if let Some(end) = end {
                        self.select(end, join, value);
                    }
                    Ok((Some(join), dst))
                }
            }
            NodeKind::Form {
                head,
                children,
                numeric,
                callee,
                ..
            } => {
                if callee.is_none() && head == "unsafe" {
                    if children.len() != 2 {
                        return Err(error(Some(source), "unsupported unsafe wrapper"));
                    }
                    let outer = self.unsafe_context;
                    self.unsafe_context = true;
                    let result = self.expression(children[1], block);
                    self.unsafe_context = outer;
                    let (end, value) = result?;
                    if let Some(end) = end {
                        self.action(
                            end,
                            Some(source),
                            Action::Compute {
                                dst,
                                operation: Compute::Identity(value),
                            },
                        );
                    }
                    Ok((end, dst))
                } else if numeric.as_ref().is_some_and(|op| {
                    matches!(
                        op.operation,
                        NumericOpcode::LogicalAnd | NumericOpcode::LogicalOr
                    )
                }) {
                    self.short_circuit(
                        source,
                        dst,
                        &children,
                        numeric.as_ref().unwrap().operation,
                        block,
                    )
                } else if callee.is_none() {
                    self.builtin(source, dst, &head, &children, numeric, block)
                } else {
                    self.operation(source, dst, head, children, numeric, callee, block)
                }
            }
            NodeKind::Symbol {
                binding: Some(_), ..
            }
            | NodeKind::Declaration(DeclarationId::Global(_)) => {
                let (end, place) = self.address(source, block)?;
                if let Some(end) = end {
                    self.action(
                        end,
                        Some(source),
                        Action::Load {
                            dst,
                            place,
                            kind: LoadKind::Read,
                        },
                    );
                }
                Ok((end, dst))
            }
            NodeKind::Syntax(children)
                if children.is_empty() && self.graph.values[dst.0].ty == Type::Unit =>
            {
                self.action(
                    block,
                    Some(source),
                    Action::Compute {
                        dst,
                        operation: Compute::Unit,
                    },
                );
                Ok((Some(block), dst))
            }
            kind @ (NodeKind::Literal(_)
            | NodeKind::Symbol { binding: None, .. }
            | NodeKind::Declaration(_)) => {
                self.action(
                    block,
                    Some(source),
                    Action::Compute {
                        dst,
                        operation: Compute::Atom { source, kind },
                    },
                );
                Ok((Some(block), dst))
            }
            _ => Err(error(
                Some(source),
                "syntax/pattern/quote is not an executable checked value",
            )),
        }
    }

    fn short_circuit(
        &mut self,
        source: NodeId,
        dst: ValueId,
        children: &[NodeId],
        opcode: NumericOpcode,
        block: BlockId,
    ) -> Result<(Option<BlockId>, ValueId), Error> {
        if children.len() != 3 {
            return Err(error(Some(source), "invalid short-circuit operands"));
        }
        let (end, left) = self.expression(children[1], block)?;
        let Some(end) = end else {
            return Ok((None, dst));
        };
        let right = self.block(Vec::new());
        let short = self.block(Vec::new());
        let join = self.block(vec![dst]);
        let conjunction = opcode == NumericOpcode::LogicalAnd;
        let (yes, no) = if conjunction {
            (right, short)
        } else {
            (short, right)
        };
        self.graph.blocks[end.0].terminator = Terminator::Branch {
            condition: left,
            yes: Self::edge(yes),
            no: Self::edge(no),
        };
        let constant = self.constant(short, Some(!conjunction));
        self.select(short, join, constant);
        let (end, value) = self.expression(children[2], right)?;
        if let Some(end) = end {
            self.select(end, join, value);
        }
        Ok((Some(join), dst))
    }

    fn match_value(
        &mut self,
        _source: NodeId,
        dst: ValueId,
        scrutinee: NodeId,
        arms: &[NodeId],
        block: BlockId,
    ) -> Result<(Option<BlockId>, ValueId), Error> {
        let (end, value) = self.expression(scrutinee, block)?;
        let Some(mut test) = end else {
            return Ok((None, dst));
        };
        let join = self.block(vec![dst]);
        for &arm in arms {
            let NodeKind::MatchArm { pattern, values } = self.node(arm)?.kind.clone() else {
                return Err(error(Some(arm), "match has an unstructured arm"));
            };
            let (guard, body) = match values.as_slice() {
                [body] => (None, *body),
                [guard, body] => {
                    let NodeKind::Form { head, children, .. } = self.node(*guard)?.kind.clone()
                    else {
                        return Err(error(Some(*guard), "unstructured match guard"));
                    };
                    if head != "when" || children.len() != 2 {
                        return Err(error(Some(*guard), "invalid match guard"));
                    }
                    (Some(children[1]), *body)
                }
                _ => return Err(error(Some(arm), "unsupported match arm sequence")),
            };
            let pattern = self.pattern(pattern, value, false)?;
            let success = self.block(Vec::new());
            let failure = self.block(Vec::new());
            self.graph.blocks[test.0].terminator = Terminator::PatternTest {
                pattern: pattern.clone(),
                yes: Self::edge(success),
                no: Self::edge(failure),
            };
            let depth = self.scopes.len();
            self.enter(success, pattern.bindings.clone());
            let body_start = if let Some(guard) = guard {
                self.action(
                    success,
                    Some(pattern.source),
                    Action::Preview(pattern.clone()),
                );
                self.scopes.push(Scope::Preview(pattern.clone()));
                let (end, guard_value) = self.expression(guard, success)?;
                let commit = self.block(Vec::new());
                let reject = self.block(Vec::new());
                if let Some(end) = end {
                    self.graph.blocks[end.0].terminator = Terminator::Branch {
                        condition: guard_value,
                        yes: Self::edge(commit),
                        no: Self::edge(reject),
                    };
                }
                // Guard effects stay executed; only aliases/scope are removed.
                self.cleanup(reject, depth);
                self.goto(reject, failure);
                self.scopes.pop();
                commit
            } else {
                success
            };
            self.action(
                body_start,
                Some(pattern.source),
                Action::Commit(pattern.clone()),
            );
            let (end, result) = self.expression(body, body_start)?;
            if let Some(end) = end {
                self.cleanup(end, depth);
                self.select(end, join, result);
            }
            self.scopes.truncate(depth);
            test = failure;
        }
        // Exhaustiveness belongs to ordinary checking. Its impossible final
        // pattern-failure edge is explicit rather than an invented value.
        self.graph.blocks[test.0].terminator = Terminator::Diverge;
        Ok((Some(join), dst))
    }

    fn operation(
        &mut self,
        source: NodeId,
        dst: ValueId,
        head: String,
        _children: Vec<NodeId>,
        numeric: Option<NumericOperation>,
        callee: Option<FunctionId>,
        block: BlockId,
    ) -> Result<(Option<BlockId>, ValueId), Error> {
        let mut end = Some(block);
        let mut operands = Vec::new();
        let schema = operation_schema(self.body, source)?;
        self.graph.operation_schemas.insert(source, schema.clone());
        for (position, child) in &schema.runtime {
            let Some(current) = end else {
                break;
            };
            let (next, value) = self.expression(*child, current)?;
            end = next;
            operands.push(Operand {
                position: position.clone(),
                value,
            });
        }
        for &child in &schema.metadata {
            self.metadata(child)?;
        }
        if let Some(current) = end {
            self.action(
                current,
                Some(source),
                Action::Compute {
                    dst,
                    operation: Compute::Checked(Operation {
                        source,
                        head,
                        callee,
                        numeric,
                        operands,
                        metadata: schema.metadata,
                    }),
                },
            );
            if self.graph.values[dst.0].ty == Type::Never {
                self.graph.blocks[current.0].terminator = Terminator::Diverge;
                end = None;
            }
        }
        Ok((end, dst))
    }

    fn builtin(
        &mut self,
        source: NodeId,
        dst: ValueId,
        head: &str,
        children: &[NodeId],
        numeric: Option<NumericOperation>,
        block: BlockId,
    ) -> Result<(Option<BlockId>, ValueId), Error> {
        match head {
            "panic" | "unreachable" => {
                // Keep the checked panic operation (not just a silent trap).
                self.operation(
                    source,
                    dst,
                    head.to_owned(),
                    children.to_vec(),
                    numeric,
                    None,
                    block,
                )
            }
            "get" | "get-payload" | "index" | "deref" | "pin-read" => {
                let (end, place) = self.address(source, block)?;
                if let Some(end) = end {
                    self.action(
                        end,
                        Some(source),
                        Action::Load {
                            dst,
                            place,
                            kind: LoadKind::Read,
                        },
                    );
                }
                Ok((end, dst))
            }
            "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" => {
                if !matches!(children.len(), 2 | 3) {
                    return Err(error(Some(source), "invalid borrow arity"));
                }
                if children.len() == 3 && matches!(head, "pin-borrow" | "pin-borrow-mut") {
                    return Err(error(Some(source), "unsupported scoped pinned borrow"));
                }
                let (end, place) = self.address(children[1], block)?;
                let Some(end) = end else {
                    return Ok((None, dst));
                };
                let scoped = children.len() == 3;
                let pinned = if scoped {
                    self.scoped_place_pinned(children[1])?
                } else {
                    // #borrow through a pinned base inherits pinning even
                    // though its spelling has no pin- prefix.
                    matches!(self.ty(source)?, Type::PinnedReference { .. })
                };
                self.action(
                    end,
                    Some(source),
                    Action::Borrow {
                        dst: (!scoped).then_some(dst),
                        place,
                        mutable: matches!(head, "borrow-mut" | "pin-borrow-mut"),
                        pinned,
                        scope: scoped.then_some(source),
                    },
                );
                if scoped {
                    let depth = self.scopes.len();
                    self.scopes.push(Scope::Borrow(source));
                    let (end, result) = self.expression(children[2], end)?;
                    if let Some(end) = end {
                        self.cleanup(end, depth);
                        self.action(
                            end,
                            Some(source),
                            Action::Compute {
                                dst,
                                operation: Compute::Identity(result),
                            },
                        );
                    }
                    self.scopes.truncate(depth);
                    Ok((end, dst))
                } else {
                    Ok((Some(end), dst))
                }
            }
            "slice-idx" | "slice-mut-idx" | "pin-get-payload" | "pin-get-payload-mut" => {
                let target = match self.ty(source)? {
                    Type::Reference { target, .. } | Type::PinnedReference { target, .. } => {
                        *target
                    }
                    _ => {
                        return Err(error(
                            Some(source),
                            "projected borrow has no checked reference type",
                        ))
                    }
                };
                let (end, place) = self.projected_address(source, block, target)?;
                if let Some(end) = end {
                    self.action(
                        end,
                        Some(source),
                        Action::Borrow {
                            dst: Some(dst),
                            place,
                            mutable: matches!(head, "slice-mut-idx" | "pin-get-payload-mut"),
                            pinned: head.starts_with("pin-"),
                            scope: None,
                        },
                    );
                }
                Ok((end, dst))
            }
            "clone" | "drop" | "forget" => {
                if children.len() != 2 {
                    return Err(error(Some(source), "invalid place operation arity"));
                }
                let (end, place) = self.address(children[1], block)?;
                if let Some(end) = end {
                    if head == "clone" {
                        self.action(
                            end,
                            Some(source),
                            Action::Load {
                                dst,
                                place,
                                kind: LoadKind::Clone,
                            },
                        );
                    } else {
                        self.action(
                            end,
                            Some(source),
                            Action::Release {
                                place,
                                kind: if head == "drop" {
                                    ReleaseKind::Drop
                                } else {
                                    ReleaseKind::Forget
                                },
                            },
                        );
                        self.action(
                            end,
                            Some(source),
                            Action::Compute {
                                dst,
                                operation: Compute::Unit,
                            },
                        );
                    }
                }
                Ok((end, dst))
            }
            "deref-set" | "pin-write" | "pin-set-field" => {
                let (target, rhs, projection) = if head == "pin-set-field" && children.len() == 4 {
                    let NodeKind::Declaration(DeclarationId::Field(field)) =
                        self.node(children[2])?.kind
                    else {
                        return Err(error(
                            Some(source),
                            "field write has no checked field identity",
                        ));
                    };
                    (
                        children[1],
                        children[3],
                        Some(AddressProjection::Field(field)),
                    )
                } else if head != "pin-set-field" && children.len() == 3 {
                    (children[1], children[2], None)
                } else {
                    return Err(error(Some(source), "invalid reference write arity"));
                };
                let (end, handle) = self.expression(target, block)?;
                let Some(end) = end else {
                    return Ok((None, dst));
                };
                let mut projections = vec![AddressProjection::Dereference];
                if let Some(projection) = projection {
                    projections.push(projection);
                }
                let place = self.make_place(
                    end,
                    PlaceDescriptor {
                        source: Some(source),
                        ty: self.ty(rhs)?,
                        root: AddressRoot::Value(handle),
                        projections,
                        parent: None,
                        checked_prefix: 0,
                    },
                );
                let (end, value) = self.expression(rhs, end)?;
                if let Some(end) = end {
                    self.action(end, Some(source), Action::Store { place, value });
                    self.action(
                        end,
                        Some(source),
                        Action::Compute {
                            dst,
                            operation: Compute::Unit,
                        },
                    );
                }
                Ok((end, dst))
            }
            "array-repeat" if !matches!(self.ty(source)?, Type::Array(_, 1)) => Err(error(
                Some(source),
                "repeated array evaluation requires an explicit multiplicity/destination contract",
            )),
            "asm" => self.assembly(source, dst, children, block),
            _ => self.operation(
                source,
                dst,
                head.to_owned(),
                children.to_vec(),
                numeric,
                None,
                block,
            ),
        }
    }

    fn assembly(
        &mut self,
        source: NodeId,
        dst: ValueId,
        children: &[NodeId],
        block: BlockId,
    ) -> Result<(Option<BlockId>, ValueId), Error> {
        self.operation(
            source,
            dst,
            "asm".into(),
            children.to_vec(),
            None,
            None,
            block,
        )
    }

    fn scoped_place_pinned(&self, source: NodeId) -> Result<bool, Error> {
        let mut current = source;
        let mut projected = false;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(current) {
                return Err(error(Some(source), "cyclic scoped borrow place"));
            }
            match &self.node(current)?.kind {
                NodeKind::Form { head, children, .. }
                    if matches!(head.as_str(), "get" | "get-payload" | "index") =>
                {
                    projected = true;
                    current = *children
                        .get(1)
                        .ok_or_else(|| error(Some(current), "scoped projection has no base"))?;
                }
                _ => {
                    return Ok(
                        projected && matches!(self.ty(current)?, Type::PinnedReference { .. })
                    )
                }
            }
        }
    }

    fn make_place(&mut self, block: BlockId, descriptor: PlaceDescriptor) -> PlaceId {
        let place = PlaceId(self.graph.places.len());
        self.graph.places.push(descriptor.clone());
        self.action(
            block,
            descriptor.source,
            Action::Place {
                dst: place,
                descriptor,
            },
        );
        place
    }

    fn address(
        &mut self,
        source: NodeId,
        block: BlockId,
    ) -> Result<(Option<BlockId>, PlaceId), Error> {
        let ty = self.ty(source)?;
        match self.node(source)?.kind.clone() {
            NodeKind::Symbol {
                binding: Some(binding),
                ..
            } => {
                let place = self.make_place(
                    block,
                    PlaceDescriptor {
                        source: Some(source),
                        ty,
                        root: AddressRoot::Local(binding),
                        projections: Vec::new(),
                        parent: None,
                        checked_prefix: 0,
                    },
                );
                Ok((Some(block), place))
            }
            NodeKind::Declaration(DeclarationId::Global(global)) => {
                let place = self.make_place(
                    block,
                    PlaceDescriptor {
                        source: Some(source),
                        ty,
                        root: AddressRoot::Global(global),
                        projections: Vec::new(),
                        parent: None,
                        checked_prefix: 0,
                    },
                );
                Ok((Some(block), place))
            }
            NodeKind::Form {
                head, callee: None, ..
            } if matches!(
                head.as_str(),
                "get" | "get-payload" | "index" | "deref" | "pin-read"
            ) =>
            {
                self.projected_address(source, block, ty)
            }
            _ => {
                let (end, value) = self.expression(source, block)?;
                // No address is used if the computed base diverges.
                let place = PlaceId(self.graph.places.len());
                let descriptor = PlaceDescriptor {
                    source: Some(source),
                    ty,
                    root: AddressRoot::Value(value),
                    projections: Vec::new(),
                    parent: None,
                    checked_prefix: 0,
                };
                if let Some(end) = end {
                    return Ok((Some(end), self.make_place(end, descriptor)));
                }
                self.graph.places.push(descriptor);
                Ok((None, place))
            }
        }
    }

    fn projected_address(
        &mut self,
        source: NodeId,
        block: BlockId,
        ty: Type,
    ) -> Result<(Option<BlockId>, PlaceId), Error> {
        let NodeKind::Form { head, children, .. } = self.node(source)?.kind.clone() else {
            return Err(error(Some(source), "projection has no checked operation"));
        };
        let base = *children
            .get(1)
            .ok_or_else(|| error(Some(source), "projection has no base"))?;
        let base_ty = self.ty(base)?;
        let handle = matches!(
            base_ty,
            Type::Reference { .. }
                | Type::PinnedReference { .. }
                | Type::RawPointer { .. }
                | Type::Slice(_)
                | Type::MutableSlice(_)
        );
        let (mut end, mut descriptor) = if handle {
            let (end, value) = self.expression(base, block)?;
            let projections = if matches!(base_ty, Type::Slice(_) | Type::MutableSlice(_)) {
                Vec::new()
            } else {
                vec![AddressProjection::Dereference]
            };
            (
                end,
                PlaceDescriptor {
                    source: Some(source),
                    ty: ty.clone(),
                    root: AddressRoot::Value(value),
                    projections,
                    parent: None,
                    checked_prefix: 0,
                },
            )
        } else {
            let (end, place) = self.address(base, block)?;
            let mut descriptor = self.graph.places[place.0].clone();
            descriptor.parent = Some(place);
            descriptor.checked_prefix = descriptor.projections.len();
            (end, descriptor)
        };
        descriptor.source = Some(source);
        descriptor.ty = ty;
        match head.as_str() {
            "deref" | "pin-read" if children.len() == 2 => {
                if !handle {
                    return Err(error(Some(source), "dereference has no checked handle"));
                }
            }
            "get" if children.len() == 3 => {
                let projection = match self.node(children[2])?.kind {
                    NodeKind::Declaration(DeclarationId::Field(field)) => {
                        AddressProjection::Field(field)
                    }
                    _ => AddressProjection::Tuple(self.static_index(children[2])?),
                };
                descriptor.projections.push(projection);
                self.metadata(children[2])?;
            }
            "get-payload" | "pin-get-payload" | "pin-get-payload-mut" if children.len() == 4 => {
                let NodeKind::Declaration(DeclarationId::Variant(variant)) =
                    self.node(children[2])?.kind
                else {
                    return Err(error(
                        Some(source),
                        "payload projection has no checked variant",
                    ));
                };
                descriptor.projections.push(AddressProjection::Payload(
                    variant,
                    self.static_index(children[3])?,
                ));
                self.metadata(children[2])?;
                self.metadata(children[3])?;
            }
            "index" | "slice-idx" | "slice-mut-idx" if children.len() == 3 => {
                if let Some(current) = end {
                    let (next, index) = self.expression(children[2], current)?;
                    end = next;
                    descriptor.projections.push(if head == "index" {
                        AddressProjection::Index(index)
                    } else {
                        AddressProjection::SliceIndex(index)
                    });
                }
            }
            _ => return Err(error(Some(source), "unsupported checked projection arity")),
        }
        if let Some(end) = end {
            return Ok((Some(end), self.make_place(end, descriptor)));
        }
        let place = PlaceId(self.graph.places.len());
        self.graph.places.push(descriptor);
        Ok((None, place))
    }

    fn static_index(&self, source: NodeId) -> Result<usize, Error> {
        match &self.node(source)?.kind {
            NodeKind::Literal(Expr::Integer(value)) => usize::try_from(*value)
                .map_err(|_| error(Some(source), "invalid static projection index")),
            NodeKind::Literal(Expr::UnsignedInteger(value)) => usize::try_from(*value)
                .map_err(|_| error(Some(source), "invalid static projection index")),
            NodeKind::Form { head, children, .. } if head == "literal" => self.static_index(
                *children
                    .last()
                    .ok_or_else(|| error(Some(source), "missing literal index"))?,
            ),
            _ => Err(error(
                Some(source),
                "projection index is not checked static metadata",
            )),
        }
    }

    fn assignment_place(
        &mut self,
        root: &PlaceRoot,
        projection: &Projection,
        source: NodeId,
        block: BlockId,
    ) -> Result<(Option<BlockId>, PlaceId), Error> {
        let root = match root {
            PlaceRoot::Local(binding) => AddressRoot::Local(*binding),
            PlaceRoot::Global(global) => AddressRoot::Global(*global),
            PlaceRoot::Parameter(_) | PlaceRoot::Allocation(_, _) => {
                return Err(error(
                    Some(source),
                    "analysis referent root is not executable storage",
                ))
            }
        };
        let mut end = Some(block);
        let projections = match projection {
            Projection::Local => Vec::new(),
            Projection::Field(field) => vec![AddressProjection::Field(*field)],
            Projection::Tuple(index) => vec![AddressProjection::Tuple(*index)],
            Projection::Payload(variant, index) => {
                vec![AddressProjection::Payload(*variant, *index)]
            }
            Projection::Array(index) => {
                let (next, index) = self.expression(*index, block)?;
                end = next;
                vec![AddressProjection::Index(index)]
            }
        };
        let descriptor = PlaceDescriptor {
            source: None,
            ty: self.ty(source)?,
            root,
            projections,
            parent: None,
            checked_prefix: 0,
        };
        if let Some(end) = end {
            return Ok((Some(end), self.make_place(end, descriptor)));
        }
        let place = PlaceId(self.graph.places.len());
        self.graph.places.push(descriptor);
        Ok((None, place))
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Available {
    Value(ValueId),
    Place(PlaceId),
    Storage(BindingId),
    Borrow(NodeId),
    Preview(NodeId),
}

impl Graph {
    fn value_type(&self, value: ValueId) -> Result<&Type, Error> {
        self.values
            .get(value.0)
            .map(|value| &value.ty)
            .ok_or_else(|| error(None, "graph input has no typed value"))
    }

    fn descriptor(&self, place: PlaceId) -> Result<&PlaceDescriptor, Error> {
        self.places
            .get(place.0)
            .ok_or_else(|| error(None, "graph input has no place descriptor"))
    }

    fn binding(&self, binding: BindingId) -> Result<&Binding, Error> {
        self.bindings
            .get(binding.0)
            .ok_or_else(|| error(None, "graph has an invalid lexical binding"))
    }

    fn same_type(&self, left: ValueId, right: ValueId) -> Result<(), Error> {
        if self.value_type(left)? != self.value_type(right)? {
            return Err(error(
                self.values[left.0].source,
                "selected/forwarded value type mismatch",
            ));
        }
        Ok(())
    }

    fn check_pattern(&self, pattern: &Pattern) -> Result<(), Error> {
        self.value_type(pattern.scrutinee)?;
        if !self.metadata.contains_key(&pattern.source) {
            return Err(error(
                Some(pattern.source),
                "pattern has no retained checked metadata",
            ));
        }
        let mut seen = HashSet::new();
        for &binding in &pattern.bindings {
            self.binding(binding)?;
            if !seen.insert(binding) {
                return Err(error(Some(pattern.source), "duplicate pattern binding"));
            }
        }
        Ok(())
    }

    fn check_place(&self, place: &PlaceDescriptor) -> Result<(), Error> {
        if let Some(parent) = place.parent {
            let parent = self.descriptor(parent)?;
            if place.root != parent.root
                || place.checked_prefix != parent.projections.len()
                || place.projections.get(..place.checked_prefix)
                    != Some(parent.projections.as_slice())
            {
                return Err(error(
                    place.source,
                    "place lost its already-checked parent prefix",
                ));
            }
        } else if place.checked_prefix != 0 {
            return Err(error(
                place.source,
                "place suppresses checks without an evaluated parent",
            ));
        }
        match place.root {
            AddressRoot::Local(binding) => {
                let binding = self.binding(binding)?;
                if place.projections.is_empty() && binding.ty != place.ty {
                    return Err(error(
                        place.source,
                        "local place type disagrees with its checked binding",
                    ));
                }
            }
            AddressRoot::Value(value) => {
                self.value_type(value)?;
            }
            AddressRoot::Global(_) => {}
        }
        for projection in &place.projections {
            if let AddressProjection::Index(value) | AddressProjection::SliceIndex(value) =
                projection
            {
                if !matches!(
                    self.value_type(*value)?,
                    Type::U8
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
                ) {
                    return Err(error(
                        place.source,
                        "dynamic place index has no checked integer type",
                    ));
                }
            }
        }
        Ok(())
    }

    fn check_operation_coverage(&self, operation: &Operation) -> Result<(), Error> {
        let schema = self
            .operation_schemas
            .get(&operation.source)
            .ok_or_else(|| {
                error(
                    Some(operation.source),
                    "operation has no checked operand schema",
                )
            })?;
        if schema.metadata != operation.metadata || schema.runtime.len() != operation.operands.len()
        {
            return Err(error(
                Some(operation.source),
                "operation runtime operand coverage is incomplete",
            ));
        }
        for ((position, source), operand) in schema.runtime.iter().zip(&operation.operands) {
            if position != &operand.position
                || self
                    .values
                    .get(operand.value.0)
                    .and_then(|value| value.source)
                    != Some(*source)
            {
                return Err(error(
                    Some(operation.source),
                    "operation runtime operand coverage/order changed",
                ));
            }
        }
        Ok(())
    }

    fn check_action(&self, located: &LocatedAction) -> Result<(), Error> {
        match &located.action {
            Action::Compute { dst, operation } => {
                let ty = self.value_type(*dst)?;
                match operation {
                    Compute::Identity(value) => self.same_type(*dst, *value)?,
                    Compute::Unit if *ty != Type::Unit => {
                        return Err(error(located.source, "Unit result type mismatch"))
                    }
                    Compute::Bool(_) if *ty != Type::Bool => {
                        return Err(error(located.source, "Bool result type mismatch"))
                    }
                    Compute::Checked(operation) => {
                        self.check_operation_coverage(operation)?;
                        if self.values[dst.0].source != Some(operation.source) {
                            return Err(error(
                                Some(operation.source),
                                "operation lost its checked result identity",
                            ));
                        }
                        let mut positions = HashSet::new();
                        for operand in &operation.operands {
                            self.value_type(operand.value)?;
                            if operand.position.is_empty()
                                || !positions.insert(operand.position.clone())
                            {
                                return Err(error(
                                    Some(operation.source),
                                    "ambiguous mapped operand position",
                                ));
                            }
                        }
                        for metadata in &operation.metadata {
                            if !self.metadata.contains_key(metadata) {
                                return Err(error(
                                    Some(*metadata),
                                    "operation lost static metadata",
                                ));
                            }
                        }
                    }
                    Compute::Atom { source, kind } => {
                        if self.values[dst.0].source != Some(*source)
                            || !matches!(
                                kind,
                                NodeKind::Literal(_)
                                    | NodeKind::Symbol { .. }
                                    | NodeKind::Declaration(_)
                            )
                        {
                            return Err(error(Some(*source), "atom is not an exact checked leaf"));
                        }
                    }
                    _ => {}
                }
            }
            Action::Place { dst, descriptor } => {
                if self.descriptor(*dst)? != descriptor {
                    return Err(error(
                        located.source,
                        "place action disagrees with its descriptor table",
                    ));
                }
                self.check_place(descriptor)?;
            }
            Action::Load { dst, place, .. } => {
                if self.value_type(*dst)? != &self.descriptor(*place)?.ty {
                    return Err(error(located.source, "place load type mismatch"));
                }
            }
            Action::Bind { binding, value, .. } => {
                if &self.binding(*binding)?.ty != self.value_type(*value)? {
                    return Err(error(located.source, "binding value type mismatch"));
                }
            }
            Action::Store { place, value } => {
                if &self.descriptor(*place)?.ty != self.value_type(*value)? {
                    return Err(error(located.source, "stored value type mismatch"));
                }
            }
            Action::Borrow {
                dst,
                place,
                mutable,
                pinned,
                scope,
            } => {
                let descriptor = self.descriptor(*place)?;
                if let Some(dst) = dst {
                    let (actual_mutable, actual_pinned, target) = match self.value_type(*dst)? {
                        Type::Reference { mutable, target } => (*mutable, false, target.as_ref()),
                        Type::PinnedReference { mutable, target } => {
                            (*mutable, true, target.as_ref())
                        }
                        _ => {
                            return Err(error(
                                located.source,
                                "borrow result is not a checked reference",
                            ))
                        }
                    };
                    if actual_mutable != *mutable
                        || actual_pinned != *pinned
                        || target != &descriptor.ty
                    {
                        return Err(error(located.source, "borrow mode/target type mismatch"));
                    }
                } else if scope.is_none() {
                    return Err(error(
                        located.source,
                        "borrow has neither a value nor a scoped lifetime",
                    ));
                }
            }
            Action::Release { place, .. } => {
                self.descriptor(*place)?;
            }
            Action::Preview(pattern) | Action::Commit(pattern) | Action::EndPreview(pattern) => {
                self.check_pattern(pattern)?
            }
            Action::ScopeEnter(bindings) | Action::ScopeExit(bindings) => {
                for &binding in bindings {
                    self.binding(binding)?;
                }
            }
            Action::EndBorrow { .. } => {}
        }
        Ok(())
    }

    fn edges<'a>(&self, terminator: &'a Terminator) -> Vec<&'a Edge> {
        match terminator {
            Terminator::Goto(edge) => vec![edge],
            Terminator::Branch { yes, no, .. } | Terminator::PatternTest { yes, no, .. } => {
                vec![yes, no]
            }
            Terminator::Await { ready, .. } => vec![ready],
            Terminator::Return(_) | Terminator::Diverge => Vec::new(),
        }
    }

    pub(crate) fn successors(&self, block: BlockId) -> Vec<BlockId> {
        let terminator = &self.blocks[block.0].terminator;
        let mut successors = self
            .edges(terminator)
            .into_iter()
            .map(|edge| edge.target)
            .collect::<Vec<_>>();
        if let Terminator::Await { pending, .. } = terminator {
            successors.push(*pending);
        }
        successors
    }

    pub(crate) fn reachable(&self) -> HashSet<BlockId> {
        let mut seen = HashSet::new();
        let mut pending = vec![self.entry];
        while let Some(block) = pending.pop() {
            if seen.insert(block) {
                pending.extend(self.successors(block));
            }
        }
        seen
    }

    fn place_inputs(descriptor: &PlaceDescriptor) -> Vec<Available> {
        let mut inputs = match descriptor.root {
            AddressRoot::Value(value) => vec![Available::Value(value)],
            AddressRoot::Local(binding) => vec![Available::Storage(binding)],
            AddressRoot::Global(_) => Vec::new(),
        };
        if let Some(parent) = descriptor.parent {
            inputs.push(Available::Place(parent));
        }
        for projection in &descriptor.projections {
            if let AddressProjection::Index(value) | AddressProjection::SliceIndex(value) =
                projection
            {
                inputs.push(Available::Value(*value));
            }
        }
        inputs
    }

    fn inputs(&self, action: &Action) -> Vec<Available> {
        match action {
            Action::Compute {
                operation: Compute::Checked(operation),
                ..
            } => operation
                .operands
                .iter()
                .map(|operand| Available::Value(operand.value))
                .collect(),
            Action::Compute {
                operation: Compute::Identity(value),
                ..
            } => vec![Available::Value(*value)],
            Action::Place { descriptor, .. } => Self::place_inputs(descriptor),
            Action::Load { place, .. }
            | Action::Borrow { place, .. }
            | Action::Release { place, .. } => {
                let mut inputs = vec![Available::Place(*place)];
                if let AddressRoot::Local(binding) = self.places[place.0].root {
                    inputs.push(Available::Storage(binding));
                }
                inputs
            }
            Action::Bind { binding, value, .. } => {
                vec![Available::Storage(*binding), Available::Value(*value)]
            }
            Action::Store { place, value } => {
                let mut inputs = vec![Available::Place(*place), Available::Value(*value)];
                if let AddressRoot::Local(binding) = self.places[place.0].root {
                    inputs.push(Available::Storage(binding));
                }
                inputs
            }
            Action::Preview(pattern) | Action::Commit(pattern) => {
                vec![Available::Value(pattern.scrutinee)]
            }
            Action::EndPreview(pattern) => vec![Available::Preview(pattern.source)],
            Action::EndBorrow { scope } => vec![Available::Borrow(*scope)],
            _ => Vec::new(),
        }
    }

    fn transfer(action: &Action, available: &mut HashSet<Available>) {
        match action {
            Action::Compute { dst, .. } | Action::Load { dst, .. } => {
                available.insert(Available::Value(*dst));
            }
            Action::Place { dst, .. } => {
                available.insert(Available::Place(*dst));
            }
            Action::Borrow { dst, scope, .. } => {
                if let Some(dst) = dst {
                    available.insert(Available::Value(*dst));
                }
                if let Some(scope) = scope {
                    available.insert(Available::Borrow(*scope));
                }
            }
            Action::ScopeEnter(bindings)
            | Action::Preview(Pattern { bindings, .. })
            | Action::Commit(Pattern { bindings, .. }) => {
                for &binding in bindings {
                    available.insert(Available::Storage(binding));
                }
                if let Action::Preview(pattern) = action {
                    available.insert(Available::Preview(pattern.source));
                }
                if let Action::Commit(pattern) = action {
                    available.remove(&Available::Preview(pattern.source));
                }
            }
            Action::ScopeExit(bindings) => {
                for &binding in bindings {
                    available.remove(&Available::Storage(binding));
                }
            }
            Action::EndPreview(pattern) => {
                available.remove(&Available::Preview(pattern.source));
            }
            Action::EndBorrow { scope } => {
                available.remove(&Available::Borrow(*scope));
            }
            _ => {}
        }
    }

    /// Checks executable structure and definite evaluation/storage availability,
    /// NOT initialization of owner contents, move legality or loan lifetimes.
    pub(crate) fn validate(&self) -> Result<(), Error> {
        if self.entry.0 >= self.blocks.len()
            || self.parameter_count > self.bindings.len()
            || !self.blocks[self.entry.0].parameters.is_empty()
        {
            return Err(error(None, "invalid executable graph entry"));
        }
        let mut parameter_definitions = HashSet::new();
        let mut value_definitions = HashSet::new();
        let mut place_definitions = HashSet::new();
        for (index, block) in self.blocks.iter().enumerate() {
            for &parameter in &block.parameters {
                self.value_type(parameter)?;
                if !parameter_definitions.insert(parameter) || !value_definitions.insert(parameter)
                {
                    return Err(error(
                        self.values[parameter.0].source,
                        "computed value has multiple graph definitions",
                    ));
                }
            }
            for located in &block.actions {
                self.check_action(located)?;
                match &located.action {
                    Action::Compute { dst, .. }
                    | Action::Load { dst, .. }
                    | Action::Borrow { dst: Some(dst), .. } => {
                        if !value_definitions.insert(*dst) {
                            return Err(error(
                                located.source,
                                "computed value has multiple structured definitions",
                            ));
                        }
                    }
                    Action::Place { dst, .. } => {
                        if !place_definitions.insert(*dst) {
                            return Err(error(located.source, "place has multiple definitions"));
                        }
                    }
                    _ => {}
                }
            }
            match &block.terminator {
                Terminator::Branch { condition, .. } => {
                    if self.value_type(*condition)? != &Type::Bool {
                        return Err(error(None, "branch condition is not Bool"));
                    }
                }
                Terminator::PatternTest { pattern, .. } => self.check_pattern(pattern)?,
                Terminator::Await {
                    site,
                    child,
                    pending,
                    ready,
                } => {
                    let site = self
                        .awaits
                        .get(*site)
                        .ok_or_else(|| error(None, "await references an unknown site"))?;
                    if self.value_type(*child)? != &site.child_type
                        || self.values[child.0].source != Some(site.child_node)
                        || *pending != BlockId(index)
                        || ready.arguments.len() != 1
                        || !matches!(ready.arguments[0], Argument::Ready(id) if id == site.site_index)
                    {
                        return Err(error(
                            Some(site.result_node),
                            "await child/retry/Ready mapping is invalid",
                        ));
                    }
                    let target = self
                        .blocks
                        .get(ready.target.0)
                        .ok_or_else(|| error(None, "invalid Ready destination"))?;
                    if target.parameters.len() != 1
                        || self
                            .values
                            .get(target.parameters[0].0)
                            .and_then(|value| value.source)
                            != Some(site.result_node)
                    {
                        return Err(error(
                            Some(site.result_node),
                            "Ready destination lost the checked await result",
                        ));
                    }
                }
                Terminator::Return(Some(value)) => {
                    self.value_type(*value)?;
                }
                _ => {}
            }
            for edge in self.edges(&block.terminator) {
                let target = self
                    .blocks
                    .get(edge.target.0)
                    .ok_or_else(|| error(None, "invalid executable graph edge"))?;
                if target.parameters.len() != edge.arguments.len() {
                    return Err(error(None, "edge argument/block parameter arity mismatch"));
                }
                for (argument, &parameter) in edge.arguments.iter().zip(&target.parameters) {
                    let ty = match argument {
                        Argument::Value(value) => self.value_type(*value)?,
                        Argument::Ready(site) => {
                            if !matches!(block.terminator, Terminator::Await { site: actual, .. } if actual == *site)
                            {
                                return Err(error(
                                    None,
                                    "Ready value appears outside its producing await edge",
                                ));
                            }
                            &self
                                .awaits
                                .get(*site)
                                .ok_or_else(|| error(None, "unknown Ready result"))?
                                .result_type
                        }
                    };
                    if self.value_type(parameter)? != ty {
                        return Err(error(None, "selected edge value type mismatch"));
                    }
                }
            }
        }
        let live = self.reachable();
        let mut predecessors = vec![Vec::new(); self.blocks.len()];
        for &block in &live {
            for successor in self.successors(block) {
                predecessors[successor.0].push(block);
            }
        }
        let initial = (0..self.parameter_count)
            .map(|index| Available::Storage(BindingId(index)))
            .collect::<HashSet<_>>();
        let mut universe = initial.clone();
        for block in &self.blocks {
            universe.extend(block.parameters.iter().copied().map(Available::Value));
            for action in &block.actions {
                Self::transfer(&action.action, &mut universe);
            }
        }
        // Include killed facts as well; top is independent of arena ordering.
        universe.extend((0..self.values.len()).map(|index| Available::Value(ValueId(index))));
        universe.extend((0..self.places.len()).map(|index| Available::Place(PlaceId(index))));
        universe.extend((0..self.bindings.len()).map(|index| Available::Storage(BindingId(index))));
        for block in &self.blocks {
            for action in &block.actions {
                universe.extend(self.inputs(&action.action));
            }
        }
        let mut before = vec![universe.clone(); self.blocks.len()];
        let mut after = before.clone();
        loop {
            let mut changed = false;
            for &id in &live {
                let mut incoming = if id == self.entry {
                    initial.clone()
                } else {
                    universe.clone()
                };
                for predecessor in &predecessors[id.0] {
                    incoming.retain(|fact| after[predecessor.0].contains(fact));
                }
                let mut outgoing = incoming.clone();
                outgoing.extend(
                    self.blocks[id.0]
                        .parameters
                        .iter()
                        .copied()
                        .map(Available::Value),
                );
                for action in &self.blocks[id.0].actions {
                    Self::transfer(&action.action, &mut outgoing);
                }
                changed |= before[id.0] != incoming || after[id.0] != outgoing;
                before[id.0] = incoming;
                after[id.0] = outgoing;
            }
            if !changed {
                break;
            }
        }
        for &id in &live {
            let block = &self.blocks[id.0];
            let mut available = before[id.0].clone();
            available.extend(block.parameters.iter().copied().map(Available::Value));
            for action in &block.actions {
                for input in self.inputs(&action.action) {
                    if !available.contains(&input) {
                        return Err(error(
                            action.source,
                            "graph input is not definitely available",
                        ));
                    }
                }
                Self::transfer(&action.action, &mut available);
            }
            let inputs = match &block.terminator {
                Terminator::Branch { condition, .. } => vec![*condition],
                Terminator::PatternTest { pattern, .. } => vec![pattern.scrutinee],
                Terminator::Await { child, .. } => vec![*child],
                Terminator::Return(Some(value)) => vec![*value],
                _ => Vec::new(),
            };
            for value in inputs {
                if !available.contains(&Available::Value(value)) {
                    return Err(error(
                        self.values[value.0].source,
                        "terminator value is not definitely evaluated",
                    ));
                }
            }
            for edge in self.edges(&block.terminator) {
                for argument in &edge.arguments {
                    if let Argument::Value(value) = argument {
                        if !available.contains(&Available::Value(*value)) {
                            return Err(error(
                                self.values[value.0].source,
                                "selected value is not definitely evaluated",
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Additional boundary check against the SAME checked body. This does not
    /// resolve names, infer types from syntax, or compare independently built IR.
    pub(crate) fn validate_against(&self, body: &Body) -> Result<(), Error> {
        for (index, value) in self.values.iter().enumerate() {
            if let Some(source) = value.source {
                if body.nodes.get(source.0).and_then(|node| node.ty.as_ref()) != Some(&value.ty)
                    || self.values_by_node.get(&source) != Some(&ValueId(index))
                {
                    return Err(error(
                        Some(source),
                        "graph value disagrees with its exact checked node/type",
                    ));
                }
            }
        }
        if self.bindings.len() != body.bindings.len()
            || self.parameter_count != body.parameter_count
            || self
                .bindings
                .iter()
                .zip(&body.bindings)
                .any(|(left, right)| left.ty != right.ty || left.name != right.name)
        {
            return Err(error(
                None,
                "graph binding schema disagrees with its checked body",
            ));
        }
        for block in &self.blocks {
            for located in &block.actions {
                if let Action::Compute {
                    operation: Compute::Checked(operation),
                    ..
                } = &located.action
                {
                    let node = body.nodes.get(operation.source.0).ok_or_else(|| {
                        error(
                            Some(operation.source),
                            "operation is outside its checked body",
                        )
                    })?;
                    let NodeKind::Form {
                        head,
                        callee,
                        numeric,
                        ..
                    } = &node.kind
                    else {
                        return Err(error(
                            Some(operation.source),
                            "operation is not its checked form",
                        ));
                    };
                    if head != &operation.head || callee != &operation.callee {
                        return Err(error(
                            Some(operation.source),
                            "operation changed its checked callee/head",
                        ));
                    }
                    let schema = operation_schema(body, operation.source)?;
                    if self.operation_schemas.get(&operation.source) != Some(&schema) {
                        return Err(error(
                            Some(operation.source),
                            "operation schema disagrees with its checked body",
                        ));
                    }
                    self.check_operation_coverage(operation)?;
                    let same_numeric = match (numeric, &operation.numeric) {
                        (None, None) => true,
                        (Some(left), Some(right)) => {
                            left.operand_type == right.operand_type
                                && left.operation == right.operation
                                && left.overflow == right.overflow
                        }
                        _ => false,
                    };
                    if !same_numeric {
                        return Err(error(
                            Some(operation.source),
                            "operation changed its checked numeric semantics",
                        ));
                    }
                    for operand in &operation.operands {
                        let mut source = operation.source;
                        for &position in &operand.position {
                            let children = match &body.nodes[source.0].kind {
                                NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                                    children
                                }
                                _ => {
                                    return Err(error(
                                        Some(source),
                                        "operand mapping crosses a runtime leaf",
                                    ))
                                }
                            };
                            source = *children.get(position).ok_or_else(|| {
                                error(Some(source), "invalid mapped operand position")
                            })?;
                        }
                        if self.values[operand.value.0].source != Some(source) {
                            return Err(error(
                                Some(source),
                                "operand lost its exact checked node identity",
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::async_source::{self, Lowered};
    use crate::typed_ir::Declarations;

    const CONTEXT: &str = "
      (#enum Child ((Waiting u64))) (#linear Child)
      (#enum ChildPoll ((Pending Child) (Ready u64)))
      (#fn step-poll ((task Child) (waker (#ref u64))) ChildPoll
        (#return (#match task
          (#case (Waiting count) (#if (#u64.== count 0u64)
            (Ready 42u64) (Pending (Waiting (#u64.-.wrap count 1u64))))))))
      (#fn first () u64 (#return 11u64))
      (#fn combine ((first u64) (second u64)) u64
        (#return (#u64.+.wrap first second)))";

    fn prepare(source: &str) -> (Lowered, Declarations) {
        prepare_with_context("", source)
    }

    fn prepare_with_context(extra: &str, source: &str) -> (Lowered, Declarations) {
        let original = crate::parse(source).unwrap().remove(0);
        let base = crate::parse_program(&format!("{CONTEXT}\n{extra}")).unwrap();
        let lowered = async_source::lower(&original, Type::U64, &base).unwrap();
        let program = lowered.program(&base).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        (lowered, declarations)
    }

    fn mapped(lowered: &Lowered, declarations: &Declarations) -> Vec<CheckedAwait> {
        lowered
            .map(
                &declarations.bodies[&lowered.body_name],
                &declarations.flows[&lowered.body_name],
                declarations,
            )
            .unwrap()
    }

    #[test]
    fn ordinary_borrows_inherit_checked_pinning_and_scoped_context() {
        let (lowered, declarations) = prepare_with_context(
            "(#struct Pair ((left u64) (right u64)))",
            "(#fn work ((owner (#pin-ref-mut Pair))) u64
              (#let view (#pin-ref u64) (#borrow (#get owner left)))
              (#drop view)
              (#let result u64 (#borrow (#get owner right)
                (#await u64 Child Pending Ready step-poll (Waiting 0u64))))
              (#return result))",
        );
        let body = &declarations.bodies[&lowered.body_name];
        let sites = mapped(&lowered, &declarations);
        let graph = build(body, &sites).unwrap();
        let borrows = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .filter_map(|located| match &located.action {
                Action::Borrow {
                    dst, pinned, scope, ..
                } => Some((*dst, *pinned, *scope)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(borrows.len(), 2);
        assert!(borrows[0].0.is_some() && borrows[0].1 && borrows[0].2.is_none());
        assert!(borrows[1].0.is_none() && borrows[1].1 && borrows[1].2.is_some());
    }

    #[test]
    fn mutable_destructure_and_immutable_match_bindings_remain_distinct() {
        let (lowered, declarations) = prepare_with_context(
            "(#struct Pair ((left u64) (right u64))) (#enum Choice ((Some u64) None))",
            "(#fn work ((pair Pair) (choice Choice)) u64
              (#let-mut (Pair left right) Pair pair)
              (#set left (#call first (:)))
              (#return (#match choice
                (#case (Some payload) (#u64.+.wrap payload left))
                (#case None right))))",
        );
        let graph = build(&declarations.bodies[&lowered.body_name], &[]).unwrap();
        let commits = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .filter_map(|located| {
                if let Action::Commit(pattern) = &located.action {
                    Some(pattern)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        assert!(commits
            .iter()
            .any(|pattern| pattern.mutable && pattern.bindings.len() == 2));
        assert!(commits
            .iter()
            .any(|pattern| !pattern.mutable && pattern.bindings.len() == 1));
    }

    #[test]
    fn place_checks_precede_rhs_await_and_nested_indices_do_not_replay_prefix_checks() {
        let (lowered, declarations) = prepare(
            "(#fn work () u64
          (#let-mut array (#array u64 2) (#array-of (#array u64 2) 1u64 2u64))
          (#set-index array (#call first (:))
            (#await u64 Child Pending Ready step-poll (Waiting 0u64)))
          (#forget array) (#return 0u64))",
        );
        let sites = mapped(&lowered, &declarations);
        let graph = build(&declarations.bodies[&lowered.body_name], &sites).unwrap();
        let check = graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(block, value)| {
                value
                    .actions
                    .iter()
                    .find_map(|action| match &action.action {
                        Action::Place { descriptor, .. }
                            if matches!(
                                descriptor.checks().as_slice(),
                                [PlaceCheck::Bounds { .. }]
                            ) =>
                        {
                            Some(BlockId(block))
                        }
                        _ => None,
                    })
            })
            .unwrap();
        let poll = graph
            .blocks
            .iter()
            .position(|block| matches!(block.terminator, Terminator::Await { .. }))
            .unwrap();
        assert_ne!(check, BlockId(poll));
        assert!(
            matches!(&graph.blocks[check.0].terminator, Terminator::Goto(edge) if edge.target == BlockId(poll))
        );

        let (lowered, declarations) = prepare(
            "(#fn work ((array (#array (#array u64 2) 2))) u64
          (#let value u64 (#index (#index array 0u64) 1u64))
          (#forget array) (#return value))",
        );
        let graph = build(&declarations.bodies[&lowered.body_name], &[]).unwrap();
        let checks = graph
            .places
            .iter()
            .flat_map(PlaceDescriptor::checks)
            .collect::<Vec<_>>();
        assert_eq!(checks.len(), 2);
        let child = graph
            .places
            .iter()
            .find(|place| place.checked_prefix == 1)
            .unwrap();
        assert!(child.parent.is_some());
        assert_eq!(child.checks().len(), 1);
    }

    #[test]
    fn payload_checks_are_explicit_and_missing_or_reordered_operands_are_rejected() {
        let (lowered, declarations) = prepare_with_context(
            "(#enum Choice ((Some u64) None))",
            "(#fn work ((choice (#ref Choice))) u64
              (#return (#call combine (: first (#get-payload choice Some 0)
                : second (#call first (:))))))",
        );
        let body = &declarations.bodies[&lowered.body_name];
        let graph = build(body, &[]).unwrap();
        assert!(graph.places.iter().any(|place| matches!(
            place.checks().as_slice(),
            [PlaceCheck::ActivePayload { .. }]
        )));
        for omitted in [true, false] {
            let mut bad = graph.clone();
            let operation = bad
                .blocks
                .iter_mut()
                .flat_map(|block| &mut block.actions)
                .find_map(|action| match &mut action.action {
                    Action::Compute {
                        operation: Compute::Checked(operation),
                        ..
                    } if operation.callee == declarations.function_id("combine") => Some(operation),
                    _ => None,
                })
                .unwrap();
            if omitted {
                operation.operands.pop();
            } else {
                operation.operands.swap(0, 1);
            }
            assert!(bad.validate().unwrap_err().message.contains("coverage"));
            assert!(bad
                .validate_against(body)
                .unwrap_err()
                .message
                .contains("coverage"));
        }
    }

    #[test]
    fn checked_empty_unit_values_lower_through_if_and_block_joins() {
        for source in [
            "(#fn work ((choose bool)) ()
              (#return (#if choose () (#block (#call first (:)) ()))))",
            "(#fn work ((choose bool)) ()
              (#let unit () ())
              (#return (#block (#if choose (#block ()) ()) unit)))",
        ] {
            let (lowered, declarations) = prepare(source);
            let body = &declarations.bodies[&lowered.body_name];
            let graph = build(body, &[]).unwrap();
            let units = body
                .nodes
                .iter()
                .enumerate()
                .filter_map(|(index, node)| {
                    (node.ty == Some(Type::Unit)
                        && matches!(&node.kind, NodeKind::Syntax(children) if children.is_empty()))
                    .then_some(NodeId(index))
                })
                .collect::<Vec<_>>();
            assert!(!units.is_empty());
            for source in units {
                let value = graph.values_by_node[&source];
                assert_eq!(graph.values[value.0].ty, Type::Unit);
                assert!(graph.blocks.iter().flat_map(|block| &block.actions).any(|located| {
                    located.source == Some(source)
                        && matches!(located.action, Action::Compute { dst, operation: Compute::Unit } if dst == value)
                }));
            }
            graph.validate_against(body).unwrap();
        }
    }

    #[test]
    fn named_operands_and_selected_joins_survive_await_without_reconstruction() {
        let (lowered, declarations) = prepare(
            "(#fn work ((choose bool) (seed u64)) u64
          (#return (#call combine
            (: second (#await u64 Child Pending Ready step-poll (Waiting seed))
             : first (#if choose (#call first (:)) 3u64)))))",
        );
        let body = &declarations.bodies[&lowered.body_name];
        let sites = mapped(&lowered, &declarations);
        let graph = build(body, &sites).unwrap();
        let (poll, child, ready, pending) = graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(index, block)| {
                if let Terminator::Await {
                    child,
                    ready,
                    pending,
                    ..
                } = &block.terminator
                {
                    Some((BlockId(index), *child, ready, *pending))
                } else {
                    None
                }
            })
            .unwrap();
        assert_eq!(poll, pending);
        assert!(graph.blocks[poll.0].actions.is_empty());
        assert_eq!(graph.values[child.0].source, Some(sites[0].child_value));
        assert_eq!(
            graph.values[graph.blocks[ready.target.0].parameters[0].0].source,
            Some(sites[0].result_value)
        );
        let operation = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|located| match &located.action {
                Action::Compute {
                    operation: Compute::Checked(operation),
                    ..
                } if operation.callee == declarations.function_id("combine") => Some(operation),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            operation
                .operands
                .iter()
                .map(|operand| operand.position.clone())
                .collect::<Vec<_>>(),
            [vec![1], vec![2]]
        );
        let first = graph.values[operation.operands[0].value.0].source.unwrap();
        assert!(matches!(body.nodes[first.0].kind, NodeKind::If { .. }));
        assert_eq!(
            graph.values[operation.operands[1].value.0].source,
            Some(sites[0].result_value)
        );
        assert_eq!(graph.awaits[0].source_path, sites[0].source_path);
        graph.validate_against(body).unwrap();
    }

    #[test]
    fn unsafe_context_and_collapsed_spans_do_not_change_execution_order() {
        let (lowered, mut declarations) = prepare(
            "(#fn work ((seed u64)) u64
          (#return (#unsafe (#u64.+.wrap (#call first (:))
            (#await u64 Child Pending Ready step-poll (Waiting seed))))))",
        );
        let sites = mapped(&lowered, &declarations);
        let graph = build(&declarations.bodies[&lowered.body_name], &sites).unwrap();
        assert!(graph.blocks.iter().flat_map(|block| &block.actions).any(|located| {
            located.unsafe_context && matches!(&located.action,
                Action::Compute { operation: Compute::Checked(operation), .. } if operation.head == "u64.+.wrap")
        }));
        let body = declarations.bodies.get_mut(&lowered.body_name).unwrap();
        let span = body.nodes.iter().find_map(|node| node.span);
        for node in &mut body.nodes {
            node.span = span;
        }
        let flow = declarations.flows.get_mut(&lowered.body_name).unwrap();
        let count = flow.nodes.len();
        let remap = |id: FlowNodeId| FlowNodeId(count - 1 - id.0);
        flow.nodes.reverse();
        for node in &mut flow.nodes {
            for successor in &mut node.successors {
                *successor = remap(*successor);
            }
        }
        flow.entry = remap(flow.entry);
        flow.exit = remap(flow.exit);
        flow.variant_pruned_edges = flow
            .variant_pruned_edges
            .iter()
            .map(|(&from, targets)| (remap(from), targets.iter().copied().map(remap).collect()))
            .collect();
        let sites = mapped(&lowered, &declarations);
        let rebuilt = build(&declarations.bodies[&lowered.body_name], &sites).unwrap();
        let shape = |graph: &Graph| {
            let mut blocks = graph.blocks.clone();
            for block in &mut blocks {
                for action in &mut block.actions {
                    action.span = None;
                }
            }
            format!("{blocks:?}")
        };
        assert_eq!(shape(&graph), shape(&rebuilt));
    }

    #[test]
    fn validation_rejects_unavailable_operands_wrong_join_arity_and_non_bool_branches() {
        let (lowered, declarations) = prepare(
            "(#fn work ((choose bool)) u64
          (#return (#if choose (#call first (:)) 3u64)))",
        );
        let body = &declarations.bodies[&lowered.body_name];
        let graph = build(body, &[]).unwrap();
        let mut bad = graph.clone();
        let edge = bad
            .blocks
            .iter_mut()
            .find_map(|block| match &mut block.terminator {
                Terminator::Goto(edge) if !edge.arguments.is_empty() => Some(edge),
                _ => None,
            })
            .unwrap();
        edge.arguments.clear();
        assert!(bad.validate().unwrap_err().message.contains("arity"));
        let mut bad = graph.clone();
        let scalar = bad
            .values
            .iter()
            .position(|value| value.ty == Type::U64)
            .unwrap();
        for block in &mut bad.blocks {
            if let Terminator::Branch { condition, .. } = &mut block.terminator {
                *condition = ValueId(scalar);
                break;
            }
        }
        assert!(bad.validate().unwrap_err().message.contains("Bool"));
        let mut bad = graph.clone();
        let producer = bad
            .blocks
            .iter_mut()
            .find_map(|block| {
                block
                    .actions
                    .iter()
                    .position(|located| {
                        matches!(
                            located.action,
                            Action::Compute {
                                operation: Compute::Checked(_),
                                ..
                            }
                        )
                    })
                    .map(|index| (block, index))
            })
            .unwrap();
        producer.0.actions.remove(producer.1);
        assert!(bad
            .validate()
            .unwrap_err()
            .message
            .contains("definitely evaluated"));
    }
}
