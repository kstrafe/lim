//! Original-source control flow for async lowering.
//!
//! Unlike the legacy nested-task rewrites, this graph keeps lexical binding
//! identities and resolved transfer targets. Pending retries the poll operation,
//! not the expression that constructed its child. Types below are declaration
//! contracts; missing contracts remain unknown, never inferred from values.
//!
//! Production currently uses this graph to validate control transfers before
//! rewriting. Frame emission and ownership/loan state at suspension are still
//! provided by the legacy lowering and checked generated functions. Data-use
//! liveness alone is NOT sufficient to select owned cancellation slots.
#![allow(dead_code)] // The general frame emitter will consume the graph next.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{async_fn::AsyncTypeEnvironment, Expr, Span, SpannedExpr};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct NodeId(usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct BindingId(usize);

#[derive(Debug)]
pub(crate) struct Error {
    pub message: String,
    pub span: Span,
}

#[derive(Debug)]
pub(crate) struct Binding<'a> {
    pub name: String,
    pub declared_type: Option<String>,
    pub mutable: bool,
    pub source: &'a SpannedExpr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Action {
    Entry,
    Evaluate,
    Read(BindingId),
    Bind(Vec<BindingId>),
    Assign(BindingId),
    ScopeExit(Vec<BindingId>),
    Branch,
    Pattern,
    PatternPreview(Vec<BindingId>),
    PatternCommit(Vec<BindingId>),
    Join,
    LoopHead,
    Transfer,
    Return,
    Await { result_type: Option<String> },
    RangeInit(BindingId),
    RangeCondition(BindingId),
    RangeStep(BindingId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EdgeKind {
    Next,
    True,
    False,
    Ready,
    Pending,
    Transfer,
}

#[derive(Clone, Debug)]
pub(crate) struct Edge {
    pub target: NodeId,
    pub kind: EdgeKind,
    /// Selected branch/break value, not a use of all predecessor values.
    pub value: Option<NodeId>,
}

#[derive(Debug)]
pub(crate) struct Node<'a> {
    pub source: &'a SpannedExpr,
    pub action: Action,
    pub operands: Vec<NodeId>,
    pub edges: Vec<Edge>,
    /// In-scope storage candidates at suspension, including unread values.
    /// Consumption/loan analysis must refine these before emitting a frame.
    pub scope: Vec<BindingId>,
}

#[derive(Debug)]
pub(crate) struct Graph<'a> {
    pub nodes: Vec<Node<'a>>,
    pub bindings: Vec<Binding<'a>>,
    pub entry: NodeId,
}

fn head(node: &SpannedExpr) -> &str {
    match node.children.first().map(|child| &child.expr) {
        Some(Expr::Symbol(name)) => name.strip_prefix('#').unwrap_or(name),
        _ => "",
    }
}

fn symbol(node: &SpannedExpr) -> Option<&str> {
    match &node.expr {
        Expr::Symbol(name) => Some(name),
        _ => None,
    }
}

fn function(node: &SpannedExpr) -> Option<&SpannedExpr> {
    match head(node) {
        "fn" => Some(node),
        "quote" | "quasiquote" => None,
        _ => node.children.iter().find_map(function),
    }
}

fn type_contract(node: &SpannedExpr) -> Option<String> {
    crate::parse_type(Some(&crate::normalize_keywords(node.expr.clone())))
        .ok()
        .map(|ty| crate::type_source(&ty))
}

pub(crate) fn check(source: &SpannedExpr, environment: &AsyncTypeEnvironment) -> Result<(), Error> {
    build(source, environment).map(|_| ())
}

pub(crate) fn build<'a>(
    source: &'a SpannedExpr,
    environment: &'a AsyncTypeEnvironment,
) -> Result<Option<Graph<'a>>, Error> {
    let Some(function) = function(source) else {
        // Some generator-produced invocations have no original source children.
        // Do not manufacture exact spans by reparsing a formatted expression.
        return Ok(None);
    };
    if function.children.len() < 4 {
        return Ok(None); // Ordinary declaration validation diagnoses malformed syntax.
    }
    let mut builder = Builder {
        graph: Graph {
            nodes: Vec::new(),
            bindings: Vec::new(),
            entry: NodeId(0),
        },
        environment,
        names: HashMap::new(),
        scopes: vec![Vec::new()],
        loops: Vec::new(),
        tail: Vec::new(),
        result: type_contract(&function.children[3]),
    };
    let entry = builder.emit(function, Action::Entry, Vec::new());
    builder.graph.entry = entry;
    for parameter in &function.children[2].children {
        let offset = usize::from(head(parameter) == "mut");
        if let (Some(name), Some(ty)) = (
            parameter.children.get(offset),
            parameter.children.get(offset + 1),
        ) {
            builder.bind_pattern(name, type_contract(ty), offset != 0);
        }
    }
    for statement in function.children.iter().skip(4) {
        builder.expression(statement, None, None)?;
    }
    Ok(Some(builder.graph))
}

#[derive(Clone)]
struct LoopTarget {
    label: Option<String>,
    break_target: NodeId,
    continue_target: NodeId,
    break_depth: usize,
    continue_depth: usize,
}

struct Builder<'a> {
    graph: Graph<'a>,
    environment: &'a AsyncTypeEnvironment,
    names: HashMap<String, BindingId>,
    scopes: Vec<Vec<BindingId>>,
    loops: Vec<LoopTarget>,
    tail: Vec<NodeId>,
    result: Option<String>,
}

impl<'a> Builder<'a> {
    fn node(&mut self, source: &'a SpannedExpr, action: Action, operands: Vec<NodeId>) -> NodeId {
        let id = NodeId(self.graph.nodes.len());
        self.graph.nodes.push(Node {
            source,
            scope: if matches!(action, Action::Await { .. }) {
                self.scopes.iter().flatten().copied().collect()
            } else {
                Vec::new()
            },
            action,
            operands,
            edges: Vec::new(),
        });
        id
    }

    fn edge(&mut self, from: NodeId, target: NodeId, kind: EdgeKind, value: Option<NodeId>) {
        self.graph.nodes[from.0].edges.push(Edge {
            target,
            kind,
            value,
        });
    }

    fn connect(&mut self, target: NodeId, value: Option<NodeId>) {
        for from in std::mem::take(&mut self.tail) {
            self.edge(from, target, EdgeKind::Next, value);
        }
    }

    fn emit(&mut self, source: &'a SpannedExpr, action: Action, operands: Vec<NodeId>) -> NodeId {
        let id = self.node(source, action, operands);
        self.connect(id, None);
        self.tail = vec![id];
        id
    }

    fn cleanup(&mut self, source: &'a SpannedExpr, depth: usize) {
        let bindings = self.scopes[depth..]
            .iter()
            .rev()
            .flatten()
            .copied()
            .collect();
        self.emit(source, Action::ScopeExit(bindings), Vec::new());
    }

    fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    fn pop_scope(&mut self, source: &'a SpannedExpr) {
        if !self.tail.is_empty() {
            self.cleanup(source, self.scopes.len() - 1);
        }
        for id in self.scopes.pop().unwrap() {
            let name = &self.graph.bindings[id.0].name;
            if self.names.get(name) == Some(&id) {
                self.names.remove(name);
            }
        }
    }

    fn bind_pattern(
        &mut self,
        pattern: &'a SpannedExpr,
        ty: Option<String>,
        mutable: bool,
    ) -> Vec<BindingId> {
        let mut fields = Vec::new();
        if let Some(ty) = &ty {
            // Layout errors belong to normal type validation; leave types unknown
            // when the source declaration environment is not yet complete.
            let _ = crate::async_fn::collect_enum_pattern_bindings(
                &crate::normalize_keywords(pattern.expr.clone()),
                ty,
                self.environment,
                &mut fields,
            );
        }
        let mut leaves = Vec::new();
        fn leaves_in<'a>(node: &'a SpannedExpr, leaves: &mut Vec<&'a SpannedExpr>) {
            if let Some(name) = symbol(node) {
                if name != "_" && !matches!(name, "true" | "false" | "#true" | "#false") {
                    leaves.push(node);
                }
            } else {
                for child in node.children.iter().skip(1) {
                    leaves_in(child, leaves);
                }
            }
        }
        if fields.is_empty() && symbol(pattern).is_none() {
            leaves_in(pattern, &mut leaves);
        } else if !fields.is_empty() {
            leaves_in(pattern, &mut leaves);
            leaves.retain(|leaf| {
                fields
                    .iter()
                    .any(|(name, _)| Some(name.as_str()) == symbol(leaf))
            });
        } else if ty.is_none() {
            leaves_in(pattern, &mut leaves);
        }
        let mut ids = Vec::new();
        for leaf in leaves {
            let name = symbol(leaf).unwrap().to_owned();
            let declared_type = fields
                .iter()
                .find(|(field, _)| field == &name)
                .map(|(_, ty)| ty.clone());
            let id = BindingId(self.graph.bindings.len());
            self.graph.bindings.push(Binding {
                name: name.clone(),
                declared_type,
                mutable,
                source: leaf,
            });
            self.names.insert(name, id);
            self.scopes.last_mut().unwrap().push(id);
            ids.push(id);
        }
        ids
    }

    fn declared_value_type(&self, node: &SpannedExpr) -> Option<String> {
        if let Some(name) = symbol(node) {
            return self
                .names
                .get(name)
                .and_then(|id| self.graph.bindings[id.0].declared_type.clone());
        }
        match head(node) {
            "literal" | "struct-literal" | "tuple" | "array-of" => {
                node.children.get(1).and_then(type_contract)
            }
            "await" if node.children.len() == 7 => type_contract(&node.children[1]),
            "call" => node
                .children
                .get(1)
                .and_then(symbol)
                .and_then(|name| self.environment.function_results.get(name))
                .cloned(),
            "clone" | "unsafe" => node
                .children
                .get(1)
                .and_then(|value| self.declared_value_type(value)),
            "as" => node.children.get(2).and_then(type_contract),
            _ => None,
        }
    }

    fn sequence(
        &mut self,
        nodes: &'a [SpannedExpr],
        expected: Option<&str>,
    ) -> Result<Option<NodeId>, Error> {
        let mut value = None;
        for (index, node) in nodes.iter().enumerate() {
            value = Some(self.expression(
                node,
                if index + 1 == nodes.len() {
                    expected
                } else {
                    None
                },
                None,
            )?);
        }
        Ok(value)
    }

    fn arm_start(&mut self, from: NodeId, source: &'a SpannedExpr, kind: EdgeKind) {
        let start = self.node(source, Action::Entry, Vec::new());
        self.edge(from, start, kind, None);
        self.tail = vec![start];
        self.push_scope();
    }

    fn conditional(
        &mut self,
        node: &'a SpannedExpr,
        expected: Option<&str>,
        short_circuit: bool,
    ) -> Result<NodeId, Error> {
        let c = &node.children;
        if c.len() < 3 {
            return self.evaluate(node, expected);
        }
        let condition = self.expression(&c[1], Some("bool"), None)?;
        let branch = self.emit(node, Action::Branch, vec![condition]);
        let join = self.node(node, Action::Join, Vec::new());
        let is_and = head(node) == "bool.&&";
        self.arm_start(
            branch,
            node,
            if short_circuit && !is_and {
                EdgeKind::False
            } else {
                EdgeKind::True
            },
        );
        let selected = self.expression(&c[2], expected, None)?;
        self.pop_scope(node);
        self.connect(join, Some(selected));
        self.arm_start(
            branch,
            node,
            if short_circuit && !is_and {
                EdgeKind::True
            } else {
                EdgeKind::False
            },
        );
        let other = if short_circuit {
            condition
        } else if let Some(other) = c.get(3) {
            self.expression(other, expected, None)?
        } else {
            self.emit(node, Action::Evaluate, Vec::new())
        };
        self.pop_scope(node);
        self.connect(join, Some(other));
        self.tail = vec![join];
        Ok(join)
    }

    fn match_value(
        &mut self,
        node: &'a SpannedExpr,
        expected: Option<&str>,
    ) -> Result<NodeId, Error> {
        let c = &node.children;
        if c.len() < 3 {
            return self.evaluate(node, expected);
        }
        let ty = self.declared_value_type(&c[1]);
        let value = self.expression(&c[1], ty.as_deref(), None)?;
        let join = self.node(node, Action::Join, Vec::new());
        for arm in c.iter().skip(2) {
            // Both original #case and the source-preserving normalized form.
            let offset = usize::from(head(arm) == "case");
            let Some(pattern) = arm.children.get(offset) else {
                continue;
            };
            let test = self.emit(pattern, Action::Pattern, vec![value]);
            let failed = self.node(pattern, Action::Entry, Vec::new());
            self.edge(test, failed, EdgeKind::False, None);
            self.arm_start(test, arm, EdgeKind::True);
            let bindings = self.bind_pattern(pattern, ty.clone(), false);
            self.emit(
                pattern,
                Action::PatternPreview(bindings.clone()),
                vec![value],
            );
            let mut body = offset + 1;
            if let Some(guard) = arm.children.get(body).filter(|guard| head(guard) == "when") {
                if let Some(guard_value) = guard.children.get(1) {
                    let guard_value = self.expression(guard_value, Some("bool"), None)?;
                    let branch = self.emit(guard, Action::Branch, vec![guard_value]);
                    let rejected = self.node(
                        guard,
                        Action::ScopeExit(self.scopes.last().unwrap().clone()),
                        Vec::new(),
                    );
                    self.edge(branch, rejected, EdgeKind::False, None);
                    self.edge(rejected, failed, EdgeKind::Next, None);
                    let accepted = self.node(guard, Action::Entry, Vec::new());
                    self.edge(branch, accepted, EdgeKind::True, None);
                    self.tail = vec![accepted];
                }
                body += 1;
            }
            self.emit(pattern, Action::PatternCommit(bindings), vec![value]);
            let selected = self.sequence(&arm.children[body..], expected)?;
            self.pop_scope(arm);
            self.connect(join, selected);
            self.tail = vec![failed];
        }
        // Unmatched exhaustiveness is checked by the ordinary type checker.
        self.tail = vec![join];
        Ok(join)
    }

    fn if_let(&mut self, node: &'a SpannedExpr, expected: Option<&str>) -> Result<NodeId, Error> {
        let c = &node.children;
        if c.len() < 4 {
            return self.evaluate(node, expected);
        }
        let ty = self.declared_value_type(&c[2]);
        let value = self.expression(&c[2], ty.as_deref(), None)?;
        let branch = self.emit(&c[1], Action::Pattern, vec![value]);
        let join = self.node(node, Action::Join, Vec::new());
        self.arm_start(branch, node, EdgeKind::True);
        let bindings = self.bind_pattern(&c[1], ty, false);
        self.emit(&c[1], Action::PatternCommit(bindings), vec![value]);
        let selected = self.expression(&c[3], expected, None)?;
        self.pop_scope(node);
        self.connect(join, Some(selected));
        self.arm_start(branch, node, EdgeKind::False);
        let other = if let Some(other) = c.get(4) {
            self.expression(other, expected, None)?
        } else {
            self.emit(node, Action::Evaluate, Vec::new())
        };
        self.pop_scope(node);
        self.connect(join, Some(other));
        self.tail = vec![join];
        Ok(join)
    }

    fn transfer(&mut self, node: &'a SpannedExpr) -> Result<NodeId, Error> {
        let named = matches!(head(node), "break-to" | "continue-to");
        let continuation = matches!(head(node), "continue" | "continue-to");
        let label = if named {
            node.children.get(1).and_then(symbol)
        } else {
            None
        };
        let target = self
            .loops
            .iter()
            .rev()
            .find(|target| !named || target.label.as_deref() == label)
            .cloned()
            .ok_or_else(|| Error {
                message: label.map_or_else(
                    || "break or continue used outside a loop".into(),
                    |label| format!("unknown or inactive loop label '{label}'"),
                ),
                span: node
                    .children
                    .get(usize::from(named))
                    .map_or(node.span, |child| child.span),
            })?;
        let value = if continuation {
            None
        } else {
            node.children
                .get(if named { 2 } else { 1 })
                .map(|value| self.expression(value, None, None))
                .transpose()?
        };
        self.cleanup(
            node,
            if continuation {
                target.continue_depth
            } else {
                target.break_depth
            },
        );
        let id = self.emit(node, Action::Transfer, value.into_iter().collect());
        self.edge(
            id,
            if continuation {
                target.continue_target
            } else {
                target.break_target
            },
            EdgeKind::Transfer,
            value,
        );
        self.tail.clear();
        Ok(id)
    }

    fn loop_value(&mut self, node: &'a SpannedExpr, label: Option<&str>) -> Result<NodeId, Error> {
        let c = &node.children;
        let enclosing_depth = self.scopes.len();
        self.push_scope();
        let kind = head(node);
        if kind == "for" {
            if let Some(init) = c.get(1) {
                self.expression(init, None, None)?;
            }
        }
        let range_type = if kind == "for-range" {
            c.get(1)
                .and_then(|binding| binding.children.get(1))
                .and_then(type_contract)
        } else {
            None
        };
        let counter = if kind == "for-range" {
            let id = BindingId(self.graph.bindings.len());
            self.graph.bindings.push(Binding {
                name: format!("lim.async.range-counter-{}", id.0),
                declared_type: range_type.clone(),
                mutable: true,
                source: node,
            });
            self.scopes.last_mut().unwrap().push(id);
            let value = c
                .get(2)
                .map(|start| self.expression(start, range_type.as_deref(), None))
                .transpose()?;
            self.emit(node, Action::RangeInit(id), value.into_iter().collect());
            Some(id)
        } else {
            None
        };
        let loop_head = self.emit(node, Action::LoopHead, Vec::new());
        let exit = self.node(node, Action::Join, Vec::new());
        let step = if matches!(kind, "for" | "for-range") {
            self.node(node, Action::Entry, Vec::new())
        } else {
            loop_head
        };
        self.loops.push(LoopTarget {
            label: label.map(str::to_owned),
            break_target: exit,
            continue_target: step,
            break_depth: enclosing_depth,
            continue_depth: self.scopes.len(),
        });
        let body_offset = match kind {
            "loop" => 1,
            "while" | "while-let" => 2,
            "for" | "for-range" => 4,
            _ => 1,
        };
        if kind != "loop" {
            let condition = if kind == "for-range" {
                // Preserve ordinary #for-range desugaring: start executes once,
                // while end executes at each condition check, including awaits.
                let end = c
                    .get(3)
                    .map(|end| self.expression(end, range_type.as_deref(), None))
                    .transpose()?;
                self.emit(
                    node,
                    Action::RangeCondition(counter.unwrap()),
                    end.into_iter().collect(),
                )
            } else if let Some(condition) = c.get(if kind == "for" {
                2
            } else if kind == "while-let" {
                2
            } else {
                1
            }) {
                self.expression(
                    condition,
                    if kind == "while-let" {
                        None
                    } else {
                        Some("bool")
                    },
                    None,
                )?
            } else {
                self.emit(node, Action::Evaluate, Vec::new())
            };
            let branch = self.emit(
                node,
                if kind == "while-let" {
                    Action::Pattern
                } else {
                    Action::Branch
                },
                vec![condition],
            );
            let rejected = self.node(
                node,
                Action::ScopeExit(self.scopes.last().unwrap().clone()),
                Vec::new(),
            );
            self.edge(branch, rejected, EdgeKind::False, None);
            self.edge(rejected, exit, EdgeKind::Next, None);
            self.arm_start(branch, node, EdgeKind::True);
            if kind == "while-let" {
                if let Some(pattern) = c.get(1) {
                    let ty = c.get(2).and_then(|value| self.declared_value_type(value));
                    let ids = self.bind_pattern(pattern, ty, false);
                    self.emit(pattern, Action::PatternCommit(ids), vec![condition]);
                }
            }
        } else {
            self.push_scope();
        }
        if kind == "for-range" {
            if let Some(name) = c.get(1).and_then(|binding| binding.children.first()) {
                let ids = self.bind_pattern(name, range_type, false);
                let value = self.emit(name, Action::Read(counter.unwrap()), Vec::new());
                self.emit(name, Action::Bind(ids), vec![value]);
            }
        }
        self.sequence(
            c.get(body_offset + usize::from(kind == "while-let")..)
                .unwrap_or(&[]),
            None,
        )?;
        self.pop_scope(node);
        self.connect(step, None);
        if step != loop_head {
            self.tail = vec![step];
            if kind == "for" {
                if let Some(step_expression) = c.get(3) {
                    self.expression(step_expression, None, None)?;
                }
            } else {
                self.emit(node, Action::RangeStep(counter.unwrap()), Vec::new());
            }
            self.connect(loop_head, None);
        }
        self.loops.pop();
        self.tail.clear();
        self.pop_scope(node);
        self.tail = vec![exit];
        Ok(exit)
    }

    fn expression(
        &mut self,
        node: &'a SpannedExpr,
        expected: Option<&str>,
        label: Option<&str>,
    ) -> Result<NodeId, Error> {
        let c = &node.children;
        if let Some(name) = symbol(node) {
            return Ok(self.emit(
                node,
                self.names
                    .get(name)
                    .copied()
                    .map_or(Action::Evaluate, Action::Read),
                Vec::new(),
            ));
        }
        match head(node) {
            "let" | "let-mut" | "let-else" if c.len() >= 4 => {
                let ty = type_contract(&c[2]);
                let value = self.expression(&c[3], ty.as_deref(), None)?;
                if head(node) == "let-else" {
                    let branch = self.emit(&c[1], Action::Pattern, vec![value]);
                    self.arm_start(branch, node, EdgeKind::False);
                    if let Some(other) = c.get(4) {
                        if head(other) == "else" {
                            if let Some(pattern) = other.children.get(1) {
                                let ids = self.bind_pattern(pattern, ty.clone(), false);
                                self.emit(pattern, Action::Bind(ids), vec![value]);
                            }
                            for statement in other.children.iter().skip(2) {
                                self.expression(statement, None, None)?;
                            }
                        } else {
                            self.expression(other, None, None)?;
                        }
                    }
                    self.pop_scope(node);
                    // The else path must diverge; normal checking enforces this.
                    self.tail.clear();
                    let success = self.node(node, Action::Entry, Vec::new());
                    self.edge(branch, success, EdgeKind::True, None);
                    self.tail = vec![success];
                }
                let ids = self.bind_pattern(&c[1], ty, head(node) == "let-mut");
                Ok(self.emit(node, Action::Bind(ids), vec![value]))
            }
            "set"
                if c.len() == 3
                    && c.get(1)
                        .and_then(symbol)
                        .is_some_and(|name| self.names.contains_key(name)) =>
            {
                let id = self.names[symbol(&c[1]).unwrap()];
                let ty = self.graph.bindings[id.0].declared_type.clone();
                let value = self.expression(&c[2], ty.as_deref(), None)?;
                Ok(self.emit(node, Action::Assign(id), vec![value]))
            }
            "return" => {
                let ty = self.result.clone();
                let value = c
                    .get(1)
                    .map(|value| self.expression(value, ty.as_deref(), None))
                    .transpose()?;
                self.cleanup(node, 0);
                let id = self.emit(node, Action::Return, value.into_iter().collect());
                self.tail.clear();
                Ok(id)
            }
            "break" | "break-to" | "continue" | "continue-to" => self.transfer(node),
            "label" if c.len() == 3 => self.expression(&c[2], expected, symbol(&c[1])),
            "loop" | "while" | "while-let" | "for" | "for-range" => self.loop_value(node, label),
            "block" | "unsafe" => {
                self.push_scope();
                let value = self.sequence(&c[1..], expected)?;
                self.pop_scope(node);
                Ok(self.emit(node, Action::Join, value.into_iter().collect()))
            }
            "if" => self.conditional(node, expected, false),
            "if-let" => self.if_let(node, expected),
            "bool.&&" | "bool.||" => self.conditional(node, Some("bool"), true),
            "match" => self.match_value(node, expected),
            "await" if matches!(c.len(), 6 | 7) => {
                let offset = usize::from(c.len() == 7);
                let task_type = type_contract(&c[1 + offset]);
                let child = self.expression(&c[5 + offset], task_type.as_deref(), None)?;
                let result_type = if offset != 0 {
                    type_contract(&c[1])
                } else {
                    expected.map(str::to_owned)
                };
                let suspension = self.emit(node, Action::Await { result_type }, vec![child]);
                self.edge(suspension, suspension, EdgeKind::Pending, None);
                let resumed = self.node(node, Action::Join, vec![suspension]);
                self.edge(suspension, resumed, EdgeKind::Ready, None);
                self.tail = vec![resumed];
                Ok(resumed)
            }
            _ => self.evaluate(node, expected),
        }
    }

    fn evaluate(
        &mut self,
        node: &'a SpannedExpr,
        _expected: Option<&str>,
    ) -> Result<NodeId, Error> {
        let c = &node.children;
        let mut operands = Vec::new();
        match head(node) {
            "quote" | "quasiquote" | "literal" | "size-of" | "align-of" | "offset-of" => {}
            "call" | "struct-literal" if c.len() == 3 => {
                let name = symbol(&c[1]).unwrap_or("");
                let order = if head(node) == "call" {
                    self.environment.function_parameter_order.get(name)
                } else {
                    self.environment.struct_field_order.get(name)
                };
                let fields = &c[2].children;
                let mut ordered = Vec::new();
                if let Some(order) = order {
                    for key in order {
                        ordered.extend(fields.iter().filter(|field| {
                            field.children.first().and_then(symbol) == Some(key.as_str())
                        }));
                    }
                }
                // Preserve unknown/malformed arguments for normal validation.
                for field in fields {
                    if !ordered.iter().any(|known| std::ptr::eq(*known, field)) {
                        ordered.push(field);
                    }
                }
                for field in ordered {
                    if let Some(value) = field.children.get(1) {
                        let ty = if head(node) == "call" {
                            self.environment.functions.get(name)
                        } else {
                            self.environment.struct_fields.get(name)
                        }
                        .and_then(|fields| {
                            field
                                .children
                                .first()
                                .and_then(symbol)
                                .and_then(|key| fields.get(key))
                        });
                        operands.push(self.expression(value, ty.map(String::as_str), None)?);
                    }
                }
            }
            "get" | "get-payload" | "as" => {
                if let Some(value) = c.get(1) {
                    operands.push(self.expression(value, None, None)?);
                }
            }
            "set-field" | "set-payload" => {
                if let Some(value) = c.get(1) {
                    operands.push(self.expression(value, None, None)?);
                }
                if let Some(value) = c.last() {
                    operands.push(self.expression(value, None, None)?);
                }
            }
            "asm" => {
                if let Some(inputs) = c.get(2) {
                    for input in &inputs.children {
                        if let Some(value) = input.children.get(1) {
                            operands.push(self.expression(value, None, None)?);
                        }
                    }
                }
            }
            operation => {
                let offset = if matches!(operation, "tuple" | "array-of")
                    || (operation == "array-repeat" && c.len() == 3)
                {
                    2
                } else {
                    1
                };
                for value in c.iter().skip(offset) {
                    operands.push(self.expression(value, None, None)?);
                }
            }
        }
        Ok(self.emit(node, Action::Evaluate, operands))
    }
}

/// Separate liveness domains avoid confusing source bindings with computed
/// operand temporaries. The latter matter for awaits nested in expressions.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Live {
    pub bindings: HashSet<BindingId>,
    pub values: HashSet<NodeId>,
}

impl Graph<'_> {
    pub(crate) fn reachable(&self) -> HashSet<NodeId> {
        let mut seen = HashSet::new();
        let mut pending = vec![self.entry];
        while let Some(node) = pending.pop() {
            if seen.insert(node) {
                pending.extend(self.nodes[node.0].edges.iter().map(|edge| edge.target));
            }
        }
        seen
    }

    /// Backward data-use liveness with edge-selected join operands. This does
    /// not account for mandatory destruction or prove that a value owns a loan.
    pub(crate) fn data_liveness(&self) -> Vec<Live> {
        let reachable = self.reachable();
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        for (index, node) in self.nodes.iter().enumerate() {
            for edge in &node.edges {
                predecessors[edge.target.0].push(NodeId(index));
            }
        }
        let mut live = vec![Live::default(); self.nodes.len()];
        let mut outputs = live.clone();
        let mut queue: VecDeque<_> = (0..self.nodes.len())
            .rev()
            .filter(|index| reachable.contains(&NodeId(*index)))
            .collect();
        let mut queued = vec![true; self.nodes.len()];
        while let Some(index) = queue.pop_front() {
            queued[index] = false;
            let node = &self.nodes[index];
            let mut out = Live::default();
            for edge in &node.edges {
                let successor = &live[edge.target.0];
                out.bindings.extend(&successor.bindings);
                out.values.extend(&successor.values);
                if let Some(value) = edge.value {
                    if outputs[edge.target.0].values.contains(&edge.target) {
                        out.values.insert(value);
                    }
                }
            }
            let mut input = out.clone();
            input.values.remove(&NodeId(index));
            input.values.extend(&node.operands);
            match &node.action {
                Action::Read(binding)
                | Action::RangeCondition(binding)
                | Action::RangeStep(binding) => {
                    input.bindings.insert(*binding);
                }
                Action::Bind(bindings)
                | Action::PatternPreview(bindings)
                | Action::PatternCommit(bindings)
                | Action::ScopeExit(bindings) => {
                    for binding in bindings {
                        input.bindings.remove(binding);
                    }
                }
                Action::Assign(binding) | Action::RangeInit(binding) => {
                    input.bindings.remove(binding);
                }
                _ => {}
            }
            if input != live[index] || out != outputs[index] {
                live[index] = input;
                outputs[index] = out;
                for predecessor in &predecessors[index] {
                    if !queued[predecessor.0] {
                        queued[predecessor.0] = true;
                        queue.push_back(predecessor.0);
                    }
                }
            }
        }
        live
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parsed(source: &str) -> Vec<SpannedExpr> {
        crate::parse(source).unwrap()
    }

    fn source_text<'a>(source: &'a str, node: &Node<'_>) -> &'a str {
        &source[node.source.span.start..node.source.span.end]
    }

    fn binding(graph: &Graph<'_>, name: &str) -> BindingId {
        BindingId(
            graph
                .bindings
                .iter()
                .position(|binding| binding.name == name)
                .unwrap(),
        )
    }

    #[test]
    fn pending_retries_only_the_poll_and_keeps_exact_source() {
        let source = "(#fn work ((saved u64)) u64
          (#let answer u64 (#await u64 Child Pending Ready poll
            (#call make (: value saved))))
          (#return (#u64.+.wrap saved answer)))";
        let parsed = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&parsed[0], &environment).unwrap().unwrap();
        let (index, await_node) = graph
            .nodes
            .iter()
            .enumerate()
            .find(|(_, node)| matches!(node.action, Action::Await { .. }))
            .unwrap();
        assert_eq!(
            source_text(source, await_node),
            "(#await u64 Child Pending Ready poll\n            (#call make (: value saved)))"
        );
        assert_eq!(
            await_node
                .edges
                .iter()
                .map(|edge| edge.kind)
                .collect::<Vec<_>>(),
            vec![EdgeKind::Pending, EdgeKind::Ready]
        );
        assert_eq!(await_node.edges[0].target, NodeId(index));
        let child = await_node.operands[0];
        assert_eq!(head(graph.nodes[child.0].source), "call");
        assert!(!await_node.edges.iter().any(|edge| edge.target == child));
        assert!(graph.data_liveness()[index]
            .bindings
            .contains(&binding(&graph, "saved")));
        assert_eq!(
            graph.bindings[binding(&graph, "answer").0]
                .declared_type
                .as_deref(),
            Some("u64")
        );
    }

    #[test]
    fn captures_computed_operands_but_keeps_unread_storage_separate() {
        let source = "(#fn work ((saved u64) (unread Resource)) u64
          (#let answer u64 (#u64.+.wrap (#clone saved)
            (#await u64 Child Pending Ready poll ())))
          (#forget unread)
          (#return answer))";
        let forms = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&forms[0], &environment).unwrap().unwrap();
        let (index, node) = graph
            .nodes
            .iter()
            .enumerate()
            .find(|(_, node)| matches!(node.action, Action::Await { .. }))
            .unwrap();
        let live = graph.data_liveness();
        let operand = graph
            .nodes
            .iter()
            .position(|node| source_text(source, node) == "(#clone saved)")
            .unwrap();
        assert!(live[index].values.contains(&NodeId(operand)));
        assert!(!live[index].bindings.contains(&binding(&graph, "saved")));
        assert!(node.scope.contains(&binding(&graph, "saved")));
        assert!(node.scope.contains(&binding(&graph, "unread")));
        // An unread linear parameter still requires consumption at cancellation:
        // absence from data liveness is never permission to discard its slot.
        let no_read = source.replace("(#forget unread)", "()");
        let no_read_parsed = parsed(&no_read);
        let graph = build(&no_read_parsed[0], &environment).unwrap().unwrap();
        let (index, node) = graph
            .nodes
            .iter()
            .enumerate()
            .find(|(_, node)| matches!(node.action, Action::Await { .. }))
            .unwrap();
        assert!(!graph.data_liveness()[index]
            .bindings
            .contains(&binding(&graph, "unread")));
        assert!(node.scope.contains(&binding(&graph, "unread")));
    }

    #[test]
    fn outer_transfers_keep_targets_and_scope_exits() {
        let source = "(#fn work ((flag bool)) u64
          (#let result u64 (#label outer (#loop
            (#let owner Resource ())
            (#for (#let-mut index u64 0u64) flag (#set index 1u64)
              (#let child Child ())
              (#let ready u64 (#await u64 Child Pending Ready poll child))
              (#if flag (#continue-to outer) (#break-to outer ready))))))
          (#return result))";
        let parsed = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&parsed[0], &environment).unwrap().unwrap();
        let outer_head = graph
            .nodes
            .iter()
            .position(|node| node.action == Action::LoopHead && head(node.source) == "loop")
            .unwrap();
        let outer_exit = graph
            .nodes
            .iter()
            .position(|node| node.action == Action::Join && head(node.source) == "loop")
            .unwrap();
        let transfers = graph
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| node.action == Action::Transfer)
            .collect::<Vec<_>>();
        assert_eq!(transfers.len(), 2);
        for (index, node) in transfers {
            let target = if head(node.source) == "continue-to" {
                outer_head
            } else {
                outer_exit
            };
            assert_eq!(node.edges[0].target, NodeId(target));
            let cleanup = graph
                .nodes
                .iter()
                .find(|candidate| {
                    candidate
                        .edges
                        .iter()
                        .any(|edge| edge.target == NodeId(index))
                })
                .unwrap();
            let Action::ScopeExit(exited) = &cleanup.action else {
                panic!("missing transfer cleanup")
            };
            for name in ["owner", "index", "child", "ready"] {
                assert!(exited.contains(&binding(&graph, name)), "{name}");
            }
            assert!(!exited.contains(&binding(&graph, "flag")));
        }
    }

    #[test]
    fn for_continue_goes_to_step_while_continue_goes_to_condition() {
        let source = "(#fn work ((flag bool)) ()
          (#for () flag (#await () Child Pending Ready poll ()) (#continue))
          (#while flag (#continue))
          (#return ()))";
        let parsed = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&parsed[0], &environment).unwrap().unwrap();
        let targets = graph
            .nodes
            .iter()
            .filter(|node| node.action == Action::Transfer)
            .map(|node| &graph.nodes[node.edges[0].target.0])
            .collect::<Vec<_>>();
        assert_eq!(targets.len(), 2);
        assert_eq!(head(targets[0].source), "for");
        assert_eq!(targets[0].action, Action::Entry);
        assert_eq!(head(targets[1].source), "while");
        assert_eq!(targets[1].action, Action::LoopHead);
        assert!(graph
            .reachable()
            .iter()
            .any(|id| matches!(graph.nodes[id.0].action, Action::Await { .. })));
    }

    #[test]
    fn match_and_if_let_keep_declared_pattern_types_and_guard_paths() {
        let source = "(#enum Choice ((Some (#tuple u64 bool)) (None)))
          (#fn work ((choice Choice)) u64
            (#return (#match choice
              (#case (Some (#tuple amount enabled)) (#when enabled)
                (#await u64 Child Pending Ready poll amount))
              (#case _ (#if-let (Some (#tuple fallback _)) choice fallback 0u64)))))";
        let mut parsed = parsed(source);
        let environment = crate::async_type_environment(&parsed);
        // Production sees #case-normalized source children; verify both forms.
        for normalized in [false, true] {
            if normalized {
                crate::normalize_match_case_forms(&mut parsed[1]).unwrap();
            }
            let graph = build(&parsed[1], &environment).unwrap().unwrap();
            for name in ["amount", "fallback"] {
                assert_eq!(
                    graph.bindings[binding(&graph, name).0]
                        .declared_type
                        .as_deref(),
                    Some("u64")
                );
            }
            assert_eq!(
                graph.bindings[binding(&graph, "enabled").0]
                    .declared_type
                    .as_deref(),
                Some("bool")
            );
            let guard = graph
                .nodes
                .iter()
                .find(|node| node.action == Action::Branch && head(node.source) == "when")
                .unwrap();
            let false_edge = guard
                .edges
                .iter()
                .find(|edge| edge.kind == EdgeKind::False)
                .unwrap();
            let Action::ScopeExit(exited) = &graph.nodes[false_edge.target.0].action else {
                panic!("guard locals must expire")
            };
            assert!(exited.contains(&binding(&graph, "amount")));
            assert!(exited.contains(&binding(&graph, "enabled")));
        }
    }

    #[test]
    fn named_operands_follow_declarations_not_written_order() {
        let source = "(#struct Values ((first u64) (second u64)))
          (#fn combine ((first u64) (second u64)) u64 (#return first))
          (#fn work () u64
            (#let record Values (#struct-literal Values (: second
              (#await u64 Child Pending Ready poll 2u64) : first 1u64)))
            (#return (#call combine (: second
              (#await u64 Child Pending Ready poll 4u64) : first 3u64))))";
        let parsed = parsed(source);
        let environment = crate::async_type_environment(&parsed);
        let graph = build(&parsed[2], &environment).unwrap().unwrap();
        let indices = ["1u64", "2u64", "3u64", "4u64"].map(|text| {
            graph
                .nodes
                .iter()
                .position(|node| source_text(source, node) == text)
                .unwrap()
        });
        assert!(indices[0] < indices[1]);
        assert!(indices[2] < indices[3]);
        let live = graph.data_liveness();
        for (index, node) in graph
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| matches!(node.action, Action::Await { .. }))
        {
            let first = if node.source.span.start < source.find("(#return (#call").unwrap() {
                indices[0]
            } else {
                indices[2]
            };
            assert!(live[index].values.contains(&NodeId(first)));
        }
    }

    #[test]
    fn skipped_branches_and_scope_exits_do_not_invent_live_locals() {
        let source = "(#fn work ((flag bool) (saved u64)) u64
          (#let selected u64 (#if flag
            (#block (#let local u64 1u64) local)
            (#await u64 Child Pending Ready poll saved)))
          (#return selected))";
        let parsed = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&parsed[0], &environment).unwrap().unwrap();
        let local = binding(&graph, "local");
        let live = graph.data_liveness();
        let (index, node) = graph
            .nodes
            .iter()
            .enumerate()
            .find(|(_, node)| matches!(node.action, Action::Await { .. }))
            .unwrap();
        assert!(!node.scope.contains(&local));
        assert!(!live[index].bindings.contains(&local));
        assert!(!live[graph.entry.0].bindings.contains(&local));
        assert!(live[index]
            .values
            .iter()
            .all(|value| !matches!(graph.nodes[value.0].action, Action::Read(id) if id == local)));
    }

    #[test]
    fn invalid_transfer_reports_original_label_or_keyword_span() {
        for (form, underline) in [
            ("(#break)", "#break"),
            ("(#continue-to missing)", "missing"),
        ] {
            let source = format!(
                "(#fn work () () (#await () Child Pending Ready poll ()) {form} (#return ()))"
            );
            let parsed = parsed(&source);
            let environment = AsyncTypeEnvironment::default();
            let error = build(&parsed[0], &environment).unwrap_err();
            assert_eq!(&source[error.span.start..error.span.end], underline);
        }
    }

    #[test]
    fn return_and_unreachable_source_do_not_reenter_loop() {
        let source = "(#fn work () u64 (#loop (#return 42u64) (#await u64 Child Pending Ready poll ())) (#return 0u64))";
        let parsed = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&parsed[0], &environment).unwrap().unwrap();
        let reachable = graph.reachable();
        assert_eq!(
            graph
                .nodes
                .iter()
                .enumerate()
                .filter(|(index, node)| reachable.contains(&NodeId(*index))
                    && node.action == Action::Return)
                .count(),
            1
        );
        assert!(!graph
            .nodes
            .iter()
            .enumerate()
            .any(|(index, node)| reachable.contains(&NodeId(index))
                && matches!(node.action, Action::Await { .. })));
    }

    #[test]
    fn range_start_is_once_but_end_is_a_loop_condition() {
        let source = "(#fn work () () (#for-range (index u64)
          (#await u64 Child Pending Ready poll 0u64)
          (#await u64 Child Pending Ready poll 4u64)
          (#continue)) (#return ()))";
        let forms = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&forms[0], &environment).unwrap().unwrap();
        let awaits = graph
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| matches!(node.action, Action::Await { .. }))
            .map(|(index, _)| NodeId(index))
            .collect::<Vec<_>>();
        let loop_head = NodeId(
            graph
                .nodes
                .iter()
                .position(|node| node.action == Action::LoopHead)
                .unwrap(),
        );
        let mut visited = HashSet::new();
        let mut pending = vec![loop_head];
        while let Some(id) = pending.pop() {
            if visited.insert(id) {
                pending.extend(graph.nodes[id.0].edges.iter().map(|edge| edge.target));
            }
        }
        assert!(!visited.contains(&awaits[0]));
        assert!(visited.contains(&awaits[1]));
        let step = graph
            .nodes
            .iter()
            .find(|node| matches!(node.action, Action::RangeStep(_)))
            .unwrap();
        assert_eq!(step.edges[0].target, loop_head);
        assert_eq!(
            graph.bindings[binding(&graph, "index").0]
                .declared_type
                .as_deref(),
            Some("u64")
        );
    }

    #[test]
    fn metadata_symbols_are_not_value_reads() {
        let source = "(#fn work ((field u64) (parameter u64) (record Record)) u64
          (#let result u64 (#await u64 Child Pending Ready poll
            (#call child (: parameter (#get record field)))))
          (#return result))";
        let forms = parsed(source);
        let environment = AsyncTypeEnvironment::default();
        let graph = build(&forms[0], &environment).unwrap().unwrap();
        let reads = graph
            .nodes
            .iter()
            .filter_map(|node| {
                if let Action::Read(id) = node.action {
                    Some(id)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        assert!(!reads.contains(&binding(&graph, "field")));
        assert!(!reads.contains(&binding(&graph, "parameter")));
        assert!(reads.contains(&binding(&graph, "record")));
    }
}
