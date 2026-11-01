//! Original async bodies analyzed through ordinary function calls.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! The synchronous driver is an analysis model, not the async runtime. It
//! evaluates a child once and polls it in an ordinary loop until Ready. The
//! source function's branches, scopes and transfers are left intact. Ordinary
//! type/ownership/loan checking can therefore see the original body separately
//! from the proposed generated dispatcher and its physical storage layout.
//!
//! This is not permission to emit unsafe frame operations. In particular,
//! physical storage and computed operands must be validated by the graph
//! emitter, followed by ordinary checking of its generated program.
#![allow(dead_code)] // Source-body mappings are also inspected by structural tests.

use std::collections::{HashMap, HashSet};

use crate::typed_body::{Body, NodeId, NodeKind};
use crate::typed_flow::{FlowAction, FlowGraph, FlowNodeId};
use crate::{Expr, Item, Program, Span, SpannedExpr, Type};

#[derive(Debug)]
pub(crate) struct Error {
    pub message: String,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Source {
    pub function: SpannedExpr,
    pub waker: Type,
    pub pinned_frame: Option<String>,
    pub generated_poll: Option<String>,
    /// Explicit literal source parameter names requesting post-terminal access.
    pub frame_access: Vec<(String, String)>,
}

impl Source {
    /// Retain the canonical original tree before match/argument normalization.
    pub(crate) fn from_invocation(node: &SpannedExpr) -> Result<Option<Self>, String> {
        if !crate::is_async_invocation(node) {
            return Ok(None);
        }
        fn find_function(node: &SpannedExpr) -> Option<&SpannedExpr> {
            match head(node) {
                "fn" => Some(node),
                "quote" | "quasiquote" => None,
                _ => node.children.iter().find_map(find_function),
            }
        }
        let Some(function) = find_function(node) else {
            return Ok(None); // The normal generator diagnoses malformed declarations.
        };
        let Expr::List(parts) = crate::normalize_builtin_generator_invocation(&node.expr)? else {
            return Ok(None);
        };
        let waker = crate::parse_type(
            parts
                .get(3)
                .map(|value| crate::normalize_keywords(value.clone()))
                .as_ref(),
        )?;
        let pinned_frame = if matches!(parts.get(1), Some(Expr::Symbol(name)) if name == "#async-fn-pinned")
        {
            match parts.get(2) {
                Some(Expr::List(names)) => names.first().and_then(|name| match name {
                    Expr::Symbol(name) => Some(name.clone()),
                    _ => None,
                }),
                _ => None,
            }
        } else {
            None
        };
        let generated_poll = match parts.get(2) {
            Some(Expr::List(names)) => names.get(4).and_then(|name| match name {
                Expr::Symbol(name) => Some(name.clone()),
                _ => None,
            }),
            _ => None,
        };
        Ok(Some(Self {
            function: function.clone(),
            waker,
            pinned_frame,
            generated_poll,
            frame_access: match parts.get(2) {
                Some(Expr::List(names)) => match names.get(6) {
                    Some(Expr::List(access)) => access
                        .iter()
                        .map(|entry| match entry {
                            Expr::List(pair) => match pair.as_slice() {
                                [Expr::Symbol(parameter), Expr::Symbol(name)] => {
                                    Ok((parameter.clone(), name.clone()))
                                }
                                _ => Err("async access requires (parameter accessor-name) pairs"
                                    .to_owned()),
                            },
                            _ => {
                                Err("async access requires (parameter accessor-name) pairs"
                                    .to_owned())
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                    None => Vec::new(),
                    _ => return Err("async access parameters must be a list".into()),
                },
                _ => Vec::new(),
            },
        }))
    }
}

pub(crate) struct AwaitSite {
    /// Path in the original #fn tree; unlike a span, unique even for syntax
    /// bundles whose expanded nodes all point to their single use site.
    pub source_path: Vec<usize>,
    pub span: Span,
    pub keyword_span: Span,
    pub child_span: Span,
    pub driver: String,
    pub child_type: Type,
    pub result_type: Type,
    pub poll: String,
    pub pending: String,
    pub ready: String,
}

pub(crate) struct Lowered {
    pub function: SpannedExpr,
    pub source_name: String,
    pub body_name: String,
    pub waker_binding: String,
    pub awaits: Vec<AwaitSite>,
    drivers: Vec<(Span, String)>,
}

#[derive(Debug)]
pub(crate) struct CheckedAwait {
    pub source_path: Vec<usize>,
    pub span: Span,
    /// The child has been evaluated here. A Pending frame retains this value,
    /// not a replay of the original constructor expression.
    pub child_value: NodeId,
    pub result_value: NodeId,
    pub call: FlowNodeId,
    pub child_type: Type,
    pub result_type: Type,
}

#[derive(Debug)]
pub(crate) struct Suspension {
    pub site: CheckedAwait,
    /// None denotes an unreachable original await, never an empty live frame.
    pub storage: Option<crate::generator::async_storage::Snapshot>,
}

fn head(node: &SpannedExpr) -> &str {
    match node.children.first().map(|node| &node.expr) {
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

fn atom(value: &str, span: Span) -> SpannedExpr {
    SpannedExpr {
        expr: Expr::Symbol(value.into()),
        span,
        children: Vec::new(),
    }
}

fn list(children: Vec<SpannedExpr>, span: Span) -> SpannedExpr {
    SpannedExpr {
        expr: Expr::List(children.iter().map(|node| node.expr.clone()).collect()),
        span,
        children,
    }
}

fn rebuild(node: &mut SpannedExpr) {
    node.expr = Expr::List(
        node.children
            .iter()
            .map(|child| child.expr.clone())
            .collect(),
    );
}

fn names(expr: &Expr, output: &mut HashSet<String>) {
    match expr {
        Expr::Symbol(name) => {
            output.insert(name.clone());
        }
        Expr::List(children) => {
            for child in children {
                names(child, output);
            }
        }
        Expr::Quote(child)
        | Expr::QuasiQuote(child)
        | Expr::Unquote(child)
        | Expr::UnquoteSplicing(child)
        | Expr::Labeled {
            expression: child, ..
        } => names(child, output),
        _ => {}
    }
}

struct Builder<'a> {
    base: &'a Program,
    interfaces: Option<&'a crate::generator::async_interfaces::Registry>,
    aliases: HashMap<String, Type>,
    used: HashSet<String>,
    prefix: String,
    next: usize,
    waker: Type,
    waker_binding: String,
    sites: Vec<AwaitSite>,
    drivers: Vec<(Span, String)>,
    frame: Option<(String, HashMap<String, Type>)>,
}

impl Builder<'_> {
    fn fail(&self, node: &SpannedExpr, message: impl Into<String>) -> Error {
        Error {
            message: message.into(),
            span: node.span,
        }
    }

    fn fresh(&mut self, role: &str) -> String {
        loop {
            let name = format!("{}.{}.{role}", self.prefix, self.next);
            self.next += 1;
            if self.used.insert(name.clone()) {
                return name;
            }
        }
    }

    fn ty(&self, node: &SpannedExpr) -> Result<Type, Error> {
        crate::parse_type(Some(&crate::normalize_keywords(node.expr.clone())))
            .map_err(|message| self.fail(node, message))
    }

    fn resolved(&self, ty: &Type, node: &SpannedExpr) -> Result<Type, Error> {
        crate::typed_ir::resolve_type(ty, &self.aliases).map_err(|message| self.fail(node, message))
    }

    fn expression(
        &mut self,
        node: &SpannedExpr,
        path: &mut Vec<usize>,
        statement: bool,
    ) -> Result<SpannedExpr, Error> {
        if head(node) == "await" {
            return self.await_expression(node, path);
        }
        if matches!(head(node), "quote" | "quasiquote") || !matches!(node.expr, Expr::List(_)) {
            return Ok(node.clone());
        }
        let mut output = node.clone();
        // Empty children are a generated syntax node, not evidence of exact
        // original locations. Its owning parser must establish a source tree.
        if output.children.is_empty() {
            return Ok(output);
        }
        for (index, child) in output.children.iter_mut().enumerate() {
            path.push(index);
            let statement_child = match head(node) {
                "block" | "unsafe" | "loop" => index >= 1,
                "while" => index >= 2,
                "while-let" => index >= 3,
                "for" => index == 1 || index >= 3,
                "let-else" if node.children.len() == 4 && head(&node.children[3]) == "else" => {
                    index == 3
                }
                "for-range" | "let-else" => index >= 4,
                "else" => index >= 1,
                "label" => index == 2 && statement,
                _ => false,
            };
            *child = self.expression(child, path, statement_child)?;
            path.pop();
        }
        if matches!(
            head(node),
            "pin" | "pin-shared" | "pin-borrow" | "pin-borrow-mut"
        ) && output.children.len() == 2
        {
            if let Some((frame, owners)) = &self.frame {
                fn project(node: &mut SpannedExpr, frame: &str, owners: &HashMap<String, Type>) {
                    if symbol(node).is_some_and(|name| owners.contains_key(name)) {
                        *node = list(
                            vec![
                                atom("#get", node.span),
                                atom(frame, node.span),
                                node.clone(),
                            ],
                            node.span,
                        );
                    } else if matches!(head(node), "get" | "get-payload")
                        && node.children.len() >= 2
                    {
                        project(&mut node.children[1], frame, owners);
                        rebuild(node);
                    }
                }
                project(&mut output.children[1], frame, owners);
                if matches!(head(node), "pin" | "pin-shared") {
                    // Local pinning has become a projection into stationary
                    // frame storage; validate it as an ordinary pinned reborrow.
                    output.children[0] = atom(
                        if head(node) == "pin" {
                            "#pin-borrow-mut"
                        } else {
                            "#pin-borrow"
                        },
                        output.children[0].span,
                    );
                }
            }
        }
        rebuild(&mut output);
        if matches!(head(node), "let" | "let-mut") && node.children.len() == 4 {
            if let Some(name) = symbol(&node.children[1]) {
                if let Some(ty) = self
                    .frame
                    .as_ref()
                    .and_then(|(_, owners)| owners.get(name))
                    .cloned()
                {
                    // The real, ordinarily checked factory transfers this
                    // binding into the named sibling field. Model that handoff
                    // at its declaration, not as an exit-check exemption or a
                    // second owned stack copy. The receiver uses the actual
                    // destination field type, so an incompatible move fails.
                    let transfer = self.handoff(name, &ty, node.children[1].span);
                    output = list(
                        vec![
                            atom("#block", node.span),
                            output,
                            transfer,
                            list(Vec::new(), node.span),
                        ],
                        node.span,
                    );
                }
            }
        }
        if !statement {
            // Async source permits transfers directly in expression arms.
            // Ordinary functions spell these as statement-bearing blocks.
            let tail = match head(node) {
                "return" | "break" | "break-to" | "continue" | "continue-to" => Some(list(
                    vec![atom("#unreachable", node.children[0].span)],
                    node.span,
                )),
                "let" | "let-mut" | "set" | "set-index" | "set-field" | "set-payload" | "for"
                | "for-range" | "while" | "while-let" => Some(list(Vec::new(), node.span)),
                _ => None,
            };
            if let Some(tail) = tail {
                output = list(
                    vec![atom("#block", node.children[0].span), output, tail],
                    node.span,
                );
            }
        }
        Ok(output)
    }

    fn handoff(&mut self, name: &str, ty: &Type, span: Span) -> SpannedExpr {
        let receiver = self.fresh("handoff");
        // Analysis-only consuming receiver: actual frame construction is
        // checked in the same context. No destruction or helper call is emitted
        // by this model, and the original initializer is still fully checked.
        self.drivers.push((
            span,
            format!(
                "(#fn {receiver} ((value {})) () (#forget value) (#return ()))",
                crate::type_source(ty)
            ),
        ));
        list(
            vec![
                atom("#call", span),
                atom(&receiver, span),
                list(
                    vec![list(vec![atom("value", span), atom(name, span)], span)],
                    span,
                ),
            ],
            span,
        )
    }

    fn await_expression(
        &mut self,
        node: &SpannedExpr,
        path: &mut Vec<usize>,
    ) -> Result<SpannedExpr, Error> {
        let c = &node.children;
        if !matches!(c.len(), 6 | 7) {
            return Err(self.fail(
                node,
                "#await requires a concrete child/poll protocol and child value",
            ));
        }
        let offset = usize::from(c.len() == 7);
        let child_type = self.ty(&c[1 + offset])?;
        let pending = symbol(&c[2 + offset]).ok_or_else(|| {
            self.fail(
                &c[2 + offset],
                "#await Pending constructor must be an identifier",
            )
        })?;
        let ready = symbol(&c[3 + offset]).ok_or_else(|| {
            self.fail(
                &c[3 + offset],
                "#await Ready constructor must be an identifier",
            )
        })?;
        let poll_name = symbol(&c[4 + offset]).ok_or_else(|| {
            self.fail(&c[4 + offset], "#await poll function must be an identifier")
        })?;
        let poll = self
            .base
            .items
            .iter()
            .find_map(|item| match item {
                Item::Function(function) if function.name == poll_name => Some(function),
                _ => None,
            })
            .or_else(|| {
                self.interfaces
                    .and_then(|interfaces| interfaces.function(poll_name))
            })
            .ok_or_else(|| {
                self.fail(
                    &c[4 + offset],
                    format!("unknown #await poll function '{poll_name}'"),
                )
            })?;
        let result_owner = self.resolved(&poll.return_type, &c[4 + offset])?;
        let variants = self
            .base
            .items
            .iter()
            .find_map(|item| match item {
                Item::Enum { name, variants, .. } if result_owner == Type::Named(name.clone()) => {
                    Some(variants)
                }
                _ => None,
            })
            .or_else(|| {
                self.interfaces
                    .and_then(|interfaces| interfaces.enum_variants(&result_owner))
            })
            .ok_or_else(|| {
                self.fail(
                    &c[4 + offset],
                    "#await poll function must return the declared Pending/Ready enum",
                )
            })?;
        let ready_fields = variants
            .iter()
            .find(|variant| variant.name == ready)
            .ok_or_else(|| {
                self.fail(
                    &c[3 + offset],
                    "#await Ready constructor is not in the poll result enum",
                )
            })?;
        let pending_fields = variants
            .iter()
            .find(|variant| variant.name == pending)
            .ok_or_else(|| {
                self.fail(
                    &c[2 + offset],
                    "#await Pending constructor is not in the poll result enum",
                )
            })?;
        if ready_fields.fields.len() != 1 || pending_fields.fields.len() != 1 {
            return Err(self.fail(
                node,
                "#await Pending and Ready constructors must each contain one value",
            ));
        }
        let result_type = if offset == 1 {
            self.ty(&c[1])?
        } else {
            ready_fields.fields[0].clone()
        };
        if self.resolved(&result_type, &c[1])?
            != self.resolved(&ready_fields.fields[0], &c[3 + offset])?
        {
            return Err(self.fail(&c[1], "#await result type does not match its Ready payload"));
        }
        if self.resolved(&child_type, &c[1 + offset])?
            != self.resolved(&pending_fields.fields[0], &c[2 + offset])?
        {
            return Err(self.fail(
                &c[1 + offset],
                "#await child type does not match its Pending payload",
            ));
        }
        let poll_return = crate::type_source(&poll.return_type);
        let unsafe_call = poll.unsafe_call || poll.external;
        path.push(c.len() - 1);
        let child = self.expression(c.last().unwrap(), path, false)?;
        path.pop();
        let driver = self.fresh("await");
        let polled = self.fresh("polled");
        let next = self.fresh("next");
        let value = self.fresh("value");
        let call_head = if unsafe_call { "#unsafe-call" } else { "#call" };
        let call = format!("({call_head} {poll_name} (: task task : waker waker))");
        let call = if unsafe_call {
            format!("(#unsafe {call})")
        } else {
            call
        };
        let declaration = if unsafe_call { "#unsafe-fn" } else { "#fn" };
        self.drivers.push((
            node.span,
            format!(
                "({declaration} {driver} ((#mut task {}) (waker (#ref {}))) {}\n\
              (#loop\n\
                (#let {polled} {poll_return} {call})\n\
                (#match {polled}\n\
                  (#case ({pending} {next}) (#block (#set task {next}) ()))\n\
                  (#case ({ready} {value}) (#block (#return {value}) (#unreachable)))))\n\
              (#return (#unreachable)))",
                crate::type_source(&child_type),
                crate::type_source(&self.waker),
                crate::type_source(&result_type),
            ),
        ));
        self.sites.push(AwaitSite {
            source_path: path.clone(),
            span: node.span,
            keyword_span: c[0].span,
            child_span: c.last().unwrap().span,
            driver: driver.clone(),
            child_type,
            result_type,
            poll: poll_name.into(),
            pending: pending.into(),
            ready: ready.into(),
        });
        Ok(list(
            vec![
                atom(call_head, c[0].span),
                atom(&driver, c[0].span),
                list(
                    vec![
                        list(vec![atom("task", c[0].span), child], node.span),
                        list(
                            vec![
                                atom("waker", c[0].span),
                                atom(&self.waker_binding, c[0].span),
                            ],
                            node.span,
                        ),
                    ],
                    node.span,
                ),
            ],
            node.span,
        ))
    }
}

/// Lower an original #fn, independently of any particular async body shape.
pub(crate) fn lower(source: &SpannedExpr, waker: Type, base: &Program) -> Result<Lowered, Error> {
    lower_with_frame(source, waker, base, None)
}

fn lower_with_frame(
    source: &SpannedExpr,
    waker: Type,
    base: &Program,
    frame: Option<&str>,
) -> Result<Lowered, Error> {
    lower_source(source, waker, base, frame, None)
}

/// Type/evaluation planning before physical frame layout. Deferred interfaces
/// supply signatures only; this is not a pin-promotion or ownership proof.
pub(crate) fn lower_in_registry(
    source: &SpannedExpr,
    waker: Type,
    base: &Program,
    interfaces: &crate::generator::async_interfaces::Registry,
) -> Result<Lowered, Error> {
    lower_source(source, waker, base, None, Some(interfaces))
}

fn lower_source(
    source: &SpannedExpr,
    waker: Type,
    base: &Program,
    frame: Option<&str>,
    interfaces: Option<&crate::generator::async_interfaces::Registry>,
) -> Result<Lowered, Error> {
    if head(source) != "fn" || source.children.len() < 5 {
        return Err(Error {
            message: "async source analysis needs the original #fn source tree".into(),
            span: source.span,
        });
    }
    let globals = base
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Let { name, .. } | Item::Static { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let variants = base
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { variants, .. } => Some(variants),
            _ => None,
        })
        .flatten()
        .map(|variant| variant.name.clone())
        .collect::<HashSet<_>>();
    if let Some((name, _)) = crate::function_shadowing_in_scope(&source.expr, &globals, &variants)
        .map_err(|message| Error {
        message,
        span: source.span,
    })? {
        return Err(Error {
            message: format!(
                "binding '{name}' shadows an existing binding; shadowing is not allowed"
            ),
            span: crate::function_shadowing_span(source, &name, globals.contains(&name))
                .unwrap_or(source.span),
        });
    }
    let source_name = symbol(&source.children[1])
        .ok_or_else(|| Error {
            message: "async source function name must be an identifier".into(),
            span: source.children[1].span,
        })?
        .to_owned();
    let mut used = base
        .items
        .iter()
        .flat_map(crate::item_declared_names)
        .collect::<HashSet<_>>();
    if let Some(interfaces) = interfaces {
        used.extend(interfaces.generated_names.keys().cloned());
    }
    names(&source.expr, &mut used);
    let aliases = base
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. } => Some((name.clone(), target.clone())),
            _ => None,
        })
        .collect();
    let mut builder = Builder {
        base,
        interfaces,
        aliases,
        used,
        prefix: format!("lim.async.source.{source_name}"),
        next: 0,
        waker,
        waker_binding: String::new(),
        sites: Vec::new(),
        drivers: Vec::new(),
        frame: None,
    };
    let body_name = builder.fresh("body");
    builder.waker_binding = builder.fresh("waker");
    let mut function = source.clone();
    function.children[1].expr = Expr::Symbol(body_name.clone());
    let mut waker_type = crate::parse(&format!("(#ref {})", crate::type_source(&builder.waker)))
        .map_err(|message| builder.fail(source, message))?
        .remove(0);
    // This implicit poll-context parameter has no original identifier span.
    fn anchor(node: &mut SpannedExpr, span: Span) {
        node.span = span;
        for child in &mut node.children {
            anchor(child, span);
        }
    }
    anchor(&mut waker_type, source.children[2].span);
    function.children[2].children.push(list(
        vec![
            atom(&builder.waker_binding, source.children[2].span),
            waker_type,
        ],
        source.children[2].span,
    ));
    if let Some(frame) = frame {
        let owners = base
            .items
            .iter()
            .find_map(|item| match item {
                Item::Struct { name, fields, .. } if name == frame => Some(
                    fields
                        .iter()
                        .filter(|field| field.name != "state")
                        .map(|field| (field.name.clone(), field.ty.clone()))
                        .collect::<HashMap<_, _>>(),
                ),
                _ => None,
            })
            .ok_or_else(|| {
                builder.fail(source, "pinned async source has no declared frame storage")
            })?;
        if !owners.is_empty() {
            let parameter = builder.fresh("frame");
            let mut frame_type = crate::parse(&format!("(#pin-ref-mut {frame})"))
                .map_err(|message| builder.fail(source, message))?
                .remove(0);
            anchor(&mut frame_type, source.children[2].span);
            function.children[2].children.push(list(
                vec![atom(&parameter, source.children[2].span), frame_type],
                source.children[2].span,
            ));
            builder.frame = Some((parameter, owners));
        }
    }
    rebuild(&mut function.children[2]);
    for (index, child) in function.children.iter_mut().enumerate().skip(4) {
        *child = builder.expression(child, &mut vec![index], true)?;
    }
    if let Some((_, owners)) = &builder.frame {
        let owners = owners.clone();
        let mut transfers = Vec::new();
        for parameter in &source.children[2].children {
            let offset = usize::from(head(parameter) == "mut");
            if let Some(name_node) = parameter.children.get(offset) {
                if let Some(name) = symbol(name_node) {
                    if let Some(ty) = owners.get(name) {
                        transfers.push(builder.handoff(name, ty, name_node.span));
                    }
                }
            }
        }
        function.children.splice(4..4, transfers);
    }
    rebuild(&mut function);
    Ok(Lowered {
        function,
        source_name,
        body_name,
        waker_binding: builder.waker_binding,
        awaits: builder.sites,
        drivers: builder.drivers,
    })
}

impl Lowered {
    /// Attach an analysis model to a program context. These functions are not
    /// imports or frame emission: callers use this separate program for the
    /// ordinary checked-body boundary and then query its immutable facts.
    pub fn program(&self, base: &Program) -> Result<Program, crate::source_error::SourceError> {
        let mut program = base.clone();
        program.generator_validation = None;
        self.append(&mut program)?;
        Ok(program)
    }

    pub fn append(&self, program: &mut Program) -> Result<(), crate::source_error::SourceError> {
        self.append_in_context(program, None)
    }

    pub(crate) fn append_with_interfaces(
        &self,
        program: &mut Program,
        interfaces: &crate::generator::async_interfaces::Registry,
    ) -> Result<(), crate::source_error::SourceError> {
        self.append_in_context(program, Some(interfaces))
    }

    fn append_in_context(
        &self,
        program: &mut Program,
        interfaces: Option<&crate::generator::async_interfaces::Registry>,
    ) -> Result<(), crate::source_error::SourceError> {
        let original_count = program.items.len();
        fn add(
            program: &mut Program,
            mut source: SpannedExpr,
        ) -> Result<(), crate::source_error::SourceError> {
            crate::normalize_match_case_forms(&mut source).map_err(|(message, span)| {
                crate::source_error::SourceError::new(message, crate::DiagnosticCode::Parse)
                    .at(span)
            })?;
            crate::collect_function_statement_spans(
                &source,
                &mut program.statement_spans,
                &mut program.statement_expressions,
            );
            let mut expression = crate::normalize_keywords(source.expr.clone());
            crate::normalize_match_cases_expr(&mut expression);
            let item = crate::parse_item(&expression).map_err(|message| {
                crate::source_error::SourceError::new(message, crate::DiagnosticCode::Parse)
                    .at(source.span)
            })?;
            for name in crate::item_declared_names(&item) {
                program.declaration_spans.insert(name.clone(), source.span);
                program
                    .declaration_expressions
                    .insert(name.clone(), source.clone());
                program
                    .declaration_occurrences
                    .insert(name, vec![source.clone()]);
            }
            program.items.push(item);
            Ok(())
        }
        for (origin, text) in &self.drivers {
            let source_id = program.source_files.len() as u32;
            let mut source = crate::parse(text)?.remove(0);
            crate::set_source_id(&mut source, source_id);
            program.source_files.push(crate::SourceFile {
                file_scope: None,
                import_prefix: String::new(),
                path: format!("<async analysis at {}:{}>", origin.line, origin.column).into(),
                source: text.clone(),
            });
            program
                .generated_source_invocations
                .insert(source_id, *origin);
            add(program, source)?;
        }
        add(program, self.function.clone())?;
        // Runtime items already have positional calls and lowered struct
        // literals. Normalize only new witnesses, using signature-only context;
        // reapplying the source syntax gate would reject valid lowered items.
        let mut context = program.items[..original_count]
            .iter()
            .filter_map(|item| match item {
                Item::Function(function) => Some(Item::Function(crate::Function {
                    name: function.name.clone(),
                    type_parameters: function.type_parameters.clone(),
                    parameters: function.parameters.clone(),
                    return_type: function.return_type.clone(),
                    body: Vec::new(),
                    unsafe_call: function.unsafe_call,
                    external: function.external,
                    calling_convention: function.calling_convention,
                })),
                Item::Struct { .. }
                | Item::ThreadTask { .. }
                | Item::Enum { .. }
                | Item::TypeAlias { .. } => Some(item.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        if let Some(interfaces) = interfaces {
            // This temporary list orders named operands. It is not checked
            // executable code, and never enters program.items or emission.
            context.extend(interfaces.signature_context());
            for (name, variants) in &interfaces.protocols {
                if !context
                    .iter()
                    .any(|item| matches!(item, Item::Enum { name: present, .. } if present == name))
                {
                    context.push(Item::Enum {
                        name: name.clone(),
                        representation: crate::Representation::Lim,
                        linear: false,
                        type_parameters: vec![],
                        variants: variants.clone(),
                    });
                }
            }
        }
        let context_count = context.len();
        context.extend(program.items.drain(original_count..));
        crate::let_else::normalize(
            &mut context,
            &mut program.statement_spans,
            &mut program.statement_expressions,
            &mut program.declaration_expressions,
            &mut program.declaration_occurrences,
            false,
        )
        .map_err(|error| error.attach(&program.source_files))?;
        crate::normalize_function_calls(
            &mut context,
            &program.statement_spans,
            &program.statement_expressions,
            &program.declaration_spans,
            &program.declaration_expressions,
            &program.source_files,
        )?;
        crate::normalize_aggregate_literals(
            &mut context,
            &program.statement_spans,
            &program.statement_expressions,
            &program.declaration_spans,
            &program.declaration_expressions,
            &program.source_files,
        )?;
        program.items.extend(context.drain(context_count..));
        Ok(())
    }

    /// Driver identity, not subtree text or a possibly shared source span,
    /// uniquely locates each await in the ordinary checked body.
    pub fn map(
        &self,
        body: &Body,
        flow: &FlowGraph,
        declarations: &crate::typed_ir::Declarations,
    ) -> Result<Vec<CheckedAwait>, Error> {
        self.awaits
            .iter()
            .map(|site| {
                let callee = declarations
                    .function_id(&site.driver)
                    .ok_or_else(|| Error {
                        message: "async source driver declaration was lost".into(),
                        span: site.keyword_span,
                    })?;
                let mut found = flow.nodes.iter().enumerate().filter_map(|(index, event)| {
                    let FlowAction::Evaluate(value) = event.action else {
                        return None;
                    };
                    let NodeKind::Form {
                        callee: Some(actual),
                        children,
                        ..
                    } = &body.nodes[value.0].kind
                    else {
                        return None;
                    };
                    (*actual == callee).then_some((FlowNodeId(index), value, children))
                });
                let Some((call, value, children)) = found.next() else {
                    return Err(Error {
                        message: "async source await event was lost".into(),
                        span: site.keyword_span,
                    });
                };
                if found.next().is_some() || children.len() != 3 {
                    return Err(Error {
                        message: "async source await event is ambiguous".into(),
                        span: site.keyword_span,
                    });
                }
                let child_value = children[1];
                let Some(child_type) = body.nodes[child_value.0].ty.clone() else {
                    return Err(Error {
                        message: "async source child has no checked type".into(),
                        span: site.child_span,
                    });
                };
                let Some(result_type) = body.nodes[value.0].ty.clone() else {
                    return Err(Error {
                        message: "async source await has no checked result type".into(),
                        span: site.keyword_span,
                    });
                };
                Ok(CheckedAwait {
                    source_path: site.source_path.clone(),
                    span: site.span,
                    child_value,
                    result_value: value,
                    call,
                    child_type,
                    result_type,
                })
            })
            .collect()
    }

    /// Query a fully validated source model at its original suspension events.
    /// This is a storage plan, not permission to move pinned/address-held slots
    /// or load partially initialized aggregates into a generated frame.
    pub fn suspensions(
        &self,
        checked: &mut crate::CheckedProgram<'_>,
    ) -> Result<Vec<Suspension>, Error> {
        let (mut facts, types) = checked
            .suspension_storage_facts(&HashSet::from([self.body_name.clone()]))
            .map_err(|error| Error {
                message: format!("async suspension storage effects are unresolved: {error:?}"),
                span: self.function.span,
            })?;
        let facts = facts.remove(&self.body_name).ok_or_else(|| Error {
            message: "async source body has no suspension storage facts".into(),
            span: self.function.span,
        })?;
        let declarations = checked.declarations();
        let body = &declarations.bodies[&self.body_name];
        let sites = self.map(body, &facts.flow, declarations)?;
        let values = crate::generator::async_values::plan_with_types(
            body,
            &facts.flow,
            &sites
                .iter()
                .map(|site| site.result_value)
                .collect::<Vec<_>>(),
            &types,
        )
        .map_err(|error| Error {
            span: error
                .value
                .and_then(|value| body.nodes[value.0].span)
                .unwrap_or(self.function.span),
            message: error.message,
        })?;
        let storage =
            crate::generator::async_storage::Analysis::new(body, &facts, &types, declarations);
        sites
            .into_iter()
            .map(|site| {
                let snapshot = match values.get(&site.result_value) {
                    None => None,
                    Some(values) => {
                        let NodeKind::Form { children, .. } = &body.nodes[site.result_value.0].kind
                        else {
                            unreachable!()
                        };
                        // The polling context is supplied anew on every poll. It
                        // is not an original source operand or stored task capture.
                        let waker = children[2];
                        let values = values
                            .iter()
                            .copied()
                            .filter(|value| *value != waker)
                            .collect::<Vec<_>>();
                        let mut snapshot = storage
                            .before_with_values(site.call, &values)
                            .ok_or_else(|| Error {
                                message: "reachable await has no checked storage snapshot".into(),
                                span: site.span,
                            })?;
                        snapshot.slots.retain(|slot| {
                            body.bindings[slot.binding.0].name != self.waker_binding
                        });
                        Some(snapshot)
                    }
                };
                Ok(Suspension {
                    site,
                    storage: snapshot,
                })
            })
            .collect()
    }
}

/// Emit ordinary validation witnesses as part of generator expansion.
pub(crate) fn attach_validation(program: &mut Program, sources: &[Source]) {
    if !sources.is_empty() {
        program.generator_validation = Some(validation_program(program, sources));
    }
}

fn validation_program(
    program: &Program,
    sources: &[Source],
) -> Result<std::sync::Arc<Program>, crate::typecheck::AnalysisError> {
    let mut analysis = program.clone();
    analysis.generator_validation = None;
    let runtime_item_count = analysis.items.len();
    for source in sources {
        let model = lower_with_frame(
            &source.function,
            source.waker.clone(),
            &analysis,
            source.pinned_frame.as_deref(),
        )
        .map_err(|error| {
            (
                error.message,
                crate::DiagnosticCode::Type,
                Some(error.span),
                Vec::new(),
            )
        })?;
        model
            .append(&mut analysis)
            .map_err(|error| (error.message, error.code, error.span, Vec::new()))?;
    }
    analysis.items.drain(..runtime_item_count);
    let names = analysis
        .items
        .iter()
        .flat_map(crate::item_declared_names)
        .collect::<HashSet<_>>();
    analysis
        .statement_spans
        .retain(|(name, _), _| names.contains(name));
    analysis
        .statement_expressions
        .retain(|(name, _), _| names.contains(name));
    analysis
        .declaration_spans
        .retain(|name, _| names.contains(name));
    analysis
        .declaration_expressions
        .retain(|name, _| names.contains(name));
    analysis
        .declaration_occurrences
        .retain(|name, _| names.contains(name));
    Ok(std::sync::Arc::new(analysis))
}

#[cfg(test)]
mod tests {
    use super::*;

    const CONTEXT: &str = "
      (#enum Child (#linear) ((Child.Waiting #u64)))
      (#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready #u64)))
      (#fn step-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task
          (#case (Child.Waiting count)
            (#if (#u64::eq count 0u64) (ChildPoll.Ready 42u64)
              (ChildPoll.Pending (Child.Waiting (#u64::sub-wrap count 1u64))))))))";

    fn prepare(context: &str, source: &str) -> (Program, SpannedExpr, Lowered) {
        let text = format!("{context}\n{source}");
        let original = crate::parse(&text).unwrap().pop().unwrap();
        let mut base = crate::parse_program(context).unwrap();
        base.source = Some(text.clone());
        base.source_files[0].source = text;
        let lowered = lower(&original, Type::U64, &base).unwrap();
        (base, original, lowered)
    }

    // Flow IDs are arena allocation order, not execution order. Assert that
    // the later event is reachable, but not before the earlier event executes.
    fn assert_before(flow: &FlowGraph, earlier: FlowNodeId, later: FlowNodeId) {
        fn reachable(
            flow: &FlowGraph,
            start: FlowNodeId,
            stop: Option<FlowNodeId>,
        ) -> HashSet<FlowNodeId> {
            let mut found = HashSet::new();
            let mut pending = vec![start];
            while let Some(node) = pending.pop() {
                if Some(node) == stop || !found.insert(node) {
                    continue;
                }
                pending.extend(flow.nodes[node.0].successors.iter().copied());
            }
            found
        }
        assert!(reachable(flow, earlier, None).contains(&later));
        assert!(!reachable(flow, flow.entry, Some(earlier)).contains(&later));
    }

    #[test]
    fn original_body_maps_to_checked_call_with_explicit_types_and_spans() {
        let (base, original, lowered) = prepare(
            CONTEXT,
            "(#fn work ((seed #u64)) #u64
               (#let child Child (Child.Waiting seed))
               (#let result #u64 (#await #u64 Child ChildPoll.Pending ChildPoll.Ready step-poll child))
               (#return result))",
        );
        let program = lowered.program(&base).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies[&lowered.body_name];
        let flow = &declarations.flows[&lowered.body_name];
        let sites = lowered.map(body, flow, declarations).unwrap();
        assert_eq!(sites.len(), 1);
        let site = &sites[0];
        assert_eq!(site.child_type, Type::Named("Child".into()));
        assert_eq!(site.result_type, Type::U64);
        assert_eq!(body.nodes[site.result_value.0].span, Some(site.span));
        assert_eq!(site.span, original.children[5].children[3].span);
        assert_eq!(site.source_path, [5, 3]);
        assert_eq!(body.parameter_count, 2);
        assert_eq!(body.bindings[0].name, "seed");
        assert_eq!(
            body.bindings[0].span,
            Some(original.children[2].children[0].children[0].span)
        );
    }

    #[test]
    fn nested_await_child_is_evaluated_before_its_outer_driver() {
        let context = format!(
            "{CONTEXT}
          (#enum BuilderPoll () ((BuilderPoll.BuilderPending Child) (BuilderPoll.BuilderReady Child)))
          (#fn build-poll ((task Child) (waker (#ref #u64))) BuilderPoll
            (#return (BuilderPoll.BuilderReady task)))"
        );
        let (base, _, lowered) = prepare(
            &context,
            "(#fn work () #u64
               (#return (#await Child ChildPoll.Pending ChildPoll.Ready step-poll
                 (#await Child BuilderPoll.BuilderPending BuilderPoll.BuilderReady build-poll (Child.Waiting 1u64)))))",
        );
        let program = lowered.program(&base).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let d = checked.declarations();
        let body = &d.bodies[&lowered.body_name];
        let flow = &d.flows[&lowered.body_name];
        let sites = lowered.map(body, flow, d).unwrap();
        assert_eq!(sites.len(), 2);
        assert_eq!(sites[0].result_type, Type::Named("Child".into()));
        assert_eq!(sites[1].child_value, sites[0].result_value);
        assert_before(flow, sites[0].call, sites[1].call);
    }

    #[test]
    fn normal_named_argument_order_is_preserved_across_awaits() {
        let context = format!(
            "{CONTEXT}
          (#fn combine ((first #u64) (second #u64)) #u64 (#return (#u64::add-wrap first second)))"
        );
        let (base, _, lowered) = prepare(
            &context,
            "(#fn work () #u64 (#return (#call combine
               (: second (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 2u64))
                : first (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64))))))",
        );
        let program = lowered.program(&base).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let d = checked.declarations();
        let sites = lowered
            .map(
                &d.bodies[&lowered.body_name],
                &d.flows[&lowered.body_name],
                d,
            )
            .unwrap();
        // Sites retain original written paths, but ordinary declaration order
        // executes first before second, exactly as non-async named calls do.
        assert_before(&d.flows[&lowered.body_name], sites[1].call, sites[0].call);
    }

    #[test]
    fn ordinary_owned_exit_check_rejects_missing_cleanup_at_original_binding() {
        let context = format!("{CONTEXT} (#struct Token (#linear) ((value #u64))) ");
        let (base, _, lowered) = prepare(
            &context,
            "(#fn work ((token Token)) #u64
               (#let result #u64 (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))
               (#return result))",
        );
        let program = lowered.program(&base).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert_eq!(error.1, crate::DiagnosticCode::Linear);
        assert!(error.0.contains("token"), "{error:?}");
        let span = error.2.unwrap();
        assert_eq!(span.source_id, 0);
        assert_eq!(&base.source_files[0].source[span.start..span.end], "token");
    }

    #[test]
    fn child_result_reference_keeps_original_source_borrow() {
        let context = "
          (#enum Child (#linear) ((Child.Holding (#ref #u64))))
          (#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready (#ref #u64))))
          (#fn step-poll ((task Child) (waker (#ref #u64))) ChildPoll
            (#return (#match task (#case (Child.Holding view) (ChildPoll.Ready view)))))";
        let (base, _, lowered) = prepare(
            context,
            "(#fn work ((view (#ref #u64))) (#ref #u64)
               (#return (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Holding view))))",
        );
        let program = lowered.program(&base).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();

        let (base, _, lowered) = prepare(
            context,
            "(#fn work () (#ref #u64)
               (#let owner #u64 42u64)
               (#return (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Holding (#borrow owner)))))",
        );
        let program = lowered.program(&base).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert_eq!(error.1, crate::DiagnosticCode::Borrow);
        assert!(
            error.0.contains("local") || error.0.contains("outlive"),
            "{error:?}"
        );
        let span = error.2.unwrap();
        assert_eq!(span.source_id, 0);
        assert!(base.source_files[0].source[span.start..span.end].contains("#await"));
    }

    #[test]
    fn arbitrary_original_transfers_remain_ordinary_control_flow() {
        let (base, _, lowered) = prepare(
            CONTEXT,
            "(#fn work ((choose #bool)) #u64
               (#let-mut total #u64 0u64)
               (#label outer (#loop
                 (#match choose
                   (#case true (#block
                     (#for-range (index #usize) 0usize 3usize
                       (#set total (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))
                       (#if (#usize::eq index 1usize) (#block (#break-to outer) (#unreachable)) ()))
                     (#continue-to outer)))
                   (#case false (#block (#break-to outer) (#unreachable))))))
               (#return total))",
        );
        let program = lowered.program(&base).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let d = checked.declarations();
        let sites = lowered
            .map(
                &d.bodies[&lowered.body_name],
                &d.flows[&lowered.body_name],
                d,
            )
            .unwrap();
        assert_eq!(sites.len(), 1);
        let flow = &d.flows[&lowered.body_name];
        assert!(flow
            .nodes
            .iter()
            .any(|node| matches!(node.action, FlowAction::Continue)));
        assert!(flow
            .nodes
            .iter()
            .any(|node| matches!(node.action, FlowAction::Break { .. })));
    }

    #[test]
    fn explicit_contract_errors_point_to_the_original_protocol_operand() {
        for (awaited, offending) in [
            (
                "(#await #u32 Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64))",
                "#u32",
            ),
            (
                "(#await Other ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64))",
                "Other",
            ),
            (
                "(#await Child ChildPoll.Pending missing step-poll (Child.Waiting 1u64))",
                "missing",
            ),
        ] {
            let source = format!("{CONTEXT}\n(#fn work () #u64 (#return {awaited}))");
            let base = crate::parse_program(CONTEXT).unwrap();
            let original = crate::parse(&source).unwrap().pop().unwrap();
            let error = lower(&original, Type::U64, &base).err().unwrap();
            assert_eq!(&source[error.span.start..error.span.end], offending);
        }
    }

    #[test]
    fn source_binding_type_mismatch_uses_the_original_await_span() {
        let (base, _, lowered) = prepare(
            CONTEXT,
            "(#fn work () #u32
               (#let wrong #u32 (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))
               (#return wrong))",
        );
        let program = lowered.program(&base).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert_eq!(error.1, crate::DiagnosticCode::Type);
        let span = error.2.unwrap();
        assert_eq!(span.source_id, 0);
        assert_eq!(
            &base.source_files[0].source[span.start..span.end],
            "(#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64))"
        );
    }

    #[test]
    fn driver_identity_disambiguates_collapsed_macro_source_spans() {
        let (base, mut original, _) = prepare(
            CONTEXT,
            "(#fn work () #u64
               (#let first #u64 (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))
               (#return (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting first))))",
        );
        let shared = original.children[4].children[3].span;
        original.children[5].children[1].span = shared;
        let lowered = lower(&original, Type::U64, &base).unwrap();
        let program = lowered.program(&base).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let d = checked.declarations();
        let sites = lowered
            .map(
                &d.bodies[&lowered.body_name],
                &d.flows[&lowered.body_name],
                d,
            )
            .unwrap();
        assert_eq!(sites.len(), 2);
        assert_eq!(sites[0].span, sites[1].span);
        assert_ne!(sites[0].source_path, sites[1].source_path);
        assert_ne!(sites[0].call, sites[1].call);
    }

    #[test]
    fn compiled_async_retains_original_tree_without_emitting_analysis_helpers() {
        let source = format!(
            "{CONTEXT}
          (#generate #async-fn (: protocol work-await : waker #u64 : function (#fn work () #u64
              (#return (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64))))))"
        );
        let program = crate::parse_program(&source).unwrap();
        let witnesses = program
            .generator_validation
            .as_ref()
            .unwrap()
            .as_ref()
            .unwrap();
        assert!(!witnesses.items.is_empty());
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        assert!(!checked
            .dump_typed_ir()
            .contains("function lim.async.source."));
        let assembly = checked
            .generate_assembly(crate::TargetDescription::host().unwrap())
            .unwrap();
        assert!(!assembly.contains("lim.async.source."));
    }

    #[test]
    fn original_type_error_cannot_be_omitted_by_an_async_rewrite() {
        let (mut base, original, _) = prepare(
            CONTEXT,
            "(#fn work () #u64
              (#let wrong #u32 (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))
              (#return 0u64))",
        );
        // Supply a valid runtime context: source checking must still reject the
        // original body, even if a future frame rewrite omits its bad binding.
        attach_validation(
            &mut base,
            &[Source {
                function: original,
                waker: Type::U64,
                pinned_frame: None,
                generated_poll: None,
                frame_access: Vec::new(),
            }],
        );
        let error = crate::CheckedProgram::validate_with_span(&base)
            .err()
            .unwrap();
        assert_eq!(error.1, crate::DiagnosticCode::Type);
        let span = error.2.unwrap();
        assert_eq!(
            &base.source_files[0].source[span.start..span.end],
            "(#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64))"
        );
    }

    #[test]
    fn unsafe_child_poll_requires_original_unsafe_scope() {
        let context = CONTEXT.replace("(#fn step-poll", "(#unsafe-fn step-poll");
        for (expression, allowed) in [
            (
                "(#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 0u64))",
                false,
            ),
            (
                "(#unsafe (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 0u64)))",
                true,
            ),
        ] {
            let (base, _, lowered) = prepare(
                &context,
                &format!("(#fn work () #u64 (#return {expression}))"),
            );
            assert!(crate::expression_source(&lowered.function.expr)
                .unwrap()
                .contains(&format!("(#unsafe-call {} ", lowered.awaits[0].driver)));
            assert!(lowered
                .drivers
                .iter()
                .any(|(_, source)| source.contains("(#unsafe (#unsafe-call step-poll ")));
            let program = lowered.program(&base).unwrap();
            let result = crate::CheckedProgram::validate_with_span(&program);
            if allowed {
                assert!(result.is_ok(), "{:?}", result.err());
            } else {
                let error = result.err().unwrap();
                assert!(error.0.contains("unsafe"), "{error:?}");
                assert_eq!(error.2.unwrap().source_id, 0);
            }
        }
    }

    #[test]
    fn original_suspension_retains_evaluated_values_not_replayed_operands() {
        let (base, _, lowered) = prepare(
            CONTEXT,
            "(#fn work () #u64 (#return (#u64::add-wrap
              (#u64::add-wrap 20u64 1u64)
              (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))))",
        );
        let program = lowered.program(&base).unwrap();
        let mut checked = crate::CheckedProgram::validate(&program).unwrap();
        let plans = lowered.suspensions(&mut checked).unwrap();
        let storage = plans[0].storage.as_ref().unwrap();
        assert_eq!(
            storage.values.len(),
            2,
            "completed left operand and child only"
        );
        assert_eq!(storage.values[0].ty, Type::U64);
        assert_eq!(storage.values[1].ty, Type::Named("Child".into()));
        assert_eq!(storage.values[1].value, plans[0].site.child_value);
        let body = &checked.declarations().bodies[&lowered.body_name];
        let span = body.nodes[storage.values[0].value.0].span.unwrap();
        assert_eq!(
            &base.source_files[0].source[span.start..span.end],
            "(#u64::add-wrap 20u64 1u64)"
        );
    }

    #[test]
    fn unnamed_reference_bearing_operand_retains_its_actual_owner() {
        let context = format!(
            "{CONTEXT}
          (#struct Held (#linear) ((view (#ref #u64))))
          (#fn make-held ((view (#ref #u64))) Held
            (#return (#struct-literal Held ((view view)))))
          (#fn combine ((held Held) (value #u64)) #u64
            (#let view (#ref #u64) (#get held view))
            (#forget held) (#return (#u64::add-wrap (#deref view) value)))"
        );
        let (base, _, lowered) = prepare(
            &context,
            "(#fn work () #u64
              (#let owner #u64 40u64)
              (#return (#call combine
                (: value (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64))
                 : held (#call make-held (: view (#borrow owner)))))))",
        );
        let program = lowered.program(&base).unwrap();
        let mut checked = crate::CheckedProgram::validate(&program).unwrap();
        let plans = lowered.suspensions(&mut checked).unwrap();
        let storage = plans[0].storage.as_ref().unwrap();
        let body = &checked.declarations().bodies[&lowered.body_name];
        let owner = storage
            .slots
            .iter()
            .find(|slot| body.bindings[slot.binding.0].name == "owner")
            .unwrap();
        assert!(owner.address_needed);
        assert!(owner.lifetime_needed);
        let held = storage
            .values
            .iter()
            .find(|slot| slot.ty == Type::Named("Held".into()))
            .unwrap();
        assert!(held
            .loans
            .iter()
            .any(|loan| loan.referent_place().root
                == crate::typed_body::PlaceRoot::Local(owner.binding)));
    }

    #[test]
    fn transferred_child_is_a_value_not_a_second_owned_local() {
        let (base, _, lowered) = prepare(
            CONTEXT,
            "(#fn work () #u64
              (#let child Child (Child.Waiting 1u64))
              (#let result #u64 (#await Child ChildPoll.Pending ChildPoll.Ready step-poll child))
              (#return result))",
        );
        let program = lowered.program(&base).unwrap();
        let mut checked = crate::CheckedProgram::validate(&program).unwrap();
        let plans = lowered.suspensions(&mut checked).unwrap();
        let storage = plans[0].storage.as_ref().unwrap();
        let body = &checked.declarations().bodies[&lowered.body_name];
        let child = storage
            .slots
            .iter()
            .find(|slot| body.bindings[slot.binding.0].name == "child")
            .unwrap();
        assert!(!child.cleanup_needed());
        assert_eq!(storage.values.len(), 1);
        assert_eq!(storage.values[0].value, plans[0].site.child_value);
    }

    #[test]
    fn unreachable_await_cannot_manufacture_a_live_storage_snapshot() {
        let (base, _, lowered) = prepare(
            CONTEXT,
            "(#fn work () #u64 (#return 1u64)
              (#let result #u64 (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))
              (#return result))",
        );
        let program = lowered.program(&base).unwrap();
        let mut checked = crate::CheckedProgram::validate(&program).unwrap();
        let plans = lowered.suspensions(&mut checked).unwrap();
        assert_eq!(plans.len(), 1);
        assert!(plans[0].storage.is_none());
    }

    #[test]
    fn promoted_linear_owner_is_transferred_once_not_duplicated_on_the_stack() {
        let mut config = crate::CompileConfig::default();
        config.set("async-lowering", "graph");
        let parse = |source: &str| {
            crate::parse_program_from_path_with_config(
                source,
                std::path::Path::new("graph-linear-owner.lim"),
                &config,
            )
        };
        let source = include_str!("../../examples/async_fn_local_self_reference.lim").replace(
            "(#struct LocalOwner () ((payload LocalPayload)))",
            "(#struct LocalOwner (#linear) ((payload LocalPayload))) ",
        ).replace("(#return (#u64::add-wrap (#deref view) result))", "(#let answer #u64 (#u64::add-wrap (#deref view) result))\n    (#forget view) (#forget owner) (#return answer)");
        let program = parse(&source).unwrap();
        let mut runtime = program.clone();
        runtime.generator_validation = None;
        crate::CheckedProgram::validate(&runtime).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
        let missing = source.replace("(#let view (#pin-ref #u64)",
            "(#let unrelated LocalOwner (#struct-literal LocalOwner ((payload (#struct-literal LocalPayload ((left 1u64) (right 2u64)))))))\n    (#let view (#pin-ref #u64)");
        let error = parse(&missing).unwrap_err();
        assert!(error.contains("unrelated"), "{error}");
    }

    #[test]
    fn reference_bearing_owners_retain_frame_and_external_borrows() {
        let mut config = crate::CompileConfig::default();
        config.set("async-lowering", "graph");
        let parse = |source: &str| {
            crate::parse_program_from_path_with_config(
                source,
                std::path::Path::new("graph-reference-owner.lim"),
                &config,
            )
        };
        let source = include_str!("../../examples/async_fn_local_self_reference.lim")
            .replace("(left #u64)", "(left (#ref #u64))")
            .replace("(#pin-ref #u64)", "(#pin-ref (#ref #u64))")
            .replace("(#deref view)", "(#deref (#deref view))");
        let external = source
            .replace("((seed #u64))", "((seed (#ref #u64)))")
            .replace(
                "(#let-mut frame",
                "(#let external-storage #u64 40u64)\n  (#let-mut frame",
            )
            .replace(": seed 40u64", ": seed (#borrow external-storage)");
        crate::CheckedProgram::validate(&parse(&external).unwrap()).unwrap();
        // On the graph route a value parameter occupies stationary frame
        // storage too; borrowing it is legal, unlike a block-local escape.
        let self_reference = source.replace("(left seed)", "(left (#borrow seed))");
        crate::CheckedProgram::validate(&parse(&self_reference).unwrap()).unwrap();
        for invalid in [external.replace(
            "(left seed)",
            "(left (#block (#let local #u64 40u64) (#borrow local)))",
        )] {
            let prepared = crate::prepare_program_syntax(
                &invalid,
                std::path::Path::new("."),
                None,
                &config,
                None,
            )
            .unwrap();
            let error = crate::expand_prepared_program(&prepared).err().unwrap();
            let message = error.message;
            let code = error.code;
            let span = error.span;
            // Staged referent contracts can reject unresolved stack-sourced
            // call inputs before the final borrow-escape diagnostic boundary.
            assert!(
                code == crate::DiagnosticCode::Borrow
                    || (code == crate::DiagnosticCode::Linear
                        && message.contains("referent entry contract")
                        && message.contains("unresolved call inputs")),
                "{message}"
            );
            assert!(span.is_some(), "{message}");
        }
    }

    #[test]
    fn polling_context_binding_is_not_a_frame_capture() {
        let (base, _, lowered) = prepare(
            CONTEXT,
            "(#fn work () #u64
              (#let first #u64 (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))
              (#return (#await Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting first))))",
        );
        let program = lowered.program(&base).unwrap();
        let mut checked = crate::CheckedProgram::validate(&program).unwrap();
        let plans = lowered.suspensions(&mut checked).unwrap();
        let body = &checked.declarations().bodies[&lowered.body_name];
        assert!(plans
            .iter()
            .all(|plan| plan.storage.as_ref().is_some_and(|storage| storage
                .slots
                .iter()
                .all(|slot| body.bindings[slot.binding.0].name != lowered.waker_binding))));
    }
}
