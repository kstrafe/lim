//! Declaration-only async planning context. No runtime bodies or frame layouts
//! Implementation detail of built-in code generation, not runtime semantics.
//! are manufactured here. Dense identities obtained during planning must be
//! converted back to names before entering another declaration arena.
use std::collections::{HashMap, HashSet};

use crate::{CallingConvention, EnumVariant, Expr, Function, Item, Parameter, Program, Span, Type};

pub(crate) use crate::generation_interfaces::{DeferredLayout, LayoutKind};

/// Publish only declaration metadata here; body checking remains authoritative.
/// Protocols can be referenced before the corresponding body is lowered, and
/// do not depend on either graph emission or legacy syntactic lowering.
pub(crate) fn protocol_declaration(invocation: &Expr) -> Result<Expr, String> {
    fn list<'a>(expr: &'a Expr, context: &str) -> Result<&'a [Expr], String> {
        match expr {
            Expr::List(items) => Ok(items),
            _ => Err(format!("#generate #async-fn {context} must be a list")),
        }
    }
    let parts = list(invocation, "async invocation")?;
    let names = list(
        parts.get(2).ok_or("async invocation requires names")?,
        "async names",
    )?;
    if !matches!(names.len(), 5 | 6 | 7) {
        return Err("invalid async function interface metadata".into());
    }
    let function = list(
        parts.get(4).ok_or("async invocation requires a function")?,
        "async function",
    )?;
    let start = match function.get(1).ok_or("async function requires a name")? {
        Expr::Symbol(name) if !name.starts_with('#') && !name.starts_with('@') => name,
        _ => return Err("#generate #async-fn function name must be a plain symbol".into()),
    };
    let protocol = names.get(5).cloned().unwrap_or_else(|| {
        Expr::Symbol(format!(
            "{}::Await",
            crate::generator::builtins::capitalized_type_name(start)
        ))
    });
    let result = function
        .get(3)
        .ok_or("async function requires a result type")?
        .clone();
    let pinned = matches!(parts.get(1), Some(Expr::Symbol(kind)) if kind == "#async-fn-pinned");
    let child = if pinned {
        Expr::List(vec![Expr::Symbol("#pin-ref-mut".into()), names[0].clone()])
    } else {
        names[0].clone()
    };
    Ok(Expr::List(vec![
        Expr::Symbol("#syntax".into()),
        protocol,
        Expr::List(vec![
            result,
            child,
            names[2].clone(),
            names[3].clone(),
            names[4].clone(),
        ]),
    ]))
}

/// The poll enum's declared fields are available before frame layout/emission.
/// This is a type-only normalization context, never an executable definition.
pub(crate) fn poll_pattern_declaration(invocation: &Expr) -> Result<Item, String> {
    let Expr::List(parts) = invocation else {
        return Err("invalid async invocation".into());
    };
    let Some(Expr::List(names)) = parts.get(2) else {
        return Err("invalid async names".into());
    };
    let name = |index| match names.get(index) {
        Some(Expr::Symbol(name)) => Ok(name.clone()),
        _ => Err("invalid async name".to_owned()),
    };
    let Some(Expr::List(function)) = parts.get(4) else {
        return Err("invalid async function".into());
    };
    let frame = Type::Named(name(0)?);
    let pending = if matches!(parts.get(1), Some(Expr::Symbol(kind)) if kind == "#async-fn-pinned")
    {
        Type::PinnedReference {
            mutable: true,
            target: Box::new(frame),
        }
    } else {
        frame
    };
    let result = crate::parse_type(
        function
            .get(3)
            .map(|ty| crate::normalize_keywords(ty.clone()))
            .as_ref(),
    )?;
    Ok(Item::Enum {
        name: name(1)?,
        representation: crate::Representation::Lim,
        linear: false,
        type_parameters: vec![],
        variants: vec![
            EnumVariant {
                name: name(2)?,
                fields: vec![pending],
                discriminant: 0,
            },
            EnumVariant {
                name: name(3)?,
                fields: vec![result],
                discriminant: 1,
            },
        ],
    })
}

#[cfg(test)]
mod protocol_tests {
    use super::*;

    fn expression(source: &str) -> Expr {
        crate::parse(source).unwrap().remove(0).expr
    }

    #[test]
    fn protocols_preserve_declared_types_and_borrow_only_pinned_frames() {
        for pinned in [false, true] {
            for (suffix, protocol) in [
                ("", "Work::Await"),
                (" WorkAwait", "WorkAwait"),
                (" WorkAwait ((owner read-owner))", "WorkAwait"),
            ] {
                let kind = if pinned {
                    "#async-fn-pinned"
                } else {
                    "#async-fn"
                };
                let frame = if pinned { "Work::frame" } else { "Work::task" };
                let invocation = expression(&format!(
                    "(#generate {kind} ({frame} WorkPoll work-pending work-ready work-poll{suffix})
                      Waker (#fn work ((owner Owner)) Result (#return (#unreachable))))"
                ));
                let task = if pinned {
                    format!("(#pin-ref-mut {frame})")
                } else {
                    frame.into()
                };
                let expected = expression(&format!(
                    "(#syntax {protocol} (Result {task} work-pending work-ready work-poll))"
                ));
                assert_eq!(protocol_declaration(&invocation).unwrap(), expected);
            }
        }
    }

    #[test]
    fn malformed_protocol_metadata_is_rejected_without_lowering_a_body() {
        for (source, message) in [
            ("bad", "async invocation must be a list"),
            ("(#generate #async-fn)", "async invocation requires names"),
            (
                "(#generate #async-fn ())",
                "invalid async function interface metadata",
            ),
            (
                "(#generate #async-fn (Work::task WorkPoll pending ready poll) Waker)",
                "async invocation requires a function",
            ),
            (
                "(#generate #async-fn (Work::task WorkPoll pending ready poll) Waker (#fn #u64 () #u64))",
                "function name must be a plain symbol",
            ),
            (
                "(#generate #async-fn (Work::task WorkPoll pending ready poll) Waker (#fn work ()))",
                "async function requires a result type",
            ),
        ] {
            let error = protocol_declaration(&expression(source)).unwrap_err();
            assert!(error.contains(message), "{error}");
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Provenance {
    Ordinary,
    AsyncStart,
    AsyncPoll,
    GraphCleanup,
    CancelDispatcher,
    GraphDestroy,
    GraphParameterAccess,
}

#[derive(Clone, Debug)]
pub(crate) struct FunctionInterface {
    /// Signature representation only; this empty body must never become a
    /// Program item or stand in for a checked implementation.
    pub declaration: Function,
    pub span: Option<Span>,
    pub provenance: Provenance,
}

#[derive(Clone, Debug)]
pub(crate) struct Error {
    pub message: String,
    pub span: Option<Span>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Registry {
    pub functions: HashMap<String, FunctionInterface>,
    pub protocols: HashMap<String, Vec<EnumVariant>>,
    pub deferred_layouts: HashMap<String, DeferredLayout>,
    pub generated_names: HashMap<String, Span>,
    aliases: HashMap<String, Type>,
    reserved: HashMap<String, Option<Span>>,
    parameter_access: Vec<(Function, Vec<(String, String)>, Span)>,
}

fn signature(function: &Function) -> Function {
    Function {
        name: function.name.clone(),
        type_parameters: function.type_parameters.clone(),
        parameters: function.parameters.clone(),
        return_type: function.return_type.clone(),
        body: Vec::new(),
        unsafe_call: function.unsafe_call,
        external: function.external,
        calling_convention: function.calling_convention,
    }
}

impl Registry {
    /// Register only explicitly requested access. The signatures are planning
    /// declarations; ordinary emitted bodies must prove their own safety.
    pub(crate) fn graph_parameter_interfaces(&mut self, program: &Program) -> Result<(), Error> {
        let mut types = None;
        for (source, access, span) in std::mem::take(&mut self.parameter_access) {
            let fail = |message| Error {
                message,
                span: Some(span),
            };
            let types =
                types.get_or_insert_with(|| crate::linearcheck::LinearTypes::from_program(program));
            for (parameter, accessor) in access {
                let parameter = source
                    .parameters
                    .iter()
                    .find(|candidate| candidate.name == parameter)
                    .ok_or_else(|| {
                        fail(format!(
                            "async access names unknown parameter '{parameter}'"
                        ))
                    })?;
                if !types.can_repeat(&parameter.ty) || types.contains_reference(&parameter.ty) {
                    return Err(fail(format!(
                        "async access parameter '{}' must be reference-free Copy data",
                        parameter.name
                    )));
                }
                for (suffix, mutable, result) in [
                    ("read", false, parameter.ty.clone()),
                    ("replace", true, Type::Unit),
                ] {
                    let name = format!("{accessor}::{suffix}");
                    if self.reserved.contains_key(&name) {
                        return Err(fail(format!(
                            "async generated name '{name}' conflicts with an existing declaration"
                        )));
                    }
                    self.reserved.insert(name.clone(), Some(span));
                    self.generated_names.insert(name.clone(), span);
                    let mut declaration = source.clone();
                    declaration.name = name.clone();
                    declaration.parameters = vec![Parameter {
                        name: "task".into(),
                        ty: Type::PinnedReference {
                            mutable,
                            target: Box::new(source.return_type.clone()),
                        },
                        mutable: false,
                    }];
                    if mutable {
                        declaration.parameters.push(Parameter {
                            name: "value".into(),
                            ty: parameter.ty.clone(),
                            mutable: false,
                        });
                    }
                    declaration.return_type = result;
                    self.functions.insert(
                        name,
                        FunctionInterface {
                            declaration,
                            span: Some(span),
                            provenance: Provenance::GraphParameterAccess,
                        },
                    );
                }
            }
        }
        Ok(())
    }
    /// The graph route has a source-named cleanup record, independent of the
    /// legacy per-state enum and the emitter's private PC/cell representation.
    pub(crate) fn graph_cleanup_interfaces(&mut self) -> Result<(), Error> {
        let polls = self
            .functions
            .values()
            .filter(|interface| interface.provenance == Provenance::AsyncPoll)
            .map(|interface| (interface.declaration.clone(), interface.span))
            .collect::<Vec<_>>();
        for (poll, span) in polls {
            let task = poll.parameters[0].ty.clone();
            let frame = match &task {
                Type::PinnedReference { target, .. } => {
                    let Type::Named(frame) = target.as_ref() else {
                        continue;
                    };
                    frame.clone()
                }
                Type::Named(frame) => frame.clone(),
                _ => continue,
            };
            let cleanup = format!("{frame}::Cleanup");
            let name = format!("{}::cleanup", crate::type_source(&poll.return_type));
            for generated in [&cleanup, &name] {
                if self.reserved.contains_key(generated) {
                    return Err(Error { message: format!("async generated name '{generated}' conflicts with an existing declaration"), span });
                }
                self.reserved.insert(generated.clone(), span);
                if let Some(span) = span {
                    self.generated_names.insert(generated.clone(), span);
                }
            }
            let origin = span.ok_or_else(|| Error {
                message: "async poll interface lost its source span".into(),
                span,
            })?;
            self.deferred_layouts.insert(
                cleanup.clone(),
                DeferredLayout {
                    kind: LayoutKind::Struct,
                    span: origin,
                    linear: true,
                },
            );
            let mut declaration = poll.clone();
            declaration.name = name.clone();
            declaration.parameters.truncate(1);
            declaration.return_type = Type::Named(cleanup.clone());
            self.functions.insert(
                name,
                FunctionInterface {
                    declaration,
                    span,
                    provenance: Provenance::GraphCleanup,
                },
            );
            if matches!(task, Type::PinnedReference { .. })
                && self.functions.values().any(|interface| {
                    interface.provenance == Provenance::CancelDispatcher
                        && interface.declaration.parameters[0].ty == Type::Named(cleanup.clone())
                })
            {
                let name = format!("{}::destroy", crate::type_source(&poll.return_type));
                if self.reserved.contains_key(&name) {
                    return Err(Error {
                        message: format!(
                            "async generated name '{name}' conflicts with an existing declaration"
                        ),
                        span,
                    });
                }
                self.reserved.insert(name.clone(), span);
                self.generated_names.insert(name.clone(), origin);
                let mut declaration = poll.clone();
                declaration.name = name.clone();
                declaration.parameters.truncate(1);
                declaration.return_type = Type::Unit;
                self.functions.insert(
                    name.clone(),
                    FunctionInterface {
                        declaration,
                        span,
                        provenance: Provenance::GraphDestroy,
                    },
                );
                let words = format!("{name}-words");
                if self.reserved.contains_key(&words) {
                    return Err(Error {
                        message: format!(
                            "async generated name '{words}' conflicts with an existing declaration"
                        ),
                        span,
                    });
                }
                self.reserved.insert(words.clone(), span);
                self.generated_names.insert(words.clone(), origin);
            }
        }
        Ok(())
    }
    pub(crate) fn interfaces(&self) -> crate::generation_interfaces::DeclarationInterfaces {
        crate::generation_interfaces::DeclarationInterfaces {
            functions: self
                .functions
                .iter()
                .map(|(name, interface)| {
                    (
                        name.clone(),
                        crate::generation_interfaces::FunctionInterface {
                            declaration: interface.declaration.clone(),
                            span: interface.span,
                            is_generated: interface.provenance != Provenance::Ordinary,
                        },
                    )
                })
                .collect(),
            protocols: self.protocols.clone(),
            deferred_layouts: self.deferred_layouts.clone(),
            generated_names: self.generated_names.clone(),
        }
    }
    pub fn from_program_invocations(
        program: &Program,
        invocations: &[crate::SpannedExpr],
    ) -> Result<Self, crate::source_error::SourceError> {
        let mut registry = Self::new(program).map_err(|error| {
            let mut error_source =
                crate::source_error::SourceError::new(error.message, crate::DiagnosticCode::Type);
            if let Some(span) = error.span {
                error_source = error_source.at(span);
            }
            error_source
        })?;
        registry.register_invocations(invocations)?;
        Ok(registry)
    }

    fn register_invocations(
        &mut self,
        invocations: &[crate::SpannedExpr],
    ) -> Result<(), crate::source_error::SourceError> {
        for invocation in invocations {
            if !crate::is_async_invocation(invocation) {
                continue;
            }
            let normalized = crate::normalize_builtin_generator_invocation(&invocation.expr)
                .map_err(|message| {
                    crate::source_error::SourceError::new(message, crate::DiagnosticCode::Parse)
                        .at(invocation.span)
                })?;
            self.register(&normalized, invocation.span)
                .map_err(|error| {
                    crate::source_error::SourceError::new(
                        error.message,
                        crate::DiagnosticCode::Type,
                    )
                    .at(error.span.unwrap_or(invocation.span))
                })?;
        }
        Ok(())
    }

    /// The context must already include imports and expanded non-async builtins.
    pub fn new(program: &Program) -> Result<Self, Error> {
        let mut registry = Self::default();
        for item in &program.items {
            let mut names = match item {
                Item::Function(function) => vec![function.name.clone()],
                Item::Struct { name, .. }
                | Item::TypeAlias { name, .. }
                | Item::Let { name, .. }
                | Item::Static { name, .. } => vec![name.clone()],
                Item::Enum { name, variants, .. } => std::iter::once(name.clone())
                    .chain(variants.iter().map(|variant| variant.name.clone()))
                    .collect(),
                Item::ThreadTask {
                    name,
                    generated_functions,
                    ..
                } => std::iter::once(name.clone())
                    .chain(
                        generated_functions
                            .iter()
                            .map(|function| function.name.clone()),
                    )
                    .collect(),
                _ => Vec::new(),
            };
            // Ordinary namespaces retain their existing language rules. Only
            // newly generated names must be unique across all namespaces.
            for name in names.drain(..) {
                registry
                    .reserved
                    .entry(name.clone())
                    .or_insert_with(|| program.declaration_spans.get(&name).copied());
            }
            match item {
                Item::Function(function) => {
                    if registry
                        .functions
                        .insert(
                            function.name.clone(),
                            FunctionInterface {
                                declaration: signature(function),
                                span: program.declaration_spans.get(&function.name).copied(),
                                provenance: Provenance::Ordinary,
                            },
                        )
                        .is_some()
                    {
                        return Err(Error {
                            message: format!("duplicate function '{}'", function.name),
                            span: program.declaration_spans.get(&function.name).copied(),
                        });
                    }
                }
                Item::Enum { name, variants, .. } => {
                    registry.protocols.insert(name.clone(), variants.clone());
                }
                Item::TypeAlias { name, target, .. } => {
                    registry.aliases.insert(name.clone(), target.clone());
                }
                _ => {}
            }
        }
        Ok(registry)
    }

    /// Register the canonical (#generate #async-fn[-pinned] names waker function [cancel])
    /// invocation. The function body is neither parsed nor analyzed here.
    pub fn register(&mut self, invocation: &Expr, span: Span) -> Result<(), Error> {
        let fail = |message: String| Error {
            message,
            span: Some(span),
        };
        let Expr::List(parts) = invocation else {
            return Err(fail("async interface requires an invocation".into()));
        };
        let pinned = matches!(parts.get(1), Some(Expr::Symbol(kind)) if kind == "#async-fn-pinned");
        if !matches!(parts.len(), 5 | 6)
            || !matches!(parts.first(), Some(Expr::Generate))
            || !matches!(parts.get(1), Some(Expr::Symbol(kind)) if kind == "#async-fn" || kind == "#async-fn-pinned")
        {
            return Err(fail("invalid normalized async invocation".into()));
        }
        let Some(Expr::List(names)) = parts.get(2) else {
            return Err(fail("async interface requires generated names".into()));
        };
        if !matches!(names.len(), 5 | 6 | 7) {
            return Err(fail(
                "async names must be (Frame Poll Pending Ready poll)".into(),
            ));
        }
        let access = match names.get(6) {
            Some(Expr::List(entries)) if pinned => entries
                .iter()
                .map(|entry| match entry {
                    Expr::List(pair) => match pair.as_slice() {
                        [Expr::Symbol(parameter), Expr::Symbol(name)] => {
                            Ok((parameter.clone(), name.clone()))
                        }
                        _ => Err(fail(
                            "async access requires (parameter accessor-name) pairs".into(),
                        )),
                    },
                    _ => Err(fail(
                        "async access requires (parameter accessor-name) pairs".into(),
                    )),
                })
                .collect::<Result<Vec<_>, _>>()?,
            None => Vec::new(),
            _ => {
                return Err(fail(
                    "async parameter access requires a pinned frame and a literal list".into(),
                ))
            }
        };
        let names = names
            .iter()
            .take(5)
            .map(|name| match name {
                Expr::Symbol(name) => Ok(name.clone()),
                _ => Err(fail("async generated names must be identifiers".into())),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let [frame, poll_type, pending, ready, poll_name] = names.as_slice() else {
            unreachable!()
        };
        let Some(Expr::List(source)) = parts.get(4) else {
            return Err(fail("async interface requires a #fn declaration".into()));
        };
        if source.len() < 5
            || !matches!(source.first(), Some(Expr::Symbol(head)) if head == "#fn" || head == "fn")
        {
            return Err(fail(
                "async interface requires a #fn declaration with a body".into(),
            ));
        }
        let Expr::List(header) = crate::normalize_keywords(Expr::List(source[..4].to_vec())) else {
            unreachable!()
        };
        let original = crate::parse_function_parts(&header, false, false).map_err(fail)?;
        let mut parameter_names = HashSet::new();
        for parameter in &original.parameters {
            if !parameter_names.insert(&parameter.name) {
                return Err(fail(format!("duplicate parameter '{}'", parameter.name)));
            }
        }
        let waker =
            crate::parse_type(Some(&crate::normalize_keywords(parts[3].clone()))).map_err(fail)?;
        let cleanup = format!("{frame}::Cleanup");
        let mut declarations = vec![Function {
            name: original.name.clone(),
            parameters: original.parameters.clone(),
            return_type: Type::Named(frame.clone()),
            body: Vec::new(),
            type_parameters: Vec::new(),
            unsafe_call: false,
            external: false,
            calling_convention: CallingConvention::Lim,
        }];
        let access_source = (!access.is_empty()).then(|| declarations[0].clone());
        let task = if pinned {
            Type::PinnedReference {
                mutable: true,
                target: Box::new(Type::Named(frame.clone())),
            }
        } else {
            Type::Named(frame.clone())
        };
        declarations.push(Function {
            name: poll_name.clone(),
            parameters: vec![
                Parameter {
                    name: "task".into(),
                    ty: task.clone(),
                    mutable: false,
                },
                Parameter {
                    name: "waker".into(),
                    ty: Type::Reference {
                        mutable: false,
                        target: Box::new(waker),
                    },
                    mutable: false,
                },
            ],
            return_type: Type::Named(poll_type.clone()),
            body: Vec::new(),
            type_parameters: Vec::new(),
            unsafe_call: false,
            external: false,
            calling_convention: CallingConvention::Lim,
        });
        let mut provenances = vec![Provenance::AsyncStart, Provenance::AsyncPoll];
        let mut reserved = names.clone();
        reserved.push(original.name.clone());
        if let Some(config) = parts.get(5) {
            let Expr::List(config) = config else {
                return Err(fail("invalid async cancellation configuration".into()));
            };
            let [Expr::Symbol(cancel), Expr::List(handlers)] = config.as_slice() else {
                return Err(fail(
                    "async cancel requires (function ((state handler) ...))".into(),
                ));
            };
            let mut states = HashSet::new();
            for handler in handlers {
                let Expr::List(handler) = handler else {
                    return Err(fail("invalid cancellation handler".into()));
                };
                let [Expr::Symbol(state), Expr::Symbol(_)] = handler.as_slice() else {
                    return Err(fail("cancellation handler requires (state handler)".into()));
                };
                if !states.insert(state) {
                    return Err(fail(format!("duplicate cancellation state '{state}'")));
                }
            }
            reserved.push(cancel.clone());
            declarations.push(Function {
                name: cancel.clone(),
                parameters: vec![Parameter {
                    name: "task".into(),
                    ty: Type::Named(cleanup.clone()),
                    mutable: false,
                }],
                return_type: Type::Unit,
                body: Vec::new(),
                type_parameters: Vec::new(),
                unsafe_call: false,
                external: false,
                calling_convention: CallingConvention::Lim,
            });
            provenances.push(Provenance::CancelDispatcher);
        }
        let mut unique = HashSet::new();
        for name in &reserved {
            if !unique.insert(name) || self.reserved.contains_key(name) {
                return Err(fail(format!(
                    "async generated name '{name}' conflicts with an existing declaration"
                )));
            }
        }
        // Commit only after checking the complete interface, including derived names.
        if let Some(source) = access_source {
            self.parameter_access.push((source, access, span));
        }
        for name in reserved {
            self.reserved.insert(name.clone(), Some(span));
            self.generated_names.insert(name, span);
        }
        self.deferred_layouts.insert(
            frame.clone(),
            DeferredLayout {
                kind: LayoutKind::Struct,
                span,
                linear: true,
            },
        );
        self.protocols.insert(
            poll_type.clone(),
            vec![
                EnumVariant {
                    name: pending.clone(),
                    fields: vec![task],
                    discriminant: 0,
                },
                EnumVariant {
                    name: ready.clone(),
                    fields: vec![original.return_type],
                    discriminant: 1,
                },
            ],
        );
        for (declaration, provenance) in declarations.into_iter().zip(provenances) {
            self.functions.insert(
                declaration.name.clone(),
                FunctionInterface {
                    declaration,
                    provenance,
                    span: Some(span),
                },
            );
        }
        Ok(())
    }

    pub fn lookup_poll_declaration(&self, name: &str) -> Option<&Function> {
        self.functions
            .get(name)
            .map(|interface| &interface.declaration)
    }

    pub fn function(&self, name: &str) -> Option<&Function> {
        self.lookup_poll_declaration(name)
    }

    pub fn enum_variants(&self, ty: &Type) -> Option<&Vec<EnumVariant>> {
        let Type::Named(name) = crate::typed_ir::resolve_type(ty, &self.aliases).ok()? else {
            return None;
        };
        self.protocols.get(&name)
    }

    pub fn signature_context(&self) -> Vec<Item> {
        let mut functions = self
            .functions
            .values()
            .filter(|interface| interface.provenance != Provenance::Ordinary)
            .map(|interface| signature(&interface.declaration))
            .collect::<Vec<_>>();
        functions.sort_by(|left, right| left.name.cmp(&right.name));
        functions.into_iter().map(Item::Function).collect()
    }
}
