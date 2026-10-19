//! Lower caller traces to ordinary, borrow-checked stack storage.
//!
//! Only the reverse-reachable callers of a trace are instrumented. Contexts
//! are owned values, including when a worker is started on another thread.
//! No global trace state, heap allocation, or enumeration of call paths is
//! needed. The acyclic call graph gives a finite conservative buffer bound.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{Expr, Item, Parameter, Program, SourceError, Statement, Type};

#[derive(Clone)]
struct Site {
    callee: Option<String>,
    line: usize,
    trace: bool,
    clone_hook: bool,
}

fn expressions(statements: &mut [Statement], visit: &mut impl FnMut(&mut Expr)) {
    for statement in statements {
        match statement {
            Statement::Let { value, .. }
            | Statement::Assign { value, .. }
            | Statement::FieldAssign { value, .. }
            | Statement::TupleAssign { value, .. }
            | Statement::EnumPayloadAssign { value, .. }
            | Statement::BreakValue(value)
            | Statement::BreakToValue { value, .. }
            | Statement::Return(Some(value))
            | Statement::Expr(value) => expression(value, visit),
            Statement::Destructure { pattern, value, .. } => {
                expression(pattern, visit);
                expression(value, visit);
            }
            Statement::LetElse {
                pattern,
                value,
                failure_pattern,
                else_body,
                ..
            } => {
                expression(pattern, visit);
                expression(value, visit);
                if let Some(pattern) = failure_pattern {
                    expression(pattern, visit);
                }
                expressions(else_body, visit);
            }
            Statement::ArrayAssign { index, value, .. } => {
                expression(index, visit);
                expression(value, visit);
            }
            Statement::While { condition, body } => {
                expression(condition, visit);
                expressions(body, visit);
            }
            Statement::Loop { body } => expressions(body, visit),
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                expressions(std::slice::from_mut(init), visit);
                expression(condition, visit);
                expressions(std::slice::from_mut(step), visit);
                expressions(body, visit);
            }
            Statement::Labeled { statement, .. } => {
                expressions(std::slice::from_mut(statement), visit)
            }
            _ => {}
        }
    }
}

fn expression(value: &mut Expr, visit: &mut impl FnMut(&mut Expr)) {
    match value {
        Expr::List(items) => {
            for item in items {
                expression(item, visit);
            }
        }
        Expr::Block(body) | Expr::Loop(body) => expressions(body, visit),
        Expr::Labeled {
            expression: inner, ..
        } => expression(inner, visit),
        _ => {}
    }
    visit(value);
}

fn form(head: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::List(
        std::iter::once(Expr::Symbol(head.into()))
            .chain(arguments)
            .collect(),
    )
}

fn zero() -> Expr {
    form("array-repeat", [Expr::Char('\0')])
}

fn usize_value(value: usize) -> Expr {
    form(
        "literal",
        [
            Expr::Symbol("usize".into()),
            Expr::UnsignedInteger(value as u128),
        ],
    )
}

fn append_call(append: &str, incoming: Expr, length: Expr, label: Expr) -> Expr {
    Expr::List(vec![
        Expr::Function(append.into()),
        incoming,
        length,
        form("slice-of", [form("borrow", [label])]),
    ])
}

fn helper(
    name: &str,
    context: &Type,
    capacity: usize,
    scope: &mut crate::gensym::Scope,
) -> Result<Item, String> {
    let incoming = scope.fresh("incoming")?;
    let length = scope.fresh("length")?;
    let segment = scope.fresh("segment")?;
    let buffer = scope.fresh("buffer")?;
    let offset = scope.fresh("offset")?;
    let index = scope.fresh("index")?;
    let context = crate::type_source(context);
    let source = format!("(#fn {name} (({incoming} {context}) ({length} #usize) ({segment} (#slice #char))) {context}
      (#let-mut {buffer} (#array #char {capacity}) {incoming})
      (#let {offset} #usize {length})
      (#let-mut {index} #usize 0usize)
      (#while (#usize::lt {index} (#slice-len {segment}))
        (#deref-set (#borrow-mut (#index {buffer} (#usize::add-wrap {offset} {index})))
          (#deref (#slice-idx {segment} {index})))
        (#set {index} (#usize::add-wrap {index} 1usize)))
      (#return {buffer}))");
    let node = crate::parse(&source)
        .map_err(|error| error.to_string())?
        .remove(0);
    crate::parse_item(&crate::normalize_keywords(node.expr))
}

/// Run after explicit calls/aggregate literals are normalized and before final
/// ownership checking. The temporary trace typing is never a native operation.
pub(crate) fn lower(program: &mut Program) -> Result<(), SourceError> {
    // Ordinary programs pay only a source-text probe, not another AST walk or
    // semantic analysis. Generated source is retained in source_files too.
    if !program
        .source_files
        .iter()
        .any(|file| file.source.contains("#call-graph"))
        && !program
            .source
            .as_ref()
            .is_some_and(|source| source.contains("#call-graph"))
    {
        return Ok(());
    }
    let Some(validation) = program.generator_validation.take() else {
        return lower_inner(program);
    };
    let witnesses = validation.map_err(|(message, code, span, labels)| {
        let mut error = SourceError::new(message, code);
        if let Some(span) = span {
            error = error.at(span);
        }
        for (span, message) in labels {
            error = error.with_label(span, message);
        }
        error.attach(&program.source_files)
    })?;
    // Instrument runtime bodies and their ordinary validation witnesses in
    // the same declaration context. Otherwise an original witness would call
    // a runtime helper without the helper's added context parameters.
    if !witnesses.source_files.starts_with(&program.source_files) {
        return Err("caller tracing requires aligned validation source identities".into());
    }
    let names = witnesses
        .items
        .iter()
        .flat_map(crate::item_declared_names)
        .collect::<HashSet<_>>();
    let mut combined = program.clone();
    combined.source_files = witnesses.source_files.clone();
    combined.items.extend(witnesses.items.iter().cloned());
    combined
        .statement_spans
        .extend(witnesses.statement_spans.clone());
    combined
        .statement_expressions
        .extend(witnesses.statement_expressions.clone());
    combined
        .declaration_spans
        .extend(witnesses.declaration_spans.clone());
    combined
        .declaration_expressions
        .extend(witnesses.declaration_expressions.clone());
    combined
        .declaration_occurrences
        .extend(witnesses.declaration_occurrences.clone());
    combined
        .generated_source_invocations
        .extend(witnesses.generated_source_invocations.clone());
    combined
        .reference_authorities
        .extend(witnesses.reference_authorities.clone());
    combined
        .syntax_bundle_uses
        .extend(witnesses.syntax_bundle_uses.clone());
    lower_inner(&mut combined)?;
    let mut checked_witnesses = combined.clone();
    checked_witnesses.items.retain(|item| {
        crate::item_declared_names(item)
            .iter()
            .any(|name| names.contains(name))
    });
    checked_witnesses
        .statement_spans
        .retain(|(name, _), _| names.contains(name));
    checked_witnesses
        .statement_expressions
        .retain(|(name, _), _| names.contains(name));
    checked_witnesses
        .declaration_spans
        .retain(|name, _| names.contains(name));
    checked_witnesses
        .declaration_expressions
        .retain(|name, _| names.contains(name));
    checked_witnesses
        .declaration_occurrences
        .retain(|name, _| names.contains(name));
    combined.items.retain(|item| {
        !crate::item_declared_names(item)
            .iter()
            .any(|name| names.contains(name))
    });
    combined
        .statement_spans
        .retain(|(name, _), _| !names.contains(name));
    combined
        .statement_expressions
        .retain(|(name, _), _| !names.contains(name));
    combined
        .declaration_spans
        .retain(|name, _| !names.contains(name));
    combined
        .declaration_expressions
        .retain(|name, _| !names.contains(name));
    combined
        .declaration_occurrences
        .retain(|name, _| !names.contains(name));
    combined.generator_validation = Some(Ok(std::sync::Arc::new(checked_witnesses)));
    *program = combined;
    Ok(())
}

fn lower_inner(program: &mut Program) -> Result<(), SourceError> {
    let mut present = false;
    for item in &mut program.items {
        if let Item::Function(function) = item {
            expressions(&mut function.body, &mut |value| {
                present |= matches!(value, Expr::List(items)
                    if matches!(items.first(), Some(Expr::Symbol(head)) if head == "call-graph"));
            });
        }
    }
    if !present {
        return Ok(());
    }

    let declarations = crate::typecheck::resolve_program_for_analysis(program, false).map_err(
        |(message, code, span, labels)| {
            let mut error = SourceError::new(message, code);
            if let Some(span) = span {
                error = error.at(span);
            }
            for (span, message) in labels {
                error = error.with_label(span, message);
            }
            error.attach(&program.source_files)
        },
    )?;
    let workers = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::ThreadTask { name, worker, .. } => Some((name.clone(), worker.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let mut sites = HashMap::<usize, Site>::new();
    let mut callers = HashMap::<String, HashSet<String>>::new();
    let mut affected = HashSet::<String>::new();
    let mut widths = HashMap::<String, usize>::new();
    for (task, worker) in &workers {
        // The native spawn operation transfers owned arguments to its worker;
        // it does not execute a source-language function body of its own.
        callers
            .entry(worker.clone())
            .or_default()
            .insert(format!("{task}::spawn"));
    }
    for item in &mut program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if function.external {
            continue;
        }
        let body = &declarations.bodies[&function.name];
        let emission = body.emission_types(function)?;
        let name = function.name.clone();
        expressions(&mut function.body, &mut |value| {
            let Expr::List(items) = &*value else { return };
            let Some(head) = items.first() else { return };
            let trace = matches!(head, Expr::Symbol(head) if head == "call-graph");
            let info = emission.get(value);
            let mut clone_hook = false;
            let callee = if let Some(callee) = info.and_then(|info| info.callee) {
                Some(declarations.function(callee).name.clone())
            } else if matches!(head, Expr::Symbol(head) if head == "clone") {
                let owner = items
                    .get(1)
                    .and_then(|value| emission.get(value))
                    .and_then(|info| info.ty.as_ref())
                    .and_then(|ty| crate::typed_ir::resolve_type(ty, &declarations.aliases).ok());
                if let Some(Type::Named(owner)) = owner {
                    let hook = format!("{owner}::clone");
                    clone_hook = declarations.function_id(&hook).is_some();
                    clone_hook.then_some(hook)
                } else {
                    None
                }
            } else if matches!(head, Expr::Symbol(head) if head == "thread-task-spawn") {
                items.get(1).and_then(|task| match task {
                    Expr::Symbol(task) => workers.get(task).cloned(),
                    _ => None,
                })
            } else {
                None
            };
            if !trace && callee.is_none() {
                return;
            }
            let line = info.and_then(|info| info.span).map_or(0, |span| span.line);
            widths
                .entry(name.clone())
                .and_modify(|width| *width = (*width).max(line.to_string().len()))
                .or_insert_with(|| line.to_string().len());
            if trace {
                affected.insert(name.clone());
            }
            if let Some(callee) = &callee {
                callers
                    .entry(callee.clone())
                    .or_default()
                    .insert(name.clone());
            }
            sites.insert(
                std::ptr::from_ref(value) as usize,
                Site {
                    callee,
                    line,
                    trace,
                    clone_hook,
                },
            );
        });
    }
    let mut pending = VecDeque::from_iter(affected.iter().cloned());
    while let Some(callee) = pending.pop_front() {
        for caller in callers.get(&callee).into_iter().flatten() {
            if affected.insert(caller.clone()) {
                pending.push_back(caller.clone());
            }
        }
    }
    if sites.values().any(|site| {
        site.line == 0
            && (site.trace
                || site
                    .callee
                    .as_ref()
                    .is_some_and(|callee| affected.contains(callee)))
    }) {
        return Err("#call-graph cannot trace a call without a retained source location".into());
    }
    // Sum one maximum segment per affected function. With recursion forbidden,
    // every runtime chain fits, even though the number of possible paths need
    // not be enumerated (and may be exponential).
    let capacity = affected.iter().try_fold(0usize, |total, name| {
        total
            .checked_add(name.chars().count() + 5 + widths.get(name).copied().unwrap_or(1))
            .ok_or("#call-graph buffer size overflow")
    })?;
    let context_ty = Type::Array(Box::new(Type::Char), capacity);
    let mut scope = crate::gensym::Scope::new('c', "call-graph-v1");
    let context_name = scope.fresh("context")?;
    let length_name = scope.fresh("length")?;
    let append = scope.fresh("append")?;
    let mut shifts = HashMap::new();
    for item in &mut program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if !affected.contains(&function.name) {
            continue;
        }
        let name = function.name.clone();
        let incoming = if name == "main" {
            zero()
        } else {
            Expr::Symbol(context_name.clone())
        };
        let length = if name == "main" {
            usize_value(0)
        } else {
            Expr::Symbol(length_name.clone())
        };
        if name != "main" {
            function.parameters.push(Parameter {
                name: context_name.clone(),
                ty: context_ty.clone(),
                mutable: false,
            });
            function.parameters.push(Parameter {
                name: length_name.clone(),
                ty: Type::Usize,
                mutable: false,
            });
        }
        let mut buffers = Vec::new();
        let mut error = None;
        expressions(&mut function.body, &mut |value| {
            let Some(site) = sites.get(&(std::ptr::from_ref(value) as usize)) else {
                return;
            };
            if !site.trace
                && !site
                    .callee
                    .as_ref()
                    .is_some_and(|callee| affected.contains(callee))
            {
                return;
            }
            let label = format!(
                "{}{name}:{}",
                if name == "main" { "" } else { " -> " },
                site.line
            );
            let label_length = label.chars().count();
            let segment = match scope.fresh("segment") {
                Ok(name) => name,
                Err(failure) => {
                    error = Some(failure);
                    return;
                }
            };
            buffers.push(Statement::Let {
                name: segment.clone(),
                ty: Type::Array(Box::new(Type::Char), label.chars().count()),
                value: Expr::String(label),
                mutable: false,
            });
            let context = append_call(
                &append,
                incoming.clone(),
                length.clone(),
                Expr::Symbol(segment),
            );
            let next_length = form("usize.+.wrap", [length.clone(), usize_value(label_length)]);
            if site.trace {
                let buffer = match scope.fresh("trace") {
                    Ok(name) => name,
                    Err(failure) => {
                        error = Some(failure);
                        return;
                    }
                };
                buffers.push(Statement::Let {
                    name: buffer.clone(),
                    ty: context_ty.clone(),
                    value: zero(),
                    mutable: true,
                });
                *value = Expr::Block(vec![
                    Statement::Assign {
                        name: buffer.clone(),
                        value: context,
                    },
                    Statement::Expr(form(
                        "borrow-slice",
                        [Expr::Symbol(buffer), usize_value(0), next_length],
                    )),
                ]);
            } else if let Expr::List(items) = value {
                if site.clone_hook {
                    items[0] = Expr::Function(site.callee.clone().unwrap());
                }
                items.push(context);
                items.push(next_length);
            }
        });
        if let Some(error) = error {
            return Err(error.into());
        }
        if !buffers.is_empty() {
            shifts.insert(name, buffers.len());
            buffers.append(&mut function.body);
            function.body = buffers;
        }
    }
    for item in &mut program.items {
        if let Item::ThreadTask {
            generated_functions,
            ..
        } = item
        {
            for signature in generated_functions {
                if affected.contains(&signature.name) {
                    signature.parameters.push(Parameter {
                        name: context_name.clone(),
                        ty: context_ty.clone(),
                        mutable: false,
                    });
                    signature.parameters.push(Parameter {
                        name: length_name.clone(),
                        ty: Type::Usize,
                        mutable: false,
                    });
                }
            }
        }
    }
    program.statement_spans = std::mem::take(&mut program.statement_spans)
        .into_iter()
        .map(|((name, index), span)| {
            let index = index + shifts.get(&name).copied().unwrap_or(0);
            ((name, index), span)
        })
        .collect();
    program.statement_expressions = std::mem::take(&mut program.statement_expressions)
        .into_iter()
        .map(|((name, index), value)| {
            let index = index + shifts.get(&name).copied().unwrap_or(0);
            ((name, index), value)
        })
        .collect();
    program
        .items
        .push(helper(&append, &context_ty, capacity, &mut scope)?);
    Ok(())
}
