//! Syntactic lowering for concrete async functions with inferred live captures.
//!
//! This deliberately emits ordinary Lim declarations before type and borrow
//! checking. No suspension point can hide a reference from those passes.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use crate::{expression_source, normalize_keywords, parse_type, Expr, Type};

thread_local! {
    static NAMED_COPY_TYPES: RefCell<Vec<HashSet<String>>> = const { RefCell::new(Vec::new()) };
    static ASYNC_TYPE_ENVIRONMENTS: RefCell<Vec<AsyncTypeEnvironment>> = const { RefCell::new(Vec::new()) };
}

struct NamedCopyTypesGuard;

impl Drop for NamedCopyTypesGuard {
    fn drop(&mut self) {
        NAMED_COPY_TYPES.with(|types| {
            types.borrow_mut().pop();
        });
    }
}

fn with_named_copy_types<T>(types: &HashSet<String>, action: impl FnOnce() -> T) -> T {
    NAMED_COPY_TYPES.with(|stack| stack.borrow_mut().push(types.clone()));
    let _guard = NamedCopyTypesGuard;
    action()
}

fn with_additional_named_copy_types<T>(additions: &[String], action: impl FnOnce() -> T) -> T {
    let mut types =
        NAMED_COPY_TYPES.with(|stack| stack.borrow().last().cloned().unwrap_or_default());
    types.extend(additions.iter().cloned());
    with_named_copy_types(&types, action)
}

fn is_named_copy_type(name: &str) -> bool {
    NAMED_COPY_TYPES.with(|stack| {
        stack
            .borrow()
            .last()
            .is_some_and(|types| types.contains(name))
    })
}

struct AsyncTypeEnvironmentGuard;

impl Drop for AsyncTypeEnvironmentGuard {
    fn drop(&mut self) {
        ASYNC_TYPE_ENVIRONMENTS.with(|environments| {
            environments.borrow_mut().pop();
        });
    }
}

fn with_async_type_environment<T>(
    environment: &AsyncTypeEnvironment,
    action: impl FnOnce() -> T,
) -> T {
    ASYNC_TYPE_ENVIRONMENTS.with(|stack| stack.borrow_mut().push(environment.clone()));
    let _guard = AsyncTypeEnvironmentGuard;
    action()
}

fn function_parameter_type(function: &str, parameter: &str) -> Option<String> {
    ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
        stack
            .borrow()
            .last()?
            .functions
            .get(function)?
            .get(parameter)
            .cloned()
    })
}

fn struct_field_type(structure: &str, field: &str) -> Option<String> {
    ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
        stack
            .borrow()
            .last()?
            .struct_fields
            .get(structure)?
            .get(field)
            .cloned()
    })
}

fn enum_constructor_field_types(variant: &str) -> Option<Vec<String>> {
    ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
        stack
            .borrow()
            .last()?
            .enums
            .values()
            .find_map(|variants| variants.get(variant).cloned())
    })
}

/// Bridge a synchronous value into a loop's poll protocol without adding a
/// suspension point. The input is evaluated once, before constructing a task.
fn immediate_await(
    value: &Expr,
    result_type: &str,
    role: &str,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<(Expr, String), String> {
    let base = fresh_async_name(source, next_name);
    let task = format!("{base}-{role}-task");
    let input = format!("{base}-{role}-input");
    let result = format!("{base}-{role}-result");
    let pending = format!("{base}-{role}-pending");
    let ready = format!("{base}-{role}-ready");
    let poll = format!("{base}-{role}-poll");
    let helper = format!(
        "(#enum {task} (({input} {result_type})))\n(#linear {task})\n\
         (#enum {result} (({pending} {task}) ({ready} {result_type})))\n\
         (#fn {poll} ((task {task}) (waker (#ref {waker}))) {result}\n\
           (#return (#match task (#case ({input} value) ({ready} value)))))"
    );
    let awaited = crate::parse(&format!(
        "(#await {result_type} {task} {pending} {ready} {poll} ({input} {}))",
        expression_source(value)?,
    ))?[0]
        .expr
        .clone();
    Ok((awaited, helper))
}

fn async_argument_is_trivial(expression: &Expr) -> bool {
    matches!(
        expression,
        Expr::Symbol(_)
            | Expr::Integer(_)
            | Expr::UnsignedInteger(_)
            | Expr::Float(_)
            | Expr::Char(_)
            | Expr::String(_)
    )
}

#[derive(Clone)]
struct Binding {
    name: String,
    ty: String,
    mutable: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct AsyncTypeEnvironment {
    pub enums: HashMap<String, HashMap<String, Vec<String>>>,
    pub aliases: HashMap<String, String>,
    pub functions: HashMap<String, HashMap<String, String>>,
    pub function_results: HashMap<String, String>,
    pub struct_fields: HashMap<String, HashMap<String, String>>,
    /// Positional struct patterns follow declaration order, never hash order.
    pub struct_field_order: HashMap<String, Vec<String>>,
}

#[derive(Clone)]
struct LoopReferenceTransfer {
    name: String,
    ty: String,
    result_index: usize,
    resumed_name: String,
    owned: bool,
}

fn async_task_capture_is_copy(ty: &Type) -> bool {
    match ty {
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
        | Type::Slice(_) => true,
        Type::Reference { mutable: false, .. } | Type::PinnedReference { mutable: false, .. } => {
            true
        }
        Type::Tuple(elements) => elements.iter().all(async_task_capture_is_copy),
        Type::Array(element, _) => async_task_capture_is_copy(element),
        Type::Never
        | Type::Reference { mutable: true, .. }
        | Type::PinnedReference { mutable: true, .. }
        | Type::MutableSlice(_)
        | Type::Atomic(_)
        | Type::Generic(_) => false,
        Type::Named(name) => is_named_copy_type(name),
    }
}

fn async_task_capture_is_mutable_reference(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Reference { mutable: true, .. }
            | Type::PinnedReference { mutable: true, .. }
            | Type::MutableSlice(_)
    )
}

#[derive(Clone)]
struct PinnedSelfReference {
    binding: Binding,
    owner: Binding,
    owner_initializer: Option<String>,
    projection: Vec<PinnedProjection>,
    target_ty: String,
    mutable: bool,
    helper_parameter: String,
    source_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum PinnedProjection {
    Field(String),
    EnumPayload { variant: String, index: usize },
}

struct Stage {
    prefix: Vec<String>,
    source_index: usize,
    available: Vec<String>,
    captures: Vec<Binding>,
    binding: Binding,
    child: String,
    pending: String,
    ready: String,
    poll: String,
    value: String,
}

fn inline_stage_task_temporary(prefix: &mut Vec<String>, task: &str) -> Result<String, String> {
    let Some(last) = prefix.last() else {
        return Ok(task.to_owned());
    };
    let parsed = crate::parse(last)?;
    let Some(statement) = parsed.first().map(|expression| &expression.expr) else {
        return Ok(task.to_owned());
    };
    let Some(binding) = form(statement, "#let").or_else(|| form(statement, "#let-mut")) else {
        return Ok(task.to_owned());
    };
    if binding.len() != 4 || !matches!(&binding[1], Expr::Symbol(name) if name == task) {
        return Ok(task.to_owned());
    }
    for preceding in &prefix[..prefix.len() - 1] {
        for expression in crate::parse(preceding)? {
            let mut names = HashSet::new();
            collect_value_names(&expression.expr, &mut names);
            if names.contains(task) {
                return Ok(task.to_owned());
            }
        }
    }
    let inlined = expression_source(&binding[3])?;
    prefix.pop();
    Ok(inlined)
}

/// A whole-value assignment defines the next value of a local; only its RHS
/// can need the old value. Projections and nested control flow remain reads
/// of their owner, so this never drops a live partially updated aggregate.
fn continuation_live_names(
    statements: &[Expr],
    returned: Option<&Expr>,
    known: &HashMap<String, Binding>,
) -> HashSet<String> {
    let mut live = HashSet::new();
    if let Some(returned) = returned {
        collect_value_names(returned, &mut live);
    }
    for statement in statements.iter().rev() {
        if let Some(assignment) = form(statement, "#set").filter(|items| items.len() == 3) {
            if let Expr::Symbol(name) = &assignment[1] {
                // Retain existing Copy slots and their inspectable cancellation
                // layout. Unique owners, in contrast, must not be duplicated
                // merely to provide a slot for a subsequent replacement.
                if known
                    .get(name)
                    .and_then(|binding| crate::parse(&binding.ty).ok())
                    .and_then(|types| types.into_iter().next())
                    .and_then(|ty| parse_type(Some(&normalize_keywords(ty.expr))).ok())
                    .is_some_and(|ty| !async_task_capture_is_copy(&ty))
                {
                    live.remove(name);
                }
                collect_value_names(&assignment[2], &mut live);
                continue;
            }
        }
        if let Ok(local) = binding(statement, "continuation liveness") {
            live.remove(&local.name);
            if let Expr::List(items) = statement {
                collect_value_names(&items[3], &mut live);
            }
        } else {
            collect_value_names(statement, &mut live);
        }
    }
    live
}

/// A dead incoming value needs no frame capture, but its explicit replacement
/// still needs a local slot in the new resume helper. Declare that slot at the
/// assignment, after evaluating its RHS. Ordinary ownership checking still
/// rejects an unconsumed old linear value in the helper that suspended.
fn resume_prefix(
    prefix: &[String],
    stage: &Stage,
    known: &HashMap<String, Binding>,
    environment: &AsyncTypeEnvironment,
) -> Result<Vec<String>, String> {
    let mut locals = stage
        .captures
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    locals.insert(stage.binding.name.clone());
    let mut rewritten = Vec::with_capacity(prefix.len());
    for statement in prefix {
        let mut parsed = crate::parse(statement)?;
        let Some(expression) = parsed.first_mut().map(|statement| &mut statement.expr) else {
            rewritten.push(statement.clone());
            continue;
        };
        if let Some(assignment) = form(expression, "#set").filter(|items| items.len() == 3) {
            if let Expr::Symbol(name) = &assignment[1] {
                if !locals.contains(name) {
                    let binding = known
                        .get(name)
                        .ok_or_else(|| format!("unknown async assignment target '{name}'"))?;
                    let ty = crate::parse(&binding.ty)?[0].expr.clone();
                    locals.insert(name.clone());
                    *expression = Expr::List(vec![
                        Expr::Symbol("#let-mut".into()),
                        assignment[1].clone(),
                        ty,
                        assignment[2].clone(),
                    ]);
                    rewritten.push(expression_source(expression)?);
                    continue;
                }
            }
        }
        if let Some(bindings) = declared_local_bindings(expression, environment)? {
            for binding in bindings {
                locals.insert(binding.name);
            }
        }
        rewritten.push(statement.clone());
    }
    Ok(rewritten)
}

fn list<'a>(expr: &'a Expr, context: &str) -> Result<&'a [Expr], String> {
    match expr {
        Expr::List(items) => Ok(items),
        _ => Err(format!("@async-fn {context} must be a list")),
    }
}

fn symbol<'a>(expr: &'a Expr, context: &str) -> Result<&'a str, String> {
    match expr {
        Expr::Symbol(name) if !name.starts_with('#') && !name.starts_with('@') => Ok(name),
        _ => Err(format!("@async-fn {context} must be a plain symbol")),
    }
}

fn form<'a>(expr: &'a Expr, head: &str) -> Option<&'a [Expr]> {
    let Expr::List(items) = expr else { return None };
    if matches!(items.first(), Some(Expr::Symbol(name)) if name == head) {
        Some(items)
    } else {
        None
    }
}

fn has_await(expr: &Expr) -> bool {
    await_count(expr) != 0
}

fn statement_has_await(statement: &crate::Statement) -> bool {
    statement_await_count(statement) != 0
}

fn statement_await_count(statement: &crate::Statement) -> usize {
    use crate::Statement as S;
    match statement {
        S::Let { value, .. }
        | S::Destructure { value, .. }
        | S::Assign { value, .. }
        | S::FieldAssign { value, .. }
        | S::TupleAssign { value, .. }
        | S::EnumPayloadAssign { value, .. }
        | S::BreakValue(value)
        | S::BreakToValue { value, .. }
        | S::Expr(value) => await_count(value),
        S::ArrayAssign { index, value, .. } => await_count(index) + await_count(value),
        S::LetElse {
            value, else_body, ..
        } => await_count(value) + else_body.iter().map(statement_await_count).sum::<usize>(),
        S::While { condition, body } => {
            await_count(condition) + body.iter().map(statement_await_count).sum::<usize>()
        }
        S::Loop { body } => body.iter().map(statement_await_count).sum(),
        S::For {
            init,
            condition,
            step,
            body,
        } => {
            statement_await_count(init)
                + await_count(condition)
                + statement_await_count(step)
                + body.iter().map(statement_await_count).sum::<usize>()
        }
        S::Labeled { statement, .. } => statement_await_count(statement),
        S::Return(Some(value)) => await_count(value),
        S::Return(None) | S::Break | S::BreakTo(_) | S::Continue | S::ContinueTo(_) => 0,
    }
}

fn await_count(expr: &Expr) -> usize {
    match expr {
        Expr::List(items) => {
            usize::from(form(expr, "#await").is_some() || form(expr, "await").is_some())
                + items.iter().map(await_count).sum::<usize>()
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            statements.iter().map(statement_await_count).sum()
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => await_count(expression),
        _ => 0,
    }
}

/// Adapt the diverging return arm of `#let-else` to the async poll helper's
/// result type. The successful pattern path continues through the function;
/// only its required diverging arm returns early.
fn rewrite_async_let_else_returns(expression: &mut Expr, ready: &str) -> Result<(), String> {
    let Expr::List(items) = expression else {
        return Ok(());
    };
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
    {
        return Ok(());
    }
    if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#let-else") {
        let Some(else_body) = items.get_mut(4) else {
            return Err("@async-fn #let-else requires a diverging else body".into());
        };
        return rewrite_async_diverging_returns(else_body, ready);
    }
    for item in items.iter_mut().skip(1) {
        rewrite_async_let_else_returns(item, ready)?;
    }
    Ok(())
}

fn rewrite_async_diverging_returns(expression: &mut Expr, ready: &str) -> Result<(), String> {
    if let Some(items) = form(expression, "#return").or_else(|| form(expression, "return")) {
        if items.len() != 2 {
            return Err("@async-fn #let-else return requires exactly one value".into());
        }
        let Expr::List(items) = expression else {
            unreachable!()
        };
        items[1] = Expr::List(vec![Expr::Symbol(ready.into()), items[1].clone()]);
        return Ok(());
    }
    let Expr::List(items) = expression else {
        return Ok(());
    };
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
    {
        return Ok(());
    }
    for item in items.iter_mut().skip(1) {
        rewrite_async_diverging_returns(item, ready)?;
    }
    Ok(())
}

/// Rewrite returns in ordinary synchronous loop bodies. A loop which itself
/// suspends owns a separate generated task result and is handled by loop
/// lowering instead; a synchronous loop remains in its containing poll helper
/// and can return that helper's `Ready` value directly.
fn rewrite_async_synchronous_loop_returns(
    expression: &mut Expr,
    ready: &str,
) -> Result<(), String> {
    let loop_body_start = ["#while", "#for", "#for-range", "#loop"]
        .into_iter()
        .find_map(|keyword| form(expression, keyword).map(|items| (keyword, items)))
        .map(|(keyword, _)| match keyword {
            "#while" => 2,
            "#for" | "#for-range" => 4,
            "#loop" => 1,
            _ => unreachable!(),
        });
    let Some(body_start) = loop_body_start else {
        if let Expr::List(items) = expression {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote" | "#fn" | "fn"))
            {
                return Ok(());
            }
            for item in items.iter_mut().skip(1) {
                rewrite_async_synchronous_loop_returns(item, ready)?;
            }
        }
        return Ok(());
    };
    if has_await(expression) {
        return Ok(());
    }
    let Expr::List(items) = expression else {
        unreachable!()
    };
    for statement in items.iter_mut().skip(body_start) {
        rewrite_async_loop_body_statement(statement, ready)?;
    }
    Ok(())
}

fn rewrite_async_non_loop_returns(expression: &mut Expr, ready: &str) -> Result<(), String> {
    if let Some(return_form) = form(expression, "#return").or_else(|| form(expression, "return")) {
        if return_form.len() != 2 {
            return Err("@async-fn early #return requires exactly one value".into());
        }
        let Expr::List(items) = expression else {
            unreachable!()
        };
        items[1] = Expr::List(vec![Expr::Symbol(ready.into()), items[1].clone()]);
        return Ok(());
    }
    if form(expression, "#let-else").is_some()
        || ["#while", "#while-let", "#for", "#for-range", "#loop"]
            .iter()
            .any(|keyword| form(expression, keyword).is_some())
    {
        return Ok(());
    }
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote" | "#fn" | "fn"))
            {
                return Ok(());
            }
            for item in items.iter_mut().skip(1) {
                rewrite_async_non_loop_returns(item, ready)?;
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                match statement {
                    crate::Statement::Expr(value)
                    | crate::Statement::Return(Some(value))
                    | crate::Statement::BreakValue(value)
                    | crate::Statement::BreakToValue { value, .. } => {
                        rewrite_async_non_loop_returns(value, ready)?;
                    }
                    _ => {}
                }
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => {
            rewrite_async_non_loop_returns(expression, ready)?;
        }
        Expr::Loop(_) | Expr::Quote(_) | Expr::QuasiQuote(_) => {}
        Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::Symbol(_)
        | Expr::At => {}
    }
    Ok(())
}

fn mark_suspending_returns(expression: &mut Expr, result_type: &Expr) {
    fn visit(expression: &mut Expr, result_type: &Expr) {
        let Expr::List(items) = expression else {
            return;
        };
        if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let-else" | "#while" | "#while-let" | "#for" | "#for-range" | "#loop" | "#fn" | "#quote" | "#quasiquote"))
        {
            return;
        }
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#return")
            && items.len() == 2
        {
            *expression = Expr::List(vec![
                Expr::Symbol("#async-terminal-return".into()),
                result_type.clone(),
                items[1].clone(),
            ]);
            return;
        }
        for item in items.iter_mut().skip(1) {
            visit(item, result_type);
        }
    }
    if has_await(expression) {
        visit(expression, result_type);
    }
}

fn rewrite_async_loop_body_statement(statement: &mut Expr, ready: &str) -> Result<(), String> {
    if let Some(return_form) = form(statement, "#return").or_else(|| form(statement, "return")) {
        if return_form.len() != 2 {
            return Err("@async-fn early #return requires exactly one value".into());
        }
        let Expr::List(items) = statement else {
            unreachable!()
        };
        items[1] = Expr::List(vec![Expr::Symbol(ready.into()), items[1].clone()]);
        return Ok(());
    }
    if form(statement, "#block")
        .or_else(|| form(statement, "block"))
        .is_some()
    {
        let Expr::List(items) = statement else {
            unreachable!()
        };
        for child in &mut items[1..] {
            rewrite_async_loop_body_statement(child, ready)?;
        }
        return Ok(());
    }
    if ["#while", "#for", "#for-range", "#loop"]
        .iter()
        .any(|keyword| form(statement, keyword).is_some())
    {
        return rewrite_async_synchronous_loop_returns(statement, ready);
    }
    Ok(())
}

/// Preserve short-circuit evaluation when an awaited right-hand operand is
/// lowered into a condition-specific poll state machine.
fn normalize_short_circuit_await(expression: &mut Expr) {
    let Expr::List(items) = expression else {
        return;
    };
    if items.len() != 3
        || !matches!(items.first(), Some(Expr::Symbol(operator))
            if matches!(operator.as_str(), "#bool.&&" | "bool.&&" | "#bool.||" | "bool.||"))
        || !has_await(&items[2])
    {
        return;
    }
    let is_and = matches!(&items[0], Expr::Symbol(operator) if operator.ends_with("&&"));
    *expression = Expr::List(vec![
        Expr::Symbol("#if".into()),
        items[1].clone(),
        if is_and {
            items[2].clone()
        } else {
            Expr::Symbol("true".into())
        },
        if is_and {
            Expr::Symbol("false".into())
        } else {
            items[2].clone()
        },
    ]);
}

/// Treat a block that only binds an await result and yields that binding as
/// the corresponding explicitly typed await expression. This keeps the block
/// result's declared type available when a conditional chooses between that
/// suspension and another branch.
fn block_await_result(expression: &Expr) -> Option<Expr> {
    let block = form(expression, "#block")?;
    if block.len() < 3 {
        return None;
    }
    let await_binding_index = block.len() - 2;
    if block[1..await_binding_index].iter().any(has_await) {
        return None;
    }
    let binding = form(&block[await_binding_index], "#let")
        .or_else(|| form(&block[await_binding_index], "#let-mut"))?;
    if binding.len() != 4 {
        return None;
    }
    let binding_name = symbol(&binding[1], "binding name").ok()?;
    if !matches!(&block[block.len() - 1], Expr::Symbol(name) if name == binding_name) {
        return None;
    }
    let await_form = form(&binding[3], "#await")?;
    let (result_type, protocol_start) = match await_form.len() {
        6 => (binding[2].clone(), 1),
        7 => (await_form[1].clone(), 2),
        _ => return None,
    };
    if parse_type(Some(&normalize_keywords(result_type.clone()))).is_err() {
        return None;
    }
    let task_index = await_form.len() - 1;
    let task = if await_binding_index == 1 {
        await_form[task_index].clone()
    } else {
        let mut task_block = vec![Expr::Symbol("#block".into())];
        task_block.extend(block[1..await_binding_index].iter().cloned());
        task_block.push(await_form[task_index].clone());
        Expr::List(task_block)
    };
    let mut normalized = vec![Expr::Symbol("#await".into()), result_type];
    normalized.extend(await_form[protocol_start..task_index].iter().cloned());
    normalized.push(task);
    Some(Expr::List(normalized))
}

struct BlockAwait {
    prefix: Vec<Expr>,
    binding: Option<String>,
    mutable_binding: bool,
    result_type: Expr,
    await_expression: Expr,
    assignment: Option<(Expr, usize)>,
    continuation: Expr,
}

fn block_await_continuation(expression: &Expr) -> Option<BlockAwait> {
    let block = form(expression, "#block")?;
    if block.len() < 3 {
        return None;
    }
    let (statement_index, binding, assignment, discard_result) =
        (1..block.len() - 1).find_map(|index| {
            let statement = &block[index];
            if let Some(binding) = form(statement, "#let").or_else(|| form(statement, "#let-mut")) {
                if binding.len() == 4 {
                    if form(&binding[3], "#await").is_some_and(|await_form| await_form.len() == 7) {
                        return Some((index, Some(binding), None, false));
                    }
                }
            }
            if let Some(await_form) = form(statement, "#await") {
                if await_form.len() == 7
                    && parse_type(Some(&normalize_keywords(await_form[1].clone())))
                        .is_ok_and(|ty| async_task_capture_is_copy(&ty))
                {
                    return Some((index, None, None, true));
                }
            }
            let Expr::List(items) = statement else {
                return None;
            };
            let rhs_index = match items.first() {
                Some(Expr::Symbol(head)) if matches!(head.as_str(), "#set" | "set") => 2,
                Some(Expr::Symbol(head))
                    if matches!(
                        head.as_str(),
                        "#set-field"
                            | "set-field"
                            | "#set-index"
                            | "set-index"
                            | "#pin-set-field"
                            | "pin-set-field"
                    ) =>
                {
                    3
                }
                _ => return None,
            };
            let value = items.get(rhs_index)?;
            if !form(value, "#await").is_some_and(|await_form| await_form.len() == 7) {
                return None;
            }
            Some((index, None, Some((statement.clone(), rhs_index)), false))
        })?;
    let await_expression = if let Some(binding) = binding {
        binding[3].clone()
    } else if discard_result {
        block[statement_index].clone()
    } else {
        let (statement, rhs_index) = assignment.as_ref()?;
        let Expr::List(items) = statement else {
            return None;
        };
        items.get(*rhs_index)?.clone()
    };
    let await_form = form(&await_expression, "#await")?;
    let result_type = if let Some(binding) = binding {
        binding[2].clone()
    } else {
        await_form[1].clone()
    };
    let parsed_result_type = parse_type(Some(&normalize_keywords(result_type.clone()))).ok()?;
    if discard_result && !async_task_capture_is_copy(&parsed_result_type) {
        return None;
    }
    if block[1..statement_index].iter().any(has_await) {
        return None;
    }
    let continuation = if statement_index + 1 == block.len() - 1 {
        block[block.len() - 1].clone()
    } else {
        Expr::List(
            std::iter::once(Expr::Symbol("#block".into()))
                .chain(block[statement_index + 1..].iter().cloned())
                .collect(),
        )
    };
    let binding = match binding {
        Some(binding) => Some(symbol(&binding[1], "binding name").ok()?.to_owned()),
        None => None,
    };
    Some(BlockAwait {
        prefix: block[1..statement_index].to_vec(),
        binding,
        mutable_binding: form(&block[statement_index], "#let-mut").is_some(),
        result_type,
        await_expression,
        assignment,
        continuation,
    })
}

fn replace_await_local(expression: &mut Expr, name: &str, replacement: &str) {
    match expression {
        Expr::Symbol(symbol) if symbol == name => *symbol = replacement.to_owned(),
        Expr::List(items) => {
            let Some(Expr::Symbol(head)) = items.first() else {
                for item in items {
                    replace_await_local(item, name, replacement);
                }
                return;
            };
            match head.as_str() {
                "#quote" | "quote" | "#quasiquote" | "quasiquote" => {}
                "#call" | "call" if items.len() == 3 => {
                    if let Expr::List(arguments) = &mut items[2] {
                        for argument in arguments {
                            if let Expr::List(pair) = argument {
                                if let Some(value) = pair.get_mut(1) {
                                    replace_await_local(value, name, replacement);
                                }
                            }
                        }
                    }
                }
                "#struct-literal" | "struct-literal" if items.len() == 3 => {
                    if let Expr::List(fields) = &mut items[2] {
                        for field in fields {
                            if let Expr::List(pair) = field {
                                if let Some(value) = pair.get_mut(1) {
                                    replace_await_local(value, name, replacement);
                                }
                            }
                        }
                    }
                }
                "#get" | "get" | "#get-field" | "get-field" if items.len() >= 3 => {
                    replace_await_local(&mut items[1], name, replacement);
                }
                "#set-field" | "set-field" | "#pin-set-field" | "pin-set-field"
                    if items.len() >= 4 =>
                {
                    replace_await_local(&mut items[1], name, replacement);
                    for value in items.iter_mut().skip(3) {
                        replace_await_local(value, name, replacement);
                    }
                }
                "#index" | "index" | "#slice-idx" | "slice-idx" if items.len() >= 3 => {
                    for value in items.iter_mut().skip(1) {
                        replace_await_local(value, name, replacement);
                    }
                }
                "#set-index" | "set-index" if items.len() >= 4 => {
                    for value in items.iter_mut().skip(1) {
                        replace_await_local(value, name, replacement);
                    }
                }
                "#as" | "as" | "#cast" | "cast" if items.len() == 3 => {
                    replace_await_local(&mut items[1], name, replacement);
                }
                "#array" | "array" | "#array-of" | "array-of" | "#tuple" | "tuple" => {
                    let start = if items
                        .get(1)
                        .is_some_and(|ty| parse_type(Some(&normalize_keywords(ty.clone()))).is_ok())
                    {
                        2
                    } else {
                        1
                    };
                    for value in items.iter_mut().skip(start) {
                        replace_await_local(value, name, replacement);
                    }
                }
                "#case" | "case" if items.len() >= 3 => {
                    for value in items.iter_mut().skip(2) {
                        replace_await_local(value, name, replacement);
                    }
                }
                "#let" | "let" | "#let-mut" | "let-mut" if items.len() == 4 => {
                    replace_await_local(&mut items[3], name, replacement);
                }
                "#if" | "if" | "#match" | "match" | "#block" | "block" => {
                    for value in items.iter_mut().skip(1) {
                        replace_await_local(value, name, replacement);
                    }
                }
                _ => {
                    for value in items.iter_mut().skip(1) {
                        replace_await_local(value, name, replacement);
                    }
                }
            }
        }
        _ => {}
    }
}

#[derive(Clone, PartialEq)]
struct AwaitProtocol {
    result_type: Expr,
    child_type: Expr,
    pending: Expr,
    ready: Expr,
    poll: Expr,
}

fn conditional_await(expression: &Expr) -> Result<Option<(AwaitProtocol, Expr)>, String> {
    if let Some(normalized) = block_await_result(expression) {
        return conditional_await(&normalized);
    }
    if let Some(await_form) = form(expression, "#await") {
        if await_form.len() != 7 {
            return Err(
                "nested #await requires an explicit result type: (#await Type Child Pending Ready poll task)"
                    .into(),
            );
        }
        parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
        parse_type(Some(&normalize_keywords(await_form[2].clone())))?;
        return Ok(Some((
            AwaitProtocol {
                result_type: await_form[1].clone(),
                child_type: await_form[2].clone(),
                pending: await_form[3].clone(),
                ready: await_form[4].clone(),
                poll: await_form[5].clone(),
            },
            await_form[6].clone(),
        )));
    }

    if let Some(items) = form(expression, "#if") {
        if items.len() != 4 {
            return Ok(None);
        }
        let then_await = conditional_await(&items[2])?;
        let else_await = conditional_await(&items[3])?;
        let (Some((protocol, then_task)), Some((else_protocol, else_task))) =
            (then_await, else_await)
        else {
            return Ok(None);
        };
        if protocol != else_protocol {
            return Ok(None);
        }
        return Ok(Some((
            protocol,
            Expr::List(vec![
                items[0].clone(),
                items[1].clone(),
                then_task,
                else_task,
            ]),
        )));
    }

    if let Some(items) = form(expression, "#match") {
        if items.len() < 3 {
            return Ok(None);
        }
        let mut protocol: Option<AwaitProtocol> = None;
        let mut task_arms = Vec::with_capacity(items.len());
        task_arms.push(items[0].clone());
        task_arms.push(items[1].clone());
        for arm in &items[2..] {
            let Some(case) = form(arm, "#case") else {
                return Ok(None);
            };
            let body_index = match case.len() {
                3 => 2,
                4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                _ => return Ok(None),
            };
            if case.len() == 4 && has_await(&case[2]) {
                return Ok(None);
            }
            let Some((case_protocol, task)) = conditional_await(&case[body_index])? else {
                return Ok(None);
            };
            if protocol
                .as_ref()
                .is_some_and(|expected| expected != &case_protocol)
            {
                return Ok(None);
            }
            protocol = Some(case_protocol);
            let mut task_arm = vec![case[0].clone(), case[1].clone()];
            if body_index == 3 {
                task_arm.push(case[2].clone());
            }
            task_arm.push(task);
            task_arms.push(Expr::List(task_arm));
        }
        if let Some(protocol) = protocol {
            return Ok(Some((protocol, Expr::List(task_arms))));
        }
    }
    Ok(None)
}

fn conditional_block_continuation(
    expression: &Expr,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(AwaitProtocol, Expr, String)>, String> {
    let Some(block) = block_await_continuation(expression) else {
        return Ok(None);
    };
    if block.binding.is_none()
        || block.assignment.is_some()
        || contains_loop_control(&block.continuation)
        || contains_return(&block.continuation)
    {
        return Ok(None);
    }
    let await_local = block.binding.as_deref().expect("validated binding");
    let mut continuation_names = HashSet::new();
    collect_value_names(&block.continuation, &mut continuation_names);
    // The helper constructs the first child as well as running its Ready
    // continuation. Capture only values used by either, not every prefix
    // declaration: a linear prefix owner may already have been consumed.
    collect_value_names(&block.await_expression, &mut continuation_names);
    continuation_names.remove(await_local);
    continuation_names.remove("true");
    continuation_names.remove("false");
    let mut local_bindings = HashSet::new();
    collect_local_binding_names(&block.continuation, &mut local_bindings);
    for local in local_bindings {
        continuation_names.remove(&local);
    }
    let mut prefix_bindings = Vec::<(Binding, Expr)>::new();
    for statement in &block.prefix {
        if has_await(statement) || contains_loop_control(statement) || contains_return(statement) {
            return Err(
                "@async-fn conditional await adapter prefixes cannot suspend or transfer control"
                    .into(),
            );
        }
        if let Some(locals) = current_local_bindings(statement)? {
            for local in locals {
                if continuation_names.remove(&local.name) {
                    let ty = crate::parse(&local.ty)?.remove(0).expr;
                    prefix_bindings.push((local, ty));
                }
            }
        }
    }
    let mut captured_bindings = continuation_names
        .iter()
        .filter_map(|name| known.get(name).cloned())
        .collect::<Vec<_>>();
    captured_bindings.sort_by(|left, right| left.name.cmp(&right.name));
    for binding in &captured_bindings {
        continuation_names.remove(&binding.name);
    }
    if let Some(name) = continuation_names.iter().next() {
        return Err(format!(
            "@async-fn conditional await continuation captures outer local '{name}'; bind it inside the branch before suspension"
        ));
    }
    let first_await = form(&block.await_expression, "#await")
        .ok_or_else(|| "@async-fn conditional block requires a direct #await".to_owned())?;
    if first_await.len() != 7 {
        return Err(
            "nested #await requires an explicit result type: (#await Type Child Pending Ready poll task)"
                .into(),
        );
    }
    let base = fresh_async_name(source, next_name);
    let function_name = format!("{base}-branch-function");
    let frame = format!("{base}-branch-frame");
    let poll_result = format!("{base}-branch-poll-result");
    let pending = format!("{base}-branch-pending");
    let ready = format!("{base}-branch-ready");
    let poll = format!("{base}-branch-poll");
    let mut parameters = Vec::new();
    let mut call_arguments = Vec::new();
    for binding in &captured_bindings {
        let name = Expr::Symbol(binding.name.clone());
        let ty = crate::parse(&binding.ty)?
            .into_iter()
            .next()
            .ok_or_else(|| "@async-fn captured binding type is empty".to_owned())?
            .expr;
        parameters.push(Expr::List(if binding.mutable {
            vec![Expr::Symbol("#mut".into()), name.clone(), ty]
        } else {
            vec![name.clone(), ty]
        }));
        call_arguments.push(Expr::Symbol(":".into()));
        call_arguments.push(name.clone());
        call_arguments.push(name);
    }
    for (local, ty) in &prefix_bindings {
        let name = Expr::Symbol(local.name.clone());
        parameters.push(Expr::List(if local.mutable {
            vec![Expr::Symbol("#mut".into()), name.clone(), ty.clone()]
        } else {
            vec![name.clone(), ty.clone()]
        }));
        call_arguments.push(Expr::Symbol(":".into()));
        call_arguments.push(name.clone());
        call_arguments.push(name);
    }
    let normalized_await = Expr::List(
        std::iter::once(Expr::Symbol("#await".into()))
            .chain(first_await[2..].iter().cloned())
            .collect(),
    );
    let first_binding = Expr::List(vec![
        Expr::Symbol(if block.mutable_binding {
            "#let-mut".into()
        } else {
            "#let".into()
        }),
        Expr::Symbol(await_local.to_owned()),
        block.result_type.clone(),
        normalized_await,
    ]);
    let continuation_result_type =
        async_expression_type(expression, known).unwrap_or_else(|| block.result_type.clone());
    let function = Expr::List(vec![
        Expr::Symbol("#fn".into()),
        Expr::Symbol(function_name.clone()),
        Expr::List(parameters),
        continuation_result_type.clone(),
        first_binding,
        Expr::List(vec![Expr::Symbol("#return".into()), block.continuation]),
    ]);
    let waker_expression = crate::parse(waker)?
        .into_iter()
        .next()
        .ok_or_else(|| "@async-fn waker type is empty".to_owned())?
        .expr;
    let invocation = Expr::List(vec![
        Expr::At,
        Expr::Symbol("async-fn".into()),
        Expr::List(vec![
            Expr::Symbol(frame.clone()),
            Expr::Symbol(poll_result.clone()),
            Expr::Symbol(pending.clone()),
            Expr::Symbol(ready.clone()),
            Expr::Symbol(poll.clone()),
        ]),
        waker_expression,
        function,
    ]);
    let helper = generated_source(&invocation)?;
    let mut call = vec![Expr::Symbol("#call".into()), Expr::Symbol(function_name)];
    call.push(Expr::List(call_arguments));
    let mut task = vec![Expr::Symbol("#block".into())];
    task.extend(block.prefix);
    task.push(Expr::List(call));
    let task = if task.len() == 2 {
        task.pop().expect("branch task call")
    } else {
        Expr::List(task)
    };
    Ok(Some((
        AwaitProtocol {
            result_type: continuation_result_type,
            child_type: Expr::Symbol(frame),
            pending: Expr::Symbol(pending),
            ready: Expr::Symbol(ready),
            poll: Expr::Symbol(poll),
        },
        task,
        helper,
    )))
}

fn first_async_await(expression: &Expr) -> Option<&[Expr]> {
    if let Some(await_form) = form(expression, "#await") {
        return Some(await_form);
    }
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
            {
                return None;
            }
            items.iter().find_map(first_async_await)
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            statements.iter().find_map(|statement| match statement {
                crate::Statement::Expr(value)
                | crate::Statement::Return(Some(value))
                | crate::Statement::BreakValue(value)
                | crate::Statement::BreakToValue { value, .. } => first_async_await(value),
                _ => None,
            })
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => first_async_await(expression),
        _ => None,
    }
}

fn has_suspending_await_input(expression: &Expr) -> bool {
    let Expr::List(items) = expression else {
        return false;
    };
    if matches!(items.first(), Some(Expr::Symbol(head))
        if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
    {
        return false;
    }
    if form(expression, "#await").is_some() && items.last().is_some_and(has_await) {
        return true;
    }
    items.iter().skip(1).any(has_suspending_await_input)
}

/// Arm-local captures obtain their types from the scrutinee declaration, not
/// from names found in a branch body. Keep them out of every other arm's scope.
fn async_pattern_scope(
    pattern: &Expr,
    input_type: Option<&str>,
    known: &HashMap<String, Binding>,
) -> HashMap<String, Binding> {
    let mut scope = known.clone();
    if let Some(ty) = input_type {
        let bindings = ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
            let stack = stack.borrow();
            let mut bindings = Vec::new();
            collect_enum_pattern_bindings(pattern, ty, stack.last()?, &mut bindings).ok()?;
            Some(bindings)
        });
        for (name, ty) in bindings.into_iter().flatten() {
            scope.insert(
                name.clone(),
                Binding {
                    name,
                    ty,
                    mutable: false,
                },
            );
        }
    }
    scope
}

/// Select generated storage from explicit declarations and builtin contracts.
/// This is not a replacement for expression checking: arity, operand types,
/// ownership and agreement between branches are checked on the emitted body.
fn async_expression_type(expression: &Expr, known: &HashMap<String, Binding>) -> Option<Expr> {
    fn source_type(source: &str) -> Option<Expr> {
        crate::parse(source)
            .ok()?
            .into_iter()
            .next()
            .map(|source| source.expr)
    }
    fn constructor_type(variant: &str) -> Option<Expr> {
        ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
            let stack = stack.borrow();
            let environment = stack.last()?;
            environment.enums.iter().find_map(|(name, variants)| {
                variants
                    .contains_key(variant)
                    .then(|| Expr::Symbol(name.clone()))
            })
        })
    }
    match expression {
        Expr::Symbol(name) if matches!(name.as_str(), "true" | "false") => {
            Some(Expr::Symbol("bool".into()))
        }
        Expr::Symbol(name) => known
            .get(name)
            .and_then(|binding| source_type(&binding.ty))
            .or_else(|| constructor_type(name)),
        Expr::Char(_) => Some(Expr::Symbol("char".into())),
        Expr::List(items) if items.is_empty() => Some(Expr::List(Vec::new())),
        Expr::List(items) => {
            let Expr::Symbol(head) = items.first()? else {
                return None;
            };
            let head = head.strip_prefix('#').unwrap_or(head);
            if let Some(operation) = crate::typed_body::NumericOperation::parse(head) {
                use crate::typed_body::NumericOpcode;
                let ty = match operation.operation {
                    NumericOpcode::Less
                    | NumericOpcode::LessEqual
                    | NumericOpcode::Greater
                    | NumericOpcode::GreaterEqual
                    | NumericOpcode::Equal
                    | NumericOpcode::NotEqual => Type::Bool,
                    _ => operation.operand_type,
                };
                return source_type(&crate::type_source(&ty));
            }
            match head {
                "literal" | "struct-literal" | "tuple" | "array-of" | "await" => {
                    items.get(1).cloned()
                }
                "as" => items.get(2).cloned(),
                "call" => {
                    let Expr::Symbol(function) = items.get(1)? else {
                        return None;
                    };
                    ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
                        source_type(stack.borrow().last()?.function_results.get(function)?)
                    })
                }
                "clone" | "unsafe" => async_expression_type(items.last()?, known),
                "borrow" | "borrow-mut" if items.len() == 2 => Some(Expr::List(vec![
                    Expr::Symbol(if head == "borrow" { "#ref" } else { "#ref-mut" }.into()),
                    async_expression_type(&items[1], known)?,
                ])),
                "deref" => {
                    let ty = async_expression_type(items.get(1)?, known)?;
                    let Type::Reference { target, .. } =
                        parse_type(Some(&normalize_keywords(ty))).ok()?
                    else {
                        return None;
                    };
                    source_type(&crate::type_source(&target))
                }
                "get" => {
                    let ty = async_expression_type(items.get(1)?, known)?;
                    let ty = parse_type(Some(&normalize_keywords(ty))).ok()?;
                    let ty = match ty {
                        Type::Reference { target, .. } | Type::PinnedReference { target, .. } => {
                            *target
                        }
                        other => other,
                    };
                    match (ty, items.get(2)?) {
                        (Type::Named(name), Expr::Symbol(field)) => {
                            source_type(&struct_field_type(&name, field)?)
                        }
                        (Type::Tuple(fields), Expr::Integer(index)) if *index >= 0 => source_type(
                            &crate::type_source(fields.get(usize::try_from(*index).ok()?)?),
                        ),
                        _ => None,
                    }
                }
                "if" => items
                    .get(2..)?
                    .iter()
                    .find_map(|branch| async_expression_type(branch, known)),
                "match" => {
                    let input_type = async_expression_type(items.get(1)?, known)
                        .and_then(|ty| expression_source(&ty).ok());
                    items.get(2..)?.iter().find_map(|arm| {
                        let Expr::List(case) = arm else {
                            return None;
                        };
                        let scope = async_pattern_scope(case.get(1)?, input_type.as_deref(), known);
                        async_expression_type(case.last()?, &scope)
                    })
                }
                "block" => {
                    let mut scope = known.clone();
                    for statement in items.iter().skip(1).take(items.len().saturating_sub(2)) {
                        if let Some(locals) = current_local_bindings(statement).ok()? {
                            for local in locals {
                                scope.insert(local.name.clone(), local);
                            }
                        }
                    }
                    async_expression_type(items.last()?, &scope)
                }
                _ => constructor_type(head),
            }
        }
        _ => None,
    }
}

fn async_loop_break_value(
    expression: &Expr,
    known: &HashMap<String, Binding>,
) -> Option<(Expr, Expr)> {
    fn collect_declared_types(expression: &Expr, known: &mut HashMap<String, Binding>) {
        let Expr::List(items) = expression else {
            return;
        };
        if matches!(items.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote" | "#fn" | "fn"))
        {
            return;
        }
        if let Ok(Some(locals)) = current_local_bindings(expression) {
            for local in locals {
                known.insert(local.name.clone(), local);
            }
        }
        for item in items.iter().skip(1) {
            collect_declared_types(item, known);
        }
    }

    let loop_items = form(expression, "#loop")?;
    let mut loop_known = known.clone();
    for statement in &loop_items[1..] {
        collect_declared_types(statement, &mut loop_known);
    }
    let value_type = |value: &Expr| async_expression_type(value, &loop_known);
    fn find_break(
        expression: &Expr,
        value_type: &impl Fn(&Expr) -> Option<Expr>,
    ) -> Option<(Expr, Expr)> {
        let Expr::List(items) = expression else {
            return None;
        };
        if matches!(items.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#loop" | "#while" | "#while-let" | "#for" | "#for-range"
                | "#quote" | "quote" | "#quasiquote" | "quasiquote" | "#fn" | "fn"))
        {
            return None;
        }
        if let Some(items) = form(expression, "#break") {
            if items.len() == 2 {
                return value_type(&items[1]).map(|ty| (items[1].clone(), ty));
            }
            return None;
        }
        items
            .iter()
            .skip(1)
            .find_map(|child| find_break(child, value_type))
    }
    // Prefer the old terminal anchor when present, preserving existing types.
    // Otherwise any explicitly typed exit of this loop can supply the schema;
    // ordinary checking validates the other payloads against it.
    loop_items
        .last()
        .and_then(|last| {
            let terminal = form(last, "#break")?;
            (terminal.len() == 2)
                .then(|| &terminal[1])
                .and_then(|value| value_type(value).map(|ty| (value.clone(), ty)))
        })
        .or_else(|| {
            loop_items
                .iter()
                .skip(1)
                .find_map(|body| find_break(body, &value_type))
        })
}

fn rewrite_async_loop_break_values(
    expression: &mut Expr,
    break_value: &Expr,
    known: &HashMap<String, Binding>,
    result_name: &str,
    result_variant: &str,
) -> bool {
    let Some(_) = form(expression, "#loop") else {
        return false;
    };
    let Some((anchor, _)) = async_loop_break_value(expression, known) else {
        return false;
    };
    if anchor != *break_value {
        return false;
    }
    fn rewrite_breaks(expression: &mut Expr, result_name: &str, result_variant: &str) {
        let Expr::List(items) = expression else {
            return;
        };
        if matches!(items.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#loop" | "#while" | "#while-let" | "#for" | "#for-range"
                | "#quote" | "quote" | "#quasiquote" | "quasiquote" | "#fn" | "fn"))
        {
            // These forms establish a different control-flow or syntax owner.
            return;
        }
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#break") && items.len() == 2
        {
            let value = items[1].clone();
            *expression = Expr::List(vec![
                Expr::Symbol("#block".into()),
                Expr::List(vec![
                    Expr::Symbol("#forget".into()),
                    Expr::Symbol(result_name.into()),
                ]),
                Expr::List(vec![
                    Expr::Symbol("#set".into()),
                    Expr::Symbol(result_name.into()),
                    Expr::List(vec![Expr::Symbol(result_variant.into()), value]),
                ]),
                Expr::List(vec![Expr::Symbol("#break".into())]),
            ]);
            return;
        }
        for child in items.iter_mut().skip(1) {
            rewrite_breaks(child, result_name, result_variant);
        }
    }
    let Expr::List(loop_items) = expression else {
        unreachable!()
    };
    for statement in loop_items.iter_mut().skip(1) {
        rewrite_breaks(statement, result_name, result_variant);
    }
    true
}

fn conditional_value_expression_task(
    expression: &Expr,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(AwaitProtocol, Expr, String)>, String> {
    if !has_await(expression) {
        return Ok(None);
    }
    let await_form = first_async_await(expression)
        .ok_or_else(|| "@async-fn could not locate conditional branch #await".to_owned())?;
    if await_form.len() != 7 {
        return Err(
            "nested #await requires an explicit result type: (#await Type Child Pending Ready poll task)"
                .into(),
        );
    }
    parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
    let mut captures = HashSet::new();
    collect_value_names(expression, &mut captures);
    let mut locals = HashSet::new();
    collect_local_binding_names(expression, &mut locals);
    for local in locals {
        captures.remove(&local);
    }
    captures.remove("true");
    captures.remove("false");

    // The generated async helper can represent enclosing bindings directly.
    // Passing them as named, typed arguments keeps the source explicit and
    // lets the ordinary ownership/borrow checker validate the transfer.
    let mut captured_parameters = captures
        .iter()
        .filter_map(|name| known.get(name).cloned())
        .collect::<Vec<_>>();
    captured_parameters.sort_by(|left, right| left.name.cmp(&right.name));
    for parameter in &captured_parameters {
        captures.remove(&parameter.name);
    }
    // Unknown names here may be enum constructors or global declarations, not
    // lexical captures. Keep them in the generated body for ordinary name
    // resolution; any unavailable local is still rejected when the generated
    // function is typechecked. The language's no-shadowing rule prevents a
    // missing local from silently resolving to a same-named global.

    let base = fresh_async_name(source, next_name);
    let function_name = format!("{base}-expression-function");
    let frame = format!("{base}-expression-frame");
    let poll_result = format!("{base}-expression-poll-result");
    let pending = format!("{base}-expression-pending");
    let ready = format!("{base}-expression-ready");
    let poll = format!("{base}-expression-poll");
    let mut helper_parameters = Vec::with_capacity(captured_parameters.len());
    let mut call_arguments = Vec::new();
    for parameter in &captured_parameters {
        let name = Expr::Symbol(parameter.name.clone());
        let ty = crate::parse(&parameter.ty)?
            .into_iter()
            .next()
            .ok_or_else(|| "@async-fn captured parameter type is empty".to_owned())?
            .expr;
        helper_parameters.push(Expr::List(if parameter.mutable {
            vec![Expr::Symbol("#mut".into()), name.clone(), ty]
        } else {
            vec![name.clone(), ty]
        }));
        call_arguments.push(Expr::Symbol(":".into()));
        call_arguments.push(Expr::Symbol(parameter.name.clone()));
        call_arguments.push(Expr::Symbol(parameter.name.clone()));
    }
    let enclosing_return_type = async_terminal_return_type(expression);
    let value_loop = if enclosing_return_type.is_none() {
        async_loop_break_value(expression, known)
    } else {
        None
    };
    let block_ends_in_loop = form(expression, "#block")
        .and_then(|block| block.last())
        .is_some_and(|tail| {
            form(tail, "#loop").is_some()
                || form(tail, "#while").is_some()
                || form(tail, "#while-let").is_some()
                || form(tail, "#for").is_some()
                || form(tail, "#for-range").is_some()
        });
    let standalone_loop = (form(expression, "#loop").is_some()
        || form(expression, "#while").is_some()
        || form(expression, "#while-let").is_some()
        || form(expression, "#for").is_some()
        || form(expression, "#for-range").is_some()
        || block_ends_in_loop)
        && enclosing_return_type.is_none();
    let unit_result_type = Expr::List(Vec::new());
    let expression_result_type = async_expression_type(expression, known);
    let function_result_type = if let Some((_, result_type)) = &value_loop {
        result_type
    } else if standalone_loop {
        &unit_result_type
    } else {
        enclosing_return_type
            .as_ref()
            .or(expression_result_type.as_ref())
            .unwrap_or(&await_form[1])
    };
    let mut function = vec![
        Expr::Symbol("#fn".into()),
        Expr::Symbol(function_name.clone()),
        Expr::List(helper_parameters),
        function_result_type.clone(),
    ];
    let mut loop_result_declaration = None;
    if let Some((break_value, result_type)) = &value_loop {
        let state_type = format!("{base}-loop-result-state");
        let empty_variant = format!("{base}-loop-result-empty");
        let filled_variant = format!("{base}-loop-result-filled");
        let state_name = format!("{base}-loop-result");
        let result_name = format!("{base}-loop-result-value");
        loop_result_declaration = Some(Expr::List(vec![
            Expr::Symbol("#enum".into()),
            Expr::Symbol(state_type.clone()),
            Expr::List(vec![
                Expr::List(vec![Expr::Symbol(empty_variant.clone())]),
                Expr::List(vec![
                    Expr::Symbol(filled_variant.clone()),
                    result_type.clone(),
                ]),
            ]),
        ]));
        function.push(Expr::List(vec![
            Expr::Symbol("#let-mut".into()),
            Expr::Symbol(state_name.clone()),
            Expr::Symbol(state_type),
            Expr::Symbol(empty_variant.clone()),
        ]));
        let mut loop_expression = expression.clone();
        if !rewrite_async_loop_break_values(
            &mut loop_expression,
            break_value,
            known,
            &state_name,
            &filled_variant,
        ) {
            return Ok(None);
        }
        normalize_async_loop_await_types(&mut loop_expression)?;
        function.push(loop_expression);
        function.push(Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(result_name.clone()),
            result_type.clone(),
            Expr::List(vec![
                Expr::Symbol("#match".into()),
                Expr::Symbol(state_name),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::Symbol(empty_variant),
                    Expr::List(vec![Expr::Symbol("#unreachable".into())]),
                ]),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::List(vec![
                        Expr::Symbol(filled_variant),
                        Expr::Symbol(result_name.clone()),
                    ]),
                    Expr::Symbol(result_name.clone()),
                ]),
            ]),
        ]));
        function.push(Expr::List(vec![
            Expr::Symbol("#return".into()),
            Expr::Symbol(result_name),
        ]));
    } else if standalone_loop {
        let mut loop_expression = expression.clone();
        normalize_async_loop_await_types(&mut loop_expression)?;
        if let Some(block) = form(&loop_expression, "#block") {
            function.extend(block[1..].iter().cloned());
        } else {
            function.push(loop_expression);
        }
        function.push(Expr::List(vec![
            Expr::Symbol("#return".into()),
            Expr::List(Vec::new()),
        ]));
    } else if let Some(block) = form(expression, "#block") {
        if block.len() < 2 {
            return Ok(None);
        }
        if enclosing_return_type.is_some() {
            if block[1..block.len() - 1].iter().any(contains_return) {
                return Ok(None);
            }
            for statement in &block[1..] {
                let mut statement = statement.clone();
                lower_async_terminal_return_markers(&mut statement)?;
                function.push(statement);
            }
            if !function
                .last()
                .is_some_and(|last| form(last, "#return").is_some())
            {
                function.push(Expr::List(vec![
                    Expr::Symbol("#return".into()),
                    Expr::List(vec![Expr::Symbol("#unreachable".into())]),
                ]));
            }
        } else {
            function.extend(block[1..block.len() - 1].iter().cloned());
            let result_name = fresh_async_name(source, next_name);
            function.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                function_result_type.clone(),
                block.last().expect("nonempty value block").clone(),
            ]));
            function.push(Expr::List(vec![
                Expr::Symbol("#return".into()),
                Expr::Symbol(result_name),
            ]));
        }
    } else {
        let mut returned_expression = expression.clone();
        lower_async_terminal_return_markers(&mut returned_expression)?;
        if enclosing_return_type.is_some() {
            function.push(returned_expression);
            if !function
                .last()
                .is_some_and(|last| form(last, "#return").is_some())
            {
                // Conditional terminal returns still need the ordinary
                // function grammar's explicit final return. Every reachable
                // branch already returns; this tail must never execute.
                function.push(Expr::List(vec![
                    Expr::Symbol("#return".into()),
                    Expr::List(vec![Expr::Symbol("#unreachable".into())]),
                ]));
            }
        } else {
            function.push(Expr::List(vec![
                Expr::Symbol("#return".into()),
                returned_expression,
            ]));
        }
    }
    let function = Expr::List(function);
    let waker_expression = crate::parse(waker)?
        .into_iter()
        .next()
        .ok_or_else(|| "@async-fn waker type is empty".to_owned())?
        .expr;
    let invocation = Expr::List(vec![
        Expr::At,
        Expr::Symbol("async-fn".into()),
        Expr::List(vec![
            Expr::Symbol(frame.clone()),
            Expr::Symbol(poll_result.clone()),
            Expr::Symbol(pending.clone()),
            Expr::Symbol(ready.clone()),
            Expr::Symbol(poll.clone()),
        ]),
        waker_expression,
        function,
    ]);
    let mut helper = String::new();
    if let Some(declaration) = loop_result_declaration {
        helper.push_str(&expression_source(&declaration)?);
        helper.push('\n');
    }
    helper.push_str(&generated_source(&invocation)?);
    let task = Expr::List(vec![
        Expr::Symbol("#call".into()),
        Expr::Symbol(function_name),
        Expr::List(call_arguments),
    ]);
    Ok(Some((
        AwaitProtocol {
            result_type: function_result_type.clone(),
            child_type: Expr::Symbol(frame),
            pending: Expr::Symbol(pending),
            ready: Expr::Symbol(ready),
            poll: Expr::Symbol(poll),
        },
        task,
        helper,
    )))
}

fn fresh_async_name(source: &str, next_name: &mut usize) -> String {
    let namespace = source
        .split_once("(#fn ")
        .and_then(|(_, rest)| rest.split_whitespace().next())
        .unwrap_or("function");
    loop {
        let name = format!("lim.async.{namespace}.choice-{}", *next_name);
        *next_name += 1;
        if !source.contains(&name) {
            return name;
        }
    }
}

/// Convert conditional branches that either await the same concrete child
/// protocol or immediately produce its result into one concrete child task.
fn conditional_await_with_immediate(
    expression: &Expr,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(AwaitProtocol, Expr, String)>, String> {
    fn immediate_terminal_value(expression: &Expr) -> Expr {
        if let Some(items) = form(expression, "#async-terminal-return") {
            if items.len() == 3 {
                return items[2].clone();
            }
        }
        match expression {
            Expr::List(items) => Expr::List(items.iter().map(immediate_terminal_value).collect()),
            _ => expression.clone(),
        }
    }
    let mut branches = Vec::<(Option<AwaitProtocol>, Expr)>::new();
    let mut branch_helpers = Vec::new();
    let condition_or_scrutinee;
    let is_if;
    if let Some(items) = form(expression, "#if") {
        if items.len() != 4 {
            return Ok(None);
        }
        condition_or_scrutinee = items[1].clone();
        is_if = true;
        for branch in &items[2..] {
            let lowered = conditional_await(branch)?;
            if let Some((protocol, task)) = lowered {
                branches.push((Some(protocol), task));
            } else if let Some((protocol, task, helper)) =
                conditional_block_continuation(branch, known, source, next_name, waker)?
            {
                branches.push((Some(protocol), task));
                branch_helpers.push(helper);
            } else if let Some((protocol, task, helper)) =
                conditional_value_expression_task(branch, known, source, next_name, waker)?
            {
                branches.push((Some(protocol), task));
                branch_helpers.push(helper);
            } else if !has_await(branch) {
                branches.push((None, immediate_terminal_value(branch)));
            } else {
                return Ok(None);
            }
        }
    } else if let Some(items) = form(expression, "#match") {
        if items.len() < 3 {
            return Ok(None);
        }
        condition_or_scrutinee = items[1].clone();
        is_if = false;
        let input_type =
            async_expression_type(&items[1], known).and_then(|ty| expression_source(&ty).ok());
        for arm in &items[2..] {
            let Some(case) = form(arm, "#case") else {
                return Ok(None);
            };
            let body_index = match case.len() {
                3 => 2,
                4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                _ => return Ok(None),
            };
            if case.len() == 4 && has_await(&case[2]) {
                return Ok(None);
            }
            let branch_known = async_pattern_scope(&case[1], input_type.as_deref(), known);
            let lowered = conditional_await(&case[body_index])?;
            if let Some((protocol, task)) = lowered {
                let mut task_arm = vec![Expr::Symbol("#case".into()), case[1].clone()];
                if body_index == 3 {
                    task_arm.push(case[2].clone());
                }
                task_arm.push(task);
                branches.push((Some(protocol), Expr::List(task_arm)));
            } else if let Some((protocol, task, helper)) = conditional_block_continuation(
                &case[body_index],
                &branch_known,
                source,
                next_name,
                waker,
            )? {
                let mut task_arm = vec![Expr::Symbol("#case".into()), case[1].clone()];
                if body_index == 3 {
                    task_arm.push(case[2].clone());
                }
                task_arm.push(task);
                branches.push((Some(protocol), Expr::List(task_arm)));
                branch_helpers.push(helper);
            } else if let Some((protocol, task, helper)) = conditional_value_expression_task(
                &case[body_index],
                &branch_known,
                source,
                next_name,
                waker,
            )? {
                let mut task_arm = vec![Expr::Symbol("#case".into()), case[1].clone()];
                if body_index == 3 {
                    task_arm.push(case[2].clone());
                }
                task_arm.push(task);
                branches.push((Some(protocol), Expr::List(task_arm)));
                branch_helpers.push(helper);
            } else if !has_await(&case[body_index]) {
                branches.push((None, immediate_terminal_value(arm)));
            } else {
                return Ok(None);
            }
        }
    } else {
        return Ok(None);
    }
    let Some(protocol) = branches.iter().find_map(|(protocol, _)| protocol.clone()) else {
        return Ok(None);
    };
    if branches.iter().any(|(branch_protocol, _)| {
        branch_protocol
            .as_ref()
            .is_some_and(|branch_protocol| branch_protocol.result_type != protocol.result_type)
    }) {
        return Err("conditional #await branches must produce the same result type".into());
    }
    if branches
        .iter()
        .all(|(branch_protocol, _)| branch_protocol.is_some())
        && branches
            .iter()
            .all(|(branch_protocol, _)| branch_protocol.as_ref() == Some(&protocol))
    {
        return Ok(None);
    }

    let choice_task = fresh_async_name(source, next_name);
    let choice_wait = format!("{choice_task}-waiting");
    let choice_done = format!("{choice_task}-ready");
    let choice_poll_result = format!("{choice_task}-poll-result");
    let choice_pending = format!("{choice_task}-pending");
    let choice_ready = format!("{choice_task}-complete");
    let choice_poll = format!("{choice_task}-poll");
    let result_type = expression_source(&protocol.result_type)?;
    let mut choice_variants = Vec::new();
    let mut poll_arms = Vec::new();
    let mut branch_waits = Vec::with_capacity(branches.len());
    for (index, (branch_protocol, _)) in branches.iter().enumerate() {
        if let Some(branch_protocol) = branch_protocol {
            let variant = format!("{choice_wait}-{index}");
            let child_type = expression_source(&branch_protocol.child_type)?;
            let child_pending = expression_source(&branch_protocol.pending)?;
            let child_ready = expression_source(&branch_protocol.ready)?;
            let child_poll = expression_source(&branch_protocol.poll)?;
            choice_variants.push(format!("({variant} {child_type})"));
            poll_arms.push(format!(
                "(#case ({variant} child)\n\
                   (#match (#call {child_poll} (: task child : waker waker))\n\
                     (#case ({child_pending} pending) ({choice_pending} ({variant} pending)))\n\
                     (#case ({child_ready} value) ({choice_ready} value))))"
            ));
            branch_waits.push(Some(variant));
        } else {
            branch_waits.push(None);
        }
    }
    choice_variants.push(format!("({choice_done} {result_type})"));
    poll_arms.push(format!(
        "(#case ({choice_done} value) ({choice_ready} value))"
    ));
    let choice_helper = format!(
        "(#enum {choice_task} ({}))\n\
         (#linear {choice_task})\n\
         (#enum {choice_poll_result} (({choice_pending} {choice_task}) ({choice_ready} {result_type})))\n\
         (#fn {choice_poll} ((task {choice_task}) (waker (#ref {waker}))) {choice_poll_result}\n\
           (#return (#match task {})))",
        choice_variants.join(" "),
        poll_arms.join(" "),
    );
    branch_helpers.push(choice_helper);
    let helper = branch_helpers.join("\n");
    let wrap = |index: usize, value: Expr| -> Expr {
        let constructor = branch_waits[index].as_ref().unwrap_or(&choice_done);
        Expr::List(vec![Expr::Symbol(constructor.clone()), value])
    };
    let selected = if is_if {
        let then_branch = wrap(0, branches[0].1.clone());
        let else_branch = wrap(1, branches[1].1.clone());
        Expr::List(vec![
            Expr::Symbol("#if".into()),
            condition_or_scrutinee,
            then_branch,
            else_branch,
        ])
    } else {
        let mut items = vec![Expr::Symbol("#match".into()), condition_or_scrutinee];
        for (index, (_, branch)) in branches.into_iter().enumerate() {
            let Expr::List(mut case) = branch else {
                unreachable!()
            };
            let value = case.pop().expect("case body");
            case.push(wrap(index, value));
            items.push(Expr::List(case));
        }
        Expr::List(items)
    };
    Ok(Some((
        AwaitProtocol {
            result_type: protocol.result_type,
            child_type: Expr::Symbol(choice_task),
            pending: Expr::Symbol(choice_pending),
            ready: Expr::Symbol(choice_ready),
            poll: Expr::Symbol(choice_poll),
        },
        selected,
        helper,
    )))
}

/// Lower a diverging `#let-else` whose mismatch arm awaits and returns and is
/// immediately followed by the function's final return. The final expression
/// runs inside the success match arm, preserving access to pattern bindings.
/// The child is constructed and polled only on the mismatch path.
fn lower_awaited_let_else_success_continuation(
    let_else: &[Expr],
    following: &[Expr],
    return_value: &Expr,
    return_type: &Expr,
    failure_value: &Expr,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, String, usize)>, String> {
    let Some(failure_await) = first_async_await(failure_value) else {
        return Ok(None);
    };
    if failure_await.len() != 7 {
        return Ok(None);
    }

    let mut used_names = HashSet::new();
    for statement in following {
        collect_value_names(statement, &mut used_names);
    }
    collect_value_names(return_value, &mut used_names);
    let mut local_names = HashSet::new();
    for statement in following {
        collect_local_binding_names(statement, &mut local_names);
    }
    local_names.extend(pattern_symbols(&let_else[1]));
    for name in local_names {
        used_names.remove(&name);
    }
    used_names.remove("true");
    used_names.remove("false");

    let mut captures = used_names
        .iter()
        .filter_map(|name| known.get(name).cloned())
        .collect::<Vec<_>>();
    captures.sort_by(|left, right| left.name.cmp(&right.name));
    for capture in &captures {
        used_names.remove(&capture.name);
    }
    if let Some(name) = used_names.iter().next() {
        return Err(format!(
            "@async-fn awaited #let-else success continuation captures unknown local '{name}'"
        ));
    }

    let base = fresh_async_name(source, next_name);
    let input_name = format!("{base}-input");
    let function_name = format!("{base}-success-function");
    let frame = format!("{base}-success-frame");
    let poll_result = format!("{base}-success-poll-result");
    let pending = format!("{base}-success-pending");
    let ready = format!("{base}-success-ready");
    let poll = format!("{base}-success-poll");
    let temp_name = nested_await_name(source, next_name);
    let mut parameters = Vec::new();
    let mut arguments = Vec::new();
    for capture in &captures {
        let name = Expr::Symbol(capture.name.clone());
        let ty = crate::parse(&capture.ty)?
            .into_iter()
            .next()
            .ok_or_else(|| "@async-fn captured binding type is empty".to_owned())?
            .expr;
        parameters.push(Expr::List(if capture.mutable {
            vec![Expr::Symbol("#mut".into()), name.clone(), ty]
        } else {
            vec![name.clone(), ty]
        }));
        arguments.push(Expr::Symbol(":".into()));
        arguments.push(name.clone());
        arguments.push(name);
    }
    let input_symbol = Expr::Symbol(input_name.clone());
    parameters.push(Expr::List(vec![input_symbol.clone(), let_else[2].clone()]));
    arguments.push(Expr::Symbol(":".into()));
    arguments.push(Expr::Symbol(input_name));
    arguments.push(Expr::Symbol(temp_name.clone()));

    let function = Expr::List(
        std::iter::once(Expr::Symbol("#fn".into()))
            .chain([
                Expr::Symbol(function_name.clone()),
                Expr::List(parameters),
                return_type.clone(),
                Expr::List(vec![
                    Expr::Symbol("#let-else".into()),
                    let_else[1].clone(),
                    let_else[2].clone(),
                    input_symbol,
                    Expr::List(vec![
                        Expr::Symbol("#return".into()),
                        Expr::List(vec![Expr::Symbol("#unreachable".into())]),
                    ]),
                ]),
            ])
            .chain(following.iter().cloned())
            .chain(std::iter::once(Expr::List(vec![
                Expr::Symbol("#return".into()),
                return_value.clone(),
            ])))
            .collect(),
    );
    let waker_expression = crate::parse(waker)?
        .into_iter()
        .next()
        .ok_or_else(|| "@async-fn waker type is empty".to_owned())?
        .expr;
    let invocation = Expr::List(vec![
        Expr::At,
        Expr::Symbol("async-fn".into()),
        Expr::List(vec![
            Expr::Symbol(frame.clone()),
            Expr::Symbol(poll_result.clone()),
            Expr::Symbol(pending.clone()),
            Expr::Symbol(ready.clone()),
            Expr::Symbol(poll.clone()),
        ]),
        waker_expression,
        function,
    ]);
    let success_helper = generated_source(&invocation)?;

    let task_known = {
        let mut task_known = known.clone();
        task_known.insert(
            temp_name.clone(),
            Binding {
                name: temp_name.clone(),
                ty: expression_source(&let_else[2])?,
                mutable: false,
            },
        );
        task_known
    };
    let mut call = vec![Expr::Symbol("#call".into()), Expr::Symbol(function_name)];
    call.push(Expr::List(arguments));
    let success_await = Expr::List(vec![
        Expr::Symbol("#await".into()),
        return_type.clone(),
        Expr::Symbol(frame),
        Expr::Symbol(pending),
        Expr::Symbol(ready),
        Expr::Symbol(poll),
        Expr::List(call),
    ]);
    let match_expression = Expr::List(vec![
        Expr::Symbol("#match".into()),
        Expr::Symbol(temp_name.clone()),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            let_else[1].clone(),
            success_await,
        ]),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            Expr::Symbol("_".into()),
            failure_value.clone(),
        ]),
    ]);
    let conditional = if let Some((protocol, task)) = conditional_await(&match_expression)? {
        Some((protocol, task, String::new()))
    } else {
        conditional_await_with_immediate(&match_expression, &task_known, source, next_name, waker)?
    };
    let Some((protocol, mut task, choice_helper)) = conditional else {
        return Ok(None);
    };
    let mut generated = vec![Expr::List(vec![
        Expr::Symbol("#let".into()),
        Expr::Symbol(temp_name),
        let_else[2].clone(),
        let_else[3].clone(),
    ])];
    let mut generated_helpers = Vec::new();
    extract_nested_awaits(
        &mut task,
        &mut generated,
        &mut generated_helpers,
        &task_known,
        source,
        next_name,
        waker,
    )?;
    let task_name = nested_await_name(source, next_name);
    generated.push(Expr::List(vec![
        Expr::Symbol("#let".into()),
        Expr::Symbol(task_name.clone()),
        protocol.child_type.clone(),
        task,
    ]));
    let result_name = nested_await_name(source, next_name);
    generated.push(Expr::List(vec![
        Expr::Symbol("#let".into()),
        Expr::Symbol(result_name.clone()),
        return_type.clone(),
        Expr::List(vec![
            Expr::Symbol("#await".into()),
            protocol.child_type,
            protocol.pending,
            protocol.ready,
            protocol.poll,
            Expr::Symbol(task_name),
        ]),
    ]));
    generated_helpers.push(success_helper);
    generated_helpers.push(choice_helper);
    Ok(Some((
        generated,
        generated_helpers.join("\n"),
        result_name,
        following.len(),
    )))
}

fn pattern_symbols(pattern: &Expr) -> HashSet<String> {
    fn visit(pattern: &Expr, names: &mut HashSet<String>) {
        match pattern {
            Expr::Symbol(name) if name != "_" => {
                names.insert(name.clone());
            }
            Expr::List(items) => {
                for item in items.iter().skip(1) {
                    visit(item, names);
                }
            }
            _ => {}
        }
    }
    let mut names = HashSet::new();
    visit(pattern, &mut names);
    names
}

fn lower_awaited_let_else_return(
    statement: &Expr,
    following: &[Expr],
    return_value: &Expr,
    return_type: &Expr,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, String, usize)>, String> {
    let Some(let_else) = form(statement, "#let-else") else {
        return Ok(None);
    };
    if let_else.len() != 5 || !has_await(&let_else[4]) {
        return Ok(None);
    }
    let (branch_value, branch_prefix) = if let Some(branch_return) = form(&let_else[4], "#return") {
        if branch_return.len() != 2 {
            return Err("@async-fn #let-else return requires exactly one value".into());
        }
        (branch_return[1].clone(), None)
    } else if let Some(block) = form(&let_else[4], "#block") {
        let Some(last) = block.last() else {
            return Ok(None);
        };
        let Some((branch_value, has_return)) = async_terminal_loop_exit_with_return_marker(
            last,
            &Expr::Symbol("lim.async.unreachable-tail".into()),
            None,
            Some(return_type),
        ) else {
            return Ok(None);
        };
        if !has_return && !async_terminal_panics(&let_else[4]) {
            return Ok(None);
        }
        let prefix = &block[1..block.len() - 1];
        if prefix
            .iter()
            .any(|statement| contains_return(statement) || contains_loop_control(statement))
        {
            return Ok(None);
        }
        (branch_value, Some(prefix))
    } else {
        let Some((branch_value, has_return)) = async_terminal_loop_exit_with_return_marker(
            &let_else[4],
            &Expr::Symbol("lim.async.unreachable-tail".into()),
            None,
            Some(return_type),
        ) else {
            return Ok(None);
        };
        if !has_return && !async_terminal_panics(&let_else[4]) {
            return Ok(None);
        }
        (branch_value, None)
    };
    let failure_value = if let Some(prefix) = branch_prefix {
        if form(&branch_value, "#await").is_some() {
            let mut block = vec![Expr::Symbol("#block".into())];
            block.extend(prefix.iter().cloned());
            let result_name = nested_await_name(source, next_name);
            block.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                first_async_await(&branch_value)
                    .and_then(|await_form| await_form.get(1))
                    .cloned()
                    .ok_or_else(|| {
                        "@async-fn #let-else awaited return has no result type".to_owned()
                    })?,
                branch_value.clone(),
            ]));
            block.push(Expr::Symbol(result_name));
            Expr::List(block)
        } else {
            Expr::List(
                std::iter::once(Expr::Symbol("#block".into()))
                    .chain(prefix.iter().cloned())
                    .chain(std::iter::once(branch_value.clone()))
                    .collect(),
            )
        }
    } else {
        branch_value
    };
    let Some(await_form) = first_async_await(&failure_value) else {
        return Ok(None);
    };
    if await_form.len() != 7 {
        if form(&failure_value, "#await").is_none() {
            return Err(
                "nested #await requires an explicit result type: (#await Type Child Pending Ready poll task)"
                    .into(),
            );
        }
        return Ok(None);
    }
    if following.iter().any(has_await) || has_await(return_value) {
        if following.iter().any(contains_return) {
            return Ok(None);
        }
        return lower_awaited_let_else_success_continuation(
            let_else,
            following,
            return_value,
            return_type,
            &failure_value,
            known,
            source,
            next_name,
            waker,
        );
    }
    if following.iter().any(contains_return) {
        return Ok(None);
    }

    let success_value = if following.is_empty() {
        return_value.clone()
    } else {
        Expr::List(
            std::iter::once(Expr::Symbol("#block".into()))
                .chain(following.iter().cloned())
                .chain(std::iter::once(return_value.clone()))
                .collect(),
        )
    };

    let match_expression = Expr::List(vec![
        Expr::Symbol("#match".into()),
        let_else[3].clone(),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            let_else[1].clone(),
            success_value,
        ]),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            Expr::Symbol("_".into()),
            failure_value,
        ]),
    ]);
    let Some((protocol, mut task, helper)) =
        conditional_await_with_immediate(&match_expression, known, source, next_name, waker)?
    else {
        return Ok(None);
    };
    let mut generated = Vec::new();
    let mut generated_helpers = Vec::new();
    extract_nested_awaits(
        &mut task,
        &mut generated,
        &mut generated_helpers,
        known,
        source,
        next_name,
        waker,
    )?;
    let result_name = nested_await_name(source, next_name);
    generated.push(Expr::List(vec![
        Expr::Symbol("#let".into()),
        Expr::Symbol(result_name.clone()),
        return_type.clone(),
        Expr::List(vec![
            Expr::Symbol("#await".into()),
            protocol.child_type,
            protocol.pending,
            protocol.ready,
            protocol.poll,
            task,
        ]),
    ]));
    generated_helpers.push(helper);
    Ok(Some((
        generated,
        generated_helpers.join("\n"),
        result_name,
        following.len(),
    )))
}

fn extract_nested_awaits(
    expression: &mut Expr,
    generated: &mut Vec<Expr>,
    generated_helpers: &mut Vec<String>,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<(), String> {
    if let Some(items) = form(expression, "#if-let") {
        if items.len() >= 4 && has_await(expression) {
            let fallback = items
                .get(4)
                .cloned()
                .unwrap_or_else(|| Expr::List(Vec::new()));
            *expression = Expr::List(vec![
                Expr::Symbol("#match".into()),
                items[2].clone(),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    items[1].clone(),
                    items[3].clone(),
                ]),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::Symbol("_".into()),
                    fallback,
                ]),
            ]);
            return extract_nested_awaits(
                expression,
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            );
        }
    }
    if matches!(expression, Expr::List(_)) {
        let was_short_circuit_await = match expression {
            Expr::List(items) => {
                items.len() == 3
                    && matches!(items.first(), Some(Expr::Symbol(operator))
                        if matches!(operator.as_str(), "#bool.&&" | "bool.&&" | "#bool.||" | "bool.||"))
                    && has_await(&items[2])
            }
            _ => false,
        };
        normalize_short_circuit_await(expression);
        if was_short_circuit_await {
            return extract_nested_awaits(
                expression,
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            );
        }
    }
    if let Some(block) = form(expression, "#block") {
        if block.len() == 2 && has_await(&block[1]) {
            *expression = block[1].clone();
            return extract_nested_awaits(
                expression,
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            );
        }
        let mut block_known = known.clone();
        for index in 1..block.len() {
            let statement = &block[index];
            if has_await(statement) {
                let value_index = if form(statement, "#let")
                    .or_else(|| form(statement, "#let-mut"))
                    .is_some_and(|binding| binding.len() == 4)
                {
                    3
                } else if form(statement, "#set").is_some_and(|assignment| assignment.len() == 3) {
                    2
                } else {
                    break;
                };
                let Expr::List(statement_items) = statement else {
                    unreachable!()
                };
                let conditional = &statement_items[value_index];
                if !matches!(
                    conditional,
                    Expr::List(items)
                        if items.first().is_some_and(|head| matches!(head, Expr::Symbol(name) if matches!(name.as_str(), "#if" | "#match")))
                ) {
                    break;
                }
                if let Some((protocol, task, helper)) = conditional_await_with_immediate(
                    conditional,
                    &block_known,
                    source,
                    next_name,
                    waker,
                )? {
                    if has_await(&task) {
                        break;
                    }
                    if !helper.is_empty() {
                        generated_helpers.push(helper);
                    }
                    let await_expression = Expr::List(vec![
                        Expr::Symbol("#await".into()),
                        protocol.result_type,
                        protocol.child_type,
                        protocol.pending,
                        protocol.ready,
                        protocol.poll,
                        task,
                    ]);
                    let Expr::List(items) = expression else {
                        unreachable!()
                    };
                    let Expr::List(binding) = &mut items[index] else {
                        unreachable!()
                    };
                    binding[value_index] = await_expression;
                    return extract_nested_awaits(
                        expression,
                        generated,
                        generated_helpers,
                        known,
                        source,
                        next_name,
                        waker,
                    );
                }
                break;
            }
            if let Ok(local) = binding(statement, "block setup") {
                block_known.insert(local.name.clone(), local);
            }
        }
    }
    if form(expression, "#block").is_some()
        && has_await(expression)
        && extract_nested_block_awaits(
            expression,
            generated,
            generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?
    {
        return Ok(());
    }
    if has_await(expression)
        && (form(expression, "#loop").is_some() || form(expression, "#while").is_some())
    {
        if let Some((protocol, mut task, helper)) =
            conditional_value_expression_task(expression, known, source, next_name, waker)?
        {
            generated_helpers.push(helper);
            extract_nested_awaits(
                &mut task,
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            )?;
            let task_name = nested_await_name(source, next_name);
            generated.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(task_name.clone()),
                protocol.child_type.clone(),
                task,
            ]));
            let result_name = nested_await_name(source, next_name);
            generated.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                protocol.result_type,
                Expr::List(vec![
                    Expr::Symbol("#await".into()),
                    protocol.child_type,
                    protocol.pending,
                    protocol.ready,
                    protocol.poll,
                    Expr::Symbol(task_name),
                ]),
            ]));
            *expression = Expr::Symbol(result_name);
            return Ok(());
        }
    }
    if let Some(BlockAwait {
        mut prefix,
        binding,
        mutable_binding,
        result_type,
        mut await_expression,
        mut assignment,
        mut continuation,
    }) = block_await_continuation(expression)
    {
        let mut renamed_prefixes: Vec<(String, String)> = Vec::new();
        for statement in &mut prefix {
            for (original, renamed) in &renamed_prefixes {
                replace_await_local(statement, original, renamed);
            }
            if let Some(locals) = current_local_bindings(statement)? {
                for local in locals {
                    let renamed = nested_await_name(source, next_name);
                    let Expr::List(items) = statement else {
                        unreachable!()
                    };
                    rename_pattern_binding(&mut items[1], &local.name, &renamed);
                    renamed_prefixes.push((local.name, renamed));
                }
            } else if has_await(statement)
                || contains_loop_control(statement)
                || contains_return(statement)
            {
                return Err(
                    "@async-fn awaited block prefixes cannot suspend or transfer control".into(),
                );
            }
            generated.push(statement.clone());
        }
        if let Expr::List(items) = &mut await_expression {
            for (original, renamed) in &renamed_prefixes {
                replace_await_local(&mut items[6], original, renamed);
            }
        }
        let temporary = nested_await_name(source, next_name);
        let await_form = form(&await_expression, "#await")
            .expect("block_await_continuation validated an await expression");
        let normalized_await = Expr::List(
            std::iter::once(Expr::Symbol("#await".into()))
                .chain(await_form[2..].iter().cloned())
                .collect(),
        );
        generated.push(Expr::List(vec![
            Expr::Symbol(if mutable_binding {
                "#let-mut".into()
            } else {
                "#let".into()
            }),
            Expr::Symbol(temporary.clone()),
            result_type,
            normalized_await,
        ]));
        for (original, renamed) in &renamed_prefixes {
            replace_await_local(&mut continuation, original, renamed);
        }
        if let Some(name) = binding {
            replace_await_local(&mut continuation, &name, &temporary);
        }
        if let Some((mut assignment, rhs_index)) = assignment.take() {
            for (original, renamed) in &renamed_prefixes {
                replace_await_local(&mut assignment, original, renamed);
            }
            let Expr::List(items) = &mut assignment else {
                unreachable!()
            };
            items[rhs_index] = Expr::Symbol(temporary);
            let mut block = if let Some(items) = form(&continuation, "#block") {
                items.to_vec()
            } else {
                vec![Expr::Symbol("#block".into()), continuation]
            };
            block.insert(1, assignment);
            continuation = Expr::List(block);
        }
        *expression = continuation;
        return extract_nested_awaits(
            expression,
            generated,
            generated_helpers,
            known,
            source,
            next_name,
            waker,
        );
    }
    if let Some(block) = form(expression, "#block") {
        for statement in block.iter().skip(1).take(block.len().saturating_sub(2)) {
            let Some(await_form) = form(statement, "#await") else {
                continue;
            };
            if await_form.len() != 7 {
                continue;
            }
            let result_type = parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
            if !async_task_capture_is_copy(&result_type) {
                return Err("@async-fn cannot discard a non-Copy #await result in a #block; bind it to a local and consume it explicitly".into());
            }
        }
    }
    if form(expression, "#block").is_some()
        && has_await(expression)
        && block_await_continuation(expression).is_none()
    {
        if let Some((protocol, task, helper)) =
            conditional_value_expression_task(expression, known, source, next_name, waker)?
        {
            generated_helpers.push(helper);
            let task_name = nested_await_name(source, next_name);
            generated.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(task_name.clone()),
                protocol.child_type.clone(),
                task,
            ]));
            let result_name = nested_await_name(source, next_name);
            generated.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                protocol.result_type,
                Expr::List(vec![
                    Expr::Symbol("#await".into()),
                    protocol.child_type,
                    protocol.pending,
                    protocol.ready,
                    protocol.poll,
                    Expr::Symbol(task_name),
                ]),
            ]));
            *expression = Expr::Symbol(result_name);
            return Ok(());
        }
    }
    if let Some(await_form) = form(expression, "#await") {
        if await_form.len() != 7 {
            return Err(
                "nested #await requires an explicit result type: (#await Type Child Pending Ready poll task)"
                    .into(),
            );
        }
        parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
        let result_type = await_form[1].clone();
        let mut await_items = await_form.to_vec();
        // The child task is evaluated before the outer suspension. Extract its
        // suspensions even when this await is nested inside another operand,
        // rather than relying on the direct-binding statement special case.
        extract_nested_awaits(
            &mut await_items[6],
            generated,
            generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
        let normalized_await = Expr::List(
            std::iter::once(Expr::Symbol("#await".into()))
                .chain(await_items.into_iter().skip(2))
                .collect(),
        );
        let name = loop {
            let name = format!("lim.async.nested-await-{}", *next_name);
            *next_name += 1;
            if !source.contains(&name) {
                break name;
            }
        };
        generated.push(Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(name.clone()),
            result_type,
            normalized_await,
        ]));
        *expression = Expr::Symbol(name);
        return Ok(());
    }

    if has_await(expression) {
        if let Some(items) = form(expression, "#if") {
            if items.len() == 4 {
                let Expr::List(items) = expression else {
                    unreachable!()
                };
                extract_nested_awaits(
                    &mut items[1],
                    generated,
                    generated_helpers,
                    known,
                    source,
                    next_name,
                    waker,
                )?;
            }
        } else if let Some(items) = form(expression, "#match") {
            if items.len() >= 3 {
                let Expr::List(items) = expression else {
                    unreachable!()
                };
                extract_nested_awaits(
                    &mut items[1],
                    generated,
                    generated_helpers,
                    known,
                    source,
                    next_name,
                    waker,
                )?;
            }
        }
    }
    if extract_mutating_async_choice(
        expression,
        generated,
        generated_helpers,
        known,
        source,
        next_name,
        waker,
    )? {
        return Ok(());
    }
    if has_await(expression) {
        let conditional = if let Some((protocol, task)) = conditional_await(expression)? {
            Some((protocol, task, None))
        } else {
            conditional_await_with_immediate(expression, known, source, next_name, waker)?
                .map(|(protocol, task, helper)| (protocol, task, Some(helper)))
        };
        if let Some((protocol, mut task, helper)) = conditional {
            if let Some(helper) = helper {
                generated_helpers.push(helper);
            }
            extract_nested_awaits(
                &mut task,
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            )?;
            let task_name = nested_await_name(source, next_name);
            generated.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(task_name.clone()),
                protocol.child_type.clone(),
                task,
            ]));
            let result_name = nested_await_name(source, next_name);
            generated.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                protocol.result_type,
                Expr::List(vec![
                    Expr::Symbol("#await".into()),
                    protocol.child_type,
                    protocol.pending,
                    protocol.ready,
                    protocol.poll,
                    Expr::Symbol(task_name),
                ]),
            ]));
            *expression = Expr::Symbol(result_name);
            return Ok(());
        }
    }
    let contains_await = has_await(expression);
    match expression {
        Expr::List(items) => {
            let Some(Expr::Symbol(head)) = items.first() else {
                for item in items {
                    extract_nested_awaits(
                        item,
                        generated,
                        generated_helpers,
                        known,
                        source,
                        next_name,
                        waker,
                    )?;
                }
                return Ok(());
            };
            if contains_await
                && matches!(
                    head.as_str(),
                    "#loop" | "#while" | "#while-let" | "#for" | "#for-range"
                )
            {
                if let Some((protocol, task, helper)) =
                    conditional_value_expression_task(expression, known, source, next_name, waker)?
                {
                    generated_helpers.push(helper);
                    let task_name = nested_await_name(source, next_name);
                    generated.push(Expr::List(vec![
                        Expr::Symbol("#let".into()),
                        Expr::Symbol(task_name.clone()),
                        protocol.child_type.clone(),
                        task,
                    ]));
                    let result_name = nested_await_name(source, next_name);
                    generated.push(Expr::List(vec![
                        Expr::Symbol("#let".into()),
                        Expr::Symbol(result_name.clone()),
                        protocol.result_type,
                        Expr::List(vec![
                            Expr::Symbol("#await".into()),
                            protocol.child_type,
                            protocol.pending,
                            protocol.ready,
                            protocol.poll,
                            Expr::Symbol(task_name),
                        ]),
                    ]));
                    *expression = Expr::Symbol(result_name);
                    return Ok(());
                }
                return Err(
                    "@async-fn cannot lower this nested loop suspension; use a unit-valued loop expression with supported loop control".into(),
                );
            }
            if head == "#block" && contains_await {
                return Err("@async-fn awaits inside #block are not lowered yet".into());
            }
            match head.as_str() {
                "#quote" | "quote" | "#quasiquote" | "quasiquote" => return Ok(()),
                "#call" | "call" if items.len() == 3 => {
                    let has_suspending_argument = match &items[2] {
                        Expr::List(arguments) => arguments.iter().any(|argument| {
                            matches!(argument, Expr::List(pair) if pair.get(1).is_some_and(has_await))
                        }),
                        _ => false,
                    };
                    let callee = match &items[1] {
                        Expr::Symbol(name) => name.clone(),
                        _ if has_suspending_argument => {
                            return Err(
                                "@async-fn cannot sequence awaited arguments to a computed callee"
                                    .into(),
                            );
                        }
                        _ => String::new(),
                    };
                    let Expr::List(arguments) = &mut items[2] else {
                        return Ok(());
                    };
                    for argument in arguments {
                        let Expr::List(pair) = argument else {
                            continue;
                        };
                        if pair.len() != 2 {
                            continue;
                        }
                        let parameter = match &pair[0] {
                            Expr::Symbol(name) => name.clone(),
                            _ => continue,
                        };
                        let value = &mut pair[1];
                        extract_nested_awaits(
                            value,
                            generated,
                            generated_helpers,
                            known,
                            source,
                            next_name,
                            waker,
                        )?;
                        let already_sequenced = match value {
                            Expr::Symbol(name) => generated.iter().any(|statement| {
                                form(statement, "#let").is_some_and(|binding| {
                                    binding.len() == 4
                                        && matches!(&binding[1], Expr::Symbol(bound) if bound == name)
                                })
                            }),
                            _ => false,
                        };
                        if has_suspending_argument
                            && !async_argument_is_trivial(value)
                            && !already_sequenced
                        {
                            let value_type = match value {
                                Expr::Symbol(name) => {
                                    known.get(name).map(|binding| binding.ty.clone())
                                }
                                _ => None,
                            };
                            let ty = function_parameter_type(&callee, &parameter)
                                .or(value_type)
                                .ok_or_else(|| {
                                    format!("@async-fn cannot determine the type of argument '{parameter}' to '{callee}' while preserving evaluation order")
                                })?;
                            let temporary = nested_await_name(source, next_name);
                            generated.push(Expr::List(vec![
                                Expr::Symbol("#let".into()),
                                Expr::Symbol(temporary.clone()),
                                crate::parse(&ty)?
                                    .into_iter()
                                    .next()
                                    .ok_or_else(|| format!("@async-fn parameter '{parameter}' of '{callee}' has an empty type"))?
                                    .expr,
                                value.clone(),
                            ]));
                            *value = Expr::Symbol(temporary);
                        }
                    }
                }
                "#struct-literal" | "struct-literal" if items.len() == 3 => {
                    let has_suspending_field = match &items[2] {
                        Expr::List(fields) => fields.iter().any(|field| {
                            matches!(field, Expr::List(pair) if pair.get(1).is_some_and(has_await))
                        }),
                        _ => false,
                    };
                    let structure = match &items[1] {
                        Expr::Symbol(name) => name.clone(),
                        _ if has_suspending_field => {
                            return Err(
                                "@async-fn cannot sequence awaited fields of a computed struct type"
                                    .into(),
                            );
                        }
                        _ => String::new(),
                    };
                    let Expr::List(fields) = &mut items[2] else {
                        return Ok(());
                    };
                    for field in fields {
                        let Expr::List(pair) = field else {
                            continue;
                        };
                        if pair.len() != 2 {
                            continue;
                        }
                        let field_name = match &pair[0] {
                            Expr::Symbol(name) => name.clone(),
                            _ => continue,
                        };
                        let value = &mut pair[1];
                        extract_nested_awaits(
                            value,
                            generated,
                            generated_helpers,
                            known,
                            source,
                            next_name,
                            waker,
                        )?;
                        let already_sequenced = match value {
                            Expr::Symbol(name) => generated.iter().any(|statement| {
                                form(statement, "#let").is_some_and(|binding| {
                                    binding.len() == 4
                                        && matches!(&binding[1], Expr::Symbol(bound) if bound == name)
                                })
                            }),
                            _ => false,
                        };
                        if has_suspending_field
                            && !async_argument_is_trivial(value)
                            && !already_sequenced
                        {
                            let value_type = match value {
                                Expr::Symbol(name) => {
                                    known.get(name).map(|binding| binding.ty.clone())
                                }
                                _ => None,
                            };
                            let ty = struct_field_type(&structure, &field_name)
                                .or(value_type)
                                .ok_or_else(|| {
                                    format!("@async-fn cannot determine the type of field '{field_name}' in '{structure}' while preserving evaluation order")
                                })?;
                            let temporary = nested_await_name(source, next_name);
                            generated.push(Expr::List(vec![
                                Expr::Symbol("#let".into()),
                                Expr::Symbol(temporary.clone()),
                                crate::parse(&ty)?
                                    .into_iter()
                                    .next()
                                    .ok_or_else(|| format!("@async-fn field '{field_name}' of '{structure}' has an empty type"))?
                                    .expr,
                                value.clone(),
                            ]));
                            *value = Expr::Symbol(temporary);
                        }
                    }
                }
                "#array" | "array" | "#array-of" | "array-of" | "#tuple" | "tuple" => {
                    let start = if items
                        .get(1)
                        .is_some_and(|ty| parse_type(Some(&normalize_keywords(ty.clone()))).is_ok())
                    {
                        2
                    } else {
                        1
                    };
                    let aggregate_type = items
                        .get(1)
                        .and_then(|ty| parse_type(Some(&normalize_keywords(ty.clone()))).ok());
                    let has_suspending_element = items.iter().skip(start).any(has_await);
                    for (element_index, item) in items.iter_mut().enumerate().skip(start) {
                        extract_nested_awaits(
                            item,
                            generated,
                            generated_helpers,
                            known,
                            source,
                            next_name,
                            waker,
                        )?;
                        let already_sequenced = match item {
                            Expr::Symbol(name) => generated.iter().any(|statement| {
                                form(statement, "#let").is_some_and(|binding| {
                                    binding.len() == 4
                                        && matches!(&binding[1], Expr::Symbol(bound) if bound == name)
                                })
                            }),
                            _ => false,
                        };
                        if !has_suspending_element
                            || async_argument_is_trivial(item)
                            || already_sequenced
                        {
                            continue;
                        }
                        let element_type = match &aggregate_type {
                            Some(Type::Tuple(elements)) => elements
                                .get(element_index - start)
                                .map(crate::type_source),
                            Some(Type::Array(element, _)) => Some(crate::type_source(element)),
                            _ => None,
                        }
                        .ok_or_else(|| {
                            format!("@async-fn cannot determine the type of aggregate element {} while preserving evaluation order", element_index - start)
                        })?;
                        let temporary = nested_await_name(source, next_name);
                        generated.push(Expr::List(vec![
                            Expr::Symbol("#let".into()),
                            Expr::Symbol(temporary.clone()),
                            crate::parse(&element_type)?
                                .into_iter()
                                .next()
                                .ok_or_else(|| {
                                    "@async-fn aggregate element has an empty type".to_owned()
                                })?
                                .expr,
                            item.clone(),
                        ]));
                        *item = Expr::Symbol(temporary);
                    }
                }
                head if items.len() == 3
                    && crate::typed_body::NumericOperation::parse(
                        head.strip_prefix('#').unwrap_or(head),
                    )
                    .is_some() =>
                {
                    let operand_type = crate::type_source(
                        &crate::typed_body::NumericOperation::parse(
                            head.strip_prefix('#').unwrap_or(head),
                        )
                        .expect("guard parsed the numeric operation")
                        .operand_type,
                    );
                    let has_suspending_operand = items.iter().skip(1).any(has_await);
                    for operand in items.iter_mut().skip(1) {
                        extract_nested_awaits(
                            operand,
                            generated,
                            generated_helpers,
                            known,
                            source,
                            next_name,
                            waker,
                        )?;
                        let already_sequenced = match operand {
                            Expr::Symbol(name) => generated.iter().any(|statement| {
                                form(statement, "#let").is_some_and(|binding| {
                                    binding.len() == 4
                                        && matches!(&binding[1], Expr::Symbol(bound) if bound == name)
                                })
                            }),
                            _ => false,
                        };
                        if !has_suspending_operand
                            || async_argument_is_trivial(operand)
                            || already_sequenced
                        {
                            continue;
                        }
                        let temporary = nested_await_name(source, next_name);
                        generated.push(Expr::List(vec![
                            Expr::Symbol("#let".into()),
                            Expr::Symbol(temporary.clone()),
                            crate::parse(&operand_type)?
                                .into_iter()
                                .next()
                                .ok_or_else(|| {
                                    "@async-fn numeric operand has an empty type".to_owned()
                                })?
                                .expr,
                            operand.clone(),
                        ]));
                        *operand = Expr::Symbol(temporary);
                    }
                }
                _ => {
                    let constructor_name = head.clone();
                    let constructor_fields = enum_constructor_field_types(&constructor_name);
                    let has_suspending_payload =
                        constructor_fields.is_some() && items.iter().skip(1).any(has_await);
                    for (payload_index, item) in items.iter_mut().enumerate().skip(1) {
                        extract_nested_awaits(
                            item,
                            generated,
                            generated_helpers,
                            known,
                            source,
                            next_name,
                            waker,
                        )?;
                        let already_sequenced = match item {
                            Expr::Symbol(name) => generated.iter().any(|statement| {
                                form(statement, "#let").is_some_and(|binding| {
                                    binding.len() == 4
                                        && matches!(&binding[1], Expr::Symbol(bound) if bound == name)
                                })
                            }),
                            _ => false,
                        };
                        if !has_suspending_payload
                            || async_argument_is_trivial(item)
                            || already_sequenced
                        {
                            continue;
                        }
                        let payload_type = constructor_fields
                            .as_ref()
                            .and_then(|fields| fields.get(payload_index - 1))
                            .ok_or_else(|| {
                                format!("@async-fn cannot determine payload {} type for enum variant '{constructor_name}' while preserving evaluation order", payload_index - 1)
                            })?;
                        let temporary = nested_await_name(source, next_name);
                        generated.push(Expr::List(vec![
                            Expr::Symbol("#let".into()),
                            Expr::Symbol(temporary.clone()),
                            crate::parse(payload_type)?
                                .into_iter()
                                .next()
                                .ok_or_else(|| format!("@async-fn payload {} of enum variant '{constructor_name}' has an empty type", payload_index - 1))?
                                .expr,
                            item.clone(),
                        ]));
                        *item = Expr::Symbol(temporary);
                    }
                }
            }
        }
        Expr::Block(_) | Expr::Loop(_) if contains_await => {
            return Err("@async-fn cannot lower suspension inside #block or #loop yet".into());
        }
        Expr::Labeled { expression, .. } => {
            extract_nested_awaits(
                expression,
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            )?;
        }
        Expr::Unquote(value) | Expr::UnquoteSplicing(value) => {
            extract_nested_awaits(
                value,
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            )?;
        }
        Expr::Quote(_) | Expr::QuasiQuote(_) | Expr::Block(_) | Expr::Loop(_) => {}
        Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::Symbol(_)
        | Expr::At => {}
    }
    Ok(())
}

fn nested_await_name(source: &str, next_name: &mut usize) -> String {
    loop {
        let name = format!("lim.async.nested-await-{}", *next_name);
        *next_name += 1;
        if !source.contains(&name) {
            return name;
        }
    }
}

fn async_mutated_names(expression: &Expr, names: &mut HashSet<String>) {
    fn place_root(expression: &Expr) -> Option<&str> {
        match expression {
            Expr::Symbol(name) => Some(name),
            Expr::List(items)
                if matches!(items.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#get" | "#index" | "#slice-idx" | "#deref" | "#pin-read")) =>
            {
                items.get(1).and_then(place_root)
            }
            _ => None,
        }
    }
    if let Expr::List(items) = expression {
        if matches!(items.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote" | "#fn" | "fn"))
        {
            return;
        }
        if let Some(name) = mutable_assignment_target(expression) {
            names.insert(name.to_owned());
        }
        if matches!(items.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#borrow-mut" | "#pin-borrow-mut"))
        {
            if let Some(name) = items.get(1).and_then(place_root) {
                names.insert(name.to_owned());
            }
        }
        for item in items.iter().skip(1) {
            async_mutated_names(item, names);
        }
    }
}

/// Return branch-local mutations with the logical result, then restore them
/// at the suspension's call site. Capturing mutable locals by value without
/// these outputs silently loses changes made in a generated branch helper.
fn extract_mutating_async_choice(
    expression: &mut Expr,
    generated: &mut Vec<Expr>,
    generated_helpers: &mut Vec<String>,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<bool, String> {
    if !has_await(expression) || contains_return(expression) {
        return Ok(false);
    }
    let is_if = form(expression, "#if").is_some_and(|items| items.len() == 4);
    if !is_if && form(expression, "#match").is_none() {
        return Ok(false);
    }
    let mut mutated = HashSet::new();
    async_mutated_names(expression, &mut mutated);
    let mut outputs = mutated
        .into_iter()
        .filter_map(|name| known.get(&name).filter(|binding| binding.mutable).cloned())
        .collect::<Vec<_>>();
    outputs.sort_by(|left, right| left.name.cmp(&right.name));
    if outputs.is_empty() {
        return Ok(false);
    }
    let Some(result_type) = async_expression_type(expression, known) else {
        return Ok(false);
    };
    let mut fields = vec![Expr::Symbol("#tuple".into()), result_type.clone()];
    for output in &outputs {
        fields.push(crate::parse(&output.ty)?[0].expr.clone());
    }
    let tuple_type = Expr::List(fields);
    let wrap = |branch: &Expr, next_name: &mut usize| {
        let result = nested_await_name(source, next_name);
        let mut tuple = vec![
            Expr::Symbol("#tuple".into()),
            tuple_type.clone(),
            Expr::Symbol(result.clone()),
        ];
        tuple.extend(
            outputs
                .iter()
                .map(|output| Expr::Symbol(output.name.clone())),
        );
        Expr::List(vec![
            Expr::Symbol("#block".into()),
            Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result),
                result_type.clone(),
                branch.clone(),
            ]),
            Expr::List(tuple),
        ])
    };
    let mut choice = expression.clone();
    let Expr::List(items) = &mut choice else {
        unreachable!()
    };
    if is_if {
        for branch in &mut items[2..] {
            *branch = wrap(branch, next_name);
        }
    } else {
        for arm in &mut items[2..] {
            let Expr::List(case) = arm else {
                return Ok(false);
            };
            let Some(branch) = case.last_mut() else {
                return Ok(false);
            };
            *branch = wrap(branch, next_name);
        }
    }
    let Some((protocol, mut task, helper)) =
        conditional_await_with_immediate(&choice, known, source, next_name, waker)?
    else {
        return Ok(false);
    };
    generated_helpers.push(helper);
    extract_nested_awaits(
        &mut task,
        generated,
        generated_helpers,
        known,
        source,
        next_name,
        waker,
    )?;
    let tuple = nested_await_name(source, next_name);
    generated.push(Expr::List(vec![
        Expr::Symbol("#let".into()),
        Expr::Symbol(tuple.clone()),
        tuple_type.clone(),
        Expr::List(vec![
            Expr::Symbol("#await".into()),
            protocol.child_type,
            protocol.pending,
            protocol.ready,
            protocol.poll,
            task,
        ]),
    ]));
    let result = nested_await_name(source, next_name);
    let restored = outputs
        .iter()
        .map(|_| nested_await_name(source, next_name))
        .collect::<Vec<_>>();
    let mut pattern = vec![Expr::Symbol("#tuple".into()), Expr::Symbol(result.clone())];
    pattern.extend(restored.iter().cloned().map(Expr::Symbol));
    // Consume the Ready tuple into ordinary explicitly typed bindings. Moving
    // reference-bearing outputs through these names preserves provenance and
    // uses the normal assignment contract rather than special-case setters.
    generated.push(Expr::List(vec![
        Expr::Symbol("#let".into()),
        Expr::List(pattern),
        tuple_type,
        Expr::Symbol(tuple),
    ]));
    for (output, restored) in outputs.iter().zip(restored) {
        generated.push(Expr::List(vec![
            Expr::Symbol("#set".into()),
            Expr::Symbol(output.name.clone()),
            Expr::Symbol(restored),
        ]));
    }
    *expression = Expr::Symbol(result);
    Ok(true)
}

fn extract_nested_block_awaits(
    expression: &mut Expr,
    generated: &mut Vec<Expr>,
    generated_helpers: &mut Vec<String>,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<bool, String> {
    let Some(block) = form(expression, "#block") else {
        return Ok(false);
    };
    let Some(await_statement) = block.iter().position(has_await).filter(|index| *index > 0) else {
        return Ok(false);
    };
    let target_value_index = if await_statement == block.len() - 1 {
        None
    } else if form(&block[await_statement], "#let")
        .or_else(|| form(&block[await_statement], "#let-mut"))
        .is_some_and(|binding| binding.len() == 4 && has_await(&binding[3]))
    {
        Some(3)
    } else if form(&block[await_statement], "#set")
        .is_some_and(|assignment| assignment.len() == 3 && has_await(&assignment[2]))
    {
        Some(2)
    } else {
        let statement = &block[await_statement];
        if contains_return(statement)
            || contains_loop_control(statement)
            || form(statement, "#await").is_some()
            || form(statement, "#let-else").is_some()
        {
            return Ok(false);
        }
        None
    };
    let whole_statement = await_statement < block.len() - 1 && target_value_index.is_none();
    if await_statement == block.len() - 1 && contains_return(&block[await_statement]) {
        return Ok(false);
    }
    if block_await_continuation(expression).is_some() {
        return Ok(false);
    }

    let mut renamed = Vec::<(String, String)>::new();
    let mut block_known = known.clone();
    for original_statement in &block[1..await_statement] {
        if has_await(original_statement)
            || contains_return(original_statement)
            || contains_loop_control(original_statement)
        {
            return Ok(false);
        }
        let mut statement = original_statement.clone();
        for (original, replacement) in &renamed {
            replace_await_local(&mut statement, original, replacement);
        }
        if let Some(locals) = current_local_bindings(&statement)? {
            for local in locals {
                let replacement = nested_await_name(source, next_name);
                let Expr::List(items) = &mut statement else {
                    unreachable!()
                };
                rename_pattern_binding(&mut items[1], &local.name, &replacement);
                block_known.insert(
                    replacement.clone(),
                    Binding {
                        name: replacement.clone(),
                        ..local.clone()
                    },
                );
                renamed.push((local.name, replacement));
            }
        }
        generated.push(statement);
    }

    let mut continuation = block[await_statement..].to_vec();
    for statement in &mut continuation {
        for (original, replacement) in &renamed {
            replace_await_local(statement, original, replacement);
        }
    }
    if await_statement == block.len() - 1 {
        let Some(tail) = continuation.first_mut() else {
            return Ok(false);
        };
        extract_nested_awaits(
            tail,
            generated,
            generated_helpers,
            &block_known,
            source,
            next_name,
            waker,
        )?;
        *expression = tail.clone();
    } else if whole_statement {
        let statement = continuation
            .first_mut()
            .expect("await statement index is inside block");
        extract_nested_awaits(
            statement,
            generated,
            generated_helpers,
            &block_known,
            source,
            next_name,
            waker,
        )?;
        *expression = Expr::List(
            std::iter::once(Expr::Symbol("#block".into()))
                .chain(continuation)
                .collect(),
        );
    } else {
        let statement = continuation
            .first_mut()
            .expect("await statement index is inside block");
        let Expr::List(items) = statement else {
            return Ok(false);
        };
        let value_index = target_value_index.expect("binding or assignment target has a value");
        extract_nested_awaits(
            &mut items[value_index],
            generated,
            generated_helpers,
            &block_known,
            source,
            next_name,
            waker,
        )?;
        *expression = Expr::List(
            std::iter::once(Expr::Symbol("#block".into()))
                .chain(continuation)
                .collect(),
        );
    }
    extract_nested_awaits(
        expression,
        generated,
        generated_helpers,
        &block_known,
        source,
        next_name,
        waker,
    )?;
    Ok(true)
}

fn collect_terminal_awaits<'a>(expression: &'a Expr, output: &mut Vec<&'a [Expr]>) {
    if let Some(await_form) = form(expression, "#await") {
        output.push(await_form);
        return;
    }
    if let Some(block) = form(expression, "#block") {
        if let Some(tail) = block.last() {
            collect_terminal_awaits(tail, output);
        }
        return;
    }
    if let Some(items) = form(expression, "#if") {
        for branch in items.iter().skip(2).take(2) {
            collect_terminal_awaits(branch, output);
        }
        return;
    }
    if let Some(items) = form(expression, "#match") {
        for arm in items.iter().skip(2) {
            let Some(case) = form(arm, "#case") else {
                continue;
            };
            let body_index = match case.len() {
                3 => 2,
                4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                _ => continue,
            };
            collect_terminal_awaits(&case[body_index], output);
        }
    }
}

fn extract_statement_awaits(
    statement: &mut Expr,
    generated: &mut Vec<Expr>,
    generated_helpers: &mut Vec<String>,
    known: &HashMap<String, Binding>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<(), String> {
    if !has_await(statement) {
        return Ok(());
    }
    fn all_branches_return(expression: &Expr) -> bool {
        if form(expression, "#async-terminal-return").is_some() {
            return true;
        }
        if let Some(block) = form(expression, "#block") {
            return block.last().is_some_and(all_branches_return);
        }
        if let Some(items) = form(expression, "#if") {
            return items.len() == 4
                && all_branches_return(&items[2])
                && all_branches_return(&items[3]);
        }
        if let Some(items) = form(expression, "#match") {
            return items.len() >= 3
                && items[2..].iter().all(|arm| {
                    form(arm, "#case")
                        .and_then(|case| case.last())
                        .is_some_and(all_branches_return)
                });
        }
        false
    }
    if form(statement, "#async-terminal-return").is_none() && all_branches_return(statement) {
        let result_type =
            async_terminal_return_type(statement).expect("marked terminal return type");
        extract_nested_awaits(
            statement,
            generated,
            generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
        *statement = Expr::List(vec![
            Expr::Symbol("#async-terminal-return".into()),
            result_type,
            statement.clone(),
        ]);
        return Ok(());
    }
    let mut discarded_awaits = Vec::new();
    if form(statement, "#await").is_some()
        || form(statement, "#block").is_some()
        || form(statement, "#if").is_some()
        || form(statement, "#match").is_some()
    {
        collect_terminal_awaits(statement, &mut discarded_awaits);
    }
    for await_form in discarded_awaits {
        if await_form.len() == 6 {
            return Err("@async-fn a discarded #await result requires an explicit type so Copy can be checked".into());
        }
        if await_form.len() == 7 {
            let result_type = parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
            if !async_task_capture_is_copy(&result_type) {
                return Err("@async-fn cannot discard a non-Copy #await result; bind it to a local and consume it explicitly".into());
            }
        }
    }
    if let Some(items) = form(statement, "#let")
        .or_else(|| form(statement, "#let-mut"))
        .or_else(|| form(statement, "let"))
        .or_else(|| form(statement, "let-mut"))
    {
        if items.len() != 4 {
            return Err("@async-fn local declaration requires a pattern, type, and value".into());
        }
        if let Some(await_form) = form(&items[3], "#await") {
            let has_pattern = matches!(&items[1], Expr::List(_));
            let task_index = match await_form.len() {
                6 => Some(5),
                7 => Some(6),
                _ => None,
            };
            if task_index.is_some_and(|index| has_await(&await_form[index])) {
                let Expr::List(statement_items) = statement else {
                    unreachable!()
                };
                let Expr::List(await_items) = &mut statement_items[3] else {
                    unreachable!()
                };
                let task_index = task_index.expect("await task index was checked");
                extract_nested_awaits(
                    &mut await_items[task_index],
                    generated,
                    generated_helpers,
                    known,
                    source,
                    next_name,
                    waker,
                )?;
            }
            if has_pattern {
                let Expr::List(items) = statement else {
                    unreachable!("validated local declaration is a list");
                };
                let temporary = nested_await_name(source, next_name);
                let awaited = std::mem::replace(&mut items[3], Expr::Symbol(temporary.clone()));
                generated.push(Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(temporary),
                    items[2].clone(),
                    awaited,
                ]));
            }
            return Ok(());
        }
        let Expr::List(items) = statement else {
            unreachable!()
        };
        extract_nested_awaits(
            &mut items[3],
            generated,
            generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
    } else if let Some(items) = form(statement, "#let-else") {
        if items.len() != 5 {
            return Err("@async-fn #let-else requires pattern, type, value, and else body".into());
        }
        if has_await(&items[4]) {
            return Err(
                "@async-fn cannot lower #await inside a #let-else diverging body yet".into(),
            );
        }
        let Expr::List(statement_items) = statement else {
            unreachable!()
        };
        if let Some(await_form) = form(&statement_items[3], "#await") {
            let task_index = match await_form.len() {
                6 => 5,
                7 => 6,
                _ => return Err("@async-fn #let-else scrutinee #await requires (#await [Type] Child Pending Ready poll task)".into()),
            };
            if has_await(&await_form[task_index]) {
                let Expr::List(await_items) = &mut statement_items[3] else {
                    unreachable!()
                };
                extract_nested_awaits(
                    &mut await_items[task_index],
                    generated,
                    generated_helpers,
                    known,
                    source,
                    next_name,
                    waker,
                )?;
            }
            let await_form = form(&statement_items[3], "#await")
                .expect("validated let-else await remains an await");
            let normalized_await = Expr::List(
                std::iter::once(Expr::Symbol("#await".into()))
                    .chain(await_form[1..].iter().cloned())
                    .collect(),
            );
            let temp_name = nested_await_name(source, next_name);
            generated.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(temp_name.clone()),
                statement_items[2].clone(),
                normalized_await,
            ]));
            statement_items[3] = Expr::Symbol(temp_name);
        } else {
            extract_nested_awaits(
                &mut statement_items[3],
                generated,
                generated_helpers,
                known,
                source,
                next_name,
                waker,
            )?;
        }
    } else if let Some(items) = form(statement, "#return") {
        if items.len() == 2 && form(&items[1], "#await").is_some() {
            return Ok(());
        }
        let Expr::List(items) = statement else {
            unreachable!()
        };
        if items.len() != 2 {
            return Err("@async-fn #return requires exactly one value".into());
        }
        extract_nested_awaits(
            &mut items[1],
            generated,
            generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
    } else {
        extract_nested_awaits(
            statement,
            generated,
            generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
    }
    Ok(())
}

/// Turn a multi-statement `#while` body containing suspension into a nested
/// async child. The child owns its per-iteration locals and keeps them in its
/// own concrete frame across Pending; explicit Copy values or mutable-reference
/// captures cross the condition/body boundary.
fn async_while_body_child(
    body: &[Expr],
    known: &HashMap<String, Binding>,
    known_order: &[String],
    source: &str,
    next_name: &mut usize,
    waker: &str,
    return_true_on_initial_let_else_mismatch: bool,
    owned_capture: Option<&str>,
    return_type: Option<&Expr>,
) -> Result<
    (
        Binding,
        Vec<Expr>,
        String,
        Vec<Binding>,
        Option<(String, String, String, Expr)>,
    ),
    String,
> {
    fn has_outer_loop_control(expression: &Expr) -> bool {
        match expression {
            Expr::List(items) => {
                match items.first() {
                    Some(Expr::Symbol(head)) if matches!(head.as_str(), "#break" | "#continue") => {
                        return true;
                    }
                    Some(Expr::Symbol(head))
                        if matches!(
                            head.as_str(),
                            "#while" | "#while-let" | "#for" | "#for-range" | "#loop"
                        ) =>
                    {
                        return false;
                    }
                    _ => {}
                }
                items.iter().any(has_outer_loop_control)
            }
            Expr::Block(statements) => statements.iter().any(|statement| match statement {
                crate::Statement::Expr(value)
                | crate::Statement::Return(Some(value))
                | crate::Statement::BreakValue(value)
                | crate::Statement::BreakToValue { value, .. } => has_outer_loop_control(value),
                _ => false,
            }),
            Expr::Loop(_) => false,
            Expr::Labeled { expression, .. }
            | Expr::Unquote(expression)
            | Expr::UnquoteSplicing(expression) => has_outer_loop_control(expression),
            _ => false,
        }
    }
    fn terminal_status(expression: &Expr) -> Result<Option<Expr>, String> {
        fn status_branch(expression: &Expr) -> Result<Expr, String> {
            if let Some(status) = terminal_status(expression)? {
                Ok(status)
            } else if form(expression, "#return").is_some() {
                Ok(expression.clone())
            } else if has_outer_loop_control(expression) {
                Err("@async-fn composed awaited while transfers must be terminal".into())
            } else {
                Ok(Expr::List(vec![
                    Expr::Symbol("#block".into()),
                    expression.clone(),
                    Expr::Symbol("false".into()),
                ]))
            }
        }

        if let Some(control) = form(expression, "#break").or_else(|| form(expression, "#continue"))
        {
            if control.len() != 1 {
                return Err(
                    "@async-fn composed awaited while body does not support labeled transfers"
                        .into(),
                );
            }
            return Ok(Some(Expr::Symbol(
                if form(expression, "#break").is_some() {
                    "true"
                } else {
                    "false"
                }
                .into(),
            )));
        }
        if let Some(items) = form(expression, "#block") {
            let Some(last) = items.last() else {
                return Ok(None);
            };
            let Some(status) = terminal_status(last)?
                .or_else(|| form(last, "#return").is_some().then(|| last.clone()))
            else {
                return Ok(None);
            };
            if items[..items.len() - 1].iter().any(has_outer_loop_control) {
                return Err("@async-fn composed awaited while transfers must be terminal".into());
            }
            let mut block = items.to_vec();
            *block.last_mut().expect("block has a terminal expression") = status;
            return Ok(Some(Expr::List(block)));
        }
        if let Some(items) = form(expression, "#if") {
            if items.len() == 4
                && (has_outer_loop_control(&items[2])
                    || has_outer_loop_control(&items[3])
                    || contains_return(&items[2])
                    || contains_return(&items[3]))
            {
                if has_outer_loop_control(&items[1]) {
                    return Err(
                        "@async-fn composed awaited while condition cannot transfer loop control"
                            .into(),
                    );
                }
                return Ok(Some(Expr::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    status_branch(&items[2])?,
                    status_branch(&items[3])?,
                ])));
            }
        }
        if let Some(items) = form(expression, "#match") {
            if items.len() >= 3
                && items[2..]
                    .iter()
                    .any(|arm| has_outer_loop_control(arm) || contains_return(arm))
            {
                if has_outer_loop_control(&items[1]) {
                    return Err(
                        "@async-fn composed awaited while match value cannot transfer loop control"
                            .into(),
                    );
                }
                let mut rewritten = items.to_vec();
                for arm in &mut rewritten[2..] {
                    let Some(case) = form(arm, "#case") else {
                        return Err(
                            "@async-fn composed awaited while match transfers require #case arms"
                                .into(),
                        );
                    };
                    let body_index = match case.len() {
                        3 => 2,
                        4 if form(&case[2], "#when").is_some() => 3,
                        _ => return Err(
                            "@async-fn composed awaited while match transfer has an invalid arm"
                                .into(),
                        ),
                    };
                    let mut case = case.to_vec();
                    case[body_index] = status_branch(&case[body_index])?;
                    *arm = Expr::List(case);
                }
                return Ok(Some(Expr::List(rewritten)));
            }
        }
        Ok(None)
    }
    let has_return = body.iter().any(contains_return);

    let mut names = HashSet::new();
    for expression in body {
        collect_value_names(expression, &mut names);
    }
    let mut locals = HashSet::new();
    for expression in body {
        collect_local_binding_names(expression, &mut locals);
    }
    names.retain(|name| !locals.contains(name) && name != "true" && name != "false");
    let captures = known_order
        .iter()
        .filter(|name| names.contains(name.as_str()))
        .filter_map(|name| known.get(name).cloned())
        .collect::<Vec<_>>();
    let mut mutated = HashSet::new();
    fn collect_assignments(expression: &Expr, names: &mut HashSet<String>) {
        if let Some(name) = mutable_assignment_target(expression) {
            names.insert(name.to_owned());
        }
        // A callee may mutate a captured value through an explicit mutable
        // borrow. Return that value with the child's other mutable outputs;
        // otherwise its mutation is lost when the iteration task completes.
        fn place_root(expression: &Expr) -> Option<&str> {
            match expression {
                Expr::Symbol(name) => Some(name),
                Expr::List(items)
                    if matches!(items.first(), Some(Expr::Symbol(head))
                    if matches!(head.as_str(), "#get" | "#index" | "#slice-idx" | "#deref" | "#pin-read")) =>
                {
                    items.get(1).and_then(place_root)
                }
                _ => None,
            }
        }
        if let Expr::List(items) = expression {
            if matches!(items.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#borrow-mut" | "#pin-borrow-mut"))
            {
                if let Some(name) = items.get(1).and_then(place_root) {
                    names.insert(name.to_owned());
                }
            }
        }
        match expression {
            Expr::List(items) => {
                for item in items {
                    collect_assignments(item, names);
                }
            }
            Expr::Block(statements) | Expr::Loop(statements) => {
                for statement in statements {
                    match statement {
                        crate::Statement::Expr(value)
                        | crate::Statement::Return(Some(value))
                        | crate::Statement::BreakValue(value)
                        | crate::Statement::BreakToValue { value, .. } => {
                            collect_assignments(value, names)
                        }
                        _ => {}
                    }
                }
            }
            Expr::Labeled { expression, .. }
            | Expr::Unquote(expression)
            | Expr::UnquoteSplicing(expression) => collect_assignments(expression, names),
            _ => {}
        }
    }
    for expression in body {
        collect_assignments(expression, &mut mutated);
    }
    for capture in &captures {
        let parsed = crate::parse(&capture.ty)?;
        let ty = parsed
            .first()
            .ok_or_else(|| "@async-fn body capture type is empty".to_owned())?;
        let ty = parse_type(Some(&normalize_keywords(ty.expr.clone())))?;
        if !async_task_capture_is_copy(&ty)
            && !async_task_capture_is_mutable_reference(&ty)
            && owned_capture != Some(capture.name.as_str())
            && !(capture.mutable && mutated.contains(&capture.name))
        {
            return Err(format!(
                "@async-fn composed awaited while body captures non-Copy local '{}'; move its task inputs into an explicit child task",
                capture.name
            ));
        }
    }
    let mut mutable_outputs = Vec::new();
    for capture in &captures {
        let ty = parse_type(Some(&normalize_keywords(
            crate::parse(&capture.ty)?[0].expr.clone(),
        )))?;
        if (capture.mutable && mutated.contains(&capture.name))
            || async_task_capture_is_mutable_reference(&ty)
        {
            // The child must return exclusive handles, even if it never
            // reassigns them. Its parent cannot retain a duplicate in Pending.
            mutable_outputs.push(capture.clone());
        }
    }

    let base = fresh_async_name(source, next_name);
    let function_name = format!("{base}-body-function");
    let frame = format!("{base}-body-frame");
    let poll_result = format!("{base}-body-poll-result");
    let pending = format!("{base}-body-pending");
    let ready = format!("{base}-body-ready");
    let poll = format!("{base}-body-poll");
    let mut child_body = body.to_vec();
    for statement in &mut child_body {
        let Some(let_form) = form(statement, "#let").or_else(|| form(statement, "#let-mut")) else {
            continue;
        };
        let Some(await_form) = let_form.get(3).and_then(|value| form(value, "#await")) else {
            continue;
        };
        if await_form.len() == 7 {
            let binding_type = parse_type(Some(&normalize_keywords(let_form[2].clone())))?;
            let await_type = parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
            if binding_type != await_type {
                return Err(format!(
                    "@async-fn nested body await result type does not match binding '{}'",
                    binding(statement, "awaited body local")?.name
                ));
            }
            let Expr::List(let_items) = statement else {
                unreachable!("direct let form is a list")
            };
            let Expr::List(await_items) = &mut let_items[3] else {
                unreachable!("await initializer is a list")
            };
            await_items.remove(1);
        }
    }
    let terminal_status = child_body
        .last()
        .map(terminal_status)
        .transpose()?
        .flatten();
    if terminal_status.is_some() {
        child_body.pop();
    }
    if child_body.iter().any(has_outer_loop_control) {
        return Err(
            "@async-fn composed awaited while body transfers must be terminal statements".into(),
        );
    }
    let body_status_type = Expr::Symbol("bool".into());
    let body_result_type = if mutable_outputs.is_empty() {
        body_status_type.clone()
    } else {
        let mut fields = vec![Expr::Symbol("#tuple".into()), body_status_type.clone()];
        for capture in &mutable_outputs {
            fields.push(
                crate::parse(&capture.ty)?
                    .into_iter()
                    .next()
                    .ok_or_else(|| "@async-fn mutable body capture type is empty".to_owned())?
                    .expr,
            );
        }
        Expr::List(fields)
    };
    let body_return = if has_return {
        let return_type = return_type.ok_or_else(|| {
            "@async-fn composed awaited while body return requires the enclosing function return type"
                .to_owned()
        })?;
        let outcome_type = fresh_async_name(source, next_name);
        let continue_variant = format!("{outcome_type}-continue");
        let return_variant = format!("{outcome_type}-return");
        Some((
            outcome_type,
            continue_variant,
            return_variant,
            return_type.clone(),
        ))
    } else {
        None
    };
    if let Some((_, _, return_variant, _)) = &body_return {
        for statement in &mut child_body {
            rewrite_async_child_returns(statement, return_variant)?;
        }
    }
    if return_true_on_initial_let_else_mismatch {
        let Some(Expr::List(let_else)) = child_body.first_mut() else {
            return Err("@async-fn child mismatch return requires a leading #let-else".into());
        };
        if !matches!(let_else.first(), Some(Expr::Symbol(head)) if head == "#let-else")
            || let_else.len() != 5
        {
            return Err("@async-fn child mismatch return requires a leading #let-else".into());
        }
        let mut mismatch_value = if mutable_outputs.is_empty() {
            Expr::Symbol("true".into())
        } else {
            Expr::List(
                std::iter::once(Expr::Symbol("#tuple".into()))
                    .chain(std::iter::once(body_result_type.clone()))
                    .chain(std::iter::once(Expr::Symbol("true".into())))
                    .chain(
                        mutable_outputs
                            .iter()
                            .map(|capture| Expr::Symbol(capture.name.clone())),
                    )
                    .collect(),
            )
        };
        if let Some((_, continue_variant, _, _)) = &body_return {
            mismatch_value =
                Expr::List(vec![Expr::Symbol(continue_variant.clone()), mismatch_value]);
        }
        let_else[4] = Expr::List(vec![Expr::Symbol("#return".into()), mismatch_value]);
    }
    let mut parameters = Vec::with_capacity(captures.len());
    let mut arguments = Vec::with_capacity(captures.len());
    for capture in &captures {
        let name = Expr::Symbol(capture.name.clone());
        let ty = crate::parse(&capture.ty)?
            .into_iter()
            .next()
            .ok_or_else(|| "@async-fn body capture type is empty".to_owned())?
            .expr;
        parameters.push(Expr::List(
            if capture.mutable && mutated.contains(&capture.name) {
                vec![Expr::Symbol("#mut".into()), name.clone(), ty]
            } else {
                vec![name.clone(), ty]
            },
        ));
        // Keep the internal call AST in canonical named-pair form. Raw colon
        // groups are parser sugar; repeated delimiters must not reach the
        // value renamer or be mistaken for argument keys.
        arguments.push(Expr::List(vec![name.clone(), name]));
    }
    let function_result_type = if let Some((outcome_type, _, _, _)) = &body_return {
        Expr::Symbol(outcome_type.clone())
    } else {
        body_result_type.clone()
    };
    let mut function = vec![
        Expr::Symbol("#fn".into()),
        Expr::Symbol(function_name.clone()),
        Expr::List(parameters),
        function_result_type.clone(),
    ];
    function.extend(child_body);
    // Return the complete state from each terminal branch. Evaluating a
    // suspending status expression as one tuple field would spawn a value
    // helper that returns only the status and loses updated captures.
    fn return_status(
        status: &Expr,
        result_type: &Expr,
        outputs: &[Binding],
        continue_variant: Option<&str>,
        function_result_type: &Expr,
    ) -> Expr {
        if let Expr::List(items) = status {
            let mut rewritten = items.clone();
            match items.first() {
                Some(Expr::Symbol(head)) if head == "#if" && items.len() == 4 => {
                    rewritten[2] = return_status(
                        &items[2],
                        result_type,
                        outputs,
                        continue_variant,
                        function_result_type,
                    );
                    rewritten[3] = return_status(
                        &items[3],
                        result_type,
                        outputs,
                        continue_variant,
                        function_result_type,
                    );
                    return Expr::List(rewritten);
                }
                Some(Expr::Symbol(head)) if head == "#block" && items.len() > 1 => {
                    let last = rewritten.last_mut().unwrap();
                    *last = return_status(
                        last,
                        result_type,
                        outputs,
                        continue_variant,
                        function_result_type,
                    );
                    return Expr::List(rewritten);
                }
                Some(Expr::Symbol(head)) if head == "#match" => {
                    for arm in &mut rewritten[2..] {
                        if let Expr::List(case) = arm {
                            if let Some(last) = case.last_mut() {
                                *last = return_status(
                                    last,
                                    result_type,
                                    outputs,
                                    continue_variant,
                                    function_result_type,
                                );
                            }
                        }
                    }
                    return Expr::List(rewritten);
                }
                Some(Expr::Symbol(head)) if head == "#return" => {
                    return Expr::List(vec![
                        Expr::Symbol("#async-terminal-return".into()),
                        function_result_type.clone(),
                        items[1].clone(),
                    ])
                }
                _ => {}
            }
        }
        let mut value = if outputs.is_empty() {
            status.clone()
        } else {
            Expr::List(
                [
                    Expr::Symbol("#tuple".into()),
                    result_type.clone(),
                    status.clone(),
                ]
                .into_iter()
                .chain(
                    outputs
                        .iter()
                        .map(|capture| Expr::Symbol(capture.name.clone())),
                )
                .collect(),
            )
        };
        if let Some(variant) = continue_variant {
            value = Expr::List(vec![Expr::Symbol(variant.into()), value]);
        }
        Expr::List(vec![
            Expr::Symbol("#async-terminal-return".into()),
            function_result_type.clone(),
            value,
        ])
    }
    let terminal_return = if terminal_status
        .as_ref()
        .is_some_and(|status| has_await(status) || contains_return(status))
    {
        let mut status = terminal_status.clone().unwrap();
        if let Some((_, _, variant, _)) = &body_return {
            rewrite_async_child_returns(&mut status, variant)?;
        }
        Some(return_status(
            &status,
            &body_result_type,
            &mutable_outputs,
            body_return
                .as_ref()
                .map(|(_, variant, _, _)| variant.as_str()),
            &function_result_type,
        ))
    } else {
        None
    };
    let body_result = if mutable_outputs.is_empty() {
        terminal_status.unwrap_or_else(|| Expr::Symbol("false".into()))
    } else {
        Expr::List(
            std::iter::once(Expr::Symbol("#tuple".into()))
                .chain(std::iter::once(body_result_type.clone()))
                .chain(std::iter::once(
                    terminal_status.unwrap_or_else(|| Expr::Symbol("false".into())),
                ))
                .chain(
                    mutable_outputs
                        .iter()
                        .map(|capture| Expr::Symbol(capture.name.clone())),
                )
                .collect(),
        )
    };
    let body_result = if let Some((_, continue_variant, _, _)) = &body_return {
        Expr::List(vec![Expr::Symbol(continue_variant.clone()), body_result])
    } else {
        body_result
    };
    if let Some(terminal_return) = terminal_return {
        function.push(Expr::List(vec![
            Expr::Symbol("#return".into()),
            terminal_return,
        ]));
    } else {
        function.push(Expr::List(vec![
            Expr::Symbol("#return".into()),
            body_result,
        ]));
    }
    let function = Expr::List(function);
    let waker = crate::parse(waker)?
        .into_iter()
        .next()
        .ok_or_else(|| "@async-fn waker type is empty".to_owned())?
        .expr;
    let invocation = Expr::List(vec![
        Expr::At,
        Expr::Symbol("async-fn".into()),
        Expr::List(vec![
            Expr::Symbol(frame.clone()),
            Expr::Symbol(poll_result.clone()),
            Expr::Symbol(pending.clone()),
            Expr::Symbol(ready.clone()),
            Expr::Symbol(poll.clone()),
        ]),
        waker,
        function,
    ]);
    let mut helper = generated_source(&invocation)?;
    if let Some((outcome_type, continue_variant, return_variant, return_type)) = &body_return {
        let outcome_definition = Expr::List(vec![
            Expr::Symbol("#enum".into()),
            Expr::Symbol(outcome_type.clone()),
            Expr::List(vec![
                Expr::List(vec![
                    Expr::Symbol(continue_variant.clone()),
                    body_result_type.clone(),
                ]),
                Expr::List(vec![
                    Expr::Symbol(return_variant.clone()),
                    return_type.clone(),
                ]),
            ]),
        ]);
        helper = format!("{}\n{}", expression_source(&outcome_definition)?, helper);
    }
    let task = Expr::List(vec![
        Expr::Symbol("#call".into()),
        Expr::Symbol(function_name),
        Expr::List(arguments),
    ]);
    let await_form = vec![
        Expr::Symbol("#await".into()),
        function_result_type.clone(),
        Expr::Symbol(frame),
        Expr::Symbol(pending),
        Expr::Symbol(ready),
        Expr::Symbol(poll),
        task,
    ];
    let binding = Binding {
        name: format!("{base}-body-result"),
        ty: expression_source(&function_result_type)?,
        mutable: false,
    };
    let form = vec![
        Expr::Symbol("#let".into()),
        Expr::Symbol(binding.name.clone()),
        function_result_type,
        Expr::List(await_form.clone()),
    ];
    let body_return = body_return.map(|(ty, continue_variant, return_variant, _)| {
        (ty, continue_variant, return_variant, body_result_type)
    });
    Ok((binding, form, helper, mutable_outputs, body_return))
}

fn rewrite_async_child_returns(expression: &mut Expr, return_variant: &str) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#fn") {
                return Ok(());
            }
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#return") {
                if items.len() != 2 {
                    return Err("@async-fn child #return requires exactly one value".into());
                }
                items[1] = Expr::List(vec![Expr::Symbol(return_variant.into()), items[1].clone()]);
                return Ok(());
            }
            for item in items {
                rewrite_async_child_returns(item, return_variant)?;
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            for statement in statements {
                match statement {
                    crate::Statement::Expr(value)
                    | crate::Statement::Return(Some(value))
                    | crate::Statement::BreakValue(value)
                    | crate::Statement::BreakToValue { value, .. } => {
                        rewrite_async_child_returns(value, return_variant)?;
                    }
                    _ => {}
                }
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => {
            rewrite_async_child_returns(expression, return_variant)?;
        }
        _ => {}
    }
    Ok(())
}

fn normalize_async_loop_await_types(expression: &mut Expr) -> Result<(), String> {
    fn find_nested_loops(expression: &mut Expr) -> Result<(), String> {
        match expression {
            Expr::List(items) => {
                if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#loop" | "#while"))
                {
                    return normalize_async_loop_await_types(expression);
                }
                for item in items.iter_mut().skip(1) {
                    find_nested_loops(item)?;
                }
            }
            Expr::Block(statements) | Expr::Loop(statements) => {
                for statement in statements {
                    if let crate::Statement::Expr(value) = statement {
                        find_nested_loops(value)?;
                    }
                }
            }
            Expr::Labeled { expression, .. }
            | Expr::Unquote(expression)
            | Expr::UnquoteSplicing(expression) => find_nested_loops(expression)?,
            _ => {}
        }
        Ok(())
    }

    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#for" | "#for-range"))
            {
                let loop_name = match items.first() {
                    Some(Expr::Symbol(name)) => name.clone(),
                    _ => unreachable!(),
                };
                for statement in items.iter_mut().skip(4) {
                    if let Expr::List(binding) = statement {
                        if matches!(binding.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let" | "#let-mut"))
                            && binding.len() == 4
                        {
                            let binding_type_expression = normalize_keywords(binding[2].clone());
                            let binding_name =
                                symbol(&binding[1], "for-range await binding")?.to_owned();
                            if let Expr::List(await_items) = &mut binding[3] {
                                if matches!(await_items.first(), Some(Expr::Symbol(head)) if head == "#await")
                                    && await_items.len() == 7
                                {
                                    let await_type = parse_type(Some(&normalize_keywords(
                                        await_items[1].clone(),
                                    )))?;
                                    let binding_type = parse_type(Some(&binding_type_expression))?;
                                    if await_type != binding_type {
                                        return Err(format!(
                                            "@async-fn {loop_name} #await result type does not match binding '{binding_name}'"
                                        ));
                                    }
                                    await_items.remove(1);
                                }
                            }
                        }
                    }
                    normalize_async_loop_await_types(statement)?;
                }
                return Ok(());
            }
            let loop_head = match items.first() {
                Some(Expr::Symbol(head)) if head == "#loop" => Some("#loop"),
                Some(Expr::Symbol(head)) if head == "#while" => Some("#while"),
                _ => None,
            };
            if let Some(loop_head) = loop_head {
                let body_start = if loop_head == "#while" { 2 } else { 1 };
                if loop_head == "#while" {
                    if let Some(Expr::List(await_items)) = items.get_mut(1) {
                        if matches!(await_items.first(), Some(Expr::Symbol(head)) if head == "#await")
                            && await_items.len() == 7
                        {
                            let await_type =
                                parse_type(Some(&normalize_keywords(await_items[1].clone())))?;
                            let bool_type = parse_type(Some(&Expr::Symbol("bool".into())))?;
                            if await_type != bool_type {
                                return Err(
                                    "@async-fn nested while condition await must produce bool"
                                        .into(),
                                );
                            }
                            await_items.remove(1);
                        }
                    }
                }
                for statement in items.iter_mut().skip(body_start) {
                    if let Expr::List(binding) = statement {
                        if matches!(binding.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let" | "#let-mut"))
                            && binding.len() == 4
                        {
                            let binding_type =
                                parse_type(Some(&normalize_keywords(binding[2].clone())))?;
                            if let Expr::List(await_items) = &mut binding[3] {
                                if matches!(await_items.first(), Some(Expr::Symbol(head)) if head == "#await")
                                    && await_items.len() == 7
                                {
                                    let await_type = parse_type(Some(&normalize_keywords(
                                        await_items[1].clone(),
                                    )))?;
                                    if binding_type != await_type {
                                        return Err(
                                            "@async-fn nested loop await result type does not match its binding"
                                                .into(),
                                        );
                                    }
                                    await_items.remove(1);
                                }
                            }
                        } else {
                            find_nested_loops(statement)?;
                        }
                    } else {
                        find_nested_loops(statement)?;
                    }
                }
            } else {
                for item in items.iter_mut().skip(1) {
                    find_nested_loops(item)?;
                }
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                if let crate::Statement::Expr(value) = statement {
                    find_nested_loops(value)?;
                }
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => find_nested_loops(expression)?,
        _ => {}
    }
    Ok(())
}

/// Lower a multi-suspension `#while-let` body into a nested async child. The
/// child takes ownership of its scrutinee and re-establishes the selected
/// pattern bindings before executing the source body. Its outcome distinguishes
/// an iteration continuation from a return out of the enclosing function.
fn lower_async_while_let_multi_await_body(
    items: &[Expr],
    condition_await: &[Expr],
    condition_helper: &str,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &Expr,
    return_type: Option<&Expr>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>)>, String> {
    let scrutinee = fresh_async_name(source, next_name);
    let mut child_known = known.clone();
    child_known.insert(
        scrutinee.clone(),
        Binding {
            name: scrutinee.clone(),
            ty: expression_source(&condition_await[1])?,
            mutable: false,
        },
    );
    let mut child_order = known_order.to_vec();
    child_order.push(scrutinee.clone());

    let mut child_body = vec![Expr::List(vec![
        Expr::Symbol("#let-else".into()),
        items[1].clone(),
        condition_await[1].clone(),
        Expr::Symbol(scrutinee),
        Expr::List(vec![Expr::Symbol("#unreachable".into())]),
    ])];
    child_body.extend(items[3..].iter().cloned());
    let (body_binding, body_form, body_helper, body_outputs, body_return) = async_while_body_child(
        &child_body,
        &child_known,
        &child_order,
        source,
        next_name,
        waker,
        true,
        child_order.last().map(String::as_str),
        return_type,
    )?;

    let mut lowered_items = items[..3].to_vec();
    lowered_items.push(Expr::List(body_form));
    let body_value = if let Some((_, continue_variant, return_variant, payload_type)) = body_return
    {
        let payload = fresh_async_name(source, next_name);
        let returned = fresh_async_name(source, next_name);
        lowered_items.push(Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(payload.clone()),
            payload_type,
            Expr::List(vec![
                Expr::Symbol("#match".into()),
                Expr::Symbol(body_binding.name.clone()),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::List(vec![
                        Expr::Symbol(continue_variant),
                        Expr::Symbol(payload.clone()),
                    ]),
                    Expr::Symbol(payload.clone()),
                ]),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::List(vec![
                        Expr::Symbol(return_variant),
                        Expr::Symbol(returned.clone()),
                    ]),
                    Expr::List(vec![
                        Expr::Symbol("#block".into()),
                        Expr::List(vec![Expr::Symbol("#return".into()), Expr::Symbol(returned)]),
                    ]),
                ]),
            ]),
        ]));
        payload
    } else {
        body_binding.name.clone()
    };
    let stopped = if body_outputs.is_empty() {
        Expr::Symbol(body_value.clone())
    } else {
        let stopped_name = fresh_async_name(source, next_name);
        let mut pattern = vec![
            Expr::Symbol("#tuple".into()),
            Expr::Symbol(stopped_name.clone()),
        ];
        let mut fields = vec![Expr::Symbol("bool".into())];
        let mut output_names = Vec::with_capacity(body_outputs.len());
        for capture in &body_outputs {
            let output_name = fresh_async_name(source, next_name);
            output_names.push(output_name.clone());
            pattern.push(Expr::Symbol(output_name));
            fields.push(crate::parse(&capture.ty)?[0].expr.clone());
        }
        lowered_items.push(Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::List(pattern),
            Expr::List(
                std::iter::once(Expr::Symbol("#tuple".into()))
                    .chain(fields)
                    .collect(),
            ),
            Expr::Symbol(body_value),
        ]));
        for (capture, output_name) in body_outputs.iter().zip(output_names) {
            lowered_items.push(Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(capture.name.clone()),
                Expr::Symbol(output_name),
            ]));
        }
        Expr::Symbol(stopped_name)
    };
    lowered_items.push(Expr::List(vec![
        Expr::Symbol("#if".into()),
        stopped,
        Expr::List(vec![Expr::Symbol("#break".into())]),
        Expr::List(vec![Expr::Symbol("#continue".into())]),
    ]));

    let Some((replacement, loop_helper, renames)) = lower_async_while_let_body_await(
        &lowered_items,
        condition_await,
        condition_helper,
        Some(
            child_order
                .last()
                .expect("the synthetic scrutinee was appended to child bindings"),
        ),
        known,
        known_order,
        following,
        return_value,
        return_type,
        source,
        next_name,
        waker,
    )?
    else {
        return Ok(None);
    };
    let helper = [body_helper, loop_helper]
        .into_iter()
        .filter(|helper| !helper.is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    Ok(Some((replacement, helper, renames)))
}

/// Lower a while loop with one await binding per iteration into a concrete
/// child task. Its poll helper runs ready iterations in a normal Lim loop and
/// stores the current captures plus child task only when the child is pending.
fn lower_async_while_let_body_await(
    items: &[Expr],
    condition_await: &[Expr],
    condition_helper: &str,
    body_task_scrutinee: Option<&str>,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &Expr,
    return_type: Option<&Expr>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>)>, String> {
    if items.len() < 5 {
        return Err(
            "@async-fn awaited #while-let body suspension requires a direct binding".into(),
        );
    }
    let body = &items[3..];
    if body[1..].iter().any(has_await) {
        return Err("@async-fn awaited #while-let supports one direct body-await binding".into());
    }
    let body_binding = binding(&body[0], "awaited while-let body")?;
    let body_form = form(&body[0], "#let")
        .or_else(|| form(&body[0], "#let-mut"))
        .ok_or_else(|| {
            "@async-fn awaited #while-let body suspension requires a direct binding".to_owned()
        })?;
    let (body_await, body_helper) = if let Some(await_form) = form(&body_form[3], "#await") {
        let awaited = if await_form.len() == 6 {
            std::iter::once(Expr::Symbol("#await".into()))
                .chain(std::iter::once(body_form[2].clone()))
                .chain(await_form[1..].iter().cloned())
                .collect()
        } else {
            await_form.to_vec()
        };
        (awaited, String::new())
    } else if let Some((protocol, task, helper)) =
        conditional_await_with_immediate(&body_form[3], known, source, next_name, waker)?
    {
        (
            vec![
                Expr::Symbol("#await".into()),
                protocol.result_type,
                protocol.child_type,
                protocol.pending,
                protocol.ready,
                protocol.poll,
                task,
            ],
            helper,
        )
    } else {
        return Err(
            "@async-fn awaited #while-let body binding requires a direct or conditional #await"
                .into(),
        );
    };
    if body_await.len() != 7 || has_await(&body_await[6]) || has_await(&condition_await[6]) {
        return Err(
            "@async-fn awaited #while-let composition requires non-suspending child-task expressions".into(),
        );
    }

    let mut task_names = HashSet::new();
    collect_value_names(&body_await[6], &mut task_names);
    let captures = known_order
        .iter()
        .filter(|name| task_names.contains(*name))
        .filter_map(|name| known.get(name).cloned())
        .collect::<Vec<_>>();
    for capture in &captures {
        let parsed_type = crate::parse(&capture.ty)?;
        let type_expression = parsed_type
            .first()
            .ok_or_else(|| "@async-fn capture type is empty".to_owned())?;
        let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
        if !async_task_capture_is_copy(&ty) {
            return Err(format!(
                "@async-fn composed awaited while-let body captures non-Copy local '{}'; move its task inputs into an explicit child task",
                capture.name
            ));
        }
    }

    let base = fresh_async_name(source, next_name);
    let composite_task = format!("{base}-scrutinee-body-task");
    let wait_scrutinee = format!("{base}-wait-scrutinee");
    let wait_body = format!("{base}-wait-body");
    let composite_result = format!("{base}-scrutinee-body-poll-result");
    let composite_pending = format!("{base}-scrutinee-body-pending");
    let composite_ready = format!("{base}-scrutinee-body-ready");
    let composite_poll = format!("{base}-scrutinee-body-poll");
    let decision_type = format!("{base}-scrutinee-body-decision");
    let stop_variant = format!("{base}-stop");
    let continue_variant = format!("{base}-continue");
    let scrutinee_type = expression_source(&condition_await[1])?;
    let condition_child = expression_source(&condition_await[2])?;
    let condition_pending = symbol(&condition_await[3], "while-let Pending variant")?;
    let condition_ready = symbol(&condition_await[4], "while-let Ready variant")?;
    let condition_poll = symbol(&condition_await[5], "while-let poll function")?;
    let condition_task = condition_await[6].clone();
    let pattern = expression_source(&items[1])?;
    let scrutinee_name = fresh_async_name(source, next_name);
    let body_child = expression_source(&body_await[2])?;
    let body_pending = symbol(&body_await[3], "while-let body Pending variant")?;
    let body_ready = symbol(&body_await[4], "while-let body Ready variant")?;
    let body_poll = symbol(&body_await[5], "while-let body poll function")?;
    let mut body_task_expression = body_await[6].clone();
    if let Some(parameter) = body_task_scrutinee {
        rename_async_value(&mut body_task_expression, parameter, "scrutinee");
    }
    let body_task = expression_source(&body_task_expression)?;
    let body_result_type = body_binding.ty.as_str();
    let capture_types = captures
        .iter()
        .map(|capture| capture.ty.as_str())
        .collect::<Vec<_>>();
    let capture_names = captures
        .iter()
        .map(|capture| capture.name.as_str())
        .collect::<Vec<_>>();
    let moves_scrutinee = body_task_scrutinee.is_some();
    let scrutinee_fields = std::iter::once(condition_child.as_str())
        .chain(capture_types.iter().copied())
        .collect::<Vec<_>>()
        .join(" ");
    let body_fields = if moves_scrutinee {
        std::iter::once(body_child.as_str())
            .chain(capture_types.iter().copied())
            .collect::<Vec<_>>()
            .join(" ")
    } else {
        [scrutinee_type.as_str(), body_child.as_str()]
            .into_iter()
            .chain(capture_types.iter().copied())
            .collect::<Vec<_>>()
            .join(" ")
    };
    let capture_pattern = capture_names.join(" ");
    let scrutinee_pattern = if capture_pattern.is_empty() {
        "child".to_owned()
    } else {
        format!("child {capture_pattern}")
    };
    let body_pattern = if moves_scrutinee && capture_pattern.is_empty() {
        "child".to_owned()
    } else if moves_scrutinee {
        format!("child {capture_pattern}")
    } else if capture_pattern.is_empty() {
        "scrutinee child".to_owned()
    } else {
        format!("scrutinee child {capture_pattern}")
    };
    let scrutinee_pending_state = std::iter::once(format!("{wait_scrutinee} pending"))
        .chain(capture_names.iter().map(|name| (*name).to_owned()))
        .collect::<Vec<_>>()
        .join(" ");
    let body_pending_state = if moves_scrutinee {
        std::iter::once(format!("{wait_body} pending"))
            .chain(capture_names.iter().map(|name| (*name).to_owned()))
            .collect::<Vec<_>>()
            .join(" ")
    } else {
        std::iter::once(format!("{wait_body} scrutinee pending"))
            .chain(capture_names.iter().map(|name| (*name).to_owned()))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let continue_fields = if moves_scrutinee {
        body_result_type.to_owned()
    } else {
        format!("{scrutinee_type} {body_result_type}")
    };
    let condition_ready_body = if moves_scrutinee {
        format!(
            "(#match (#call {body_poll} (: task {body_task} : waker waker))\n\
               (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
               (#case ({body_ready} value) ({composite_ready} ({continue_variant} value))))"
        )
    } else {
        format!(
            "(#match scrutinee\n\
               (#case {pattern}\n\
                 (#match (#call {body_poll} (: task {body_task} : waker waker))\n\
                   (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                   (#case ({body_ready} value) ({composite_ready} ({continue_variant} scrutinee value)))))\n\
               (#case _ ({composite_ready} {stop_variant})))"
        )
    };
    let body_ready_result = if moves_scrutinee {
        format!("({composite_ready} ({continue_variant} value))")
    } else {
        format!("({composite_ready} ({continue_variant} scrutinee value))")
    };
    let composite_helper = format!(
        "(#enum {decision_type} ({stop_variant} ({continue_variant} {continue_fields})))\n\
         (#enum {composite_task} (({wait_scrutinee} {scrutinee_fields}) ({wait_body} {body_fields})))\n\
         (#linear {composite_task})\n\
         (#enum {composite_result} (({composite_pending} {composite_task}) ({composite_ready} {decision_type})))\n\
         (#fn {composite_poll} ((task {composite_task}) (waker (#ref {waker}))) {composite_result}\n\
           (#return (#match task\n\
             (#case ({wait_scrutinee} {scrutinee_pattern})\n\
               (#match (#call {condition_poll} (: task child : waker waker))\n\
                 (#case ({condition_pending} pending) ({composite_pending} ({scrutinee_pending_state})))\n\
                 (#case ({condition_ready} scrutinee)\n\
                    {condition_ready_body})))\n\
              (#case ({wait_body} {body_pattern})\n\
                (#match (#call {body_poll} (: task child : waker waker))\n\
                  (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                  (#case ({body_ready} value) {body_ready_result}))))))"
    );

    let decision_name = fresh_async_name(source, next_name);
    let stopped_name = fresh_async_name(source, next_name);
    let body_stopped_name = fresh_async_name(source, next_name);
    let body_value_name = fresh_async_name(source, next_name);
    let body_binding_head = if body_binding.mutable {
        "#let-mut"
    } else {
        "#let"
    };
    let mut success = vec![Expr::Symbol("#block".into())];
    success.push(Expr::List(vec![
        Expr::Symbol("#let-mut".into()),
        Expr::Symbol(body_stopped_name.clone()),
        Expr::Symbol("bool".into()),
        Expr::Symbol("false".into()),
    ]));
    success.push(Expr::List(vec![
        Expr::Symbol(body_binding_head.into()),
        Expr::Symbol(body_binding.name),
        Expr::Symbol(body_binding.ty),
        Expr::Symbol(body_value_name.clone()),
    ]));
    success.extend(body[1..].iter().cloned());
    if success.len() > 3 && contains_loop_control(success.last().expect("body has a stop local")) {
        rewrite_while_let_terminal(
            success.last_mut().expect("body has a stop local"),
            &body_stopped_name,
        )?;
    }
    success.push(Expr::Symbol(body_stopped_name.clone()));
    let matched = if moves_scrutinee {
        Expr::List(success)
    } else {
        Expr::List(vec![
            Expr::Symbol("#match".into()),
            Expr::Symbol(scrutinee_name.clone()),
            Expr::List(vec![
                Expr::Symbol("#case".into()),
                items[1].clone(),
                Expr::List(success),
            ]),
            Expr::List(vec![
                Expr::Symbol("#case".into()),
                Expr::Symbol("_".into()),
                Expr::List(vec![Expr::Symbol("#unreachable".into())]),
            ]),
        ])
    };
    let continue_pattern = if moves_scrutinee {
        Expr::List(vec![
            Expr::Symbol(continue_variant),
            Expr::Symbol(body_value_name),
        ])
    } else {
        Expr::List(vec![
            Expr::Symbol(continue_variant),
            Expr::Symbol(scrutinee_name),
            Expr::Symbol(body_value_name),
        ])
    };
    let stopped_value = Expr::List(vec![
        Expr::Symbol("#match".into()),
        Expr::Symbol(decision_name.clone()),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            Expr::Symbol(stop_variant),
            Expr::Symbol("true".into()),
        ]),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            continue_pattern,
            matched,
        ]),
    ]);
    let mut condition_state = vec![Expr::Symbol(wait_scrutinee), condition_task];
    condition_state.extend(
        captures
            .iter()
            .map(|capture| Expr::Symbol(capture.name.clone())),
    );
    let loop_form = Expr::List(vec![
        Expr::Symbol("#loop".into()),
        Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(decision_name),
            Expr::Symbol(decision_type),
            Expr::List(vec![
                Expr::Symbol("#await".into()),
                Expr::Symbol(composite_task),
                Expr::Symbol(composite_pending),
                Expr::Symbol(composite_ready),
                Expr::Symbol(composite_poll),
                Expr::List(condition_state),
            ]),
        ]),
        Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(stopped_name.clone()),
            Expr::Symbol("bool".into()),
            stopped_value,
        ]),
        Expr::List(vec![
            Expr::Symbol("#if".into()),
            Expr::Symbol(stopped_name),
            Expr::List(vec![Expr::Symbol("#break".into())]),
            Expr::List(vec![Expr::Symbol("#continue".into())]),
        ]),
    ]);
    let Some((replacement, loop_helper, renames)) = lower_async_loop_with_transfers(
        &loop_form,
        known,
        known_order,
        &[],
        following,
        return_value,
        return_type,
        source,
        next_name,
        waker,
    )?
    else {
        return Ok(None);
    };
    let helper = [
        condition_helper,
        body_helper.as_str(),
        composite_helper.as_str(),
        loop_helper.as_str(),
    ]
    .into_iter()
    .filter(|helper| !helper.is_empty())
    .collect::<Vec<_>>()
    .join("\n");
    Ok(Some((replacement, helper, renames)))
}

fn lower_async_while(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &mut Expr,
    return_type: &Expr,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>, usize, bool)>, String> {
    if let Some(items) = form(statement, "#while") {
        let condition = if let Some(await_form) = form(&items[1], "#await") {
            (Some(await_form.to_vec()), String::new())
        } else if let Some((protocol, task, helper)) =
            conditional_value_expression_task(&items[1], known, source, next_name, waker)?
        {
            (
                Some(vec![
                    Expr::Symbol("#await".into()),
                    protocol.child_type,
                    protocol.pending,
                    protocol.ready,
                    protocol.poll,
                    task,
                ]),
                helper,
            )
        } else {
            (None, String::new())
        };
        let return_index = items.len().saturating_sub(1);
        let body_exit = if items.len() >= 3
            && !(items[2..].iter().any(has_await) && contains_loop_control(&items[return_index]))
        {
            async_terminal_loop_exit_with_return_marker(
                &items[return_index],
                return_value,
                items[2..].iter().any(has_await).then_some(return_type),
                None,
            )
        } else {
            None
        };
        if let (Some(mut await_form), Some((body_return, true))) = (condition.0, body_exit) {
            match await_form.len() {
                6 => {}
                7 => {
                    let result_type = parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
                    if result_type != Type::Bool {
                        return Err(
                            "@async-fn awaited #while condition #await result type must be bool"
                                .into(),
                        );
                    }
                    await_form.remove(1);
                }
                _ => {
                    return Err(
                        "@async-fn awaited #while condition requires (#await [bool] Child Pending Ready poll task)"
                            .into(),
                    );
                }
            }
            if following
                .iter()
                .any(|statement| contains_return(statement) || contains_loop_control(statement))
                || has_await(await_form.last().expect("await has a task"))
            {
                return Err(
                    "@async-fn awaited #while body cannot return in this shape yet; early return requires a terminal condition await and a continuation without control transfers"
                        .into(),
                );
            }
            let condition_name = fresh_async_name(source, next_name);
            let condition_binding = Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(condition_name.clone()),
                Expr::Symbol("bool".into()),
                Expr::List(await_form),
            ]);
            let mut replacement = vec![condition_binding];
            let returned_body = if return_index == 2 {
                body_return
            } else {
                Expr::List(
                    std::iter::once(Expr::Symbol("#block".into()))
                        .chain(items[2..return_index].iter().cloned())
                        .chain(std::iter::once(body_return))
                        .collect(),
                )
            };
            let result_name = fresh_async_name(source, next_name);
            let (false_branch, consumes_return_await) =
                if let Some(await_form) = form(return_value, "#await") {
                    let typed_await = match await_form.len() {
                        6 => std::iter::once(Expr::Symbol("#await".into()))
                            .chain(std::iter::once(return_type.clone()))
                            .chain(await_form[1..].iter().cloned())
                            .collect(),
                        7 => await_form.to_vec(),
                        _ => return Err("@async-fn final #return await has an invalid form".into()),
                    };
                    (Expr::List(typed_await), true)
                } else {
                    (
                        if following.is_empty() {
                            return_value.clone()
                        } else {
                            Expr::List(
                                std::iter::once(Expr::Symbol("#block".into()))
                                    .chain(following.iter().cloned())
                                    .chain(std::iter::once(return_value.clone()))
                                    .collect(),
                            )
                        },
                        false,
                    )
                };
            replacement.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                return_type.clone(),
                Expr::List(vec![
                    Expr::Symbol("#if".into()),
                    Expr::Symbol(condition_name),
                    returned_body,
                    false_branch,
                ]),
            ]));
            *return_value = Expr::Symbol(result_name);
            return Ok(Some((
                replacement,
                condition.1,
                Vec::new(),
                following.len(),
                consumes_return_await,
            )));
        }
    }
    Ok(lower_async_while_with_transfers(
        statement,
        known,
        known_order,
        &[],
        &[],
        following,
        return_value,
        Some(return_type),
        source,
        next_name,
        waker,
    )?
    .map(|(replacement, helper, renames)| (replacement, helper, renames, 0, false)))
}

fn lower_async_while_with_return_continue(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &mut Expr,
    return_type: &Expr,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>, usize, bool)>, String> {
    let Some(items) = form(statement, "#while") else {
        return Ok(None);
    };
    if items.len() < 3
        || following
            .iter()
            .any(|statement| contains_return(statement) || contains_loop_control(statement))
    {
        return Ok(None);
    }
    let (condition_await, condition_helper) = if let Some(await_form) = form(&items[1], "#await") {
        (await_form.to_vec(), String::new())
    } else if let Some((protocol, task, helper)) =
        conditional_value_expression_task(&items[1], known, source, next_name, waker)?
    {
        (
            vec![
                Expr::Symbol("#await".into()),
                protocol.child_type,
                protocol.pending,
                protocol.ready,
                protocol.poll,
                task,
            ],
            helper,
        )
    } else {
        return Ok(None);
    };
    if condition_await.len() != 6
        || has_await(&condition_await[5])
        || items[2..].iter().any(has_await)
    {
        return Ok(None);
    }
    let return_type_ast = parse_type(Some(&normalize_keywords(return_type.clone())))?;
    let return_type_is_copy = async_task_capture_is_copy(&return_type_ast);
    let terminal = items.len() - 1;
    if !contains_return(&items[terminal])
        || async_terminal_loop_exit(&items[terminal], &Expr::Symbol("lim.async.tail".into()))
            .is_some()
        || items[2..terminal]
            .iter()
            .any(|statement| contains_loop_control(statement) || contains_return(statement))
    {
        return Ok(None);
    }

    let status_type = fresh_async_name(source, next_name);
    let status_name = fresh_async_name(source, next_name);
    let tail_variant = format!("{status_type}-tail");
    let returned_variant = format!("{status_type}-returned");
    let result_name = fresh_async_name(source, next_name);
    let Some((body, true)) = items.last().and_then(|terminal| {
        rewrite_async_loop_returns(
            terminal,
            &status_name,
            &returned_variant,
            !return_type_is_copy,
        )
    }) else {
        return Ok(None);
    };

    let return_type_source = expression_source(return_type)?;
    let mut rewritten_loop = statement.clone();
    let Expr::List(loop_items) = &mut rewritten_loop else {
        unreachable!("while form is a list")
    };
    loop_items[1] = Expr::List(condition_await);
    *loop_items.last_mut().expect("while has terminal body") = body;

    let mut loop_known = known.clone();
    loop_known.insert(
        status_name.clone(),
        Binding {
            name: status_name.clone(),
            ty: status_type.clone(),
            mutable: true,
        },
    );
    let mut loop_known_order = known_order.to_vec();
    loop_known_order.push(status_name.clone());
    let (return_tail, consumes_return_await) =
        if let Some(await_form) = form(return_value, "#await") {
            let typed_await = match await_form.len() {
                6 => std::iter::once(Expr::Symbol("#await".into()))
                    .chain(std::iter::once(return_type.clone()))
                    .chain(await_form[1..].iter().cloned())
                    .collect(),
                7 => await_form.to_vec(),
                _ => return Err("@async-fn final #return await has an invalid form".into()),
            };
            (Expr::List(typed_await), true)
        } else {
            (return_value.clone(), false)
        };
    let tail_value = if following.is_empty() {
        return_tail
    } else {
        Expr::List(
            std::iter::once(Expr::Symbol("#block".into()))
                .chain(following.iter().cloned())
                .chain(std::iter::once(return_tail))
                .collect(),
        )
    };
    let mut loop_return = Expr::List(vec![
        Expr::Symbol("#match".into()),
        Expr::Symbol(status_name.clone()),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            Expr::Symbol(tail_variant.clone()),
            tail_value,
        ]),
        Expr::List(vec![
            Expr::Symbol("#case".into()),
            Expr::List(vec![
                Expr::Symbol(returned_variant.clone()),
                Expr::Symbol(result_name.clone()),
            ]),
            Expr::Symbol(result_name),
        ]),
    ]);
    let Some((mut replacement, loop_helper, renames, _, _)) = lower_async_while(
        &rewritten_loop,
        &loop_known,
        &loop_known_order,
        following,
        &mut loop_return,
        return_type,
        source,
        next_name,
        waker,
    )?
    else {
        return Ok(None);
    };
    *return_value = loop_return;
    replacement.insert(
        0,
        Expr::List(vec![
            Expr::Symbol("#let-mut".into()),
            Expr::Symbol(status_name),
            Expr::Symbol(status_type.clone()),
            Expr::List(vec![Expr::Symbol(tail_variant.clone())]),
        ]),
    );
    let status_declarations = format!(
        "(#enum {status_type} (({tail_variant}) ({returned_variant} {return_type_source})))"
    );
    let status_declarations = if return_type_is_copy {
        status_declarations
    } else {
        format!("{status_declarations}\n(#linear {status_type})")
    };
    Ok(Some((
        replacement,
        [status_declarations, condition_helper, loop_helper]
            .into_iter()
            .filter(|declaration| !declaration.is_empty())
            .collect::<Vec<_>>()
            .join("\n"),
        renames,
        following.len(),
        consumes_return_await,
    )))
}

fn async_while_has_terminal_return(statement: &Expr) -> bool {
    let Some(items) = form(statement, "#while") else {
        return false;
    };
    if items.len() < 3 || !has_await(&items[1]) {
        return false;
    }
    items.last().is_some_and(|last| {
        async_terminal_loop_exit(last, &Expr::Symbol("lim.async.tail".into()))
            .is_some_and(|(_, contains_return)| contains_return)
    })
}

fn async_terminal_loop_exit(expression: &Expr, tail: &Expr) -> Option<(Expr, bool)> {
    async_terminal_loop_exit_with_return_marker(expression, tail, None, None)
}

fn async_terminal_panics(expression: &Expr) -> bool {
    if form(expression, "#panic").is_some() {
        return true;
    }
    if let Some(block) = form(expression, "#block") {
        return block.last().is_some_and(async_terminal_panics);
    }
    if let Some(conditional) = form(expression, "#if") {
        return conditional.len() == 4
            && async_terminal_panics(&conditional[2])
            && async_terminal_panics(&conditional[3]);
    }
    if let Some(match_form) = form(expression, "#match") {
        return match_form.len() >= 3
            && match_form[2..].iter().all(|arm| {
                let Some(case) = form(arm, "#case") else {
                    return false;
                };
                let body = match case.len() {
                    3 => &case[2],
                    4 if form(&case[2], "#when").is_some() => &case[3],
                    _ => return false,
                };
                async_terminal_panics(body)
            });
    }
    false
}

fn async_terminal_loop_exit_with_return_marker(
    expression: &Expr,
    tail: &Expr,
    return_type: Option<&Expr>,
    unreachable_return_type: Option<&Expr>,
) -> Option<(Expr, bool)> {
    if form(expression, "#panic").is_some() {
        return Some((expression.clone(), false));
    }
    if let Some(return_form) = form(expression, "#return") {
        return (return_form.len() == 2).then(|| {
            let returned = if let Some(return_type) = return_type {
                Expr::List(vec![
                    Expr::Symbol("#async-terminal-return".into()),
                    return_type.clone(),
                    return_form[1].clone(),
                ])
            } else {
                return_form[1].clone()
            };
            (returned, true)
        });
    }
    if form(expression, "#unreachable").is_some() {
        if let Some(return_type) = unreachable_return_type {
            return Some((
                Expr::List(vec![
                    Expr::Symbol("#async-terminal-return".into()),
                    return_type.clone(),
                    expression.clone(),
                ]),
                true,
            ));
        }
    }
    if let Some(break_form) = form(expression, "#break") {
        return (break_form.len() == 1).then(|| (tail.clone(), false));
    }
    if let Some(block) = form(expression, "#block") {
        if block.len() < 2 {
            return None;
        }
        let (returned, contains_return) = async_terminal_loop_exit_with_return_marker(
            block.last()?,
            tail,
            return_type,
            unreachable_return_type,
        )?;
        return Some((
            Expr::List(
                block[..block.len() - 1]
                    .iter()
                    .cloned()
                    .chain(std::iter::once(returned))
                    .collect(),
            ),
            contains_return,
        ));
    }
    if let Some(conditional) = form(expression, "#if") {
        if conditional.len() != 4 {
            return None;
        }
        let (then_value, then_returns) = async_terminal_loop_exit_with_return_marker(
            &conditional[2],
            tail,
            return_type,
            unreachable_return_type,
        )?;
        let (else_value, else_returns) = async_terminal_loop_exit_with_return_marker(
            &conditional[3],
            tail,
            return_type,
            unreachable_return_type,
        )?;
        return Some((
            Expr::List(vec![
                conditional[0].clone(),
                conditional[1].clone(),
                then_value,
                else_value,
            ]),
            then_returns || else_returns,
        ));
    }
    let match_form = form(expression, "#match")?;
    if match_form.len() < 3 {
        return None;
    }
    let mut lowered = match_form[..2].to_vec();
    let mut any_return = false;
    for arm in &match_form[2..] {
        let case = form(arm, "#case")?;
        let body_index = match case.len() {
            3 => 2,
            4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
            _ => return None,
        };
        let (returned, contains_return) = async_terminal_loop_exit_with_return_marker(
            &case[body_index],
            tail,
            return_type,
            unreachable_return_type,
        )?;
        any_return |= contains_return;
        lowered.push(Expr::List(
            case[..body_index]
                .iter()
                .cloned()
                .chain(std::iter::once(returned))
                .collect(),
        ));
    }
    Some((Expr::List(lowered), any_return))
}

fn rewrite_async_loop_returns(
    expression: &Expr,
    status: &str,
    returned_variant: &str,
    linear_status: bool,
) -> Option<(Expr, bool)> {
    if let Some(return_form) = form(expression, "#return") {
        if return_form.len() != 2 || has_await(&return_form[1]) {
            return None;
        }
        let mut statements = vec![Expr::Symbol("#block".into())];
        if linear_status {
            statements.push(Expr::List(vec![
                Expr::Symbol("#forget".into()),
                Expr::Symbol(status.into()),
            ]));
        }
        statements.extend([
            Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(status.into()),
                Expr::List(vec![
                    Expr::Symbol(returned_variant.into()),
                    return_form[1].clone(),
                ]),
            ]),
            Expr::List(vec![Expr::Symbol("#break".into())]),
        ]);
        return Some((Expr::List(statements), true));
    }
    if let Some(block) = form(expression, "#block") {
        if block.len() < 2 || block[1..block.len() - 1].iter().any(contains_return) {
            return None;
        }
        let (last, found) =
            rewrite_async_loop_returns(block.last()?, status, returned_variant, linear_status)?;
        let mut lowered = block.to_vec();
        *lowered.last_mut()? = last;
        return Some((Expr::List(lowered), found));
    }
    if let Some(conditional) = form(expression, "#if") {
        if conditional.len() != 4 || contains_return(&conditional[1]) {
            return None;
        }
        let mut lowered = conditional.to_vec();
        let mut found = false;
        for index in [2, 3] {
            if contains_return(&conditional[index]) {
                let (branch, branch_found) = rewrite_async_loop_returns(
                    &conditional[index],
                    status,
                    returned_variant,
                    linear_status,
                )?;
                lowered[index] = branch;
                found |= branch_found;
            }
        }
        return found.then_some((Expr::List(lowered), found));
    }
    if let Some(match_form) = form(expression, "#match") {
        if match_form.len() < 3 || contains_return(&match_form[1]) {
            return None;
        }
        let mut lowered = match_form.to_vec();
        let mut found = false;
        for arm_index in 2..match_form.len() {
            let case = form(&match_form[arm_index], "#case")?;
            let body_index = match case.len() {
                3 => 2,
                4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                _ => return None,
            };
            if case[1..body_index].iter().any(contains_return) {
                return None;
            }
            if contains_return(&case[body_index]) {
                let (body, body_found) = rewrite_async_loop_returns(
                    &case[body_index],
                    status,
                    returned_variant,
                    linear_status,
                )?;
                let mut lowered_case = case.to_vec();
                lowered_case[body_index] = body;
                lowered[arm_index] = Expr::List(lowered_case);
                found |= body_found;
            }
        }
        return found.then_some((Expr::List(lowered), found));
    }
    None
}

/// Replace returns in terminal `#for` body control-flow with a marker that is
/// resolved inside the generated iteration task, where it can also stop the
/// separately scheduled awaited step.
fn rewrite_async_for_body_returns(
    expression: &Expr,
    status: &str,
    returned_variant: &str,
    linear_status: bool,
) -> Option<Expr> {
    if let Some(return_form) = form(expression, "#return") {
        if return_form.len() != 2 || has_await(&return_form[1]) {
            return None;
        }
        return Some(Expr::List(vec![
            Expr::Symbol("#async-for-return".into()),
            Expr::Symbol(status.into()),
            Expr::Symbol(returned_variant.into()),
            return_form[1].clone(),
            Expr::Symbol(if linear_status { "true" } else { "false" }.into()),
        ]));
    }
    if let Some(block) = form(expression, "#block") {
        if block.len() < 2 || block[1..block.len() - 1].iter().any(contains_return) {
            return None;
        }
        let mut lowered = block.to_vec();
        *lowered.last_mut()? =
            rewrite_async_for_body_returns(block.last()?, status, returned_variant, linear_status)?;
        return Some(Expr::List(lowered));
    }
    if let Some(conditional) = form(expression, "#if") {
        if conditional.len() != 4 || contains_return(&conditional[1]) {
            return None;
        }
        let mut lowered = conditional.to_vec();
        for index in [2, 3] {
            if contains_return(&conditional[index]) {
                lowered[index] = rewrite_async_for_body_returns(
                    &conditional[index],
                    status,
                    returned_variant,
                    linear_status,
                )?;
            }
        }
        return Some(Expr::List(lowered));
    }
    if let Some(match_form) = form(expression, "#match") {
        if match_form.len() < 3 || contains_return(&match_form[1]) {
            return None;
        }
        let mut lowered = match_form.to_vec();
        for arm_index in 2..match_form.len() {
            let case = form(&match_form[arm_index], "#case")?;
            let body_index = match case.len() {
                3 => 2,
                4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                _ => return None,
            };
            if case[1..body_index].iter().any(contains_return) {
                return None;
            }
            if contains_return(&case[body_index]) {
                let mut lowered_case = case.to_vec();
                lowered_case[body_index] = rewrite_async_for_body_returns(
                    &case[body_index],
                    status,
                    returned_variant,
                    linear_status,
                )?;
                lowered[arm_index] = Expr::List(lowered_case);
            }
        }
        return Some(Expr::List(lowered));
    }
    None
}

fn lower_async_while_with_transfers(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    transfers: &[LoopReferenceTransfer],
    owned_captures: &[String],
    following: &[Expr],
    return_value: &Expr,
    return_type: Option<&Expr>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>)>, String> {
    if !has_await(statement) {
        return Ok(None);
    }
    if let Some(items) = form(statement, "#while-let") {
        if items.len() < 4 {
            return Err(
                "@async-fn awaited #while-let requires a pattern, awaited value, and body".into(),
            );
        }
        if has_suspending_await_input(&items[2]) {
            let mut condition = items[2].clone();
            let mut iteration = Vec::new();
            let mut dependencies = Vec::new();
            extract_nested_awaits(
                &mut condition,
                &mut iteration,
                &mut dependencies,
                known,
                source,
                next_name,
                waker,
            )?;
            iteration.push(Expr::List(vec![
                Expr::Symbol("#match".into()),
                condition,
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    items[1].clone(),
                    terminal_async_iteration_body(&items[3..], source, next_name)?,
                ]),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::Symbol("_".into()),
                    Expr::List(vec![Expr::Symbol("#break".into())]),
                ]),
            ]));
            let mut loop_form = vec![Expr::Symbol("#loop".into())];
            loop_form.extend(iteration);
            let Some((replacement, helper, renames)) = lower_async_loop_with_transfers(
                &Expr::List(loop_form),
                known,
                known_order,
                transfers,
                following,
                return_value,
                return_type,
                source,
                next_name,
                waker,
            )?
            else {
                return Err("@async-fn failed to lower while-let task dependencies".into());
            };
            dependencies.push(helper);
            return Ok(Some((replacement, dependencies.join("\n"), renames)));
        }
        if has_await(&items[2]) {
            let (await_form, conditional_helper) = if let Some(await_form) =
                form(&items[2], "#await")
            {
                (await_form.to_vec(), String::new())
            } else if let Some((protocol, task, helper)) =
                conditional_await_with_immediate(&items[2], known, source, next_name, waker)?
            {
                (
                    vec![
                        Expr::Symbol("#await".into()),
                        protocol.result_type,
                        protocol.child_type,
                        protocol.pending,
                        protocol.ready,
                        protocol.poll,
                        task,
                    ],
                    helper,
                )
            } else if let Some((protocol, task, helper)) =
                conditional_value_expression_task(&items[2], known, source, next_name, waker)?
            {
                (
                    vec![
                        Expr::Symbol("#await".into()),
                        protocol.result_type,
                        protocol.child_type,
                        protocol.pending,
                        protocol.ready,
                        protocol.poll,
                        task,
                    ],
                    helper,
                )
            } else {
                return Err(
                        "@async-fn #while-let requires an awaited scrutinee with an explicit result type".into(),
                    );
            };
            if await_form.len() != 7 {
                return Err(
                    "@async-fn #while-let requires an explicitly typed #await value".into(),
                );
            }
            parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
            if items[3..].iter().any(has_await) || items[3..].iter().any(contains_return) {
                let body_binding_value = items[3..].first().and_then(|statement| {
                    let binding =
                        form(statement, "#let").or_else(|| form(statement, "#let-mut"))?;
                    (binding.len() == 4).then_some(&binding[3])
                });
                let body_has_direct_await_binding = if let Some(value) = body_binding_value {
                    if form(value, "#await").is_some() {
                        true
                    } else {
                        let mut probe_name = *next_name;
                        conditional_await_with_immediate(
                            value,
                            known,
                            source,
                            &mut probe_name,
                            waker,
                        )?
                        .is_some()
                    }
                } else {
                    false
                };
                if items[3..].iter().any(contains_return)
                    || items[3..].iter().map(await_count).sum::<usize>() > 1
                    || !body_has_direct_await_binding
                {
                    return lower_async_while_let_multi_await_body(
                        items,
                        &await_form,
                        &conditional_helper,
                        known,
                        known_order,
                        following,
                        return_value,
                        return_type,
                        source,
                        next_name,
                        waker,
                    );
                }
                return lower_async_while_let_body_await(
                    items,
                    &await_form,
                    &conditional_helper,
                    None,
                    known,
                    known_order,
                    following,
                    return_value,
                    return_type,
                    source,
                    next_name,
                    waker,
                );
            }
            let terminal_index = items.len() - 1;
            if items[3..terminal_index].iter().any(contains_loop_control) {
                return Err("@async-fn #while-let transfers must be terminal statements".into());
            }

            let result_name = fresh_async_name(source, next_name);
            let stopped_name = fresh_async_name(source, next_name);
            let normalized_await = Expr::List(
                std::iter::once(Expr::Symbol("#await".into()))
                    .chain(await_form[2..].iter().cloned())
                    .collect(),
            );
            let await_binding = Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                await_form[1].clone(),
                normalized_await,
            ]);
            let mut matched_body = vec![Expr::Symbol("#block".into())];
            matched_body.extend(items[3..].iter().cloned());
            if matched_body.len() > 1
                && contains_loop_control(matched_body.last().expect("non-empty matched body"))
            {
                rewrite_while_let_terminal(
                    matched_body.last_mut().expect("non-empty matched body"),
                    &stopped_name,
                )?;
            }
            let success_body = Expr::List(vec![
                Expr::Symbol("#block".into()),
                Expr::List(vec![
                    Expr::Symbol("#match".into()),
                    Expr::Symbol(result_name),
                    Expr::List(vec![
                        Expr::Symbol("#case".into()),
                        items[1].clone(),
                        Expr::List(matched_body),
                    ]),
                    Expr::List(vec![
                        Expr::Symbol("#case".into()),
                        Expr::Symbol("_".into()),
                        Expr::List(vec![
                            Expr::Symbol("#block".into()),
                            Expr::List(vec![
                                Expr::Symbol("#set".into()),
                                Expr::Symbol(stopped_name.clone()),
                                Expr::Symbol("true".into()),
                            ]),
                            Expr::List(Vec::new()),
                        ]),
                    ]),
                ]),
            ]);
            let terminal = Expr::List(vec![
                Expr::Symbol("#if".into()),
                Expr::Symbol(stopped_name.clone()),
                Expr::List(vec![Expr::Symbol("#break".into())]),
                Expr::List(vec![Expr::Symbol("#continue".into())]),
            ]);
            let loop_form = Expr::List(vec![
                Expr::Symbol("#loop".into()),
                await_binding,
                Expr::List(vec![
                    Expr::Symbol("#let-mut".into()),
                    Expr::Symbol(stopped_name),
                    Expr::Symbol("bool".into()),
                    Expr::Symbol("false".into()),
                ]),
                success_body,
                terminal,
            ]);
            let Some((replacement, helper, renames)) = lower_async_loop_with_transfers(
                &loop_form,
                known,
                known_order,
                transfers,
                following,
                return_value,
                return_type,
                source,
                next_name,
                waker,
            )?
            else {
                return Ok(None);
            };
            let helper = [conditional_helper, helper]
                .into_iter()
                .filter(|helper| !helper.is_empty())
                .collect::<Vec<_>>()
                .join("\n");
            return Ok(Some((replacement, helper, renames)));
        }
        // Body suspension does not require the scrutinee itself to suspend.
        // Carry its statically declared type through an immediate Ready task
        // and reuse the pattern/loan handling of the awaited-scrutinee path.
        let result_type = if let Expr::Symbol(name) = &items[2] {
            known.get(name).map(|binding| binding.ty.clone())
        } else {
            None
        }
        .or_else(|| {
            let variant = match &items[1] {
                Expr::Symbol(name) => Some(name.as_str()),
                Expr::List(pattern) => pattern.first().and_then(|head| match head {
                    Expr::Symbol(name) => Some(name.as_str()),
                    _ => None,
                }),
                _ => None,
            }?;
            ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
                stack
                    .borrow()
                    .last()?
                    .enums
                    .iter()
                    .find_map(|(name, variants)| {
                        variants.contains_key(variant).then(|| name.clone())
                    })
            })
        })
        .ok_or_else(|| {
            "@async-fn cannot resolve the declared type of a synchronous #while-let scrutinee"
                .to_owned()
        })?;
        let (awaited, helper) = immediate_await(
            &items[2],
            &result_type,
            "scrutinee",
            source,
            next_name,
            waker,
        )?;
        let mut rewritten = items.to_vec();
        rewritten[2] = awaited;
        let Some((replacement, loop_helper, renames)) = lower_async_while_with_transfers(
            &Expr::List(rewritten),
            known,
            known_order,
            transfers,
            owned_captures,
            following,
            return_value,
            return_type,
            source,
            next_name,
            waker,
        )?
        else {
            return Err("@async-fn failed to lower synchronous while-let scrutinee".into());
        };
        return Ok(Some((
            replacement,
            format!("{helper}\n{loop_helper}"),
            renames,
        )));
    }
    let Some(items) = form(statement, "#while") else {
        return Ok(None);
    };
    if items.len() < 3 {
        return Err("@async-fn awaited #while requires a condition and body".into());
    }
    let mut condition = items[1].clone();
    normalize_short_circuit_await(&mut condition);
    if has_suspending_await_input(&condition) {
        // Task-producing awaits belong to every condition evaluation, not to
        // the statement before the loop. Sequence them at the start of an
        // iteration and let the ordinary multi-await body machine retain all
        // local state, mutations and loans between the dependency stages.
        if let Some(await_form) = form(&condition, "#await") {
            if await_form.len() == 6 {
                let Expr::List(items) = &mut condition else {
                    unreachable!()
                };
                items.insert(1, Expr::Symbol("bool".into()));
            }
        }
        let mut iteration = Vec::new();
        let mut dependencies = Vec::new();
        extract_nested_awaits(
            &mut condition,
            &mut iteration,
            &mut dependencies,
            known,
            source,
            next_name,
            waker,
        )?;
        iteration.push(Expr::List(vec![
            Expr::Symbol("#if".into()),
            condition,
            terminal_async_iteration_body(&items[2..], source, next_name)?,
            Expr::List(vec![Expr::Symbol("#break".into())]),
        ]));
        let mut loop_form = vec![Expr::Symbol("#loop".into())];
        loop_form.extend(iteration);
        let Some((replacement, helper, renames)) = lower_async_loop_with_transfers(
            &Expr::List(loop_form),
            known,
            known_order,
            transfers,
            following,
            return_value,
            return_type,
            source,
            next_name,
            waker,
        )?
        else {
            return Err("@async-fn failed to lower condition task dependencies".into());
        };
        dependencies.push(helper);
        return Ok(Some((replacement, dependencies.join("\n"), renames)));
    }
    if has_await(&condition) {
        let (mut await_form, condition_helper) = if let Some(await_form) =
            form(&condition, "#await")
        {
            (await_form.to_vec(), String::new())
        } else if let Some((protocol, task, helper)) =
            conditional_await_with_immediate(&condition, known, source, next_name, waker)?
        {
            (
                vec![
                    Expr::Symbol("#await".into()),
                    protocol.child_type,
                    protocol.pending,
                    protocol.ready,
                    protocol.poll,
                    task,
                ],
                helper,
            )
        } else if let Some((protocol, task, helper)) =
            conditional_value_expression_task(&condition, known, source, next_name, waker)?
        {
            (
                vec![
                    Expr::Symbol("#await".into()),
                    protocol.child_type,
                    protocol.pending,
                    protocol.ready,
                    protocol.poll,
                    task,
                ],
                helper,
            )
        } else {
            return Err(
                "@async-fn awaited #while condition requires a direct #await or conditional #if with a direct #await branch".into(),
            );
        };
        match await_form.len() {
            6 => {}
            7 => {
                let result_type = parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
                if result_type != Type::Bool {
                    return Err(
                        "@async-fn awaited #while condition #await result type must be bool".into(),
                    );
                }
                await_form.remove(1);
            }
            _ => {
                return Err(
                    "@async-fn awaited #while condition requires (#await [bool] Child Pending Ready poll task)"
                        .into(),
                );
            }
        }
        let body = &items[2..];
        if body.iter().any(has_await) {
            let direct_body_await = body.first().is_some_and(|statement| {
                let Some(binding) = form(statement, "#let").or_else(|| form(statement, "#let-mut"))
                else {
                    return false;
                };
                let Some(value) = binding.get(3) else {
                    return false;
                };
                if let Some(await_form) = form(value, "#await") {
                    let task_index = await_form.len().saturating_sub(1);
                    matches!(await_form.len(), 6 | 7)
                        && await_form
                            .get(task_index)
                            .is_some_and(|task| !has_await(task))
                } else {
                    conditional_await_with_immediate(value, known, source, next_name, waker)
                        .ok()
                        .flatten()
                        .is_some_and(|(_, task, _)| !has_await(&task))
                }
            });
            let use_body_child =
                (body.len() > 1 && body[1..].iter().any(has_await)) || !direct_body_await;
            let (
                body_binding,
                body_form,
                body_await,
                body_helper,
                body_continuation,
                body_outputs,
                body_return,
            ) = if use_body_child {
                let (binding, generated_form, helper, outputs, body_return) =
                    async_while_body_child(
                        body,
                        known,
                        known_order,
                        source,
                        next_name,
                        waker,
                        false,
                        None,
                        return_type,
                    )?;
                let await_form = form(&generated_form[3], "#await")
                    .expect("generated loop body binding contains an await")
                    .to_vec();
                (
                    binding,
                    generated_form,
                    await_form,
                    helper,
                    Vec::new(),
                    outputs,
                    body_return,
                )
            } else {
                let body_binding = binding(&body[0], "awaited while body")?;
                let body_form = form(&body[0], "#let")
                    .or_else(|| form(&body[0], "#let-mut"))
                    .ok_or_else(|| {
                        "@async-fn awaited while body suspension requires a direct binding"
                            .to_owned()
                    })?
                    .to_vec();
                let (body_await, body_helper) = if let Some(await_form) =
                    form(&body_form[3], "#await")
                {
                    (await_form.to_vec(), String::new())
                } else if let Some((protocol, task, helper)) = conditional_await_with_immediate(
                    &body_form[3],
                    known,
                    source,
                    next_name,
                    waker,
                )? {
                    (
                        vec![
                            Expr::Symbol("#await".into()),
                            protocol.result_type,
                            protocol.child_type,
                            protocol.pending,
                            protocol.ready,
                            protocol.poll,
                            task,
                        ],
                        helper,
                    )
                } else {
                    return Err(
                                "@async-fn awaited while body binding requires a direct or conditional #await"
                                    .into(),
                            );
                };
                (
                    body_binding,
                    body_form,
                    body_await,
                    body_helper,
                    body[1..].to_vec(),
                    Vec::new(),
                    None,
                )
            };
            let mut transfers = transfers.to_vec();
            for (output_index, output) in body_outputs.iter().enumerate() {
                if transfers
                    .iter()
                    .any(|transfer| transfer.name == output.name)
                {
                    continue;
                }
                let parsed_type = crate::parse(&output.ty)?;
                let type_expression = parsed_type
                    .first()
                    .ok_or_else(|| "@async-fn mutable body output type is empty".to_owned())?;
                let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
                if !async_task_capture_is_copy(&ty) || async_task_capture_is_mutable_reference(&ty)
                {
                    transfers.push(LoopReferenceTransfer {
                        name: output.name.clone(),
                        ty: output.ty.clone(),
                        result_index: output_index + 1,
                        resumed_name: fresh_async_name(source, next_name),
                        owned: !async_task_capture_is_mutable_reference(&ty),
                    });
                }
            }
            if body_await.len() != 7 || has_await(&body_await[6]) || has_await(&await_form[5]) {
                return Err(
                    "@async-fn awaited while condition/body composition requires direct awaits with non-suspending child-task expressions".into(),
                );
            }
            let mut task_names = HashSet::new();
            collect_value_names(&body_await[6], &mut task_names);
            let captures = known_order
                .iter()
                .filter(|name| task_names.contains(*name))
                .filter_map(|name| known.get(name).cloned())
                .collect::<Vec<_>>();
            for capture in &captures {
                let parsed_type = crate::parse(&capture.ty)?;
                let type_expression = parsed_type
                    .first()
                    .ok_or_else(|| "@async-fn capture type is empty".to_owned())?;
                let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
                if !async_task_capture_is_copy(&ty)
                    && !async_task_capture_is_mutable_reference(&ty)
                    && !owned_captures.contains(&capture.name)
                    && !body_outputs
                        .iter()
                        .any(|output| output.name == capture.name)
                {
                    return Err(format!(
                        "@async-fn composed awaited while body captures non-Copy local '{}'; move its task inputs into an explicit child task",
                        capture.name
                    ));
                }
            }

            let base = fresh_async_name(source, next_name);
            let composite_task = format!("{base}-condition-body-task");
            let wait_condition = format!("{base}-wait-condition");
            let wait_body = format!("{base}-wait-body");
            let composite_result = format!("{base}-condition-body-poll-result");
            let composite_pending = format!("{base}-condition-body-pending");
            let composite_ready = format!("{base}-condition-body-ready");
            let composite_poll = format!("{base}-condition-body-poll");
            let decision_type = format!("{base}-condition-body-decision");
            let stop_variant = format!("{base}-stop");
            let continue_variant = format!("{base}-continue");
            let condition_child = expression_source(&await_form[1])?;
            let condition_pending = symbol(&await_form[2], "while condition Pending variant")?;
            let condition_ready = symbol(&await_form[3], "while condition Ready variant")?;
            let condition_poll = symbol(&await_form[4], "while condition poll function")?;
            let body_child = expression_source(&body_await[2])?;
            let body_pending = symbol(&body_await[3], "while body Pending variant")?;
            let body_ready = symbol(&body_await[4], "while body Ready variant")?;
            let body_poll = symbol(&body_await[5], "while body poll function")?;
            let body_task = expression_source(&body_await[6])?;
            let body_result_type = expression_source(&body_form[2])?;
            let capture_types = captures
                .iter()
                .map(|capture| capture.ty.as_str())
                .collect::<Vec<_>>();
            let capture_names = captures
                .iter()
                .map(|capture| capture.name.as_str())
                .collect::<Vec<_>>();
            let mut body_captures = Vec::new();
            for capture in &captures {
                let parsed_type = crate::parse(&capture.ty)?;
                let type_expression = parsed_type
                    .first()
                    .ok_or_else(|| "@async-fn capture type is empty".to_owned())?;
                let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
                if !async_task_capture_is_mutable_reference(&ty)
                    && !owned_captures.contains(&capture.name)
                    && !body_outputs
                        .iter()
                        .any(|output| output.name == capture.name)
                {
                    body_captures.push(capture.clone());
                }
            }
            let body_capture_types = body_captures
                .iter()
                .map(|capture| capture.ty.as_str())
                .collect::<Vec<_>>();
            let body_capture_names = body_captures
                .iter()
                .map(|capture| capture.name.as_str())
                .collect::<Vec<_>>();
            let condition_fields = std::iter::once(condition_child.as_str())
                .chain(capture_types.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let body_fields = std::iter::once(body_child.as_str())
                .chain(body_capture_types.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let condition_pattern = std::iter::once("child")
                .chain(capture_names.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let body_pattern = std::iter::once("child")
                .chain(body_capture_names.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let condition_pending_state = std::iter::once(format!("{wait_condition} pending"))
                .chain(capture_names.iter().map(|name| (*name).to_owned()))
                .collect::<Vec<_>>()
                .join(" ");
            let body_pending_state = std::iter::once(format!("{wait_body} pending"))
                .chain(body_capture_names.iter().map(|name| (*name).to_owned()))
                .collect::<Vec<_>>()
                .join(" ");
            let (body_data_type, body_data_type_source, body_value_bindings, body_data_values) =
                if transfers.is_empty() {
                    let body_data_type = body_return
                        .as_ref()
                        .map(|(_, _, _, payload_type)| payload_type.clone())
                        .unwrap_or_else(|| body_form[2].clone());
                    (
                        body_data_type.clone(),
                        expression_source(&body_data_type)?,
                        Vec::new(),
                        Vec::new(),
                    )
                } else {
                    if body_return.is_some() {
                        return Err(
                            "@async-fn returning multi-await loop bodies cannot transfer mutable captures yet"
                                .into(),
                        );
                    }
                    let body_result_type_expr = normalize_keywords(body_form[2].clone());
                    let Expr::List(body_type_items) = &body_result_type_expr else {
                        return Err(
                            format!(
                                "@async-fn reference transfer requires a tuple body result, got {body_result_type}"
                            ),
                        );
                    };
                    if !matches!(body_type_items.first(), Some(Expr::Symbol(head)) if head == "tuple")
                    {
                        return Err(
                            format!(
                                "@async-fn reference transfer requires a tuple body result, got {body_result_type}"
                            ),
                        );
                    }
                    let body_fields = &body_type_items[1..];
                    let mut transferred_indices = HashSet::new();
                    for transfer in &transfers {
                        if transfer.result_index >= body_fields.len()
                            || !transferred_indices.insert(transfer.result_index)
                        {
                            return Err(
                                "@async-fn reference transfer has an invalid tuple field".into()
                            );
                        }
                        let field_ty = parse_type(Some(&normalize_keywords(
                            body_fields[transfer.result_index].clone(),
                        )))?;
                        let transfer_type_expr =
                            normalize_keywords(crate::parse(&transfer.ty)?[0].expr.clone());
                        let transfer_ty = parse_type(Some(&transfer_type_expr))?;
                        if field_ty != transfer_ty {
                            return Err(format!(
                                "@async-fn reference transfer '{}' does not match its result field",
                                transfer.name
                            ));
                        }
                    }
                    let mut body_data_type_items = vec![Expr::Symbol("#tuple".into())];
                    let mut body_value_bindings = Vec::with_capacity(body_fields.len());
                    let mut body_data_values = Vec::new();
                    for (index, field_type) in body_fields.iter().enumerate() {
                        if let Some(transfer) = transfers
                            .iter()
                            .find(|transfer| transfer.result_index == index)
                        {
                            body_value_bindings.push(transfer.resumed_name.clone());
                        } else {
                            body_data_type_items.push(field_type.clone());
                            let field_name = fresh_async_name(source, next_name);
                            body_value_bindings.push(field_name.clone());
                            body_data_values.push(field_name);
                        }
                    }
                    let body_data_type = Expr::List(body_data_type_items);
                    let body_data_type_source = expression_source(&body_data_type)?;
                    (
                        body_data_type,
                        body_data_type_source,
                        body_value_bindings,
                        body_data_values,
                    )
                };
            let transfer_type_sources = transfers
                .iter()
                .map(|transfer| transfer.ty.as_str())
                .collect::<Vec<_>>();
            let ready_type_source = if transfers.is_empty() {
                decision_type.clone()
            } else {
                std::iter::once(format!("(#tuple {decision_type}"))
                    .chain(transfer_type_sources.iter().map(|ty| (*ty).to_owned()))
                    .collect::<Vec<_>>()
                    .join(" ")
                    + ")"
            };
            let stop_result = if transfers.is_empty() {
                stop_variant.clone()
            } else {
                format!(
                    "(#tuple {ready_type_source} {stop_variant} {})",
                    transfers
                        .iter()
                        .map(|transfer| transfer.name.as_str())
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            };
            let body_ready_conversion = if transfers.is_empty() {
                format!("({composite_ready} ({continue_variant} value))")
            } else {
                let pattern = format!("(#tuple {})", body_value_bindings.join(" "));
                let value_type = expression_source(&normalize_keywords(body_form[2].clone()))?;
                let body_data = if body_data_values.is_empty() {
                    "()".to_owned()
                } else {
                    format!(
                        "(#tuple {body_data_type_source} {})",
                        body_data_values.join(" ")
                    )
                };
                let transferred_values = transfers
                    .iter()
                    .map(|transfer| transfer.resumed_name.as_str())
                    .collect::<Vec<_>>()
                    .join(" ");
                format!(
                    "(#block (#let {pattern} {value_type} value) ({composite_ready} (#tuple {ready_type_source} ({continue_variant} {body_data}) {transferred_values})))"
                )
            };
            let composite_decision_definition = if transfers.is_empty() {
                format!("(#enum {decision_type} ({stop_variant} ({continue_variant} {body_result_type})))")
            } else {
                format!(
                    "(#enum {decision_type} ({stop_variant} ({continue_variant} {body_data_type_source})))"
                )
            };
            let composite_helper = if transfers.is_empty() {
                format!(
                "(#enum {decision_type} ({stop_variant} ({continue_variant} {body_result_type})))\n\
                 (#enum {composite_task} (({wait_condition} {condition_fields}) ({wait_body} {body_fields})))\n\
                 (#linear {composite_task})\n\
                 (#enum {composite_result} (({composite_pending} {composite_task}) ({composite_ready} {decision_type})))\n\
                 (#fn {composite_poll} ((task {composite_task}) (waker (#ref {waker}))) {composite_result}\n\
                   (#return (#match task\n\
                     (#case ({wait_condition} {condition_pattern})\n\
                       (#match (#call {condition_poll} (: task child : waker waker))\n\
                         (#case ({condition_pending} pending) ({composite_pending} ({condition_pending_state})))\n\
                         (#case ({condition_ready} condition)\n\
                           (#if condition\n\
                             (#match (#call {body_poll} (: task {body_task} : waker waker))\n\
                               (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                               (#case ({body_ready} value) ({composite_ready} ({continue_variant} value))))\n\
                             ({composite_ready} {stop_variant})))))\n\
                     (#case ({wait_body} {body_pattern})\n\
                       (#match (#call {body_poll} (: task child : waker waker))\n\
                         (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                         (#case ({body_ready} value) ({composite_ready} ({continue_variant} value))))))))"
                )
            } else {
                format!(
                    "{composite_decision_definition}\n\
                     (#enum {composite_task} (({wait_condition} {condition_fields}) ({wait_body} {body_fields})))\n\
                     (#linear {composite_task})\n\
                     (#enum {composite_result} (({composite_pending} {composite_task}) ({composite_ready} {ready_type_source})))\n\
                     (#fn {composite_poll} ((task {composite_task}) (waker (#ref {waker}))) {composite_result}\n\
                       (#return (#match task\n\
                         (#case ({wait_condition} {condition_pattern})\n\
                           (#match (#call {condition_poll} (: task child : waker waker))\n\
                             (#case ({condition_pending} pending) ({composite_pending} ({condition_pending_state})))\n\
                             (#case ({condition_ready} condition)\n\
                               (#if condition\n\
                                 (#match (#call {body_poll} (: task {body_task} : waker waker))\n\
                                   (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                                   (#case ({body_ready} value) {body_ready_conversion}))\n\
                                 ({composite_ready} {stop_result})))))\n\
                         (#case ({wait_body} {body_pattern})\n\
                           (#match (#call {body_poll} (: task child : waker waker))\n\
                             (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                             (#case ({body_ready} value) {body_ready_conversion}))))))"
                )
            };

            let decision_name = fresh_async_name(source, next_name);
            let stopped_name = fresh_async_name(source, next_name);
            let body_stopped_name = fresh_async_name(source, next_name);
            let payload_name = fresh_async_name(source, next_name);
            let body_success_payload = if body_return.is_some() {
                fresh_async_name(source, next_name)
            } else {
                payload_name.clone()
            };
            let body_local_outputs = body_outputs
                .iter()
                .filter(|output| {
                    !transfers
                        .iter()
                        .any(|transfer| transfer.owned && transfer.name == output.name)
                })
                .collect::<Vec<_>>();
            let mut body_success = vec![Expr::Symbol("#block".into())];
            if body_outputs.is_empty() {
                body_success.push(Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(body_binding.name.clone()),
                    body_data_type.clone(),
                    Expr::Symbol(body_success_payload.clone()),
                ]));
            } else {
                let status_name = fresh_async_name(source, next_name);
                let output_names = body_outputs
                    .iter()
                    .filter(|output| {
                        !transfers
                            .iter()
                            .any(|transfer| transfer.owned && transfer.name == output.name)
                    })
                    .map(|_| fresh_async_name(source, next_name))
                    .collect::<Vec<_>>();
                let pattern = Expr::List(
                    std::iter::once(Expr::Symbol("#tuple".into()))
                        .chain(std::iter::once(Expr::Symbol(status_name.clone())))
                        .chain(output_names.iter().cloned().map(Expr::Symbol))
                        .collect(),
                );
                body_success.push(Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    pattern,
                    body_data_type.clone(),
                    Expr::Symbol(body_success_payload.clone()),
                ]));
                body_success.push(Expr::List(vec![
                    Expr::Symbol("#let-mut".into()),
                    Expr::Symbol(body_stopped_name.clone()),
                    Expr::Symbol("bool".into()),
                    Expr::Symbol(status_name),
                ]));
                for (capture, value) in body_local_outputs.iter().zip(output_names) {
                    body_success.push(Expr::List(vec![
                        Expr::Symbol("#set".into()),
                        Expr::Symbol(capture.name.clone()),
                        Expr::Symbol(value),
                    ]));
                }
            }
            if body_outputs.is_empty() {
                body_success.push(Expr::List(vec![
                    Expr::Symbol("#let-mut".into()),
                    Expr::Symbol(body_stopped_name.clone()),
                    Expr::Symbol("bool".into()),
                    Expr::Symbol("false".into()),
                ]));
                body_success.extend(body_continuation);
                if use_body_child {
                    body_success.push(Expr::List(vec![
                        Expr::Symbol("#set".into()),
                        Expr::Symbol(body_stopped_name.clone()),
                        Expr::Symbol(body_binding.name),
                    ]));
                }
            }
            if body_success.len() > 3
                && contains_loop_control(body_success.last().expect("body has a stop local"))
            {
                rewrite_while_let_terminal(
                    body_success.last_mut().expect("body has a stop local"),
                    &body_stopped_name,
                )?;
            }
            body_success.push(Expr::Symbol(body_stopped_name));
            let body_success = if let Some((_, continue_variant, return_variant, _)) = &body_return
            {
                let returned_value = fresh_async_name(source, next_name);
                Expr::List(vec![
                    Expr::Symbol("#match".into()),
                    Expr::Symbol(payload_name.clone()),
                    Expr::List(vec![
                        Expr::Symbol("#case".into()),
                        Expr::List(vec![
                            Expr::Symbol(continue_variant.clone()),
                            Expr::Symbol(body_success_payload),
                        ]),
                        Expr::List(body_success),
                    ]),
                    Expr::List(vec![
                        Expr::Symbol("#case".into()),
                        Expr::List(vec![
                            Expr::Symbol(return_variant.clone()),
                            Expr::Symbol(returned_value.clone()),
                        ]),
                        Expr::List(vec![
                            Expr::Symbol("#block".into()),
                            Expr::List(vec![
                                Expr::Symbol("#return".into()),
                                Expr::Symbol(returned_value),
                            ]),
                        ]),
                    ]),
                ])
            } else {
                Expr::List(body_success)
            };
            let stopped_value = Expr::List(vec![
                Expr::Symbol("#match".into()),
                Expr::Symbol(decision_name.clone()),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::Symbol(stop_variant),
                    Expr::Symbol("true".into()),
                ]),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::List(vec![
                        Expr::Symbol(continue_variant),
                        Expr::Symbol(payload_name),
                    ]),
                    body_success,
                ]),
            ]);
            let mut condition_state = vec![Expr::Symbol(wait_condition), await_form[5].clone()];
            condition_state.extend(
                captures
                    .iter()
                    .map(|capture| Expr::Symbol(capture.name.clone())),
            );
            let await_expression = Expr::List(vec![
                Expr::Symbol("#await".into()),
                Expr::Symbol(composite_task),
                Expr::Symbol(composite_pending),
                Expr::Symbol(composite_ready),
                Expr::Symbol(composite_poll),
                Expr::List(condition_state),
            ]);
            let mut loop_form = vec![Expr::Symbol("#loop".into())];
            if transfers.is_empty() {
                loop_form.push(Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(decision_name),
                    Expr::Symbol(decision_type),
                    await_expression,
                ]));
            } else {
                let result_name = fresh_async_name(source, next_name);
                loop_form.push(Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(result_name.clone()),
                    Expr::Symbol(ready_type_source.clone()),
                    await_expression,
                ]));
                let mut pattern = vec![Expr::Symbol("#tuple".into()), Expr::Symbol(decision_name)];
                pattern.extend(
                    transfers
                        .iter()
                        .map(|transfer| Expr::Symbol(transfer.resumed_name.clone())),
                );
                loop_form.push(Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::List(pattern),
                    Expr::Symbol(ready_type_source.clone()),
                    Expr::Symbol(result_name),
                ]));
            }
            loop_form.extend([
                Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(stopped_name.clone()),
                    Expr::Symbol("bool".into()),
                    stopped_value,
                ]),
                Expr::List(vec![
                    Expr::Symbol("#if".into()),
                    Expr::Symbol(stopped_name),
                    Expr::List(vec![Expr::Symbol("#break".into())]),
                    Expr::List(vec![Expr::Symbol("#continue".into())]),
                ]),
            ]);
            let Some((replacement, loop_helper, renames)) = lower_async_loop_with_transfers(
                &Expr::List(loop_form),
                known,
                known_order,
                &transfers,
                following,
                return_value,
                return_type,
                source,
                next_name,
                waker,
            )?
            else {
                return Ok(None);
            };
            let helper = [condition_helper, body_helper, composite_helper, loop_helper]
                .into_iter()
                .filter(|helper| !helper.is_empty())
                .collect::<Vec<_>>()
                .join("\n");
            return Ok(Some((replacement, helper, renames)));
        }
        if body
            .iter()
            .any(|expression| matches!(form(expression, "#return"), Some(_)))
        {
            return Err("@async-fn awaited #while body cannot return yet".into());
        }

        let terminal = body
            .last()
            .filter(|expression| contains_loop_control(expression));
        let prefix = if terminal.is_some() {
            &body[..body.len() - 1]
        } else {
            body
        };
        if prefix.iter().any(contains_loop_control) {
            return Err("@async-fn awaited #while transfers must be terminal statements".into());
        }
        if let Some(terminal) = terminal {
            let mut probe = terminal.clone();
            if !rewrite_terminal_loop_control(&mut probe, "lim.async.done")? {
                return Err("@async-fn awaited #while has unsupported loop control".into());
            }
        }

        // Re-express an awaited condition as a loop whose first operation is
        // the suspension. The guarded body preserves while's rule that a
        // false condition skips the body; the final transfers are lowered to
        // explicit generated done state by lower_async_loop.
        let condition_name = fresh_async_name(source, next_name);
        let await_binding = Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(condition_name.clone()),
            Expr::Symbol("bool".into()),
            Expr::List(await_form),
        ]);
        let mut body_block = vec![Expr::Symbol("#block".into())];
        body_block.extend(prefix.iter().cloned());
        let guarded_body = Expr::List(vec![
            Expr::Symbol("#if".into()),
            Expr::Symbol(condition_name.clone()),
            Expr::List(body_block),
            Expr::List(Vec::new()),
        ]);
        let when_true = terminal
            .cloned()
            .unwrap_or_else(|| Expr::List(vec![Expr::Symbol("#continue".into())]));
        let loop_terminal = Expr::List(vec![
            Expr::Symbol("#if".into()),
            Expr::Symbol(condition_name),
            when_true,
            Expr::List(vec![Expr::Symbol("#break".into())]),
        ]);
        let mut loop_form = vec![Expr::Symbol("#loop".into()), await_binding];
        loop_form.push(guarded_body);
        loop_form.push(loop_terminal);
        let Some((replacement, helper, renames)) = lower_async_loop_with_transfers(
            &Expr::List(loop_form),
            known,
            known_order,
            transfers,
            following,
            return_value,
            return_type,
            source,
            next_name,
            waker,
        )?
        else {
            return Ok(None);
        };
        let helper = [condition_helper, helper]
            .into_iter()
            .filter(|helper| !helper.is_empty())
            .collect::<Vec<_>>()
            .join("\n");
        return Ok(Some((replacement, helper, renames)));
    }
    let body = &items[2..];
    let await_indices = body
        .iter()
        .enumerate()
        .filter_map(|(index, expression)| has_await(expression).then_some(index))
        .collect::<Vec<_>>();
    let body_awaits_are_direct_bindings = body.iter().filter(|expr| has_await(expr)).all(|expr| {
        let Some(binding) = form(expr, "#let").or_else(|| form(expr, "#let-mut")) else {
            return false;
        };
        let Some(await_form) = binding.get(3).and_then(|value| form(value, "#await")) else {
            return false;
        };
        await_form.len() == 6 && !has_await(&await_form[5])
    });
    if body.iter().map(await_count).sum::<usize>() > 2 || !body_awaits_are_direct_bindings {
        let (body_binding, mut body_form, body_helper, body_outputs, body_return) =
            async_while_body_child(
                body,
                known,
                known_order,
                source,
                next_name,
                waker,
                false,
                None,
                return_type,
            )?;
        let binding_type = parse_type(Some(&normalize_keywords(body_form[2].clone())))?;
        let Expr::List(await_form) = &mut body_form[3] else {
            unreachable!("generated body await initializer is a list")
        };
        if await_form.len() == 7 {
            let await_type = parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
            if binding_type != await_type {
                return Err(
                    "@async-fn generated loop body task result type does not match its binding"
                        .into(),
                );
            }
            await_form.remove(1);
        }

        let loop_done = fresh_async_name(source, next_name);
        let loop_condition = Expr::List(vec![
            Expr::Symbol("#bool.&&".into()),
            Expr::List(vec![
                Expr::Symbol("#bool.==".into()),
                Expr::Symbol(loop_done.clone()),
                Expr::Symbol("false".into()),
            ]),
            items[1].clone(),
        ]);
        let mut rewritten = vec![Expr::Symbol("#while".into()), loop_condition];
        rewritten.push(Expr::List(body_form));
        let mut body_value = Expr::Symbol(body_binding.name.clone());
        if let Some((_, continued, returned, payload_type)) = body_return {
            let payload_name = fresh_async_name(source, next_name);
            let result_name = fresh_async_name(source, next_name);
            let data_name = fresh_async_name(source, next_name);
            rewritten.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(data_name.clone()),
                payload_type,
                Expr::List(vec![
                    Expr::Symbol("#match".into()),
                    body_value,
                    Expr::List(vec![
                        Expr::Symbol("#case".into()),
                        Expr::List(vec![
                            Expr::Symbol(continued),
                            Expr::Symbol(payload_name.clone()),
                        ]),
                        Expr::Symbol(payload_name),
                    ]),
                    Expr::List(vec![
                        Expr::Symbol("#case".into()),
                        Expr::List(vec![
                            Expr::Symbol(returned),
                            Expr::Symbol(result_name.clone()),
                        ]),
                        Expr::List(vec![
                            Expr::Symbol("#block".into()),
                            Expr::List(vec![
                                Expr::Symbol("#return".into()),
                                Expr::Symbol(result_name),
                            ]),
                        ]),
                    ]),
                ]),
            ]));
            body_value = Expr::Symbol(data_name);
        }
        let mut child_transfers = transfers.to_vec();
        let stopped = if body_outputs.is_empty() {
            body_value
        } else {
            let stopped_name = fresh_async_name(source, next_name);
            let mut pattern = vec![
                Expr::Symbol("#tuple".into()),
                Expr::Symbol(stopped_name.clone()),
            ];
            let mut fields = vec![Expr::Symbol("bool".into())];
            let mut output_names = Vec::with_capacity(body_outputs.len());
            for (index, capture) in body_outputs.iter().enumerate() {
                let output_name = fresh_async_name(source, next_name);
                output_names.push(output_name.clone());
                pattern.push(Expr::Symbol(output_name.clone()));
                fields.push(crate::parse(&capture.ty)?[0].expr.clone());
                let ty = parse_type(Some(&normalize_keywords(
                    crate::parse(&capture.ty)?[0].expr.clone(),
                )))?;
                if async_task_capture_is_mutable_reference(&ty)
                    && !child_transfers
                        .iter()
                        .any(|transfer| transfer.name == capture.name)
                {
                    child_transfers.push(LoopReferenceTransfer {
                        name: capture.name.clone(),
                        ty: capture.ty.clone(),
                        result_index: index + 1,
                        resumed_name: output_name,
                        owned: false,
                    });
                }
            }
            rewritten.push(Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::List(pattern),
                Expr::List(
                    std::iter::once(Expr::Symbol("#tuple".into()))
                        .chain(fields)
                        .collect(),
                ),
                body_value,
            ]));
            for (capture, output_name) in body_outputs.iter().zip(output_names) {
                if child_transfers
                    .iter()
                    .any(|transfer| transfer.name == capture.name)
                {
                    continue;
                }
                rewritten.push(Expr::List(vec![
                    Expr::Symbol("#set".into()),
                    Expr::Symbol(capture.name.clone()),
                    Expr::Symbol(output_name),
                ]));
            }
            Expr::Symbol(stopped_name)
        };
        rewritten.push(Expr::List(vec![
            Expr::Symbol("#set".into()),
            Expr::Symbol(loop_done.clone()),
            stopped,
        ]));
        let mut child_known = known.clone();
        child_known.insert(
            loop_done.clone(),
            Binding {
                name: loop_done.clone(),
                ty: "bool".into(),
                mutable: true,
            },
        );
        let mut child_order = known_order.to_vec();
        child_order.push(loop_done.clone());
        let Some((mut replacement, loop_helper, renames)) = lower_async_while_with_transfers(
            &Expr::List(rewritten),
            &child_known,
            &child_order,
            &child_transfers,
            &[],
            following,
            return_value,
            return_type,
            source,
            next_name,
            waker,
        )?
        else {
            return Err("@async-fn failed to lower multi-await loop body".into());
        };
        replacement.insert(
            0,
            Expr::List(vec![
                Expr::Symbol("#let-mut".into()),
                Expr::Symbol(loop_done),
                Expr::Symbol("bool".into()),
                Expr::Symbol("false".into()),
            ]),
        );
        let helper = [body_helper, loop_helper]
            .into_iter()
            .filter(|helper| !helper.is_empty())
            .collect::<Vec<_>>()
            .join("\n");
        return Ok(Some((replacement, helper, renames)));
    }
    if await_indices.len() != 1 {
        if await_indices.len() >= 2 {
            let first_index = await_indices[0];
            let second_index = await_indices[1];
            let first_binding = binding(&body[first_index], "first loop await")?;
            let second_binding = binding(&body[second_index], "second loop await")?;
            let first_form = form(&body[first_index], "#let")
                .or_else(|| form(&body[first_index], "#let-mut"))
                .ok_or_else(|| "@async-fn first loop await must be a direct binding".to_owned())?;
            let second_form = form(&body[second_index], "#let")
                .or_else(|| form(&body[second_index], "#let-mut"))
                .ok_or_else(|| "@async-fn second loop await must be a direct binding".to_owned())?;
            let first_await = form(&first_form[3], "#await").ok_or_else(|| {
                "@async-fn first loop binding must be initialized directly by #await".to_owned()
            })?;
            let second_await = form(&second_form[3], "#await").ok_or_else(|| {
                "@async-fn second loop binding must be initialized directly by #await".to_owned()
            })?;
            if first_await.len() != 6
                || second_await.len() != 6
                || has_await(&first_await[5])
                || has_await(&second_await[5])
            {
                return Err(
                    "@async-fn sequenced loop awaits require direct bindings and non-suspending task expressions".into(),
                );
            }
            let middle = &body[first_index + 1..second_index];
            for expression in middle {
                if has_await(expression)
                    || contains_loop_control(expression)
                    || is_control_flow_statement(expression)
                    || form(expression, "#let").is_some()
                    || form(expression, "#let-mut").is_some()
                    || form(expression, "#set").is_some()
                    || form(expression, "#return").is_some()
                {
                    return Err(
                        "@async-fn statements between loop awaits must be nonbinding, noncontrol, and nonsuspending expressions".into(),
                    );
                }
            }
            let mut second_task_names = HashSet::new();
            collect_value_names(&second_await[5], &mut second_task_names);
            if let Some(name) = second_task_names
                .iter()
                .find(|name| **name != first_binding.name && known.contains_key(*name))
            {
                return Err(format!(
                    "@async-fn second loop task uses outer local '{name}'; carry it in the first child result"
                ));
            }
            let mut middle_names = HashSet::new();
            for expression in middle {
                collect_value_names(expression, &mut middle_names);
            }
            if let Some(name) = middle_names
                .iter()
                .find(|name| **name != first_binding.name && known.contains_key(*name))
            {
                return Err(format!(
                    "@async-fn statement between loop awaits uses outer local '{name}'; carry it in the first child result"
                ));
            }
            let prefix_bindings = body[..first_index]
                .iter()
                .filter(|expression| {
                    form(expression, "#let").is_some() || form(expression, "#let-mut").is_some()
                })
                .map(|expression| binding(expression, "loop-await prefix"))
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(binding) = prefix_bindings
                .iter()
                .find(|binding| second_task_names.contains(&binding.name))
            {
                return Err(format!(
                    "@async-fn second loop task uses per-iteration local '{}'; carry it in the first child result",
                    binding.name
                ));
            }
            if let Some(binding) = prefix_bindings
                .iter()
                .find(|binding| middle_names.contains(&binding.name))
            {
                return Err(format!(
                    "@async-fn statement between loop awaits uses per-iteration local '{}'; carry it in the first child result",
                    binding.name
                ));
            }
            let mut suffix_names = HashSet::new();
            for expression in &body[second_index + 1..] {
                collect_value_names(expression, &mut suffix_names);
            }
            let preserve_first_result = suffix_names.contains(&first_binding.name);

            let base = fresh_async_name(source, next_name);
            let sequence_task = format!("{base}-sequence-task");
            let wait_first = format!("{base}-wait-first");
            let wait_second = format!("{base}-wait-second");
            let sequence_poll = format!("{base}-sequence-poll");
            let sequence_result = format!("{base}-sequence-result");
            let sequence_pending = format!("{base}-sequence-pending");
            let sequence_ready = format!("{base}-sequence-ready");
            let first_child_type = expression_source(&first_await[1])?;
            let second_child_type = expression_source(&second_await[1])?;
            let first_pending = symbol(&first_await[2], "first loop child Pending variant")?;
            let first_ready = symbol(&first_await[3], "first loop child Ready variant")?;
            let first_poll = symbol(&first_await[4], "first loop child poll function")?;
            let second_pending = symbol(&second_await[2], "second loop child Pending variant")?;
            let second_ready = symbol(&second_await[3], "second loop child Ready variant")?;
            let second_poll = symbol(&second_await[4], "second loop child poll function")?;
            let mut second_task = second_await[5].clone();
            let first_result = format!("{base}-first-result");
            let second_resume_first = format!("{base}-resume-first");
            replace_await_local(&mut second_task, &first_binding.name, &first_result);
            let second_task = expression_source(&second_task)?;
            let mut middle = middle.to_vec();
            for expression in &mut middle {
                replace_await_local(expression, &first_binding.name, &first_result);
            }
            let middle_source = middle
                .iter()
                .map(expression_source)
                .collect::<Result<Vec<_>, _>>()?
                .join(" ");
            let second_result_type = second_binding.ty.as_str();
            let sequence_ready_type = if preserve_first_result {
                format!("(#tuple {} {second_result_type})", first_binding.ty)
            } else {
                second_result_type.to_owned()
            };
            let wait_second_fields = if preserve_first_result {
                format!("{} {second_child_type}", first_binding.ty)
            } else {
                second_child_type.clone()
            };
            let pending_after_first = if preserve_first_result {
                format!("({sequence_pending} ({wait_second} {first_result} pending))")
            } else {
                format!("({sequence_pending} ({wait_second} pending))")
            };
            let ready_after_first = if preserve_first_result {
                format!("({sequence_ready} (#tuple {first_result} value))")
            } else {
                format!("({sequence_ready} value)")
            };
            let second_poll_from_first = format!(
                "(#match (#call {second_poll} (: task {second_task} : waker waker))\n\
                   (#case ({second_pending} pending) {pending_after_first})\n\
                   (#case ({second_ready} value) {ready_after_first}))"
            );
            let pending_again = if preserve_first_result {
                format!("({sequence_pending} ({wait_second} {second_resume_first} pending))")
            } else {
                format!("({sequence_pending} ({wait_second} pending))")
            };
            let ready_again = if preserve_first_result {
                format!("({sequence_ready} (#tuple {second_resume_first} value))")
            } else {
                format!("({sequence_ready} value)")
            };
            let wait_second_pattern = if preserve_first_result {
                format!("({wait_second} {second_resume_first} child)")
            } else {
                format!("({wait_second} child)")
            };
            let second_poll_again = format!(
                "(#match (#call {second_poll} (: task child : waker waker))\n\
                   (#case ({second_pending} pending) {pending_again})\n\
                   (#case ({second_ready} value) {ready_again}))"
            );
            let uses_first_result = second_task_names.contains(&first_binding.name)
                || middle_names.contains(&first_binding.name)
                || preserve_first_result;
            let first_ready_continuation = if uses_first_result {
                format!("(#block {middle_source} {second_poll_from_first})")
            } else {
                format!(
                    "(#block (#forget {first_result}) {middle_source} {second_poll_from_first})"
                )
            };
            let sequence_helper = format!(
                "(#enum {sequence_task} (({wait_first} {first_child_type}) ({wait_second} {wait_second_fields})))\n\
                 (#linear {sequence_task})\n\
                 (#enum {sequence_result} (({sequence_pending} {sequence_task}) ({sequence_ready} {sequence_ready_type})))\n\
                 (#fn {sequence_poll} ((task {sequence_task}) (waker (#ref {waker}))) {sequence_result}\n\
                   (#return (#match task\n\
                     (#case ({wait_first} child)\n\
                       (#match (#call {first_poll} (: task child : waker waker))\n\
                         (#case ({first_pending} pending) ({sequence_pending} ({wait_first} pending)))\n\
                         (#case ({first_ready} {first_result}) {first_ready_continuation})))\n\
                     (#case {wait_second_pattern} {second_poll_again}))))"
            );

            let mut rewritten = statement.clone();
            let Expr::List(loop_items) = &mut rewritten else {
                unreachable!()
            };
            let first_global_index = first_index + 2;
            let second_global_index = second_index + 2;
            loop_items.drain(first_global_index..second_global_index);
            let second_await_value = Expr::List(vec![
                Expr::Symbol("#await".into()),
                Expr::Symbol(sequence_task),
                Expr::Symbol(sequence_pending),
                Expr::Symbol(sequence_ready),
                Expr::Symbol(sequence_poll),
                Expr::List(vec![Expr::Symbol(wait_first), first_await[5].clone()]),
            ]);
            if preserve_first_result {
                let tuple_name = fresh_async_name(source, next_name);
                let tuple_type = Expr::List(vec![
                    Expr::Symbol("#tuple".into()),
                    crate::parse(&first_binding.ty)?[0].expr.clone(),
                    crate::parse(&second_binding.ty)?[0].expr.clone(),
                ]);
                loop_items[first_global_index] = Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(tuple_name.clone()),
                    tuple_type.clone(),
                    second_await_value,
                ]);
                for (field_index, local) in
                    [&first_binding, &second_binding].into_iter().enumerate()
                {
                    loop_items.insert(
                        first_global_index + 1 + field_index,
                        Expr::List(vec![
                            Expr::Symbol("#let".into()),
                            Expr::Symbol(local.name.clone()),
                            crate::parse(&local.ty)?[0].expr.clone(),
                            Expr::List(vec![
                                Expr::Symbol("#get".into()),
                                Expr::Symbol(tuple_name.clone()),
                                Expr::UnsignedInteger(field_index as u128),
                            ]),
                        ]),
                    );
                }
            } else {
                let Expr::List(second_binding_form) = &mut loop_items[first_global_index] else {
                    unreachable!()
                };
                second_binding_form[3] = second_await_value;
            }
            let Some((replacement, helper, renames)) = lower_async_while_with_transfers(
                &rewritten,
                known,
                known_order,
                transfers,
                &[],
                following,
                return_value,
                return_type,
                source,
                next_name,
                waker,
            )?
            else {
                return Ok(None);
            };
            let helper = [sequence_helper, helper]
                .into_iter()
                .filter(|helper| !helper.is_empty())
                .collect::<Vec<_>>()
                .join("\n");
            return Ok(Some((replacement, helper, renames)));
        }
        return Err(
            "@async-fn loop lowering currently requires exactly one await binding per iteration"
                .into(),
        );
    }
    let await_index = await_indices[0];
    let await_binding = binding(&body[await_index], "loop await")?;
    let binding_form = form(&body[await_index], "#let")
        .or_else(|| form(&body[await_index], "#let-mut"))
        .ok_or_else(|| "@async-fn loop await must be a direct binding".to_owned())?;
    let (await_form, branch_helper) = if let Some(await_form) = form(&binding_form[3], "#await") {
        (await_form.to_vec(), String::new())
    } else if let Some((protocol, task, helper)) =
        conditional_await_with_immediate(&binding_form[3], known, source, next_name, waker)?
    {
        (
            vec![
                Expr::Symbol("#await".into()),
                protocol.child_type,
                protocol.pending,
                protocol.ready,
                protocol.poll,
                task,
            ],
            helper,
        )
    } else {
        return Err(
            "@async-fn loop binding requires a direct #await or conditional #if/#match with a direct #await branch".into(),
        );
    };
    if await_form.len() != 6 || has_await(&await_form[5]) {
        return Err("@async-fn loop #await requires one non-suspending child task".into());
    }
    let prefix = &body[..await_index];
    if prefix.iter().any(|expression| {
        has_await(expression)
            || matches!(
                expression,
                Expr::List(parts)
                    if matches!(parts.first(), Some(Expr::Symbol(head))
                        if matches!(head.as_str(), "#let-else" | "#return" | "#break" | "#continue"))
            )
    }) {
        return Err("@async-fn loop-await prefix cannot suspend or transfer control".into());
    }
    let suffix = &body[await_index + 1..];
    let terminal_loop_transfer = suffix.last().and_then(|expression| {
        let Expr::List(items) = expression else {
            return None;
        };
        if items.len() != 1 {
            return None;
        }
        match items.first() {
            Some(Expr::Symbol(name)) if matches!(name.as_str(), "#break" | "#continue") => {
                Some(name.as_str())
            }
            _ => None,
        }
    });
    let suffix_body = if terminal_loop_transfer.is_some() {
        &suffix[..suffix.len() - 1]
    } else {
        suffix
    };
    if suffix_body.iter().any(|expression| {
        has_await(expression)
            || matches!(
                expression,
                Expr::List(parts)
                    if matches!(parts.first(), Some(Expr::Symbol(head))
                        if matches!(head.as_str(), "#return" | "#break" | "#continue"))
            )
    }) {
        return Err("@async-fn loop-await suffix cannot suspend or transfer control".into());
    }

    let mut prefix_bindings = HashSet::new();
    for expression in prefix {
        if form(expression, "#let").is_some() || form(expression, "#let-mut").is_some() {
            let local = binding(expression, "loop-await prefix")?;
            if known.contains_key(&local.name) {
                return Err(format!(
                    "@async-fn loop-await prefix binding '{}' shadows an existing name",
                    local.name
                ));
            }
            prefix_bindings.insert(local.name);
        }
    }
    let mut suffix_names = HashSet::new();
    for expression in suffix_body {
        collect_value_names(expression, &mut suffix_names);
    }
    if let Some(name) = prefix_bindings
        .iter()
        .find(|name| suffix_names.contains(name.as_str()))
    {
        return Err(format!(
            "@async-fn loop-await local '{}' is not available after suspension; move it into the child task or a captured value",
            name
        ));
    }

    let mut used_names = HashSet::new();
    collect_value_names(&condition, &mut used_names);
    collect_value_names(&await_form[5], &mut used_names);
    for expression in prefix.iter().chain(suffix_body) {
        collect_value_names(expression, &mut used_names);
    }
    let captures = known_order
        .iter()
        .filter(|name| used_names.contains(name.as_str()))
        .filter_map(|name| known.get(name).cloned())
        .collect::<Vec<_>>();
    let mut transfer_bindings = HashMap::new();
    for transfer in transfers {
        let capture = captures
            .iter()
            .find(|capture| capture.name == transfer.name)
            .ok_or_else(|| {
                format!(
                    "@async-fn transferred reference '{}' is not a live loop capture",
                    transfer.name
                )
            })?;
        if capture.ty != transfer.ty || transfer_bindings.contains_key(&transfer.name) {
            return Err(format!(
                "@async-fn has an invalid transfer descriptor for '{}'",
                transfer.name
            ));
        }
        let parsed_type = crate::parse(&capture.ty)?;
        let type_expression = parsed_type
            .first()
            .ok_or_else(|| "@async-fn reference transfer type is empty".to_owned())?;
        let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
        if !transfer.owned && !async_task_capture_is_mutable_reference(&ty) {
            return Err(format!(
                "@async-fn transfer '{}' is not a mutable reference",
                transfer.name
            ));
        }
        if transfer.owned && async_task_capture_is_copy(&ty) {
            return Err(format!(
                "@async-fn owned transfer '{}' must have a linear type",
                transfer.name
            ));
        }
        transfer_bindings.insert(transfer.name.clone(), transfer);
    }
    let wait_captures = captures
        .iter()
        .filter(|capture| !transfer_bindings.contains_key(&capture.name))
        .cloned()
        .collect::<Vec<_>>();

    let mut used_after = HashSet::new();
    for expression in following {
        collect_value_names(expression, &mut used_after);
    }
    collect_value_names(return_value, &mut used_after);
    let output_captures = captures
        .iter()
        .filter(|binding| used_after.contains(&binding.name))
        .cloned()
        .collect::<Vec<_>>();

    let base = fresh_async_name(source, next_name);
    let task_type = format!("{base}-task");
    let task_start = format!("{base}-start");
    let task_wait = format!("{base}-wait");
    let task_poll_result = format!("{base}-poll-result");
    let output_type = format!("{base}-outputs");
    let (mut output_type_source, mut ready_type, mut ready_value) = if output_captures.is_empty() {
        (String::new(), "()".to_owned(), "()".to_owned())
    } else {
        let fields = output_captures
            .iter()
            .map(|binding| format!("({} {})", binding.name, binding.ty))
            .collect::<Vec<_>>()
            .join(" ");
        let values = output_captures
            .iter()
            .map(|binding| format!("({} {})", binding.name, binding.name))
            .collect::<Vec<_>>()
            .join(" ");
        let declarations = format!("(#struct {output_type} ({fields}))");
        let value = format!("(#struct-literal {output_type} ({values}))");
        (declarations, output_type.clone(), value)
    };
    let task_pending = format!("{base}-pending");
    let task_ready = format!("{base}-ready");
    let loop_return = if suffix_body.iter().any(contains_return) {
        let enclosing_type = return_type
            .ok_or_else(|| "@async-fn loop return requires its enclosing result type".to_owned())?;
        let outcome = format!("{base}-exit");
        let completed = format!("{base}-completed");
        let returned = format!("{base}-returned");
        output_type_source.push_str(&format!(
            "\n(#enum {outcome} (({completed} {ready_type}) ({returned} {})))",
            expression_source(enclosing_type)?
        ));
        ready_value = format!("({completed} {ready_value})");
        ready_type = outcome.clone();
        Some((outcome, completed, returned, enclosing_type.clone()))
    } else {
        None
    };
    let task_run = format!("{base}-run");
    let task_iteration = format!("{base}-iteration");
    let task_resume = format!("{base}-resume");
    let task_poll = format!("{base}-poll");
    let child_type = expression_source(&await_form[1])?;
    let child_pending = symbol(&await_form[2], "loop child Pending variant")?;
    let child_ready = symbol(&await_form[3], "loop child Ready variant")?;
    let child_poll = symbol(&await_form[4], "loop child poll function")?;
    let child_task = expression_source(&await_form[5])?;
    parse_type(Some(&normalize_keywords(await_form[1].clone())))?;

    let capture_types = types(&captures);
    let capture_names = arguments(&captures);
    let wait_capture_types = types(&wait_captures);
    let wait_capture_names = arguments(&wait_captures);
    let active_pattern_names = captures
        .iter()
        .enumerate()
        .map(|(index, binding)| {
            let ty = parse_type(Some(&normalize_keywords(
                crate::parse(&binding.ty)?[0].expr.clone(),
            )))?;
            Ok(if async_task_capture_is_mutable_reference(&ty) {
                binding.name.clone()
            } else {
                format!("{base}-active-{index}")
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let active_local_bindings = captures
        .iter()
        .zip(&active_pattern_names)
        .filter(|(binding, name)| binding.name != **name)
        .map(|(binding, name)| {
            format!(
                "({} {} {} {name})",
                if binding.mutable { "#let-mut" } else { "#let" },
                binding.name,
                binding.ty
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let start_variant = if capture_types.is_empty() {
        task_start.clone()
    } else {
        format!("({task_start} {capture_types})")
    };
    let wait_fields = if wait_capture_types.is_empty() {
        child_type.clone()
    } else {
        format!("{wait_capture_types} {child_type}")
    };
    let wait_variant = format!("({task_wait} {wait_fields})");
    let start_pattern = if capture_names.is_empty() {
        task_start.clone()
    } else {
        format!("({task_start} {capture_names})")
    };
    let wait_pattern = if wait_capture_names.is_empty() {
        format!("({task_wait} {base}-child)")
    } else {
        format!("({task_wait} {wait_capture_names} {base}-child)")
    };
    let task_wait_with_child = if wait_capture_names.is_empty() {
        format!("({task_wait} {base}-child-state)")
    } else {
        format!("({task_wait} {wait_capture_names} {base}-child-state)")
    };
    // Transfer one owned aggregate into the runner. Keeping separate raw
    // reference parameters alive while cycling the same handles through a
    // local enum would leave an additional parent loan in scope.
    let run_state = format!("{base}-run-state");
    let run_parameters = format!("({base}-input-state {run_state}) (waker (#ref {waker}))");
    let mut resume_parameters = wait_captures.iter().map(parameter).collect::<Vec<_>>();
    let result_parameter = if await_binding.mutable {
        format!("(#mut {base}-result {})", await_binding.ty)
    } else {
        format!("({base}-result {})", await_binding.ty)
    };
    resume_parameters.push(result_parameter);
    resume_parameters.push(format!("(waker (#ref {waker}))"));
    let resume_parameters = resume_parameters.join(" ");
    let call_run = format!("(: {base}-input-state ({base}-active {capture_names}) : waker waker)");
    let resumed_capture_names = captures
        .iter()
        .map(|binding| {
            transfer_bindings
                .get(&binding.name)
                .map_or(binding.name.as_str(), |transfer| {
                    transfer.resumed_name.as_str()
                })
        })
        .collect::<Vec<_>>()
        .join(" ");
    let call_resumed_run =
        format!("(: {base}-input-state ({base}-active {resumed_capture_names}) : waker waker)");
    let active_variant = if capture_types.is_empty() {
        format!("{base}-active")
    } else {
        format!("({base}-active {capture_types})")
    };
    let active_pattern = if capture_names.is_empty() {
        format!("{base}-active")
    } else {
        format!("({base}-active {})", active_pattern_names.join(" "))
    };
    let active_value = format!("{base}-input-state");
    let active_value_from_captures = if capture_names.is_empty() {
        format!("{base}-active")
    } else {
        format!(
            "({base}-active {})",
            captures
                .iter()
                .map(|capture| transfer_bindings
                    .get(&capture.name)
                    .map_or(capture.name.as_str(), |transfer| transfer
                        .resumed_name
                        .as_str()))
                .collect::<Vec<_>>()
                .join(" ")
        )
    };
    let run_state_pending = format!("{base}-run-pending");
    let run_state_ready = format!("{base}-run-ready");
    let run_state_pending_pattern = format!("({run_state_pending} {base}-pending-task)");
    let run_state_ready_pattern = format!("({run_state_ready} {base}-ready-value)");
    let call_resume = {
        let mut arguments = named_arguments(&wait_captures);
        if !arguments.is_empty() {
            arguments.push(' ');
        }
        arguments.push_str(&format!(": {base}-result {base}-result : waker waker"));
        format!("({arguments})")
    };
    let loop_condition = expression_source(&condition)?;
    let prefix_source = prefix
        .iter()
        .map(expression_source)
        .collect::<Result<Vec<_>, _>>()?
        .join(" ");
    let mut iteration_suffix_body = suffix_body.to_vec();
    let mut suffix_body = suffix_body.to_vec();
    if let Some((_, _, returned, _)) = &loop_return {
        for expression in &mut suffix_body {
            rewrite_async_child_returns(expression, returned)?;
            rewrite_async_non_loop_returns(expression, &task_ready)?;
        }
        for expression in &mut iteration_suffix_body {
            rewrite_async_child_returns(expression, returned)?;
            rewrite_async_non_loop_returns(expression, &run_state_ready)?;
        }
    }
    let iteration_suffix_source = iteration_suffix_body
        .iter()
        .map(expression_source)
        .collect::<Result<Vec<_>, _>>()?
        .join(" ");
    let suffix_source = suffix_body
        .iter()
        .map(expression_source)
        .collect::<Result<Vec<_>, _>>()?
        .join(" ");
    let mut resumed_ready = crate::parse(&ready_value)?[0].expr.clone();
    for transfer in transfers {
        rename_async_value(&mut resumed_ready, &transfer.name, &transfer.resumed_name);
    }
    let resumed_ready_value = expression_source(&resumed_ready)?;
    let loop_ready_continuation = if terminal_loop_transfer == Some("#break") {
        format!("({run_state_ready} {resumed_ready_value})")
    } else {
        active_value_from_captures.clone()
    };
    let resumed_loop_return = if terminal_loop_transfer == Some("#break") {
        format!("(#return ({task_ready} {resumed_ready_value}))")
    } else {
        format!("(#return (#call {task_run} {call_resumed_run}))")
    };
    let child_poll_call = format!("(#call {child_poll} (: task {base}-child : waker waker))");
    let await_let = if await_binding.mutable {
        "#let-mut"
    } else {
        "#let"
    };
    let await_name = &await_binding.name;
    let await_type = &await_binding.ty;
    let task_source = format!(
        "{output_type_source}
         (#enum {task_type} ({start_variant} {wait_variant}))
         (#linear {task_type})
         (#enum {run_state} ({active_variant} ({run_state_pending} {task_type}) ({run_state_ready} {ready_type})))
         (#enum {task_poll_result} (({task_pending} {task_type}) ({task_ready} {ready_type})))
         (#fn {task_run} ({run_parameters}) {task_poll_result}
         (#let-mut {base}-outcome {run_state} {active_value})
         (#let-mut {base}-stopped bool false)
         (#while (#bool.== {base}-stopped false)
             (#set {base}-outcome
               (#match {base}-outcome
                 (#case {active_pattern}
                   (#call {task_iteration} (: {base}-iteration-state ({base}-active {}) : waker waker)))
                 (#case {run_state_pending_pattern} (#unreachable))
                 (#case {run_state_ready_pattern} (#unreachable))))
             (#set {base}-outcome
               (#match {base}-outcome
                 (#case {active_pattern} ({base}-active {}))
                 (#case {run_state_pending_pattern}
                   (#block (#set {base}-stopped true) ({run_state_pending} {base}-pending-task)))
                 (#case {run_state_ready_pattern}
                   (#block (#set {base}-stopped true) ({run_state_ready} {base}-ready-value))))))
           (#return (#match {base}-outcome
             (#case {run_state_pending_pattern} ({task_pending} {base}-pending-task))
             (#case {run_state_ready_pattern} ({task_ready} {base}-ready-value))
             (#case {active_pattern} (#unreachable)))))
         (#fn {task_iteration} (({base}-iteration-state {run_state}) (waker (#ref {waker}))) {run_state}
           (#return (#match {base}-iteration-state
                 (#case {active_pattern}
                   (#block
                     {active_local_bindings}
                     (#if {loop_condition}
                       (#block
                         {prefix_source}
                         (#let {base}-child {child_type} {child_task})
                         (#match {child_poll_call}
                           (#case ({child_pending} {base}-child-state)
                             ({run_state_pending} {task_wait_with_child}))
                           (#case ({child_ready} {base}-result)
                             (#block
                               ({await_let} {await_name} {await_type} {base}-result)
                               {iteration_suffix_source}
                               {loop_ready_continuation}))))
                       ({run_state_ready} {ready_value}))))
                 (#case {run_state_pending_pattern} (#unreachable))
                 (#case {run_state_ready_pattern} (#unreachable)))))
         (#fn {task_resume} ({resume_parameters}) {task_poll_result}
           ({await_let} {await_name} {await_type} {base}-result)
           {suffix_source}
           {resumed_loop_return})
         (#fn {task_poll} ((task {task_type}) (waker (#ref {waker}))) {task_poll_result}
           (#return (#match task
             (#case {start_pattern} (#call {task_run} {call_run}))
             (#case {wait_pattern}
               (#match {child_poll_call}
                 (#case ({child_pending} {base}-child-state)
                   ({task_pending} {task_wait_with_child}))
                 (#case ({child_ready} {base}-result)
                   (#call {task_resume} {call_resume})))))))",
        active_pattern_names.join(" "),
        active_pattern_names.join(" "),
    );
    let task_variable = format!("{base}-value");
    let result_variable = format!("{base}-result");
    let replacement = vec![
        Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(task_variable.clone()),
            Expr::Symbol(task_type.clone()),
            Expr::List(
                std::iter::once(Expr::Symbol(task_start))
                    .chain(
                        captures
                            .iter()
                            .map(|binding| Expr::Symbol(binding.name.clone())),
                    )
                    .collect(),
            ),
        ]),
        Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(result_variable.clone()),
            if loop_return.is_some() {
                Expr::Symbol(ready_type.clone())
            } else if output_captures.is_empty() {
                Expr::List(Vec::new())
            } else {
                Expr::Symbol(output_type.clone())
            },
            Expr::List(vec![
                Expr::Symbol("#await".into()),
                Expr::Symbol(task_type),
                Expr::Symbol(task_pending),
                Expr::Symbol(task_ready),
                Expr::Symbol(task_poll),
                Expr::Symbol(task_variable),
            ]),
        ]),
    ];
    let mut replacement = replacement;
    let result_variable = if let Some((_, completed, returned, enclosing_type)) = &loop_return {
        let value = fresh_async_name(source, next_name);
        let returned_value = fresh_async_name(source, next_name);
        let output = fresh_async_name(source, next_name);
        replacement.push(Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol(output.clone()),
            if output_captures.is_empty() {
                Expr::List(Vec::new())
            } else {
                Expr::Symbol(output_type.clone())
            },
            Expr::List(vec![
                Expr::Symbol("#match".into()),
                Expr::Symbol(result_variable.clone()),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::List(vec![
                        Expr::Symbol(completed.clone()),
                        Expr::Symbol(value.clone()),
                    ]),
                    Expr::Symbol(value),
                ]),
                Expr::List(vec![
                    Expr::Symbol("#case".into()),
                    Expr::List(vec![
                        Expr::Symbol(returned.clone()),
                        Expr::Symbol(returned_value.clone()),
                    ]),
                    Expr::List(vec![
                        Expr::Symbol("#block".into()),
                        Expr::List(vec![
                            Expr::Symbol("#async-terminal-return".into()),
                            enclosing_type.clone(),
                            Expr::Symbol(returned_value),
                        ]),
                    ]),
                ]),
            ]),
        ]));
        output
    } else {
        result_variable
    };
    let mut renamed_outputs = Vec::new();
    let resumed_names = output_captures
        .iter()
        .map(|_| fresh_async_name(source, next_name))
        .collect::<Vec<_>>();
    if !output_captures.is_empty() {
        // Destructure the Ready aggregate in one move. Projecting fields one
        // at a time would leave the linear aggregate alive while also binding
        // its contained mutable references.
        let pattern = Expr::List(
            std::iter::once(Expr::Symbol(output_type.clone()))
                .chain(resumed_names.iter().cloned().map(Expr::Symbol))
                .collect(),
        );
        replacement.push(Expr::List(vec![
            Expr::Symbol(
                if output_captures.iter().any(|binding| binding.mutable) {
                    "#let-mut"
                } else {
                    "#let"
                }
                .into(),
            ),
            pattern,
            Expr::Symbol(output_type.clone()),
            Expr::Symbol(result_variable.clone()),
        ]));
    }
    for (binding, resumed_name) in output_captures.iter().zip(resumed_names) {
        renamed_outputs.push((
            binding.name.clone(),
            Binding {
                name: resumed_name,
                ty: binding.ty.clone(),
                mutable: binding.mutable,
            },
        ));
    }
    let task_source = [branch_helper, task_source]
        .into_iter()
        .filter(|helper| !helper.is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    Ok(Some((replacement, task_source, renamed_outputs)))
}

/// Desugar a `#for-range` with one direct await per iteration to a while loop,
/// then reuse the same concrete loop-task lowering. The generated counter is
/// carried in the task state so Pending resumes the same range iteration.
fn lower_async_for_range(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &Expr,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>)>, String> {
    if !has_await(statement) {
        return Ok(None);
    }
    let Some(items) = form(statement, "#for-range") else {
        return Ok(None);
    };
    if items.len() < 5 {
        return Err("@async-fn #for-range await requires a binding, bounds, and body".into());
    }
    let bounds_suspend = has_await(&items[2]) || has_await(&items[3]);
    if bounds_suspend {
        let mut start = items[2].clone();
        let mut end = items[3].clone();
        let mut generated = Vec::new();
        let mut generated_helpers = Vec::new();
        extract_nested_awaits(
            &mut start,
            &mut generated,
            &mut generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
        extract_nested_awaits(
            &mut end,
            &mut generated,
            &mut generated_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
        if !generated.iter().any(has_await) {
            return Err(
                "@async-fn #for-range bounds require explicitly typed #await expressions".into(),
            );
        }
        let mut range = statement.clone();
        let Expr::List(range_items) = &mut range else {
            unreachable!()
        };
        range_items[2] = start;
        range_items[3] = end;
        let mut range_known = known.clone();
        let mut range_order = known_order.to_vec();
        for declaration in &generated {
            if form(declaration, "#let").is_some() || form(declaration, "#let-mut").is_some() {
                let local = binding(declaration, "for-range bound await")?;
                range_order.push(local.name.clone());
                range_known.insert(local.name.clone(), local);
            }
        }
        let (range_body, range_helper, renames) = if let Some((replacement, helper, renames)) =
            lower_async_for_range(
                &range,
                &range_known,
                &range_order,
                following,
                return_value,
                source,
                next_name,
                waker,
            )? {
            (replacement, helper, renames)
        } else {
            (vec![range], String::new(), Vec::new())
        };
        generated.extend(range_body);
        let helper = [generated_helpers.join("\n"), range_helper]
            .into_iter()
            .filter(|helper| !helper.is_empty())
            .collect::<Vec<_>>()
            .join("\n");
        return Ok(Some((generated, helper, renames)));
    }
    let Expr::List(range_binding) = &items[1] else {
        return Err("@async-fn #for-range binding must have the form (name Type)".into());
    };
    if range_binding.len() != 2 {
        return Err("@async-fn #for-range binding must have the form (name Type)".into());
    }
    let iteration_name = symbol(&range_binding[0], "for-range binding name")?.to_owned();
    let iteration_type = symbol(&range_binding[1], "for-range integer type")?.to_owned();
    if !matches!(
        iteration_type.as_str(),
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
    ) {
        return Err(format!(
            "@async-fn #for-range await requires an integer index type, got '{iteration_type}'"
        ));
    }

    let index = fresh_async_name(source, next_name);
    let index_binding = Expr::List(vec![
        Expr::Symbol("#let-mut".into()),
        Expr::Symbol(index.clone()),
        Expr::Symbol(iteration_type.clone()),
        items[2].clone(),
    ]);
    let iteration_binding = Expr::List(vec![
        Expr::Symbol("#let".into()),
        Expr::Symbol(iteration_name),
        Expr::Symbol(iteration_type.clone()),
        Expr::Symbol(index.clone()),
    ]);
    let condition = Expr::List(vec![
        Expr::Symbol(format!("#{iteration_type}.<")),
        Expr::Symbol(index.clone()),
        items[3].clone(),
    ]);
    let increment = Expr::List(vec![
        Expr::Symbol("#set".into()),
        Expr::Symbol(index.clone()),
        Expr::List(vec![
            Expr::Symbol(format!("#{iteration_type}.+.wrap")),
            Expr::Symbol(index.clone()),
            Expr::Integer(1),
        ]),
    ]);
    let mut body = items[4..].to_vec();
    let step_is_lowered_at_transfer = if let Some(terminal) = body.last_mut() {
        if contains_loop_control(terminal) {
            rewrite_for_terminal_control(terminal, &increment)?
        } else {
            false
        }
    } else {
        false
    };
    let mut while_items = vec![Expr::Symbol("#while".into()), condition, iteration_binding];
    while_items.extend(body);
    if !step_is_lowered_at_transfer {
        while_items.push(increment);
    }
    let lowered_loop = Expr::List(while_items);

    let mut loop_known = known.clone();
    loop_known.insert(
        index.clone(),
        Binding {
            name: index.clone(),
            ty: iteration_type,
            mutable: true,
        },
    );
    let mut loop_order = known_order.to_vec();
    loop_order.push(index.clone());
    let Some((mut replacement, helper, renames)) = lower_async_while_with_transfers(
        &lowered_loop,
        &loop_known,
        &loop_order,
        &[],
        &[],
        following,
        return_value,
        None,
        source,
        next_name,
        waker,
    )?
    else {
        return Err("@async-fn failed to lower awaited #for-range".into());
    };
    replacement.insert(0, index_binding);
    Ok(Some((replacement, helper, renames)))
}

/// Lower a `#for` loop that uses an existing counter. Initializer-local
/// declarations are intentionally rejected because their source scope ends
/// with the loop and must not leak into the generated async function.
fn async_for_body_step_task(
    body: &[Expr],
    return_signal: bool,
    generated_copy_types: &[String],
    owned_captures: &[String],
    step: &Expr,
    post_step: &[Expr],
    target: &Binding,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<(AwaitProtocol, Expr, String, Vec<Binding>, bool), String> {
    let transfer_name = (return_signal || body.iter().any(contains_loop_control))
        .then(|| fresh_async_name(source, next_name));
    let mut iteration_body = body.to_vec();
    let mut has_break = return_signal;
    if let Some(transfer_name) = &transfer_name {
        if return_signal {
            let mut found_return = false;
            for expression in &mut iteration_body {
                found_return |= rewrite_async_for_return_marker(expression, transfer_name)?;
            }
            if !found_return {
                return Err("@async-fn lost a three-phase #for return during lowering".into());
            }
        }
        for expression in &mut iteration_body {
            has_break |= rewrite_async_for_body_transfer(expression, transfer_name)?;
        }
    }
    let mut function_body = Vec::new();
    if has_break {
        let stop = transfer_name.as_ref().expect("break has a stop binding");
        function_body.push(Expr::List(vec![
            Expr::Symbol("#let-mut".into()),
            Expr::Symbol(stop.clone()),
            Expr::Symbol("bool".into()),
            Expr::Symbol("false".into()),
        ]));
    }
    function_body.extend(iteration_body);
    let mut step_choice_helper = None;
    if has_break {
        let stop = transfer_name.as_ref().expect("break has a stop binding");
        let mut step_block = vec![Expr::Symbol("#block".into())];
        let mut step_aliases = Vec::new();
        let mut restore_step_aliases = Vec::new();
        let mut step_names = HashSet::new();
        collect_value_names(step, &mut step_names);
        for expression in post_step {
            collect_value_names(expression, &mut step_names);
        }
        let mut step = step.clone();
        let mut post_step = post_step.to_vec();
        for name in known_order.iter().filter(|name| step_names.contains(*name)) {
            let Some(capture) = known.get(name) else {
                continue;
            };
            let alias = fresh_async_name(source, next_name);
            let parsed_type = crate::parse(&capture.ty)?;
            let ty = parsed_type
                .first()
                .ok_or_else(|| "@async-fn three-phase #for capture type is empty".to_owned())?
                .expr
                .clone();
            step_aliases.push(Expr::List(if capture.mutable {
                vec![
                    Expr::Symbol("#let-mut".into()),
                    Expr::Symbol(alias.clone()),
                    ty,
                    Expr::Symbol(capture.name.clone()),
                ]
            } else {
                vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(alias.clone()),
                    ty,
                    Expr::Symbol(capture.name.clone()),
                ]
            }));
            if capture.mutable {
                restore_step_aliases.push(Expr::List(vec![
                    Expr::Symbol("#set".into()),
                    Expr::Symbol(capture.name.clone()),
                    Expr::Symbol(alias.clone()),
                ]));
            }
            rename_async_value(&mut step, &capture.name, &alias);
            for expression in &mut post_step {
                rename_async_value(expression, &capture.name, &alias);
            }
        }
        let target = post_step
            .first()
            .and_then(|expression| form(expression, "#set"))
            .and_then(|set| set.get(1))
            .and_then(|target| match target {
                Expr::Symbol(name) => Some(name.clone()),
                _ => None,
            })
            .ok_or_else(|| "@async-fn three-phase #for lost its step assignment".to_owned())?;
        let mut step = step;
        let step_binding = form(&step, "#let")
            .or_else(|| form(&step, "#let-mut"))
            .ok_or_else(|| "@async-fn three-phase #for step is not a binding".to_owned())?;
        let await_expression = step_binding
            .get(3)
            .ok_or_else(|| "@async-fn three-phase #for step binding has no value".to_owned())?
            .clone();
        let await_items = form(&await_expression, "#await")
            .ok_or_else(|| "@async-fn three-phase #for step requires a direct await".to_owned())?;
        if await_items.len() != 7 {
            return Err(
                "@async-fn three-phase #for step await must retain its explicit result type".into(),
            );
        }
        let choice_base = fresh_async_name(source, next_name);
        let choice_task_type = format!("{choice_base}-step-choice-task");
        let choice_skip = format!("{choice_base}-step-choice-skip");
        let choice_run = format!("{choice_base}-step-choice-run");
        let choice_poll_result = format!("{choice_base}-step-choice-poll-result");
        let choice_pending = format!("{choice_base}-step-choice-pending");
        let choice_ready = format!("{choice_base}-step-choice-ready");
        let choice_poll = format!("{choice_base}-step-choice-poll");
        let result_type_source = expression_source(&await_items[1])?;
        let child_type_source = expression_source(&await_items[2])?;
        let pending_source = symbol(&await_items[3], "step Pending variant")?;
        let ready_source = symbol(&await_items[4], "step Ready variant")?;
        let child_poll = symbol(&await_items[5], "step poll function")?;
        let child_task = await_items[6].clone();
        let skip_value = Expr::List(vec![
            Expr::Symbol(choice_skip.clone()),
            Expr::Symbol(target),
        ]);
        let run_value = Expr::List(vec![Expr::Symbol(choice_run.clone()), child_task]);
        let choice_task = Expr::List(vec![
            Expr::Symbol("#if".into()),
            Expr::Symbol(stop.clone()),
            skip_value,
            run_value,
        ]);
        let choice_await = Expr::List(vec![
            Expr::Symbol("#await".into()),
            await_items[1].clone(),
            Expr::Symbol(choice_task_type.clone()),
            Expr::Symbol(choice_pending.clone()),
            Expr::Symbol(choice_ready.clone()),
            Expr::Symbol(choice_poll.clone()),
            choice_task,
        ]);
        let choice_helper = format!(
            "(#enum {choice_task_type} (({choice_skip} {result_type_source}) ({choice_run} {child_type_source})))\n\
             (#linear {choice_task_type})\n\
             (#enum {choice_poll_result} (({choice_pending} {choice_task_type}) ({choice_ready} {result_type_source})))\n\
             (#fn {choice_poll} ((task {choice_task_type}) (waker (#ref {waker}))) {choice_poll_result}\n\
               (#return (#match task\n\
                 (#case ({choice_skip} value) ({choice_ready} value))\n\
                 (#case ({choice_run} child)\n\
                   (#match (#call {child_poll} (: task child : waker waker))\n\
                     (#case ({pending_source} pending) ({choice_pending} ({choice_run} pending)))\n\
                     (#case ({ready_source} value) ({choice_ready} value)))))))"
        );
        step_choice_helper = Some(choice_helper);
        let step_binding = match &mut step {
            Expr::List(items) => items,
            _ => unreachable!(),
        };
        step_binding[3] = choice_await;
        step_block.push(step);
        step_block.extend(post_step);
        step_block.push(Expr::List(Vec::new()));
        function_body.extend(step_aliases);
        function_body.push(Expr::List(step_block));
        function_body.extend(restore_step_aliases);
    } else {
        function_body.push(step.clone());
        function_body.extend(post_step.iter().cloned());
    }
    for expression in &mut function_body {
        let Some(binding) = form(expression, "#let").or_else(|| form(expression, "#let-mut"))
        else {
            continue;
        };
        if binding.len() != 4 {
            continue;
        }
        let Some(await_form) = form(&binding[3], "#await") else {
            continue;
        };
        if await_form.len() == 7 {
            let normalized = Expr::List(
                std::iter::once(Expr::Symbol("#await".into()))
                    .chain(await_form[2..].iter().cloned())
                    .collect(),
            );
            let Expr::List(binding) = expression else {
                unreachable!()
            };
            binding[3] = normalized;
        }
    }
    let mut value_names = HashSet::new();
    for expression in &function_body {
        collect_value_names(expression, &mut value_names);
    }
    let mut local_names = HashSet::new();
    for expression in &function_body {
        collect_local_binding_names(expression, &mut local_names);
    }
    for local in local_names {
        value_names.remove(&local);
    }
    let captures = known_order
        .iter()
        .filter(|name| value_names.contains(*name))
        .filter_map(|name| known.get(name).cloned())
        .collect::<Vec<_>>();
    if !captures.iter().any(|capture| capture.name == target.name) {
        return Err("@async-fn three-phase #for lost its step target binding".into());
    }
    for capture in &captures {
        let parsed_type = crate::parse(&capture.ty)?;
        let type_expression = parsed_type
            .first()
            .ok_or_else(|| "@async-fn three-phase #for capture type is empty".to_owned())?;
        let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
        if !with_additional_named_copy_types(generated_copy_types, || {
            async_task_capture_is_copy(&ty)
        }) && !async_task_capture_is_mutable_reference(&ty)
            && !owned_captures.contains(&capture.name)
        {
            return Err(format!(
                "@async-fn three-phase #for captures non-Copy local '{}'; carry it in a concrete child-task result",
                capture.name
            ));
        }
    }
    let updated = captures
        .iter()
        .filter(|capture| capture.mutable)
        .cloned()
        .collect::<Vec<_>>();
    if !updated.iter().any(|capture| capture.name == target.name) {
        return Err("@async-fn three-phase #for step target is not mutable".into());
    }
    let mut tuple_types = vec![Expr::Symbol("#tuple".into())];
    if has_break {
        tuple_types.push(Expr::Symbol("bool".into()));
    }
    for capture in &updated {
        let parsed_type = crate::parse(&capture.ty)?;
        let ty = parsed_type
            .first()
            .ok_or_else(|| "@async-fn three-phase #for capture type is empty".to_owned())?
            .expr
            .clone();
        tuple_types.push(ty.clone());
    }
    let result_type = Expr::List(tuple_types);
    let result_value = Expr::List(
        std::iter::once(Expr::Symbol("#tuple".into()))
            .chain(std::iter::once(result_type.clone()))
            .chain(
                transfer_name
                    .as_ref()
                    .filter(|_| has_break)
                    .map(|name| Expr::Symbol(name.clone())),
            )
            .chain(
                updated
                    .iter()
                    .map(|capture| Expr::Symbol(capture.name.clone())),
            )
            .collect(),
    );
    function_body.push(Expr::List(vec![
        Expr::Symbol("#return".into()),
        result_value,
    ]));

    let base = fresh_async_name(source, next_name);
    let function_name = format!("{base}-iteration-function");
    let frame = format!("{base}-iteration-frame");
    let poll_result = format!("{base}-iteration-poll-result");
    let pending = format!("{base}-iteration-pending");
    let ready = format!("{base}-iteration-ready");
    let poll = format!("{base}-iteration-poll");
    let mut parameters = Vec::new();
    let mut call_arguments = Vec::new();
    for capture in &captures {
        let parsed_type = crate::parse(&capture.ty)?;
        let ty = parsed_type
            .first()
            .ok_or_else(|| "@async-fn three-phase #for capture type is empty".to_owned())?
            .expr
            .clone();
        let name = Expr::Symbol(capture.name.clone());
        parameters.push(Expr::List(if capture.mutable {
            vec![Expr::Symbol("#mut".into()), name.clone(), ty]
        } else {
            vec![name.clone(), ty]
        }));
        call_arguments.push(Expr::List(vec![name.clone(), name]));
    }
    let function = Expr::List(
        vec![
            Expr::Symbol("#fn".into()),
            Expr::Symbol(function_name.clone()),
            Expr::List(parameters),
            result_type.clone(),
        ]
        .into_iter()
        .chain(function_body)
        .collect(),
    );
    let waker_expression = crate::parse(waker)?
        .into_iter()
        .next()
        .ok_or_else(|| "@async-fn waker type is empty".to_owned())?
        .expr;
    let invocation = Expr::List(vec![
        Expr::At,
        Expr::Symbol("async-fn".into()),
        Expr::List(vec![
            Expr::Symbol(frame.clone()),
            Expr::Symbol(poll_result.clone()),
            Expr::Symbol(pending.clone()),
            Expr::Symbol(ready.clone()),
            Expr::Symbol(poll.clone()),
        ]),
        waker_expression,
        function,
    ]);
    let iteration_helper =
        with_additional_named_copy_types(generated_copy_types, || generated_source(&invocation))?;
    let helper = std::iter::once(step_choice_helper.unwrap_or_default())
        .chain(std::iter::once(iteration_helper))
        .filter(|helper| !helper.is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    let task = Expr::List(vec![
        Expr::Symbol("#call".into()),
        Expr::Symbol(function_name),
        Expr::List(call_arguments),
    ]);
    Ok((
        AwaitProtocol {
            result_type,
            child_type: Expr::Symbol(frame),
            pending: Expr::Symbol(pending),
            ready: Expr::Symbol(ready),
            poll: Expr::Symbol(poll),
        },
        task,
        helper,
        updated,
        has_break,
    ))
}

fn lower_async_for(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &mut Expr,
    return_type: &Expr,
    source: &str,
    next_name: &mut usize,
    waker: &str,
    type_environment: &AsyncTypeEnvironment,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>, usize)>, String> {
    if !has_await(statement) {
        return Ok(None);
    }
    let Some(items) = form(statement, "#for") else {
        return Ok(None);
    };
    if items.len() < 5 {
        return Err("@async-fn #for await requires init, condition, step, and body".into());
    }
    let direct_step_await = form(&items[3], "#await").is_some()
        || form(&items[3], "#set")
            .is_some_and(|set| set.len() == 3 && form(&set[2], "#await").is_some());
    if has_await(&items[3]) && !direct_step_await {
        // A computed step belongs to the iteration's body, not to a separate
        // direct-await adapter. Let body lowering sequence its arbitrary
        // expressions and return every mutated capture to the outer loop,
        // whether the condition itself suspends or is synchronous.
        let step = items[3].clone();
        let mut body = items[4..].to_vec();
        if body
            .last()
            .is_some_and(|last| contains_loop_control(last) || contains_return(last))
        {
            rewrite_for_terminal_control(body.last_mut().unwrap(), &step)?;
        } else {
            body.push(step);
        }
        let mut rewritten = items[..4].to_vec();
        rewritten[3] = Expr::List(vec![]);
        rewritten.extend(body);
        return lower_async_for(
            &Expr::List(rewritten),
            known,
            known_order,
            following,
            return_value,
            return_type,
            source,
            next_name,
            waker,
            type_environment,
        );
    }
    // A void await is a valid effect-only step. Route it through the same
    // assignment machinery as value-producing steps, including the skip-step
    // path for break and the run-step path for continue.
    if let Some(awaited) = form(&items[3], "#await") {
        if awaited.len() == 7
            && parse_type(Some(&normalize_keywords(awaited[1].clone())))? == Type::Unit
        {
            let unit_name = fresh_async_name(source, next_name);
            let mut child_known = known.clone();
            child_known.insert(
                unit_name.clone(),
                Binding {
                    name: unit_name.clone(),
                    ty: "()".into(),
                    mutable: true,
                },
            );
            let mut child_order = known_order.to_vec();
            child_order.push(unit_name.clone());
            let mut rewritten = items.to_vec();
            rewritten[3] = Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(unit_name.clone()),
                items[3].clone(),
            ]);
            // The three-phase path carries terminal loop transfers through
            // an awaited condition. An immediate condition adapter adds no
            // suspension and lets synchronous conditions use that same path.
            let condition_helper =
                if !has_await(&items[2]) && items[4..].iter().any(contains_loop_control) {
                    let (awaited, helper) =
                        immediate_await(&items[2], "bool", "condition", source, next_name, waker)?;
                    rewritten[2] = awaited;
                    helper
                } else {
                    String::new()
                };
            let Some((mut replacement, helper, renames, consumed)) = lower_async_for(
                &Expr::List(rewritten),
                &child_known,
                &child_order,
                following,
                return_value,
                return_type,
                source,
                next_name,
                waker,
                type_environment,
            )?
            else {
                return Err("@async-fn failed to lower unit-await for step".into());
            };
            replacement.insert(
                0,
                Expr::List(vec![
                    Expr::Symbol("#let-mut".into()),
                    Expr::Symbol(unit_name),
                    Expr::List(vec![]),
                    Expr::List(vec![]),
                ]),
            );
            let helper = [condition_helper, helper]
                .into_iter()
                .filter(|helper| !helper.is_empty())
                .collect::<Vec<_>>()
                .join("\n");
            return Ok(Some((replacement, helper, renames, consumed)));
        }
    }
    let initializer = &items[1];
    let mut condition = items[2].clone();
    normalize_short_circuit_await(&mut condition);
    let awaited_condition = has_await(&condition);
    let awaited_step = has_await(&items[3]);
    let awaited_initializer = has_await(initializer);
    let mut initializer_prefix = Vec::new();
    let mut initializer_helpers = Vec::new();
    let mut initializer_value = None;
    if awaited_initializer && form(initializer, "#let-else").is_some() {
        let mut initializer_statement = initializer.clone();
        extract_statement_awaits(
            &mut initializer_statement,
            &mut initializer_prefix,
            &mut initializer_helpers,
            known,
            source,
            next_name,
            waker,
        )?;
        if awaited_condition || awaited_step || items[4..].iter().any(has_await) {
            let let_else = form(&initializer_statement, "#let-else").ok_or_else(|| {
                "@async-fn lost awaited #let-else initializer during lowering".to_owned()
            })?;
            let mut pattern_bindings = Vec::new();
            collect_enum_pattern_bindings(
                &let_else[1],
                symbol(&let_else[2], "#let-else type")?,
                type_environment,
                &mut pattern_bindings,
            )?;
            let mut loop_known = known.clone();
            let mut loop_order = known_order.to_vec();
            let mut condition = condition;
            let mut step = items[3].clone();
            let mut body = items[4..].to_vec();
            let mut seen = HashSet::new();
            for (name, ty) in pattern_bindings {
                if !seen.insert(name.clone()) || known.contains_key(&name) {
                    return Err(format!(
                        "@async-fn #for initializer pattern binding '{name}' shadows an existing name"
                    ));
                }
                let generated_name = fresh_async_name(source, next_name);
                rename_pattern_binding(
                    &mut expression_list_mut(&mut initializer_statement)[1],
                    &name,
                    &generated_name,
                );
                rename_async_value(&mut condition, &name, &generated_name);
                rename_async_value(&mut step, &name, &generated_name);
                for expression in &mut body {
                    rename_async_value(expression, &name, &generated_name);
                }
                loop_known.insert(
                    generated_name.clone(),
                    Binding {
                        name: generated_name.clone(),
                        ty,
                        mutable: false,
                    },
                );
                loop_order.push(generated_name);
            }
            let mut loop_items = vec![
                Expr::Symbol("#for".into()),
                Expr::List(Vec::new()),
                condition,
                step,
            ];
            loop_items.extend(body);
            let loop_form = Expr::List(loop_items);
            let Some((replacement, loop_helpers, renames, consumed_following)) = lower_async_for(
                &loop_form,
                &loop_known,
                &loop_order,
                following,
                return_value,
                return_type,
                source,
                next_name,
                waker,
                type_environment,
            )?
            else {
                return Err(
                    "@async-fn failed to lower awaited #for after #let-else initializer".into(),
                );
            };
            let mut output = initializer_prefix;
            output.push(initializer_statement);
            output.extend(replacement);
            let helpers = [initializer_helpers.join("\n"), loop_helpers]
                .into_iter()
                .filter(|helper| !helper.is_empty())
                .collect::<Vec<_>>()
                .join("\n");
            return Ok(Some((output, helpers, renames, consumed_following)));
        }
        let mut loop_form = vec![
            Expr::Symbol("#for".into()),
            initializer_statement,
            items[2].clone(),
            items[3].clone(),
        ];
        loop_form.extend(items[4..].iter().cloned());
        initializer_prefix.push(Expr::List(loop_form));
        return Ok(Some((
            initializer_prefix,
            initializer_helpers.join("\n"),
            Vec::new(),
            0,
        )));
    }
    if awaited_initializer {
        let initializer_form = form(initializer, "#let")
            .or_else(|| form(initializer, "#let-mut"))
            .ok_or_else(|| {
                "@async-fn #for initializer suspension requires a #let or #let-mut binding"
                    .to_owned()
            })?;
        if initializer_form.len() != 4 {
            return Err("@async-fn #for initializer requires (#let name Type (#await ...))".into());
        }
        if let Some(await_form) = form(&initializer_form[3], "#await") {
            if await_form.len() == 6 && has_await(&await_form[5]) {
                let mut value = initializer_form[3].clone();
                let Expr::List(await_items) = &mut value else {
                    unreachable!()
                };
                extract_nested_awaits(
                    &mut await_items[5],
                    &mut initializer_prefix,
                    &mut initializer_helpers,
                    known,
                    source,
                    next_name,
                    waker,
                )?;
                initializer_value = Some(value);
            }
        } else {
            let mut value = initializer_form[3].clone();
            extract_nested_awaits(
                &mut value,
                &mut initializer_prefix,
                &mut initializer_helpers,
                known,
                source,
                next_name,
                waker,
            )?;
            if !initializer_prefix.iter().any(has_await) {
                return Err(
                    "@async-fn #for initializer requires a direct or nested typed #await".into(),
                );
            }
            initializer_value = Some(value);
        }
    }
    let mut loop_known = known.clone();
    let mut loop_order = known_order.to_vec();
    let mut transferred_reference_declarations = Vec::new();
    let mut transferred_reference_renames = Vec::new();
    let mut body_reference_transfers = Vec::new();
    let mut initializer_statement = initializer.clone();
    let mut condition_helpers = Vec::new();
    let mut return_status_initialization = None;
    let mut return_status_completion = None;
    let mut return_status_copy_types = Vec::new();
    let mut return_status_owned_captures = Vec::new();
    let mut consumed_following = 0;
    if awaited_condition && form(&condition, "#await").is_none() {
        let mut condition_known = loop_known.clone();
        if form(initializer, "#let").is_some() || form(initializer, "#let-mut").is_some() {
            let local = binding(initializer, "for initializer")?;
            condition_known.insert(local.name.clone(), local);
        }
        let condition_task = if let Some((protocol, task, helper)) =
            conditional_await_with_immediate(
                &condition,
                &condition_known,
                source,
                next_name,
                waker,
            )? {
            Some((protocol, task, helper))
        } else {
            conditional_value_expression_task(
                &condition,
                &condition_known,
                source,
                next_name,
                waker,
            )?
        };
        let Some((protocol, task, helper)) = condition_task else {
            return Err(
                "@async-fn #for condition requires an explicitly typed awaited expression".into(),
            );
        };
        if !helper.is_empty() {
            condition_helpers.push(helper);
        }
        condition = Expr::List(vec![
            Expr::Symbol("#await".into()),
            protocol.child_type,
            protocol.pending,
            protocol.ready,
            protocol.poll,
            task,
        ]);
    }
    let mut step = items[3].clone();
    let mut loop_body = items[4..].to_vec();
    if let Some(init_form) = form(initializer, "#let").or_else(|| form(initializer, "#let-mut")) {
        let local = binding(initializer, "for initializer")?;
        if known.contains_key(&local.name) {
            return Err(format!(
                "@async-fn #for initializer '{}' shadows an existing name",
                local.name
            ));
        }
        let generated_name = fresh_async_name(source, next_name);
        rename_async_value(&mut condition, &local.name, &generated_name);
        rename_async_value(&mut step, &local.name, &generated_name);
        for expression in &mut loop_body {
            rename_async_value(expression, &local.name, &generated_name);
        }
        loop_known.insert(
            generated_name.clone(),
            Binding {
                name: generated_name.clone(),
                ty: local.ty.clone(),
                mutable: local.mutable,
            },
        );
        loop_order.push(generated_name.clone());
        initializer_statement = Expr::List(vec![
            Expr::Symbol(
                if form(initializer, "#let-mut").is_some() {
                    "#let-mut"
                } else {
                    "#let"
                }
                .into(),
            ),
            Expr::Symbol(generated_name),
            Expr::Symbol(local.ty),
            initializer_value
                .take()
                .unwrap_or_else(|| init_form[3].clone()),
        ]);
    }

    if awaited_initializer
        && !awaited_condition
        && !awaited_step
        && !loop_body.iter().any(has_await)
    {
        let mut for_items = vec![
            Expr::Symbol("#for".into()),
            Expr::List(Vec::new()),
            condition,
            step,
        ];
        for_items.extend(loop_body);
        initializer_prefix.push(initializer_statement);
        initializer_prefix.push(Expr::List(for_items));
        return Ok(Some((
            initializer_prefix,
            initializer_helpers.join("\n"),
            Vec::new(),
            0,
        )));
    }

    let mut post_step = Vec::new();
    let mut step_prefix = Vec::new();
    let mut step_helpers = Vec::new();
    if awaited_step {
        if let Some(set) = form(&step, "#set") {
            if set.len() != 3 {
                return Err(
                    "@async-fn awaited #for step assignment requires a target and value".into(),
                );
            }
            let target = symbol(&set[1], "#for step assignment target")?.to_owned();
            let target_binding = loop_known.get(&target).ok_or_else(|| {
                format!("@async-fn awaited #for step assigns unknown local '{target}'")
            })?;
            let result_name = fresh_async_name(source, next_name);
            let value = if let Some(await_form) = form(&set[2], "#await") {
                let await_form = if await_form.len() == 7 {
                    parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
                    std::iter::once(Expr::Symbol("#await".into()))
                        .chain(await_form[2..].iter().cloned())
                        .collect()
                } else if await_form.len() == 6 {
                    await_form.to_vec()
                } else {
                    return Err(
                        "@async-fn awaited #for step assignment requires (#await Child Pending Ready poll task)".into(),
                    );
                };
                Expr::List(await_form)
            } else {
                let mut value = set[2].clone();
                extract_nested_awaits(
                    &mut value,
                    &mut step_prefix,
                    &mut step_helpers,
                    &loop_known,
                    source,
                    next_name,
                    waker,
                )?;
                if !step_prefix.iter().any(has_await) {
                    return Err(
                        "@async-fn awaited #for step assignment requires a direct or nested typed #await".into(),
                    );
                }
                value
            };
            let value = if awaited_condition {
                let await_items = form(&value, "#await").ok_or_else(|| {
                    "@async-fn awaited #for step requires a direct #await".to_owned()
                })?;
                Expr::List(
                    std::iter::once(Expr::Symbol("#await".into()))
                        .chain(std::iter::once(Expr::Symbol(target_binding.ty.clone())))
                        .chain(await_items[1..].iter().cloned())
                        .collect(),
                )
            } else {
                value
            };
            step = Expr::List(vec![
                Expr::Symbol("#let".into()),
                Expr::Symbol(result_name.clone()),
                Expr::Symbol(target_binding.ty.clone()),
                value,
            ]);
            post_step.push(Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(target),
                Expr::Symbol(result_name),
            ]));
        } else if form(&step, "#let").is_none() && form(&step, "#let-mut").is_none() {
            return Err(
                "@async-fn awaited #for step currently requires a direct await binding or assignment".into(),
            );
        }
    }

    if awaited_condition {
        if awaited_step {
            let combined_body_step = loop_body.iter().any(|expression| {
                has_await(expression)
                    || contains_loop_control(expression)
                    || contains_return(expression)
            });
            if combined_body_step {
                let return_signal = loop_body.iter().any(contains_return);
                if return_signal {
                    consumed_following = following.len();
                    if loop_body[..loop_body.len().saturating_sub(1)]
                        .iter()
                        .any(contains_return)
                    {
                        return Err(
                            "@async-fn three-phase #for returns must be terminal body control flow"
                                .into(),
                        );
                    }
                    let return_type_ast =
                        parse_type(Some(&normalize_keywords(return_type.clone())))?;
                    let return_type_is_copy = async_task_capture_is_copy(&return_type_ast);
                    let status_type = fresh_async_name(source, next_name);
                    let status_name = fresh_async_name(source, next_name);
                    if return_type_is_copy {
                        return_status_copy_types.push(status_type.clone());
                    } else {
                        return_status_owned_captures.push(status_name.clone());
                    }
                    let tail_variant = format!("{status_type}-tail");
                    let returned_variant = format!("{status_type}-returned");
                    let return_type_source = expression_source(return_type)?;
                    let terminal = loop_body
                        .last_mut()
                        .expect("a for form contains its body after validation");
                    *terminal = rewrite_async_for_body_returns(
                    terminal,
                    &status_name,
                    &returned_variant,
                    !return_type_is_copy,
                )
                .ok_or_else(|| {
                    "@async-fn three-phase #for requires returns in terminal #block, #if, or #match branches"
                        .to_owned()
                })?;
                    loop_known.insert(
                        status_name.clone(),
                        Binding {
                            name: status_name.clone(),
                            ty: status_type.clone(),
                            mutable: true,
                        },
                    );
                    loop_order.push(status_name.clone());
                    step_helpers.push(format!(
                        "(#enum {status_type} (({tail_variant}) ({returned_variant} {return_type_source})))"
                    ));
                    if !return_type_is_copy {
                        step_helpers.push(format!("(#linear {status_type})"));
                    }
                    return_status_initialization = Some(Expr::List(vec![
                        Expr::Symbol("#let-mut".into()),
                        Expr::Symbol(status_name.clone()),
                        Expr::Symbol(status_type),
                        Expr::List(vec![Expr::Symbol(tail_variant.clone())]),
                    ]));
                    return_status_completion = Some((status_name, returned_variant, tail_variant));
                }
                let mut loop_uses = HashSet::new();
                collect_value_names(&condition, &mut loop_uses);
                collect_value_names(&step, &mut loop_uses);
                for expression in &loop_body {
                    collect_value_names(expression, &mut loop_uses);
                }
                for name in loop_order.clone() {
                    if !loop_uses.contains(&name) {
                        continue;
                    }
                    let Some(capture) = loop_known.get(&name).cloned() else {
                        continue;
                    };
                    if capture.mutable {
                        continue;
                    }
                    let parsed_type = crate::parse(&capture.ty)?;
                    let type_expression = parsed_type
                        .first()
                        .ok_or_else(|| "@async-fn capture type is empty".to_owned())?;
                    let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
                    if !async_task_capture_is_mutable_reference(&ty) {
                        continue;
                    }
                    let alias = fresh_async_name(source, next_name);
                    let alias_binding = Binding {
                        name: alias.clone(),
                        ty: capture.ty.clone(),
                        mutable: true,
                    };
                    transferred_reference_declarations.push(Expr::List(vec![
                        Expr::Symbol("#let-mut".into()),
                        Expr::Symbol(alias.clone()),
                        Expr::Symbol(capture.ty.clone()),
                        Expr::Symbol(capture.name.clone()),
                    ]));
                    for expression in [&mut condition, &mut step] {
                        rename_async_value(expression, &capture.name, &alias);
                    }
                    for expression in &mut loop_body {
                        rename_async_value(expression, &capture.name, &alias);
                    }
                    loop_known.remove(&capture.name);
                    loop_known.insert(alias.clone(), alias_binding.clone());
                    loop_order.retain(|candidate| candidate != &capture.name);
                    loop_order.push(alias.clone());
                    transferred_reference_renames.push((capture.name, alias_binding));
                }
                let set_target = form(&items[3], "#set")
                    .and_then(|set| set.get(1))
                    .ok_or_else(|| {
                        "@async-fn three-phase #for requires an awaited step assignment".to_owned()
                    })?;
                let target = symbol(set_target, "three-phase #for step target")?;
                let target_binding = loop_known.get(target).ok_or_else(|| {
                    format!("@async-fn three-phase #for assigns unknown local '{target}'")
                })?;
                let (protocol, task, helper, updated, has_break) = async_for_body_step_task(
                    &loop_body,
                    return_signal,
                    &return_status_copy_types,
                    &return_status_owned_captures,
                    &step,
                    &post_step,
                    target_binding,
                    &loop_known,
                    &loop_order,
                    source,
                    next_name,
                    waker,
                )?;
                if !helper.is_empty() {
                    step_helpers.push(helper);
                }
                let result_name = fresh_async_name(source, next_name);
                let await_result = Expr::List(vec![
                    Expr::Symbol("#await".into()),
                    protocol.result_type.clone(),
                    protocol.child_type,
                    protocol.pending,
                    protocol.ready,
                    protocol.poll,
                    task,
                ]);
                loop_body = vec![Expr::List(vec![
                    Expr::Symbol("#let".into()),
                    Expr::Symbol(result_name.clone()),
                    protocol.result_type,
                    await_result,
                ])];
                for (index, binding) in updated.into_iter().enumerate() {
                    let result_index = index + if has_break { 1 } else { 0 };
                    let parsed_type = crate::parse(&binding.ty)?;
                    let type_expression = parsed_type
                        .first()
                        .ok_or_else(|| "@async-fn capture type is empty".to_owned())?;
                    let ty = parse_type(Some(&normalize_keywords(type_expression.expr.clone())))?;
                    if async_task_capture_is_mutable_reference(&ty) {
                        body_reference_transfers.push(LoopReferenceTransfer {
                            name: binding.name.clone(),
                            ty: binding.ty.clone(),
                            result_index,
                            resumed_name: fresh_async_name(source, next_name),
                            owned: false,
                        });
                    } else if return_status_owned_captures.contains(&binding.name) {
                        body_reference_transfers.push(LoopReferenceTransfer {
                            name: binding.name.clone(),
                            ty: binding.ty.clone(),
                            result_index,
                            resumed_name: fresh_async_name(source, next_name),
                            owned: true,
                        });
                    } else {
                        let compact_index = result_index
                            - body_reference_transfers
                                .iter()
                                .filter(|transfer| transfer.result_index < result_index)
                                .count();
                        loop_body.push(Expr::List(vec![
                            Expr::Symbol("#set".into()),
                            Expr::Symbol(binding.name),
                            Expr::List(vec![
                                Expr::Symbol("#get".into()),
                                Expr::Symbol(result_name.clone()),
                                Expr::UnsignedInteger(compact_index as u128),
                            ]),
                        ]));
                    }
                }
                if has_break {
                    loop_body.push(Expr::List(vec![
                        Expr::Symbol("#if".into()),
                        Expr::List(vec![
                            Expr::Symbol("#get".into()),
                            Expr::Symbol(result_name),
                            Expr::UnsignedInteger(0),
                        ]),
                        Expr::List(vec![Expr::Symbol("#break".into())]),
                        Expr::List(Vec::new()),
                    ]));
                }
            }
            if !combined_body_step
                && loop_body.iter().any(|expression| {
                    contains_loop_control(expression) || contains_return(expression)
                })
            {
                return Err(
                    "@async-fn #for with awaited condition and step does not support body transfers yet".into(),
                );
            }
            if !combined_body_step {
                let await_form = form(&step, "#let")
                    .and_then(|binding| binding.get(3))
                    .and_then(|value| form(value, "#await"))
                    .ok_or_else(|| {
                        "@async-fn awaited #for step requires a direct #await".to_owned()
                    })?;
                let mut task = await_form
                    .last()
                    .expect("typed awaited #for step includes a task expression")
                    .clone();
                if !loop_body.is_empty() {
                    let mut task_block = vec![Expr::Symbol("#block".into())];
                    task_block.append(&mut loop_body);
                    task_block.push(task);
                    task = Expr::List(task_block);
                }
                let Expr::List(step_binding) = &mut step else {
                    unreachable!()
                };
                let Expr::List(await_items) = &mut step_binding[3] else {
                    unreachable!()
                };
                let task_index = await_items.len() - 1;
                await_items[task_index] = task;
                loop_body.push(step.clone());
                loop_body.extend(post_step.clone());
            }
        } else {
            let terminal_index = loop_body.len().saturating_sub(1);
            if loop_body[..terminal_index]
                .iter()
                .any(contains_loop_control)
            {
                return Err("@async-fn #for loop transfers must be terminal statements".into());
            }
            if loop_body.last().is_some_and(contains_loop_control) {
                rewrite_for_terminal_control(loop_body.last_mut().unwrap(), &step)?;
            } else {
                loop_body.push(step.clone());
            }
        }
    } else if !matches!(&step, Expr::List(items) if items.is_empty()) {
        loop_body.extend(step_prefix);
        loop_body.push(step.clone());
        loop_body.extend(post_step);
    }
    let mut while_items = vec![Expr::Symbol("#while".into()), condition];
    while_items.extend(loop_body);
    let lowered_loop = Expr::List(while_items);
    if let Some((status_name, returned_variant, tail_variant)) = return_status_completion.take() {
        let old_return_value = return_value.clone();
        let result_name = fresh_async_name(source, next_name);
        let normal_completion = if following.is_empty() {
            old_return_value
        } else {
            Expr::List(
                std::iter::once(Expr::Symbol("#block".into()))
                    .chain(following.iter().cloned())
                    .chain(std::iter::once(old_return_value))
                    .collect(),
            )
        };
        *return_value = Expr::List(vec![
            Expr::Symbol("#match".into()),
            Expr::Symbol(status_name),
            Expr::List(vec![
                Expr::Symbol("#case".into()),
                Expr::List(vec![
                    Expr::Symbol(returned_variant),
                    Expr::Symbol(result_name.clone()),
                ]),
                Expr::Symbol(result_name),
            ]),
            Expr::List(vec![
                Expr::Symbol("#case".into()),
                Expr::Symbol(tail_variant),
                normal_completion,
            ]),
        ]);
    }
    // The loop task owns each transferred mutable reference while it is
    // Pending, then returns it in its Ready payload. Liveness must be computed
    // using the alias that is actually carried by the loop, not the original
    // binding name (which is no longer in the loop's environment).
    let mut loop_following = following.to_vec();
    let mut loop_return_value = return_value.clone();
    for (source_name, alias_binding) in &transferred_reference_renames {
        for expression in &mut loop_following {
            rename_async_value(expression, source_name, &alias_binding.name);
        }
        rename_async_value(&mut loop_return_value, source_name, &alias_binding.name);
    }
    let lowered_loop_following = if consumed_following == 0 {
        loop_following.as_slice()
    } else {
        &[]
    };
    let Some((mut replacement, helper, renames)) =
        with_additional_named_copy_types(&return_status_copy_types, || {
            lower_async_while_with_transfers(
                &lowered_loop,
                &loop_known,
                &loop_order,
                &body_reference_transfers,
                &return_status_owned_captures,
                lowered_loop_following,
                &loop_return_value,
                Some(return_type),
                source,
                next_name,
                waker,
            )
        })?
    else {
        return Err("@async-fn failed to lower awaited #for".into());
    };
    let transfer_prefix_len = transferred_reference_declarations.len();
    replacement.splice(0..0, transferred_reference_declarations);
    let initializer_prefix_len = initializer_prefix.len();
    replacement.splice(transfer_prefix_len..transfer_prefix_len, initializer_prefix);
    if !matches!(initializer, Expr::List(items) if items.is_empty()) {
        replacement.insert(
            transfer_prefix_len + initializer_prefix_len,
            initializer_statement,
        );
    }
    if let Some(initialization) = return_status_initialization {
        replacement.insert(0, initialization);
    }
    let helper = [
        initializer_helpers.join("\n"),
        condition_helpers.join("\n"),
        step_helpers.join("\n"),
        helper,
    ]
    .into_iter()
    .filter(|helper| !helper.is_empty())
    .collect::<Vec<_>>()
    .join("\n");
    let mut renames = renames;
    for (source_name, alias_binding) in transferred_reference_renames {
        if let Some((_, resumed_binding)) = renames
            .iter()
            .find(|(name, _)| name == &alias_binding.name)
            .cloned()
        {
            renames.retain(|(name, _)| name != &alias_binding.name && name != &source_name);
            renames.push((source_name, resumed_binding));
        } else {
            renames.push((source_name, alias_binding));
        }
    }
    Ok(Some((replacement, helper, renames, consumed_following)))
}

fn resolve_async_enum_name<'a>(
    type_name: &'a str,
    environment: &'a AsyncTypeEnvironment,
) -> Option<&'a str> {
    let mut current = type_name;
    for _ in 0..=environment.aliases.len() {
        if environment.enums.contains_key(current) {
            return Some(current);
        }
        current = environment.aliases.get(current)?;
    }
    None
}

fn collect_enum_pattern_bindings(
    pattern: &Expr,
    type_name: &str,
    environment: &AsyncTypeEnvironment,
    bindings: &mut Vec<(String, String)>,
) -> Result<(), String> {
    match pattern {
        Expr::Symbol(name) if name == "_" || matches!(name.as_str(), "true" | "false") => {}
        Expr::Symbol(name) => {
            let is_unit_variant = resolve_async_enum_name(type_name, environment)
                .and_then(|enum_name| environment.enums.get(enum_name))
                .is_some_and(|variants| variants.contains_key(name));
            if !is_unit_variant {
                bindings.push((name.clone(), type_name.to_owned()));
            }
        }
        Expr::List(items) if !items.is_empty() => {
            let Expr::Symbol(variant_name) = &items[0] else {
                return Err("@async-fn #for initializer requires named enum patterns".into());
            };
            // Tuple/array payloads have explicit structural declarations too.
            // Resolve aliases only to select their layout; keep the declared
            // field type spelling when introducing each captured binding.
            let mut declared = type_name;
            let mut visited = HashSet::new();
            while let Some(target) = environment.aliases.get(declared) {
                if !visited.insert(declared) {
                    return Err(format!("@async-fn cyclic pattern type alias '{type_name}'"));
                }
                declared = target;
            }
            let parsed = crate::parse(declared)?;
            let ty = parse_type(Some(&normalize_keywords(
                parsed
                    .first()
                    .ok_or_else(|| format!("@async-fn missing pattern type '{type_name}'"))?
                    .expr
                    .clone(),
            )))?;
            let structural_fields = match ty {
                Type::Tuple(fields) if matches!(variant_name.as_str(), "#tuple" | "tuple") => {
                    Some(fields.iter().map(crate::type_source).collect::<Vec<_>>())
                }
                Type::Array(element, length)
                    if matches!(variant_name.as_str(), "#array" | "array") =>
                {
                    if length != items.len() - 1 {
                        return Err(format!("@async-fn array pattern expects {length} elements"));
                    }
                    Some(vec![crate::type_source(&element); length])
                }
                Type::Named(name)
                    if variant_name == &name && environment.struct_fields.contains_key(&name) =>
                {
                    let order = environment.struct_field_order.get(&name).ok_or_else(|| {
                        format!("@async-fn missing declared field order for '{name}'")
                    })?;
                    let fields = &environment.struct_fields[&name];
                    Some(
                        order
                            .iter()
                            .map(|field| {
                                fields.get(field).cloned().ok_or_else(|| {
                                    format!("@async-fn missing declared field '{name}.{field}'")
                                })
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                _ => None,
            };
            if let Some(fields) = structural_fields {
                if fields.len() != items.len() - 1 {
                    return Err(format!(
                        "@async-fn aggregate pattern '{variant_name}' expects {} fields",
                        fields.len()
                    ));
                }
                for (pattern, field_type) in items[1..].iter().zip(&fields) {
                    collect_enum_pattern_bindings(pattern, field_type, environment, bindings)?;
                }
                return Ok(());
            }
            let enum_name = resolve_async_enum_name(type_name, environment).ok_or_else(|| {
                format!("@async-fn cannot resolve enum payload types for '{type_name}'")
            })?;
            let fields = environment
                .enums
                .get(enum_name)
                .and_then(|variants| variants.get(variant_name))
                .ok_or_else(|| {
                    format!(
                        "@async-fn cannot resolve pattern variant '{variant_name}' for '{type_name}'"
                    )
                })?;
            if fields.len() != items.len() - 1 {
                return Err(format!(
                    "@async-fn enum pattern '{variant_name}' has {} fields, but the declaration has {}",
                    items.len() - 1,
                    fields.len()
                ));
            }
            for (field_pattern, field_type) in items[1..].iter().zip(fields) {
                collect_enum_pattern_bindings(field_pattern, field_type, environment, bindings)?;
            }
        }
        Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Char(_) | Expr::String(_) => {}
        _ => return Err("@async-fn #for initializer has an unsupported pattern".into()),
    }
    Ok(())
}

fn rename_pattern_binding(pattern: &mut Expr, from: &str, to: &str) {
    match pattern {
        Expr::Symbol(name) if name == from => *name = to.to_owned(),
        Expr::List(items) => {
            for item in items.iter_mut().skip(1) {
                rename_pattern_binding(item, from, to);
            }
        }
        _ => {}
    }
}

fn contains_loop_control(expression: &Expr) -> bool {
    match expression {
        Expr::List(items) => {
            matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#break" | "break" | "#continue" | "continue" | "#break-to" | "break-to" | "#continue-to" | "continue-to"))
                || items.iter().skip(1).any(contains_loop_control)
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            statements.iter().any(|statement| match statement {
                crate::Statement::Expr(value)
                | crate::Statement::Return(Some(value))
                | crate::Statement::BreakValue(value)
                | crate::Statement::BreakToValue { value, .. } => contains_loop_control(value),
                _ => false,
            })
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => contains_loop_control(expression),
        _ => false,
    }
}

/// Unlabelled transfers belong to the nearest loop. Named transfers remain
/// conservative here because they may explicitly target an enclosing loop.
fn contains_enclosing_loop_control(expression: &Expr) -> bool {
    fn named_transfer(expression: &Expr) -> bool {
        let Expr::List(items) = expression else {
            return false;
        };
        if matches!(items.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
        {
            return false;
        }
        matches!(items.first(), Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#break-to" | "break-to" | "#continue-to" | "continue-to"))
            || items.iter().skip(1).any(named_transfer)
    }
    let Expr::List(items) = expression else {
        return contains_loop_control(expression);
    };
    if matches!(items.first(), Some(Expr::Symbol(head))
        if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
    {
        return false;
    }
    if matches!(items.first(), Some(Expr::Symbol(head))
        if matches!(head.as_str(), "#loop" | "#while" | "#while-let" | "#for" | "#for-range"))
    {
        return named_transfer(expression);
    }
    matches!(items.first(), Some(Expr::Symbol(head))
        if matches!(head.as_str(), "#break" | "break" | "#continue" | "continue"
            | "#break-to" | "break-to" | "#continue-to" | "continue-to"))
        || items.iter().skip(1).any(contains_enclosing_loop_control)
}

fn exits(expression: &Expr) -> bool {
    let Expr::List(items) = expression else {
        return false;
    };
    match items.first() {
        Some(Expr::Symbol(head)) if matches!(head.as_str(), "#break" | "#continue" | "#return") => {
            true
        }
        Some(Expr::Symbol(head))
            if matches!(
                head.as_str(),
                "#let-else"
                    | "#while"
                    | "#while-let"
                    | "#for"
                    | "#for-range"
                    | "#loop"
                    | "#fn"
                    | "#quote"
                    | "#quasiquote"
            ) =>
        {
            false
        }
        _ => items.iter().skip(1).any(exits),
    }
}
/// Move an iteration's remaining statements into its fall-through branches.
/// Loop transfers then remain terminal even when written before a suspension.
/// Put implicit iteration fallthrough after each continuing branch, without
/// letting early continue, break, or return execute the rest of the body.
fn terminal_async_iteration_body(
    statements: &[Expr],
    source: &str,
    next_name: &mut usize,
) -> Result<Expr, String> {
    let mut body = vec![Expr::Symbol("#loop".into())];
    body.extend_from_slice(statements);
    body.push(Expr::List(vec![Expr::Symbol("#continue".into())]));
    let mut body = Expr::List(body);
    terminalize_async_iterations(&mut body, source, next_name)?;
    let Expr::List(mut body) = body else {
        unreachable!()
    };
    body[0] = Expr::Symbol("#block".into());
    Ok(Expr::List(body))
}

fn terminalize_async_iterations(
    expression: &mut Expr,
    source: &str,
    next_name: &mut usize,
) -> Result<(), String> {
    fn sequence(body: &[Expr], source: &str, next: &mut usize) -> Result<Vec<Expr>, String> {
        let Some(index) = body
            .iter()
            .take(body.len().saturating_sub(1))
            .position(exits)
        else {
            return Ok(body.to_vec());
        };
        let mut result = body[..index].to_vec();
        result.push(append(&body[index], &body[index + 1..], source, next)?);
        Ok(result)
    }
    fn scoped_branch(
        branch: &Expr,
        tail: &[Expr],
        source: &str,
        next: &mut usize,
    ) -> Result<Expr, String> {
        let mut branch = branch.clone();
        let mut locals = HashSet::new();
        collect_local_binding_names(&branch, &mut locals);
        let mut locals = locals.into_iter().collect::<Vec<_>>();
        locals.sort();
        let mut tail_values = HashSet::new();
        let mut tail_locals = HashSet::new();
        for statement in tail {
            collect_value_names(statement, &mut tail_values);
            collect_local_binding_names(statement, &mut tail_locals);
        }
        // The continuation cannot refer to a branch-local binding. Preserve
        // original names for ordinary global-shadowing checks; freshen only
        // when the continuation independently declares the same spelling.
        fn rename_declarations(expression: &mut Expr, from: &str, to: &str) {
            let Expr::List(items) = expression else {
                return;
            };
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "#quasiquote"))
            {
                return;
            }
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let" | "#let-mut" | "#let-else" | "#case" | "#if-let" | "#while-let"))
            {
                if let Some(pattern) = items.get_mut(1) {
                    rename_async_value(pattern, from, to);
                }
            }
            for item in items.iter_mut().skip(1) {
                rename_declarations(item, from, to);
            }
        }
        for local in locals {
            if tail_values.contains(&local) && !tail_locals.contains(&local) {
                return Err(format!("unknown value '{local}' outside its branch scope"));
            }
            if !tail_locals.contains(&local) {
                continue;
            }
            let fresh = fresh_async_name(source, next);
            rename_async_value(&mut branch, &local, &fresh);
            rename_declarations(&mut branch, &local, &fresh);
        }
        let mut statements = if let Some(block) = form(&branch, "#block") {
            block[1..].to_vec()
        } else {
            vec![branch]
        };
        statements.extend_from_slice(tail);
        Ok(Expr::List(
            std::iter::once(Expr::Symbol("#block".into()))
                .chain(sequence(&statements, source, next)?)
                .collect(),
        ))
    }
    fn append(
        expression: &Expr,
        tail: &[Expr],
        source: &str,
        next: &mut usize,
    ) -> Result<Expr, String> {
        if form(expression, "#break").is_some()
            || form(expression, "#continue").is_some()
            || form(expression, "#return").is_some()
        {
            return Ok(expression.clone());
        }
        if let Some(items) = form(expression, "#if") {
            if items.len() == 4 && !exits(&items[1]) {
                return Ok(Expr::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    scoped_branch(&items[2], tail, source, next)?,
                    scoped_branch(&items[3], tail, source, next)?,
                ]));
            }
        }
        if let Some(items) = form(expression, "#match") {
            if items.len() >= 3 && !exits(&items[1]) {
                let mut rewritten = items[..2].to_vec();
                for arm in &items[2..] {
                    let mut case = form(arm, "#case")
                        .ok_or_else(|| "@async-fn iteration match requires #case arms".to_owned())?
                        .to_vec();
                    let body_index = match case.len() {
                        3 => 2,
                        4 if form(&case[2], "#when").is_some() => 3,
                        _ => return Err("@async-fn iteration match has an invalid arm".into()),
                    };
                    let mut names = pattern_symbols(&case[1]).into_iter().collect::<Vec<_>>();
                    names.sort();
                    let mut tail_values = HashSet::new();
                    let mut tail_locals = HashSet::new();
                    for statement in tail {
                        collect_value_names(statement, &mut tail_values);
                        collect_local_binding_names(statement, &mut tail_locals);
                    }
                    for name in names {
                        if tail_values.contains(&name) && !tail_locals.contains(&name) {
                            return Err(format!(
                                "unknown value '{name}' outside its match arm scope"
                            ));
                        }
                        if !tail_locals.contains(&name) {
                            continue;
                        }
                        let fresh = fresh_async_name(source, next);
                        for part in &mut case[1..] {
                            rename_async_value(part, &name, &fresh);
                        }
                    }
                    case[body_index] = scoped_branch(&case[body_index], tail, source, next)?;
                    rewritten.push(Expr::List(case));
                }
                return Ok(Expr::List(rewritten));
            }
        }
        if form(expression, "#block").is_some() {
            return scoped_branch(expression, tail, source, next);
        }
        Err("@async-fn cannot yet terminalize a loop transfer inside this expression".into())
    }
    let Expr::List(items) = expression else {
        return Ok(());
    };
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#fn" | "#quote" | "#quasiquote"))
    {
        return Ok(());
    }
    let body_start = match items.first() {
        Some(Expr::Symbol(head)) => match head.as_str() {
            "#while" => Some(2),
            "#while-let" => Some(3),
            "#for" | "#for-range" => Some(4),
            "#loop" => Some(1),
            "#async-body" => Some(1),
            _ => None,
        },
        _ => None,
    };
    let function_body = matches!(items.first(), Some(Expr::Symbol(head)) if head == "#async-body");
    if !function_body {
        for item in items.iter_mut().skip(1) {
            terminalize_async_iterations(item, source, next_name)?;
        }
    }
    if let Some(start) = body_start.filter(|start| *start < items.len()) {
        let needed = if function_body {
            items[start..]
                .iter()
                .take(items.len() - start - 1)
                .any(|statement| has_await(statement) && exits(statement))
        } else {
            items[start..].iter().any(has_await)
        };
        if needed {
            let body = sequence(&items[start..], source, next_name)?;
            items.truncate(start);
            items.extend(body);
        }
    }
    Ok(())
}

/// Async loop lowering operates on the loop form itself. A label around an
/// awaited loop would otherwise be mistaken for an ordinary value-producing
/// form, causing await extraction to detach the label from its loop. Remove
/// that wrapper after translating transfers that target it to local loop
/// transfers. Transfers from nested loops cannot be translated this way: an
/// unlabelled transfer there would change its target.
fn lower_labeled_async_loop(statement: &mut Expr) -> Result<(), String> {
    if let Expr::List(items) = statement {
        if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote" | "#fn" | "fn"))
        {
            return Ok(());
        }
        let is_label = matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#label" | "label"));
        if !is_label {
            for item in items.iter_mut().skip(1) {
                lower_labeled_async_loop(item)?;
            }
            return Ok(());
        }
    }
    if let Expr::Block(statements) | Expr::Loop(statements) = statement {
        for statement in statements {
            lower_labeled_async_statement(statement)?;
        }
        return Ok(());
    }
    let (label, loop_expression) = match statement {
        Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#label" | "label")) =>
        {
            if items.len() != 3 {
                return Err("@async-fn #label requires a label and one loop statement".into());
            }
            let label = symbol(&items[1], "async loop label")?.to_owned();
            (label, items[2].clone())
        }
        Expr::Labeled { label, expression } => (label.clone(), *expression.clone()),
        _ => return Ok(()),
    };
    if !has_await(&loop_expression) {
        return Ok(());
    }
    if ![
        "#while",
        "while",
        "#while-let",
        "while-let",
        "#loop",
        "loop",
        "#for",
        "for",
        "#for-range",
        "for-range",
    ]
    .iter()
    .any(|keyword| form(&loop_expression, keyword).is_some())
    {
        return Err("@async-fn #label must wrap a loop when its body awaits".into());
    }
    let mut lowered = loop_expression;
    rewrite_labeled_async_transfers(&mut lowered, &label, true, false)?;
    *statement = lowered;
    Ok(())
}

fn lower_labeled_async_statement(statement: &mut crate::Statement) -> Result<(), String> {
    use crate::Statement as S;
    if let S::Labeled {
        label,
        statement: inner,
    } = statement
    {
        if statement_has_await(inner) {
            rewrite_labeled_loop_statement(inner, label)?;
            *statement = (**inner).clone();
            return Ok(());
        }
        return lower_labeled_async_statement(inner);
    }
    match statement {
        S::Let { value, .. }
        | S::Destructure { value, .. }
        | S::Assign { value, .. }
        | S::FieldAssign { value, .. }
        | S::TupleAssign { value, .. }
        | S::EnumPayloadAssign { value, .. }
        | S::BreakValue(value)
        | S::BreakToValue { value, .. }
        | S::Expr(value)
        | S::Return(Some(value)) => lower_labeled_async_loop(value),
        S::ArrayAssign { index, value, .. } => {
            lower_labeled_async_loop(index)?;
            lower_labeled_async_loop(value)
        }
        S::LetElse {
            value, else_body, ..
        } => {
            lower_labeled_async_loop(value)?;
            for statement in else_body {
                lower_labeled_async_statement(statement)?;
            }
            Ok(())
        }
        S::While { condition, body } => {
            lower_labeled_async_loop(condition)?;
            for statement in body {
                lower_labeled_async_statement(statement)?;
            }
            Ok(())
        }
        S::Loop { body } => {
            for statement in body {
                lower_labeled_async_statement(statement)?;
            }
            Ok(())
        }
        S::For {
            init,
            condition,
            step,
            body,
        } => {
            lower_labeled_async_statement(init)?;
            lower_labeled_async_loop(condition)?;
            lower_labeled_async_statement(step)?;
            for statement in body {
                lower_labeled_async_statement(statement)?;
            }
            Ok(())
        }
        S::Return(None) | S::Break | S::BreakTo(_) | S::Continue | S::ContinueTo(_) => Ok(()),
        S::Labeled { .. } => unreachable!("labeled statement handled above"),
    }
}

fn rewrite_labeled_loop_statement(
    statement: &mut crate::Statement,
    label: &str,
) -> Result<(), String> {
    use crate::Statement as S;
    let body = match statement {
        S::While { body, .. } | S::Loop { body } | S::For { body, .. } => body,
        _ => return Err("@async-fn #label must wrap a loop when its body awaits".into()),
    };
    for statement in body {
        rewrite_labeled_loop_body_statement(statement, label, false)?;
    }
    Ok(())
}

fn rewrite_labeled_loop_body_statement(
    statement: &mut crate::Statement,
    label: &str,
    nested_loop: bool,
) -> Result<(), String> {
    use crate::Statement as S;
    match statement {
        S::BreakTo(target) if target == label => {
            if nested_loop {
                return Err(format!(
                    "@async-fn cannot lower transfer to outer label '{label}' from a nested loop"
                ));
            }
            *statement = S::Break;
        }
        S::BreakToValue {
            label: target,
            value,
        } if target == label => {
            if nested_loop {
                return Err(format!(
                    "@async-fn cannot lower transfer to outer label '{label}' from a nested loop"
                ));
            }
            *statement = S::BreakValue(value.clone());
        }
        S::ContinueTo(target) if target == label => {
            if nested_loop {
                return Err(format!(
                    "@async-fn cannot lower transfer to outer label '{label}' from a nested loop"
                ));
            }
            *statement = S::Continue;
        }
        S::Labeled {
            label: nested_label,
            ..
        } if nested_label == label => return Ok(()),
        S::Expr(expression)
        | S::Let {
            value: expression, ..
        }
        | S::Destructure {
            value: expression, ..
        }
        | S::Assign {
            value: expression, ..
        }
        | S::FieldAssign {
            value: expression, ..
        }
        | S::TupleAssign {
            value: expression, ..
        }
        | S::EnumPayloadAssign {
            value: expression, ..
        }
        | S::BreakValue(expression)
        | S::BreakToValue {
            value: expression, ..
        }
        | S::Return(Some(expression)) => {
            rewrite_labeled_async_transfers(expression, label, false, nested_loop)?;
        }
        S::ArrayAssign { index, value, .. } => {
            rewrite_labeled_async_transfers(index, label, false, nested_loop)?;
            rewrite_labeled_async_transfers(value, label, false, nested_loop)?;
        }
        S::LetElse {
            value, else_body, ..
        } => {
            rewrite_labeled_async_transfers(value, label, false, nested_loop)?;
            for statement in else_body {
                rewrite_labeled_loop_body_statement(statement, label, nested_loop)?;
            }
        }
        S::While { body, .. } | S::Loop { body } | S::For { body, .. } => {
            for statement in body {
                rewrite_labeled_loop_body_statement(statement, label, true)?;
            }
        }
        S::Labeled { statement, .. } => {
            rewrite_labeled_loop_body_statement(statement, label, nested_loop)?;
        }
        _ => {}
    }
    Ok(())
}

fn rewrite_labeled_async_transfers(
    expression: &mut Expr,
    label: &str,
    root_loop: bool,
    nested_loop: bool,
) -> Result<(), String> {
    let Expr::List(items) = expression else {
        if let Expr::Labeled {
            label: nested_label,
            expression,
        } = expression
        {
            if nested_label == label {
                return Ok(());
            }
            return rewrite_labeled_async_transfers(expression, label, false, nested_loop);
        }
        return Ok(());
    };
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
    {
        return Ok(());
    }
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#label" | "label"))
        && items
            .get(1)
            .is_some_and(|name| matches!(name, Expr::Symbol(name) if name == label))
    {
        return Ok(());
    }
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#break-to" | "break-to" | "#continue-to" | "continue-to"))
        && items
            .get(1)
            .is_some_and(|name| matches!(name, Expr::Symbol(name) if name == label))
    {
        if nested_loop {
            return Err(format!(
                "@async-fn cannot lower transfer to outer label '{label}' from a nested loop"
            ));
        }
        let is_break = matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#break-to" | "break-to"));
        if (!is_break && items.len() != 2) || (is_break && !(2..=3).contains(&items.len())) {
            return Err(format!("@async-fn invalid transfer to label '{label}'"));
        }
        let mut replacement = vec![Expr::Symbol(
            if is_break { "#break" } else { "#continue" }.into(),
        )];
        if is_break && items.len() == 3 {
            replacement.push(items[2].clone());
        }
        *expression = Expr::List(replacement);
        return Ok(());
    }
    let is_loop = matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#while" | "while" | "#while-let" | "while-let" | "#loop" | "loop" | "#for" | "for" | "#for-range" | "for-range"));
    let nested_loop = nested_loop || (is_loop && !root_loop);
    for item in items.iter_mut().skip(1) {
        rewrite_labeled_async_transfers(item, label, false, nested_loop)?;
    }
    Ok(())
}

fn contains_return(expression: &Expr) -> bool {
    match expression {
        Expr::List(items) => {
            matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#return" | "#async-terminal-return"))
                || items.iter().skip(1).any(contains_return)
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            statements.iter().any(|statement| match statement {
                crate::Statement::Expr(value)
                | crate::Statement::Return(Some(value))
                | crate::Statement::BreakValue(value)
                | crate::Statement::BreakToValue { value, .. } => contains_return(value),
                _ => false,
            })
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => contains_return(expression),
        _ => false,
    }
}

fn lower_async_terminal_return_markers(expression: &mut Expr) -> Result<(), String> {
    if let Some(items) = form(expression, "#async-terminal-return") {
        if items.len() != 3 {
            return Err("@async-fn malformed terminal return marker".into());
        }
        *expression = Expr::List(vec![Expr::Symbol("#return".into()), items[2].clone()]);
        return Ok(());
    }
    match expression {
        Expr::List(items) => {
            for item in items.iter_mut().skip(1) {
                lower_async_terminal_return_markers(item)?;
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            for statement in statements {
                match statement {
                    crate::Statement::Expr(value)
                    | crate::Statement::Return(Some(value))
                    | crate::Statement::BreakValue(value)
                    | crate::Statement::BreakToValue { value, .. } => {
                        lower_async_terminal_return_markers(value)?
                    }
                    _ => {}
                }
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => lower_async_terminal_return_markers(expression)?,
        _ => {}
    }
    Ok(())
}

/// Resolve return signals introduced by loop lowering after source returns
/// have already been adapted. Only marked returns are wrapped here.
fn resolve_generated_async_returns(expression: &mut Expr, ready: &str) {
    let Expr::List(items) = expression else {
        return;
    };
    if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#async-terminal-return")
        && items.len() == 3
    {
        *expression = Expr::List(vec![
            Expr::Symbol("#return".into()),
            Expr::List(vec![Expr::Symbol(ready.into()), items[2].clone()]),
        ]);
        return;
    }
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "#quasiquote" | "#fn"))
    {
        return;
    }
    for item in items.iter_mut().skip(1) {
        resolve_generated_async_returns(item, ready);
    }
}

fn async_terminal_return_type(expression: &Expr) -> Option<Expr> {
    if let Some(items) = form(expression, "#async-terminal-return") {
        return (items.len() == 3).then(|| items[1].clone());
    }
    match expression {
        Expr::List(items) => items.iter().skip(1).find_map(async_terminal_return_type),
        Expr::Block(statements) | Expr::Loop(statements) => {
            statements.iter().find_map(|statement| match statement {
                crate::Statement::Expr(value)
                | crate::Statement::Return(Some(value))
                | crate::Statement::BreakValue(value)
                | crate::Statement::BreakToValue { value, .. } => async_terminal_return_type(value),
                _ => None,
            })
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => async_terminal_return_type(expression),
        _ => None,
    }
}

fn rewrite_while_let_terminal(expression: &mut Expr, stopped: &str) -> Result<bool, String> {
    if let Some(items) = form(expression, "#break") {
        if items.len() != 1 {
            return Err(
                "@async-fn awaited #while-let does not support value-bearing #break".into(),
            );
        }
        *expression = Expr::List(vec![
            Expr::Symbol("#block".into()),
            Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(stopped.into()),
                Expr::Symbol("true".into()),
            ]),
            Expr::List(Vec::new()),
        ]);
        return Ok(true);
    }
    if let Some(items) = form(expression, "#continue") {
        if items.len() != 1 {
            return Err("@async-fn awaited #while-let does not support labeled #continue".into());
        }
        *expression = Expr::List(vec![
            Expr::Symbol("#block".into()),
            Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(stopped.into()),
                Expr::Symbol("false".into()),
            ]),
            Expr::List(Vec::new()),
        ]);
        return Ok(true);
    }
    if let Some(items) = form(expression, "#if") {
        if items.len() != 4 {
            return Err("@async-fn awaited #while-let requires a complete terminal #if".into());
        }
        let mut transferred = false;
        for branch_index in [2, 3] {
            let branch = &mut expression_list_mut(expression)[branch_index];
            if contains_loop_control(branch) {
                transferred |= rewrite_while_let_terminal(branch, stopped)?;
            }
        }
        return Ok(transferred);
    }
    if let Some(items) = form(expression, "#match") {
        if items.len() < 3 {
            return Err("@async-fn awaited loop requires a match with at least one arm".into());
        }
        let arm_count = items.len();
        let mut transferred = false;
        for arm_index in 2..arm_count {
            let (body_index, guard_has_control, body_has_control) = {
                let case = form(&expression_list_mut(expression)[arm_index], "#case").ok_or_else(
                    || "@async-fn awaited loop requires valid terminal match arms".to_owned(),
                )?;
                let body_index = match case.len() {
                    3 => 2,
                    4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                    _ => {
                        return Err(
                            "@async-fn awaited loop requires valid terminal match arms".into()
                        )
                    }
                };
                (
                    body_index,
                    case[1..body_index].iter().any(contains_loop_control),
                    contains_loop_control(&case[body_index]),
                )
            };
            if guard_has_control {
                return Err("@async-fn awaited loop transfers cannot occur in match guards".into());
            }
            if body_has_control {
                let Expr::List(match_items) = expression else {
                    unreachable!()
                };
                let Expr::List(case_items) = &mut match_items[arm_index] else {
                    unreachable!()
                };
                let mut rewritten = case_items[body_index].clone();
                transferred |= rewrite_while_let_terminal(&mut rewritten, stopped)?;
                case_items[body_index] = Expr::List(vec![
                    Expr::Symbol("#block".into()),
                    rewritten,
                    Expr::List(Vec::new()),
                ]);
            }
        }
        return Ok(transferred);
    }
    if let Some(items) = form(expression, "#block") {
        if items.len() < 2 {
            return Ok(false);
        }
        if items[1..items.len() - 1].iter().any(contains_loop_control) {
            return Err("@async-fn awaited #while-let transfers must be terminal".into());
        }
        let last = items.len() - 1;
        return rewrite_while_let_terminal(&mut expression_list_mut(expression)[last], stopped);
    }
    if contains_loop_control(expression) {
        return Err(
            "@async-fn awaited loop only supports terminal #break/#continue, #if, or #match branches".into(),
        );
    }
    Ok(false)
}

/// Preserve a C-style for-loop step when its final body form transfers control.
/// A continue runs the step first, a break skips it, and ordinary branch exits
/// run it before the next awaited condition.
fn rewrite_for_terminal_control(expression: &mut Expr, step: &Expr) -> Result<bool, String> {
    if form(expression, "#return").is_some() || form(expression, "#async-terminal-return").is_some()
    {
        return Ok(true);
    }
    if let Some(items) = form(expression, "#break") {
        if items.len() != 1 {
            return Err("@async-fn awaited #for does not support value-bearing #break".into());
        }
        return Ok(true);
    }
    if let Some(items) = form(expression, "#continue") {
        if items.len() != 1 {
            return Err("@async-fn awaited #for does not support labeled #continue".into());
        }
        *expression = Expr::List(vec![
            Expr::Symbol("#block".into()),
            step.clone(),
            expression.clone(),
        ]);
        return Ok(true);
    }
    if let Some(items) = form(expression, "#block") {
        if items.len() < 2 {
            return Ok(false);
        }
        if items[1..items.len() - 1].iter().any(contains_loop_control) {
            return Err("@async-fn awaited #for transfers must be terminal statements".into());
        }
        let last = items.len() - 1;
        return rewrite_for_terminal_control(&mut expression_list_mut(expression)[last], step);
    }
    if let Some(items) = form(expression, "#if") {
        if items.len() != 4 {
            return Err("@async-fn awaited #for requires a complete terminal #if".into());
        }
        let mut has_transfer = false;
        for branch_index in [2, 3] {
            let branch = &mut expression_list_mut(expression)[branch_index];
            if contains_loop_control(branch) || contains_return(branch) {
                has_transfer |= rewrite_for_terminal_control(branch, step)?;
            } else {
                *branch = Expr::List(vec![
                    Expr::Symbol("#block".into()),
                    branch.clone(),
                    step.clone(),
                ]);
            }
        }
        return Ok(has_transfer);
    }
    if let Some(items) = form(expression, "#match") {
        if items.len() < 3 {
            return Err("@async-fn awaited #for requires a match with at least one arm".into());
        }
        let arm_count = items.len();
        let mut has_transfer = false;
        for arm_index in 2..arm_count {
            let (body_index, guard_has_control, body_has_control) = {
                let case = form(&expression_list_mut(expression)[arm_index], "#case").ok_or_else(
                    || "@async-fn awaited #for requires valid terminal match arms".to_owned(),
                )?;
                let body_index = match case.len() {
                    3 => 2,
                    4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                    _ => {
                        return Err(
                            "@async-fn awaited #for requires valid terminal match arms".into()
                        )
                    }
                };
                (
                    body_index,
                    case[1..body_index].iter().any(contains_loop_control),
                    contains_loop_control(&case[body_index]) || contains_return(&case[body_index]),
                )
            };
            if guard_has_control {
                return Err("@async-fn awaited #for transfers cannot occur in match guards".into());
            }
            let Expr::List(match_items) = expression else {
                unreachable!()
            };
            let Expr::List(case_items) = &mut match_items[arm_index] else {
                unreachable!()
            };
            if body_has_control {
                has_transfer |= rewrite_for_terminal_control(&mut case_items[body_index], step)?;
            } else {
                case_items[body_index] = Expr::List(vec![
                    Expr::Symbol("#block".into()),
                    case_items[body_index].clone(),
                    step.clone(),
                ]);
            }
        }
        return Ok(has_transfer);
    }
    if contains_loop_control(expression) {
        return Err(
            "@async-fn awaited #for only supports terminal #break/#continue, #if, or #match branches".into(),
        );
    }
    *expression = Expr::List(vec![
        Expr::Symbol("#block".into()),
        expression.clone(),
        step.clone(),
    ]);
    Ok(false)
}

/// Turn terminal body transfers in a synthesized awaited for-iteration into
/// state. The awaited step is scheduled after the body, so continue is simply
/// the end of the body while break sets a flag that suppresses the step.
fn rewrite_async_for_return_marker(expression: &mut Expr, stopped: &str) -> Result<bool, String> {
    if let Some(items) = form(expression, "#async-for-return") {
        if items.len() != 5 {
            return Err("@async-fn malformed internal for-return transfer".into());
        }
        let mut replacement = vec![Expr::Symbol("#block".into())];
        if matches!(items[4], Expr::Symbol(ref value) if value == "true") {
            replacement.push(Expr::List(vec![
                Expr::Symbol("#forget".into()),
                items[1].clone(),
            ]));
        }
        replacement.extend([
            Expr::List(vec![
                Expr::Symbol("#set".into()),
                items[1].clone(),
                Expr::List(vec![items[2].clone(), items[3].clone()]),
            ]),
            Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(stopped.into()),
                Expr::Symbol("true".into()),
            ]),
            Expr::List(Vec::new()),
        ]);
        *expression = Expr::List(replacement);
        return Ok(true);
    }
    let Expr::List(items) = expression else {
        return Ok(false);
    };
    let mut found = false;
    for item in items.iter_mut().skip(1) {
        found |= rewrite_async_for_return_marker(item, stopped)?;
    }
    Ok(found)
}

fn rewrite_async_for_body_transfer(expression: &mut Expr, stopped: &str) -> Result<bool, String> {
    if let Some(items) = form(expression, "#break") {
        if items.len() != 1 {
            return Err("@async-fn awaited #for does not support value-bearing #break".into());
        }
        *expression = Expr::List(vec![
            Expr::Symbol("#block".into()),
            Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(stopped.into()),
                Expr::Symbol("true".into()),
            ]),
            Expr::List(Vec::new()),
        ]);
        return Ok(true);
    }
    if let Some(items) = form(expression, "#continue") {
        if items.len() != 1 {
            return Err("@async-fn awaited #for does not support labeled #continue".into());
        }
        *expression = Expr::List(Vec::new());
        return Ok(false);
    }
    if let Some(items) = form(expression, "#block") {
        if items.len() < 2 {
            return Ok(false);
        }
        if items[1..items.len() - 1].iter().any(contains_loop_control) {
            return Err("@async-fn awaited #for transfers must be terminal statements".into());
        }
        let last = items.len() - 1;
        return rewrite_async_for_body_transfer(
            &mut expression_list_mut(expression)[last],
            stopped,
        );
    }
    if let Some(items) = form(expression, "#if").map(<[Expr]>::to_vec) {
        if items.len() != 4 {
            return Err("@async-fn awaited #for requires a complete terminal #if".into());
        }
        let mut has_break = false;
        for branch in [2, 3] {
            if contains_loop_control(&items[branch]) {
                has_break |= rewrite_async_for_body_transfer(
                    &mut expression_list_mut(expression)[branch],
                    stopped,
                )?;
            }
        }
        return Ok(has_break);
    }
    if let Some(items) = form(expression, "#match").map(<[Expr]>::to_vec) {
        if items.len() < 3 {
            return Err("@async-fn awaited #for requires a match with at least one arm".into());
        }
        let arm_count = items.len();
        let mut has_break = false;
        for arm_index in 2..arm_count {
            let (body_index, guard_has_control, body_has_control) = {
                let case = form(&expression_list_mut(expression)[arm_index], "#case").ok_or_else(
                    || "@async-fn awaited #for requires valid terminal match arms".to_owned(),
                )?;
                let body_index = match case.len() {
                    3 => 2,
                    4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                    _ => {
                        return Err(
                            "@async-fn awaited #for requires valid terminal match arms".into()
                        )
                    }
                };
                (
                    body_index,
                    case[1..body_index].iter().any(contains_loop_control),
                    contains_loop_control(&case[body_index]),
                )
            };
            if guard_has_control {
                return Err("@async-fn awaited #for transfers cannot occur in match guards".into());
            }
            if body_has_control {
                let Expr::List(match_items) = expression else {
                    unreachable!()
                };
                let Expr::List(case_items) = &mut match_items[arm_index] else {
                    unreachable!()
                };
                has_break |= rewrite_async_for_body_transfer(&mut case_items[body_index], stopped)?;
            }
        }
        return Ok(has_break);
    }
    if contains_loop_control(expression) {
        return Err(
            "@async-fn awaited #for only supports terminal #break/#continue, #if, or #match branches".into(),
        );
    }
    Ok(false)
}

/// Rewrite a terminal loop transfer after an await into state carried by the
/// generated while loop. Only direct transfers and terminal #if branches are
/// accepted; more complex control flow remains explicit and diagnosable.
fn rewrite_terminal_loop_control(expression: &mut Expr, done: &str) -> Result<bool, String> {
    if let Some(items) = form(expression, "#break") {
        if items.len() != 1 {
            return Err("@async-fn awaited #loop does not support value-bearing #break".into());
        }
        *expression = Expr::List(vec![
            Expr::Symbol("#block".into()),
            Expr::List(vec![
                Expr::Symbol("#set".into()),
                Expr::Symbol(done.into()),
                Expr::Symbol("true".into()),
            ]),
            Expr::List(Vec::new()),
        ]);
        return Ok(true);
    }
    if let Some(items) = form(expression, "#continue") {
        if items.len() != 1 {
            return Err("@async-fn awaited #loop does not support labeled #continue".into());
        }
        *expression = Expr::List(Vec::new());
        return Ok(true);
    }
    if let Some(items) = form(expression, "#block") {
        if items.len() < 2 {
            return Ok(false);
        }
        if items[1..items.len() - 1].iter().any(contains_loop_control) {
            return Err("@async-fn awaited #loop transfers must be terminal statements".into());
        }
        let last = items.len() - 1;
        return rewrite_terminal_loop_control(&mut expression_list_mut(expression)[last], done);
    }
    if let Some(items) = form(expression, "#if") {
        if items.len() != 4 {
            return Err("@async-fn awaited #loop requires a complete terminal #if".into());
        }
        let then_control =
            rewrite_terminal_loop_control(&mut expression_list_mut(expression)[2], done)?;
        let else_control =
            rewrite_terminal_loop_control(&mut expression_list_mut(expression)[3], done)?;
        return Ok(then_control || else_control);
    }
    if let Some(items) = form(expression, "#match") {
        if items.len() < 3 {
            return Err("@async-fn awaited #loop requires a match with at least one arm".into());
        }
        let arm_count = items.len();
        let mut transferred = false;
        for arm_index in 2..arm_count {
            let (body_index, guard_has_control, body_has_control) = {
                let case = form(&expression_list_mut(expression)[arm_index], "#case").ok_or_else(
                    || "@async-fn awaited #loop requires valid terminal match arms".to_owned(),
                )?;
                let body_index = match case.len() {
                    3 => 2,
                    4 if form(&case[2], "#when").is_some_and(|guard| guard.len() == 2) => 3,
                    _ => {
                        return Err(
                            "@async-fn awaited #loop requires valid terminal match arms".into()
                        )
                    }
                };
                (
                    body_index,
                    case[1..body_index].iter().any(contains_loop_control),
                    contains_loop_control(&case[body_index]),
                )
            };
            if guard_has_control {
                return Err(
                    "@async-fn awaited #loop transfers cannot occur in match guards".into(),
                );
            }
            if body_has_control {
                let Expr::List(match_items) = expression else {
                    unreachable!()
                };
                let Expr::List(case_items) = &mut match_items[arm_index] else {
                    unreachable!()
                };
                transferred |= rewrite_terminal_loop_control(&mut case_items[body_index], done)?;
            }
        }
        return Ok(transferred);
    }
    if contains_loop_control(expression) {
        return Err(
            "@async-fn awaited #loop only supports terminal #break/#continue, #if, or #match branches".into(),
        );
    }
    Ok(false)
}

fn expression_list_mut(expression: &mut Expr) -> &mut Vec<Expr> {
    let Expr::List(items) = expression else {
        unreachable!("called only for a list form")
    };
    items
}

fn lower_async_loop(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &Expr,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>)>, String> {
    lower_async_loop_with_transfers(
        statement,
        known,
        known_order,
        &[],
        following,
        return_value,
        None,
        source,
        next_name,
        waker,
    )
}

fn lower_async_loop_with_transfers(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    transfers: &[LoopReferenceTransfer],
    following: &[Expr],
    return_value: &Expr,
    return_type: Option<&Expr>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String, Vec<(String, Binding)>)>, String> {
    if !has_await(statement) {
        return Ok(None);
    }
    let Some(items) = form(statement, "#loop") else {
        return Ok(None);
    };
    if items.len() < 2 {
        return Err("@async-fn awaited #loop requires a body".into());
    }
    // A value-bearing loop is an expression, not the unit-valued loop handled
    // by this statement-level state machine. Let the general expression
    // adapter lower Copy results; reject a discarded linear result here,
    // before it can be hidden in the generated adapter's output state.
    if let Some((_, result_type)) = async_loop_break_value(statement, known) {
        let result_type = parse_type(Some(&normalize_keywords(result_type)))?;
        if !async_task_capture_is_copy(&result_type) {
            return Err(
                "@async-fn cannot discard a non-Copy result from an awaited #loop; bind it and consume it explicitly".into(),
            );
        }
        return Ok(None);
    }
    let done = fresh_async_name(source, next_name);
    let mut body = items[1..].to_vec();
    let Some(last) = body.last_mut() else {
        return Err("@async-fn awaited #loop requires a body".into());
    };
    rewrite_terminal_loop_control(last, &done)?;
    if body[..body.len() - 1]
        .iter()
        .any(contains_enclosing_loop_control)
    {
        return Err("@async-fn awaited #loop control transfers must follow the await".into());
    }
    let condition = Expr::List(vec![
        Expr::Symbol("#bool.==".into()),
        Expr::Symbol(done.clone()),
        Expr::Symbol("false".into()),
    ]);
    let mut while_items = vec![Expr::Symbol("#while".into()), condition];
    while_items.extend(body);
    let lowered_loop = Expr::List(while_items);
    let mut loop_known = known.clone();
    loop_known.insert(
        done.clone(),
        Binding {
            name: done.clone(),
            ty: "bool".into(),
            mutable: true,
        },
    );
    let mut loop_order = known_order.to_vec();
    loop_order.push(done.clone());
    let Some((mut replacement, helper, renames)) = lower_async_while_with_transfers(
        &lowered_loop,
        &loop_known,
        &loop_order,
        transfers,
        &[],
        following,
        return_value,
        return_type,
        source,
        next_name,
        waker,
    )?
    else {
        return Err("@async-fn failed to lower awaited #loop".into());
    };
    replacement.insert(
        0,
        Expr::List(vec![
            Expr::Symbol("#let-mut".into()),
            Expr::Symbol(done),
            Expr::Symbol("bool".into()),
            Expr::Symbol("false".into()),
        ]),
    );
    Ok(Some((replacement, helper, renames)))
}

fn mutable_assignment_target(expr: &Expr) -> Option<&str> {
    let Expr::List(items) = expr else {
        return None;
    };
    if !matches!(
        items.first(),
        Some(Expr::Symbol(head))
            if matches!(head.as_str(), "#set" | "set" | "#set-field" | "set-field" | "#set-index" | "set-index" | "#pin-set-field" | "pin-set-field")
    ) {
        return None;
    }
    match items.get(1) {
        Some(Expr::Symbol(name)) => Some(name),
        _ => None,
    }
}

fn is_control_flow_statement(expr: &Expr) -> bool {
    ["#if", "#match", "#block"]
        .iter()
        .any(|head| form(expr, head).is_some())
}

fn binding(expr: &Expr, context: &str) -> Result<Binding, String> {
    let items = form(expr, "#let")
        .or_else(|| form(expr, "#let-mut"))
        .or_else(|| form(expr, "let"))
        .or_else(|| form(expr, "let-mut"))
        .ok_or_else(|| {
            format!(
                "@async-fn {context} supports only explicit #let or #let-mut bindings: {expr:?}"
            )
        })?;
    if items.len() != 4 {
        return Err(format!(
            "@async-fn {context} requires (#let name Type value)"
        ));
    }
    let name = symbol(&items[1], "binding name")?.to_owned();
    parse_type(Some(&normalize_keywords(items[2].clone())))?;
    Ok(Binding {
        name,
        ty: expression_source(&items[2])?,
        mutable: matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let-mut" | "let-mut")),
    })
}

/// Resolve every leaf of a local pattern from its explicit declaration.
/// Preserve pattern order, mutability, and aliases; no body-use inference.
fn declared_local_bindings(
    expression: &Expr,
    environment: &AsyncTypeEnvironment,
) -> Result<Option<Vec<Binding>>, String> {
    let Some(items) = form(expression, "#let")
        .or_else(|| form(expression, "#let-mut"))
        .or_else(|| form(expression, "let"))
        .or_else(|| form(expression, "let-mut"))
        .or_else(|| form(expression, "#let-else"))
        .or_else(|| form(expression, "let-else"))
    else {
        return Ok(None);
    };
    let let_else = matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let-else" | "let-else"));
    if items.len() != if let_else { 5 } else { 4 } {
        return Err("@async-fn local declaration requires a pattern, type, and value".into());
    }
    if !let_else && matches!(&items[1], Expr::Symbol(_)) {
        return binding(expression, "local declaration").map(|binding| Some(vec![binding]));
    }
    parse_type(Some(&normalize_keywords(items[2].clone())))?;
    let ty = expression_source(&items[2])?;
    let mut fields = Vec::new();
    collect_enum_pattern_bindings(&items[1], &ty, environment, &mut fields)?;
    let mutable = matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let-mut" | "let-mut"));
    let mut seen = HashSet::new();
    let mut bindings = Vec::with_capacity(fields.len());
    for (name, ty) in fields {
        if !seen.insert(name.clone()) {
            return Err(format!("@async-fn duplicate pattern binding '{name}'"));
        }
        bindings.push(Binding { name, ty, mutable });
    }
    Ok(Some(bindings))
}

fn current_local_bindings(expression: &Expr) -> Result<Option<Vec<Binding>>, String> {
    ASYNC_TYPE_ENVIRONMENTS.with(|stack| {
        let stack = stack.borrow();
        match stack.last() {
            Some(environment) => declared_local_bindings(expression, environment),
            None => declared_local_bindings(expression, &AsyncTypeEnvironment::default()),
        }
    })
}

fn pinned_self_references(
    params: &[Binding],
    body: &[Expr],
) -> Result<Vec<PinnedSelfReference>, String> {
    let mut references = Vec::new();
    for (index, statement) in body.iter().enumerate() {
        let Some(items) = form(statement, "#let") else {
            continue;
        };
        if items.len() != 4 {
            continue;
        }
        let Type::PinnedReference { mutable, .. } =
            parse_type(Some(&normalize_keywords(items[2].clone())))?
        else {
            continue;
        };
        let Some((owner_name, projection)) = pinned_self_reference_target(&items[3]) else {
            continue;
        };
        let (owner, owner_initializer) = if let Some(parameter) =
            params.iter().find(|parameter| parameter.name == owner_name)
        {
            (parameter.clone(), None)
        } else {
            let Some((owner_index, owner_statement)) =
                body[..index]
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|(_, statement)| {
                        form(statement, "#let")
                            .or_else(|| form(statement, "#let-mut"))
                            .is_some_and(|items| {
                                items.get(1).is_some_and(|name| {
                                matches!(name, Expr::Symbol(name) if name == &owner_name)
                            })
                            })
                    })
            else {
                continue;
            };
            let local = binding(owner_statement, "pinned self-reference owner")?;
            if local.mutable {
                // Keep mutable stack locals on the ordinary borrow-checking
                // path so their more specific escaping-pin diagnostic wins.
                continue;
            }
            let owner_binding = form(owner_statement, "#let").unwrap();
            let initializer = expression_source(&owner_binding[3])?;
            if has_await(&owner_binding[3]) {
                return Err(format!(
                    "@async-fn-pinned self-reference owner '{}' cannot be initialized by #await",
                    local.name
                ));
            }
            if owner_index != 0 {
                return Err(format!(
                    "@async-fn-pinned local self-reference owner '{}' must be the first function statement",
                    local.name
                ));
            }
            (local, Some(initializer))
        };
        if owner.mutable {
            return Err(format!(
                "@async-fn-pinned self-reference owner '{}' must be an immutable parameter",
                owner.name
            ));
        }
        let local = binding(statement, "pinned self-reference")?;
        if local.mutable {
            return Err(format!(
                "@async-fn-pinned self-reference '{}' must use immutable #let",
                local.name
            ));
        }
        references.push(PinnedSelfReference {
            target_ty: pinned_reference_target_source(&items[2])?,
            binding: local,
            owner,
            owner_initializer,
            projection,
            mutable,
            helper_parameter: String::new(),
            source_index: index,
        });
    }

    Ok(references)
}

fn pinned_projection_target(
    expression: &Expr,
    projection: &mut Vec<PinnedProjection>,
) -> Option<String> {
    fn visit(expression: &Expr, projection: &mut Vec<PinnedProjection>) -> Option<String> {
        match expression {
            Expr::Symbol(name) => Some(name.clone()),
            Expr::List(items)
                if items.len() == 3
                    && matches!(items.first(), Some(Expr::Symbol(head)) if head == "#get") =>
            {
                let Expr::Symbol(field) = &items[2] else {
                    return None;
                };
                let owner = visit(&items[1], projection)?;
                projection.push(PinnedProjection::Field(field.clone()));
                Some(owner)
            }
            Expr::List(items)
                if items.len() == 4
                    && matches!(items.first(), Some(Expr::Symbol(head)) if head == "#pin-get-payload") =>
            {
                let borrow = form(&items[1], "#pin-borrow")
                    .or_else(|| form(&items[1], "#pin-borrow-mut"))?;
                if borrow.len() != 2 {
                    return None;
                }
                let owner = visit(&borrow[1], projection)?;
                let Expr::Symbol(variant) = &items[2] else {
                    return None;
                };
                let index = match &items[3] {
                    Expr::Integer(index) if *index >= 0 => usize::try_from(*index).ok()?,
                    Expr::UnsignedInteger(index) => usize::try_from(*index).ok()?,
                    _ => return None,
                };
                projection.push(PinnedProjection::EnumPayload {
                    variant: variant.clone(),
                    index,
                });
                Some(owner)
            }
            _ => None,
        }
    }

    visit(expression, projection)
}

fn pinned_self_reference_target(expression: &Expr) -> Option<(String, Vec<PinnedProjection>)> {
    let target = if let Some(borrow) =
        form(expression, "#pin-borrow").or_else(|| form(expression, "#pin-borrow-mut"))
    {
        if borrow.len() != 2 {
            return None;
        }
        &borrow[1]
    } else {
        expression
    };
    let mut projection = Vec::new();
    let owner = pinned_projection_target(target, &mut projection)?;
    Some((owner, projection))
}

fn pinned_reference_target_source(type_expression: &Expr) -> Result<String, String> {
    let Expr::List(items) = type_expression else {
        return Err("pinned reference binding requires (#pin-ref Type)".into());
    };
    if items.len() != 2
        || !matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#pin-ref" | "#pin-ref-mut"))
    {
        return Err("pinned reference binding requires (#pin-ref Type)".into());
    }
    expression_source(&items[1])
}

fn rewrite_pinned_self_references(expression: &mut Expr, references: &[PinnedSelfReference]) {
    let replacement = match expression {
        _ => pinned_self_reference_target(expression).and_then(|(owner, projection)| {
            references
                .iter()
                .find(|reference| {
                    reference.owner.name == owner && reference.projection == projection
                })
                .map(|reference| reference.helper_parameter.clone())
        }),
    };
    if let Some(replacement) = replacement {
        *expression = Expr::Symbol(replacement);
        return;
    }
    if let Expr::List(items) = expression {
        if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
        {
            return;
        }
        for item in items {
            rewrite_pinned_self_references(item, references);
        }
    }
}

fn rename_symbol(expression: &mut Expr, source: &str, replacement: &str) {
    match expression {
        Expr::Symbol(name) if name == source => *name = replacement.to_owned(),
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#quote" | "quote" | "#quasiquote" | "quasiquote"))
            {
                return;
            }
            for item in items {
                rename_symbol(item, source, replacement);
            }
        }
        Expr::Block(items) | Expr::Loop(items) => {
            for item in items {
                rename_statement_symbols(item, source, replacement);
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => rename_symbol(expression, source, replacement),
        _ => {}
    }
}

fn rename_statement_symbols(statement: &mut crate::Statement, source: &str, replacement: &str) {
    use crate::Statement;
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Expr(value) => rename_symbol(value, source, replacement),
        Statement::LetElse {
            value, else_body, ..
        } => {
            rename_symbol(value, source, replacement);
            for statement in else_body {
                rename_statement_symbols(statement, source, replacement);
            }
        }
        Statement::ArrayAssign { index, value, .. } => {
            rename_symbol(index, source, replacement);
            rename_symbol(value, source, replacement);
        }
        Statement::While { condition, body } => {
            rename_symbol(condition, source, replacement);
            for statement in body {
                rename_statement_symbols(statement, source, replacement);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                rename_statement_symbols(statement, source, replacement);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            rename_statement_symbols(init, source, replacement);
            rename_symbol(condition, source, replacement);
            rename_statement_symbols(step, source, replacement);
            for statement in body {
                rename_statement_symbols(statement, source, replacement);
            }
        }
        Statement::Labeled { statement, .. } => {
            rename_statement_symbols(statement, source, replacement)
        }
        Statement::Return(Some(value)) => rename_symbol(value, source, replacement),
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
}

fn self_reference_live_after_await(reference: &PinnedSelfReference, body: &[Expr]) -> bool {
    let mut crossed_await = false;
    for statement in body.iter().skip(reference.source_index + 1) {
        if crossed_await {
            let mut used = HashSet::new();
            collect_value_names(statement, &mut used);
            if used.contains(&reference.binding.name) {
                return true;
            }
        }
        crossed_await |= has_await(statement);
    }
    false
}

fn parameters(expr: &Expr) -> Result<Vec<Binding>, String> {
    list(expr, "function parameters")?
        .iter()
        .map(|parameter| {
            let items = list(parameter, "function parameter")?;
            let mutable = matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#mut" | "mut"));
            let (name_index, type_index) = if mutable { (1, 2) } else { (0, 1) };
            if items.len() != type_index + 1 {
                return Err("@async-fn parameters require (name Type) or (#mut name Type)".into());
            }
            let name = symbol(&items[name_index], "parameter name")?.to_owned();
            parse_type(Some(&normalize_keywords(items[type_index].clone())))?;
            Ok(Binding {
                name,
                ty: expression_source(&items[type_index])?,
                mutable,
            })
        })
        .collect()
}

fn signature(bindings: &[Binding]) -> String {
    bindings.iter().map(parameter).collect::<Vec<_>>().join(" ")
}

fn parameter(binding: &Binding) -> String {
    if binding.mutable {
        format!("(#mut {} {})", binding.name, binding.ty)
    } else {
        format!("({} {})", binding.name, binding.ty)
    }
}

fn arguments(bindings: &[Binding]) -> String {
    bindings
        .iter()
        .map(|binding| binding.name.as_str())
        .collect::<Vec<_>>()
        .join(" ")
}

fn types(bindings: &[Binding]) -> String {
    bindings
        .iter()
        .map(|binding| binding.ty.as_str())
        .collect::<Vec<_>>()
        .join(" ")
}

fn named_arguments(bindings: &[Binding]) -> String {
    bindings
        .iter()
        .map(|binding| format!(": {} {}", binding.name, binding.name))
        .collect::<Vec<_>>()
        .join(" ")
}

pub(crate) fn generated_source(invocation: &Expr) -> Result<String, String> {
    // Nested iteration/branch tasks still call ordinary declared functions.
    // Retain their explicit signature metadata while sequencing arguments;
    // only standalone invocations start with an empty environment.
    let environment =
        ASYNC_TYPE_ENVIRONMENTS.with(|stack| stack.borrow().last().cloned().unwrap_or_default());
    with_async_type_environment(&environment, || {
        generated_source_with_capture_selection(invocation, CaptureSelection::Syntax, &environment)
    })
}

pub(crate) fn generated_source_with_environment(
    invocation: &Expr,
    captures: Option<&HashMap<usize, HashSet<String>>>,
    copy_types: &HashSet<String>,
    type_environment: &AsyncTypeEnvironment,
) -> Result<String, String> {
    with_async_type_environment(type_environment, || {
        with_named_copy_types(copy_types, || match captures {
            Some(captures) => generated_source_with_capture_selection(
                invocation,
                CaptureSelection::Typed(captures),
                type_environment,
            ),
            None => generated_source_with_capture_selection(
                invocation,
                CaptureSelection::Syntax,
                type_environment,
            ),
        })
    })
}

enum CaptureSelection<'a> {
    Syntax,
    Typed(&'a HashMap<usize, HashSet<String>>),
}

struct AsyncCancelConfig {
    function: String,
    handlers: HashMap<String, String>,
}

struct AsyncCancelState {
    variant: String,
    fields: Vec<(String, String)>,
}

fn parse_async_cancel_config(expression: &Expr) -> Result<AsyncCancelConfig, String> {
    let config = list(expression, "async cancellation configuration")?;
    if config.len() != 2 {
        return Err(
            "@async-fn :cancel requires (cancel-function ((State-variant handler) ...))".into(),
        );
    }
    let function = symbol(&config[0], "cancellation function name")?.to_owned();
    let entries = list(&config[1], "async cancellation handlers")?;
    let mut handlers = HashMap::new();
    for entry in entries {
        let entry = list(entry, "async cancellation handler")?;
        if entry.len() != 2 {
            return Err("async cancellation handlers must be (State-variant handler)".into());
        }
        let variant = symbol(&entry[0], "cancellation state variant")?.to_owned();
        let handler = symbol(&entry[1], "cancellation handler function")?.to_owned();
        if handlers.insert(variant.clone(), handler).is_some() {
            return Err(format!(
                "async cancellation state '{variant}' is listed more than once"
            ));
        }
    }
    Ok(AsyncCancelConfig { function, handlers })
}

fn async_cancel_function(
    config: &AsyncCancelConfig,
    state_type: &str,
    states: &[AsyncCancelState],
    done_variant: Option<&str>,
) -> Result<String, String> {
    let expected = states
        .iter()
        .map(|state| state.variant.as_str())
        .collect::<HashSet<_>>();
    for variant in config.handlers.keys() {
        if !expected.contains(variant.as_str()) {
            return Err(format!(
                "async cancellation handler refers to unknown state '{variant}'"
            ));
        }
    }
    for state in states {
        if !config.handlers.contains_key(&state.variant) {
            return Err(format!(
                "async cancellation requires a handler for state '{}'",
                state.variant
            ));
        }
    }

    let mut cases = Vec::with_capacity(states.len() + done_variant.is_some() as usize);
    for (state_index, state) in states.iter().enumerate() {
        let handler = &config.handlers[&state.variant];
        let bindings = (0..state.fields.len())
            .map(|field_index| format!("lim.async.cancel.{state_index}.{field_index}"))
            .collect::<Vec<_>>();
        let pattern = if bindings.is_empty() {
            state.variant.clone()
        } else {
            format!("({} {})", state.variant, bindings.join(" "))
        };
        let argument = match state.fields.as_slice() {
            [] => "()".to_owned(),
            [(_, _)] => bindings[0].clone(),
            fields => format!(
                "(#tuple (#tuple {}) {})",
                fields
                    .iter()
                    .map(|(_, ty)| ty.as_str())
                    .collect::<Vec<_>>()
                    .join(" "),
                bindings.join(" ")
            ),
        };
        cases.push(format!(
            "(#case {pattern} (#call {handler} (: task {argument})))"
        ));
    }
    if let Some(done_variant) = done_variant {
        cases.push(format!("(#case {done_variant} ())"));
    }
    Ok(format!(
        "(#fn {} ((task {})) ()\n  (#return (#match task {})))",
        config.function,
        state_type,
        cases.join(" ")
    ))
}

fn generated_source_with_capture_selection(
    invocation: &Expr,
    capture_selection: CaptureSelection<'_>,
    type_environment: &AsyncTypeEnvironment,
) -> Result<String, String> {
    let invocation = list(invocation, "invocation")?;
    let pinned =
        matches!(&invocation.get(1), Some(Expr::Symbol(name)) if name == "async-fn-pinned");
    let generator_name = if pinned {
        "@async-fn-pinned"
    } else {
        "@async-fn"
    };
    if !(invocation.len() == 5 || invocation.len() == 6)
        || !matches!(invocation[0], Expr::At)
        || !matches!(&invocation[1], Expr::Symbol(name) if name == "async-fn" || name == "async-fn-pinned")
    {
        return Err(format!("{generator_name} requires (@{} (: names (Frame Poll Pending Ready poll) : waker Waker : function (#fn name ((arg Type) ...) Result ...) : cancel (cancel-function ((State-variant handler) ...))))", generator_name.trim_start_matches('@')).into());
    }
    let cancel_config = invocation
        .get(5)
        .map(parse_async_cancel_config)
        .transpose()?;
    let names = list(&invocation[2], "generated names")?;
    if names.len() != 5 {
        return Err("@async-fn names must be (Frame Poll Pending Ready poll)".into());
    }
    let names = names
        .iter()
        .map(|name| symbol(name, "generated name").map(str::to_owned))
        .collect::<Result<Vec<_>, _>>()?;
    if names.iter().collect::<HashSet<_>>().len() != names.len() {
        return Err("@async-fn generated names must be distinct".into());
    }
    let [frame, public_poll_result, public_pending, public_ready, public_poll] = names.as_slice()
    else {
        unreachable!()
    };
    let frame = frame.clone();
    let frame_state = if pinned {
        format!("{frame}-state")
    } else {
        frame.clone()
    };
    let mut poll_result = public_poll_result.clone();
    let mut pending = public_pending.clone();
    let mut ready = public_ready.clone();
    let mut poll = public_poll.clone();
    if pinned {
        poll_result = format!("{frame}-move-poll-result");
        pending = format!("{frame}-move-pending");
        ready = format!("{frame}-move-ready");
        poll = format!("{public_poll}-move");
    }
    let waker = expression_source(&invocation[3])?;
    parse_type(Some(&normalize_keywords(invocation[3].clone())))?;
    let function = form(&invocation[4], "#fn")
        .ok_or_else(|| "@async-fn last argument must be a #fn declaration".to_owned())?;
    crate::validate_async_function_shadowing(&invocation[4])?;
    if function.len() < 5 {
        return Err("@async-fn #fn requires a name, parameters, result type, and body".into());
    }
    let start = symbol(&function[1], "function name")?;
    if start == public_poll || names.iter().any(|name| name == start) {
        return Err("@async-fn start function must differ from generated names".into());
    }
    let cancel = format!("{public_poll}-cancel");
    let params = parameters(&function[2])?;
    let result = expression_source(&function[3])?;
    parse_type(Some(&normalize_keywords(function[3].clone())))?;
    let mut known = HashMap::new();
    for parameter in &params {
        if known
            .insert(
                parameter.name.clone(),
                Binding {
                    name: parameter.name.clone(),
                    ty: parameter.ty.clone(),
                    mutable: parameter.mutable,
                },
            )
            .is_some()
        {
            return Err(format!("@async-fn duplicate binding '{}'", parameter.name));
        }
    }
    let mut known_order = params
        .iter()
        .map(|parameter| parameter.name.clone())
        .collect::<Vec<_>>();
    let source = expression_source(&invocation[4])?;
    let mut next_nested_await = 0;
    let normalized_body = if function[4..]
        .iter()
        .take(function[4..].len().saturating_sub(1))
        .any(|statement| has_await(statement) && exits(statement))
    {
        let mut normalized_body = Expr::List(
            std::iter::once(Expr::Symbol("#async-body".into()))
                .chain(function[4..].iter().cloned())
                .collect(),
        );
        terminalize_async_iterations(&mut normalized_body, &source, &mut next_nested_await)?;
        let Expr::List(mut normalized_body) = normalized_body else {
            unreachable!("body normalization preserves the list wrapper");
        };
        normalized_body.remove(0);
        if !normalized_body
            .last()
            .is_some_and(|last| form(last, "#return").is_some())
        {
            normalized_body.push(Expr::List(vec![
                Expr::Symbol("#return".into()),
                Expr::List(vec![Expr::Symbol("#unreachable".into())]),
            ]));
        }
        Cow::Owned(normalized_body)
    } else {
        Cow::Borrowed(&function[4..])
    };
    let body = normalized_body.as_ref();
    let mut self_references = if pinned {
        pinned_self_references(&params, body)?
    } else {
        Vec::new()
    };
    let mut hoisted_owner_names = HashSet::new();
    for reference in &self_references {
        if self_reference_live_after_await(reference, body) {
            if body.iter().take(reference.source_index).any(has_await) {
                return Err(format!(
                    "@async-fn-pinned self-reference '{}' must be initialized before the first #await",
                    reference.binding.name
                ));
            }
            hoisted_owner_names.insert(reference.owner.name.clone());
        }
    }
    self_references.retain(|reference| hoisted_owner_names.contains(&reference.owner.name));
    let mut hoisted_owners = Vec::new();
    let mut owner_indices = HashMap::new();
    let mut self_reference_sources = Vec::new();
    for reference in &mut self_references {
        owner_indices
            .entry(reference.owner.name.clone())
            .or_insert_with(|| {
                hoisted_owners.push(reference.owner.clone());
                hoisted_owners.len() - 1
            });
        reference.helper_parameter = format!("lim.async.self-ref.{}", self_reference_sources.len());
        self_reference_sources.push(reference.clone());
    }
    let last = form(body.last().unwrap(), "#return")
        .ok_or_else(|| "@async-fn body must end with (#return value)".to_owned())?;
    if last.len() != 2 {
        return Err("@async-fn final #return requires exactly one value".into());
    }
    let mut return_await = form(&last[1], "#await").map(<[Expr]>::to_vec);
    let mut return_value = last[1].clone();
    let waker_source = expression_source(&invocation[3])?;
    let mut statements = body[..body.len() - 1].to_vec();
    for (source_index, statement) in statements.iter_mut().enumerate() {
        lower_labeled_async_loop(statement)?;
        terminalize_async_iterations(statement, &source, &mut next_nested_await)
            .map_err(|error| format!("async statement {source_index}: {error}"))?;
        rewrite_async_synchronous_loop_returns(statement, &ready)?;
        mark_suspending_returns(statement, &function[3]);
        rewrite_async_non_loop_returns(statement, &ready)?;
    }
    let mut generated_helpers = Vec::new();
    let mut lowered_statements = Vec::new();
    let mut lowering_known = known.clone();
    let mut lowering_known_order = known_order.clone();
    let mut consumed_async_statements = HashSet::new();
    for source_index in 0..statements.len() {
        if consumed_async_statements.contains(&source_index) {
            continue;
        }
        let mut statement = statements[source_index].clone();
        let following = statements[source_index + 1..].to_vec();
        if let Some((replacement, helper, result_name, consumed_following)) =
            lower_awaited_let_else_return(
                &statement,
                &following,
                &return_value,
                &function[3],
                &lowering_known,
                &source,
                &mut next_nested_await,
                &waker_source,
            )
            .map_err(|error| format!("async statement {source_index}: {error}"))?
        {
            for consumed_index in source_index + 1..=source_index + consumed_following {
                consumed_async_statements.insert(consumed_index);
            }
            if !helper.is_empty() {
                generated_helpers.push(helper);
            }
            lowered_statements.extend(replacement);
            return_value = Expr::Symbol(result_name);
            continue;
        }
        if let Some((replacement, helper, renames, consumed_following, consumes_return_await)) =
            lower_async_while_with_return_continue(
                &statement,
                &lowering_known,
                &lowering_known_order,
                &following,
                &mut return_value,
                &function[3],
                &source,
                &mut next_nested_await,
                &waker_source,
            )
            .map_err(|error| format!("async statement {source_index}: {error}"))?
        {
            if consumes_return_await {
                return_await = None;
            }
            for consumed_index in source_index + 1..=source_index + consumed_following {
                consumed_async_statements.insert(consumed_index);
            }
            apply_async_output_renames(
                &mut statements[source_index + 1..],
                &mut return_value,
                &mut lowering_known,
                &mut lowering_known_order,
                &renames,
            );
            generated_helpers.push(helper);
            lowered_statements.extend(replacement);
            continue;
        }
        if async_while_has_terminal_return(&statement) {
            if let Some((replacement, helper, renames, consumed_following, consumes_return_await)) =
                lower_async_while(
                    &statement,
                    &lowering_known,
                    &lowering_known_order,
                    &following,
                    &mut return_value,
                    &function[3],
                    &source,
                    &mut next_nested_await,
                    &waker_source,
                )
                .map_err(|error| format!("async statement {source_index}: {error}"))?
            {
                if consumes_return_await {
                    return_await = None;
                }
                for consumed_index in source_index + 1..=source_index + consumed_following {
                    consumed_async_statements.insert(consumed_index);
                }
                apply_async_output_renames(
                    &mut statements[source_index + 1..],
                    &mut return_value,
                    &mut lowering_known,
                    &mut lowering_known_order,
                    &renames,
                );
                generated_helpers.push(helper);
                let mut replacement_known = lowering_known.clone();
                let mut replacement_known_order = lowering_known_order.clone();
                for mut generated_statement in replacement {
                    let mut extracted = Vec::new();
                    extract_statement_awaits(
                        &mut generated_statement,
                        &mut extracted,
                        &mut generated_helpers,
                        &replacement_known,
                        &source,
                        &mut next_nested_await,
                        &waker_source,
                    )
                    .map_err(|error| format!("async statement {source_index}: {error}"))?;
                    lowered_statements.extend(extracted);
                    lowered_statements.push(generated_statement.clone());
                    if let Ok(local) = binding(&generated_statement, "generated loop local") {
                        replacement_known_order.push(local.name.clone());
                        replacement_known.insert(local.name.clone(), local);
                    }
                }
                continue;
            }
        }
        if let Some((replacement, helper, renames)) = lower_async_loop(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &following,
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )
        .map_err(|error| format!("async statement {source_index}: {error}"))?
        {
            apply_async_output_renames(
                &mut statements[source_index + 1..],
                &mut return_value,
                &mut lowering_known,
                &mut lowering_known_order,
                &renames,
            );
            if !helper.is_empty() {
                generated_helpers.push(helper);
            }
            lowered_statements.extend(replacement);
            continue;
        }
        if let Some((replacement, helper, renames, consumed_following)) = lower_async_for(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &following,
            &mut return_value,
            &function[3],
            &source,
            &mut next_nested_await,
            &waker_source,
            type_environment,
        )
        .map_err(|error| format!("async statement {source_index}: {error}"))?
        {
            for consumed_index in source_index + 1..=source_index + consumed_following {
                consumed_async_statements.insert(consumed_index);
            }
            apply_async_output_renames(
                &mut statements[source_index + 1..],
                &mut return_value,
                &mut lowering_known,
                &mut lowering_known_order,
                &renames,
            );
            if !helper.is_empty() {
                generated_helpers.push(helper);
            }
            lowered_statements.extend(replacement);
            continue;
        }
        if let Some((replacement, helper, renames)) = lower_async_for_range(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &following,
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )
        .map_err(|error| format!("async statement {source_index}: {error}"))?
        {
            apply_async_output_renames(
                &mut statements[source_index + 1..],
                &mut return_value,
                &mut lowering_known,
                &mut lowering_known_order,
                &renames,
            );
            generated_helpers.push(helper);
            lowered_statements.extend(replacement);
            continue;
        }
        if let Some((replacement, helper, renames, consumed_following, consumes_return_await)) =
            lower_async_while(
                &statement,
                &lowering_known,
                &lowering_known_order,
                &following,
                &mut return_value,
                &function[3],
                &source,
                &mut next_nested_await,
                &waker_source,
            )
            .map_err(|error| format!("async statement {source_index}: {error}"))?
        {
            if consumes_return_await {
                return_await = None;
            }
            for consumed_index in source_index + 1..=source_index + consumed_following {
                consumed_async_statements.insert(consumed_index);
            }
            apply_async_output_renames(
                &mut statements[source_index + 1..],
                &mut return_value,
                &mut lowering_known,
                &mut lowering_known_order,
                &renames,
            );
            generated_helpers.push(helper);
            lowered_statements.extend(replacement);
            continue;
        }
        let mut generated = Vec::new();
        extract_statement_awaits(
            &mut statement,
            &mut generated,
            &mut generated_helpers,
            &lowering_known,
            &source,
            &mut next_nested_await,
            &waker_source,
        )
        .map_err(|error| format!("async statement {source_index}: {error}"))?;
        lowered_statements.extend(generated);
        lowered_statements.push(statement.clone());
        if let Some(locals) = declared_local_bindings(&statement, type_environment)? {
            for local in locals {
                lowering_known_order.push(local.name.clone());
                lowering_known.insert(local.name.clone(), local);
            }
        }
    }
    statements = lowered_statements;
    // Loop adapters introduce output aggregate declarations alongside their
    // helpers. Pattern captures must use those actual declarations too, not
    // guess fields from names already seen in the enclosing body.
    let pattern_environment = if !generated_helpers.is_empty()
        && statements.iter().any(|statement| {
            form(statement, "#let")
                .or_else(|| form(statement, "#let-mut"))
                .or_else(|| form(statement, "let"))
                .or_else(|| form(statement, "let-mut"))
                .or_else(|| form(statement, "#let-else"))
                .or_else(|| form(statement, "let-else"))
                .is_some_and(|items| matches!(items.get(1), Some(Expr::List(_))))
        }) {
        let mut environment = type_environment.clone();
        for helper in &generated_helpers {
            let declarations = crate::parse(helper)?;
            let metadata = crate::async_type_environment(&declarations);
            environment.aliases.extend(metadata.aliases);
            environment.enums.extend(metadata.enums);
            environment.struct_fields.extend(metadata.struct_fields);
            environment
                .struct_field_order
                .extend(metadata.struct_field_order);
        }
        Cow::Owned(environment)
    } else {
        Cow::Borrowed(type_environment)
    };
    for statement in &mut statements {
        rewrite_async_let_else_returns(statement, &ready)?;
        resolve_generated_async_returns(statement, &ready);
    }
    if let Some(await_expression) = &return_await {
        let mut return_statement = Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol("lim.async.return-value".into()),
            function[3].clone(),
            Expr::List(await_expression.clone()),
        ]);
        let mut generated = Vec::new();
        extract_statement_awaits(
            &mut return_statement,
            &mut generated,
            &mut generated_helpers,
            &lowering_known,
            &source,
            &mut next_nested_await,
            &waker_source,
        )?;
        statements.extend(generated);
        statements.push(return_statement);
    } else {
        let mut generated = Vec::new();
        extract_nested_awaits(
            &mut return_value,
            &mut generated,
            &mut generated_helpers,
            &lowering_known,
            &source,
            &mut next_nested_await,
            &waker_source,
        )?;
        statements.extend(generated);
    }
    for statement in &mut statements {
        rewrite_pinned_self_references(statement, &self_references);
    }
    rewrite_pinned_self_references(&mut return_value, &self_references);
    for reference in self_references.iter().filter(|reference| reference.mutable) {
        for statement in &mut statements {
            let is_binding = binding(statement, "self-reference binding")
                .is_ok_and(|binding| binding.name == reference.binding.name);
            if !is_binding {
                rename_symbol(
                    statement,
                    &reference.binding.name,
                    &reference.helper_parameter,
                );
            }
        }
        rename_symbol(
            &mut return_value,
            &reference.binding.name,
            &reference.helper_parameter,
        );
    }
    let returned = if return_await.is_some() {
        "lim.async.return-value".to_owned()
    } else {
        expression_source(&return_value)?
    };
    let mut stages = Vec::new();
    let mut prefix = Vec::new();
    for (source_index, statement) in statements.iter().enumerate() {
        if !has_await(statement) {
            if form(statement, "#let")
                .or_else(|| form(statement, "#let-mut"))
                .or_else(|| form(statement, "let"))
                .or_else(|| form(statement, "let-mut"))
                .or_else(|| form(statement, "#let-else"))
                .or_else(|| form(statement, "let-else"))
                .is_some()
            {
                let Some(mut local) = binding(statement, "between #await forms").ok() else {
                    let locals = declared_local_bindings(statement, &pattern_environment)?
                        .expect("binding form was checked");
                    for local in locals {
                        let name = local.name.clone();
                        if known.insert(name.clone(), local).is_some() {
                            return Err(format!("@async-fn duplicate binding '{name}'"));
                        }
                        known_order.push(name);
                    }
                    prefix.push(expression_source(statement)?);
                    continue;
                };
                if let Some(reference) = self_references
                    .iter()
                    .find(|reference| reference.binding.name == local.name && reference.mutable)
                {
                    local.name = reference.helper_parameter.clone();
                    known.insert(local.name.clone(), local.clone());
                    known_order.push(local.name);
                    continue;
                }
                if known.insert(local.name.clone(), local.clone()).is_some() {
                    return Err(format!("@async-fn duplicate binding '{}'", local.name));
                }
                known_order.push(local.name.clone());
                prefix.push(expression_source(statement)?);
            } else if let Some(name) = mutable_assignment_target(statement) {
                if !known.get(name).is_some_and(|binding| binding.mutable) {
                    return Err(format!(
                        "@async-fn assignment to '{name}' requires a mutable #let or #mut parameter"
                    ));
                }
                prefix.push(expression_source(statement)?);
            } else if form(statement, "#deref-set").is_some() {
                // The type checker validates that this writes through a
                // mutable reference. Captures are inferred from the resolved
                // value uses just like other statements between stages.
                prefix.push(expression_source(statement)?);
            } else if is_control_flow_statement(statement) {
                prefix.push(expression_source(statement)?);
            } else {
                prefix.push(expression_source(statement)?);
            }
            continue;
        }
        if form(statement, "#let")
            .or_else(|| form(statement, "#let-mut"))
            .or_else(|| form(statement, "let"))
            .or_else(|| form(statement, "let-mut"))
            .is_none()
        {
            return Err(
                "@async-fn #await must be a top-level #let/#let-mut initializer or the direct #return value; awaits inside #if/#match/#block are not lowered yet".into(),
            );
        }
        let local = binding(statement, "#await")?;
        let let_form = form(statement, "#let")
            .or_else(|| form(statement, "#let-mut"))
            .or_else(|| form(statement, "let"))
            .or_else(|| form(statement, "let-mut"))
            .expect("binding statement was validated");
        let await_form = form(&let_form[3], "#await").ok_or_else(|| {
            "@async-fn #await must be the entire initializer of a top-level #let or #let-mut"
                .to_owned()
        })?;
        let protocol_start = match await_form.len() {
            6 => 1,
            7 => {
                let await_result = parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
                let binding_result = parse_type(Some(&normalize_keywords(
                    crate::parse(&local.ty)?
                        .into_iter()
                        .next()
                        .ok_or_else(|| "@async-fn binding type is empty".to_owned())?
                        .expr,
                )))?;
                if await_result != binding_result {
                    return Err(format!(
                        "@async-fn #await result type does not match binding '{}'",
                        local.name
                    ));
                }
                2
            }
            _ => {
                return Err(
                    "#await requires (#await ChildTask Pending Ready poll task-expression) or (#await ResultType ChildTask Pending Ready poll task-expression)".into(),
                );
            }
        };
        if known.contains_key(&local.name) {
            return Err(format!("@async-fn duplicate binding '{}'", local.name));
        }
        let child = expression_source(&await_form[protocol_start])?;
        parse_type(Some(&normalize_keywords(
            await_form[protocol_start].clone(),
        )))?;
        let value = expression_source(&await_form[protocol_start + 4])?;
        if has_await(&await_form[protocol_start + 4]) {
            return Err("@async-fn nested #await is not supported".into());
        }
        stages.push(Stage {
            prefix: std::mem::take(&mut prefix),
            source_index,
            available: known_order.clone(),
            captures: Vec::new(),
            binding: local,
            child,
            pending: symbol(&await_form[protocol_start + 1], "child Pending variant")?.to_owned(),
            ready: symbol(&await_form[protocol_start + 2], "child Ready variant")?.to_owned(),
            poll: symbol(&await_form[protocol_start + 3], "child poll function")?.to_owned(),
            value,
        });
        let local = &stages.last().unwrap().binding;
        known.insert(local.name.clone(), local.clone());
        known_order.push(local.name.clone());
    }
    if stages.is_empty() {
        if pinned {
            let start_variant = format!("{frame}-start");
            let done_variant = format!("{frame}-done");
            let start_helper = format!("{poll}-start");
            let body_helper = fresh_async_name(&source, &mut next_nested_await);
            let result_name = fresh_async_name(&source, &mut next_nested_await);
            let start_parameters = signature(&params);
            let start_arguments = arguments(&params);
            let start_types = types(&params);
            let poll_arguments = named_arguments(&params);
            let body = function[4..]
                .iter()
                .map(expression_source)
                .collect::<Result<Vec<_>, _>>()?
                .join(" ");
            if source.contains(public_poll_result)
                || source.contains(&format!("({public_pending} "))
                || source.contains(&format!("({public_ready} "))
                || source.contains(&frame_state)
            {
                return Err(format!(
                    "{generator_name} generated poll declarations collide with their input"
                ));
            }
            let mut generated = format!(
                "(#enum {frame_state} (({start_variant} {start_types}) ({done_variant})))\n\
                 (#linear {frame_state})\n\
                 (#struct {frame} ((state {frame_state})))\n\
                 (#linear {frame})\n\
                 (#fn {start} ({start_parameters}) {frame}\n\
                   (#return (#struct-literal {frame} ((state ({start_variant} {start_arguments}))))))\n\
                 (#enum {poll_result} (({pending} {frame_state}) ({ready} {result})))\n\
                 (#fn {body_helper} ({start_parameters}) {result}\n\
                   {body})\n\
                 (#fn {start_helper} ({start_parameters} (waker (#ref {waker}))) {poll_result}\n\
                   (#let {result_name} {result} (#call {body_helper} ({poll_arguments})))\n\
                   (#return ({ready} {result_name})))\n\
                 (#fn {poll} ((task {frame_state}) (waker (#ref {waker}))) {poll_result}\n\
                   (#return (#match task\n\
                     (#case ({start_variant} {start_arguments})\n\
                       (#call {start_helper} ({poll_arguments} : waker waker)))\n\
                     (#case {done_variant} (#unreachable)))))\n\
                 (#enum {public_poll_result} (({public_pending} (#pin-ref-mut {frame})) ({public_ready} {result})))\n\
                 (#fn {public_poll} ((task (#pin-ref-mut {frame})) (waker (#ref {waker}))) {public_poll_result}\n\
                   (#let lim.async.pin-state (#pin-ref-mut {frame_state})\n\
                     (#pin-borrow-mut (#get task state)))\n\
                   (#let state {frame_state} (#unsafe (#pin-read lim.async.pin-state)))\n\
                   (#drop lim.async.pin-state)\n\
                   (#let outcome {poll_result}\n\
                     (#call {poll} (: task state : waker waker)))\n\
                   (#return (#match outcome\n\
                     (#case ({pending} next-state)\n\
                       (#block\n\
                         (#let lim.async.pending-state (#pin-ref-mut {frame_state})\n\
                           (#pin-borrow-mut (#get task state)))\n\
                         (#unsafe (#pin-write lim.async.pending-state next-state))\n\
                         (#drop lim.async.pending-state)\n\
                         ({public_pending} task)))\n\
                     (#case ({ready} value)\n\
                       (#block\n\
                         (#let lim.async.ready-state (#pin-ref-mut {frame_state})\n\
                           (#pin-borrow-mut (#get task state)))\n\
                         (#unsafe (#pin-write lim.async.ready-state ({done_variant})))\n\
                         (#drop lim.async.ready-state)\n\
                         ({public_ready} value))))))\n\
                 (#fn {cancel} ((task (#pin-ref-mut {frame}))) {frame_state}\n\
                   (#let lim.async.cancel-state (#pin-ref-mut {frame_state})\n\
                     (#pin-borrow-mut (#get task state)))\n\
                   (#let state {frame_state} (#unsafe (#pin-read lim.async.cancel-state)))\n\
                   (#unsafe (#pin-write lim.async.cancel-state ({done_variant})))\n\
                   (#drop lim.async.cancel-state)\n\
                   (#return state))"
            );
            if let Some(config) = &cancel_config {
                if config.function == cancel {
                    return Err(format!(
                        "{generator_name} cancellation function '{}' conflicts with generated pinned-state extraction",
                        config.function
                    ));
                }
                let cleanup = async_cancel_function(
                    config,
                    &frame_state,
                    &[AsyncCancelState {
                        variant: start_variant,
                        fields: params
                            .iter()
                            .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
                            .collect(),
                    }],
                    Some(&done_variant),
                )?;
                generated.push('\n');
                generated.push_str(&cleanup);
            }
            return Ok(generated);
        }
        let start_variant = format!("{frame}-start");
        let start_helper = format!("{poll}-start");
        let body_helper = fresh_async_name(&source, &mut next_nested_await);
        let result_name = fresh_async_name(&source, &mut next_nested_await);
        let start_parameters = signature(&params);
        let start_arguments = arguments(&params);
        let start_types = types(&params);
        let poll_arguments = named_arguments(&params);
        let body = function[4..]
            .iter()
            .map(expression_source)
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let mut generated = format!(
            "{}\n\
             (#enum {frame_state} (({start_variant} {start_types})))\n\
             (#linear {frame_state})\n\
             (#fn {start} ({start_parameters}) {frame_state}\n\
               (#return ({start_variant} {start_arguments})))\n\
             (#enum {poll_result} (({pending} {frame_state}) ({ready} {result})))\n\
             (#fn {body_helper} ({start_parameters}) {result}\n\
               {body})\n\
             (#fn {start_helper} ({start_parameters} (waker (#ref {waker}))) {poll_result}\n\
               (#let {result_name} {result} (#call {body_helper} ({poll_arguments})))\n\
               (#return ({ready} {result_name})))\n\
             (#fn {poll} ((task {frame_state}) (waker (#ref {waker}))) {poll_result}\n\
               (#return (#match task\n\
                 (#case ({start_variant} {start_arguments})\n\
                   (#call {start_helper} ({poll_arguments} : waker waker))))))",
            generated_helpers.join("\n")
        );
        if let Some(config) = &cancel_config {
            let cleanup = async_cancel_function(
                config,
                &frame_state,
                &[AsyncCancelState {
                    variant: start_variant,
                    fields: params
                        .iter()
                        .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
                        .collect(),
                }],
                None,
            )?;
            generated.push('\n');
            generated.push_str(&cleanup);
        }
        return Ok(generated);
    }
    for (stage_index, stage) in stages.iter_mut().enumerate() {
        let live = continuation_live_names(
            &statements[stage.source_index + 1..],
            return_await.is_none().then_some(&return_value),
            &known,
        );
        stage.captures = stage
            .available
            .iter()
            .filter(|name| match &capture_selection {
                CaptureSelection::Syntax => live.contains(name.as_str()),
                CaptureSelection::Typed(captures) => {
                    live.contains(name.as_str())
                        && (captures
                        .get(&stage_index)
                        .is_some_and(|live| live.contains(name.as_str()))
                        // A mutated binding still needs a local slot even if
                        // its incoming value is dead before the first read,
                        // but only when source liveness says it crosses here.
                        || (live.contains(name.as_str())
                            && known.get(*name).is_some_and(|binding| binding.mutable)))
                }
            })
            .filter_map(|name| known.get(name).cloned())
            .collect();
    }
    let self_reference_declarations = self_references
        .iter()
        .map(|reference| reference.source_index)
        .collect::<HashSet<_>>();
    for reference in &self_references {
        if reference.owner.name == "state" {
            return Err("@async-fn-pinned self-reference owner cannot be named 'state'".into());
        }
        let mut used_elsewhere = false;
        for (index, statement) in body.iter().enumerate() {
            if self_reference_declarations.contains(&index) {
                continue;
            }
            let mut names = HashSet::new();
            collect_value_names(statement, &mut names);
            used_elsewhere |= names.contains(&reference.owner.name);
        }
        if used_elsewhere {
            return Err(format!(
                "@async-fn-pinned self-reference owner '{}' may only be used to initialize its pinned reference",
                reference.owner.name
            ));
        }
    }
    let start_params = params
        .iter()
        .filter(|parameter| !owner_indices.contains_key(&parameter.name))
        .cloned()
        .collect::<Vec<_>>();
    let frame_owner_fields = hoisted_owners
        .iter()
        .map(|owner| format!("({} {})", owner.name, owner.ty))
        .collect::<Vec<_>>();
    let local_hoisted_owners = hoisted_owners
        .iter()
        .filter_map(|owner| {
            self_references
                .iter()
                .find(|reference| reference.owner.name == owner.name)
                .and_then(|reference| {
                    reference
                        .owner_initializer
                        .as_ref()
                        .map(|initializer| (owner, initializer))
                })
        })
        .collect::<Vec<_>>();
    let local_hoisted_owner_names = local_hoisted_owners
        .iter()
        .map(|(owner, _)| owner.name.as_str())
        .collect::<HashSet<_>>();
    let start_owner_initializers = local_hoisted_owners
        .iter()
        .map(|(owner, initializer)| format!("(#let {} {} {})", owner.name, owner.ty, initializer))
        .collect::<Vec<_>>()
        .join(" ");
    let self_reference_parameters = self_reference_sources
        .iter()
        .enumerate()
        .map(|(_, reference)| {
            format!(
                "({} ({} {}))",
                reference.helper_parameter,
                if reference.mutable {
                    "#pin-ref-mut"
                } else {
                    "#pin-ref"
                },
                reference.target_ty
            )
        })
        .collect::<Vec<_>>();
    let self_reference_arguments = self_reference_sources
        .iter()
        .enumerate()
        .map(|(index, reference)| {
            format!(
                ": {} lim.async.self-ref.{index}",
                reference.helper_parameter
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let self_reference_borrows = self_reference_sources
        .iter()
        .enumerate()
        .map(|(index, reference)| {
            let mut place = format!("(#get task {})", reference.owner.name);
            for projection in &reference.projection {
                match projection {
                    PinnedProjection::Field(field) => {
                        place = format!("(#get {place} {field})");
                    }
                    PinnedProjection::EnumPayload { variant, index } => {
                        place =
                            format!("(#pin-get-payload (#pin-borrow {place}) {variant} {index})");
                    }
                }
            }
            let initializer = if matches!(
                reference.projection.last(),
                Some(PinnedProjection::EnumPayload { .. })
            ) {
                place
            } else {
                format!(
                    "({} {place})",
                    if reference.mutable {
                        "#pin-borrow-mut"
                    } else {
                        "#pin-borrow"
                    }
                )
            };
            format!(
                "(#let lim.async.self-ref.{index} ({} {})\n\
                   {initializer})",
                if reference.mutable {
                    "#pin-ref-mut"
                } else {
                    "#pin-ref"
                },
                reference.target_ty
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let self_reference_parameter_suffix = self_reference_parameters.join(" ");
    let self_reference_argument_suffix = if self_reference_arguments.is_empty() {
        String::new()
    } else {
        format!(" {self_reference_arguments}")
    };
    let self_reference_drops = self_reference_sources
        .iter()
        .enumerate()
        .map(|(index, _)| format!("(#drop lim.async.self-ref.{index})"))
        .collect::<Vec<_>>()
        .join(" ");
    let reserved = [
        "waker",
        "lim.async.task",
        "lim.async.polled-task",
        "lim.async.child",
        "lim.async.value",
        "lim.async.pin-state",
        "lim.async.pending-state",
        "lim.async.ready-state",
        "lim.async.cancel-state",
    ];
    let mut source_names = HashSet::new();
    collect_value_names(&invocation[4], &mut source_names);
    if known.keys().any(|name| reserved.contains(&name.as_str()))
        || (0..self_reference_sources.len())
            .any(|index| source_names.contains(&format!("lim.async.self-ref.{index}")))
    {
        return Err("@async-fn bindings cannot use reserved waker or lim.async.* names".into());
    }
    let start_variant = format!("{frame}-start");
    let start_helper = format!("{poll}-start");
    if start == start_helper
        || start.starts_with(&format!("{poll}-child-"))
        || start.starts_with(&format!("{poll}-resume-"))
    {
        return Err("@async-fn start function collides with a generated helper".into());
    }
    let mut variants = vec![format!("({start_variant} {})", types(&start_params))];
    let mut await_cases = Vec::new();
    let done_variant = format!("{frame}-done");
    if pinned {
        if source.contains(&cancel) {
            return Err(format!("{generator_name} generated cancellation function '{cancel}' collides with its input"));
        }
        variants.push(format!("({done_variant})"));
        await_cases.push(format!("(#case {done_variant} (#unreachable))"));
    }
    let mut helpers = Vec::new();
    for (index, stage) in stages.iter().enumerate() {
        let await_variant = format!("{frame}-await-{index}");
        let resume = format!("{poll}-resume-{index}");
        let child_helper = format!("{poll}-child-{index}");
        variants.push(format!(
            "({await_variant} {} {})",
            types(&stage.captures),
            stage.child
        ));
        let continuation = if let Some(next) = stages.get(index + 1) {
            let mut next_prefix = resume_prefix(&next.prefix, stage, &known, &pattern_environment)?;
            let next_value = inline_stage_task_temporary(&mut next_prefix, &next.value)?;
            // Calls evaluate in parameter declaration order: captures precede
            // the child parameter. Finish task construction before snapshots
            // of those captures, including mutations in the task expression.
            let next_task = fresh_async_name(&source, &mut next_nested_await);
            next_prefix.push(format!("(#let {next_task} {} {next_value})", next.child));
            format!(
                "(#return (#block {} (#call {poll}-child-{} ({} : lim.async.task {} : waker waker))))",
                next_prefix.join(" "),
                index + 1,
                named_arguments(&next.captures),
                next_task
            )
        } else {
            format!(
                "{} (#return ({ready} {returned}))",
                resume_prefix(&prefix, stage, &known, &pattern_environment)?.join(" ")
            )
        };
        helpers.push(format!(
            "(#fn {resume} ({} {} (waker (#ref {waker}))) {poll_result}
               {continuation})",
            signature(&stage.captures),
            parameter(&stage.binding)
        ));
        helpers.push(format!(
            "(#fn {child_helper} ({} (lim.async.task {}) (waker (#ref {waker}))) {poll_result}
               (#return (#match
                 (#call {} (: task lim.async.task : waker waker))
                 (#case ({} lim.async.child)
                   ({pending} ({await_variant} {} lim.async.child)))
                 (#case ({} lim.async.value)
                   (#call {resume} ({} : {} lim.async.value : waker waker))))))",
            signature(&stage.captures),
            stage.child,
            stage.poll,
            stage.pending,
            arguments(&stage.captures),
            stage.ready,
            named_arguments(&stage.captures),
            stage.binding.name,
        ));
        await_cases.push(format!(
            "(#case ({await_variant} {} lim.async.child)
               (#call {child_helper} ({} : lim.async.task lim.async.child : waker waker)))",
            arguments(&stage.captures),
            named_arguments(&stage.captures),
        ));
    }
    let first = &stages[0];
    let first_prefix = first
        .prefix
        .iter()
        .filter(|statement| {
            !local_hoisted_owner_names.iter().any(|name| {
                statement
                    .strip_prefix("(#let ")
                    .is_some_and(|rest| rest.starts_with(&format!("{name} ")))
            })
        })
        .cloned()
        .collect::<Vec<_>>()
        .join(" ");
    let has_mutable_self_references = self_reference_sources
        .iter()
        .any(|reference| reference.mutable);
    let start_call = format!(
        "(#call {start_helper} ({} : waker waker{}))",
        named_arguments(&start_params),
        self_reference_argument_suffix
    );
    let start_body = if !has_mutable_self_references || self_reference_borrows.is_empty() {
        start_call
    } else {
        format!("(#block {} {start_call})", self_reference_borrows)
    };
    let start_case = format!(
        "(#case ({start_variant} {}) {start_body})",
        arguments(&start_params)
    );
    let frame_fields = std::iter::once(format!("(state {frame_state})"))
        .chain(frame_owner_fields.iter().cloned())
        .collect::<Vec<_>>()
        .join(" ");
    let frame_start_values = std::iter::once(format!(
        "(state ({start_variant} {}))",
        arguments(&start_params)
    ))
    .chain(
        hoisted_owners
            .iter()
            .map(|owner| format!("({} {})", owner.name, owner.name)),
    )
    .collect::<Vec<_>>()
    .join(" ");
    let frame_declarations = if pinned {
        format!(
            "(#enum {frame_state} ({}))\n\
             (#linear {frame_state})\n\
             (#struct {frame} ({frame_fields}))\n\
             (#linear {frame})\n\
             (#fn {start} ({}) {frame}\n\
               {start_owner_initializers}\n\
               (#return (#struct-literal {frame} ({frame_start_values}))))",
            variants.join(" "),
            signature(&params),
        )
    } else {
        format!(
            "(#enum {frame_state} ({}))\n\
             (#linear {frame_state})\n\
             (#fn {start} ({}) {frame_state}\n\
               (#return ({start_variant} {})))",
            variants.join(" "),
            signature(&params),
            arguments(&params),
        )
    };
    let poll_function = if pinned && has_mutable_self_references {
        String::new()
    } else {
        format!(
            "(#fn {poll} ((task {frame_state}) (waker (#ref {waker})) {self_reference_parameter_suffix}) {poll_result}\n\
               (#return (#match task {start_case} {})))",
            await_cases.join(" ")
        )
    };
    let pinned_poll_outcome = if has_mutable_self_references {
        format!(
            "(#let outcome {poll_result} (#match state {start_case} {}))",
            await_cases.join(" ")
        )
    } else {
        format!(
            "{self_reference_borrows} (#let outcome {poll_result} (#call {poll} (: task state : waker waker{self_reference_argument_suffix}))) {self_reference_drops}"
        )
    };
    let first_task = fresh_async_name(&source, &mut next_nested_await);
    let mut generated = format!(
        "{}\n{}
         (#enum {poll_result} (({pending} {frame_state}) ({ready} {result})))
         {}
         (#fn {start_helper} ({} (waker (#ref {waker})) {self_reference_parameter_suffix}) {poll_result}
           {}
           (#let {first_task} {} {})
           (#return (#call {poll}-child-0 ({} : lim.async.task {} : waker waker))))
         {poll_function}",
        generated_helpers.join("\n"),
        frame_declarations,
        helpers.join("\n"),
        signature(&start_params),
        first_prefix,
        first.child,
        first.value,
        named_arguments(&first.captures),
        first_task,
    );
    if let Some(config) = &cancel_config {
        let mut cancellation_states = vec![AsyncCancelState {
            variant: start_variant.clone(),
            fields: start_params
                .iter()
                .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
                .collect(),
        }];
        for (index, stage) in stages.iter().enumerate() {
            let mut fields = stage
                .captures
                .iter()
                .map(|capture| (capture.name.clone(), capture.ty.clone()))
                .collect::<Vec<_>>();
            fields.push(("lim.async.child".into(), stage.child.clone()));
            cancellation_states.push(AsyncCancelState {
                variant: format!("{frame}-await-{index}"),
                fields,
            });
        }
        let cleanup = async_cancel_function(
            config,
            &frame_state,
            &cancellation_states,
            pinned.then_some(done_variant.as_str()),
        )?;
        generated.push('\n');
        generated.push_str(&cleanup);
    }
    if !pinned {
        return Ok(generated);
    }
    if source.contains(public_poll_result)
        || source.contains(&format!("({public_pending} "))
        || source.contains(&format!("({public_ready} "))
        || source.contains(&frame_state)
    {
        return Err(format!(
            "{generator_name} generated poll declarations collide with their input"
        ));
    }
    Ok(format!(
        "{generated}
         (#enum {public_poll_result} (({public_pending} (#pin-ref-mut {frame})) ({public_ready} {result})))
         (#fn {public_poll} ((task (#pin-ref-mut {frame})) (waker (#ref {waker}))) {public_poll_result}
           (#let lim.async.pin-state (#pin-ref-mut {frame_state})
             (#pin-borrow-mut (#get task state)))
           (#let state {frame_state} (#unsafe (#pin-read lim.async.pin-state)))
           (#drop lim.async.pin-state)
           {pinned_poll_outcome}
           (#return (#match outcome
             (#case ({pending} next-state)
               (#block
                 (#let lim.async.pending-state (#pin-ref-mut {frame_state})
                   (#pin-borrow-mut (#get task state)))
                 (#unsafe (#pin-write lim.async.pending-state next-state))
                 (#drop lim.async.pending-state)
                 ({public_pending} task)))
             (#case ({ready} value)
               (#block
                 (#let lim.async.ready-state (#pin-ref-mut {frame_state})
                   (#pin-borrow-mut (#get task state)))
                 (#unsafe (#pin-write lim.async.ready-state ({done_variant})))
                 (#drop lim.async.ready-state)
                 ({public_ready} value))))))
         (#fn {cancel} ((task (#pin-ref-mut {frame}))) {frame_state}
           (#let lim.async.cancel-state (#pin-ref-mut {frame_state})
             (#pin-borrow-mut (#get task state)))
           (#let state {frame_state} (#unsafe (#pin-read lim.async.cancel-state)))
           (#unsafe (#pin-write lim.async.cancel-state ({done_variant})))
           (#drop lim.async.cancel-state)
           (#return state))",
        public_pending = public_pending,
        public_ready = public_ready,
        public_poll_result = public_poll_result,
        public_poll = public_poll,
        pinned_poll_outcome = pinned_poll_outcome,
    ))
}

fn collect_value_names(expr: &Expr, names: &mut HashSet<String>) {
    match expr {
        Expr::Symbol(symbol) => {
            names.insert(symbol.clone());
        }
        Expr::List(items) => {
            let Some(Expr::Symbol(head)) = items.first() else {
                for item in items {
                    collect_value_names(item, names);
                }
                return;
            };
            match head.as_str() {
                "#literal" => {}
                "#as" | "as" if items.len() == 3 => {
                    collect_value_names(&items[1], names);
                }
                "#size-of" | "size-of" | "#align-of" | "align-of" => {}
                "#tuple" | "tuple" | "#array-of" | "array-of" => {
                    for value in items.iter().skip(2) {
                        collect_value_names(value, names);
                    }
                }
                "#asm" | "asm" if items.len() >= 3 => {
                    if let Expr::List(registers) = &items[2] {
                        for register in registers {
                            if let Expr::List(pair) = register {
                                if let Some(value) = pair.get(1) {
                                    collect_value_names(value, names);
                                }
                            }
                        }
                    }
                }
                "#async-terminal-return" if items.len() == 3 => {
                    collect_value_names(&items[2], names);
                }
                "#await" => {
                    let task_index = if items.len() == 7 { 6 } else { 5 };
                    if let Some(value) = items.get(task_index) {
                        collect_value_names(value, names);
                    }
                }
                "#for-range" if items.len() >= 5 => {
                    for value in items.iter().skip(2) {
                        collect_value_names(value, names);
                    }
                }
                "#let" | "#let-mut" | "let" | "let-mut" if items.len() >= 4 => {
                    collect_value_names(&items[3], names);
                }
                "#let-else" | "let-else" if items.len() >= 5 => {
                    collect_value_names(&items[3], names);
                    collect_value_names(&items[4], names);
                }
                "#struct-literal" if items.len() >= 3 => {
                    if let Expr::List(fields) = &items[2] {
                        for field in fields {
                            if let Expr::List(pair) = field {
                                if let Some(value) = pair.get(1) {
                                    collect_value_names(value, names);
                                }
                            }
                        }
                    }
                }
                "#get" | "get" if items.len() >= 2 => {
                    collect_value_names(&items[1], names);
                }
                "#get-payload" | "get-payload" if items.len() >= 2 => {
                    collect_value_names(&items[1], names);
                }
                "#set-field" | "set-field" if items.len() >= 4 => {
                    collect_value_names(&items[1], names);
                    collect_value_names(&items[3], names);
                }
                "#call" | "call" => {
                    for item in items.iter().skip(2) {
                        collect_named_values(item, names);
                    }
                }
                "#case" | "case" => {
                    for item in items.iter().skip(2) {
                        collect_value_names(item, names);
                    }
                }
                "#match" | "match" => {
                    if let Some(scrutinee) = items.get(1) {
                        collect_value_names(scrutinee, names);
                    }
                    for arm in items.iter().skip(2) {
                        collect_value_names(arm, names);
                    }
                }
                "#quote" | "quote" | "#quasiquote" | "quasiquote" => {}
                _ => {
                    for item in items.iter().skip(1) {
                        collect_named_values(item, names);
                    }
                }
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            for statement in statements {
                match statement {
                    crate::Statement::Let { value, .. }
                    | crate::Statement::Expr(value)
                    | crate::Statement::Return(Some(value))
                    | crate::Statement::BreakValue(value)
                    | crate::Statement::BreakToValue { value, .. } => {
                        collect_value_names(value, names);
                    }
                    crate::Statement::Assign { name, value }
                    | crate::Statement::ArrayAssign { name, value, .. }
                    | crate::Statement::FieldAssign { name, value, .. }
                    | crate::Statement::TupleAssign { name, value, .. }
                    | crate::Statement::EnumPayloadAssign { name, value, .. } => {
                        names.insert(name.clone());
                        collect_value_names(value, names);
                    }
                    _ => {}
                }
            }
        }
        Expr::Labeled { expression, .. } => collect_value_names(expression, names),
        Expr::Unquote(value) | Expr::UnquoteSplicing(value) => collect_value_names(value, names),
        Expr::Quote(_) | Expr::QuasiQuote(_) | Expr::At => {}
        Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_) => {}
    }
}

fn collect_local_binding_names(expr: &Expr, names: &mut HashSet<String>) {
    match expr {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#while-let") {
                if let Some(pattern) = items.get(1) {
                    names.extend(pattern_symbols(pattern));
                }
                for value in items.iter().skip(2) {
                    collect_local_binding_names(value, names);
                }
                return;
            }
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#for-range") {
                if let Some(Expr::List(binding)) = items.get(1) {
                    if let Some(Expr::Symbol(name)) = binding.first() {
                        names.insert(name.clone());
                    }
                }
                for value in items.iter().skip(2) {
                    collect_local_binding_names(value, names);
                }
                return;
            }
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let" | "#let-mut" | "let" | "let-mut" | "#let-else" | "let-else"))
            {
                if let Some(pattern) = items.get(1) {
                    names.extend(pattern_symbols(pattern));
                }
                for value in items.iter().skip(3) {
                    collect_local_binding_names(value, names);
                }
                return;
            }
            for item in items.iter().skip(1) {
                collect_local_binding_names(item, names);
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            for statement in statements {
                match statement {
                    crate::Statement::Expr(value)
                    | crate::Statement::Return(Some(value))
                    | crate::Statement::BreakValue(value)
                    | crate::Statement::BreakToValue { value, .. } => {
                        collect_local_binding_names(value, names)
                    }
                    _ => {}
                }
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => collect_local_binding_names(expression, names),
        _ => {}
    }
}

fn collect_named_values(expr: &Expr, names: &mut HashSet<String>) {
    if let Expr::List(items) = expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == ":") {
            for value in items.iter().skip(2).step_by(2) {
                collect_value_names(value, names);
            }
            return;
        }
    }
    collect_value_names(expr, names);
}

fn rename_named_values(expr: &mut Expr, from: &str, to: &str) {
    if let Expr::List(items) = expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == ":") {
            for value in items.iter_mut().skip(2).step_by(2) {
                rename_async_value(value, from, to);
            }
            return;
        }
    }
    rename_async_value(expr, from, to);
}

/// Rename a value reference without rewriting declaration names, type names,
/// field labels, function names, or named-argument keys.
fn rename_async_value(expr: &mut Expr, from: &str, to: &str) {
    match expr {
        Expr::Symbol(name) if name == from => *name = to.to_owned(),
        Expr::List(items) => {
            let Some(Expr::Symbol(head)) = items.first() else {
                for item in items {
                    rename_async_value(item, from, to);
                }
                return;
            };
            match head.as_str() {
                "#quote" | "quote" | "#quasiquote" | "quasiquote" => {}
                "#call" | "call" => {
                    if let Some(arguments) = items.get_mut(2) {
                        rename_named_values(arguments, from, to);
                    }
                }
                "#let" | "#let-mut" | "let" | "let-mut" if items.len() >= 4 => {
                    rename_async_value(&mut items[3], from, to);
                }
                "#let-else" | "let-else" if items.len() >= 5 => {
                    rename_async_value(&mut items[3], from, to);
                    rename_async_value(&mut items[4], from, to);
                }
                "#await" if items.len() >= 6 => {
                    let task_index = if items.len() == 7 { 6 } else { 5 };
                    if let Some(task) = items.get_mut(task_index) {
                        rename_async_value(task, from, to);
                    }
                }
                "#struct-literal" if items.len() >= 3 => {
                    if let Expr::List(fields) = &mut items[2] {
                        for field in fields {
                            if let Expr::List(pair) = field {
                                if let Some(value) = pair.get_mut(1) {
                                    rename_async_value(value, from, to);
                                }
                            }
                        }
                    }
                }
                "#get" | "get" | "#get-payload" | "get-payload" if items.len() >= 2 => {
                    rename_async_value(&mut items[1], from, to);
                }
                "#set" | "set" if items.len() >= 3 => {
                    rename_async_value(&mut items[1], from, to);
                    rename_async_value(&mut items[2], from, to);
                }
                "#set-field" | "set-field" if items.len() >= 4 => {
                    rename_async_value(&mut items[1], from, to);
                    rename_async_value(&mut items[3], from, to);
                }
                "#set-index" | "set-index" if items.len() >= 4 => {
                    for item in &mut items[1..4] {
                        rename_async_value(item, from, to);
                    }
                }
                "#match" | "match" => {
                    for item in items.iter_mut().skip(1) {
                        rename_async_value(item, from, to);
                    }
                }
                "#case" | "case" => {
                    for item in items.iter_mut().skip(2) {
                        rename_async_value(item, from, to);
                    }
                }
                "#literal" if items.len() >= 3 => {
                    rename_async_value(&mut items[2], from, to);
                }
                _ => {
                    for item in items.iter_mut().skip(1) {
                        rename_named_values(item, from, to);
                    }
                }
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            for statement in statements {
                match statement {
                    crate::Statement::Let { value, .. }
                    | crate::Statement::Expr(value)
                    | crate::Statement::Return(Some(value))
                    | crate::Statement::BreakValue(value)
                    | crate::Statement::BreakToValue { value, .. } => {
                        rename_async_value(value, from, to);
                    }
                    crate::Statement::Assign { name, value }
                    | crate::Statement::ArrayAssign { name, value, .. }
                    | crate::Statement::FieldAssign { name, value, .. }
                    | crate::Statement::TupleAssign { name, value, .. }
                    | crate::Statement::EnumPayloadAssign { name, value, .. } => {
                        if name == from {
                            *name = to.to_owned();
                        }
                        rename_async_value(value, from, to);
                    }
                    _ => {}
                }
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => rename_async_value(expression, from, to),
        Expr::Quote(_) | Expr::QuasiQuote(_) | Expr::At => {}
        Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_) => {}
    }
}

fn apply_async_output_renames(
    following: &mut [Expr],
    return_value: &mut Expr,
    known: &mut HashMap<String, Binding>,
    known_order: &mut Vec<String>,
    renames: &[(String, Binding)],
) {
    for (old_name, new_binding) in renames {
        for expression in following.iter_mut() {
            rename_async_value(expression, old_name, &new_binding.name);
        }
        rename_async_value(return_value, old_name, &new_binding.name);
        known.remove(old_name);
        known_order.retain(|name| name != old_name);
        known_order.push(new_binding.name.clone());
        known.insert(new_binding.name.clone(), new_binding.clone());
    }
}

#[cfg(test)]
mod async_lowering_tests {
    use super::*;

    #[test]
    fn nested_pattern_scope_walks_separate_declarations_from_value_uses() {
        let expression = crate::parse(
            "(#let-else (Some (Parts (#tuple first second) _)) Maybe input
          (#block (#let (#array failed other) (#array u64 2) fallback) (#return failed)))",
        )
        .unwrap()
        .remove(0)
        .expr;
        let mut locals = HashSet::new();
        collect_local_binding_names(&expression, &mut locals);
        assert_eq!(
            locals,
            ["first", "second", "failed", "other"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        );
        let mut values = HashSet::new();
        collect_value_names(&expression, &mut values);
        assert_eq!(
            values,
            ["input", "fallback", "failed"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        );
    }

    #[test]
    fn capture_walk_ignores_type_annotations_and_assembly_register_labels() {
        let expression = crate::parse(
            "(#block (#as byte u64)
          (#tuple (#tuple u64 bool) number decision)
          (#array-of (#array u32 2) left right)
          (#size-of Layout) (#align-of Layout)
          (#unsafe (#asm u64 ((rax input) (rdi (#as count usize))) \"syscall\")))",
        )
        .unwrap()
        .remove(0)
        .expr;
        let mut names = HashSet::new();
        collect_value_names(&expression, &mut names);
        assert_eq!(
            names,
            ["byte", "number", "decision", "left", "right", "input", "count"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        );
    }

    #[test]
    fn local_pattern_bindings_preserve_nested_order_aliases_and_mutability() {
        let environment = crate::async_type_environment(
            &crate::parse("(#type Narrow u16) (#struct Parts ((z (#array Narrow 2)) (a u64)))")
                .unwrap(),
        );
        let expression = |source| crate::parse(source).unwrap().remove(0).expr;
        let bindings = declared_local_bindings(
            &expression("(#let-mut (Parts (#array first second) tail) Parts parts)"),
            &environment,
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            bindings
                .iter()
                .map(|binding| (binding.name.as_str(), binding.ty.as_str(), binding.mutable))
                .collect::<Vec<_>>(),
            [
                ("first", "Narrow", true),
                ("second", "Narrow", true),
                ("tail", "u64", true)
            ]
        );
        let ignored = declared_local_bindings(
            &expression("(#let (Parts (#array _ only) _) Parts parts)"),
            &environment,
        )
        .unwrap()
        .unwrap();
        assert_eq!(ignored.len(), 1);
        assert_eq!(ignored[0].name, "only");
        assert!(!ignored[0].mutable);
        let duplicate = declared_local_bindings(
            &expression("(#let (Parts (#array repeated repeated) tail) Parts parts)"),
            &environment,
        )
        .err()
        .expect("duplicate leaves must fail before capture layout");
        assert!(
            duplicate.contains("duplicate pattern binding 'repeated'"),
            "{duplicate}"
        );
    }

    #[test]
    fn stage_task_inlining_leaves_pattern_declarations_intact() {
        let mut prefix = vec!["(#let (#tuple left right) (#tuple u64 u64) pair)".into()];
        let original = prefix.clone();
        assert_eq!(
            inline_stage_task_temporary(&mut prefix, "child").unwrap(),
            "child"
        );
        assert_eq!(prefix, original);
    }

    #[test]
    fn suspension_detection_walks_structured_control_flow() {
        let await_expression = Expr::List(vec![Expr::Symbol("#await".into())]);
        let mut expression = Expr::Block(vec![crate::Statement::Labeled {
            label: "outer".into(),
            statement: Box::new(crate::Statement::While {
                condition: Expr::Symbol("true".into()),
                body: vec![
                    crate::Statement::Expr(await_expression),
                    crate::Statement::ContinueTo("outer".into()),
                ],
            }),
        }]);
        assert!(has_await(&expression));
        assert_eq!(await_count(&expression), 1);
        lower_labeled_async_loop(&mut expression).unwrap();
        let Expr::Block(statements) = expression else {
            panic!("block expression was not retained")
        };
        let [crate::Statement::While { body, .. }] = statements.as_slice() else {
            panic!("labeled loop was not lowered")
        };
        assert!(matches!(body.last(), Some(crate::Statement::Continue)));
    }
}
