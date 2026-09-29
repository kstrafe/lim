//! Syntactic lowering for concrete async functions with inferred live captures.
//!
//! This deliberately emits ordinary Lim declarations before type and borrow
//! checking. No suspension point can hide a reference from those passes.

use std::collections::{HashMap, HashSet};

use crate::{expression_source, normalize_keywords, parse_type, Expr, Type};

#[derive(Clone)]
struct Binding {
    name: String,
    ty: String,
    mutable: bool,
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
        | Type::Generic(_)
        | Type::Named(_) => false,
    }
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
    match expr {
        Expr::List(items) => form(expr, "#await").is_some() || items.iter().any(has_await),
        _ => false,
    }
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
    let (statement_index, binding, assignment) = (1..block.len() - 1).find_map(|index| {
        let statement = &block[index];
        if let Some(binding) = form(statement, "#let").or_else(|| form(statement, "#let-mut")) {
            if binding.len() == 4 {
                if form(&binding[3], "#await").is_some_and(|await_form| await_form.len() == 7) {
                    return Some((index, Some(binding), None));
                }
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
        Some((index, None, Some((statement.clone(), rhs_index))))
    })?;
    let await_expression = if let Some(binding) = binding {
        binding[3].clone()
    } else {
        let (statement, rhs_index) = assignment.as_ref()?;
        let Expr::List(items) = statement else {
            return None;
        };
        items.get(*rhs_index)?.clone()
    };
    let await_form = form(&await_expression, "#await")?;
    parse_type(Some(&normalize_keywords(await_form[1].clone()))).ok()?;
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
        result_type: await_form[1].clone(),
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
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(AwaitProtocol, Expr, String)>, String> {
    let mut branches = Vec::<(Option<AwaitProtocol>, Expr)>::new();
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
            } else if !has_await(branch) {
                branches.push((None, branch.clone()));
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
            let lowered = conditional_await(&case[body_index])?;
            if let Some((protocol, task)) = lowered {
                let mut task_arm = vec![Expr::Symbol("#case".into()), case[1].clone()];
                if body_index == 3 {
                    task_arm.push(case[2].clone());
                }
                task_arm.push(task);
                branches.push((Some(protocol), Expr::List(task_arm)));
            } else if !has_await(&case[body_index]) {
                branches.push((None, arm.clone()));
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
    let helper = format!(
        "(#enum {choice_task} ({}))\n\
         (#linear {choice_task})\n\
         (#enum {choice_poll_result} (({choice_pending} {choice_task}) ({choice_ready} {result_type})))\n\
         (#fn {choice_poll} ((task {choice_task}) (waker (#ref {waker}))) {choice_poll_result}\n\
           (#return (#match task {})))",
        choice_variants.join(" "),
        poll_arms.join(" "),
    );
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

fn extract_nested_awaits(
    expression: &mut Expr,
    generated: &mut Vec<Expr>,
    generated_helpers: &mut Vec<String>,
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
                source,
                next_name,
                waker,
            );
        }
    }
    if let Expr::List(items) = expression {
        if items.len() == 3
            && matches!(items.first(), Some(Expr::Symbol(operator))
                if matches!(operator.as_str(), "#bool.&&" | "bool.&&" | "#bool.||" | "bool.||"))
            && has_await(&items[2])
        {
            let operator = match &items[0] {
                Expr::Symbol(operator) => operator.as_str(),
                _ => unreachable!(),
            };
            let is_and = operator.ends_with("&&");
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
            return extract_nested_awaits(
                expression,
                generated,
                generated_helpers,
                source,
                next_name,
                waker,
            );
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
            let binding = form(statement, "#let").or_else(|| form(statement, "#let-mut"));
            if let Some(binding) = binding {
                if binding.len() != 4 {
                    return Err(
                        "@async-fn awaited block bindings require a name, type, and value".into(),
                    );
                }
                let original = symbol(&binding[1], "block binding name")?.to_owned();
                let renamed = nested_await_name(source, next_name);
                let Expr::List(items) = statement else {
                    unreachable!()
                };
                items[1] = Expr::Symbol(renamed.clone());
                renamed_prefixes.push((original, renamed));
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
            source,
            next_name,
            waker,
        );
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
        let normalized_await = Expr::List(
            std::iter::once(Expr::Symbol("#await".into()))
                .chain(await_form[2..].iter().cloned())
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
                    source,
                    next_name,
                    waker,
                )?;
            }
        }
    }
    if has_await(expression) {
        let conditional = if let Some((protocol, task)) = conditional_await(expression)? {
            Some((protocol, task, None))
        } else {
            conditional_await_with_immediate(expression, source, next_name, waker)?
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
                        source,
                        next_name,
                        waker,
                    )?;
                }
                return Ok(());
            };
            if contains_await && head == "#loop" {
                return Err(
                    "@async-fn cannot lower #await inside #loop yet; supported #while, #for-range, and existing-counter #for forms preserve loop-carried suspension state".into(),
                );
            }
            if matches!(head.as_str(), "#if" | "#match" | "#block") && contains_await {
                return Err(format!(
                    "@async-fn awaits inside #if/#match/#block are not lowered yet"
                ));
            }
            match head.as_str() {
                "#quote" | "quote" | "#quasiquote" | "quasiquote" => return Ok(()),
                "#call" | "call" if items.len() == 3 => {
                    if let Expr::List(arguments) = &mut items[2] {
                        for argument in arguments {
                            if let Expr::List(pair) = argument {
                                if let Some(value) = pair.get_mut(1) {
                                    extract_nested_awaits(
                                        value,
                                        generated,
                                        generated_helpers,
                                        source,
                                        next_name,
                                        waker,
                                    )?;
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
                                    extract_nested_awaits(
                                        value,
                                        generated,
                                        generated_helpers,
                                        source,
                                        next_name,
                                        waker,
                                    )?;
                                }
                            }
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
                    for item in items.iter_mut().skip(start) {
                        extract_nested_awaits(
                            item,
                            generated,
                            generated_helpers,
                            source,
                            next_name,
                            waker,
                        )?;
                    }
                }
                _ => {
                    for item in items.iter_mut().skip(1) {
                        extract_nested_awaits(
                            item,
                            generated,
                            generated_helpers,
                            source,
                            next_name,
                            waker,
                        )?;
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

fn extract_statement_awaits(
    statement: &mut Expr,
    generated: &mut Vec<Expr>,
    generated_helpers: &mut Vec<String>,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<(), String> {
    if !has_await(statement) {
        return Ok(());
    }
    if let Some(items) = form(statement, "#let")
        .or_else(|| form(statement, "#let-mut"))
        .or_else(|| form(statement, "let"))
        .or_else(|| form(statement, "let-mut"))
    {
        if let Some(await_form) = form(&items[3], "#await") {
            if await_form.len() == 6 && has_await(&await_form[5]) {
                let Expr::List(statement_items) = statement else {
                    unreachable!()
                };
                let Expr::List(await_items) = &mut statement_items[3] else {
                    unreachable!()
                };
                extract_nested_awaits(
                    &mut await_items[5],
                    generated,
                    generated_helpers,
                    source,
                    next_name,
                    waker,
                )?;
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
            source,
            next_name,
            waker,
        )?;
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
            source,
            next_name,
            waker,
        )?;
    } else {
        extract_nested_awaits(
            statement,
            generated,
            generated_helpers,
            source,
            next_name,
            waker,
        )?;
    }
    Ok(())
}

/// Lower a while loop with one await binding per iteration into a concrete
/// child task. Its poll helper runs ready iterations in a normal Lim loop and
/// stores the current captures plus child task only when the child is pending.
fn lower_async_while_let_body_await(
    items: &[Expr],
    condition_await: &[Expr],
    condition_helper: &str,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &Expr,
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
        (await_form.to_vec(), String::new())
    } else if let Some((protocol, task, helper)) =
        conditional_await_with_immediate(&body_form[3], source, next_name, waker)?
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
    let body_child = expression_source(&body_await[2])?;
    let body_pending = symbol(&body_await[3], "while-let body Pending variant")?;
    let body_ready = symbol(&body_await[4], "while-let body Ready variant")?;
    let body_poll = symbol(&body_await[5], "while-let body poll function")?;
    let body_task = expression_source(&body_await[6])?;
    let body_result_type = body_binding.ty.as_str();
    let capture_types = captures
        .iter()
        .map(|capture| capture.ty.as_str())
        .collect::<Vec<_>>();
    let capture_names = captures
        .iter()
        .map(|capture| capture.name.as_str())
        .collect::<Vec<_>>();
    let scrutinee_fields = std::iter::once(condition_child.as_str())
        .chain(capture_types.iter().copied())
        .collect::<Vec<_>>()
        .join(" ");
    let body_fields = [scrutinee_type.as_str(), body_child.as_str()]
        .into_iter()
        .chain(capture_types.iter().copied())
        .collect::<Vec<_>>()
        .join(" ");
    let capture_pattern = capture_names.join(" ");
    let scrutinee_pattern = if capture_pattern.is_empty() {
        "child".to_owned()
    } else {
        format!("child {capture_pattern}")
    };
    let body_pattern = if capture_pattern.is_empty() {
        "scrutinee child".to_owned()
    } else {
        format!("scrutinee child {capture_pattern}")
    };
    let scrutinee_pending_state = std::iter::once(format!("{wait_scrutinee} pending"))
        .chain(capture_names.iter().map(|name| (*name).to_owned()))
        .collect::<Vec<_>>()
        .join(" ");
    let body_pending_state = std::iter::once(format!("{wait_body} scrutinee pending"))
        .chain(capture_names.iter().map(|name| (*name).to_owned()))
        .collect::<Vec<_>>()
        .join(" ");
    let composite_helper = format!(
        "(#enum {decision_type} ({stop_variant} ({continue_variant} {scrutinee_type} {body_result_type})))\n\
         (#enum {composite_task} (({wait_scrutinee} {scrutinee_fields}) ({wait_body} {body_fields})))\n\
         (#linear {composite_task})\n\
         (#enum {composite_result} (({composite_pending} {composite_task}) ({composite_ready} {decision_type})))\n\
         (#fn {composite_poll} ((task {composite_task}) (waker (#ref {waker}))) {composite_result}\n\
           (#return (#match task\n\
             (#case ({wait_scrutinee} {scrutinee_pattern})\n\
               (#match (#call {condition_poll} (: task child : waker waker))\n\
                 (#case ({condition_pending} pending) ({composite_pending} ({scrutinee_pending_state})))\n\
                 (#case ({condition_ready} scrutinee)\n\
                   (#match scrutinee\n\
                     (#case {pattern}\n\
                       (#match (#call {body_poll} (: task {body_task} : waker waker))\n\
                         (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                         (#case ({body_ready} value) ({composite_ready} ({continue_variant} scrutinee value)))))\n\
                     (#case _ ({composite_ready} {stop_variant}))))))\n\
             (#case ({wait_body} {body_pattern})\n\
               (#match (#call {body_poll} (: task child : waker waker))\n\
                 (#case ({body_pending} pending) ({composite_pending} ({body_pending_state})))\n\
                 (#case ({body_ready} value) ({composite_ready} ({continue_variant} scrutinee value))))))))"
    );

    let decision_name = fresh_async_name(source, next_name);
    let stopped_name = fresh_async_name(source, next_name);
    let body_stopped_name = fresh_async_name(source, next_name);
    let scrutinee_name = fresh_async_name(source, next_name);
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
    let matched = Expr::List(vec![
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
    ]);
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
                Expr::Symbol(scrutinee_name),
                Expr::Symbol(body_value_name),
            ]),
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
    let Some((replacement, loop_helper, renames)) = lower_async_loop(
        &loop_form,
        known,
        known_order,
        following,
        return_value,
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
    return_value: &Expr,
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
        if has_await(&items[2]) {
            let (await_form, conditional_helper) = if let Some(await_form) =
                form(&items[2], "#await")
            {
                (await_form.to_vec(), String::new())
            } else if let Some((protocol, task, helper)) =
                conditional_await_with_immediate(&items[2], source, next_name, waker)?
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
                        "@async-fn #while-let requires a direct #await or conditional #if with a direct #await branch".into(),
                    );
            };
            if await_form.len() != 7 {
                return Err(
                    "@async-fn #while-let requires an explicitly typed #await value".into(),
                );
            }
            parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
            if items[3..].iter().any(has_await) {
                return lower_async_while_let_body_await(
                    items,
                    &await_form,
                    &conditional_helper,
                    known,
                    known_order,
                    following,
                    return_value,
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
            let Some((replacement, helper, renames)) = lower_async_loop(
                &loop_form,
                known,
                known_order,
                following,
                return_value,
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
        return Err("@async-fn #while-let with suspension requires an awaited scrutinee".into());
    }
    let Some(items) = form(statement, "#while") else {
        return Ok(None);
    };
    if items.len() < 3 {
        return Err("@async-fn awaited #while requires a condition and body".into());
    }
    let condition = &items[1];
    if has_await(condition) {
        let (await_form, condition_helper) = if let Some(await_form) = form(condition, "#await") {
            (await_form.to_vec(), String::new())
        } else if let Some((protocol, task, helper)) =
            conditional_await_with_immediate(condition, source, next_name, waker)?
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
        if await_form.len() != 6 {
            return Err(
                "@async-fn awaited #while condition requires (#await Child Pending Ready poll task)"
                    .into(),
            );
        }
        let body = &items[2..];
        if body.iter().any(has_await) {
            if body.is_empty() || body[1..].iter().any(has_await) {
                return Err(
                    "@async-fn an awaited #while condition can be composed with one direct body await binding"
                        .into(),
                );
            }
            let body_binding = binding(&body[0], "awaited while body")?;
            let body_form = form(&body[0], "#let")
                .or_else(|| form(&body[0], "#let-mut"))
                .ok_or_else(|| {
                    "@async-fn awaited while body suspension requires a direct binding".to_owned()
                })?;
            let (body_await, body_helper) = if let Some(await_form) = form(&body_form[3], "#await")
            {
                (await_form.to_vec(), String::new())
            } else if let Some((protocol, task, helper)) =
                conditional_await_with_immediate(&body_form[3], source, next_name, waker)?
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
                    "@async-fn awaited while body binding requires a direct or conditional #await"
                        .into(),
                );
            };
            if body_await.len() != 7
                || body[1..].iter().any(has_await)
                || has_await(&body_await[6])
                || has_await(&await_form[5])
            {
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
                if !async_task_capture_is_copy(&ty) {
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
            let condition_fields = std::iter::once(condition_child.as_str())
                .chain(capture_types.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let body_fields = std::iter::once(body_child.as_str())
                .chain(capture_types.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let condition_pattern = std::iter::once("child")
                .chain(capture_names.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let body_pattern = std::iter::once("child")
                .chain(capture_names.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            let condition_pending_state = std::iter::once(format!("{wait_condition} pending"))
                .chain(capture_names.iter().map(|name| (*name).to_owned()))
                .collect::<Vec<_>>()
                .join(" ");
            let body_pending_state = std::iter::once(format!("{wait_body} pending"))
                .chain(capture_names.iter().map(|name| (*name).to_owned()))
                .collect::<Vec<_>>()
                .join(" ");
            let composite_helper = format!(
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
            );

            let decision_name = fresh_async_name(source, next_name);
            let stopped_name = fresh_async_name(source, next_name);
            let body_stopped_name = fresh_async_name(source, next_name);
            let payload_name = fresh_async_name(source, next_name);
            let body_binding_head = if body_binding.mutable {
                "#let-mut"
            } else {
                "#let"
            };
            let mut body_success = vec![Expr::Symbol("#block".into())];
            body_success.push(Expr::List(vec![
                Expr::Symbol(body_binding_head.into()),
                Expr::Symbol(body_binding.name),
                Expr::Symbol(body_binding.ty),
                Expr::Symbol(payload_name.clone()),
            ]));
            body_success.push(Expr::List(vec![
                Expr::Symbol("#let-mut".into()),
                Expr::Symbol(body_stopped_name.clone()),
                Expr::Symbol("bool".into()),
                Expr::Symbol("false".into()),
            ]));
            body_success.extend(body[1..].iter().cloned());
            if body_success.len() > 3
                && contains_loop_control(body_success.last().expect("body has a stop local"))
            {
                rewrite_while_let_terminal(
                    body_success.last_mut().expect("body has a stop local"),
                    &body_stopped_name,
                )?;
            }
            body_success.push(Expr::Symbol(body_stopped_name));
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
                    Expr::List(body_success),
                ]),
            ]);
            let mut condition_state = vec![Expr::Symbol(wait_condition), await_form[5].clone()];
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
            let Some((replacement, loop_helper, renames)) = lower_async_loop(
                &loop_form,
                known,
                known_order,
                following,
                return_value,
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
        let Some((replacement, helper, renames)) = lower_async_loop(
            &Expr::List(loop_form),
            known,
            known_order,
            following,
            return_value,
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
            if suffix_names.contains(&first_binding.name) {
                return Err(format!(
                    "@async-fn first loop await result '{}' cannot be used after the second await",
                    first_binding.name
                ));
            }

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
            let second_poll_from_first = format!(
                "(#match (#call {second_poll} (: task {second_task} : waker waker))\n\
                   (#case ({second_pending} pending) ({sequence_pending} ({wait_second} pending)))\n\
                   (#case ({second_ready} value) ({sequence_ready} value)))"
            );
            let second_poll_again = format!(
                "(#match (#call {second_poll} (: task child : waker waker))\n\
                   (#case ({second_pending} pending) ({sequence_pending} ({wait_second} pending)))\n\
                   (#case ({second_ready} value) ({sequence_ready} value)))"
            );
            let uses_first_result = second_task_names.contains(&first_binding.name)
                || middle_names.contains(&first_binding.name);
            let first_ready_continuation = if uses_first_result {
                format!("(#block {middle_source} {second_poll_from_first})")
            } else {
                format!(
                    "(#block (#forget {first_result}) {middle_source} {second_poll_from_first})"
                )
            };
            let sequence_helper = format!(
                "(#enum {sequence_task} (({wait_first} {first_child_type}) ({wait_second} {second_child_type})))\n\
                 (#linear {sequence_task})\n\
                 (#enum {sequence_result} (({sequence_pending} {sequence_task}) ({sequence_ready} {second_result_type})))\n\
                 (#fn {sequence_poll} ((task {sequence_task}) (waker (#ref {waker}))) {sequence_result}\n\
                   (#return (#match task\n\
                     (#case ({wait_first} child)\n\
                       (#match (#call {first_poll} (: task child : waker waker))\n\
                         (#case ({first_pending} pending) ({sequence_pending} ({wait_first} pending)))\n\
                         (#case ({first_ready} {first_result}) {first_ready_continuation})))\n\
                     (#case ({wait_second} child) {second_poll_again}))))"
            );

            let mut rewritten = statement.clone();
            let Expr::List(loop_items) = &mut rewritten else {
                unreachable!()
            };
            let first_global_index = first_index + 2;
            let second_global_index = second_index + 2;
            loop_items.drain(first_global_index..second_global_index);
            let Expr::List(second_binding_form) = &mut loop_items[first_global_index] else {
                unreachable!()
            };
            second_binding_form[3] = Expr::List(vec![
                Expr::Symbol("#await".into()),
                Expr::Symbol(sequence_task),
                Expr::Symbol(sequence_pending),
                Expr::Symbol(sequence_ready),
                Expr::Symbol(sequence_poll),
                Expr::List(vec![Expr::Symbol(wait_first), first_await[5].clone()]),
            ]);
            let Some((replacement, helper, renames)) = lower_async_while(
                &rewritten,
                known,
                known_order,
                following,
                return_value,
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
        conditional_await_with_immediate(&binding_form[3], source, next_name, waker)?
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
    if suffix.iter().any(|expression| {
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
    for expression in suffix {
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
    collect_value_names(condition, &mut used_names);
    collect_value_names(&await_form[5], &mut used_names);
    for expression in prefix.iter().chain(suffix) {
        collect_value_names(expression, &mut used_names);
    }
    let captures = known_order
        .iter()
        .filter(|name| used_names.contains(name.as_str()))
        .filter_map(|name| known.get(name).cloned())
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
    let (output_type_source, ready_type, ready_value) = if output_captures.is_empty() {
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
    let task_run = format!("{base}-run");
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
    let active_pattern_names = captures
        .iter()
        .enumerate()
        .map(|(index, _)| format!("{base}-active-{index}"))
        .collect::<Vec<_>>();
    let active_local_bindings = captures
        .iter()
        .zip(&active_pattern_names)
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
    let capture_arguments = named_arguments(&captures);
    let start_variant = if capture_types.is_empty() {
        task_start.clone()
    } else {
        format!("({task_start} {capture_types})")
    };
    let wait_fields = if capture_types.is_empty() {
        child_type.clone()
    } else {
        format!("{capture_types} {child_type}")
    };
    let wait_variant = format!("({task_wait} {wait_fields})");
    let start_pattern = if capture_names.is_empty() {
        task_start.clone()
    } else {
        format!("({task_start} {capture_names})")
    };
    let wait_pattern = if capture_names.is_empty() {
        format!("({task_wait} {base}-child)")
    } else {
        format!("({task_wait} {capture_names} {base}-child)")
    };
    let task_wait_with_child = if capture_names.is_empty() {
        format!("({task_wait} {base}-child-state)")
    } else {
        format!("({task_wait} {capture_names} {base}-child-state)")
    };
    let run_parameter_names = captures
        .iter()
        .enumerate()
        .map(|(index, _)| format!("{base}-input-{index}"))
        .collect::<Vec<_>>();
    let mut run_parameters = captures
        .iter()
        .zip(&run_parameter_names)
        .map(|(binding, name)| {
            format!(
                "({}{name} {})",
                if binding.mutable { "#mut " } else { "" },
                binding.ty
            )
        })
        .collect::<Vec<_>>();
    run_parameters.push(format!("(waker (#ref {waker}))"));
    let run_parameters = run_parameters.join(" ");
    let mut resume_parameters = captures.iter().map(parameter).collect::<Vec<_>>();
    let result_parameter = if await_binding.mutable {
        format!("(#mut {base}-result {})", await_binding.ty)
    } else {
        format!("({base}-result {})", await_binding.ty)
    };
    resume_parameters.push(result_parameter);
    resume_parameters.push(format!("(waker (#ref {waker}))"));
    let resume_parameters = resume_parameters.join(" ");
    let call_run = run_parameter_names
        .iter()
        .zip(captures.iter())
        .map(|(parameter, binding)| format!(": {parameter} {}", binding.name))
        .chain(std::iter::once(": waker waker".to_owned()))
        .collect::<Vec<_>>()
        .join(" ");
    let call_run = format!("({call_run})");
    let initial_active_values = run_parameter_names.join(" ");
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
    let active_value = if initial_active_values.is_empty() {
        format!("{base}-active")
    } else {
        format!("({base}-active {initial_active_values})")
    };
    let active_value_from_captures = if capture_names.is_empty() {
        format!("{base}-active")
    } else {
        format!("({base}-active {capture_names})")
    };
    let run_state = format!("{base}-run-state");
    let run_state_pending = format!("{base}-run-pending");
    let run_state_ready = format!("{base}-run-ready");
    let run_state_pending_pattern = format!("({run_state_pending} {base}-pending-task)");
    let run_state_ready_pattern = format!("({run_state_ready} {base}-ready-value)");
    let call_resume = {
        let mut arguments = capture_arguments;
        if !arguments.is_empty() {
            arguments.push(' ');
        }
        arguments.push_str(&format!(": {base}-result {base}-result : waker waker"));
        format!("({arguments})")
    };
    let loop_condition = expression_source(condition)?;
    let prefix_source = prefix
        .iter()
        .map(expression_source)
        .collect::<Result<Vec<_>, _>>()?
        .join(" ");
    let suffix_source = suffix
        .iter()
        .map(expression_source)
        .collect::<Result<Vec<_>, _>>()?
        .join(" ");
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
                   (#block
                     {active_local_bindings}
                     (#if {loop_condition}
                       (#block
                         {prefix_source}
                         (#let {base}-child {child_type} {child_task})
                         (#match {child_poll_call}
                           (#case ({child_pending} {base}-child-state)
                             (#block
                               (#set {base}-stopped true)
                               ({run_state_pending} {task_wait_with_child})))
                           (#case ({child_ready} {base}-result)
                             (#block
                               ({await_let} {await_name} {await_type} {base}-result)
                               {suffix_source}
                               {active_value_from_captures}))))
                       (#block
                         (#set {base}-stopped true)
                         ({run_state_ready} {ready_value})))))
                 (#case {run_state_pending_pattern} (#unreachable))
                 (#case {run_state_ready_pattern} (#unreachable)))))
           (#return (#match {base}-outcome
             (#case {run_state_pending_pattern} ({task_pending} {base}-pending-task))
             (#case {run_state_ready_pattern} ({task_ready} {base}-ready-value))
             (#case {active_pattern} (#unreachable)))))
         (#fn {task_resume} ({resume_parameters}) {task_poll_result}
           ({await_let} {await_name} {await_type} {base}-result)
           {suffix_source}
           (#return (#call {task_run} {call_run})))
         (#fn {task_poll} ((task {task_type}) (waker (#ref {waker}))) {task_poll_result}
           (#return (#match task
             (#case {start_pattern} (#call {task_run} {call_run}))
             (#case {wait_pattern}
               (#match {child_poll_call}
                 (#case ({child_pending} {base}-child-state)
                   ({task_pending} {task_wait_with_child}))
                 (#case ({child_ready} {base}-result)
                   (#call {task_resume} {call_resume})))))))",
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
            if output_captures.is_empty() {
                Expr::List(Vec::new())
            } else {
                Expr::Symbol(output_type)
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
    let mut renamed_outputs = Vec::new();
    for binding in &output_captures {
        let resumed_name = fresh_async_name(source, next_name);
        replacement.push(Expr::List(vec![
            Expr::Symbol(if binding.mutable { "#let-mut" } else { "#let" }.into()),
            Expr::Symbol(resumed_name.clone()),
            Expr::Symbol(binding.ty.clone()),
            Expr::List(vec![
                Expr::Symbol("#get".into()),
                Expr::Symbol(result_variable.clone()),
                Expr::Symbol(binding.name.clone()),
            ]),
        ]));
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
            source,
            next_name,
            waker,
        )?;
        extract_nested_awaits(
            &mut end,
            &mut generated,
            &mut generated_helpers,
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
    let mut while_items = vec![Expr::Symbol("#while".into()), condition, iteration_binding];
    while_items.extend(items[4..].iter().cloned());
    while_items.push(increment);
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
    let Some((mut replacement, helper, renames)) = lower_async_while(
        &lowered_loop,
        &loop_known,
        &loop_order,
        following,
        return_value,
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
fn lower_async_for(
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
    let Some(items) = form(statement, "#for") else {
        return Ok(None);
    };
    if items.len() < 5 {
        return Err("@async-fn #for await requires init, condition, step, and body".into());
    }
    let initializer = &items[1];
    let awaited_condition = has_await(&items[2]);
    let awaited_step = has_await(&items[3]);
    let awaited_initializer = has_await(initializer);
    let mut initializer_prefix = Vec::new();
    let mut initializer_helpers = Vec::new();
    let mut initializer_value = None;
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
    let mut initializer_statement = initializer.clone();
    let mut condition = items[2].clone();
    let mut condition_helpers = Vec::new();
    if awaited_condition && form(&condition, "#await").is_none() {
        let Some((protocol, task, helper)) =
            conditional_await_with_immediate(&condition, source, next_name, waker)?
        else {
            return Err(
                "@async-fn #for condition requires a direct #await or conditional #if with a direct #await branch".into(),
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
    if awaited_step && awaited_condition {
        return Err("@async-fn #for cannot suspend in both its condition and step yet".into());
    }
    if awaited_step && loop_body.iter().any(has_await) {
        return Err("@async-fn #for cannot suspend in both its body and step yet".into());
    }
    if awaited_condition && loop_body.iter().any(has_await) {
        return Err("@async-fn #for condition and body cannot both suspend yet".into());
    }
    if form(initializer, "#let-else").is_some() {
        return Err("@async-fn #for await does not support #let-else initializers".into());
    }
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
                if await_form.len() != 6 {
                    return Err(
                        "@async-fn awaited #for step assignment requires (#await Child Pending Ready poll task)".into(),
                    );
                }
                Expr::List(await_form.to_vec())
            } else {
                let mut value = set[2].clone();
                extract_nested_awaits(
                    &mut value,
                    &mut step_prefix,
                    &mut step_helpers,
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
    } else {
        loop_body.extend(step_prefix);
        loop_body.push(step.clone());
        loop_body.extend(post_step);
    }
    let mut while_items = vec![Expr::Symbol("#while".into()), condition];
    while_items.extend(loop_body);
    let lowered_loop = Expr::List(while_items);
    let Some((mut replacement, helper, renames)) = lower_async_while(
        &lowered_loop,
        &loop_known,
        &loop_order,
        following,
        return_value,
        source,
        next_name,
        waker,
    )?
    else {
        return Err("@async-fn failed to lower awaited #for".into());
    };
    let initializer_prefix_len = initializer_prefix.len();
    replacement.splice(0..0, initializer_prefix);
    if !matches!(initializer, Expr::List(items) if items.is_empty()) {
        replacement.insert(initializer_prefix_len, initializer_statement);
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
    Ok(Some((replacement, helper, renames)))
}

fn contains_loop_control(expression: &Expr) -> bool {
    match expression {
        Expr::List(items) => {
            matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#break" | "#continue"))
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

fn contains_return(expression: &Expr) -> bool {
    match expression {
        Expr::List(items) => {
            matches!(items.first(), Some(Expr::Symbol(head)) if head == "#return")
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
            Expr::Symbol("#set".into()),
            Expr::Symbol(stopped.into()),
            Expr::Symbol("false".into()),
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
            if contains_loop_control(branch) {
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
                    contains_loop_control(&case[body_index]),
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
    if !has_await(statement) {
        return Ok(None);
    }
    let Some(items) = form(statement, "#loop") else {
        return Ok(None);
    };
    if items.len() < 2 {
        return Err("@async-fn awaited #loop requires a body".into());
    }
    let done = fresh_async_name(source, next_name);
    let mut body = items[1..].to_vec();
    let Some(last) = body.last_mut() else {
        return Err("@async-fn awaited #loop requires a body".into());
    };
    let has_terminal_control = rewrite_terminal_loop_control(last, &done)?;
    if !has_terminal_control {
        return Err(
            "@async-fn awaited #loop requires a terminal #break or #continue after suspension"
                .into(),
        );
    }
    if body[..body.len() - 1].iter().any(contains_loop_control) {
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
    let Some((mut replacement, helper, renames)) = lower_async_while(
        &lowered_loop,
        &loop_known,
        &loop_order,
        following,
        return_value,
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
    let invocation = list(invocation, "invocation")?;
    let pinned =
        matches!(&invocation.get(1), Some(Expr::Symbol(name)) if name == "async-fn-pinned");
    let generator_name = if pinned {
        "@async-fn-pinned"
    } else {
        "@async-fn"
    };
    if invocation.len() != 5
        || !matches!(invocation[0], Expr::At)
        || !matches!(&invocation[1], Expr::Symbol(name) if name == "async-fn" || name == "async-fn-pinned")
    {
        return Err(format!("{generator_name} requires (@{} (: names (Frame Poll Pending Ready poll) : waker Waker : function (#fn name ((arg Type) ...) Result ...)))", generator_name.trim_start_matches('@')).into());
    }
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
    let body = &function[4..];
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
    let return_await = form(&last[1], "#await").map(<[Expr]>::to_vec);
    let mut return_value = last[1].clone();
    let source = expression_source(&invocation[4])?;
    let waker_source = expression_source(&invocation[3])?;
    let mut statements = body[..body.len() - 1].to_vec();
    let mut next_nested_await = 0;
    let mut generated_helpers = Vec::new();
    let mut lowered_statements = Vec::new();
    let mut lowering_known = known.clone();
    let mut lowering_known_order = known_order.clone();
    for source_index in 0..statements.len() {
        let mut statement = statements[source_index].clone();
        let following = statements[source_index + 1..].to_vec();
        if let Some((replacement, helper, renames)) = lower_async_loop(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &following,
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )? {
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
        if let Some((replacement, helper, renames)) = lower_async_for(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &following,
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )? {
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
        )? {
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
        if let Some((replacement, helper, renames)) = lower_async_while(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &following,
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )? {
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
            &source,
            &mut next_nested_await,
            &waker_source,
        )?;
        lowered_statements.extend(generated);
        lowered_statements.push(statement.clone());
        if let Ok(local) = binding(&statement, "source local") {
            lowering_known_order.push(local.name.clone());
            lowering_known.insert(local.name.clone(), local);
        }
    }
    statements = lowered_statements;
    if let Some(await_expression) = &return_await {
        statements.push(Expr::List(vec![
            Expr::Symbol("#let".into()),
            Expr::Symbol("lim.async.return-value".into()),
            function[3].clone(),
            Expr::List(await_expression.clone()),
        ]));
    } else {
        let mut generated = Vec::new();
        extract_nested_awaits(
            &mut return_value,
            &mut generated,
            &mut generated_helpers,
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
                .is_some()
            {
                let mut local = binding(statement, "between #await forms")?;
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
        if await_form.len() != 6 {
            return Err(
                "#await requires (#await ChildTask Pending Ready poll task-expression)".into(),
            );
        }
        if known.contains_key(&local.name) {
            return Err(format!("@async-fn duplicate binding '{}'", local.name));
        }
        let child = expression_source(&await_form[1])?;
        parse_type(Some(&normalize_keywords(await_form[1].clone())))?;
        let value = expression_source(&await_form[5])?;
        if has_await(&await_form[5]) {
            return Err("@async-fn nested #await is not supported".into());
        }
        stages.push(Stage {
            prefix: std::mem::take(&mut prefix),
            source_index,
            available: known_order.clone(),
            captures: Vec::new(),
            binding: local,
            child,
            pending: symbol(&await_form[2], "child Pending variant")?.to_owned(),
            ready: symbol(&await_form[3], "child Ready variant")?.to_owned(),
            poll: symbol(&await_form[4], "child poll function")?.to_owned(),
            value,
        });
        let local = &stages.last().unwrap().binding;
        known.insert(local.name.clone(), local.clone());
        known_order.push(local.name.clone());
        if stages.len() > 32 {
            return Err("@async-fn supports at most 32 suspension points".into());
        }
    }
    if stages.is_empty() {
        return Err(
            "@async-fn requires at least one top-level (#let name Type (#await ...))".into(),
        );
    }
    for stage in &mut stages {
        let mut live = HashSet::new();
        for statement in &statements[stage.source_index + 1..] {
            collect_value_names(statement, &mut live);
        }
        if return_await.is_none() {
            collect_value_names(&return_value, &mut live);
        }
        stage.captures = stage
            .available
            .iter()
            .filter(|name| live.contains(name.as_str()))
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
            format!(
                "{} (#return (#call {poll}-child-{} ({} : lim.async.task {} : waker waker)))",
                next.prefix.join(" "),
                index + 1,
                named_arguments(&next.captures),
                next.value
            )
        } else {
            format!("{} (#return ({ready} {returned}))", prefix.join(" "))
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
    let generated = format!(
        "{}\n{}
         (#enum {poll_result} (({pending} {frame_state}) ({ready} {result})))
         {}
         (#fn {start_helper} ({} (waker (#ref {waker})) {self_reference_parameter_suffix}) {poll_result}
           {}
           (#return (#call {poll}-child-0 ({} : lim.async.task {} : waker waker))))
         {poll_function}",
        generated_helpers.join("\n"),
        frame_declarations,
        helpers.join("\n"),
        signature(&start_params),
        first_prefix,
        named_arguments(&first.captures),
        first.value,
    );
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
                "#await" => {
                    if let Some(value) = items.get(5) {
                        collect_value_names(value, names);
                    }
                }
                "#let" | "#let-mut" | "let" | "let-mut" if items.len() >= 4 => {
                    collect_value_names(&items[3], names);
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
                    rename_async_value(&mut items[5], from, to);
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
