//! Syntactic lowering for concrete async functions with inferred live captures.
//!
//! This deliberately emits ordinary Lim declarations before type and borrow
//! checking. No suspension point can hide a reference from those passes.

use std::collections::{HashMap, HashSet};

use crate::{expression_source, normalize_keywords, parse_type, Expr};

#[derive(Clone)]
struct Binding {
    name: String,
    ty: String,
    mutable: bool,
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
    let binding = form(&block[await_binding_index], "#let")?;
    if binding.len() != 4 {
        return None;
    }
    let binding_name = symbol(&binding[1], "binding name").ok()?;
    if !matches!(&block[block.len() - 1], Expr::Symbol(name) if name == binding_name) {
        return None;
    }
    let await_form = form(&binding[3], "#await")?;
    if await_form.len() != 6 {
        return None;
    }
    let task = if await_binding_index == 1 {
        await_form[5].clone()
    } else {
        let mut task_block = vec![Expr::Symbol("#block".into())];
        task_block.extend(block[1..await_binding_index].iter().cloned());
        task_block.push(await_form[5].clone());
        Expr::List(task_block)
    };
    Some(Expr::List(vec![
        Expr::Symbol("#await".into()),
        binding[2].clone(),
        await_form[1].clone(),
        await_form[2].clone(),
        await_form[3].clone(),
        await_form[4].clone(),
        task,
    ]))
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
            if case.len() != 3 {
                return Ok(None);
            }
            let Some((case_protocol, task)) = conditional_await(&case[2])? else {
                return Ok(None);
            };
            if protocol
                .as_ref()
                .is_some_and(|expected| expected != &case_protocol)
            {
                return Ok(None);
            }
            protocol = Some(case_protocol);
            task_arms.push(Expr::List(vec![case[0].clone(), case[1].clone(), task]));
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
            if case.len() != 3 {
                return Ok(None);
            }
            let lowered = conditional_await(&case[2])?;
            if let Some((protocol, task)) = lowered {
                branches.push((
                    Some(protocol),
                    Expr::List(vec![Expr::Symbol("#case".into()), case[1].clone(), task]),
                ));
            } else if !has_await(&case[2]) {
                branches.push((
                    None,
                    Expr::List(vec![
                        Expr::Symbol("#case".into()),
                        case[1].clone(),
                        case[2].clone(),
                    ]),
                ));
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
        if form(&items[3], "#await").is_some() {
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

fn collect_mutated_names(expression: &Expr, names: &mut HashSet<String>) {
    if let Some(name) = mutable_assignment_target(expression) {
        names.insert(name.to_owned());
    }
    if let Expr::List(items) = expression {
        for item in items.iter().skip(1) {
            collect_mutated_names(item, names);
        }
    }
}

/// Lower a while loop with one await binding per iteration into a concrete
/// child task. Its poll helper runs ready iterations in a normal Lim loop and
/// stores the current captures plus child task only when the child is pending.
fn lower_async_while(
    statement: &Expr,
    known: &HashMap<String, Binding>,
    known_order: &[String],
    following: &[Expr],
    return_value: &Expr,
    source: &str,
    next_name: &mut usize,
    waker: &str,
) -> Result<Option<(Vec<Expr>, String)>, String> {
    if !has_await(statement) {
        return Ok(None);
    }
    let Some(items) = form(statement, "#while") else {
        return Ok(None);
    };
    if items.len() < 3 {
        return Err("@async-fn awaited #while requires a condition and body".into());
    }
    let condition = &items[1];
    if has_await(condition) {
        return Err("@async-fn #await in a loop condition is not supported".into());
    }
    let body = &items[2..];
    let await_indices = body
        .iter()
        .enumerate()
        .filter_map(|(index, expression)| has_await(expression).then_some(index))
        .collect::<Vec<_>>();
    if await_indices.len() != 1 {
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
    let await_form = form(&binding_form[3], "#await").ok_or_else(|| {
        "@async-fn loop binding must be initialized directly by #await".to_owned()
    })?;
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
    let mut mutated = HashSet::new();
    for expression in prefix.iter().chain(suffix) {
        collect_mutated_names(expression, &mut mutated);
    }
    collect_mutated_names(&await_form[5], &mut mutated);
    if let Some(name) = captures
        .iter()
        .find(|binding| mutated.contains(&binding.name) && used_after.contains(&binding.name))
    {
        return Err(format!(
            "@async-fn loop mutates '{}' and uses it after the loop; loop-result capture transfer is not supported yet",
            name.name
        ));
    }

    let base = fresh_async_name(source, next_name);
    let task_type = format!("{base}-task");
    let task_start = format!("{base}-start");
    let task_wait = format!("{base}-wait");
    let task_poll_result = format!("{base}-poll-result");
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
    let mut run_parameters = captures.iter().map(parameter).collect::<Vec<_>>();
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
    let call_run = if capture_arguments.is_empty() {
        "(: waker waker)".to_owned()
    } else {
        format!("({capture_arguments} : waker waker)")
    };
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
    let task_source = format!(
        "(#enum {task_type} ({start_variant} {wait_variant}))
         (#linear {task_type})
         (#enum {task_poll_result} (({task_pending} {task_type}) ({task_ready} ())))
         (#fn {task_run} ({run_parameters}) {task_poll_result}
           (#let-mut {base}-outcome {task_poll_result} ({task_ready} ()))
           (#let-mut {base}-stopped bool false)
           (#while (#bool.&& (#bool.== {base}-stopped false) {loop_condition})
             {prefix_source}
             (#let {base}-child {child_type} {child_task})
             (#match {child_poll_call}
               (#case ({child_pending} {base}-child-state)
                 (#block
                   (#forget {base}-outcome)
                   (#set {base}-outcome ({task_pending} {task_wait_with_child}))
                   (#set {base}-stopped true)
                   ()))
               (#case ({child_ready} {base}-result)
                 (#block (#let {} {} {base}-result) {} ()))))
           (#return {base}-outcome))
         (#fn {task_resume} ({resume_parameters}) {task_poll_result}
           ({} {} {} {base}-result)
           {}
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
        await_binding.name,
        await_binding.ty,
        suffix_source,
        if await_binding.mutable {
            "#let-mut"
        } else {
            "#let"
        },
        await_binding.name,
        await_binding.ty,
        suffix_source,
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
            Expr::Symbol(result_variable),
            Expr::List(Vec::new()),
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
    Ok(Some((replacement, task_source)))
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
) -> Result<Option<(Vec<Expr>, String)>, String> {
    if !has_await(statement) {
        return Ok(None);
    }
    let Some(items) = form(statement, "#for-range") else {
        return Ok(None);
    };
    if items.len() < 5 {
        return Err("@async-fn #for-range await requires a binding, bounds, and body".into());
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
    let Some((mut replacement, helper)) = lower_async_while(
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
    Ok(Some((replacement, helper)))
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
) -> Result<Option<(Vec<Expr>, String)>, String> {
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
    if has_await(initializer) || has_await(&items[2]) || has_await(&items[3]) {
        return Err(
            "@async-fn #for await cannot suspend in its initializer, condition, or step".into(),
        );
    }
    let mut loop_known = known.clone();
    let mut loop_order = known_order.to_vec();
    let mut initializer_statement = initializer.clone();
    let mut condition = items[2].clone();
    let mut step = items[3].clone();
    let mut loop_body = items[4..].to_vec();
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
            init_form[3].clone(),
        ]);
    }

    let mut while_items = vec![Expr::Symbol("#while".into()), condition];
    while_items.extend(loop_body);
    while_items.push(step);
    let lowered_loop = Expr::List(while_items);
    let Some((mut replacement, helper)) = lower_async_while(
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
    if !matches!(initializer, Expr::List(items) if items.is_empty()) {
        replacement.insert(0, initializer_statement);
    }
    Ok(Some((replacement, helper)))
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
    for (source_index, mut statement) in statements.iter().cloned().enumerate() {
        if let Some((replacement, helper)) = lower_async_for(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &statements[source_index + 1..],
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )? {
            generated_helpers.push(helper);
            lowered_statements.extend(replacement);
            continue;
        }
        if let Some((replacement, helper)) = lower_async_for_range(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &statements[source_index + 1..],
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )? {
            generated_helpers.push(helper);
            lowered_statements.extend(replacement);
            continue;
        }
        if let Some((replacement, helper)) = lower_async_while(
            &statement,
            &lowering_known,
            &lowering_known_order,
            &statements[source_index + 1..],
            &return_value,
            &source,
            &mut next_nested_await,
            &waker_source,
        )? {
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
                let local = binding(statement, "between #await forms")?;
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
    let reserved = [
        "waker",
        "lim.async.task",
        "lim.async.polled-task",
        "lim.async.child",
        "lim.async.value",
    ];
    if known.keys().any(|name| reserved.contains(&name.as_str())) {
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
    let mut variants = vec![format!("({start_variant} {})", types(&params))];
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
    let start_case = format!(
        "(#case ({start_variant} {}) (#call {start_helper} ({} : waker waker)))",
        arguments(&params),
        named_arguments(&params),
    );
    let generated = format!(
        "{}\n(#enum {frame} ({}))
         (#linear {frame})
         (#enum {poll_result} (({pending} {frame}) ({ready} {result})))
         (#fn {start} ({}) {frame} (#return ({start_variant} {})))
         {}
         (#fn {start_helper} ({} (waker (#ref {waker}))) {poll_result}
           {}
           (#return (#call {poll}-child-0 ({} : lim.async.task {} : waker waker))))
         (#fn {poll} ((task {frame}) (waker (#ref {waker}))) {poll_result}
           (#return (#match task {start_case} {})))",
        generated_helpers.join("\n"),
        variants.join(" "),
        signature(&params),
        arguments(&params),
        helpers.join("\n"),
        signature(&params),
        first.prefix.join(" "),
        named_arguments(&first.captures),
        first.value,
        await_cases.join(" "),
    );
    if !pinned {
        return Ok(generated);
    }
    if source.contains(public_poll_result)
        || source.contains(&format!("({public_pending} "))
        || source.contains(&format!("({public_ready} "))
    {
        return Err(format!(
            "{generator_name} generated poll declarations collide with their input"
        ));
    }
    Ok(format!(
        "{generated}
         (#enum {public_poll_result} (({public_pending} (#pin-ref-mut {frame})) ({public_ready} {result})))
         (#fn {public_poll} ((task (#pin-ref-mut {frame})) (waker (#ref {waker}))) {public_poll_result}
           (#let state {frame} (#unsafe (#pin-read task)))
           (#let outcome {poll_result} (#call {poll} (: task state : waker waker)))
           (#return (#match outcome
             (#case ({pending} next-state)
               (#block (#unsafe (#pin-write task next-state)) ({public_pending} task)))
             (#case ({ready} value)
               (#block (#unsafe (#pin-write task ({done_variant}))) ({public_ready} value))))))
         (#fn {cancel} ((task (#pin-ref-mut {frame}))) {frame}
           (#let state {frame} (#unsafe (#pin-read task)))
           (#unsafe (#pin-write task ({done_variant})))
           (#return state))",
        public_pending = public_pending,
        public_ready = public_ready,
        public_poll_result = public_poll_result,
        public_poll = public_poll,
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
