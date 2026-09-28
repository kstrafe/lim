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

#[derive(Clone, PartialEq)]
struct AwaitProtocol {
    result_type: Expr,
    child_type: Expr,
    pending: Expr,
    ready: Expr,
    poll: Expr,
}

fn conditional_await(expression: &Expr) -> Result<Option<(AwaitProtocol, Expr)>, String> {
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
            return Err(
                "conditional #await branches must use the same result type, child type, variants, and poll function".into(),
            );
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
        let mut protocol = None;
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
                return Err(
                    "conditional #await branches must use the same result type, child type, variants, and poll function".into(),
                );
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
            .is_some_and(|branch_protocol| branch_protocol != &protocol)
    }) {
        return Err(
            "conditional #await branches must use the same result type, child type, variants, and poll function".into(),
        );
    }
    if branches
        .iter()
        .all(|(branch_protocol, _)| branch_protocol.is_some())
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
    let child_type = expression_source(&protocol.child_type)?;
    let result_type = expression_source(&protocol.result_type)?;
    let child_pending = expression_source(&protocol.pending)?;
    let child_ready = expression_source(&protocol.ready)?;
    let child_poll = expression_source(&protocol.poll)?;
    let helper = format!(
        "(#enum {choice_task} (({choice_wait} {child_type}) ({choice_done} {result_type})))\n\
         (#linear {choice_task})\n\
         (#enum {choice_poll_result} (({choice_pending} {choice_task}) ({choice_ready} {result_type})))\n\
         (#fn {choice_poll} ((task {choice_task}) (waker (#ref {waker}))) {choice_poll_result}\n\
           (#return (#match task\n\
             (#case ({choice_wait} child)\n\
               (#match (#call {child_poll} (: task child : waker waker))\n\
                 (#case ({child_pending} pending) ({choice_pending} ({choice_wait} pending)))\n\
                 (#case ({child_ready} value) ({choice_ready} value))))\n\
             (#case ({choice_done} value) ({choice_ready} value)))))"
    );
    let wrap = |protocol: Option<AwaitProtocol>, value: Expr| -> Expr {
        let constructor = if protocol.is_some() {
            &choice_wait
        } else {
            &choice_done
        };
        Expr::List(vec![Expr::Symbol(constructor.clone()), value])
    };
    let selected = if is_if {
        let then_branch = wrap(branches[0].0.clone(), branches[0].1.clone());
        let else_branch = wrap(branches[1].0.clone(), branches[1].1.clone());
        Expr::List(vec![
            Expr::Symbol("#if".into()),
            condition_or_scrutinee,
            then_branch,
            else_branch,
        ])
    } else {
        let mut items = vec![Expr::Symbol("#match".into()), condition_or_scrutinee];
        for (branch_protocol, branch) in branches {
            let Expr::List(mut case) = branch else {
                unreachable!()
            };
            let value = case.pop().expect("case body");
            case.push(wrap(branch_protocol, value));
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
    if is_control_flow_statement(statement) {
        return Err("@async-fn awaits inside #if/#match/#block are not lowered yet".into());
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
    for mut statement in statements {
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
        lowered_statements.push(statement);
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
                return Err(format!(
                    "@async-fn between #await forms supports explicit bindings, mutable assignments, #deref-set, and #if/#match/#block forms: {statement:?}"
                ));
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
