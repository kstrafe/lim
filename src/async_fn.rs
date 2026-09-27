//! Syntactic lowering for concrete async functions with explicit captures.
//!
//! This deliberately emits ordinary Lim declarations before type and borrow
//! checking. No suspension point can hide a reference from those passes.

use std::collections::{HashMap, HashSet};

use crate::{expression_source, normalize_keywords, parse_type, Expr};

struct Binding {
    name: String,
    ty: String,
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

fn binding(expr: &Expr, context: &str) -> Result<Binding, String> {
    let items = form(expr, "#let")
        .ok_or_else(|| format!("@async-fn {context} supports only explicit #let bindings"))?;
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
    })
}

fn parameters(expr: &Expr) -> Result<Vec<Binding>, String> {
    list(expr, "function parameters")?
        .iter()
        .map(|parameter| {
            let items = list(parameter, "function parameter")?;
            if items.len() != 2 {
                return Err("@async-fn parameters require (name Type); mutable parameters are not supported yet".into());
            }
            let name = symbol(&items[0], "parameter name")?.to_owned();
            parse_type(Some(&normalize_keywords(items[1].clone())))?;
            Ok(Binding {
                name,
                ty: expression_source(&items[1])?,
            })
        })
        .collect()
}

fn signature(bindings: &[Binding]) -> String {
    bindings
        .iter()
        .map(|binding| format!("({} {})", binding.name, binding.ty))
        .collect::<Vec<_>>()
        .join(" ")
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
        .map(|binding| format!("({} {})", binding.name, binding.name))
        .collect::<Vec<_>>()
        .join(" ")
}

pub(crate) fn generated_source(invocation: &Expr) -> Result<String, String> {
    let invocation = list(invocation, "invocation")?;
    if invocation.len() != 5
        || !matches!(invocation[0], Expr::At)
        || !matches!(&invocation[1], Expr::Symbol(name) if name == "async-fn")
    {
        return Err("@async-fn requires (@async-fn (Frame Poll Pending Ready poll) Waker (#fn name ((arg Type) ...) Result ...))".into());
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
    let [frame, poll_result, pending, ready, poll] = names.as_slice() else {
        unreachable!()
    };
    let waker = expression_source(&invocation[3])?;
    parse_type(Some(&normalize_keywords(invocation[3].clone())))?;
    let function = form(&invocation[4], "#fn")
        .ok_or_else(|| "@async-fn last argument must be a #fn declaration".to_owned())?;
    if function.len() < 6 {
        return Err("@async-fn #fn requires a name, parameters, result type, and body".into());
    }
    let start = symbol(&function[1], "function name")?;
    if start == poll || names.iter().any(|name| name == start) {
        return Err("@async-fn start function must differ from generated names".into());
    }
    let params = parameters(&function[2])?;
    let result = expression_source(&function[3])?;
    parse_type(Some(&normalize_keywords(function[3].clone())))?;
    let mut known = HashMap::new();
    for parameter in &params {
        if known
            .insert(parameter.name.clone(), parameter.ty.clone())
            .is_some()
        {
            return Err(format!("@async-fn duplicate binding '{}'", parameter.name));
        }
    }
    let body = &function[4..];
    let last = form(body.last().unwrap(), "#return")
        .ok_or_else(|| "@async-fn body must end with (#return value)".to_owned())?;
    if last.len() != 2 || has_await(&last[1]) {
        return Err("@async-fn final #return requires one value and no nested #await".into());
    }
    let returned = expression_source(&last[1])?;
    let mut stages = Vec::new();
    let mut prefix = Vec::new();
    for (source_index, statement) in body[..body.len() - 1].iter().enumerate() {
        if !has_await(statement) {
            let local = binding(statement, "between #await forms")?;
            if known.insert(local.name.clone(), local.ty.clone()).is_some() {
                return Err(format!("@async-fn duplicate binding '{}'", local.name));
            }
            prefix.push(expression_source(statement)?);
            continue;
        }
        let local = binding(statement, "#await")?;
        let let_form = form(statement, "#let").unwrap();
        let await_form = form(&let_form[3], "#await").ok_or_else(|| {
            "@async-fn #await must be the entire initializer of a top-level #let".to_owned()
        })?;
        if await_form.len() != 7 {
            return Err("#await requires (#await (captures ...) ChildTask Pending Ready poll task-expression)".into());
        }
        if known.contains_key(&local.name) {
            return Err(format!("@async-fn duplicate binding '{}'", local.name));
        }
        let mut captures = Vec::new();
        let mut captured = HashSet::new();
        for name in list(&await_form[1], "#await captures")? {
            let name = symbol(name, "captured name")?;
            let ty = known.get(name).ok_or_else(|| {
                format!("@async-fn capture '{name}' is not an earlier parameter or #let")
            })?;
            if !captured.insert(name) {
                return Err(format!("@async-fn duplicate capture '{name}'"));
            }
            captures.push(Binding {
                name: name.to_owned(),
                ty: ty.clone(),
            });
        }
        let child = expression_source(&await_form[2])?;
        parse_type(Some(&normalize_keywords(await_form[2].clone())))?;
        let value = expression_source(&await_form[6])?;
        if has_await(&await_form[6]) {
            return Err("@async-fn nested #await is not supported".into());
        }
        let mut available = known.keys().cloned().collect::<Vec<_>>();
        available.sort();
        stages.push(Stage {
            prefix: std::mem::take(&mut prefix),
            source_index,
            available,
            captures,
            binding: local,
            child,
            pending: symbol(&await_form[3], "child Pending variant")?.to_owned(),
            ready: symbol(&await_form[4], "child Ready variant")?.to_owned(),
            poll: symbol(&await_form[5], "child poll function")?.to_owned(),
            value,
        });
        let local = &stages.last().unwrap().binding;
        known.insert(local.name.clone(), local.ty.clone());
        if stages.len() > 32 {
            return Err("@async-fn supports at most 32 suspension points".into());
        }
    }
    if stages.is_empty() {
        return Err(
            "@async-fn requires at least one top-level (#let name Type (#await ...))".into(),
        );
    }
    for stage in &stages {
        let captured = stage
            .captures
            .iter()
            .map(|binding| binding.name.as_str())
            .collect::<HashSet<_>>();
        for name in &stage.available {
            if !captured.contains(name.as_str())
                && body[stage.source_index + 1..]
                    .iter()
                    .any(|statement| contains_symbol(statement, name))
            {
                return Err(format!(
                    "@async-fn value '{name}' is used after #await but is absent from its capture list"
                ));
            }
        }
    }
    let reserved = [
        "waker",
        "lim.async.task",
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
                "{} (#return (#call {poll}-child-{} (#fn-args {} (lim.async.task {}) (waker waker))))",
                next.prefix.join(" "),
                index + 1,
                named_arguments(&next.captures),
                next.value
            )
        } else {
            format!("{} (#return ({ready} {returned}))", prefix.join(" "))
        };
        helpers.push(format!(
            "(#fn {resume} ({} ({} {}) (waker (#ref {waker}))) {poll_result}
               {continuation})",
            signature(&stage.captures),
            stage.binding.name,
            stage.binding.ty
        ));
        helpers.push(format!(
            "(#fn {child_helper} ({} (lim.async.task {}) (waker (#ref {waker}))) {poll_result}
               (#return (#match
                 (#call {} (#fn-args (task lim.async.task) (waker waker)))
                 (#case ({} lim.async.child)
                   ({pending} ({await_variant} {} lim.async.child)))
                 (#case ({} lim.async.value)
                   (#call {resume} (#fn-args {} ({} lim.async.value) (waker waker)))))))",
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
               (#call {child_helper} (#fn-args {} (lim.async.task lim.async.child) (waker waker))))",
            arguments(&stage.captures),
            named_arguments(&stage.captures),
        ));
    }
    let first = &stages[0];
    let start_case = format!(
        "(#case ({start_variant} {}) (#call {start_helper} (#fn-args {} (waker waker))))",
        arguments(&params),
        named_arguments(&params),
    );
    Ok(format!(
        "(#enum {frame} ({}))
         (#linear {frame})
         (#enum {poll_result} (({pending} {frame}) ({ready} {result})))
         (#fn {start} ({}) {frame} (#return ({start_variant} {})))
         {}
         (#fn {start_helper} ({} (waker (#ref {waker}))) {poll_result}
           {}
           (#return (#call {poll}-child-0 (#fn-args {} (lim.async.task {}) (waker waker)))))
         (#fn {poll} ((task {frame}) (waker (#ref {waker}))) {poll_result}
           (#return (#match task {start_case} {})))",
        variants.join(" "),
        signature(&params),
        arguments(&params),
        helpers.join("\n"),
        signature(&params),
        first.prefix.join(" "),
        named_arguments(&first.captures),
        first.value,
        await_cases.join(" "),
    ))
}

fn contains_symbol(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Symbol(symbol) => symbol == name,
        Expr::List(items) => items.iter().any(|item| contains_symbol(item, name)),
        _ => false,
    }
}
