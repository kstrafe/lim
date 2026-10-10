//! Collapse checked continuation-shaped async syntax into an ordinary poll loop.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! The tagged frame remains the state index and initialized-storage witness.
//! This changes execution structure, not layout or cleanup permissions. Source
//! bodies and the final generated ordinary program still require full checking.

use std::collections::{HashMap, HashSet};

use crate::Expr;

fn form<'a>(expression: &'a Expr, head: &str) -> Option<&'a [Expr]> {
    match expression {
        Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(name)) if name == head) => {
            Some(items)
        }
        _ => None,
    }
}

fn symbol(expression: &Expr) -> Option<&str> {
    match expression {
        Expr::Symbol(name) => Some(name),
        _ => None,
    }
}

fn list(head: &str, values: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::List(
        std::iter::once(Expr::Symbol(head.into()))
            .chain(values)
            .collect(),
    )
}

fn call(expression: &Expr) -> Option<(&str, &[Expr])> {
    let items = form(expression, "#call")?;
    let [_, name, Expr::List(arguments)] = items else {
        return None;
    };
    Some((symbol(name)?, arguments))
}

fn arguments(items: &[Expr]) -> Result<HashMap<String, Expr>, String> {
    items
        .iter()
        .map(|item| {
            let Expr::List(pair) = item else {
                return Err("async dispatcher lost a named argument".into());
            };
            let [Expr::Symbol(name), value] = pair.as_slice() else {
                return Err("async dispatcher lost a named argument".into());
            };
            Ok((name.clone(), value.clone()))
        })
        .collect()
}

fn parameters(function: &[Expr]) -> Result<Vec<(String, Expr, bool)>, String> {
    let Expr::List(parameters) = &function[2] else {
        return Err("async dispatcher lost a function signature".into());
    };
    parameters
        .iter()
        .map(|parameter| {
            let Expr::List(items) = parameter else {
                return Err("async dispatcher lost a parameter".into());
            };
            match items.as_slice() {
                [Expr::Symbol(name), ty] => Ok((name.clone(), ty.clone(), false)),
                [Expr::Symbol(head), Expr::Symbol(name), ty] if head == "#mut" => {
                    Ok((name.clone(), ty.clone(), true))
                }
                _ => Err("async dispatcher lost a parameter".into()),
            }
        })
        .collect()
}

fn replace_values(expression: &mut Expr, names: &HashMap<String, String>) {
    match expression {
        Expr::Symbol(name) => {
            if let Some(replacement) = names.get(name) {
                *name = replacement.clone();
            }
        }
        Expr::List(items) => {
            if matches!(
                items.first().and_then(symbol),
                Some("#quote" | "#quasiquote")
            ) {
                return;
            }
            if matches!(items.first().and_then(symbol), Some("#call")) {
                if let Some(Expr::List(arguments)) = items.get_mut(2) {
                    for argument in arguments {
                        if let Expr::List(pair) = argument {
                            if let Some(value) = pair.get_mut(1) {
                                replace_values(value, names);
                            }
                        }
                    }
                }
            } else if matches!(items.first().and_then(symbol), Some("#struct-literal")) {
                if let Some(Expr::List(fields)) = items.get_mut(2) {
                    for field in fields {
                        if let Expr::List(pair) = field {
                            if let Some(value) = pair.get_mut(1) {
                                replace_values(value, names);
                            }
                        }
                    }
                }
            } else if matches!(
                items.first().and_then(symbol),
                Some("#let" | "#let-mut" | "#let-else")
            ) {
                // Binding patterns and their declared types are not uses of
                // the renamed incoming parameter. Shadowing is prohibited.
                for value in items.iter_mut().skip(3) {
                    replace_values(value, names);
                }
            } else if matches!(
                items.first().and_then(symbol),
                Some("#get" | "#get-payload" | "#set-field" | "#set-payload" | "#pin-set-field")
            ) {
                if let Some(receiver) = items.get_mut(1) {
                    replace_values(receiver, names);
                }
                let start = if matches!(
                    items.first().and_then(symbol),
                    Some("#get" | "#get-payload")
                ) {
                    items.len()
                } else if matches!(items.first().and_then(symbol), Some("#set-payload")) {
                    4
                } else {
                    3
                };
                for value in items.iter_mut().skip(start) {
                    replace_values(value, names);
                }
            } else if matches!(items.first().and_then(symbol), Some("#as" | "#literal")) {
                let index = if matches!(items.first().and_then(symbol), Some("#as")) {
                    1
                } else {
                    2
                };
                if let Some(value) = items.get_mut(index) {
                    replace_values(value, names);
                }
            } else if matches!(
                items.first().and_then(symbol),
                Some("#array-of" | "#array-repeat")
            ) {
                for value in items.iter_mut().skip(2) {
                    replace_values(value, names);
                }
            } else if matches!(items.first().and_then(symbol), Some("#tuple")) {
                let start = if items.get(1).is_some_and(|value| {
                    form(value, "#tuple").is_some()
                        && crate::parse_type(Some(&crate::normalize_keywords(value.clone())))
                            .is_ok()
                }) {
                    2
                } else {
                    1
                };
                for value in items.iter_mut().skip(start) {
                    replace_values(value, names);
                }
            } else if matches!(items.first().and_then(symbol), Some("#label" | "#break-to")) {
                if let Some(value) = items.get_mut(2) {
                    replace_values(value, names);
                }
            } else if matches!(
                items.first().and_then(symbol),
                Some("#continue-to" | "#size-of" | "#align-of" | "#offset-of" | "#ptr-null")
            ) {
            } else {
                for value in items.iter_mut().skip(1) {
                    replace_values(value, names);
                }
            }
        }
        _ => {}
    }
}

struct Hygiene<'a> {
    used: &'a mut HashSet<String>,
    variants: &'a HashSet<String>,
    scope: &'a mut crate::gensym::Scope,
}

impl Hygiene<'_> {
    fn pattern(&mut self, pattern: &mut Expr, names: &mut HashMap<String, String>) {
        match pattern {
            Expr::Symbol(name)
                if name != "_"
                    && name != "true"
                    && name != "false"
                    && !self.variants.contains(name) =>
            {
                let original = name.clone();
                if names.contains_key(&original) {
                    loop {
                        let candidate = self
                            .scope
                            .fresh("binding")
                            .expect("fixed valid gensym hint");
                        if self.used.insert(candidate.clone()) {
                            *name = candidate;
                            break;
                        }
                    }
                }
                names.insert(original, name.clone());
            }
            Expr::List(items)
                if !matches!(
                    items.first().and_then(symbol),
                    Some("#literal" | "#range" | "#range-inclusive")
                ) =>
            {
                for item in items.iter_mut().skip(1) {
                    self.pattern(item, names);
                }
            }
            _ => {}
        }
    }

    fn statements(&mut self, statements: &mut [Expr], names: &mut HashMap<String, String>) {
        for statement in statements {
            self.expression(statement, names);
            if let Expr::List(items) = statement {
                if matches!(
                    items.first().and_then(symbol),
                    Some("#let" | "#let-mut" | "#let-else")
                ) {
                    if let Some(pattern) = items.get_mut(1) {
                        self.pattern(pattern, names);
                    }
                }
            }
        }
    }

    fn expression(&mut self, expression: &mut Expr, names: &HashMap<String, String>) {
        let Expr::List(items) = expression else {
            replace_values(expression, names);
            return;
        };
        match items.first().and_then(symbol) {
            Some("#quote" | "#quasiquote") => {}
            Some("#block" | "#loop") => self.statements(&mut items[1..], &mut names.clone()),
            Some("#case") => {
                let mut scope = names.clone();
                if let Some(pattern) = items.get_mut(1) {
                    self.pattern(pattern, &mut scope);
                }
                for value in items.iter_mut().skip(2) {
                    self.expression(value, &scope);
                }
            }
            Some("#while") => {
                if let Some(condition) = items.get_mut(1) {
                    self.expression(condition, names);
                }
                self.statements(&mut items[2..], &mut names.clone());
            }
            Some("#while-let") => {
                let mut scope = names.clone();
                self.expression(&mut items[3], names);
                self.pattern(&mut items[1], &mut scope);
                self.statements(&mut items[4..], &mut scope);
            }
            Some("#for") => {
                let mut scope = names.clone();
                self.statements(&mut items[1..2], &mut scope);
                self.expression(&mut items[2], &scope);
                self.expression(&mut items[3], &scope);
                self.statements(&mut items[4..], &mut scope);
            }
            Some("#for-range") => {
                self.expression(&mut items[2], names);
                self.expression(&mut items[3], names);
                let mut scope = names.clone();
                if let Expr::List(binding) = &mut items[1] {
                    self.pattern(&mut binding[0], &mut scope);
                }
                self.statements(&mut items[4..], &mut scope);
            }
            Some("#label") => self.expression(&mut items[2], names),
            Some("#break-to") => {
                if let Some(value) = items.get_mut(2) {
                    self.expression(value, names);
                }
            }
            Some("#continue-to") => {}
            _ => {
                self.operands(items, names);
            }
        }
    }

    fn operands(&mut self, items: &mut [Expr], names: &HashMap<String, String>) {
        match items.first().and_then(symbol) {
            Some("#call" | "#struct-literal") => {
                if let Some(Expr::List(pairs)) = items.get_mut(2) {
                    for pair in pairs {
                        if let Expr::List(pair) = pair {
                            if let Some(value) = pair.get_mut(1) {
                                self.expression(value, names);
                            }
                        }
                    }
                }
            }
            Some("#let" | "#let-mut" | "#let-else") => {
                for value in items.iter_mut().skip(3) {
                    self.expression(value, names);
                }
            }
            Some("#get" | "#get-payload" | "#set-field" | "#set-payload" | "#pin-set-field") => {
                self.expression(&mut items[1], names);
                let start = match items.first().and_then(symbol) {
                    Some("#get" | "#get-payload") => items.len(),
                    Some("#set-payload") => 4,
                    _ => 3,
                };
                for value in items.iter_mut().skip(start) {
                    self.expression(value, names);
                }
            }
            Some("#as" | "#literal") => {
                let index = if items.first().and_then(symbol) == Some("#as") {
                    1
                } else {
                    2
                };
                if let Some(value) = items.get_mut(index) {
                    self.expression(value, names);
                }
            }
            Some("#array-of" | "#array-repeat") => {
                for value in items.iter_mut().skip(2) {
                    self.expression(value, names);
                }
            }
            Some("#size-of" | "#align-of" | "#offset-of" | "#ptr-null") => {}
            Some("#tuple") => {
                let start = if items.get(1).is_some_and(|value| {
                    form(value, "#tuple").is_some()
                        && crate::parse_type(Some(&crate::normalize_keywords(value.clone())))
                            .is_ok()
                }) {
                    2
                } else {
                    1
                };
                for value in items.iter_mut().skip(start) {
                    self.expression(value, names);
                }
            }
            _ => {
                for value in items.iter_mut().skip(1) {
                    self.expression(value, names);
                }
            }
        }
    }
}

// Source functions have already passed the no-shadowing gate. Only collisions
// introduced by generated capture patterns or merging separate scopes are renamed.
fn hygienize(
    forms: &mut [Expr],
    used: &mut HashSet<String>,
    variants: &HashSet<String>,
    identity: &str,
) -> Result<(), String> {
    let mut scope = crate::gensym::Scope::new('a', identity);
    for expression in forms {
        if let Expr::List(items) = expression {
            if items.first().and_then(symbol) == Some("#fn") {
                let mut names = parameters(items)?
                    .into_iter()
                    .map(|(name, _, _)| (name.clone(), name))
                    .collect();
                Hygiene {
                    used,
                    variants,
                    scope: &mut scope,
                }
                .statements(&mut items[4..], &mut names);
            }
        }
    }
    Ok(())
}

/// Capture-analysis witnesses must obey the same no-shadowing rule as final
/// output. Only generated bindings are freshened; callable parameter names,
/// fields, constructors and types retain their explicit public spelling.
pub(crate) fn hygienize_source(
    source: &str,
    environment: &crate::generator::async_fn::AsyncTypeEnvironment,
) -> Result<String, String> {
    let mut forms = crate::parse(source)?
        .into_iter()
        .map(|node| node.expr)
        .collect::<Vec<_>>();
    let mut used = HashSet::new();
    let mut variants = environment
        .enums
        .values()
        .flat_map(|variants| variants.keys().cloned())
        .collect::<HashSet<_>>();
    for expression in &forms {
        symbols(expression, &mut used);
        if let Some(declaration) = form(expression, "#enum") {
            if let Some(Expr::List(cases)) = declaration.get(2) {
                for case in cases {
                    let name = symbol(case).or_else(|| match case {
                        Expr::List(items) => items.first().and_then(symbol),
                        _ => None,
                    });
                    if let Some(name) = name {
                        variants.insert(name.into());
                    }
                }
            }
        }
    }
    hygienize(&mut forms, &mut used, &variants, source)?;
    forms
        .iter()
        .map(crate::expression_source)
        .collect::<Result<Vec<_>, _>>()
        .map(|forms| forms.join("\n"))
}

struct Dispatcher<'a> {
    functions: &'a HashMap<String, Vec<Expr>>,
    children: HashMap<String, String>,
    state: String,
    state_type: Expr,
    label: String,
    next: String,
    removed: HashSet<String>,
    helpers: HashSet<String>,
}

impl Dispatcher<'_> {
    fn transition(&self, name: &str, args: &[Expr]) -> Result<Expr, String> {
        let arguments = arguments(args)?;
        let function = &self.functions[name];
        let values = parameters(function)?
            .into_iter()
            .filter(|(name, _, _)| name != "waker")
            .map(|(name, _, _)| {
                arguments
                    .get(&name)
                    .cloned()
                    .ok_or_else(|| format!("async transition lost '{name}'"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(list(
            "#block",
            [
                list(
                    "#let",
                    [
                        Expr::Symbol(self.next.clone()),
                        self.state_type.clone(),
                        list(&self.children[name], values),
                    ],
                ),
                list(
                    "#set",
                    [
                        Expr::Symbol(self.state.clone()),
                        Expr::Symbol(self.next.clone()),
                    ],
                ),
                list("#continue-to", [Expr::Symbol(self.label.clone())]),
            ],
        ))
    }

    fn inline(&mut self, name: &str, args: &[Expr]) -> Result<Expr, String> {
        let function = self
            .functions
            .get(name)
            .ok_or_else(|| format!("async dispatcher lost helper '{name}'"))?
            .clone();
        self.removed.insert(name.into());
        let args = arguments(args)?;
        let mut body = Vec::new();
        for (name, ty, mutable) in parameters(&function)? {
            let value = args
                .get(&name)
                .ok_or_else(|| format!("async helper lost '{name}'"))?;
            // Forwarded capture/waker bindings already have their checked type
            // and mutability. Do not shadow them or duplicate exclusive loans.
            if value == &Expr::Symbol(name.clone()) {
                continue;
            }
            body.push(list(
                if mutable { "#let-mut" } else { "#let" },
                [Expr::Symbol(name), ty, value.clone()],
            ));
        }
        for mut statement in function[4..].iter().cloned() {
            self.rewrite(&mut statement)?;
            body.push(statement);
        }
        Ok(list("#block", body))
    }

    fn rewrite(&mut self, expression: &mut Expr) -> Result<(), String> {
        if let Some((name, args)) = call(expression) {
            let name = name.to_owned();
            let args = args.to_vec();
            if self.children.contains_key(&name) {
                *expression = self.transition(&name, &args)?;
                return Ok(());
            }
            if self.helpers.contains(&name) {
                *expression = self.inline(&name, &args)?;
                return Ok(());
            }
        }
        if let Expr::List(items) = expression {
            if matches!(
                items.first().and_then(symbol),
                Some("#quote" | "#quasiquote")
            ) {
                return Ok(());
            }
            for item in items.iter_mut().skip(1) {
                self.rewrite(item)?;
            }
            if matches!(items.first().and_then(symbol), Some("#return")) {
                if items.len() != 2 {
                    return Err("async helper lost its explicit return".into());
                }
                let value = items.pop().unwrap();
                *expression = self.exit(value);
            }
        }
        Ok(())
    }

    // Put exits at value-producing leaves. A transition is already divergent;
    // wrapping it in another break would manufacture an unreachable aggregate
    // result and obscure the actual destination of nested control flow.
    fn exit(&self, mut value: Expr) -> Expr {
        if let Expr::List(items) = &mut value {
            match items.first().and_then(symbol) {
                Some("#block") if items.len() > 1 => {
                    if let Some(last) = items.last_mut() {
                        *last = self.exit(last.clone());
                        return value;
                    }
                }
                Some("#match") => {
                    for case in items.iter_mut().skip(2) {
                        if let Expr::List(parts) = case {
                            if let Some(body) = parts.get_mut(2) {
                                *body = self.exit(body.clone());
                            }
                        }
                    }
                    return value;
                }
                Some("#if") if items.len() == 4 => {
                    items[2] = self.exit(items[2].clone());
                    items[3] = self.exit(items[3].clone());
                    return value;
                }
                Some("#break-to" | "#continue-to" | "#return" | "#panic" | "#unreachable") => {
                    return value;
                }
                _ => {}
            }
        }
        list(
            "#block",
            [list("#break-to", [Expr::Symbol(self.label.clone()), value])],
        )
    }
}

fn symbols(expression: &Expr, used: &mut HashSet<String>) {
    match expression {
        Expr::Symbol(name) => {
            used.insert(name.clone());
        }
        Expr::List(items) => {
            for item in items {
                symbols(item, used);
            }
        }
        _ => {}
    }
}

fn fresh(used: &mut HashSet<String>, stem: String) -> String {
    if used.insert(stem.clone()) {
        return stem;
    }
    for index in 0.. {
        let candidate = format!("{stem}-{index}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!()
}

fn local_types(expression: &Expr, types: &mut HashMap<String, Expr>) {
    if let Expr::List(items) = expression {
        if matches!(items.first().and_then(symbol), Some("#let" | "#let-mut")) && items.len() == 4 {
            if let Some(name) = symbol(&items[1]) {
                types.insert(name.into(), items[2].clone());
            }
        }
        for item in items.iter().skip(1) {
            local_types(item, types);
        }
    }
}

fn has_entry(
    expression: &Expr,
    children: &HashMap<String, String>,
    helpers: &HashSet<String>,
) -> bool {
    if let Some((name, _)) = call(expression) {
        return children.contains_key(name) || helpers.contains(name);
    }
    match expression {
        Expr::List(items) => items
            .iter()
            .skip(1)
            .any(|item| has_entry(item, children, helpers)),
        _ => false,
    }
}

fn dispatch_matches(
    expression: &mut Expr,
    name: &str,
    functions: &HashMap<String, Vec<Expr>>,
    children: &HashMap<String, String>,
    helpers: &HashSet<String>,
    types: &HashMap<String, Expr>,
    used: &mut HashSet<String>,
    removed: &mut HashSet<String>,
) -> Result<(), String> {
    let matched = form(expression, "#match").filter(|items| {
        items
            .iter()
            .skip(2)
            .any(|case| has_entry(case, children, helpers))
    });
    if let Some(matched) = matched {
        let incoming = matched
            .get(1)
            .and_then(symbol)
            .ok_or("async dispatcher lost its state binding")?;
        let state_type = types
            .get(incoming)
            .ok_or("async dispatcher lost its state type")?
            .clone();
        let incoming = incoming.to_owned();
        let state = fresh(used, format!("lim.async.{name}.state"));
        let label = fresh(used, format!("lim.async.{name}.dispatch"));
        let next = fresh(used, format!("{label}.next"));
        let mut dispatcher = Dispatcher {
            functions,
            children: children.clone(),
            state: state.clone(),
            state_type: state_type.clone(),
            label: label.clone(),
            next,
            removed: HashSet::new(),
            helpers: helpers.clone(),
        };
        let mut cases = matched[2..].to_vec();
        for (case_index, case) in cases.iter_mut().enumerate() {
            let Expr::List(items) = case else {
                return Err("async dispatcher lost a match case".into());
            };
            let mut names = HashMap::new();
            if let Some(Expr::List(pattern)) = items.get_mut(1) {
                for (index, binding) in pattern.iter_mut().enumerate().skip(1) {
                    if let Expr::Symbol(original) = binding {
                        let saved =
                            fresh(used, format!("lim.async.{name}.saved-{case_index}-{index}"));
                        names.insert(original.clone(), saved.clone());
                        *original = saved;
                    }
                }
            }
            for value in items.iter_mut().skip(2) {
                replace_values(value, &names);
                if let Some((name, args)) = call(value).filter(|(name, _)| {
                    dispatcher.children.contains_key(*name) || dispatcher.helpers.contains(*name)
                }) {
                    let name = name.to_owned();
                    let args = args.to_vec();
                    *value = dispatcher.inline(&name, &args)?;
                } else {
                    dispatcher.rewrite(value)?;
                }
            }
        }
        *expression = list(
            "#block",
            [
                list(
                    "#let-mut",
                    [
                        Expr::Symbol(state.clone()),
                        state_type,
                        Expr::Symbol(incoming),
                    ],
                ),
                list(
                    "#label",
                    [
                        Expr::Symbol(label),
                        list(
                            "#loop",
                            [list(
                                "#match",
                                std::iter::once(Expr::Symbol(state)).chain(cases),
                            )],
                        ),
                    ],
                ),
            ],
        );
        removed.extend(dispatcher.removed);
        return Ok(());
    }
    if let Expr::List(items) = expression {
        for item in items.iter_mut().skip(1) {
            dispatch_matches(
                item, name, functions, children, helpers, types, used, removed,
            )?;
        }
    }
    Ok(())
}

fn fuse(
    expression: &mut Expr,
    name: &str,
    helper: &[Expr],
    used: &mut HashSet<String>,
) -> Result<(), String> {
    if let Some((callee, args)) = call(expression).filter(|(callee, _)| *callee == name) {
        let _ = callee;
        let args = arguments(args)?;
        let mut bindings = Vec::new();
        let mut renames = HashMap::new();
        for (index, (parameter, ty, mutable)) in parameters(helper)?.into_iter().enumerate() {
            let argument = args
                .get(&parameter)
                .ok_or("async dispatcher lost a pinned argument")?;
            if argument == &Expr::Symbol(parameter.clone()) {
                continue;
            }
            let local = fresh(used, format!("lim.async.{name}.input-{index}"));
            bindings.push(list(
                if mutable { "#let-mut" } else { "#let" },
                [Expr::Symbol(local.clone()), ty, argument.clone()],
            ));
            renames.insert(parameter, local);
        }
        for mut body in helper[4..].iter().cloned() {
            replace_values(&mut body, &renames);
            if let Some(returned) = form(&body, "#return") {
                body = returned[1].clone();
            }
            bindings.push(body);
        }
        *expression = list("#block", bindings);
        return Ok(());
    }
    if let Expr::List(items) = expression {
        for value in items.iter_mut().skip(1) {
            fuse(value, name, helper, used)?;
        }
    }
    Ok(())
}

/// Build dispatch loops without new unsafe operations or new frame variants.
pub(crate) fn collapse(
    source: &str,
    environment: &crate::generator::async_fn::AsyncTypeEnvironment,
) -> Result<String, String> {
    let mut forms = crate::parse(source)?
        .into_iter()
        .map(|node| node.expr)
        .collect::<Vec<_>>();
    let functions = forms
        .iter()
        .filter_map(|expression| {
            let function = form(expression, "#fn")?;
            Some((symbol(&function[1])?.to_owned(), function.to_vec()))
        })
        .collect::<HashMap<_, _>>();
    let mut removed = HashSet::new();
    let mut used = HashSet::new();
    for expression in &forms {
        symbols(expression, &mut used);
    }
    let mut variants = environment
        .enums
        .values()
        .flat_map(|variants| variants.keys().cloned())
        .collect::<HashSet<_>>();
    for expression in &forms {
        if let Some(declaration) = form(expression, "#enum") {
            if let Some(Expr::List(cases)) = declaration.get(2) {
                for case in cases {
                    let name = symbol(case).or_else(|| match case {
                        Expr::List(items) => items.first().and_then(symbol),
                        _ => None,
                    });
                    if let Some(name) = name {
                        variants.insert(name.into());
                    }
                }
            }
        }
    }
    for expression in &mut forms {
        let Some(function) = form(expression, "#fn") else {
            continue;
        };
        let public_name = symbol(&function[1]).unwrap().to_owned();
        let name = if functions.contains_key(&format!("{public_name}-move-start")) {
            format!("{public_name}-move")
        } else {
            public_name
        };
        if !functions.contains_key(&format!("{name}-start")) {
            continue;
        }
        let child_prefix = format!("{name}-child-");
        let mut children = HashMap::new();
        for (child_name, child) in &functions {
            if !child_name
                .strip_prefix(&child_prefix)
                .is_some_and(|suffix| suffix.parse::<usize>().is_ok())
            {
                continue;
            }
            // The checked Pending arm records the exact initialized state.
            let pending = form(&child[4], "#return")
                .and_then(|value| value.get(1))
                .and_then(|value| form(value, "#match"))
                .and_then(|value| value.get(2))
                .and_then(|value| form(value, "#case"))
                .and_then(|value| value.get(2))
                .and_then(|value| match value {
                    Expr::List(items) => items.get(1),
                    _ => None,
                })
                .and_then(|value| match value {
                    Expr::List(items) => items.first().and_then(symbol),
                    _ => None,
                });
            if let Some(variant) = pending {
                children.insert(child_name.clone(), variant.to_owned());
            }
        }
        let helpers = functions
            .keys()
            .filter(|helper| {
                **helper == format!("{name}-start")
                    || helper
                        .strip_prefix(&format!("{name}-resume-"))
                        .is_some_and(|index| index.parse::<usize>().is_ok())
            })
            .cloned()
            .collect();
        let mut function = function.to_vec();
        let mut types = parameters(&function)?
            .into_iter()
            .map(|(name, ty, _)| (name, ty))
            .collect::<HashMap<_, _>>();
        for body in &function[4..] {
            local_types(body, &mut types);
        }
        for body in &mut function[4..] {
            dispatch_matches(
                body,
                &name,
                &functions,
                &children,
                &helpers,
                &types,
                &mut used,
                &mut removed,
            )?;
        }
        *expression = Expr::List(function);
    }
    // Pinned polling used to wrap a second by-value poll. Embed its dispatcher
    // in the public in-place poll, while leaving the pin/cleanup boundary intact.
    hygienize(&mut forms, &mut used, &variants, source)?;
    let dispatched = forms
        .iter()
        .filter_map(|expression| {
            let function = form(expression, "#fn")?;
            Some((symbol(&function[1])?.to_owned(), function.to_vec()))
        })
        .collect::<HashMap<_, _>>();
    for expression in &mut forms {
        let Some(function) = form(expression, "#fn") else {
            continue;
        };
        let name = symbol(&function[1]).unwrap();
        let inner = format!("{name}-move");
        if let Some(helper) = dispatched.get(&inner) {
            let mut function = function.to_vec();
            for body in &mut function[4..] {
                fuse(body, &inner, helper, &mut used)?;
            }
            *expression = Expr::List(function);
            removed.insert(inner);
        }
    }
    forms.retain(|expression| {
        !form(expression, "#fn")
            .and_then(|function| symbol(&function[1]))
            .is_some_and(|name| removed.contains(name))
    });
    hygienize(&mut forms, &mut used, &variants, source)?;
    forms
        .iter()
        .map(crate::expression_source)
        .collect::<Result<Vec<_>, _>>()
        .map(|forms| forms.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inlined_scopes_rename_collisions_without_capturing_outer_values() {
        let input = "(#fn poll ((task Frame)) #u64
          (#return (#block
            (#let result #u64 (#block (#let task #u64 42u64) task))
            (#match task (#case (Frame-start value) result)))))";
        let mut forms = crate::parse(input)
            .unwrap()
            .into_iter()
            .map(|node| node.expr)
            .collect::<Vec<_>>();
        let mut used = HashSet::new();
        for expression in &forms {
            symbols(expression, &mut used);
        }
        hygienize(&mut forms, &mut used, &HashSet::new(), input).unwrap();
        let rendered = crate::expression_source(&forms[0]).unwrap();
        let token = crate::lex(&rendered)
            .unwrap()
            .into_iter()
            .find_map(|token| match token.kind {
                crate::TokenKind::Symbol(name) if crate::gensym::reserved(&name) => Some(name),
                _ => None,
            })
            .unwrap();
        let expected = "(#fn poll ((task Frame)) #u64
          (#return (#block
            (#let result #u64 (#block
              (#let lim.async.dispatch.binding.task #u64 42u64)
              lim.async.dispatch.binding.task))
            (#match task (#case (Frame-start value) result)))))";
        let expected = expected.replace("lim.async.dispatch.binding.task", &token);
        assert_eq!(forms[0], crate::parse(&expected).unwrap().remove(0).expr);
    }

    #[test]
    fn parameter_renaming_preserves_fields_types_and_named_argument_keys() {
        let input = "(#block
          (#let value task (#struct-literal task ((task task))))
          (#set-field value task task)
          (#get task task)
          (#call task ((task task)))
          (#array-of (#array task 1) task)
          (#tuple (#tuple task) task)
          (#as task task)
          (#literal task 1))";
        let mut expression = crate::parse(input).unwrap().remove(0).expr;
        replace_values(
            &mut expression,
            &HashMap::from([("task".into(), "saved".into())]),
        );
        let expected = "(#block
          (#let value task (#struct-literal task ((task saved))))
          (#set-field value task saved)
          (#get saved task)
          (#call task ((task saved)))
          (#array-of (#array task 1) saved)
          (#tuple (#tuple task) saved)
          (#as saved task)
          (#literal task 1))";
        assert_eq!(expression, crate::parse(expected).unwrap().remove(0).expr);
    }
}
