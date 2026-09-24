//! Pure, immutable syntax generators used by `@name` declarations.

use std::{
    collections::{HashMap, HashSet},
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, SystemTime},
};

use crate::{Expr, Span, SpannedExpr};

const MAX_EVALUATION_STEPS: usize = 200_000;
const MAX_GENERATED_NODES: usize = 1_000_000;
const MAX_EXPANSION_DEPTH: usize = 128;
static CACHE_TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Debug)]
struct GeneratorParameter {
    name: String,
    capabilities: Vec<String>,
}

#[derive(Clone)]
struct Generator {
    parameters: Vec<GeneratorParameter>,
    body: Expr,
    span: Span,
    source_body: Option<SpannedExpr>,
}

type GeneratorFunction = Generator;
type CapabilityOperations = HashMap<String, String>;
type Capabilities = HashMap<String, HashMap<String, CapabilityOperations>>;

#[derive(Clone)]
struct GeneratorFingerprint {
    hash: u128,
    material: String,
    dependencies: Vec<String>,
}

#[derive(Clone, Debug)]
enum Value {
    Syntax(Expr),
    Boolean(bool),
}

enum TemplateValue {
    Syntax(Expr),
    Splice(Vec<Expr>),
}

type Environment = HashMap<String, Expr>;
type ExpandedForms = (Vec<SpannedExpr>, Vec<Expr>);
type ExpandedFormsWithHits = (ExpandedForms, usize);

fn declared_lim_function_signatures(
    expressions: &[SpannedExpr],
) -> Result<HashMap<String, String>, String> {
    let mut signatures = HashMap::new();
    for expression in expressions {
        let normalized = crate::normalize_keywords(expression.expr.clone());
        let Expr::List(items) = &normalized else {
            continue;
        };
        let Some(Expr::Symbol(kind)) = items.first() else {
            continue;
        };
        let external = match kind.as_str() {
            "fn" => false,
            "extern-fn" => true,
            _ => continue,
        };
        let function = crate::parse_function(items, external)
            .map_err(|error| at_span(error, expression.span, "capability operation signature"))?;
        let arguments = function
            .parameters
            .iter()
            .map(|parameter| parameter.ty.clone())
            .collect::<Vec<_>>();
        let signature = format!("{arguments:?}->{:?}", function.return_type);
        if signatures.contains_key(&function.name) {
            let name_span = expression
                .children
                .get(1)
                .filter(|name| matches!(&name.expr, Expr::Symbol(name) if name == &function.name))
                .map_or(expression.span, |name| name.span);
            return Err(at_span(
                format!(
                    "duplicate function '{}' while resolving generator capability contracts",
                    function.name
                ),
                name_span,
                "function declaration",
            ));
        }
        signatures.insert(function.name.clone(), signature);
    }
    Ok(signatures)
}

fn hash_capability_definitions(capabilities: &Capabilities) -> u128 {
    let mut material = Vec::new();
    let mut names = capabilities.keys().collect::<Vec<_>>();
    names.sort();
    for name in names {
        let types = &capabilities[name];
        let mut type_names = types.keys().collect::<Vec<_>>();
        type_names.sort();
        for type_name in type_names {
            let operations = &types[type_name];
            let mut operation_names = operations.keys().collect::<Vec<_>>();
            operation_names.sort();
            for operation in operation_names {
                material.push(format!(
                    "{name}/{type_name}/{operation}:{}",
                    operations[operation]
                ));
            }
        }
    }
    stable_hash(material.join("\n").as_bytes())
}

pub(crate) fn expand_with_generated_cached_with_context(
    expressions: Vec<SpannedExpr>,
    cache_dir: Option<&Path>,
    dependency_context: &str,
) -> Result<(Vec<SpannedExpr>, Vec<Expr>), String> {
    expand_with_generated_cached_and_hits(expressions, cache_dir, dependency_context)
        .map(|(result, _)| result)
}

fn expand_with_generated_cached_and_hits(
    expressions: Vec<SpannedExpr>,
    cache_dir: Option<&Path>,
    dependency_context: &str,
) -> Result<ExpandedFormsWithHits, String> {
    let mut generators = HashMap::new();
    let mut functions = HashMap::new();
    let mut capabilities: Capabilities = HashMap::new();
    let declared_functions = declared_lim_function_signatures(&expressions)?;
    let mut remaining = Vec::new();
    for expression in expressions {
        if let Expr::List(items) = &expression.expr {
            if is_operator(items.first(), "#capability") {
                let capability = symbol(items.get(1), "capability name")
                    .map_err(|error| at_span(error, expression.span, "capability declaration"))?
                    .to_owned();
                let type_name = symbol(items.get(2), "capability type")
                    .map_err(|error| at_span(error, expression.span, "capability declaration"))?
                    .to_owned();
                if items.len() != 4 || capability.starts_with('#') || type_name.starts_with('#') {
                    return Err(at_span(
                        "#capability requires a name, concrete type, and operation contracts"
                            .into(),
                        expression.span,
                        "capability declaration",
                    ));
                }
                let mut operations = HashMap::new();
                let operation_forms = match items.get(3) {
                    Some(Expr::List(forms)) if !forms.is_empty() => forms,
                    _ => {
                        return Err(at_span(
                            "#capability operation contracts must be a non-empty list".into(),
                            expression.span,
                            "capability declaration",
                        ))
                    }
                };
                for (operation_index, operation) in operation_forms.iter().enumerate() {
                    let operation_name_span = expression
                        .children
                        .get(3)
                        .and_then(|contracts| contracts.children.get(operation_index))
                        .and_then(|operation| operation.children.first())
                        .map_or(expression.span, |name| name.span);
                    let Expr::List(parts) = operation else {
                        return Err(at_span(
                            "capability operations have the form (function (ArgumentType ...) ReturnType)".into(),
                            expression.span,
                            "capability declaration",
                        ));
                    };
                    if parts.len() != 3 {
                        return Err(at_span(
                            "capability operations have the form (function (ArgumentType ...) ReturnType)".into(),
                            expression.span,
                            "capability declaration",
                        ));
                    }
                    let operation_name = symbol(parts.first(), "capability operation function")
                        .map_err(|error| {
                            at_span(error, expression.span, "capability declaration")
                        })?;
                    let argument_types = match &parts[1] {
                        Expr::List(types) => types
                            .iter()
                            .map(|ty| {
                                crate::parse_type(Some(&crate::normalize_keywords(ty.clone())))
                            })
                            .collect::<Result<Vec<_>, _>>()
                            .map_err(|error| {
                                at_span(error, expression.span, "capability declaration")
                            })?,
                        _ => {
                            return Err(at_span(
                                "capability operation argument types must be a list".into(),
                                expression.span,
                                "capability declaration",
                            ))
                        }
                    };
                    let return_type =
                        crate::parse_type(Some(&crate::normalize_keywords(parts[2].clone())))
                            .map_err(|error| {
                                at_span(error, expression.span, "capability declaration")
                            })?;
                    let signature = format!("{argument_types:?}->{return_type:?}");
                    let Some(actual_signature) = declared_functions.get(operation_name) else {
                        return Err(at_span(
                            format!("capability '{capability}' for '{type_name}' requires operation function '{operation_name}', but it is not declared"),
                            operation_name_span,
                            "capability declaration",
                        ));
                    };
                    if actual_signature != &signature {
                        return Err(at_span(
                            format!("capability operation '{operation_name}' has signature {actual_signature}; contract requires {signature}"),
                            operation_name_span,
                            "capability declaration",
                        ));
                    }
                    if operations
                        .insert(operation_name.to_owned(), signature)
                        .is_some()
                    {
                        return Err(at_span(
                            format!("duplicate operation '{operation_name}' in capability '{capability}'"),
                            operation_name_span,
                            "capability declaration",
                        ));
                    }
                }
                let types = capabilities.entry(capability.clone()).or_default();
                if types.insert(type_name.clone(), operations).is_some() {
                    let type_name_span = expression
                        .children
                        .get(2)
                        .filter(
                            |name| matches!(&name.expr, Expr::Symbol(name) if name == &type_name),
                        )
                        .map_or(expression.span, |name| name.span);
                    return Err(at_span(
                        format!("duplicate capability '{capability}' declaration for type '{type_name}'"),
                        type_name_span,
                        "capability declaration",
                    ));
                }
                continue;
            }
            if is_operator(items.first(), "#generator") {
                let generator = parse_generator(items, &expression).map_err(|error| {
                    if error.contains("source span ") {
                        error
                    } else {
                        at_span(error, expression.span, "generator declaration")
                    }
                })?;
                let name = symbol(items.get(1), "generator name")?.to_owned();
                if functions.contains_key(&name) {
                    let name_span = expression
                        .children
                        .get(1)
                        .filter(|symbol| matches!(&symbol.expr, Expr::Symbol(symbol) if symbol == &name))
                        .map_or(expression.span, |symbol| symbol.span);
                    return Err(at_span(
                        format!("duplicate generator or generator function declaration '{name}'"),
                        name_span,
                        "generator declaration",
                    ));
                }
                if generators.insert(name.clone(), generator).is_some() {
                    let name_span = expression
                        .children
                        .get(1)
                        .filter(|symbol| matches!(&symbol.expr, Expr::Symbol(symbol) if symbol == &name))
                        .map_or(expression.span, |symbol| symbol.span);
                    return Err(at_span(
                        format!("duplicate generator declaration '{name}'"),
                        name_span,
                        "generator declaration",
                    ));
                }
                continue;
            }
            if is_operator(items.first(), "#gn-fn") {
                let function = parse_generator_function(items, &expression).map_err(|error| {
                    at_span(error, expression.span, "generator function declaration")
                })?;
                let name = symbol(items.get(1), "generator function name")?.to_owned();
                if generators.contains_key(&name)
                    || functions.insert(name.clone(), function).is_some()
                {
                    let name_span = expression
                        .children
                        .get(1)
                        .filter(|symbol| matches!(&symbol.expr, Expr::Symbol(symbol) if symbol == &name))
                        .map_or(expression.span, |symbol| symbol.span);
                    return Err(at_span(
                        format!("duplicate generator or generator function declaration '{name}'"),
                        name_span,
                        "generator function declaration",
                    ));
                }
                continue;
            }
        }
        remaining.push(expression);
    }

    let interpreter_hash = stable_hash(include_bytes!("generator.rs"));
    let capability_hash = hash_capability_definitions(&capabilities);
    let function_hashes =
        generator_function_hashes(&functions, interpreter_hash).map_err(|error| {
            let responsible_function = error
                .strip_prefix("recursive generator function calls are not allowed: ")
                .and_then(|cycle| {
                    let names = cycle.split(" -> ").collect::<Vec<_>>();
                    names.get(names.len().saturating_sub(2)).copied()
                })
                .or_else(|| {
                    error
                        .split_once(" called from generator function '")
                        .and_then(|(_, rest)| rest.strip_suffix('\'').or(Some(rest)))
                });
            responsible_function
                .and_then(|name| functions.get(name))
                .map_or(error.clone(), |function| {
                    let callee = error
                        .strip_prefix("recursive generator function calls are not allowed: ")
                        .and_then(|cycle| cycle.split(" -> ").last());
                    let call_span = callee.and_then(|callee| {
                        function
                            .source_body
                            .as_ref()
                            .and_then(|body| generator_call_span(body, callee))
                    });
                    at_span(
                        error,
                        call_span.unwrap_or(function.span),
                        "generator function",
                    )
                })
        })?;
    let generator_hashes = generator_hashes(&generators, &function_hashes, interpreter_hash);
    let mut context = ExpansionContext {
        generators: &generators,
        functions: &functions,
        capabilities: &capabilities,
        capability_hash,
        generator_fingerprints: generator_hashes,
        active_functions: Vec::new(),
        active: Vec::new(),
        seen_invocations: HashSet::new(),
        budget: Budget {
            evaluation_steps: MAX_EVALUATION_STEPS,
            generated_nodes: 0,
        },
        cache_hits: 0,
        cache_dir,
        dependency_context,
        invocation_span: None,
    };
    let mut output = Vec::new();
    let mut generated = Vec::new();
    for expression in remaining {
        context.invocation_span = Some(expression.span);
        let is_user_invocation = match &expression.expr {
            Expr::List(items) if matches!(items.first(), Some(Expr::At)) => items
                .get(1)
                .and_then(|item| match item {
                    Expr::Symbol(name) => Some(generators.contains_key(name)),
                    _ => None,
                })
                .unwrap_or(false),
            _ => false,
        };
        let original_expr = expression.expr.clone();
        let original_children = expression.children.clone();
        let expanded = expand_top(expression.expr, &mut context)
            .map_err(|error| at_span(error, expression.span, "generator expansion"))?;
        if is_user_invocation {
            for form in &expanded {
                context.budget.generated_nodes = context
                    .budget
                    .generated_nodes
                    .saturating_add(expression_nodes(form));
            }
            if context.budget.generated_nodes > MAX_GENERATED_NODES {
                return Err(at_span(
                    format!(
                        "generator output exceeds maximum of {MAX_GENERATED_NODES} syntax nodes"
                    ),
                    expression.span,
                    "generator expansion",
                ));
            }
            generated.extend(expanded.iter().cloned());
        }
        output.extend(expanded.into_iter().map(|expr| {
            let unchanged = expr == original_expr;
            SpannedExpr {
                expr,
                span: expression.span,
                children: if unchanged {
                    original_children.clone()
                } else {
                    Vec::new()
                },
            }
        }));
    }
    Ok(((output, generated), context.cache_hits))
}

fn parse_generator_function(
    items: &[Expr],
    source: &SpannedExpr,
) -> Result<GeneratorFunction, String> {
    if items.len() != 4 {
        return Err("#gn-fn requires a name, parameter list, and body".into());
    }
    parse_generator(items, source).map_err(|error| {
        error
            .replace("#generator", "#gn-fn")
            .replace("generator '", "generator function '")
    })
}

fn parse_generator(items: &[Expr], source: &SpannedExpr) -> Result<Generator, String> {
    if items.len() != 4 {
        return Err("#generator requires a name, parameter list, and body".into());
    }
    let name = symbol(items.get(1), "generator name")?;
    let parameters = match items.get(2) {
        Some(Expr::List(parameters)) => parameters,
        _ => return Err(format!("generator '{name}' parameters must be a list")),
    };
    let mut names = Vec::with_capacity(parameters.len());
    for (parameter_index, parameter) in parameters.iter().enumerate() {
        let (name, capabilities) = match parameter {
            Expr::Symbol(name) => (name.as_str(), Vec::new()),
            Expr::List(items) if !items.is_empty() => {
                let name = symbol(items.first(), "generator parameter name")?;
                let mut required = Vec::new();
                for capability in &items[1..] {
                    let capability = symbol(Some(capability), "generator parameter capability")?;
                    if capability.starts_with('#') || capability.starts_with('@') {
                        return Err(format!("invalid generator capability '{capability}'"));
                    }
                    required.push(capability.to_owned());
                }
                (name, required)
            }
            _ => {
                return Err("generator parameter must be a symbol or (name capability ...)".into())
            }
        };
        if name.starts_with('#') || name.starts_with('@') {
            return Err(format!("invalid generator parameter '{name}'"));
        }
        if names
            .iter()
            .any(|existing: &GeneratorParameter| existing.name == name)
        {
            let parameter_span = source
                .children
                .get(2)
                .and_then(|parameters| parameters.children.get(parameter_index))
                .and_then(|parameter| match &parameter.expr {
                    Expr::List(_) => parameter.children.first(),
                    _ => Some(parameter),
                })
                .map_or(source.span, |name| name.span);
            return Err(at_span(
                format!("duplicate generator parameter '{name}'"),
                parameter_span,
                "generator parameter",
            ));
        }
        names.push(GeneratorParameter {
            name: name.to_owned(),
            capabilities,
        });
    }
    Ok(Generator {
        parameters: names,
        body: items[3].clone(),
        span: source.span,
        source_body: source.children.get(3).cloned(),
    })
}

fn generator_call_span(expression: &SpannedExpr, callee: &str) -> Option<Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "#gn-call")
            && matches!(items.get(1), Some(Expr::Symbol(name)) if name == callee)
        {
            return expression.children.get(1).map(|name| name.span);
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| generator_call_span(child, callee))
}

struct Budget {
    evaluation_steps: usize,
    generated_nodes: usize,
}

struct ExpansionContext<'a> {
    generators: &'a HashMap<String, Generator>,
    functions: &'a HashMap<String, GeneratorFunction>,
    capabilities: &'a Capabilities,
    capability_hash: u128,
    generator_fingerprints: HashMap<String, GeneratorFingerprint>,
    active_functions: Vec<String>,
    active: Vec<String>,
    seen_invocations: HashSet<String>,
    budget: Budget,
    cache_hits: usize,
    cache_dir: Option<&'a Path>,
    dependency_context: &'a str,
    invocation_span: Option<Span>,
}

fn expand_top(expression: Expr, context: &mut ExpansionContext<'_>) -> Result<Vec<Expr>, String> {
    let Expr::List(items) = &expression else {
        return Ok(vec![expression]);
    };
    if !matches!(items.first(), Some(Expr::At)) {
        return Ok(vec![expression]);
    }
    let Some(Expr::Symbol(name)) = items.get(1) else {
        return Err("generator invocation requires a name after '@'".into());
    };
    let Some(generator) = context.generators.get(name).cloned() else {
        // Built-in declarations such as @optional are handled by the Lim parser.
        return Ok(vec![expression]);
    };
    if context.active.iter().any(|entry| entry == name) {
        let mut chain = context.active.join(" -> ");
        if !chain.is_empty() {
            chain.push_str(" -> ");
        }
        chain.push_str(name);
        return Err(format!(
            "recursive generator expansion is not allowed: {chain}"
        ));
    }
    if items.len() - 2 != generator.parameters.len() {
        return Err(format!(
            "{} expects {} syntax argument(s), received {}",
            invocation_description(
                name,
                expression_arguments(items),
                &generator,
                context.invocation_span,
            ),
            generator.parameters.len(),
            items.len() - 2
        ));
    }
    for (parameter, argument) in generator.parameters.iter().zip(&items[2..]) {
        for capability in &parameter.capabilities {
            let Expr::Symbol(type_name) = argument else {
                return Err(format!(
                    "{} parameter '{}' requires capability '{}' on a concrete type symbol",
                    invocation_description(
                        name,
                        expression_arguments(items),
                        &generator,
                        context.invocation_span,
                    ),
                    parameter.name,
                    capability,
                ));
            };
            if !context
                .capabilities
                .get(capability)
                .is_some_and(|types| types.contains_key(type_name))
            {
                return Err(format!(
                    "{} parameter '{}' requires capability '{}' for type '{}'; declare (#capability {} {})",
                    invocation_description(
                        name,
                        expression_arguments(items),
                        &generator,
                        context.invocation_span,
                    ),
                    parameter.name,
                    capability,
                    type_name,
                    capability,
                    type_name,
                ));
            }
        }
    }
    if context.active.len() >= MAX_EXPANSION_DEPTH {
        return Err(format!(
            "generator expansion exceeds maximum depth of {MAX_EXPANSION_DEPTH}"
        ));
    }
    let invocation_key = format!("{name}:{:?}", &items[2..]);
    if !context.seen_invocations.insert(invocation_key) {
        return Ok(Vec::new());
    }
    let cache_key = format!(
        "lim-generator-cache-v6\ncompiler={}\ntarget={}-{}\ndependency-context={}\ncapability-hash={:032x}\ngenerator-hash={:032x}\ngenerator-input={}\narguments={:?}",
        env!("CARGO_PKG_VERSION"),
        std::env::consts::ARCH,
        std::env::consts::OS,
        context.dependency_context,
        context.capability_hash,
        context.generator_fingerprints[name].hash,
        context.generator_fingerprints[name].material,
        &items[2..],
    );
    let cached = context
        .cache_dir
        .and_then(|directory| read_cached_expansion(directory, &cache_key));
    if cached.is_some() {
        context.cache_hits = context.cache_hits.saturating_add(1);
    }
    context.active.push(name.clone());
    let forms = match cached {
        Some(forms) => forms,
        None => {
            let environment = generator
                .parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .zip(items[2..].iter().cloned())
                .collect();
            let result = match evaluate(&generator.body, &environment, context) {
                Ok(result) => result,
                Err(error) => {
                    context.active.pop();
                    return Err(format!(
                        "{}: {error}",
                        invocation_description(
                            name,
                            expression_arguments(items),
                            &generator,
                            context.invocation_span,
                        )
                    ));
                }
            };
            let Value::Syntax(Expr::List(forms)) = result else {
                context.active.pop();
                return Err(format!("@{name} must return a list of generated forms"));
            };
            if let Some(directory) = context.cache_dir {
                write_cached_expansion(directory, &cache_key, &forms);
            }
            forms
        }
    };
    let mut expanded = Vec::new();
    for form in forms {
        match expand_top(form, context) {
            Ok(forms) => expanded.extend(forms),
            Err(error) => {
                context.active.pop();
                return Err(format!(
                    "while expanding generated output from {}: {error}",
                    invocation_description(
                        name,
                        expression_arguments(items),
                        &generator,
                        context.invocation_span,
                    )
                ));
            }
        }
    }
    context.active.pop();
    Ok(expanded)
}

fn expression_arguments(items: &[Expr]) -> Vec<Expr> {
    items[2..].to_vec()
}

fn invocation_description(
    name: &str,
    arguments: Vec<Expr>,
    generator: &Generator,
    invocation_span: Option<Span>,
) -> String {
    let arguments = arguments
        .iter()
        .enumerate()
        .map(|(index, argument)| format!("argument {index}={argument:?}"))
        .collect::<Vec<_>>();
    format!(
        "@{name} invocation at {}:{} (defined at {}:{}; {})",
        invocation_span.map_or(generator.span.line, |span| span.line),
        invocation_span.map_or(generator.span.column, |span| span.column),
        generator.span.line,
        generator.span.column,
        if arguments.is_empty() {
            "no arguments".to_owned()
        } else {
            arguments.join(", ")
        }
    )
}

fn generator_function_hashes(
    functions: &HashMap<String, GeneratorFunction>,
    interpreter_hash: u128,
) -> Result<HashMap<String, GeneratorFingerprint>, String> {
    let mut hashes = HashMap::new();
    let mut active = Vec::new();
    let mut names = functions.keys().collect::<Vec<_>>();
    names.sort();
    for name in names {
        hash_generator_function(name, functions, interpreter_hash, &mut hashes, &mut active)?;
    }
    Ok(hashes)
}

fn hash_generator_function(
    name: &str,
    functions: &HashMap<String, GeneratorFunction>,
    interpreter_hash: u128,
    hashes: &mut HashMap<String, GeneratorFingerprint>,
    active: &mut Vec<String>,
) -> Result<GeneratorFingerprint, String> {
    if let Some(hash) = hashes.get(name) {
        return Ok(hash.clone());
    }
    if active.iter().any(|entry| entry == name) {
        let mut chain = active.join(" -> ");
        if !chain.is_empty() {
            chain.push_str(" -> ");
        }
        chain.push_str(name);
        return Err(format!(
            "recursive generator function calls are not allowed: {chain}"
        ));
    }
    let function = functions.get(name).ok_or_else(|| {
        active.last().map_or_else(
            || format!("unknown generator function '{name}'"),
            |caller| {
                format!(
                    "unknown generator function '{name}' called from generator function '{caller}'"
                )
            },
        )
    })?;
    active.push(name.to_owned());
    let mut calls = Vec::new();
    collect_generator_function_calls(&function.body, &mut calls);
    calls.sort();
    calls.dedup();
    let definition = format!(
        "lim-generator-function-v1\ninterpreter={interpreter_hash:032x}\nname={name}\nparameters={:?}\nbody={:?}",
        function.parameters, function.body
    );
    let mut hash_material = definition.clone();
    for called in &calls {
        match functions.get(called) {
            Some(_) => {
                let fingerprint =
                    hash_generator_function(called, functions, interpreter_hash, hashes, active)?;
                hash_material.push_str(&format!("\ncall={called}:{:032x}", fingerprint.hash));
            }
            None => hash_material.push_str(&format!("\nmissing-call={called}")),
        }
    }
    active.pop();
    let fingerprint = GeneratorFingerprint {
        hash: stable_hash(hash_material.as_bytes()),
        material: definition,
        dependencies: calls,
    };
    hashes.insert(name.to_owned(), fingerprint.clone());
    Ok(fingerprint)
}

fn generator_hashes(
    generators: &HashMap<String, Generator>,
    function_hashes: &HashMap<String, GeneratorFingerprint>,
    interpreter_hash: u128,
) -> HashMap<String, GeneratorFingerprint> {
    generators
        .iter()
        .map(|(name, generator)| {
            let mut calls = Vec::new();
            collect_generator_function_calls(&generator.body, &mut calls);
            calls.sort();
            calls.dedup();
            let definition = format!(
                "lim-generator-v1\ninterpreter={interpreter_hash:032x}\nname={name}\nparameters={:?}\nbody={:?}",
                generator.parameters, generator.body
            );
            let mut closure = HashSet::new();
            let mut pending = calls.clone();
            while let Some(called) = pending.pop() {
                if !closure.insert(called.clone()) {
                    continue;
                }
                if let Some(fingerprint) = function_hashes.get(&called) {
                    pending.extend(fingerprint.dependencies.iter().cloned());
                }
            }
            let mut closure = closure.into_iter().collect::<Vec<_>>();
            closure.sort();
            let mut material = definition.clone();
            let mut hash_material = definition;
            for called in closure {
                match function_hashes.get(&called) {
                    Some(fingerprint) => {
                        material.push_str(&format!(
                            "\nhelper={called}:{}:{}",
                            fingerprint.material.len(),
                            fingerprint.material
                        ));
                    }
                    None => material.push_str(&format!("\nmissing-helper={called}")),
                }
            }
            for called in &calls {
                match function_hashes.get(called) {
                    Some(fingerprint) => {
                        hash_material.push_str(&format!("\ncall={called}:{:032x}", fingerprint.hash));
                    }
                    None => hash_material.push_str(&format!("\nmissing-call={called}")),
                }
            }
            (
                name.clone(),
                GeneratorFingerprint {
                    hash: stable_hash(hash_material.as_bytes()),
                    material,
                    dependencies: calls,
                },
            )
        })
        .collect()
}

fn collect_generator_function_calls(expression: &Expr, calls: &mut Vec<String>) {
    match expression {
        Expr::List(items) => {
            let Some(Expr::Symbol(operator)) = items.first() else {
                return;
            };
            match operator.as_str() {
                "#gn-call" => {
                    if let Some(Expr::Symbol(name)) = items.get(1) {
                        calls.push(name.clone());
                    }
                    for argument in items.iter().skip(2) {
                        collect_generator_function_calls(argument, calls);
                    }
                }
                "#gn-if" | "#gn-equal" | "#gn-symbol?" | "#gn-list?" | "#gn-symbol"
                | "#gn-list" | "#gn-first" | "#gn-rest" | "#gn-for-each" | "#gn-error" => {
                    for argument in items.iter().skip(1) {
                        collect_generator_function_calls(argument, calls);
                    }
                }
                _ => {}
            }
        }
        Expr::QuasiQuote(template) => collect_template_function_calls(template, 1, calls),
        Expr::Unquote(inner) | Expr::UnquoteSplicing(inner) => {
            collect_generator_function_calls(inner, calls)
        }
        Expr::Quote(_) | Expr::Labeled { .. } | Expr::Block(_) | Expr::Loop(_) => {}
        Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
}

fn collect_template_function_calls(expression: &Expr, depth: usize, calls: &mut Vec<String>) {
    match expression {
        Expr::QuasiQuote(inner) => collect_template_function_calls(inner, depth + 1, calls),
        Expr::Unquote(inner) | Expr::UnquoteSplicing(inner) if depth == 1 => {
            collect_generator_function_calls(inner, calls)
        }
        Expr::Unquote(inner) | Expr::UnquoteSplicing(inner) => {
            collect_template_function_calls(inner, depth - 1, calls)
        }
        Expr::List(items) => {
            for item in items {
                collect_template_function_calls(item, depth, calls);
            }
        }
        Expr::Block(_) | Expr::Loop(_) | Expr::Quote(_) | Expr::Labeled { .. } => {}
        Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
}

fn cache_path(directory: &Path, key: &str) -> PathBuf {
    // Stable FNV-1a 128-bit naming; the complete key is stored and compared
    // inside each file, so a digest collision can never produce a false hit.
    directory.join(format!(
        "generator-{:032x}.cache",
        stable_hash(key.as_bytes())
    ))
}

/// Read or create an inspectable generated-source artifact in the shared
/// content-addressed cache. The complete key lives beside the `.lim` file so
/// a digest collision is detected instead of treated as a hit.
pub(crate) fn cached_generated_source(
    directory: &Path,
    key: &str,
    generate: impl FnOnce() -> Result<String, String>,
) -> Result<String, String> {
    let digest = stable_hash(key.as_bytes());
    let path = directory.join(format!("generated-{digest:032x}.lim"));
    let key_path = directory.join(format!("generated-{digest:032x}.key"));
    let digest_path = directory.join(format!("generated-{digest:032x}.hash"));
    cleanup_abandoned_staging(directory);
    if let Ok(existing_key) = fs::read_to_string(&key_path) {
        if existing_key != key {
            return Err(format!(
                "generated-source cache hash collision at {}",
                path.display()
            ));
        }
        if let (Ok(source), Ok(expected_digest)) =
            (fs::read_to_string(&path), fs::read_to_string(&digest_path))
        {
            if expected_digest == generated_source_digest(key, &source)
                && crate::parse(&source).is_ok()
            {
                return Ok(source);
            }
        }
    }

    let source = generate()?;
    fs::create_dir_all(directory)
        .map_err(|error| format!("cannot create generated-source cache: {error}"))?;
    publish_cache_file(&path, source.as_bytes(), "generated source")?;
    publish_cache_file(&key_path, key.as_bytes(), "generated-source cache key")?;
    // Publish the digest last: readers treat it as the commit marker for the
    // corresponding source and full key and reject any intermediate mixture.
    publish_cache_file(
        &digest_path,
        generated_source_digest(key, &source).as_bytes(),
        "generated-source cache digest",
    )?;
    Ok(source)
}

fn generated_source_digest(key: &str, source: &str) -> String {
    let mut contents = Vec::with_capacity(key.len() + 1 + source.len());
    contents.extend_from_slice(key.as_bytes());
    contents.push(0);
    contents.extend_from_slice(source.as_bytes());
    format!("{:032x}", stable_hash(&contents))
}

fn write_cache_staging(target: &Path, contents: &[u8]) -> Result<PathBuf, String> {
    for _ in 0..128 {
        let sequence = CACHE_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let temporary = target.with_extension(format!("{}-{sequence}.tmp", std::process::id()));
        let mut file = match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
        {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("cannot create cache staging file: {error}")),
        };
        if let Err(error) = file.write_all(contents) {
            let _ = fs::remove_file(&temporary);
            return Err(format!("cannot write cache staging file: {error}"));
        }
        return Ok(temporary);
    }
    Err("cannot allocate a unique cache staging file".into())
}

fn publish_cache_file(target: &Path, contents: &[u8], description: &str) -> Result<(), String> {
    let temporary = write_cache_staging(target, contents)?;
    if let Err(error) = fs::rename(&temporary, target) {
        let _ = fs::remove_file(temporary);
        return Err(format!("cannot publish {description}: {error}"));
    }
    Ok(())
}

fn cleanup_abandoned_staging(directory: &Path) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    let now = SystemTime::now();
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if !path.extension().is_some_and(|extension| extension == "tmp") {
            continue;
        }
        let stale = entry
            .metadata()
            .and_then(|metadata| metadata.modified())
            .ok()
            .and_then(|modified| now.duration_since(modified).ok())
            .is_some_and(|age| age > Duration::from_secs(60 * 60));
        if stale {
            let _ = fs::remove_file(path);
        }
    }
}

fn stable_hash(bytes: &[u8]) -> u128 {
    let mut hash = 0x6c62272e07bb014262b821756295c58du128;
    for byte in bytes {
        hash ^= u128::from(*byte);
        hash = hash.wrapping_mul(0x0000000001000000000000000000013bu128);
    }
    hash
}

fn read_cached_expansion(directory: &Path, key: &str) -> Option<Vec<Expr>> {
    cleanup_abandoned_staging(directory);
    let bytes = fs::read(cache_path(directory, key)).ok()?;
    if bytes.get(..8)? != b"LIMGEN2\0" {
        return None;
    }
    let mut cursor = 8;
    let key_length = read_cache_length(&bytes, &mut cursor)?;
    let key_end = cursor.checked_add(key_length)?;
    if bytes.get(cursor..key_end)? != key.as_bytes() {
        return None;
    }
    cursor = key_end;
    let source_length = read_cache_length(&bytes, &mut cursor)?;
    let source_end = cursor.checked_add(source_length)?;
    let source_bytes = bytes.get(cursor..source_end)?;
    cursor = source_end;
    let checksum_end = cursor.checked_add(16)?;
    if checksum_end != bytes.len() {
        return None;
    }
    let checksum = u128::from_le_bytes(bytes.get(cursor..checksum_end)?.try_into().ok()?);
    if checksum != stable_hash(&bytes[..cursor]) {
        return None;
    }
    let source = std::str::from_utf8(source_bytes).ok()?;
    Some(
        crate::parse(source)
            .ok()?
            .into_iter()
            .map(|expression| expression.expr)
            .collect(),
    )
}

fn read_cache_length(bytes: &[u8], cursor: &mut usize) -> Option<usize> {
    let end = cursor.checked_add(8)?;
    let length = u64::from_le_bytes(bytes.get(*cursor..end)?.try_into().ok()?);
    *cursor = end;
    usize::try_from(length).ok()
}

fn write_cached_expansion(directory: &Path, key: &str, expressions: &[Expr]) {
    let source = expressions
        .iter()
        .map(crate::expression_source)
        .collect::<Result<Vec<_>, _>>();
    let Ok(source) = source else {
        return;
    };
    let source = source.join("\n");
    let path = cache_path(directory, key);
    if fs::create_dir_all(directory).is_err() {
        return;
    }
    if let Ok(existing) = fs::read(&path) {
        if let Some(existing_key) = cached_expansion_key(&existing) {
            if existing_key != key.as_bytes()
                && std::str::from_utf8(existing_key)
                    .is_ok_and(|value| cache_path(directory, value) == path)
            {
                // A genuine digest collision must not overwrite the other entry.
                return;
            }
        }
    }
    let mut contents = Vec::with_capacity(40 + key.len() + source.len());
    contents.extend_from_slice(b"LIMGEN2\0");
    contents.extend_from_slice(&(key.len() as u64).to_le_bytes());
    contents.extend_from_slice(key.as_bytes());
    contents.extend_from_slice(&(source.len() as u64).to_le_bytes());
    contents.extend_from_slice(source.as_bytes());
    contents.extend_from_slice(&stable_hash(&contents).to_le_bytes());
    let _ = publish_cache_file(&path, &contents, "generator syntax cache");
}

fn cached_expansion_key(bytes: &[u8]) -> Option<&[u8]> {
    if bytes.get(..8)? != b"LIMGEN2\0" {
        return None;
    }
    let mut cursor = 8;
    let length = read_cache_length(bytes, &mut cursor)?;
    bytes.get(cursor..cursor.checked_add(length)?)
}

fn evaluate(
    expression: &Expr,
    environment: &Environment,
    context: &mut ExpansionContext<'_>,
) -> Result<Value, String> {
    if context.budget.evaluation_steps == 0 {
        return Err(format!(
            "generator evaluation exceeds maximum of {MAX_EVALUATION_STEPS} steps"
        ));
    }
    context.budget.evaluation_steps -= 1;
    if let Expr::Symbol(name) = expression {
        return Ok(Value::Syntax(
            environment
                .get(name)
                .cloned()
                .unwrap_or_else(|| expression.clone()),
        ));
    }
    if let Expr::QuasiQuote(template) = expression {
        return match evaluate_template(template, environment, context, 1, false)? {
            TemplateValue::Syntax(syntax) => Ok(Value::Syntax(syntax)),
            TemplateValue::Splice(_) => {
                Err("unquote-splicing is only valid inside a syntax list".into())
            }
        };
    }
    if matches!(expression, Expr::Unquote(_) | Expr::UnquoteSplicing(_)) {
        return Err("unquote forms are only valid inside a backtick syntax template".into());
    }
    let Expr::List(items) = expression else {
        return Ok(Value::Syntax(expression.clone()));
    };
    let operator = match items.first() {
        Some(Expr::Symbol(operator)) => operator.as_str(),
        _ => return Ok(Value::Syntax(expression.clone())),
    };
    match operator {
        "#gn-if" => {
            arity(operator, items, 4)?;
            match evaluate(&items[1], environment, context)? {
                Value::Boolean(true) => evaluate(&items[2], environment, context),
                Value::Boolean(false) => evaluate(&items[3], environment, context),
                Value::Syntax(_) => Err("#gn-if condition must be a #gn predicate".into()),
            }
        }
        "#gn-equal" => {
            arity(operator, items, 3)?;
            let left = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let right = syntax(evaluate(&items[2], environment, context)?, operator)?;
            Ok(Value::Boolean(left == right))
        }
        "#gn-symbol?" | "#gn-list?" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, context)?, operator)?;
            Ok(Value::Boolean(if operator == "#gn-symbol?" {
                matches!(value, Expr::Symbol(_))
            } else {
                matches!(value, Expr::List(_))
            }))
        }
        "#gn-symbol" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let Expr::String(value) = value else {
                return Err("#gn-symbol requires a string literal".into());
            };
            Ok(Value::Syntax(Expr::Symbol(value)))
        }
        "#gn-list" => {
            let mut values = Vec::with_capacity(items.len().saturating_sub(1));
            for item in &items[1..] {
                values.push(syntax(evaluate(item, environment, context)?, operator)?);
            }
            Ok(Value::Syntax(Expr::List(values)))
        }
        "#gn-first" | "#gn-rest" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let Expr::List(values) = value else {
                return Err(format!("{operator} requires list syntax"));
            };
            if operator == "#gn-first" {
                values
                    .into_iter()
                    .next()
                    .map(Value::Syntax)
                    .ok_or_else(|| "#gn-first cannot read an empty list".into())
            } else {
                Ok(Value::Syntax(Expr::List(
                    values.into_iter().skip(1).collect(),
                )))
            }
        }
        "#gn-for-each" => {
            arity(operator, items, 4)?;
            let variable = symbol(items.get(1), "#gn-for-each binding")?.to_owned();
            let list = syntax(evaluate(&items[2], environment, context)?, operator)?;
            let Expr::List(values) = list else {
                return Err("#gn-for-each requires a list of syntax values".into());
            };
            let mut result = Vec::with_capacity(values.len());
            for value in values {
                let mut nested = environment.clone();
                nested.insert(variable.clone(), value);
                match evaluate(&items[3], &nested, context)? {
                    Value::Syntax(syntax) => result.push(syntax),
                    Value::Boolean(_) => return Err("#gn-for-each body must produce syntax".into()),
                }
            }
            Ok(Value::Syntax(Expr::List(result)))
        }
        "#gn-call" => {
            if items.len() < 2 {
                return Err("#gn-call requires a function name".into());
            }
            let name = symbol(items.get(1), "#gn-call function name")?;
            let Some(function) = context.functions.get(name).cloned() else {
                return Err(format!("unknown generator function '{name}'"));
            };
            if items.len() - 2 != function.parameters.len() {
                return Err(format!(
                    "#gn-call {name} expects {} syntax argument(s), received {}",
                    function.parameters.len(),
                    items.len() - 2
                ));
            }
            if context.active_functions.iter().any(|active| active == name) {
                let mut chain = context.active_functions.join(" -> ");
                if !chain.is_empty() {
                    chain.push_str(" -> ");
                }
                chain.push_str(name);
                return Err(format!(
                    "recursive generator function calls are not allowed: {chain}"
                ));
            }
            let mut nested = Environment::new();
            for (parameter, argument) in function.parameters.iter().zip(&items[2..]) {
                nested.insert(
                    parameter.name.clone(),
                    syntax(evaluate(argument, environment, context)?, "#gn-call")?,
                );
            }
            context.active_functions.push(name.to_owned());
            let result = evaluate(&function.body, &nested, context);
            context.active_functions.pop();
            match result? {
                value @ Value::Syntax(_) => Ok(value),
                Value::Boolean(_) => Err(format!(
                    "#gn-fn {name} must return a syntax value (symbol, literal, or list)"
                )),
            }
        }
        "#gn-error" => {
            arity(operator, items, 2)?;
            let message = syntax(evaluate(&items[1], environment, context)?, operator)?;
            match message {
                Expr::String(message) => Err(format!("generator error: {message}")),
                _ => Err("#gn-error requires a string literal message".into()),
            }
        }
        _ if operator.starts_with("#gn-") => Err(format!("unknown generator builtin '{operator}'")),
        _ => Ok(Value::Syntax(expression.clone())),
    }
}

fn evaluate_template(
    expression: &Expr,
    environment: &Environment,
    context: &mut ExpansionContext<'_>,
    depth: usize,
    splice_allowed: bool,
) -> Result<TemplateValue, String> {
    if context.budget.evaluation_steps == 0 {
        return Err(format!(
            "generator evaluation exceeds maximum of {MAX_EVALUATION_STEPS} steps"
        ));
    }
    context.budget.evaluation_steps -= 1;
    match expression {
        Expr::QuasiQuote(inner) => {
            match evaluate_template(inner, environment, context, depth + 1, false)? {
                TemplateValue::Syntax(inner) => {
                    Ok(TemplateValue::Syntax(Expr::QuasiQuote(Box::new(inner))))
                }
                TemplateValue::Splice(_) => unreachable!("nested quasiquote root cannot splice"),
            }
        }
        Expr::Unquote(inner) if depth == 1 => Ok(TemplateValue::Syntax(syntax(
            evaluate(inner, environment, context)?,
            "unquote",
        )?)),
        Expr::Unquote(inner) => {
            match evaluate_template(inner, environment, context, depth - 1, false)? {
                TemplateValue::Syntax(inner) => {
                    Ok(TemplateValue::Syntax(Expr::Unquote(Box::new(inner))))
                }
                TemplateValue::Splice(_) => unreachable!("unquote root cannot splice"),
            }
        }
        Expr::UnquoteSplicing(inner) if depth == 1 => {
            if !splice_allowed {
                return Err("unquote-splicing is only valid inside a syntax list".into());
            }
            let value = syntax(evaluate(inner, environment, context)?, "unquote-splicing")?;
            match value {
                Expr::List(values) => Ok(TemplateValue::Splice(values)),
                _ => Err("unquote-splicing requires list syntax".into()),
            }
        }
        Expr::UnquoteSplicing(inner) => {
            match evaluate_template(inner, environment, context, depth - 1, false)? {
                TemplateValue::Syntax(inner) => Ok(TemplateValue::Syntax(Expr::UnquoteSplicing(
                    Box::new(inner),
                ))),
                TemplateValue::Splice(_) => {
                    unreachable!("nested unquote-splicing root cannot splice")
                }
            }
        }
        Expr::List(items) => {
            let mut result = Vec::new();
            for item in items {
                match evaluate_template(item, environment, context, depth, true)? {
                    TemplateValue::Syntax(value) => result.push(value),
                    TemplateValue::Splice(values) => result.extend(values),
                }
            }
            Ok(TemplateValue::Syntax(Expr::List(result)))
        }
        other => Ok(TemplateValue::Syntax(other.clone())),
    }
}

fn syntax(value: Value, operation: &str) -> Result<Expr, String> {
    match value {
        Value::Syntax(value) => Ok(value),
        Value::Boolean(_) => Err(format!("{operation} requires syntax")),
    }
}

fn arity(operation: &str, items: &[Expr], expected: usize) -> Result<(), String> {
    if items.len() == expected {
        Ok(())
    } else {
        Err(format!("{operation} requires {} argument(s)", expected - 1))
    }
}

fn symbol<'a>(expression: Option<&'a Expr>, context: &str) -> Result<&'a str, String> {
    match expression {
        Some(Expr::Symbol(value)) => Ok(value.strip_prefix('#').unwrap_or(value)),
        _ => Err(format!("expected symbol for {context}")),
    }
}

fn is_operator(expression: Option<&Expr>, expected: &str) -> bool {
    matches!(expression, Some(Expr::Symbol(name)) if name == expected)
}

fn at_span(message: String, span: Span, context: &str) -> String {
    format!(
        "{}:{}: {context}: {message}; source span {}:{}:{}",
        span.line, span.column, span.source_id, span.start, span.end
    )
}

fn expression_nodes(expression: &Expr) -> usize {
    match expression {
        Expr::List(items) => 1usize.saturating_add(items.iter().map(expression_nodes).sum()),
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value)
        | Expr::Labeled {
            expression: value, ..
        } => 1usize.saturating_add(expression_nodes(value)),
        _ => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inspectable_generated_source_cache_uses_the_full_key_and_reuses_source() {
        let directory =
            std::env::temp_dir().join(format!("lim-inspectable-cache-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        let first =
            cached_generated_source(&directory, "key-a", || Ok("(#type Cached u64)".into()))
                .unwrap();
        let source_path = fs::read_dir(&directory)
            .unwrap()
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .find(|path| path.extension().is_some_and(|extension| extension == "lim"))
            .unwrap();
        fs::write(&source_path, "(#type Edited u64)").unwrap();
        let mut regenerated = false;
        let second = cached_generated_source(&directory, "key-a", || {
            regenerated = true;
            Ok("(#type Cached u64)".into())
        })
        .unwrap();
        assert!(regenerated, "edited but valid source must not be trusted");
        assert_eq!(fs::read_to_string(source_path).unwrap(), second);
        let different =
            cached_generated_source(&directory, "key-b", || Ok("(#type Other u64)".into()))
                .unwrap();
        assert_eq!(first, second);
        assert_ne!(first, different);
        let entries = fs::read_dir(&directory)
            .unwrap()
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .collect::<Vec<_>>();
        assert_eq!(
            entries
                .iter()
                .filter(|path| path.extension().is_some_and(|ext| ext == "lim"))
                .count(),
            2
        );
        assert_eq!(
            entries
                .iter()
                .filter(|path| path.extension().is_some_and(|ext| ext == "key"))
                .count(),
            2
        );
        let _ = fs::remove_dir_all(directory);
    }

    #[test]
    fn generated_source_cache_publication_is_safe_for_concurrent_writers() {
        let directory = std::env::temp_dir().join(format!(
            "lim-concurrent-generated-cache-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let abandoned = directory.join("abandoned.1-0.tmp");
        fs::write(&abandoned, "incomplete cache write").unwrap();
        let old_time = SystemTime::now() - Duration::from_secs(2 * 60 * 60);
        OpenOptions::new()
            .write(true)
            .open(&abandoned)
            .unwrap()
            .set_times(fs::FileTimes::new().set_modified(old_time))
            .unwrap();
        let workers = (0..12)
            .map(|index| {
                let directory = directory.clone();
                std::thread::spawn(move || {
                    let (key, source) = if index % 2 == 0 {
                        ("shared-key", "(#type Shared u64)")
                    } else {
                        ("other-key", "(#type Other u64)")
                    };
                    cached_generated_source(&directory, key, || Ok(source.into())).unwrap()
                })
            })
            .collect::<Vec<_>>();
        for (index, worker) in workers.into_iter().enumerate() {
            assert_eq!(
                worker.join().unwrap(),
                if index % 2 == 0 {
                    "(#type Shared u64)"
                } else {
                    "(#type Other u64)"
                }
            );
        }
        assert_eq!(
            cached_generated_source(&directory, "shared-key", || {
                Err("concurrent cache entry was not published coherently".into())
            })
            .unwrap(),
            "(#type Shared u64)"
        );
        assert_eq!(
            cached_generated_source(&directory, "other-key", || {
                Err("concurrent cache entry was not published coherently".into())
            })
            .unwrap(),
            "(#type Other u64)"
        );
        assert!(fs::read_dir(&directory)
            .unwrap()
            .filter_map(Result::ok)
            .all(|entry| entry
                .path()
                .extension()
                .is_some_and(|extension| extension != "tmp")));
        assert!(!abandoned.exists(), "stale staging file should be removed");
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn generator_evaluation_has_a_finite_step_budget() {
        let expression = Expr::List(
            std::iter::once(Expr::Symbol("#gn-list".into()))
                .chain((0..=MAX_EVALUATION_STEPS).map(|_| Expr::Integer(0)))
                .collect(),
        );
        let error = evaluate(
            &expression,
            &Environment::new(),
            &mut ExpansionContext {
                generators: &HashMap::new(),
                functions: &HashMap::new(),
                capabilities: &HashMap::new(),
                capability_hash: 0,
                generator_fingerprints: HashMap::new(),
                active_functions: Vec::new(),
                active: Vec::new(),
                seen_invocations: HashSet::new(),
                budget: Budget {
                    evaluation_steps: MAX_EVALUATION_STEPS,
                    generated_nodes: 0,
                },
                cache_hits: 0,
                cache_dir: None,
                dependency_context: "",
                invocation_span: None,
            },
        )
        .unwrap_err();
        assert!(error.contains("exceeds maximum"));
    }

    #[test]
    fn generated_syntax_cache_hits_and_invalidates_for_generator_dependencies() {
        let directory =
            std::env::temp_dir().join(format!("lim-generator-cache-{}", std::process::id()));
        let source = "(#gn-fn make-type (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name u64))) (#gn-fn make-alias (name) `,(#gn-call make-type name)) (#gn-fn unused (name) (#gn-list name)) (#generator alias (name) (#gn-call make-alias name)) (#generator forward (call) (#gn-list call)) (#generator spare (name) (#gn-list name)) (@forward (@alias CachedType)) (@alias CachedType)";
        let parse_forms = |source: &str| crate::parse(source).unwrap();

        let ((first, _), first_hits) =
            expand_with_generated_cached_and_hits(parse_forms(source), Some(&directory), "")
                .unwrap();
        assert_eq!(first_hits, 0);
        assert_eq!(first.len(), 1, "nested duplicate invocations deduplicate");

        let ((second, _), second_hits) =
            expand_with_generated_cached_and_hits(parse_forms(source), Some(&directory), "")
                .unwrap();
        assert!(
            second_hits >= 1,
            "an identical generator call should hit disk cache"
        );
        for entry in fs::read_dir(&directory).unwrap().filter_map(Result::ok) {
            let path = entry.path();
            if path
                .extension()
                .is_some_and(|extension| extension == "cache")
            {
                let mut contents = fs::read(&path).unwrap();
                let cached = b"CachedType";
                let edited = b"HackedType";
                if let Some(offset) = contents
                    .windows(cached.len())
                    .position(|part| part == cached)
                {
                    contents[offset..offset + cached.len()].copy_from_slice(edited);
                    fs::write(path, contents).unwrap();
                }
            }
        }
        let ((third, _), third_hits) =
            expand_with_generated_cached_and_hits(parse_forms(source), Some(&directory), "")
                .unwrap();
        assert_eq!(third_hits, 0, "edited cache bytes must fail verification");
        assert_eq!(third, first);
        let syntax = |forms: &[SpannedExpr]| {
            forms
                .iter()
                .map(|form| form.expr.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(syntax(&second), syntax(&first));
        assert_eq!(
            second.len(),
            1,
            "cached raw forms still expand and deduplicate nested invocations"
        );

        let unrelated_change = source.replace("(#gn-list name)", "(#gn-list name name)");
        let ((unrelated, _), unrelated_hits) = expand_with_generated_cached_and_hits(
            parse_forms(&unrelated_change),
            Some(&directory),
            "",
        )
        .unwrap();
        assert!(
            unrelated_hits >= 2,
            "changing an unrelated helper should preserve both cache hits"
        );
        assert_eq!(syntax(&unrelated), syntax(&second));

        let changed_dependency = source.replace("name u64", "name u32");
        let ((changed, _), changed_hits) = expand_with_generated_cached_and_hits(
            parse_forms(&changed_dependency),
            Some(&directory),
            "",
        )
        .unwrap();
        assert_eq!(changed_hits, 1, "only the dependent invocation should miss");
        assert_ne!(changed, second);
        let _ = std::fs::remove_dir_all(directory);
    }

    #[test]
    fn generated_cache_invalidates_when_capability_contract_changes() {
        let directory = std::env::temp_dir().join(format!(
            "lim-generator-capability-cache-{}",
            std::process::id()
        ));
        let source = |operation: &str| {
            format!(
                "(#fn less ((a (#ref u64)) (b (#ref u64))) bool (#return true)) (#fn less-v2 ((a (#ref u64)) (b (#ref u64))) bool (#return true)) (#capability sortable u64 (({operation} ((#ref u64) (#ref u64)) bool))) (#generator emit ((element sortable)) (#gn-list (#gn-list (#gn-symbol \"#type\") Generated element))) (@emit u64)"
            )
        };
        let expand = |text: &str| {
            expand_with_generated_cached_and_hits(crate::parse(text).unwrap(), Some(&directory), "")
                .unwrap()
        };

        let ((first, _), first_hits) = expand(&source("less"));
        assert_eq!(first_hits, 0);
        let ((again, _), again_hits) = expand(&source("less"));
        assert!(again_hits > 0);
        assert_eq!(first[0].expr, again[0].expr);

        let ((changed, _), changed_hits) = expand(&source("less-v2"));
        assert_eq!(
            changed_hits, 0,
            "a changed capability contract must miss cache"
        );
        assert_eq!(first[0].expr, changed[0].expr);
        let _ = fs::remove_dir_all(directory);
    }

    #[test]
    fn generated_syntax_cache_includes_import_and_cfg_context() {
        let directory =
            std::env::temp_dir().join(format!("lim-generator-context-{}", std::process::id()));
        let source =
            "(#generator make (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name u64))) (@make ContextType)";
        let parse_forms = |source: &str| crate::parse(source).unwrap();

        let ((first, _), first_hits) = expand_with_generated_cached_and_hits(
            parse_forms(source),
            Some(&directory),
            "imports=module-a\ncfg=feature=one",
        )
        .unwrap();
        assert_eq!(first_hits, 0);
        let ((same, _), same_hits) = expand_with_generated_cached_and_hits(
            parse_forms(source),
            Some(&directory),
            "imports=module-a\ncfg=feature=one",
        )
        .unwrap();
        assert!(same_hits >= 1);
        assert_eq!(same, first);

        let ((changed, _), changed_hits) = expand_with_generated_cached_and_hits(
            parse_forms(source),
            Some(&directory),
            "imports=module-b\ncfg=feature=one",
        )
        .unwrap();
        assert_eq!(changed_hits, 0);
        assert_eq!(changed, first);
        let _ = std::fs::remove_dir_all(directory);
    }
}
