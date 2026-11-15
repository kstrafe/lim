//! Pure, immutable syntax generators used by `#generate name` declarations.

use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    fs::{self, OpenOptions},
    io::{Read, Write},
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicU64, Ordering},
        Mutex, OnceLock,
    },
    time::{Duration, Instant, SystemTime},
};

use crate::generator_authority::Syntax;
use crate::{Expr, Span, SpannedExpr};

pub(crate) const GENERATED_SOURCE_FORMAT: &str = "lim-generated-source-format-v4-explicit-effects";
const MAX_EVALUATION_STEPS: usize = 200_000;
const MAX_GENERATED_NODES: usize = 1_000_000;
const MAX_EXPANSION_DEPTH: usize = 128;
const MAX_CACHE_ARTIFACT_BYTES: u64 = 64 * 1024 * 1024;
static CACHE_TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);
static INTERPRETER_HASH: OnceLock<u128> = OnceLock::new();
// Housekeeping is independent of cache correctness. Bound both its frequency
// and retained directory history for callers compiling many projects.
const CACHE_CLEANUP_INTERVAL: Duration = Duration::from_secs(60);
const MAX_CLEANUP_DIRECTORIES: usize = 64;
static CACHE_CLEANUP_TIMES: OnceLock<Mutex<HashMap<PathBuf, Instant>>> = OnceLock::new();

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
    Syntax(Syntax),
    Boolean(bool),
}

enum TemplateValue {
    Syntax(Syntax),
    Splice(Vec<Syntax>),
}

pub(crate) mod array;
pub(crate) mod async_addresses;
pub(crate) mod async_aggregate;
pub(crate) mod async_array_anchor;
pub(crate) mod async_cells;
// Independent source-contract regressions; executable lowering uses the
// checked original-body graph rather than these former syntax probes.
#[cfg(test)]
pub(crate) mod async_cfg;
#[cfg(test)]
pub(crate) mod async_contract;
pub(crate) mod async_emit;
pub(crate) mod async_exec;
pub(crate) mod async_immediate;
pub(crate) mod async_initialization;
pub(crate) mod async_interfaces;
pub(crate) mod async_layout;
pub(crate) mod async_lease;
pub(crate) mod async_lend;
pub(crate) mod async_owner;
pub(crate) mod async_pattern;
pub(crate) mod async_prepare;
pub(crate) mod async_preview_alias;
pub(crate) mod async_projection;
pub(crate) mod async_render;
pub(crate) mod async_retire;
pub(crate) mod async_self_borrow;
pub(crate) mod async_slice_anchor;
pub(crate) mod async_source;
pub(crate) mod async_types;
mod async_word_cleanup;
pub(crate) mod builtins;
mod effects;
pub(crate) mod frontend;
pub(crate) use crate::capture_storage as async_storage;
pub(crate) mod async_values;

type Environment = HashMap<String, Syntax>;
type ExpandedForms = (Vec<SpannedExpr>, Vec<Expr>);
type ExpandedFormsWithHits = (ExpandedForms, usize);

fn declared_lim_function_signatures(
    expressions: &[SpannedExpr],
) -> Result<HashMap<String, String>, crate::source_error::SourceError> {
    let mut signatures = HashMap::new();
    for expression in expressions {
        let Expr::List(raw_items) = &expression.expr else {
            continue;
        };
        let Some(Expr::Symbol(kind)) = raw_items.first() else {
            continue;
        };
        let external = match kind.as_str() {
            "#fn" | "#unsafe-fn" => false,
            "#extern-fn" => true,
            _ => continue,
        };
        // Capability contracts use signatures, never bodies. Body syntax and
        // safety are still checked by the ordinary frontend after expansion.
        let header_len = if external {
            raw_items.len()
        } else {
            raw_items.len().min(4)
        };
        let normalized =
            crate::normalize_keywords(Expr::List(raw_items[..header_len].to_vec().into()));
        let Expr::List(items) = &normalized else {
            unreachable!()
        };
        let function = crate::parse_function_parts(items, external, false).map_err(|error| {
            let span = Span {
                end: expression
                    .children
                    .first()
                    .map_or(expression.span.end, |head| head.span.end),
                ..expression.span
            };
            crate::source_error::SourceError::new(error, crate::DiagnosticCode::Parse).at(span)
        })?;
        let arguments = function
            .parameters
            .iter()
            .map(|parameter| parameter.ty.clone())
            .collect::<Vec<_>>();
        let safety = if function.unsafe_call { "unsafe " } else { "" };
        let signature = format!("{safety}{arguments:?}->{:?}", function.return_type);
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

#[cfg(test)]
#[test]
fn capability_signature_scan_does_not_parse_function_bodies() {
    let source = "#fn answer { #params = ((value #u64)); #returns = #u64; #body = ( (#not-a-builtin value) ); }\n";
    let signatures = declared_lim_function_signatures(&crate::parse_source_unit(source).unwrap()).unwrap();
    assert_eq!(signatures["answer"], "[U64]->U64");
    // Skipping bodies here must not skip ordinary compilation validation.
    assert!(crate::parse_program(source).is_err());
    assert!(declared_lim_function_signatures(
        &crate::parse("(#extern-fn #abi-c foreign () #u64 (#return 42u64))").unwrap()
    )
    .is_err());
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

#[derive(Default)]
pub(crate) struct Origins {
    pub qualified: HashSet<Span>,
    pub definitions: HashMap<u32, Span>,
    pub generated_sources: Vec<(crate::SourceFile, Span)>,
    pub visibility: Option<crate::library::Visibility>,
    pub user: HashSet<Span>,
    pub builtins: HashMap<String, Vec<Span>>,
    pub source_invocation_names: HashMap<Span, String>,
    pub source_paths: Vec<PathBuf>,
    pub standard_declarations: HashSet<Span>,
    pub generation: crate::generator_provenance::Registry,
}

impl Origins {
    pub(crate) fn context_header(
        &self,
        producer: &str,
        definition: Span,
        invocation: Span,
    ) -> String {
        let invocation = self.invocation_origin(invocation);
        let descriptor = |span: Span| {
            self.visibility.as_ref().map_or_else(
                || ("<global>".into(), String::new()),
                |visibility| visibility.module_context(span),
            )
        };
        let (definition_module, definition_file) = descriptor(definition);
        let (invocation_module, invocation_file) = descriptor(invocation);
        let pair = |key: &str, value: String| {
            Expr::List(vec![Expr::Symbol(key.into()), Expr::String(value)].into())
        };
        let header = Expr::List(
            vec![
                Expr::Symbol(crate::generator_authority::HEADER.into()),
                Expr::List(
                    vec![
                        pair("producer", producer.into()),
                        pair("definition-module", definition_module),
                        pair("definition-file", definition_file),
                        pair("invocation-module", invocation_module),
                        pair("invocation-file", invocation_file),
                    ]
                    .into(),
                ),
            ]
            .into(),
        );
        crate::expression_source(&header).expect("context header contains only reader syntax")
    }

    fn invocation_origin(&self, mut span: Span) -> Span {
        for _ in 0..self.generated_sources.len() {
            let Some(index) = (span.source_id as usize).checked_sub(self.source_paths.len()) else {
                break;
            };
            let Some((_, origin)) = self.generated_sources.get(index) else {
                break;
            };
            span = *origin;
        }
        span
    }

    pub(crate) fn expansion_context(&self, span: Span) -> String {
        self.visibility
            .as_ref()
            .map_or_else(String::new, |visibility| {
                visibility.expansion_context(self.invocation_origin(span))
            })
    }

    pub(crate) fn authority_signature(&self, form: &SpannedExpr) -> String {
        // Direct syntax has its own file's authority, just as a template
        // authored in that file does. Keep other producers distinct.
        let definition = crate::generator_authority::source_context(form.span, &self.definitions)
            .unwrap_or(form.span);
        self.expansion_context(definition)
    }
}

pub(crate) fn expand_with_origins(
    expressions: Vec<SpannedExpr>,
    cache_dir: Option<&Path>,
    dependency_context: &str,
    origins: &mut Origins,
) -> Result<ExpandedForms, crate::source_error::SourceError> {
    expand_with_hits_and_origins(expressions, cache_dir, dependency_context, origins)
        .map(|(result, _)| result)
}

#[cfg(test)]
fn expand_with_generated_cached_and_hits(
    expressions: Vec<SpannedExpr>,
    cache_dir: Option<&Path>,
    dependency_context: &str,
) -> Result<ExpandedFormsWithHits, crate::source_error::SourceError> {
    expand_with_hits_and_origins(
        expressions,
        cache_dir,
        dependency_context,
        &mut Origins::default(),
    )
}

fn expand_with_hits_and_origins(
    expressions: Vec<SpannedExpr>,
    cache_dir: Option<&Path>,
    dependency_context: &str,
    origins: &mut Origins,
) -> Result<ExpandedFormsWithHits, crate::source_error::SourceError> {
    for expression in &expressions {
        crate::validate_reserved_declarations(&expression.expr).map_err(|error| {
            let span =
                crate::reserved_declaration_span(expression, &error).unwrap_or(expression.span);
            at_span(error, span, "declaration")
        })?;
        if let Expr::List(items) = &expression.expr {
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#gn" || head == "#gn-fn")
            {
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    if name.starts_with('#')
                        && !origins.standard_declarations.contains(&expression.span)
                        && !crate::standard_library::is_generator_declaration(&expression.expr)
                    {
                        return Err(at_span(
                            format!("identifier '{name}' is reserved for the language and standard library"),
                            expression.children.get(1).map_or(expression.span, |name| name.span),
                            "generator name",
                        ));
                    }
                }
            }
        }
        if crate::gensym::contains_reserved(&expression.expr) {
            return Err(at_span(
                "identifiers beginning with 'lim.gensym.' are reserved for compiler-generated symbols",
                expression.span,
                "generator input",
            ));
        }
    }
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
                        "#capability requires a name, concrete type, and operation contracts",
                        expression.span,
                        "capability declaration",
                    ));
                }
                let mut operations = HashMap::new();
                let operation_forms = match items.get(3) {
                    Some(Expr::List(forms)) if !forms.is_empty() => forms,
                    _ => {
                        return Err(at_span(
                            "#capability operation contracts must be a non-empty list",
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
                            "capability operations have the form (function (ArgumentType ...) ReturnType)",
                            expression.span,
                            "capability declaration",
                        ));
                    };
                    if parts.len() != 3 {
                        return Err(at_span(
                            "capability operations have the form (function (ArgumentType ...) ReturnType)",
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
                                "capability operation argument types must be a list",
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
            if is_operator(items.first(), "#gn") {
                let generator = parse_generator(items, &expression).map_err(|error| {
                    if error.span.is_some() {
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

    // Preserve explicit global qualification in the interpreter even when a
    // generator parameter happens to have the same spelling. The normalized
    // Function node is compiler-only and is converted back to symbol syntax
    // when evaluated; no marker survives into generated code.
    fn bind_qualified(expr: &mut Expr, source: &SpannedExpr, qualified: &HashSet<Span>) {
        if qualified.contains(&source.span) {
            if let Expr::Symbol(name) = expr {
                *expr = Expr::Function(name.clone());
            }
            return;
        }
        match expr {
            Expr::List(items) => {
                for (item, source) in items.iter_mut().zip(&source.children) {
                    bind_qualified(item, source, qualified);
                }
            }
            Expr::Quote(inner)
            | Expr::QuasiQuote(inner)
            | Expr::Unquote(inner)
            | Expr::UnquoteSplicing(inner) => {
                if let Some(source) = source.children.first() {
                    bind_qualified(inner, source, qualified);
                }
            }
            _ => {}
        }
    }
    for definition in generators.values_mut().chain(functions.values_mut()) {
        if let Some(source) = &definition.source_body {
            bind_qualified(&mut definition.body, source, &origins.qualified);
        }
    }
    let interpreter_hash = interpreter_hash();
    let capability_hash = hash_capability_definitions(&capabilities);
    let function_hashes = generator_function_hashes(&functions, interpreter_hash)?;
    let generator_hashes = generator_hashes(&generators, &function_hashes, interpreter_hash);
    let mut context = ExpansionContext {
        generators: &generators,
        functions: &functions,
        capabilities: &capabilities,
        capability_hash,
        generator_fingerprints: generator_hashes,
        active_functions: Vec::new(),
        active: Vec::new(),
        gensym_scopes: Vec::new(),
        gensyms: crate::gensym::Registry::default(),
        seen_invocations: HashSet::new(),
        invocation_artifacts: HashMap::new(),
        invocation_children: HashMap::new(),
        active_invocations: Vec::new(),
        generation_origins: Vec::new(),
        origins,
        invocation_builtins: HashMap::new(),
        active_builtins: Vec::new(),
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
        // Ordinary forms pass through intact, including every nested source span.
        // Only generator invocations need expansion.
        let needs_expansion = matches!(&expression.expr, Expr::List(items)
            if matches!(items.first(), Some(Expr::Generate)));
        if !needs_expansion {
            output.push(expression);
            continue;
        }
        context.invocation_span = Some(expression.span);
        if crate::generated_lookup::enabled() {
            if let Expr::List(items) = &expression.expr {
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    context
                        .origins
                        .source_invocation_names
                        .insert(expression.span, name.clone());
                }
            }
        }
        let is_user_invocation = match &expression.expr {
            Expr::List(items) if matches!(items.first(), Some(Expr::Generate)) => items
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
        let expanded = expand_top(expression.expr.into(), &mut context)
            .map_err(|error| at_span(error, expression.span, "generator expansion"))?;
        if is_user_invocation {
            for form in &expanded {
                context.budget.generated_nodes = context
                    .budget
                    .generated_nodes
                    .saturating_add(expression_nodes(&form.expr));
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
            generated.extend(expanded.iter().map(|form| form.expr.clone()));
        }
        for syntax in expanded {
            if syntax.has_authority() {
                let definition = syntax.authority().unwrap();
                let producer = context
                    .generators
                    .iter()
                    .find_map(|(name, generator)| {
                        (generator.span == definition).then_some(name.as_str())
                    })
                    .unwrap_or("<builtin>");
                let header = context
                    .origins
                    .context_header(producer, definition, expression.span);
                let text = format_generated_syntax(&format!(
                    "{header}\n{}",
                    crate::expression_source(&syntax.expr)?
                ))?;
                let mut tree = crate::parse_source_unit(&text)?.remove(1);
                let id = u32::try_from(
                    context.origins.source_paths.len() + context.origins.generated_sources.len(),
                )
                .map_err(|_| "too many generated source files")?;
                crate::set_source_id(&mut tree, id);
                syntax.attach(&tree, &mut context.origins.definitions);
                context.origins.generated_sources.push((
                    crate::SourceFile {
                        file_scope: None,
                        path: format!(
                            "<generated from {}:{}:{}>",
                            context
                                .origins
                                .source_paths
                                .get(expression.span.source_id as usize)
                                .map_or_else(
                                    || "<source>".into(),
                                    |path| path.display().to_string()
                                ),
                            expression.span.line,
                            expression.span.column
                        )
                        .into(),
                        source: text,
                    },
                    expression.span,
                ));
                output.push(tree);
                continue;
            }
            let expr = syntax.expr;
            let unchanged = expr == original_expr;
            output.push(SpannedExpr {
                expr,
                span: expression.span,
                children: if unchanged {
                    original_children.clone()
                } else {
                    Vec::new().into()
                },
            });
        }
    }
    if let Some(span) = context.invocation_span {
        flush_invocation_artifacts(&context)
            .map_err(|error| at_span(error, span, "generated-source publication"))?;
    }
    Ok(((output, generated), context.cache_hits))
}

fn parse_generator_function(
    items: &[Expr],
    source: &SpannedExpr,
) -> Result<GeneratorFunction, crate::source_error::SourceError> {
    if items.len() != 4 {
        return Err("#gn-fn requires a name, parameter list, and body".into());
    }
    let generator = parse_generator(items, source).map_err(|mut error| {
        if error.message.starts_with("#gn requires ") {
            error.message = error.message.replacen("#gn", "#gn-fn", 1);
        }
        error.message = error.message.replace("generator '", "generator function '");
        error
    })?;
    Ok(generator)
}

fn parse_generator(
    items: &[Expr],
    source: &SpannedExpr,
) -> Result<Generator, crate::source_error::SourceError> {
    if items.len() != 4 {
        return Err("#gn requires a name, parameter list, and body".into());
    }
    let name = symbol(items.get(1), "generator name")?;
    let parameters = match items.get(2) {
        Some(Expr::List(parameters)) => parameters,
        _ => return Err(format!("generator '{name}' parameters must be a list").into()),
    };
    let mut names = Vec::with_capacity(parameters.len());
    for (parameter_index, parameter) in parameters.iter().enumerate() {
        let (name, capabilities) = match parameter {
            Expr::Symbol(name) => (name.as_str(), Vec::new()),
            Expr::List(items) if !items.is_empty() => {
                let name = match items.first() {
                    Some(Expr::Symbol(name)) => name.as_str(),
                    _ => {
                        let span = source
                            .children
                            .get(2)
                            .and_then(|parameters| parameters.children.get(parameter_index))
                            .and_then(|parameter| parameter.children.first())
                            .map_or(source.span, |node| node.span);
                        return Err(at_span(
                            "generator parameter declarations name one binding; nested lists are not destructuring patterns",
                            span,
                            "generator parameter",
                        ));
                    }
                };
                let mut required = Vec::new();
                for (annotation_index, capability) in items[1..].iter().enumerate() {
                    let capability = match capability {
                        Expr::Symbol(name) => name.as_str(),
                        _ => {
                            let span = source
                                .children
                                .get(2)
                                .and_then(|parameters| parameters.children.get(parameter_index))
                                .and_then(|parameter| parameter.children.get(annotation_index + 1))
                                .map_or(source.span, |node| node.span);
                            return Err(at_span(
                                "generator parameter annotations must be capability names, not nested patterns",
                                span,
                                "generator parameter",
                            ));
                        }
                    };
                    if capability.starts_with('#') || capability.starts_with('@') {
                        return Err(format!("invalid generator capability '{capability}'").into());
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
            return Err(format!("invalid generator parameter '{name}'").into());
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

struct InvocationArtifact {
    key: String,
    source: String,
    origins: HashSet<Span>,
    generator: Option<String>,
    direct_origins: HashSet<Span>,
    needs_publication: bool,
}

struct ExpansionContext<'a> {
    generators: &'a HashMap<String, Generator>,
    functions: &'a HashMap<String, GeneratorFunction>,
    capabilities: &'a Capabilities,
    capability_hash: u128,
    generator_fingerprints: HashMap<String, GeneratorFingerprint>,
    active_functions: Vec<String>,
    active: Vec<String>,
    gensym_scopes: Vec<crate::gensym::Scope>,
    gensyms: crate::gensym::Registry,
    seen_invocations: HashSet<String>,
    invocation_artifacts: HashMap<String, InvocationArtifact>,
    invocation_children: HashMap<String, HashSet<String>>,
    active_invocations: Vec<String>,
    generation_origins: Vec<crate::generator_provenance::Origin>,
    budget: Budget,
    cache_hits: usize,
    cache_dir: Option<&'a Path>,
    dependency_context: &'a str,
    invocation_span: Option<Span>,
    origins: &'a mut Origins,
    invocation_builtins: HashMap<String, Vec<String>>,
    active_builtins: Vec<Vec<String>>,
}

fn record_invocation_origins(key: &str, context: &mut ExpansionContext<'_>) {
    let Some(span) = context.invocation_span else {
        return;
    };
    if crate::generated_lookup::enabled() && context.active_invocations.is_empty() {
        if let Some(artifact) = context.invocation_artifacts.get_mut(key) {
            artifact.direct_origins.insert(span);
        }
    }
    let mut pending = vec![key.to_owned()];
    let mut visited = HashSet::new();
    while let Some(key) = pending.pop() {
        if !visited.insert(key.clone()) {
            continue;
        }
        if let Some(artifact) = context.invocation_artifacts.get_mut(&key) {
            artifact.origins.insert(span);
        }
        if let Some(children) = context.invocation_children.get(&key) {
            pending.extend(children.iter().cloned());
        }
    }
}

fn flush_invocation_artifacts(context: &ExpansionContext<'_>) -> Result<(), String> {
    let Some(directory) = context.cache_dir else {
        return Ok(());
    };
    let mut created_directories = false;
    for artifact in context.invocation_artifacts.values() {
        if crate::generated_lookup::enabled() {
            let (path, _) = generated_expansion_paths(directory, &artifact.key);
            for &span in &artifact.origins {
                crate::generated_lookup::record(
                    span,
                    &context.origins.source_paths,
                    &path,
                    artifact.generator.as_deref().unwrap_or_default(),
                    !artifact.direct_origins.contains(&span),
                );
            }
        }
        let origins = artifact
            .origins
            .iter()
            .filter_map(|span| {
                context
                    .origins
                    .source_paths
                    .get(span.source_id as usize)
                    .map(|path| format!("{}:{}", path.display(), span.line))
            })
            .collect::<Vec<_>>();
        let recorded = recorded_generated_origins(&artifact.source)
            .into_iter()
            .collect::<HashSet<_>>();
        if !artifact.needs_publication
            && origins
                .iter()
                .all(|origin| recorded.contains(&origin.replace(['\r', '\n'], " ")))
        {
            continue;
        }
        if !created_directories {
            fs::create_dir_all(directory).map_err(|error| error.to_string())?;
            fs::create_dir_all(generated_source_directory(directory))
                .map_err(|error| error.to_string())?;
            created_directories = true;
        }
        let source = annotate_generated_source(&artifact.source, &origins);
        publish_generated_expansion(directory, &artifact.key, &source)?;
    }
    Ok(())
}

fn record_builtin_origin(context: &mut ExpansionContext<'_>, key: String) {
    if let Some(span) = context.invocation_span {
        context
            .origins
            .builtins
            .entry(key.clone())
            .or_default()
            .push(span);
    }
    for outputs in &mut context.active_builtins {
        if !outputs.contains(&key) {
            outputs.push(key.clone());
        }
    }
}

fn expand_top(
    expression: Syntax,
    context: &mut ExpansionContext<'_>,
) -> Result<Vec<Syntax>, String> {
    let Expr::List(items) = &expression.expr else {
        return Ok(vec![expression]);
    };
    if !matches!(items.first(), Some(Expr::Generate)) {
        let source = context
            .invocation_span
            .map(|span| context.origins.invocation_origin(span).source_id);
        if let Some(source) = source {
            context.origins.generation.record_in_source(
                &expression.expr,
                &context.generation_origins,
                source,
            );
        } else {
            context
                .origins
                .generation
                .record(&expression.expr, &context.generation_origins);
        }
        return Ok(vec![expression]);
    }
    let Some(Expr::Symbol(name)) = items.get(1) else {
        return Err("generator invocation requires a name after '#generate'".into());
    };
    let parts = expression.clone().parts().unwrap();
    if let (Some(visibility), Some(span)) = (&context.origins.visibility, context.invocation_span) {
        if let Err(error) = visibility.access(name, span, false) {
            if !parts[1]
                .authority()
                .is_some_and(|author| visibility.access(name, author, false).is_ok())
            {
                return Err(error.message);
            }
        }
    }
    let arguments = parts.into_iter().skip(2).collect::<Vec<_>>();
    let Some(generator) = context.generators.get(name).cloned() else {
        if builtins::named_builtin_keys(name).is_none() {
            return Err(format!("unknown generator '#generate {name}'"));
        }
        // Built-in declarations such as #generate #optional are handled by the Lim parser.
        context
            .origins
            .generation
            .record_builtin_parents(&expression.expr, &context.generation_origins)?;
        record_builtin_origin(context, crate::expression_source(&expression.expr)?);
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
    for (parameter, argument) in generator.parameters.iter().zip(&arguments) {
        for capability in &parameter.capabilities {
            let Expr::Symbol(type_name) = &argument.expr else {
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
            if !context.capabilities.get(capability).is_some_and(|types| {
                types.contains_key(type_name.strip_prefix('#').unwrap_or(type_name))
            }) {
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
    let instance = context
        .invocation_span
        .map(|span| context.origins.expansion_context(span))
        .unwrap_or_default();
    let argument_identities = arguments.iter().map(Syntax::identity).collect::<Vec<_>>();
    let invocation_key = format!("{instance}:{name}:{argument_identities:?}");
    if let Some(span) = context.invocation_span {
        context.origins.user.insert(span);
    }
    if context.cache_dir.is_some() {
        if let Some(parent) = context.active_invocations.last() {
            context
                .invocation_children
                .entry(parent.clone())
                .or_default()
                .insert(invocation_key.clone());
        }
    }
    let duplicate = !context.seen_invocations.insert(invocation_key.clone());
    if duplicate {
        let mut origins = context.generation_origins.clone();
        origins.push(crate::generator_provenance::Origin {
            producer: name.as_str().into(),
            invocation: invocation_key.as_str().into(),
        });
        context
            .origins
            .generation
            .inherit_invocation(&invocation_key, &origins);
        record_invocation_origins(&invocation_key, context);
        for builtin in context
            .invocation_builtins
            .get(&invocation_key)
            .cloned()
            .unwrap_or_default()
        {
            record_builtin_origin(context, builtin);
        }
        return Ok(Vec::new());
    }
    let header = context.origins.context_header(
        name,
        generator.span,
        context.invocation_span.unwrap_or(generator.span),
    );
    let cache_key = format!(
        "lim-generator-cache-v15\ncompiler={}\nimplementation={}\ndependency-context={}\ncapability-hash={:032x}\ngenerator-hash={:032x}\ngenerator-input={}\ninstance={}\narguments={:?}\ncontext={header}",
        concat!(env!("CARGO_PKG_VERSION"), "-record-functions-v1"),
        env!("LIM_BUILD_FINGERPRINT"),
        context.dependency_context,
        context.capability_hash,
        context.generator_fingerprints[name].hash,
        context.generator_fingerprints[name].material,
        instance,
        &argument_identities,
    );
    let scope = context.gensyms.open(&cache_key)?;
    let cached = match context.cache_dir {
        Some(directory) => load_generated_expansion(directory, &cache_key)?,
        None => None,
    }
    .filter(|(_, forms)| {
        context
            .gensyms
            .restore_refs(forms.iter().map(|form| &form.expr), &scope)
    });
    if let Some(directory) = context.cache_dir {
        let path = cache_path(directory, &cache_key);
        crate::cache_report::record(
            "syntax",
            &path,
            &cache_key,
            if cached.is_some() {
                "hit"
            } else if path.exists() {
                "invalid-entry"
            } else {
                "missing-entry"
            },
        );
    }
    if cached.is_some() {
        context.cache_hits = context.cache_hits.saturating_add(1);
    }
    context.active.push(name.clone());
    context
        .generation_origins
        .push(crate::generator_provenance::Origin {
            producer: name.as_str().into(),
            invocation: invocation_key.as_str().into(),
        });
    context.active_invocations.push(invocation_key.clone());
    context.active_builtins.push(Vec::new());
    context.gensym_scopes.push(scope);
    let mut cached_source = None;
    let forms = match cached {
        Some((source, forms)) => {
            cached_source = Some(source);
            forms
        }
        None => {
            let environment = generator
                .parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .zip(arguments.iter().cloned())
                .collect();
            let result = match evaluate(&generator.body, &environment, context) {
                Ok(result) => result,
                Err(error) => {
                    context.active.pop();
                    context.active_builtins.pop();
                    context.gensym_scopes.pop();
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
            let Value::Syntax(result) = result else {
                return Err(format!("#generate {name} must return syntax"));
            };
            let Some(forms) = result.parts() else {
                context.active.pop();
                context.active_builtins.pop();
                context.gensym_scopes.pop();
                return Err(format!(
                    "#generate {name} must return a list of generated forms"
                ));
            };
            forms
        }
    };
    let forms = forms
        .into_iter()
        .map(|form| Syntax::authored(form.expr, Some(generator.span)))
        .collect::<Vec<_>>();
    for form in &forms {
        crate::generator_authority::validate_output(&form.expr)?;
    }
    if context.cache_dir.is_some() {
        let needs_publication = cached_source.is_none();
        let source = match cached_source {
            Some(source) => source,
            None => {
                let source = format_generated_syntax(&format!(
                    "{header}\n{}",
                    forms
                        .iter()
                        .map(|form| crate::expression_source(&form.expr))
                        .collect::<Result<Vec<_>, _>>()?
                        .join("\n")
                ))?;
                source
            }
        };
        context.invocation_artifacts.insert(
            invocation_key.clone(),
            InvocationArtifact {
                key: cache_key,
                source,
                origins: context.invocation_span.into_iter().collect(),
                generator: crate::generated_lookup::enabled().then(|| name.clone()),
                direct_origins: if crate::generated_lookup::enabled()
                    && context.active_invocations.len() == 1
                {
                    context.invocation_span.into_iter().collect()
                } else {
                    HashSet::new()
                },
                needs_publication,
            },
        );
    }
    let mut expanded = Vec::new();
    for form in forms {
        match expand_top(form, context) {
            Ok(forms) => expanded.extend(forms),
            Err(error) => {
                context.active.pop();
                context.active_builtins.pop();
                context.gensym_scopes.pop();
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
    context.active_invocations.pop();
    context.generation_origins.pop();
    context.gensym_scopes.pop();
    let builtins = context.active_builtins.pop().unwrap();
    context.invocation_builtins.insert(invocation_key, builtins);
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
        "#generate {name} invocation at {}:{} (defined at {}:{}; {})",
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
) -> Result<HashMap<String, GeneratorFingerprint>, crate::source_error::SourceError> {
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
) -> Result<u128, crate::source_error::SourceError> {
    if let Some(hash) = hashes.get(name) {
        return Ok(hash.hash);
    }
    if active.iter().any(|entry| entry == name) {
        let mut chain = active.join(" -> ");
        if !chain.is_empty() {
            chain.push_str(" -> ");
        }
        chain.push_str(name);
        let message = format!("recursive generator function calls are not allowed: {chain}");
        let error =
            crate::source_error::SourceError::new(message, crate::DiagnosticCode::Generator);
        let caller = active.last().and_then(|caller| functions.get(caller));
        return Err(caller.map_or(error.clone(), |caller| {
            let span = caller
                .source_body
                .as_ref()
                .and_then(|body| generator_call_span(body, name))
                .unwrap_or(caller.span);
            at_span(error, span, "generator function")
        }));
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
                let hash =
                    hash_generator_function(called, functions, interpreter_hash, hashes, active)?;
                write!(hash_material, "\ncall={called}:{hash:032x}").unwrap();
            }
            None => write!(hash_material, "\nmissing-call={called}").unwrap(),
        }
    }
    active.pop();
    let fingerprint = GeneratorFingerprint {
        hash: stable_hash(hash_material.as_bytes()),
        material: definition,
        dependencies: calls,
    };
    let hash = fingerprint.hash;
    hashes.insert(name.to_owned(), fingerprint);
    Ok(hash)
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
            let mut pending = calls.iter().map(String::as_str).collect::<Vec<_>>();
            while let Some(called) = pending.pop() {
                if !closure.insert(called) {
                    continue;
                }
                if let Some(fingerprint) = function_hashes.get(called) {
                    pending.extend(fingerprint.dependencies.iter().map(String::as_str));
                }
            }
            let mut closure = closure.into_iter().collect::<Vec<_>>();
            closure.sort();
            let mut material = definition.clone();
            let mut hash_material = definition;
            for called in closure {
                match function_hashes.get(called) {
                    Some(fingerprint) => {
                        write!(material,
                            "\nhelper={called}:{}:{}",
                            fingerprint.material.len(),
                            fingerprint.material
                        ).unwrap();
                    }
                    None => write!(material, "\nmissing-helper={called}").unwrap(),
                }
            }
            for called in &calls {
                match function_hashes.get(called) {
                    Some(fingerprint) => {
                        write!(hash_material, "\ncall={called}:{:032x}", fingerprint.hash).unwrap();
                    }
                    None => write!(hash_material, "\nmissing-call={called}").unwrap(),
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
                    if let Some(Expr::Symbol(name) | Expr::Function(name)) = items.get(1) {
                        calls.push(name.clone());
                    }
                    for argument in items.iter().skip(2) {
                        collect_generator_function_calls(argument, calls);
                    }
                }
                "#gn-if" | "#gn-equal" | "#gn-symbol?" | "#gn-list?" | "#gn-symbol"
                | "#gn-gensym" | "#gn-symbol-append" | "#gn-variant" | "#gn-get" | "#gn-length"
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
        Expr::Function(_)
        | Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::Generate => {}
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
        Expr::Function(_)
        | Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::Generate => {}
    }
}

pub(crate) fn cache_path(directory: &Path, key: &str) -> PathBuf {
    if key.starts_with("lim-generator-cache-") {
        return generated_expansion_paths(directory, key).0;
    }
    // Stable FNV-1a 128-bit naming; the complete key is stored and compared
    // inside each file, so a digest collision can never produce a false hit.
    directory.join(format!(
        "generator-{:032x}.cache",
        stable_hash(key.as_bytes())
    ))
}

/// Keep inspectable Lim separate from analysis caches and cache metadata.
pub(crate) fn generated_source_directory(cache: &Path) -> PathBuf {
    if cache.file_name().is_some_and(|name| name == "cache") {
        cache
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join("generated")
    } else {
        cache.join("generated")
    }
}

/// Read or create an inspectable generated-source artifact in the shared
/// content-addressed cache. The complete key and digest remain in the metadata
/// directory, so a digest collision is detected instead of treated as a hit.
#[cfg(test)]
pub(crate) fn cached_generated_source(
    directory: &Path,
    key: &str,
    generate: impl FnOnce() -> Result<String, String>,
) -> Result<String, String> {
    cached_generated_source_with_origins(directory, key, &[], generate)
}

pub(crate) fn cached_generated_source_with_origins(
    directory: &Path,
    key: &str,
    origins: &[String],
    generate: impl FnOnce() -> Result<String, String>,
) -> Result<String, String> {
    let formatted_key = format!("{GENERATED_SOURCE_FORMAT}\n{key}");
    let key = formatted_key.as_str();
    let digest = stable_hash(key.as_bytes());
    let source_directory = generated_source_directory(directory);
    let path = source_directory.join(format!("generated-{digest:032x}.lim"));
    let key_path = directory.join(format!("generated-{digest:032x}.key"));
    let digest_path = directory.join(format!("generated-{digest:032x}.hash"));
    cleanup_abandoned_staging(directory);
    cleanup_abandoned_staging(&source_directory);
    if let Some(existing_key) = read_bounded_cache_text(&key_path) {
        if existing_key != key {
            crate::cache_report::record("source", &path, key, "key-collision");
            return Err(format!(
                "generated-source cache hash collision at {}",
                path.display()
            ));
        }
        if let (Some(source), Some(expected_digest)) = (
            read_bounded_cache_text(&path),
            read_bounded_cache_text(&digest_path),
        ) {
            if expected_digest == generated_source_digest(key, &source)
                && crate::parse_source_unit(&source)
                    .is_ok_and(|forms| crate::generator_authority::matches_key(key, &forms))
            {
                crate::cache_report::record("source", &path, key, "hit");
                let recorded = recorded_generated_origins(&source);
                if origins
                    .iter()
                    .all(|origin| recorded.contains(&origin.replace(['\r', '\n'], " ")))
                {
                    return Ok(source);
                }
                let annotated = annotate_generated_source(&source, origins);
                if annotated != source {
                    publish_cache_file(&path, annotated.as_bytes(), "generated source")?;
                    publish_cache_file(
                        &digest_path,
                        generated_source_digest(key, &annotated).as_bytes(),
                        "generated-source cache digest",
                    )?;
                }
                return Ok(annotated);
            }
        }
    }

    crate::cache_report::record(
        "source",
        &path,
        key,
        if path.exists() || key_path.exists() || digest_path.exists() {
            "invalid-entry"
        } else {
            "missing-entry"
        },
    );
    let source = annotate_generated_source(&format_generated_source(&generate()?)?, origins);
    fs::create_dir_all(directory)
        .map_err(|error| format!("cannot create generated-source cache: {error}"))?;
    fs::create_dir_all(&source_directory)
        .map_err(|error| format!("cannot create generated-source directory: {error}"))?;
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

pub(crate) fn cached_generated_source_path(directory: &Path, key: &str) -> PathBuf {
    let digest = stable_hash(format!("{GENERATED_SOURCE_FORMAT}\n{key}").as_bytes());
    generated_source_directory(directory).join(format!("generated-{digest:032x}.lim"))
}

const GENERATED_ORIGINS_HEADER: &str = "// Generated from:\n";

fn recorded_generated_origins(source: &str) -> Vec<String> {
    source
        .strip_prefix(GENERATED_ORIGINS_HEADER)
        .and_then(|source| source.split_once("\n\n"))
        .map_or_else(Vec::new, |(header, _)| {
            header
                .lines()
                .filter_map(|line| line.strip_prefix("// "))
                .map(str::to_owned)
                .collect()
        })
}

fn annotate_generated_source(source: &str, origins: &[String]) -> String {
    let body = if source.starts_with(GENERATED_ORIGINS_HEADER) {
        source.split_once("\n\n").map_or(source, |(_, body)| body)
    } else {
        source
    };
    let mut recorded = recorded_generated_origins(source);
    recorded.extend(
        origins
            .iter()
            .map(|origin| origin.replace(['\r', '\n'], " ")),
    );
    let mut origins = recorded;
    if origins.is_empty() {
        return body.to_owned();
    }
    origins.sort();
    origins.dedup();
    let mut output = GENERATED_ORIGINS_HEADER.to_owned();
    for origin in origins {
        output.push_str("// ");
        // A filename cannot inject source through the provenance comment.
        output.push_str(&origin);
        output.push('\n');
    }
    output.push('\n');
    output.push_str(body);
    output
}

/// Keep declarations at column zero and indent their bodies structurally.
/// Templates supply syntax; their incidental whitespace is never published.
pub(crate) fn format_generated_syntax(source: &str) -> Result<String, String> {
    render_generated_forms(&crate::parse(source)?)
}

pub(crate) fn format_generated_source(source: &str) -> Result<String, String> {
    render_generated_forms(&crate::parse_source_unit(source)?)
}

fn render_generated_forms(forms: &[SpannedExpr]) -> Result<String, String> {
    fn render(expression: &Expr, indent: usize) -> Result<String, String> {
        let flat = crate::expression_source(expression)?;
        let Expr::List(items) = expression else {
            return Ok(flat);
        };
        let head = match items.first() {
            Some(Expr::Symbol(head)) => head.as_str(),
            _ => "",
        };
        let prefix = match head {
            "#fn" | "#unsafe-fn" => 4,
            "#case" | "#case-ref" | "#case-ref-mut" | "#case-pin" | "#case-pin-mut" | "#call"
            | "#unsafe-call" | "#match" | "#if" => 2,
            "#enum" | "#struct" => 3,
            "#struct-literal" => 2,
            "#let" | "#let-mut" => 3,
            "#thread-task" => 3,
            _ => 1,
        };
        if items.len() <= prefix
            || (!matches!(head, "#fn" | "#unsafe-fn") && indent + flat.len() <= 100)
        {
            return Ok(flat);
        }
        let mut output = String::from("(");
        for (index, item) in items[..prefix].iter().enumerate() {
            if index != 0 {
                output.push(' ');
            }
            output.push_str(&crate::expression_source(item)?);
        }
        for item in &items[prefix..] {
            output.push('\n');
            output.push_str(&" ".repeat(indent + 2));
            output.push_str(&render(item, indent + 2)?);
        }
        output.push(')');
        Ok(output)
    }

    let mut output = String::new();
    for parsed in forms {
        if !output.is_empty() {
            output.push('\n');
        }
        if let Some(source) = crate::source_forms::modern_declaration_source(&parsed.expr)? {
            output.push_str(&source);
        } else {
            crate::declaration_source(&parsed.expr)?;
            let rendered = render(&parsed.expr, 0)?;
            output.push_str(&rendered[1..rendered.len() - 1]);
        }
        output.push('\n');
    }
    Ok(output)
}

fn generated_source_digest(key: &str, source: &str) -> String {
    format!(
        "{:032x}",
        stable_hash_parts(&[key.as_bytes(), &[0], source.as_bytes()])
    )
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
    let times = CACHE_CLEANUP_TIMES.get_or_init(|| Mutex::new(HashMap::new()));
    let Ok(mut times) = times.lock() else {
        return;
    };
    let started = Instant::now();
    if times
        .get(directory)
        .is_some_and(|last| started.duration_since(*last) < CACHE_CLEANUP_INTERVAL)
    {
        return;
    }
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    if times.len() >= MAX_CLEANUP_DIRECTORIES {
        times.clear();
    }
    times.insert(directory.to_path_buf(), started);
    // Concurrent publishers need not wait for the directory traversal. Only
    // hour-old temporary files are eligible, as before.
    drop(times);
    let now = SystemTime::now();
    for entry in entries.filter_map(Result::ok) {
        if !is_cache_staging_name(&entry.file_name()) {
            continue;
        }
        let stale = entry
            .metadata()
            .and_then(|metadata| metadata.modified())
            .ok()
            .and_then(|modified| now.duration_since(modified).ok())
            .is_some_and(|age| age > Duration::from_secs(60 * 60));
        if stale {
            let _ = fs::remove_file(entry.path());
        }
    }
}

/// DirEntry names are basenames, so an ASCII suffix is sufficient here.
/// A dotfile named exactly `.tmp` has no extension and is not staging.
/// Construct a full directory path only when a stale candidate is removed.
fn is_cache_staging_name(name: &std::ffi::OsStr) -> bool {
    let bytes = name.as_encoded_bytes();
    bytes.len() > 4 && bytes.ends_with(b".tmp")
}

fn interpreter_hash() -> u128 {
    *INTERPRETER_HASH.get_or_init(|| {
        stable_hash_parts(&[
            include_bytes!("generator.rs"),
            include_bytes!("gensym.rs"),
            include_bytes!("generator_authority.rs"),
        ])
    })
}

pub(crate) fn stable_hash(bytes: &[u8]) -> u128 {
    stable_hash_parts(&[bytes])
}

fn stable_hash_parts(parts: &[&[u8]]) -> u128 {
    let mut hash = 0x6c62272e07bb014262b821756295c58du128;
    for bytes in parts {
        for byte in *bytes {
            hash ^= u128::from(*byte);
            hash = hash.wrapping_mul(0x0000000001000000000000000000013bu128);
        }
    }
    hash
}

fn generated_expansion_paths(directory: &Path, key: &str) -> (PathBuf, PathBuf) {
    let digest = stable_hash(key.as_bytes());
    (
        generated_source_directory(directory).join(format!("generated-{digest:032x}.lim")),
        directory.join(format!("generated-{digest:032x}.key")),
    )
}

// The readable artifact is the cache payload, not a second copy of it.
// Nested invocations remain in this file and get their own cached artifacts.
fn load_generated_expansion(
    directory: &Path,
    key: &str,
) -> Result<Option<(String, Vec<Syntax>)>, String> {
    let (path, key_path) = generated_expansion_paths(directory, key);
    cleanup_abandoned_staging(directory);
    cleanup_abandoned_staging(&generated_source_directory(directory));
    let Some(metadata) = read_bounded_cache_text(&key_path) else {
        return Ok(None);
    };
    let Some((expected_digest, existing_key)) = metadata.split_once('\n') else {
        return Ok(None);
    };
    if existing_key != key {
        return Err(format!(
            "generated-source cache hash collision at {}",
            path.display()
        ));
    }
    crate::cache_report::record("syntax-read", &path, key, "read");
    let Some(source) = read_bounded_cache_text(&path) else {
        return Ok(None);
    };
    if expected_digest != generated_source_digest(key, &source) {
        return Ok(None);
    }
    let Ok(forms) = crate::parse_source_unit(&source) else {
        return Ok(None);
    };
    if !crate::generator_authority::matches_key(key, &forms) {
        return Ok(None);
    }
    let expressions = forms.into_iter().map(|node| node.expr).collect();
    let forms = crate::generator_authority::restore(expressions);
    Ok(Some((source, forms)))
}

#[cfg(test)]
fn read_generated_expansion(directory: &Path, key: &str, origins: &[String]) -> Option<Vec<Expr>> {
    let (source, forms) = load_generated_expansion(directory, key).ok()??;
    let recorded = recorded_generated_origins(&source);
    if !origins
        .iter()
        .all(|origin| recorded.contains(&origin.replace(['\r', '\n'], " ")))
    {
        let annotated = annotate_generated_source(&source, origins);
        publish_generated_expansion(directory, key, &annotated).ok()?;
    }
    Some(forms.into_iter().map(|form| form.expr).collect())
}

fn publish_generated_expansion(directory: &Path, key: &str, source: &str) -> Result<(), String> {
    let (path, key_path) = generated_expansion_paths(directory, key);
    publish_cache_file(&path, source.as_bytes(), "generated source")?;
    // The metadata is the commit marker for the corresponding source.
    publish_cache_file(
        &key_path,
        format!("{}\n{key}", generated_source_digest(key, source)).as_bytes(),
        "generated-source cache metadata",
    )?;
    crate::cache_report::record("syntax-publication", &path, key, "write");
    Ok(())
}

#[cfg(test)]
fn write_generated_expansion(
    directory: &Path,
    key: &str,
    expressions: &[Expr],
    origins: &[String],
) -> Result<(), String> {
    let (path, key_path) = generated_expansion_paths(directory, key);
    // Refuse to overwrite a different full key, even on a digest collision.
    if read_bounded_cache_text(&key_path).is_some_and(|existing| {
        existing
            .split_once('\n')
            .is_some_and(|(_, existing_key)| existing_key != key)
    }) {
        return Err(format!(
            "generated-source cache hash collision at {}",
            path.display()
        ));
    }
    let source = expressions
        .iter()
        .map(crate::expression_source)
        .collect::<Result<Vec<_>, _>>()?;
    let body = source.join("\n");
    let source = match key.lines().find_map(|line| line.strip_prefix("context=")) {
        Some(header) => format_generated_syntax(&format!("{header}\n{body}"))?,
        None => format_generated_syntax(&body)?,
    };
    let mut origins = origins.to_vec();
    if let Some(previous) = read_bounded_cache_text(&path) {
        origins.extend(recorded_generated_origins(&previous));
    }
    let source = annotate_generated_source(&source, &origins);
    (|| -> Result<(), String> {
        fs::create_dir_all(directory).map_err(|error| error.to_string())?;
        fs::create_dir_all(generated_source_directory(directory))
            .map_err(|error| error.to_string())?;
        publish_generated_expansion(directory, key, &source)
    })()
}

#[cfg(test)]
pub(crate) fn read_cached_expansion(directory: &Path, key: &str) -> Option<Vec<Expr>> {
    if key.starts_with("lim-generator-cache-") {
        return read_generated_expansion(directory, key, &[]);
    }
    cleanup_abandoned_staging(directory);
    let bytes = read_bounded_cache_file(&cache_path(directory, key))?;
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

fn read_bounded_cache_file(path: &Path) -> Option<Vec<u8>> {
    // Limit the read itself: a separate pathname size check both costs a
    // syscall on every hit and cannot bound a concurrently growing file.
    let file = fs::File::open(path).ok()?;
    let mut bytes = Vec::new();
    file.take(MAX_CACHE_ARTIFACT_BYTES + 1)
        .read_to_end(&mut bytes)
        .ok()?;
    (bytes.len() as u64 <= MAX_CACHE_ARTIFACT_BYTES).then_some(bytes)
}

fn read_bounded_cache_text(path: &Path) -> Option<String> {
    String::from_utf8(read_bounded_cache_file(path)?).ok()
}

#[cfg(test)]
fn read_cache_length(bytes: &[u8], cursor: &mut usize) -> Option<usize> {
    let end = cursor.checked_add(8)?;
    let length = u64::from_le_bytes(bytes.get(*cursor..end)?.try_into().ok()?);
    *cursor = end;
    usize::try_from(length).ok()
}

#[cfg(test)]
pub(crate) fn write_cached_expansion(directory: &Path, key: &str, expressions: &[Expr]) {
    if key.starts_with("lim-generator-cache-") {
        let _ = write_generated_expansion(directory, key, expressions, &[]);
        return;
    }
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
    if let Some(existing) = read_bounded_cache_file(&path) {
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

#[cfg(test)]
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
    if let Expr::Function(name) = expression {
        return Ok(Value::Syntax(Expr::Symbol(name.clone()).into()));
    }
    if let Expr::Symbol(name) = expression {
        return Ok(Value::Syntax(
            environment
                .get(name)
                .cloned()
                .unwrap_or_else(|| expression.clone().into()),
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
        return Ok(Value::Syntax(expression.clone().into()));
    };
    let operator = match items.first() {
        Some(Expr::Symbol(operator)) => operator.as_str(),
        _ => return Ok(Value::Syntax(expression.clone().into())),
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
            Ok(Value::Boolean(left.expr == right.expr))
        }
        "#gn-symbol?" | "#gn-list?" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, context)?, operator)?;
            Ok(Value::Boolean(if operator == "#gn-symbol?" {
                matches!(value.expr, Expr::Symbol(_))
            } else {
                matches!(value.expr, Expr::List(_))
            }))
        }
        "#gn-gensym" => {
            arity(operator, items, 2)?;
            let hint = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let Expr::String(hint) = hint.expr else {
                return Err("#gn-gensym requires a string hint".into());
            };
            let name = context
                .gensym_scopes
                .last_mut()
                .ok_or("#gn-gensym requires an active generator invocation")?
                .fresh(&hint)?;
            context.gensyms.issue(&name);
            Ok(Value::Syntax(Expr::Symbol(name).into()))
        }
        "#gn-symbol" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let Expr::String(value) = value.expr else {
                return Err("#gn-symbol requires a string literal".into());
            };
            if crate::gensym::reserved(&value) {
                return Err("#gn-symbol cannot forge compiler-reserved gensym identifiers".into());
            }
            let parsed =
                crate::parse(&value).map_err(|_| "#gn-symbol must produce one identifier")?;
            if parsed.len() != 1 || parsed[0].expr != Expr::Symbol(value.clone()) {
                return Err("#gn-symbol must produce one identifier".into());
            }
            Ok(Value::Syntax(Expr::Symbol(value).into()))
        }
        "#gn-symbol-append" | "#gn-variant" => {
            arity(operator, items, 3)?;
            let base = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let suffix = syntax(evaluate(&items[2], environment, context)?, operator)?;
            let Expr::Symbol(mut base) = base.expr else {
                return Err(format!("{operator} requires a symbol base"));
            };
            if crate::gensym::reserved(&base) {
                return Err(format!(
                    "{operator} cannot alter compiler-reserved gensym identifiers"
                ));
            }
            let suffix = match suffix.expr {
                Expr::String(suffix) | Expr::Symbol(suffix) => suffix,
                _ => return Err(format!("{operator} requires a string or symbol suffix")),
            };
            base.push_str(if operator == "#gn-variant" { "." } else { "::" });
            base.push_str(&suffix);
            if operator == "#gn-variant" {
                crate::names::require(&base, "variant")?;
            }
            if crate::gensym::reserved(&base) {
                return Err(format!(
                    "{operator} cannot forge compiler-reserved gensym identifiers"
                ));
            }
            let parsed = crate::parse(&base)
                .map_err(|_| format!("{operator} must produce one ordinary identifier"))?;
            if parsed.len() != 1 || parsed[0].expr != Expr::Symbol(base.clone()) {
                return Err(format!("{operator} must produce one ordinary identifier"));
            }
            Ok(Value::Syntax(Expr::Symbol(base).into()))
        }
        "#gn-list" => {
            let mut values = Vec::with_capacity(items.len().saturating_sub(1));
            for item in &items[1..] {
                values.push(syntax(evaluate(item, environment, context)?, operator)?);
            }
            Ok(Value::Syntax(Syntax::list(values)))
        }
        "#gn-get" => {
            if !matches!(items.len(), 3 | 4) {
                return Err(
                    "#gn-get requires a named syntax list, a key, and an optional fallback".into(),
                );
            }
            let options = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let key = syntax(evaluate(&items[2], environment, context)?, operator)?;
            let (Some(options), Expr::Symbol(key)) = (options.parts(), key.expr) else {
                return Err("#gn-get requires a named syntax list and a symbol key".into());
            };
            let mut seen = HashSet::new();
            let mut found = None;
            for option in options {
                let Some(pair) = option.parts() else {
                    return Err("#gn-get entries must be (key value) pairs".into());
                };
                let [name, value] = pair.as_slice() else {
                    return Err("#gn-get entries must be (key value) pairs".into());
                };
                let Expr::Symbol(name) = &name.expr else {
                    return Err("#gn-get entries must be (key value) pairs".into());
                };
                if !seen.insert(name.clone()) {
                    return Err(format!("#gn-get repeats key '{name}'"));
                }
                if name == &key {
                    found = Some(value.clone());
                }
            }
            match found {
                Some(value) => Ok(Value::Syntax(value)),
                None if items.len() == 4 => evaluate(&items[3], environment, context),
                None => Err(format!("#gn-get is missing key '{key}'")),
            }
        }
        "#gn-length" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let Some(values) = value.parts() else {
                return Err("#gn-length requires list syntax".into());
            };
            Ok(Value::Syntax(Expr::Integer(values.len() as i128).into()))
        }
        "#gn-first" | "#gn-rest" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, context)?, operator)?;
            let Some(values) = value.parts() else {
                return Err(format!("{operator} requires list syntax"));
            };
            if operator == "#gn-first" {
                values
                    .into_iter()
                    .next()
                    .map(Value::Syntax)
                    .ok_or_else(|| "#gn-first cannot read an empty list".into())
            } else {
                Ok(Value::Syntax(Syntax::list(
                    values.into_iter().skip(1).collect(),
                )))
            }
        }
        "#gn-for-each" => {
            arity(operator, items, 4)?;
            let variable = symbol(items.get(1), "#gn-for-each binding")?.to_owned();
            if variable.starts_with('#') {
                return Err(format!(
                    "identifier '{variable}' is reserved for the language and standard library"
                ));
            }
            if environment.contains_key(&variable) {
                return Err(format!(
                    "#gn-for-each binding '{variable}' shadows an existing generator binding; shadowing is not allowed"
                ));
            }
            let list = syntax(evaluate(&items[2], environment, context)?, operator)?;
            let Some(values) = list.parts() else {
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
            Ok(Value::Syntax(Syntax::list(result)))
        }
        "#gn-call" => {
            if items.len() < 2 {
                return Err("#gn-call requires a function name".into());
            }
            let name = symbol(items.get(1), "#gn-call function name")?;
            if let Some(visibility) = &context.origins.visibility {
                let caller = context
                    .active_functions
                    .last()
                    .and_then(|name| context.functions.get(name))
                    .or_else(|| {
                        context
                            .active
                            .last()
                            .and_then(|name| context.generators.get(name))
                    })
                    .map(|definition| definition.span)
                    .or(context.invocation_span);
                if let Some(caller) = caller {
                    visibility
                        .access(name, caller, false)
                        .map_err(|error| error.message)?;
                }
            }
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
            match message.expr {
                Expr::String(message) => Err(format!("generator error: {message}")),
                _ => Err("#gn-error requires a string literal message".into()),
            }
        }
        _ if operator.starts_with("#gn-") => Err(format!("unknown generator builtin '{operator}'")),
        _ => Ok(Value::Syntax(expression.clone().into())),
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
        Expr::Function(name) => Ok(TemplateValue::Syntax(Expr::Symbol(name.clone()).into())),
        Expr::QuasiQuote(inner) => {
            match evaluate_template(inner, environment, context, depth + 1, false)? {
                TemplateValue::Syntax(inner) => {
                    Ok(TemplateValue::Syntax(inner.wrap(Expr::QuasiQuote)))
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
                    Ok(TemplateValue::Syntax(inner.wrap(Expr::Unquote)))
                }
                TemplateValue::Splice(_) => unreachable!("unquote root cannot splice"),
            }
        }
        Expr::UnquoteSplicing(inner) if depth == 1 => {
            if !splice_allowed {
                return Err("unquote-splicing is only valid inside a syntax list".into());
            }
            let value = syntax(evaluate(inner, environment, context)?, "unquote-splicing")?;
            match value.parts() {
                Some(values) => Ok(TemplateValue::Splice(values)),
                None => Err("unquote-splicing requires list syntax".into()),
            }
        }
        Expr::UnquoteSplicing(inner) => {
            match evaluate_template(inner, environment, context, depth - 1, false)? {
                TemplateValue::Syntax(inner) => {
                    Ok(TemplateValue::Syntax(inner.wrap(Expr::UnquoteSplicing)))
                }
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
            Ok(TemplateValue::Syntax(Syntax::list(result)))
        }
        other => Ok(TemplateValue::Syntax(other.clone().into())),
    }
}

fn syntax(value: Value, operation: &str) -> Result<Syntax, String> {
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
        Some(Expr::Symbol(value)) if context == "capability type" => {
            Ok(value.strip_prefix('#').unwrap_or(value))
        }
        Some(Expr::Symbol(value) | Expr::Function(value)) => Ok(value),
        _ => Err(format!("expected symbol for {context}")),
    }
}

fn is_operator(expression: Option<&Expr>, expected: &str) -> bool {
    matches!(expression, Some(Expr::Symbol(name)) if name == expected)
}

fn at_span(
    message: impl Into<crate::source_error::SourceError>,
    span: Span,
    context: &str,
) -> crate::source_error::SourceError {
    let mut error = message.into();
    error.message = format!("{context}: {}", error.message);
    error.code = crate::DiagnosticCode::Generator;
    error.at(span)
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
    fn ordinary_forms_preserve_nested_spans_without_expansion() {
        let forms = crate::parse(
            "(#fn main () #u64\n  (#let value #u64 (#u64::add-wrap 1u64 2u64))\n  (#return value))",
        )
        .unwrap();
        let expected = format!("{forms:?}");
        let ((output, generated), hits) =
            expand_with_generated_cached_and_hits(forms, None, "").unwrap();
        assert_eq!(format!("{output:?}"), expected);
        assert!(generated.is_empty());
        assert_eq!(hits, 0);
    }

    #[test]
    fn helper_digest_lookup_preserves_shared_dependency_material() {
        let source = "(#gn-fn leaf (value) value)
            (#gn-fn left (value) (#gn-call leaf value))
            (#gn-fn right (value) (#gn-call leaf value))
            (#gn-fn root (value)
                (#gn-list (#gn-call right value) (#gn-call left value)
                          (#gn-call left value)))";
        let functions = crate::parse(source)
            .unwrap()
            .into_iter()
            .map(|source| {
                let Expr::List(items) = &source.expr else {
                    panic!("expected helper declaration");
                };
                let Expr::Symbol(name) = &items[1] else {
                    panic!("expected helper name");
                };
                (
                    name.clone(),
                    parse_generator_function(items, &source).unwrap(),
                )
            })
            .collect::<HashMap<_, _>>();
        let interpreter = 42;
        let mut hashes = generator_function_hashes(&functions, interpreter).unwrap();
        for (name, expected_calls) in [
            ("leaf", vec![]),
            ("left", vec!["leaf"]),
            ("right", vec!["leaf"]),
            ("root", vec!["left", "right"]),
        ] {
            let function = &functions[name];
            let definition = format!(
                "lim-generator-function-v1\ninterpreter={interpreter:032x}\nname={name}\nparameters={:?}\nbody={:?}",
                function.parameters, function.body
            );
            let mut material = definition.clone();
            for dependency in &expected_calls {
                material.push_str(&format!(
                    "\ncall={dependency}:{:032x}",
                    hashes[*dependency].hash
                ));
            }
            assert_eq!(hashes[name].material, definition);
            assert_eq!(hashes[name].dependencies, expected_calls);
            assert_eq!(hashes[name].hash, stable_hash(material.as_bytes()));
        }
        // A memoized lookup returns only the digest and leaves the stored
        // collision-check material and dependency records in place.
        let expected = hashes["root"].hash;
        assert_eq!(
            hash_generator_function(
                "root",
                &functions,
                interpreter,
                &mut hashes,
                &mut Vec::new()
            )
            .unwrap(),
            expected
        );
        assert_eq!(hashes.len(), 4);

        // The generator closure must include each shared helper once, in
        // lexical order, while retaining unknown helpers in its fingerprint.
        let source = crate::parse(
            "(#gn build (value) (#gn-list (#gn-call root value)
                (#gn-call left value) (#gn-call missing value)))",
        )
        .unwrap()
        .remove(0);
        let Expr::List(items) = &source.expr else {
            panic!("expected generator");
        };
        let generator = parse_generator(items, &source).unwrap();
        let definition = format!(
            "lim-generator-v1\ninterpreter={interpreter:032x}\nname=build\nparameters={:?}\nbody={:?}",
            generator.parameters, generator.body
        );
        let mut expected_material = definition.clone();
        for name in ["leaf", "left"] {
            expected_material.push_str(&format!(
                "\nhelper={name}:{}:{}",
                hashes[name].material.len(),
                hashes[name].material
            ));
        }
        expected_material.push_str("\nmissing-helper=missing");
        for name in ["right", "root"] {
            expected_material.push_str(&format!(
                "\nhelper={name}:{}:{}",
                hashes[name].material.len(),
                hashes[name].material
            ));
        }
        let mut expected_hash_material = definition;
        expected_hash_material.push_str(&format!("\ncall=left:{:032x}", hashes["left"].hash));
        expected_hash_material.push_str("\nmissing-call=missing");
        expected_hash_material.push_str(&format!("\ncall=root:{:032x}", hashes["root"].hash));
        let generators = HashMap::from([("build".to_owned(), generator)]);
        let fingerprints = generator_hashes(&generators, &hashes, interpreter);
        assert_eq!(fingerprints["build"].material, expected_material);
        assert_eq!(
            fingerprints["build"].hash,
            stable_hash(expected_hash_material.as_bytes())
        );
        assert_eq!(
            fingerprints["build"].dependencies,
            ["left", "missing", "root"]
        );
    }

    #[test]
    fn interpreter_fingerprint_matches_embedded_source() {
        let expected = stable_hash_parts(&[
            include_bytes!("generator.rs"),
            include_bytes!("gensym.rs"),
            include_bytes!("generator_authority.rs"),
        ]);
        assert_eq!(interpreter_hash(), expected);
        assert_eq!(interpreter_hash(), expected);
    }

    #[test]
    fn segmented_hash_preserves_generated_source_digest_format() {
        for (key, source) in [
            ("", ""),
            ("key", "#fn main { #params = (); #returns = #u64; #body = ( (#return 42u64) ); }\n"),
            ("κλειδί\0key", "λ\0source"),
        ] {
            let mut joined = key.as_bytes().to_vec();
            joined.push(0);
            joined.extend_from_slice(source.as_bytes());
            assert_eq!(
                generated_source_digest(key, source),
                format!("{:032x}", stable_hash(&joined))
            );
            // Splitting at every byte boundary must retain the same hash,
            // including empty segments and boundaries within UTF-8 text.
            for boundary in 0..=joined.len() {
                assert_eq!(
                    stable_hash_parts(&[&joined[..boundary], &[], &joined[boundary..]]),
                    stable_hash(&joined)
                );
            }
        }
    }

    #[test]
    fn generator_iteration_bindings_cannot_shadow_parameters_or_outer_bindings() {
        for source in [
            "#gn bad (items) (#gn-for-each items items (#gn-first items))\n#generate bad (one)\n",
            "#gn bad (items) (#gn-for-each item items (#gn-for-each item items (#gn-first item)))\n#generate bad (one)\n",
        ] {
            let error = expand_with_generated_cached_and_hits(crate::parse_source_unit(source).unwrap(), None, "")
                .unwrap_err();
            assert!(
                error.message.contains("shadowing is not allowed"),
                "source: {source}\nerror: {}",
                error.message
            );
        }
    }

    #[test]
    fn generator_parameter_forms_bind_one_name_each() {
        let source = "(#gn make (plain (element sortable) entries) `((#type ,plain ,element)))";
        let forms = crate::parse(source).unwrap();
        let Expr::List(items) = &forms[0].expr else {
            panic!("generator form")
        };
        let generator = parse_generator(items, &forms[0]).unwrap();
        assert_eq!(generator.parameters.len(), 3);
        assert_eq!(generator.parameters[0].name, "plain");
        assert!(generator.parameters[0].capabilities.is_empty());
        assert_eq!(generator.parameters[1].name, "element");
        assert_eq!(generator.parameters[1].capabilities, ["sortable"]);
        assert_eq!(generator.parameters[2].name, "entries");
        assert!(generator.parameters[2].capabilities.is_empty());
        assert!(matches!(generator.body, Expr::QuasiQuote(_)));

        let source = "(#gn one ((left right)) left)";
        let forms = crate::parse(source).unwrap();
        let Expr::List(items) = &forms[0].expr else {
            panic!("generator form")
        };
        let generator = parse_generator(items, &forms[0]).unwrap();
        assert_eq!(generator.parameters.len(), 1);
        assert_eq!(generator.parameters[0].name, "left");
        assert_eq!(generator.parameters[0].capabilities, ["right"]);
    }

    #[test]
    fn generator_parameter_nested_patterns_report_the_offending_form() {
        for (source, expected) in [
            ("(#gn bad (((left right) sortable)) left)", "(left right)"),
            ("(#gn bad ((item (left right))) item)", "(left right)"),
        ] {
            let forms = crate::parse(source).unwrap();
            let Expr::List(items) = &forms[0].expr else {
                panic!("generator form")
            };
            let error = parse_generator(items, &forms[0]).err().unwrap();
            assert!(
                error.message.contains("not destructuring patterns")
                    || error.message.contains("not nested patterns"),
                "{}",
                error.message
            );
            let span = error.span.unwrap();
            assert_eq!(&source[span.start..span.end], expected);
        }
    }

    #[test]
    fn generated_source_formatting_preserves_syntax_and_cache_hits() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-format-{}", std::process::id()));
        let raw = "\n#fn start { #params = ((value #u64)); #returns = #u64; #body = (\n  (#return value) ); }\n#fn other { #params = (); #returns = (#array #char 3); #body = ( (#return \"()\\n\") ); }\n";
        let formatted =
            cached_generated_source(&directory, "formatting", || Ok(raw.into())).unwrap();
        assert_eq!(
            formatted,
            "#fn start {\n  #params = { value = #u64; };\n  #returns = #u64;\n  #body:\n    (#return value);\n}\n\n#fn other {\n  #params = {};\n  #returns = (#array #char 3);\n  #body:\n    (#return \"()\\n\");\n}\n"
        );
        let syntax = |source: &str| {
            crate::parse_source_unit(source)
                .unwrap()
                .into_iter()
                .map(|parsed| parsed.expr)
                .collect::<Vec<_>>()
        };
        assert_eq!(syntax(raw), syntax(&formatted));
        assert_eq!(format_generated_source(&formatted).unwrap(), formatted);
        assert_eq!(
            cached_generated_source(&directory, "formatting", || {
                panic!("formatted cache hit must not rerun the generator")
            })
            .unwrap(),
            formatted
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn inspectable_generated_source_cache_uses_the_full_key_and_reuses_source() {
        let directory =
            std::env::temp_dir().join(format!("lim-inspectable-cache-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        let first =
            cached_generated_source(&directory, "key-a", || Ok("#type Cached #u64\n".into()))
                .unwrap();
        let source_path = fs::read_dir(generated_source_directory(&directory))
            .unwrap()
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .find(|path| path.extension().is_some_and(|extension| extension == "lim"))
            .unwrap();
        fs::write(&source_path, b"LIMGEN").unwrap();
        let mut regenerated = false;
        let second = cached_generated_source(&directory, "key-a", || {
            regenerated = true;
            Ok("#type Cached #u64\n".into())
        })
        .unwrap();
        assert!(regenerated, "edited but valid source must not be trusted");
        assert_eq!(fs::read_to_string(source_path).unwrap(), second);
        let different =
            cached_generated_source(&directory, "key-b", || Ok("#type Other #u64\n".into()))
                .unwrap();
        assert_eq!(first, second);
        assert_ne!(first, different);
        let entries = fs::read_dir(generated_source_directory(&directory))
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
        assert!(entries
            .iter()
            .all(|path| path.extension().is_some_and(|ext| ext == "lim")));
        assert_eq!(
            fs::read_dir(&directory)
                .unwrap()
                .filter_map(Result::ok)
                .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "key"))
                .count(),
            2
        );
        let _ = fs::remove_dir_all(directory);
    }

    #[test]
    fn syntax_cache_rejects_truncated_and_forged_lengths() {
        let directory =
            std::env::temp_dir().join(format!("lim-truncated-syntax-cache-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        let path = cache_path(&directory, "robustness-key");
        for bytes in [
            b"LIMGEN2\0".as_slice(),
            b"LIMGEN2\0\xff\xff\xff\xff\xff\xff\xff\xff".as_slice(),
            b"LIMGEN2\0\x01\0\0\0\0\0\0\0x".as_slice(),
        ] {
            fs::write(&path, bytes).unwrap();
            assert!(read_cached_expansion(&directory, "robustness-key").is_none());
        }
        OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len(MAX_CACHE_ARTIFACT_BYTES + 1)
            .unwrap();
        assert!(read_bounded_cache_file(&path).is_none());
        let _ = fs::remove_dir_all(directory);
    }

    #[test]
    fn generated_context_must_match_the_key_even_with_a_valid_source_digest() {
        let directory = std::env::temp_dir().join(format!(
            "lim-generated-context-{}-{}",
            std::process::id(),
            CACHE_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        fs::create_dir(directory.join("generated")).unwrap();
        let header = "#generated-context ((producer \"expected\"))\n";
        let key = format!("lim-generator-cache-v15\ncontext=({})", header.trim());
        let wrong = "#generated-context ((producer \"other\"))\n#type Value #u64\n";
        publish_generated_expansion(&directory, &key, wrong).unwrap();
        assert!(load_generated_expansion(&directory, &key)
            .unwrap()
            .is_none());
        let right = format!("{header}\n#type Value #u64\n");
        publish_generated_expansion(&directory, &key, &right).unwrap();
        let (_, forms) = load_generated_expansion(&directory, &key).unwrap().unwrap();
        assert_eq!(forms.len(), 1);
        assert!(!crate::generator_authority::is_header(&forms[0].expr));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn staging_filename_filter_matches_basename_extension_semantics() {
        for name in [
            "tmp",
            ".tmp",
            "a.tmp",
            ".a.tmp",
            "..tmp",
            "...tmp",
            "generated-012345.7-9.tmp",
            "a.TMP",
            "a.tmp.",
            "a.tmp.backup",
            "é.tmp",
            "é.TMP",
            "é.tmp.cache",
            "",
            ".",
            "..",
        ] {
            let name = std::ffi::OsStr::new(name);
            assert_eq!(
                is_cache_staging_name(name),
                Path::new(name)
                    .extension()
                    .is_some_and(|extension| extension == "tmp"),
                "{name:?}"
            );
        }
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            for bytes in [b"\xff.tmp".as_slice(), b"\xff.tmp.backup", b"\xff.TMP"] {
                let name = std::ffi::OsStr::from_bytes(bytes);
                assert_eq!(
                    is_cache_staging_name(name),
                    Path::new(name)
                        .extension()
                        .is_some_and(|extension| extension == "tmp"),
                    "{name:?}"
                );
            }
        }
    }

    #[test]
    fn cache_housekeeping_is_throttled_without_removing_recent_staging() {
        let directory = std::env::temp_dir().join(format!(
            "lim-throttled-cache-cleanup-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let stale = directory.join("abandoned.tmp");
        let recent = directory.join("active.tmp");
        let create_stale = || {
            fs::write(&stale, "incomplete").unwrap();
            OpenOptions::new()
                .write(true)
                .open(&stale)
                .unwrap()
                .set_times(
                    fs::FileTimes::new()
                        .set_modified(SystemTime::now() - Duration::from_secs(2 * 60 * 60)),
                )
                .unwrap();
        };
        create_stale();
        fs::write(&recent, "active").unwrap();
        cleanup_abandoned_staging(&directory);
        assert!(!stale.exists());
        assert!(recent.exists());
        create_stale();
        cleanup_abandoned_staging(&directory);
        assert!(
            stale.exists(),
            "repeat lookup must not traverse the directory"
        );
        CACHE_CLEANUP_TIMES
            .get()
            .unwrap()
            .lock()
            .unwrap()
            .insert(directory.clone(), Instant::now() - CACHE_CLEANUP_INTERVAL);
        cleanup_abandoned_staging(&directory);
        assert!(!stale.exists(), "cleanup resumes after its interval");
        assert!(recent.exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn generated_source_origins_refresh_without_rerunning_generation() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-origins-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        let first = cached_generated_source_with_origins(
            &directory,
            "origins",
            &["z.lim:8".into(), "a.lim:3".into(), "a.lim:3".into()],
            || Ok("#type Cached #u64\n".into()),
        )
        .unwrap();
        assert!(first.starts_with("// Generated from:\n// a.lim:3\n// z.lim:8\n\n"));
        let second = cached_generated_source_with_origins(
            &directory,
            "origins",
            &["new.lim:12".into()],
            || panic!("provenance changes must not rerun generation"),
        )
        .unwrap();
        assert!(second.starts_with("// Generated from:\n// a.lim:3\n// new.lim:12\n// z.lim:8\n\n"));
        assert_eq!(
            crate::parse_source_unit(&first)
                .unwrap()
                .into_iter()
                .map(|form| form.expr)
                .collect::<Vec<_>>(),
            crate::parse_source_unit(&second)
                .unwrap()
                .into_iter()
                .map(|form| form.expr)
                .collect::<Vec<_>>()
        );
        let third = cached_generated_source_with_origins(
            &directory,
            "origins",
            &["new.lim:12".into()],
            || panic!("the refreshed digest must validate on subsequent cache hits"),
        )
        .unwrap();
        assert_eq!(second, third);
        let paths = fs::read_dir(&directory)
            .unwrap()
            .chain(fs::read_dir(generated_source_directory(&directory)).unwrap())
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.is_file())
            .collect::<Vec<_>>();
        let timestamp = std::time::UNIX_EPOCH + Duration::from_secs(12345);
        for path in &paths {
            fs::File::options()
                .write(true)
                .open(path)
                .unwrap()
                .set_times(fs::FileTimes::new().set_modified(timestamp))
                .unwrap();
        }
        for sites in [
            vec!["z.lim:8".into(), "new.lim:12".into(), "a.lim:3".into()],
            vec!["a.lim:3".into()],
            vec![],
        ] {
            let cached =
                cached_generated_source_with_origins(&directory, "origins", &sites, || {
                    panic!("covered origins must reuse generation")
                })
                .unwrap();
            assert_eq!(cached, second);
            for path in &paths {
                assert_eq!(
                    fs::metadata(path).unwrap().modified().unwrap(),
                    timestamp,
                    "covered origins must not rewrite {}",
                    path.display()
                );
            }
        }
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn nested_deduplicated_generators_keep_precise_builtin_origins() {
        let source = "#gn inner () `((#generate #optional ((type #u64) (name Shared))))
#gn outer () `((#generate inner) (#generate #optional ((type #u64) (name OuterOnly))))
#gn other () `((#generate inner))\n#generate outer\n#generate other\n#generate other\n";
        let mut origins = Origins::default();
        expand_with_origins(crate::parse_source_unit(source).unwrap(), None, "", &mut origins).unwrap();
        let sites = |name: &str| {
            let (_, spans) = origins
                .builtins
                .iter()
                .find(|(key, _)| key.contains(name))
                .unwrap();
            let mut lines = spans.iter().map(|span| span.line).collect::<Vec<_>>();
            lines.sort();
            lines.dedup();
            lines
        };
        assert_eq!(sites("Shared"), vec![4, 5, 6]);
        assert_eq!(sites("OuterOnly"), vec![4]);
        assert_eq!(origins.user.len(), 3);
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
                        ("shared-key", "#type Shared #u64\n")
                    } else {
                        ("other-key", "#type Other #u64\n")
                    };
                    cached_generated_source(&directory, key, || Ok(source.into())).unwrap()
                })
            })
            .collect::<Vec<_>>();
        for (index, worker) in workers.into_iter().enumerate() {
            assert_eq!(
                worker.join().unwrap(),
                if index % 2 == 0 {
                    "#type Shared #u64\n"
                } else {
                    "#type Other #u64\n"
                }
            );
        }
        assert_eq!(
            cached_generated_source(&directory, "shared-key", || {
                Err("concurrent cache entry was not published coherently".into())
            })
            .unwrap(),
            "#type Shared #u64\n"
        );
        assert_eq!(
            cached_generated_source(&directory, "other-key", || {
                Err("concurrent cache entry was not published coherently".into())
            })
            .unwrap(),
            "#type Other #u64\n"
        );
        assert!(fs::read_dir(&directory)
            .unwrap()
            .filter_map(Result::ok)
            .filter(|entry| entry.path().is_file())
            .all(|entry| entry
                .path()
                .extension()
                .is_some_and(|extension| extension != "tmp")));
        assert!(!abandoned.exists(), "stale staging file should be removed");
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn gensym_cache_preserves_identity_and_nested_inherited_symbols() {
        let directory = std::env::temp_dir().join(format!(
            "lim-gensym-cache-{}-{}",
            std::process::id(),
            CACHE_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let source = "#gn-fn emit (name temporary) `((#fn ,name ((task #u64)) #u64
                (#let ,temporary #u64 task) (#return ,temporary)))
#gn child (name temporary) (#gn-call emit name temporary)
#gn-fn forward (name temporary) `((#generate child ,name ,temporary))
#gn parent (name) (#gn-call forward name (#gn-gensym \"task\"))\n#generate parent first\n#generate parent second\n#generate parent first\n";
        let expand = |source: &str| {
            expand_with_generated_cached_and_hits(
                crate::parse_source_unit(source).unwrap(),
                Some(&directory),
                "test-context",
            )
            .unwrap()
        };
        let ((cold, _), hits) = expand(source);
        assert_eq!(hits, 0);
        assert_eq!(cold.len(), 2);
        let ((warm, _), hits) = expand(source);
        assert_eq!(
            hits, 4,
            "both parent and child invocations restore without interpretation"
        );
        assert_eq!(cold, warm);
        let output = cold
            .iter()
            .map(|node| crate::expression_source(&node.expr).unwrap())
            .collect::<Vec<_>>();
        let locals = output
            .iter()
            .map(|source| {
                crate::lex(source)
                    .unwrap()
                    .into_iter()
                    .filter_map(|token| match token.kind {
                        crate::TokenKind::Symbol(name) if crate::gensym::reserved(&name) => {
                            Some(name)
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(locals[0].len(), 2);
        assert_eq!(
            locals[0][0], locals[0][1],
            "reuse the same identity in declaration and reference"
        );
        assert_ne!(locals[0][0], locals[1][0]);
        let reordered = source.replace(
            "#generate parent first\n#generate parent second\n",
            "#generate parent second\n#generate parent first\n",
        );
        let ((reordered, _), hits) = expand(&reordered);
        assert_eq!(hits, 4);
        assert_eq!(
            reordered[0].expr, cold[1].expr,
            "identity is independent of expansion order"
        );
        let changed = source.replace("(#return ,temporary)", "(#return task)");
        let ((changed, _), hits) = expand(&changed);
        assert_eq!(
            hits, 2,
            "child helper changes invalidate the child, not the forwarding parent"
        );
        assert_ne!(changed[0].expr, cold[0].expr);
        fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn gensym_cache_rejects_a_foreign_namespace_even_with_a_valid_checksum() {
        let directory = std::env::temp_dir().join(format!(
            "lim-gensym-foreign-cache-{}-{}",
            std::process::id(),
            CACHE_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let source = "#gn emit () `((#type ,(#gn-gensym \"task\") #u64))\n#generate emit\n";
        let expand = || {
            expand_with_generated_cached_and_hits(
                crate::parse_source_unit(source).unwrap(),
                Some(&directory),
                "",
            )
            .unwrap()
        };
        let ((cold, _), hits) = expand();
        assert_eq!(hits, 0);
        let path = fs::read_dir(&directory)
            .unwrap()
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .find(|path| path.extension().is_some_and(|extension| extension == "key"))
            .unwrap();
        let key = fs::read_to_string(&path).unwrap();
        let (_, key) = key.split_once('\n').unwrap();
        let mut forms = read_cached_expansion(&directory, key).unwrap();
        let Expr::List(items) = &mut forms[0] else {
            panic!()
        };
        let Expr::Symbol(name) = &mut items[1] else {
            panic!()
        };
        // Keep valid syntax and checksum, but make ownership structurally wrong.
        let digit = crate::gensym::PREFIX.len() + 1;
        let replacement = if name.as_bytes()[digit] == b'0' {
            "1"
        } else {
            "0"
        };
        name.replace_range(digit..digit + 1, replacement);
        write_cached_expansion(&directory, key, &forms);
        assert!(read_cached_expansion(&directory, key).is_some());
        let ((repaired, _), hits) = expand();
        assert_eq!(hits, 0);
        assert_eq!(repaired, cold);
        let (_, hits) = expand();
        assert_eq!(hits, 1);
        fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn gensym_evaluations_and_helper_calls_share_one_invocation_counter() {
        let source = "#gn-fn fresh () (#gn-gensym \"task\")
#gn emit () `((#type ,(#gn-call fresh) #u64) (#type ,(#gn-call fresh) #u64))
#generate emit\n";
        let ((forms, _), _) =
            expand_with_generated_cached_and_hits(crate::parse_source_unit(source).unwrap(), None, "").unwrap();
        assert_eq!(forms.len(), 2);
        let Expr::List(first) = &forms[0].expr else {
            panic!()
        };
        let Expr::List(second) = &forms[1].expr else {
            panic!()
        };
        assert_ne!(first[1], second[1]);
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
                gensym_scopes: Vec::new(),
                gensyms: crate::gensym::Registry::default(),
                seen_invocations: HashSet::new(),
                invocation_artifacts: HashMap::new(),
                invocation_children: HashMap::new(),
                active_invocations: Vec::new(),
                generation_origins: Vec::new(),
                origins: &mut Origins::default(),
                invocation_builtins: HashMap::new(),
                active_builtins: Vec::new(),
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
        let source = "#gn-fn make-type (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64))\n#gn-fn make-alias (name) `,(#gn-call make-type name)\n#gn-fn unused (name) (#gn-list name)\n#gn alias (name) (#gn-call make-alias name)\n#gn forward (call) (#gn-list call)\n#gn spare (name) (#gn-list name)\n#generate forward (#generate alias CachedType)\n#generate alias CachedType\n";
        let parse_forms = |source: &str| crate::parse_source_unit(source).unwrap();

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
        for entry in fs::read_dir(generated_source_directory(&directory))
            .unwrap()
            .filter_map(Result::ok)
        {
            let path = entry.path();
            if path.extension().is_some_and(|extension| extension == "lim") {
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

        let changed_dependency = source.replace("name #u64", "name #u32");
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
    fn cached_generators_replay_literal_enum_contributions() {
        let directory = loop {
            let sequence = CACHE_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "lim-collection-cache-{}-{sequence}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => break path,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create collection cache directory: {error}"),
            }
        };
        let source = "#gn error-case (variant payload)
              `((#enum-contribute Error (,variant ,payload)))
#generate error-case First #u64
#generate error-case Second #u32\n";
        let expand = |source: &str| {
            expand_with_generated_cached_and_hits(
                crate::parse_source_unit(source).unwrap(),
                Some(&directory),
                "",
            )
            .unwrap()
        };
        let ((first, _), _) = expand(source);
        let ((warm, _), hits) = expand(source);
        assert_eq!(hits, 2);
        assert_eq!(first, warm);
        let changed = source.replace("Second #u32", "Second #u16");
        let ((changed_forms, _), hits) = expand(&changed);
        assert_eq!(hits, 1);
        assert_ne!(first, changed_forms);
        assert_eq!(first.len(), 2);
        assert!(format!("{:?}", first[0].expr).contains("#enum-contribute"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn identical_literal_list_arguments_deduplicate() {
        let source = "#gn alias (entries) `((#type Alias ,(#gn-first entries)))
#generate alias (#u64)
#generate alias (#u64)\n";
        let ((forms, _), _) =
            expand_with_generated_cached_and_hits(crate::parse_source_unit(source).unwrap(), None, "").unwrap();
        assert_eq!(forms.len(), 1);
        assert!(format!("{:?}", forms[0].expr).contains("Alias"));
    }

    #[test]
    fn bare_identifiers_remain_literal_syntax() {
        let source = "#gn alias (entry) `((#type Alias ,entry))
#generate alias Entries\n";
        let ((forms, _), _) =
            expand_with_generated_cached_and_hits(crate::parse_source_unit(source).unwrap(), None, "").unwrap();
        assert!(format!("{:?}", forms[0].expr).contains("Entries"));
    }

    #[test]
    fn old_generator_keyword_is_not_accepted() {
        let source = "#generator alias (name) `((#type ,name #u64))\n#generate alias Old\n";
        assert!(crate::parse_program(source).is_err());
    }

    #[test]
    fn generated_cache_invalidates_when_capability_contract_changes() {
        let directory = std::env::temp_dir().join(format!(
            "lim-generator-capability-cache-{}",
            std::process::id()
        ));
        let source = |operation: &str| {
            format!(
                "#fn less {{ #params = ((a (#ref #u64)) (b (#ref #u64))); #returns = #bool; #body = ( (#return true) ); }}\n#fn less-v2 {{ #params = ((a (#ref #u64)) (b (#ref #u64))); #returns = #bool; #body = ( (#return true) ); }}\n#capability sortable #u64 (({operation} ((#ref #u64) (#ref #u64)) #bool))\n#gn emit ((element sortable)) (#gn-list (#gn-list (#gn-symbol \"#type\") Generated element))\n#generate emit #u64\n"
            )
        };
        let expand = |text: &str| {
            expand_with_generated_cached_and_hits(crate::parse_source_unit(text).unwrap(), Some(&directory), "")
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
            "#gn make (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name #u64))\n#generate make ContextType\n";
        let parse_forms = |source: &str| crate::parse_source_unit(source).unwrap();

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
