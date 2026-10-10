//! Built-in generator expansion, validation witnesses, and source publication.
//! Runtime parsing and semantic checking consume ordinary emitted declarations.
use super::{async_cfg, async_contract, async_dispatch, async_fn, async_source};
use crate::*;

pub(crate) fn async_function_statement_source(
    expression: &SpannedExpr,
    statement_index: usize,
) -> Option<&SpannedExpr> {
    if matches!(
        &expression.expr,
        Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#fn" || head == "fn")
    ) {
        return expression.children.get(4 + statement_index);
    }
    expression
        .children
        .iter()
        .find_map(|child| async_function_statement_source(child, statement_index))
}

pub(crate) fn async_lowering_statement_index(error: &str) -> Option<usize> {
    let marker = "async statement ";
    let start = error.find(marker)? + marker.len();
    let rest = &error[start..];
    let end = rest.find(':')?;
    rest[..end].parse().ok()
}

pub(crate) fn is_async_invocation(expression: &SpannedExpr) -> bool {
    matches!(&expression.expr, Expr::List(items)
        if matches!(items.first(), Some(Expr::At))
        && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "async-fn" | "async-fn-pinned")))
}

pub(crate) type ExpansionPlans = HashMap<(u32, usize, usize), HashMap<usize, HashSet<String>>>;

pub(crate) fn async_generated_source(
    invocation: &Expr,
    span: Span,
    capture_plans: Option<&ExpansionPlans>,
    copy_types: &HashSet<String>,
    type_environment: &async_fn::AsyncTypeEnvironment,
) -> Result<String, String> {
    let key = (span.source_id, span.start, span.end);
    let captures = capture_plans.and_then(|plans| plans.get(&key));
    let source = async_fn::generated_source_with_environment(
        invocation,
        captures,
        copy_types,
        type_environment,
    )?;
    // Private capture witnesses are checked too: freshen introduced match
    // bindings before analysis, without changing public parameter keys.
    // The uncollapsed helpers are private capture-analysis witnesses only.
    // Executable/inspectable output uses one dispatcher per concrete future.
    if capture_plans.is_some() {
        async_dispatch::collapse(&source, type_environment)
    } else {
        async_dispatch::hygienize_source(&source, type_environment)
    }
}

pub(crate) fn async_type_environment(
    expressions: &[SpannedExpr],
) -> async_fn::AsyncTypeEnvironment {
    let mut environment = async_fn::AsyncTypeEnvironment::default();
    for expression in expressions {
        // Only declarations contributing to the environment need normalization.
        // In particular, do not copy an async invocation's entire function body.
        if !matches!(&expression.expr, Expr::List(items)
            if matches!(items.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#fn" | "#unsafe-fn" | "#extern-fn" | "#enum" | "#type" | "#struct")))
        {
            continue;
        }
        // Async lowering needs function signatures, not a second parse of
        // every imported function body. Ordinary parsing validates the bodies.
        let signature = match &expression.expr {
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#fn" | "#unsafe-fn")) => {
                Expr::List(items.iter().take(4).cloned().collect())
            }
            other => other.clone(),
        };
        let normalized = normalize_keywords(signature);
        let parsed = match &normalized {
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "fn" | "unsafe-fn")) => {
                parse_function_parts(items, false, false).map(Item::Function)
            }
            _ => parse_item(&normalized),
        };
        let Ok(item) = parsed else {
            continue;
        };
        match item {
            Item::Enum { name, variants, .. } => {
                environment.enums.insert(
                    name,
                    variants
                        .into_iter()
                        .map(|variant| {
                            (
                                variant.name,
                                variant.fields.iter().map(type_source).collect(),
                            )
                        })
                        .collect(),
                );
            }
            Item::TypeAlias { name, target, .. } => {
                environment.aliases.insert(name, type_source(&target));
            }
            Item::Struct { name, fields, .. } => {
                environment.struct_field_order.insert(
                    name.clone(),
                    fields.iter().map(|field| field.name.clone()).collect(),
                );
                environment.struct_fields.insert(
                    name,
                    fields
                        .into_iter()
                        .map(|field| (field.name, type_source(&field.ty)))
                        .collect(),
                );
            }
            Item::Function(function) => {
                environment.function_parameter_order.insert(
                    function.name.clone(),
                    function
                        .parameters
                        .iter()
                        .map(|parameter| parameter.name.clone())
                        .collect(),
                );
                environment
                    .function_results
                    .insert(function.name.clone(), type_source(&function.return_type));
                environment.functions.insert(
                    function.name,
                    function
                        .parameters
                        .into_iter()
                        .map(|parameter| (parameter.name, type_source(&parameter.ty)))
                        .collect(),
                );
            }
            _ => {}
        }
    }
    environment
}

pub(crate) fn copy_type_names_from_items(items: &[Item]) -> HashSet<String> {
    let program = Program {
        items: items.to_vec(),
        source: None,
        source_files: Vec::new(),
        statement_spans: HashMap::new(),
        statement_expressions: HashMap::new(),
        declaration_spans: HashMap::new(),
        declaration_expressions: HashMap::new(),
        declaration_occurrences: HashMap::new(),
        generated_source_invocations: HashMap::new(),
        syntax_bundle_uses: HashMap::new(),
        generator_validation: None,
    };
    let linear_types = linearcheck::LinearTypes::from_program(&program);
    items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, .. } | Item::Struct { name, .. } | Item::Enum { name, .. } => {
                Some(name.clone())
            }
            _ => None,
        })
        .filter(|name| linear_types.can_repeat(&Type::Named(name.clone())))
        .collect()
}

pub(crate) fn copy_type_names(expressions: &[SpannedExpr]) -> HashSet<String> {
    let items = expressions
        .iter()
        .filter(|expression| {
            matches!(&expression.expr,
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#type" | "#struct" | "#enum" | "#linear")))
            || matches!(&expression.expr, Expr::List(items)
                if matches!(items.first(), Some(Expr::At))
                && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "optional" | "result")))
        })
        .filter_map(|expression| {
            let invocation = normalize_builtin_generator_invocation(&expression.expr).ok()?;
            parse_item(&normalize_keywords(invocation)).ok()
        })
        .collect::<Vec<_>>();
    copy_type_names_from_items(&items)
}

pub(crate) fn async_copy_type_identity(types: &HashSet<String>) -> String {
    let mut names = types.iter().collect::<Vec<_>>();
    names.sort();
    format!("{names:?}")
}

pub(crate) fn async_type_environment_identity(
    environment: &async_fn::AsyncTypeEnvironment,
) -> String {
    let mut enums = environment.enums.iter().collect::<Vec<_>>();
    enums.sort_by(|left, right| left.0.cmp(right.0));
    let enums = enums
        .into_iter()
        .map(|(name, variants)| {
            let mut variants = variants.iter().collect::<Vec<_>>();
            variants.sort_by(|left, right| left.0.cmp(right.0));
            let variants = variants
                .into_iter()
                .map(|(name, fields)| format!("{name}:{fields:?}"))
                .collect::<Vec<_>>()
                .join(",");
            format!("{name}{{{variants}}}")
        })
        .collect::<Vec<_>>()
        .join(";");
    let mut aliases = environment.aliases.iter().collect::<Vec<_>>();
    aliases.sort_by(|left, right| left.0.cmp(right.0));
    let aliases = aliases
        .into_iter()
        .map(|(name, target)| format!("{name}={target}"))
        .collect::<Vec<_>>()
        .join(";");
    let mut functions = environment.functions.iter().collect::<Vec<_>>();
    functions.sort_by(|left, right| left.0.cmp(right.0));
    let functions = functions
        .into_iter()
        .map(|(name, parameters)| {
            let mut parameters = parameters.iter().collect::<Vec<_>>();
            parameters.sort_by(|left, right| left.0.cmp(right.0));
            let parameters = parameters
                .into_iter()
                .map(|(name, ty)| format!("{name}:{ty}"))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{name}[order={:?}]({parameters})->{}",
                environment.function_parameter_order.get(name),
                environment
                    .function_results
                    .get(name)
                    .map_or("", String::as_str)
            )
        })
        .collect::<Vec<_>>()
        .join(";");
    let mut structs = environment.struct_fields.iter().collect::<Vec<_>>();
    structs.sort_by(|left, right| left.0.cmp(right.0));
    let structs = structs
        .into_iter()
        .map(|(name, fields)| {
            let mut fields = fields.iter().collect::<Vec<_>>();
            fields.sort_by(|left, right| left.0.cmp(right.0));
            let fields = fields
                .into_iter()
                .map(|(name, ty)| format!("{name}:{ty}"))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{name}[order={:?}]{{{fields}}}",
                environment.struct_field_order.get(name)
            )
        })
        .collect::<Vec<_>>()
        .join(";");
    format!("enums:{enums};aliases:{aliases};functions:{functions};structs:{structs}")
}

struct AsyncCaptureInvocation {
    key: (u32, usize, usize),
    poll_name: String,
    pinned: bool,
}

fn async_capture_invocations(program: &Program) -> Vec<AsyncCaptureInvocation> {
    let mut invocations = Vec::new();
    for span in program.generated_source_invocations.values() {
        let Some(file) = program.source_files.get(span.source_id as usize) else {
            continue;
        };
        let Some(text) = file.source.get(span.start..span.end) else {
            continue;
        };
        let Ok(mut parsed) = parse(text) else {
            continue;
        };
        if parsed.len() != 1 {
            continue;
        }
        let expression = parsed.remove(0).expr;
        let Ok(normalized) = normalize_builtin_generator_invocation(&expression) else {
            continue;
        };
        let Expr::List(items) = &normalized else {
            continue;
        };
        let Some(Expr::Symbol(kind)) = items.get(1) else {
            continue;
        };
        let pinned = kind == "async-fn-pinned";
        if kind != "async-fn" && !pinned {
            continue;
        }
        let Some(Expr::List(names)) = items.get(2) else {
            continue;
        };
        let Some(Expr::Symbol(poll_name)) = names.get(4) else {
            continue;
        };
        invocations.push(AsyncCaptureInvocation {
            key: (span.source_id, span.start, span.end),
            poll_name: poll_name.clone(),
            pinned,
        });
    }
    invocations
}

fn async_capture_plans(
    program: &Program,
    live_parameters: &HashMap<String, HashSet<usize>>,
    invocations: &[AsyncCaptureInvocation],
) -> ExpansionPlans {
    let mut plans = HashMap::new();
    for invocation in invocations {
        let mut stages = HashMap::new();
        let prefix = format!(
            "{}{}-resume-",
            invocation.poll_name,
            if invocation.pinned { "-move" } else { "" }
        );
        for item in &program.items {
            let Item::Function(function) = item else {
                continue;
            };
            let Some(stage_index) = function
                .name
                .strip_prefix(&prefix)
                .and_then(|suffix| suffix.parse::<usize>().ok())
            else {
                continue;
            };
            let capture_count = function.parameters.len().saturating_sub(2);
            let live = live_parameters.get(&function.name);
            let captures = function
                .parameters
                .iter()
                .enumerate()
                .take(capture_count)
                .filter(|(parameter_index, _)| {
                    live.is_some_and(|live| live.contains(parameter_index))
                })
                .map(|(_, parameter)| parameter.name.clone())
                .collect();
            stages.insert(stage_index, captures);
        }
        plans.insert(invocation.key, stages);
    }
    plans
}

pub(crate) fn async_capture_plan_identity(
    plan: Option<&HashMap<usize, HashSet<String>>>,
) -> String {
    let Some(plan) = plan else {
        return "syntax-fallback".into();
    };
    let mut stages = plan.iter().collect::<Vec<_>>();
    stages.sort_by_key(|(stage, _)| **stage);
    stages
        .into_iter()
        .map(|(stage, names)| {
            let mut names = names.iter().collect::<Vec<_>>();
            names.sort();
            format!("{stage}:{names:?}")
        })
        .collect::<Vec<_>>()
        .join(";")
}

pub(crate) fn parse_program_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<Program, SourceError> {
    expand_program_in_directory(source, base, source_path, config, cache_directory)
        .map(|(program, _)| program)
}

pub(crate) fn expand_program_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<(Program, ExpansionPlans), SourceError> {
    let prepared = prepare_program_syntax(source, base, source_path, config, cache_directory)?;
    expand_prepared_program(&prepared)
}

pub(crate) fn expand_prepared_program(
    prepared: &PreparedProgramSyntax,
) -> Result<(Program, ExpansionPlans), SourceError> {
    let capture_cache_key = format!(
        "lim-async-captures-v1\nimplementation={}\n{}",
        env!("LIM_BUILD_FINGERPRINT"),
        prepared.dependency_context
    );
    if let Some(directory) = prepared
        .capture_cache_directory
        .as_deref()
        .filter(|_| prepared.expressions.iter().any(is_async_invocation))
    {
        if let Some(plans) = generator::read_cached_expansion(directory, &capture_cache_key)
            .and_then(|forms| decode_async_capture_plans(&forms))
        {
            if let Ok(program) = parse_prepared_program_with_async_captures(prepared, Some(&plans))
            {
                crate::cache_report::record(
                    "async-captures",
                    &generator::cache_path(directory, &capture_cache_key),
                    &capture_cache_key,
                    "hit",
                );
                return Ok((program, plans));
            }
        }
    }
    let probe = parse_prepared_program_with_async_captures(prepared, None)?;
    let invocations = async_capture_invocations(&probe);
    if invocations.is_empty() {
        return Ok((probe, ExpansionPlans::new()));
    }
    let prefixes = invocations
        .iter()
        .map(|invocation| {
            format!(
                "{}{}-resume-",
                invocation.poll_name,
                if invocation.pinned { "-move" } else { "" }
            )
        })
        .collect::<Vec<_>>();
    let live_parameters = match typecheck::typed_capture_requirements(&probe, &prefixes) {
        Ok(live_parameters) => live_parameters,
        Err(_) => {
            // Keep parsing semantically invalid programs so callers can ask
            // the ordinary checked-program boundary for its source diagnostic.
            let no_typed_capture_plan = ExpansionPlans::new();
            let fallback =
                parse_prepared_program_with_async_captures(prepared, Some(&no_typed_capture_plan))?;
            return Ok((fallback, no_typed_capture_plan));
        }
    };
    let capture_plans = async_capture_plans(&probe, &live_parameters, &invocations);
    if capture_plans.is_empty() {
        return Ok((probe, capture_plans));
    }
    let program = parse_prepared_program_with_async_captures(prepared, Some(&capture_plans))?;
    if let Some(directory) = prepared.capture_cache_directory.as_deref() {
        crate::cache_report::record(
            "async-captures",
            &generator::cache_path(directory, &capture_cache_key),
            &capture_cache_key,
            "missing-or-invalid",
        );
        generator::write_cached_expansion(
            directory,
            &capture_cache_key,
            &encode_async_capture_plans(&capture_plans),
        );
    }
    Ok((program, capture_plans))
}

pub(crate) fn encode_async_capture_plans(plans: &ExpansionPlans) -> Vec<Expr> {
    let mut entries = plans.iter().collect::<Vec<_>>();
    entries.sort_by_key(|(key, _)| **key);
    entries
        .into_iter()
        .map(|((source_id, start, end), stages)| {
            let mut stages = stages.iter().collect::<Vec<_>>();
            stages.sort_by_key(|(stage, _)| **stage);
            Expr::List(vec![
                Expr::List(vec![
                    Expr::Integer(i128::from(*source_id)),
                    Expr::Integer(*start as i128),
                    Expr::Integer(*end as i128),
                ]),
                Expr::List(
                    stages
                        .into_iter()
                        .map(|(stage, captures)| {
                            let mut captures = captures
                                .iter()
                                .cloned()
                                .map(Expr::Symbol)
                                .collect::<Vec<_>>();
                            captures.sort_by(|left, right| match (left, right) {
                                (Expr::Symbol(left), Expr::Symbol(right)) => left.cmp(right),
                                _ => unreachable!(),
                            });
                            Expr::List(vec![Expr::Integer(*stage as i128), Expr::List(captures)])
                        })
                        .collect(),
                ),
            ])
        })
        .collect()
}

pub(crate) fn decode_async_capture_plans(forms: &[Expr]) -> Option<ExpansionPlans> {
    fn index(expression: &Expr) -> Option<usize> {
        let Expr::Integer(value) = expression else {
            return None;
        };
        usize::try_from(*value).ok()
    }
    let mut plans = ExpansionPlans::new();
    if forms.is_empty() {
        return None;
    }
    for form in forms {
        let Expr::List(entry) = form else {
            return None;
        };
        let [Expr::List(key), Expr::List(stages)] = entry.as_slice() else {
            return None;
        };
        let [source_id, start, end] = key.as_slice() else {
            return None;
        };
        let key = (
            u32::try_from(index(source_id)?).ok()?,
            index(start)?,
            index(end)?,
        );
        if key.1 > key.2 {
            return None;
        }
        let mut decoded_stages = HashMap::new();
        for stage in stages {
            let Expr::List(stage) = stage else {
                return None;
            };
            let [stage, Expr::List(names)] = stage.as_slice() else {
                return None;
            };
            let mut captures = HashSet::new();
            for name in names {
                let Expr::Symbol(name) = name else {
                    return None;
                };
                if !captures.insert(name.clone()) {
                    return None;
                }
            }
            if decoded_stages.insert(index(stage)?, captures).is_some() {
                return None;
            }
        }
        if plans.insert(key, decoded_stages).is_some() {
            return None;
        }
    }
    Some(plans)
}

pub(crate) struct PreparedProgramSyntax {
    pub(crate) bundles: syntax_bundle::Bundles,
    pub(crate) capture_cache_directory: Option<PathBuf>,
    pub(crate) root_source: String,
    pub(crate) expressions: Vec<SpannedExpr>,
    pub(crate) source_files: Vec<SourceFile>,
    pub(crate) dependency_context: String,
    pub(crate) user_generated: Vec<Expr>,
    pub(crate) generator_origins: generator::Origins,
    pub(crate) async_copy_types: HashSet<String>,
    pub(crate) async_types: async_fn::AsyncTypeEnvironment,
    pub(crate) worker_functions: HashMap<String, Function>,
}

pub(crate) fn prepare_program_syntax(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<PreparedProgramSyntax, SourceError> {
    let (loaded, source_files) = load_imports_with_sources(source, base, source_path, config)?;
    let dependency_context = generator_dependency_context(&loaded, config);
    let mut bundles = syntax_bundle::Bundles::default();
    let loaded = bundles
        .expand(loaded, false)
        .map_err(|error| error.attach(&source_files))?;
    let mut generator_origins = generator::Origins::default();
    let (expanded, user_generated) = generator::expand_with_origins(
        loaded,
        cache_directory,
        &dependency_context,
        &mut generator_origins,
    )
    .map_err(|error| attach_generator_source(error, &source_files))?;
    let expressions = expand_cfg_forms(expanded, config)
        .map_err(|error| attach_generator_source(error, &source_files))?;
    let mut with_protocols = Vec::with_capacity(expressions.len());
    for expression in expressions {
        if is_async_invocation(&expression) {
            let invocation =
                normalize_builtin_generator_invocation(&expression.expr).map_err(|message| {
                    attach_span_to_source_error_kind(
                        message,
                        expression.span,
                        &source_files,
                        "generator error: ",
                    )
                })?;
            let declaration = async_fn::protocol_declaration(&invocation).map_err(|message| {
                attach_span_to_source_error_kind(
                    message,
                    expression.span,
                    &source_files,
                    "generator error: ",
                )
            })?;
            with_protocols.push(SpannedExpr {
                expr: declaration,
                span: expression.span,
                children: vec![],
            });
        }
        with_protocols.push(expression);
    }
    // Bundle expansion rewrites invocation text, but not its call-site origins.
    let builtin_keys = with_protocols
        .iter()
        .filter(|form| {
            !matches!(&form.expr, Expr::List(items)
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#syntax"))
        })
        .map(|form| {
            if matches!(&form.expr, Expr::List(items) if matches!(items.first(), Some(Expr::At))) {
                expression_source(&form.expr).map(Some)
            } else {
                Ok(None)
            }
        })
        .collect::<Result<Vec<_>, String>>()?;
    let expressions = bundles
        .expand(with_protocols, true)
        .map_err(|error| error.attach(&source_files))?;
    for (form, key) in expressions.iter().zip(builtin_keys) {
        if let Some(key) = key {
            let rewritten = expression_source(&form.expr)?;
            if rewritten != key {
                if let Some(origins) = generator_origins.builtins.remove(&key) {
                    generator_origins
                        .builtins
                        .entry(rewritten)
                        .or_default()
                        .extend(origins);
                }
            }
        }
    }
    // Generated declarations and cfg selection are already expanded here, so
    // detect async users after those passes rather than from the root file.
    let needs_async = expressions.iter().any(is_async_invocation);
    let needs_copy_types = needs_async || expressions.iter().any(|expression| {
        matches!(&expression.expr, Expr::List(items)
            if matches!(items.first(), Some(Expr::At))
            && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "optional" | "result")))
    });
    let async_copy_types = if needs_copy_types {
        copy_type_names(&expressions)
    } else {
        HashSet::new()
    };
    let async_types = if needs_async {
        async_type_environment(&expressions)
    } else {
        async_fn::AsyncTypeEnvironment::default()
    };
    let needs_workers = expressions.iter().any(is_thread_spawn_invocation);
    let worker_functions = expressions
        .iter()
        .filter(|_| needs_workers)
        .filter_map(|expression| {
            match parse_item(&normalize_keywords(expression.expr.clone())).ok()? {
                Item::Function(function) if !function.external => {
                    Some((function.name.clone(), function))
                }
                _ => None,
            }
        })
        .collect();
    Ok(PreparedProgramSyntax {
        bundles,
        capture_cache_directory: cache_directory.map(Path::to_path_buf),
        root_source: source.to_owned(),
        expressions,
        source_files,
        dependency_context,
        user_generated,
        generator_origins,
        async_copy_types,
        async_types,
        worker_functions,
    })
}

pub(crate) fn parse_prepared_program_with_async_captures(
    prepared: &PreparedProgramSyntax,
    capture_plans: Option<&ExpansionPlans>,
) -> Result<Program, SourceError> {
    parse_prepared_program_items(prepared, capture_plans, true)
}

/// Declaration input for original-body planning. Async interfaces live in an
/// explicit deferred registry, not invented executable/extern declarations.
/// Ordinary bodies are parsed but stay unnormalized until layout completion;
/// the planner checks only the source models attached to this context.
pub(crate) fn parse_prepared_async_declarations(
    prepared: &PreparedProgramSyntax,
) -> Result<Program, SourceError> {
    parse_prepared_program_items(prepared, None, false)
}

pub(crate) fn parse_prepared_program_items(
    prepared: &PreparedProgramSyntax,
    capture_plans: Option<&ExpansionPlans>,
    expand_async: bool,
) -> Result<Program, SourceError> {
    let expressions = prepared.expressions.clone();
    let mut source_files = prepared.source_files.clone();
    let async_copy_types = &prepared.async_copy_types;
    let async_types = &prepared.async_types;
    let mut items = Vec::with_capacity(expressions.len());
    let mut statement_spans = HashMap::new();
    let mut statement_expressions = HashMap::new();
    let mut declaration_spans = HashMap::new();
    let mut declaration_expressions = HashMap::new();
    let mut declaration_occurrences: HashMap<String, Vec<SpannedExpr>> = HashMap::new();
    let mut generated_source_invocations = HashMap::new();
    let mut async_functions = Vec::new();
    let worker_functions = &prepared.worker_functions;
    for mut expression in expressions {
        if !expand_async && is_async_invocation(&expression) {
            continue;
        }
        let original_async = async_source::Source::from_invocation(&expression)?;
        validate_primitive_spelling(&expression).map_err(|(message, span)| {
            attach_span_to_source_error_kind(message, span, &source_files, "parse error: ")
        })?;
        validate_prefixed_forms(&expression.expr).map_err(|error| {
            attach_span_to_source_error_kind(error, expression.span, &source_files, "parse error: ")
        })?;
        normalize_match_case_forms(&mut expression).map_err(|(error, span)| {
            attach_span_to_source_error_kind(error, span, &source_files, "parse error: ")
        })?;
        let form_span = expression.span;
        let invocation_text = source_files
            .get(form_span.source_id as usize)
            .and_then(|file| file.source.get(form_span.start..form_span.end))
            .unwrap_or("")
            .trim_start();
        let is_generated_output =
            expression.children.is_empty() && invocation_text.starts_with("(@");
        if is_generated_output {
            let generated_text = expression_source(&expression.expr)?;
            let source_id = u32::try_from(source_files.len())
                .map_err(|_| "too many source files while tracking generator output".to_owned())?;
            let mut parsed = parse(&generated_text)?;
            if parsed.len() != 1 {
                return Err("generator output did not parse as exactly one source form".into());
            }
            let mut generated_expression = parsed.remove(0);
            set_source_id(&mut generated_expression, source_id);
            source_files.push(SourceFile {
                path: PathBuf::from(format!(
                    "<generated from {}:{}:{}>",
                    source_files.get(form_span.source_id as usize).map_or_else(
                        || "<source>".to_owned(),
                        |file| file.path.display().to_string()
                    ),
                    form_span.line,
                    form_span.column
                )),
                source: generated_text,
            });
            generated_source_invocations.insert(source_id, form_span);
            expression = generated_expression;
        }
        let original_async = match original_async {
            Some(source) => Some(source),
            None => async_source::Source::from_invocation(&expression)?,
        };
        if let Some(source) = original_async {
            async_functions.push(source);
        }
        collect_function_statement_spans(
            &expression,
            &mut statement_spans,
            &mut statement_expressions,
        );
        let normalized_invocation = normalize_builtin_generator_invocation(&expression.expr)
            .map_err(|error| {
                attach_span_to_source_error_kind(
                    error,
                    form_span,
                    &source_files,
                    "generator error: ",
                )
            })?;
        // Keep the original source tree for diagnostics without recursively
        // copying it. Normalization below works on its own invocation tree.
        let source_expression = expression;
        let mut expression = normalize_keywords(normalized_invocation.clone());
        normalize_match_cases_expr(&mut expression);
        let mut generated_declarations = HashMap::new();
        if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::At)) {
                let kind = forms.get(1).and_then(|form| match form {
                    Expr::Symbol(kind) => Some(kind.as_str()),
                    _ => None,
                });
                if matches!(
                    kind,
                    Some(
                        "thread-spawn"
                            | "optional"
                            | "result"
                            | "vec"
                            | "vec-alloc"
                            | "vec-sort"
                            | "async-fn"
                            | "async-fn-pinned"
                    )
                ) {
                    let generated_text = if matches!(kind, Some("async-fn" | "async-fn-pinned")) {
                        async_generated_source(
                            &normalized_invocation,
                            form_span,
                            capture_plans,
                            &async_copy_types,
                            &async_types,
                        )
                        .ok()
                    } else {
                        kind.and_then(|kind| {
                            materialize_builtin_generated_source(
                                kind,
                                forms,
                                &worker_functions,
                                &async_copy_types,
                            )
                            .ok()
                        })
                    };
                    if let Some(generated_text) = generated_text {
                        let source_id = u32::try_from(source_files.len()).map_err(|_| {
                            "too many source files while tracking builtin output".to_owned()
                        })?;
                        let source_path = format!(
                            "<generated from {}:{}:{}>",
                            source_files.get(form_span.source_id as usize).map_or_else(
                                || "<source>".to_owned(),
                                |file| file.path.display().to_string()
                            ),
                            form_span.line,
                            form_span.column
                        );
                        let mut generated_forms = parse(&generated_text)?;
                        for generated_form in &mut generated_forms {
                            set_source_id(generated_form, source_id);
                            normalize_match_case_forms(generated_form)
                                .map_err(|(error, _)| error)?;
                            collect_function_statement_spans(
                                generated_form,
                                &mut statement_spans,
                                &mut statement_expressions,
                            );
                            let parsed_item =
                                parse_item(&normalize_keywords(generated_form.expr.clone()));
                            if let Ok(item) = parsed_item {
                                for name in item_declared_names(&item) {
                                    generated_declarations.insert(name, generated_form.clone());
                                }
                            }
                        }
                        source_files.push(SourceFile {
                            path: PathBuf::from(source_path),
                            source: generated_text,
                        });
                        generated_source_invocations.insert(source_id, form_span);
                    }
                }
            }
        }
        let parsed_items = if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::At)) {
                let generated = if matches!(forms.get(1), Some(Expr::Symbol(kind)) if kind == "async-fn" || kind == "async-fn-pinned")
                {
                    if let Some(error) = async_contract::check(&source_expression, &async_types) {
                        return Err(attach_span_to_source_error_kind(
                            error.message,
                            error.span,
                            &source_files,
                            "generator error: ",
                        ));
                    }
                    if let Err(error) = async_cfg::check(&source_expression, &async_types) {
                        return Err(attach_span_to_source_error_kind(
                            error.message,
                            error.span,
                            &source_files,
                            "generator error: ",
                        ));
                    }
                    async_generated_source(
                        &normalized_invocation,
                        form_span,
                        capture_plans,
                        &async_copy_types,
                        &async_types,
                    )
                    .and_then(|source| parse_generated_source_items(&source))
                } else {
                    parse_generated_items_with_copy_types(forms, &async_copy_types)
                };
                generated.map_err(|error| {
                    let is_async_fn = matches!(forms.get(1), Some(Expr::Symbol(kind)) if kind == "async-fn" || kind == "async-fn-pinned");
                    let escaped_name = error.split_once("unknown value '")
                        .and_then(|(_, rest)| rest.split_once("' outside").map(|(name, _)| name));
                    let error_span = if is_async_fn && escaped_name.is_some() {
                        source_value_symbol_span(&source_expression, escaped_name.unwrap())
                            .unwrap_or(form_span)
                    } else if is_async_fn && error.contains("shadowing") {
                        let details = match &normalized_invocation {
                            Expr::List(invocation) => invocation.get(4),
                            _ => None,
                        }
                        .and_then(|function| function_shadowing(function).ok().flatten());
                        details
                            .and_then(|(name, statement_index)| {
                                let statement = statement_index.and_then(|index| {
                                    async_function_statement_source(&source_expression, index)
                                })?;
                                shadow_binding_span(statement.span, &name, &source_files)
                            })
                            .unwrap_or(form_span)
                    } else if is_async_fn
                        && async_lowering_statement_index(&error).is_some()
                    {
                        let statement_index = async_lowering_statement_index(&error)
                            .expect("checked async statement marker");
                        match &normalized_invocation {
                            Expr::List(invocation) => invocation.get(4),
                            _ => None,
                        }
                        .and_then(|_| {
                            async_function_statement_source(&source_expression, statement_index)
                        })
                        .and_then(|statement| {
                            if error.contains("body cannot return")
                                || error.contains("does not support body returns")
                            {
                                if let Some(span) =
                                    source_form_head_span(statement, &["#return"])
                                {
                                    return Some(span);
                                }
                            }
                            let await_index = if error.contains(
                                "nested #await requires an explicit result type",
                            ) {
                                1
                            } else if error.contains(
                                "awaited #let-else #for initialization cannot yet be combined with suspension",
                            ) {
                                1
                            } else {
                                0
                            };
                            source_form_head_span_nth(statement, &["#await"], await_index)
                                .or_else(|| source_form_head_span_nth(statement, &["#await"], 0))
                                .or(Some(statement.span))
                        })
                        .unwrap_or(form_span)
                    } else if is_async_fn && (error.contains("await") || error.contains("capture")) {
                        source_form_head_span(&source_expression, &["#await"])
                            .unwrap_or(form_span)
                    } else {
                        form_span
                    };
                    attach_span_to_source_error_kind(
                        format!(
                            "{error} while expanding generated declaration {}",
                            expression_source(&expression).unwrap_or_else(|_| "<?>".into())
                        ),
                        error_span,
                        &source_files,
                        "generator error: ",
                    )
                })?
            } else {
                vec![parse_item(&expression).map_err(|error| {
                    let error_span =
                        precise_parse_error_span(&source_expression, &error).unwrap_or(form_span);
                    attach_span_to_source_error_kind(
                        error,
                        error_span,
                        &source_files,
                        "parse error: ",
                    )
                })?]
            }
        } else {
            vec![parse_item(&expression).map_err(|error| {
                attach_span_to_source_error_kind(error, form_span, &source_files, "parse error: ")
            })?]
        };
        for item in parsed_items {
            for name in item_declared_names(&item) {
                let expression = generated_declarations
                    .get(&name)
                    .unwrap_or(&source_expression)
                    .clone();
                declaration_occurrences
                    .entry(name.clone())
                    .or_default()
                    .push(expression.clone());
                declaration_spans.entry(name.clone()).or_insert(form_span);
                declaration_expressions.entry(name).or_insert(expression);
            }
            items.push(item);
        }
    }
    for item in &items {
        for name in item_declared_names(item) {
            if let Some(definition) = prepared.bundles.definitions.get(&name) {
                return Err(SourceError::new(
                    format!("declaration '{name}' conflicts with a syntax bundle"),
                    DiagnosticCode::Parse,
                )
                .at(*declaration_spans.get(&name).unwrap_or(&definition.span))
                .with_label(definition.span, "syntax bundle defined here")
                .attach(&source_files));
            }
        }
    }
    rename_shadowed_locals(
        &mut items,
        &statement_spans,
        &declaration_spans,
        &source_files,
        &prepared.bundles.definitions,
    )?;
    synthesize_thread_join_results(&mut items, &declaration_spans, &source_files)?;
    let mut items = specialize_generic_types(
        items,
        &statement_spans,
        &statement_expressions,
        &declaration_spans,
        &declaration_expressions,
        &source_files,
    )?;
    if expand_async {
        normalize_function_calls(
            &mut items,
            &statement_spans,
            &statement_expressions,
            &declaration_spans,
            &declaration_expressions,
            &source_files,
        )?;
        normalize_struct_literals(
            &mut items,
            &statement_spans,
            &statement_expressions,
            &declaration_spans,
            &declaration_expressions,
            &source_files,
        )?;
    }
    let mut program = Program {
        items,
        source: Some(prepared.root_source.clone()),
        source_files,
        statement_spans,
        statement_expressions,
        declaration_spans,
        declaration_expressions,
        declaration_occurrences,
        generated_source_invocations,
        syntax_bundle_uses: prepared.bundles.uses.clone(),
        generator_validation: None,
    };
    async_source::attach_validation(&mut program, &async_functions);
    Ok(program)
}

pub(crate) fn write_generated_sources_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    directory: &Path,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<(), SourceError> {
    let prepared = prepare_program_syntax(source, base, source_path, config, cache_directory)?;
    let has_async = prepared.expressions.iter().any(|expression| matches!(&expression.expr,
        Expr::List(items) if matches!(items.first(), Some(Expr::At))
            && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "async-fn" | "async-fn-pinned"))));
    let plans = if has_async {
        expand_prepared_program(&prepared)?.1
    } else {
        ExpansionPlans::new()
    };
    write_prepared_generated_sources(&prepared, directory, cache_directory, &plans)
}

pub(crate) fn write_prepared_generated_sources(
    prepared: &PreparedProgramSyntax,
    directory: &Path,
    cache_directory: Option<&Path>,
    async_plans: &ExpansionPlans,
) -> Result<(), SourceError> {
    let expanded = &prepared.expressions;
    let user_generated = &prepared.user_generated;
    let dependency_context = &prepared.dependency_context;
    let worker_functions = &prepared.worker_functions;
    let copy_types = &prepared.async_copy_types;
    let async_types = &prepared.async_types;
    let generated_cache = cache_directory
        .map(Path::to_path_buf)
        .unwrap_or_else(|| directory.join("cache"));
    let location = |span: Span| {
        let path = prepared
            .source_files
            .get(span.source_id as usize)
            .map_or_else(
                || "<source>".to_owned(),
                |file| file.path.display().to_string(),
            );
        format!("{path}:{}", span.line)
    };
    let builtin_origins = prepared
        .generator_origins
        .builtins
        .iter()
        .map(|(key, spans)| {
            (
                key.clone(),
                spans.iter().copied().map(&location).collect::<Vec<_>>(),
            )
        })
        .collect::<HashMap<_, _>>();
    for expression in expanded {
        if !matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::At)))
        {
            continue;
        }
        let capture_key = (
            expression.span.source_id,
            expression.span.start,
            expression.span.end,
        );
        let capture_plan = async_plans.get(&capture_key);
        let invocation = expression_source(&expression.expr)?;
        let original = normalize_builtin_generator_invocation(&expression.expr)?;
        let Expr::List(forms) = normalize_keywords(original.clone()) else {
            continue;
        };
        if !matches!(forms.first(), Some(Expr::At)) {
            continue;
        }
        let kind = expect_symbol(forms.get(1), "generated declaration name")?;
        if !matches!(
            kind,
            "thread-spawn"
                | "vec"
                | "vec-alloc"
                | "vec-sort"
                | "optional"
                | "result"
                | "async-fn"
                | "async-fn-pinned"
        ) {
            continue;
        }
        let key = format!(
            "lim-inspectable-generated-source-v5\ncompiler={}\nimplementation={}\ntarget=x86_64-sysv\ndependency-context={}\nasync-capture-plan={}\nasync-copy-types={}\nasync-type-environment={}\ninvocation={invocation}",
            env!("CARGO_PKG_VERSION"),
            env!("LIM_BUILD_FINGERPRINT"),
            dependency_context,
            async_capture_plan_identity(capture_plan),
            async_copy_type_identity(&copy_types),
            async_type_environment_identity(&async_types),
        );
        generator::cached_generated_source_with_origins(
            &generated_cache,
            &key,
            &builtin_origins[&invocation],
            || {
                if matches!(kind, "async-fn" | "async-fn-pinned") {
                    let source = async_fn::generated_source_with_environment(
                        &original,
                        capture_plan,
                        &copy_types,
                        &async_types,
                    )?;
                    async_dispatch::collapse(&source, &async_types)
                } else {
                    materialize_builtin_generated_source(
                        &kind,
                        &forms,
                        &worker_functions,
                        copy_types,
                    )
                }
            },
        )?;
    }
    if !user_generated.is_empty() {
        let source = user_generated
            .iter()
            .map(expression_source)
            .collect::<Result<Vec<_>, _>>()?
            .join("\n");
        let key = format!(
            "lim-inspectable-user-generator-source-v2\ncompiler={}\ntarget={}-{}\ndependency-context={}\nsource={source}",
            env!("CARGO_PKG_VERSION"),
            std::env::consts::ARCH,
            std::env::consts::OS,
            dependency_context,
        );
        let origins = prepared
            .generator_origins
            .user
            .iter()
            .copied()
            .map(location)
            .collect::<Vec<_>>();
        generator::cached_generated_source_with_origins(&generated_cache, &key, &origins, || {
            Ok(source)
        })?;
    }
    Ok(())
}
