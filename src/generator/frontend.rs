//! Built-in generator expansion, validation witnesses, and source publication.
//! Runtime parsing and semantic checking consume ordinary emitted declarations.
use super::{async_source, async_types};
use crate::*;

pub(crate) fn is_async_invocation(expression: &SpannedExpr) -> bool {
    matches!(&expression.expr, Expr::List(items)
        if matches!(items.first(), Some(Expr::Generate))
        && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "#async-fn" | "#async-fn-pinned")))
}

pub(crate) fn async_type_environment(
    expressions: &[SpannedExpr],
) -> async_types::AsyncTypeEnvironment {
    let mut environment = async_types::AsyncTypeEnvironment::default();
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
        generated_definition_contexts: HashMap::new(),
        syntax_bundle_uses: HashMap::new(),
        contracts: crate::contracts::Metadata::default(),
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
                if matches!(head.as_str(), "#type" | "#struct" | "#enum")))
            || matches!(&expression.expr, Expr::List(items)
                if matches!(items.first(), Some(Expr::Generate))
                && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "#optional" | "#result" | "#array")))
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
    environment: &async_types::AsyncTypeEnvironment,
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

pub(crate) fn parse_program_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<Program, SourceError> {
    expand_program_in_directory(source, base, source_path, config, cache_directory)
}

pub(crate) fn expand_program_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<Program, SourceError> {
    let prepared = prepare_program_syntax(source, base, source_path, config, cache_directory)?;
    expand_prepared_program(&prepared)
}

pub(crate) fn expand_prepared_owned_program(
    prepared: &PreparedProgramSyntax,
    config: &CompileConfig,
    target: &str,
) -> Result<
    (
        typecheck::OwnedProgram,
        Option<Vec<super::async_emit::Generated>>,
    ),
    SourceError,
> {
    if prepared.expressions.iter().any(is_async_invocation) {
        let (program, generated) = graph_generated_owned_program(
            prepared,
            prepared.capture_cache_directory.as_deref(),
            Some((config, target)),
        )?;
        Ok((program, Some(generated)))
    } else {
        let program = expand_prepared_program(prepared)?;
        Ok((typecheck::OwnedProgram::new(program), None))
    }
}

fn validate_syntax_bundle_declarations(
    items: &[Item],
    declaration_spans: &HashMap<String, Span>,
    bundles: &syntax_bundle::Bundles,
    source_files: &[SourceFile],
) -> Result<(), SourceError> {
    for item in items {
        for name in item_declared_names(item) {
            if let Some(definition) = bundles.definitions.get(&name) {
                return Err(SourceError::new(
                    format!("declaration '{name}' conflicts with a syntax bundle"),
                    DiagnosticCode::Parse,
                )
                .at(*declaration_spans.get(&name).unwrap_or(&definition.span))
                .with_label(definition.span, "syntax bundle defined here")
                .attach(source_files));
            }
        }
    }
    Ok(())
}

fn graph_generated_program(
    prepared: &PreparedProgramSyntax,
    cache_directory: Option<&Path>,
) -> Result<(Program, Vec<super::async_emit::Generated>), SourceError> {
    let (program, generated) = graph_generated_owned_program(prepared, cache_directory, None)?;
    Ok((program.into_program(), generated))
}

fn contextual_generated_source(
    prepared: &PreparedProgramSyntax,
    invocation: &SpannedExpr,
    source: &str,
) -> String {
    let producer = match &invocation.expr {
        Expr::List(items) => match items.get(1) {
            Some(Expr::Symbol(name)) => name.as_str(),
            _ => "<builtin>",
        },
        _ => "<builtin>",
    };
    let definition = crate::generator_authority::source_context(
        invocation.span,
        &prepared.generator_origins.definitions,
    )
    .unwrap_or(invocation.span);
    let header = prepared
        .generator_origins
        .context_header(producer, definition, invocation.span);
    format!("{header}\n{source}")
}

fn graph_generated_owned_program(
    prepared: &PreparedProgramSyntax,
    cache_directory: Option<&Path>,
    validation_context: Option<(&CompileConfig, &str)>,
) -> Result<(typecheck::OwnedProgram, Vec<super::async_emit::Generated>), SourceError> {
    let mut planning = super::async_prepare::prepare(prepared)?;
    let invocations = prepared
        .expressions
        .iter()
        .filter(|node| is_async_invocation(node))
        .collect::<Vec<_>>();
    let mut outputs = (0..invocations.len()).map(|_| None).collect::<Vec<_>>();
    let mut staged = Vec::new();
    let key_context = graph_source_key_context(prepared);
    let order = super::async_layout::emission_order(&planning)?;
    for index in order {
        let function = &planning.functions[index];
        let invocation = invocations[index];
        let key = graph_source_key(prepared, &key_context, invocation)?;
        let origins = vec![graph_source_origin(prepared, invocation.span)];
        // Probe through the shared key/digest/parser verifier. Its callback
        // deliberately refuses publication on a miss: all fresh output must
        // pass the complete ordinary program check together before any write.
        let mut missing = false;
        let cached = if let Some(directory) = cache_directory {
            match generator::cached_generated_source_with_origins(directory, &key, &origins, || {
                // The shared loader repairs invalid entries for other routes.
                // Graph output must fail closed instead of disguising a corrupt
                // hit as fresh emission. Mirror only its public artifact naming;
                // key, digest and parser verification stay in the shared loader.
                let digest = generator::stable_hash(
                    format!("lim-generated-source-format-v1\n{key}").as_bytes(),
                );
                for path in [
                    generator::generated_source_directory(directory)
                        .join(format!("generated-{digest:032x}.lim")),
                    directory.join(format!("generated-{digest:032x}.key")),
                    directory.join(format!("generated-{digest:032x}.hash")),
                ] {
                    if path.try_exists().map_err(|error| error.to_string())? {
                        return Err(format!(
                            "invalid async graph cache entry at {}",
                            path.display()
                        ));
                    }
                }
                missing = true;
                Err("async graph output is staged until program validation".into())
            }) {
                Ok(source) => {
                    record_generated_artifact(prepared, invocation, directory, &key)?;
                    Some(source)
                }
                Err(_) if missing => None,
                Err(error) => return Err(error.into()),
            }
        } else {
            None
        };
        let output = if let Some(source) = cached {
            let start = planning
                .interfaces
                .function(&function.model.source_name)
                .ok_or("async cached output lost its start interface")?;
            let Type::Named(frame) = &start.return_type else {
                return Err("async cached output lost its frame identity".into());
            };
            super::async_emit::Generated {
                frame: frame.clone(),
                source,
                origin: function.source.function.span,
            }
        } else {
            let mut output =
                super::async_emit::generate_function(&planning, function).map_err(|error| {
                    SourceError::new(error.message, DiagnosticCode::Type)
                        .at(error.span)
                        .attach(&planning.program.source_files)
                })?;
            let normalized = normalize_builtin_generator_invocation(&invocation.expr)?;
            output.source.push_str(&format!(
                "\n{}\n",
                expression_source(&super::async_interfaces::protocol_declaration(&normalized)?)?
            ));
            output.source = generator::format_generated_source(&contextual_generated_source(
                prepared,
                invocation,
                &output.source,
            ))?;
            // Match the shared cache's inspectable provenance annotation before
            // checking, so the checked program and published text are identical.
            output.source = format!(
                "; Generated from:\n; {}\n\n{}",
                origins[0].replace(['\r', '\n'], " "),
                output.source
            );
            if cache_directory.is_some() {
                staged.push((index, key, origins));
            }
            output
        };
        planning.install_generated_layouts(&output.source)?;
        outputs[index] = Some(output);
    }
    let generated = outputs
        .into_iter()
        .map(|output| output.expect("every async invocation has an emitted or cached output"))
        .collect::<Vec<_>>();
    let mut program =
        typecheck::OwnedProgram::new(super::async_emit::program(&planning, &generated)?);
    crate::file_access::validate(program.program())?;
    validate_syntax_bundle_declarations(
        &program.program().items,
        &program.program().declaration_spans,
        &prepared.bundles,
        &program.program().source_files,
    )?;
    validate_generation_requirements(prepared, &generated)?;
    // Planning is not an ownership proof. Validate both the original witnesses
    // and the emitted ordinary code before accepting or publishing graph output.
    let summaries = cache_directory
        .zip(validation_context)
        .map(|(directory, (config, target))| {
            crate::semantic_cache::Session::begin(directory, program.program(), config, target)
        });
    program
        .validate()
        .map_err(|(message, code, span, labels)| {
            let mut error = SourceError::new(message, code);
            if let Some(span) = span {
                error = error.at(span);
            }
            for (span, message) in labels {
                error = error.with_label(span, message);
            }
            error.attach(&program.program().source_files)
        })?;
    if let Some(summaries) = summaries {
        summaries.publish();
    }
    if let Some(directory) = cache_directory {
        for (index, key, origins) in staged {
            let output = &generated[index];
            let published =
                generator::cached_generated_source_with_origins(directory, &key, &origins, || {
                    Ok(output.source.clone())
                })?;
            record_generated_artifact(prepared, invocations[index], directory, &key)?;
            // A concurrent publisher may have installed this key after the
            // probe. Require identical ordinary declarations rather than use
            // unchecked replacement text or validate the whole program twice.
            let declarations = |text: &str| {
                crate::parse(text)
                    .map(|forms| forms.into_iter().map(|form| form.expr).collect::<Vec<_>>())
            };
            if declarations(&published)? != declarations(&output.source)? {
                return Err("async graph cache changed during validated publication".into());
            }
        }
    }
    Ok((program, generated))
}

fn graph_source_origin(prepared: &PreparedProgramSyntax, span: Span) -> String {
    let path = prepared
        .source_files
        .get(span.source_id as usize)
        .map_or_else(
            || "<source>".to_owned(),
            |file| file.path.display().to_string(),
        );
    format!("{path}:{}", span.line)
}

// The whole-program environment is immutable throughout an expansion or
// publication pass. Sort and serialize it once, not for every invocation.
fn graph_source_key_context(prepared: &PreparedProgramSyntax) -> String {
    format!("lim-inspectable-async-graph-v4\ncompiler={}\nimplementation={}\ndependency-context={}\ncopy-types={}\ntype-environment={}",
        env!("CARGO_PKG_VERSION"), env!("LIM_BUILD_FINGERPRINT"), prepared.graph_dependency_context,
        async_copy_type_identity(&prepared.async_copy_types), async_type_environment_identity(&prepared.async_types))
}

fn graph_source_key(
    prepared: &PreparedProgramSyntax,
    context: &str,
    invocation: &SpannedExpr,
) -> Result<String, String> {
    let header = contextual_generated_source(prepared, invocation, "");
    Ok(format!(
        "{context}\ninvocation={}\ncontext={}",
        expression_source(&invocation.expr)?,
        header.trim()
    ))
}

pub(crate) fn expand_prepared_program(
    prepared: &PreparedProgramSyntax,
) -> Result<Program, SourceError> {
    if prepared.expressions.iter().any(is_async_invocation) {
        let (program, _) =
            graph_generated_program(prepared, prepared.capture_cache_directory.as_deref())?;
        return Ok(program);
    }
    parse_prepared_program_items(prepared, true)
}

pub(crate) struct PreparedProgramSyntax {
    contract_checks: bool,
    graph_dependency_context: String,
    pub(crate) bundles: syntax_bundle::Bundles,
    pub(crate) capture_cache_directory: Option<PathBuf>,
    pub(crate) root_source: String,
    pub(crate) expressions: Vec<SpannedExpr>,
    pub(crate) source_files: Vec<SourceFile>,
    generated_source_invocations: HashMap<u32, Span>,
    pub(crate) dependency_context: String,
    pub(crate) generator_origins: generator::Origins,
    generation_requirements: Vec<crate::generator_provenance::Requirement>,
    pub(crate) async_copy_types: HashSet<String>,
    pub(crate) async_types: async_types::AsyncTypeEnvironment,
    pub(crate) worker_functions: HashMap<String, Function>,
}

pub(crate) fn prepare_program_syntax(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<PreparedProgramSyntax, SourceError> {
    if let Some(value) = config.values.get("async-lowering") {
        if value != "graph" {
            return Err(format!("unknown async-lowering '{value}'; expected graph").into());
        }
    }
    let (mut loaded, mut source_files) =
        load_imports_with_sources(source, base, source_path, config)?;
    let visibility = crate::library::check_generators(&loaded, &source_files)?;
    let qualified = crate::library::qualify(&mut loaded, &visibility, &source_files)?;
    let dependency_context = generator_dependency_context(&loaded, config);
    let mut bundles = syntax_bundle::Bundles::default();
    let loaded = bundles
        .expand(loaded, false)
        .map_err(|error| error.attach(&source_files))?;
    let mut generator_origins = generator::Origins::default();
    generator_origins.qualified = qualified;
    generator_origins.visibility = Some(visibility);
    generator_origins.source_paths = source_files.iter().map(|file| file.path.clone()).collect();
    // Imports may prefix the bodies of library generators. Authorize only the
    // original shipped declaration, never a path or a transformed name alone.
    for expression in &loaded {
        if !matches!(&expression.expr, Expr::List(items)
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#gn")
            && matches!(items.get(1), Some(Expr::Symbol(name)) if name.starts_with('#')))
        {
            continue;
        }
        if let Some(source) = source_files
            .get(expression.span.source_id as usize)
            .and_then(|file| file.source.get(expression.span.start..expression.span.end))
        {
            if let Ok(forms) = parse(source) {
                if forms.len() == 1 && standard_library::is_generator_declaration(&forms[0].expr) {
                    generator_origins
                        .standard_declarations
                        .insert(expression.span);
                }
            }
        }
    }
    let (expanded, _) = generator::expand_with_origins(
        loaded,
        cache_directory,
        &dependency_context,
        &mut generator_origins,
    )
    .map_err(|error| attach_generator_source(error, &source_files))?;
    let mut generated_source_invocations = HashMap::new();
    for (file, origin) in &generator_origins.generated_sources {
        generated_source_invocations.insert(source_files.len() as u32, *origin);
        source_files.push(file.clone());
    }
    let expressions = expand_cfg_forms(expanded, config)
        .map_err(|error| attach_generator_source(error, &source_files))?;
    // A parser-backed builtin may be emitted by a user generator and also be
    // called directly. Canonicalize literal arguments before deduplicating so
    // both routes compile one definition and retain every invocation origin.
    let mut builtin_invocations = HashMap::<(String, String, String), String>::new();
    let mut unique = Vec::with_capacity(expressions.len());
    for expression in expressions {
        if matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Generate)))
        {
            let normalized =
                normalize_builtin_generator_invocation(&expression.expr).map_err(|message| {
                    let span =
                        reserved_declaration_span(&expression, &message).unwrap_or(expression.span);
                    attach_span_to_source_error_kind(
                        message,
                        span,
                        &source_files,
                        "generator error: ",
                    )
                })?;
            let canonical = expression_source(&normalized)?;
            let original = expression_source(&expression.expr)?;
            let instance = generator_origins.expansion_context(expression.span);
            let identity = (
                instance,
                canonical,
                generator_origins.authority_signature(&expression),
            );
            if let Some(retained) = builtin_invocations.get(&identity) {
                if retained != &original {
                    generator_origins
                        .generation
                        .rewrite_builtin(&original, retained);
                    if let Some(origins) = generator_origins.builtins.remove(&original) {
                        generator_origins
                            .builtins
                            .entry(retained.clone())
                            .or_default()
                            .extend(origins);
                    }
                }
                continue;
            }
            builtin_invocations.insert(identity, original);
        }
        unique.push(expression);
    }
    let mut expressions = unique;
    // Contributions and syntax bundles disappear during preprocessing. Retain
    // their exact generated trees and origins before merging/expanding them so
    // navigation can still identify variant and bundle declaration tokens.
    for expression in &mut expressions {
        if expression.children.is_empty()
            && matches!(&expression.expr, Expr::List(parts)
                if matches!(parts.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#enum-contribute" | "#syntax")))
        {
            let origin = expression.span;
            let text = expression_source(&expression.expr)?;
            let mut parsed = parse(&text)?;
            let source_id = u32::try_from(source_files.len()).map_err(|_| {
                "too many source files while tracking enum contributions".to_owned()
            })?;
            let mut tree = parsed.remove(0);
            set_source_id(&mut tree, source_id);
            let path = source_files.get(origin.source_id as usize).map_or_else(
                || "<source>".to_owned(),
                |file| file.path.display().to_string(),
            );
            source_files.push(SourceFile {
                file_scope: None,
                path: format!("<generated from {path}:{}:{}>", origin.line, origin.column).into(),
                source: text,
            });
            generated_source_invocations.insert(source_id, origin);
            *expression = tree;
        }
    }
    crate::library::check_contributions(
        &expressions,
        &source_files,
        &generated_source_invocations,
        &generator_origins.definitions,
    )?;
    let mut expressions = crate::distributed_enum::merge(expressions)
        .map_err(|error| attach_generator_source(error, &source_files))?;
    let invocation_keys = expressions.iter().map(|form| {
        if matches!(&form.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Generate))) {
            expression_source(&form.expr).map(Some)
        } else { Ok(None) }
    }).collect::<Result<Vec<_>, String>>()?;
    let declaration_keys = expressions
        .iter()
        .map(|form| {
            fn locations<'a>(
                node: &'a SpannedExpr,
                wanted: &HashSet<&str>,
                found: &mut HashMap<&'a str, Span>,
            ) {
                if found.len() == wanted.len() {
                    return;
                }
                if let Expr::Symbol(name) = &node.expr {
                    if wanted.contains(name.as_str()) {
                        found.entry(name).or_insert(node.span);
                    }
                }
                for child in &node.children {
                    locations(child, wanted, found);
                }
            }
            let names = crate::generator_provenance::declared_names(&form.expr);
            let wanted = names.iter().copied().collect::<HashSet<_>>();
            let mut found = HashMap::new();
            locations(form, &wanted, &mut found);
            names
                .into_iter()
                .map(|name| {
                    let mut source = found.get(name).copied().unwrap_or(form.span).source_id;
                    while let Some(origin) = generated_source_invocations.get(&source) {
                        source = origin.source_id;
                    }
                    (source, name.to_owned())
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    crate::file_access::resolve(
        &mut expressions,
        &mut source_files,
        &generated_source_invocations,
        &generator_origins.definitions,
        config,
    )
    .map_err(|error| error.attach(&source_files))?;
    let resolved_declarations =
        expressions
            .iter()
            .zip(declaration_keys)
            .flat_map(|(form, names)| {
                names
                    .into_iter()
                    .zip(crate::generator_provenance::declared_names(&form.expr))
                    .map(|((source, old), resolved)| (source, old, resolved.to_owned()))
            });
    generator_origins
        .generation
        .resolve_declarations(resolved_declarations);
    // File resolution changes literal invocation identities. Keep provenance,
    // cache origins and generated-file lookup indexed by that same spelling.
    for (form, old) in expressions.iter().zip(invocation_keys) {
        if let Some(old) = old {
            let resolved = expression_source(&form.expr)?;
            if resolved != old {
                generator_origins
                    .generation
                    .rewrite_builtin(&old, &resolved);
                if let Some(origins) = generator_origins.builtins.remove(&old) {
                    generator_origins
                        .builtins
                        .entry(resolved)
                        .or_default()
                        .extend(origins);
                }
            }
        }
    }
    let (expressions, generation_requirements) = crate::generator_provenance::extract(expressions)
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
            let declaration =
                super::async_interfaces::protocol_declaration(&invocation).map_err(|message| {
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
                children: vec![].into(),
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
            if matches!(&form.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Generate))) {
                expression_source(&form.expr).map(Some)
            } else {
                Ok(None)
            }
        })
        .collect::<Result<Vec<_>, String>>()?;
    crate::library::check_bundle_uses(
        &with_protocols,
        &bundles.definitions,
        &source_files,
        &generated_source_invocations,
        &generator_origins.definitions,
    )?;
    let expressions = bundles
        .expand_with_provenance(
            with_protocols,
            &mut source_files,
            &mut generator_origins.definitions,
            &mut generated_source_invocations,
        )
        .map_err(|error| error.attach(&source_files))?;
    for (form, key) in expressions.iter().zip(builtin_keys) {
        if let Some(key) = key {
            let rewritten = expression_source(&form.expr)?;
            if rewritten != key {
                generator_origins
                    .generation
                    .rewrite_builtin(&key, &rewritten);
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
            if matches!(items.first(), Some(Expr::Generate))
            && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "#optional" | "#result" | "#array")))
    });
    let async_copy_types = if needs_copy_types {
        copy_type_names(&expressions)
    } else {
        HashSet::new()
    };
    let async_types = if needs_async {
        async_type_environment(&expressions)
    } else {
        async_types::AsyncTypeEnvironment::default()
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
        contract_checks: config
            .values
            .get("contracts")
            .is_some_and(|v| matches!(v.as_str(), "check" | "test")),
        graph_dependency_context: {
            // Current witnesses retain spans; artifact identity retains only
            // semantic dependencies and configuration, independent of location.
            let mut settings = config.values.iter().collect::<Vec<_>>();
            settings.sort();
            let syntax = expressions
                .iter()
                .map(|node| expression_source(&node.expr))
                .collect::<Result<Vec<_>, _>>()?
                .join("\n");
            let contexts = expressions
                .iter()
                .filter(|node| is_async_invocation(node))
                .map(|node| {
                    let definition = crate::generator_authority::source_context(
                        node.span,
                        &generator_origins.definitions,
                    )
                    .unwrap_or(node.span);
                    generator_origins.context_header("#async-fn", definition, node.span)
                })
                .collect::<Vec<_>>()
                .join("\n");
            format!(
                "cfg={settings:?}\nsyntax={:032x}\ncontexts={:032x}",
                generator::stable_hash(syntax.as_bytes()),
                generator::stable_hash(contexts.as_bytes())
            )
        },
        bundles,
        capture_cache_directory: cache_directory.map(Path::to_path_buf),
        root_source: source.to_owned(),
        expressions,
        source_files,
        generated_source_invocations,
        dependency_context,
        generator_origins,
        generation_requirements,
        async_copy_types,
        async_types,
        worker_functions,
    })
}

/// Declaration input for original-body planning. Async interfaces live in an
/// explicit deferred registry, not invented executable/extern declarations.
/// Ordinary bodies are parsed but stay unnormalized until layout completion;
/// the planner checks only the source models attached to this context.
pub(crate) fn parse_prepared_async_declarations(
    prepared: &PreparedProgramSyntax,
) -> Result<Program, SourceError> {
    parse_prepared_program_items(prepared, false)
}

pub(crate) fn parse_prepared_program_items(
    prepared: &PreparedProgramSyntax,
    expand_async: bool,
) -> Result<Program, SourceError> {
    let expressions = prepared.expressions.clone();
    let mut source_files = prepared.source_files.clone();
    let async_copy_types = &prepared.async_copy_types;
    let mut items = Vec::with_capacity(expressions.len());
    let mut statement_spans = HashMap::new();
    let mut statement_expressions = HashMap::new();
    let mut declaration_spans = HashMap::new();
    let mut declaration_expressions = HashMap::new();
    let mut declaration_occurrences: HashMap<String, Vec<SourceExpression>> = HashMap::new();
    let mut generated_source_invocations = prepared.generated_source_invocations.clone();
    let mut generated_definition_contexts = prepared.generator_origins.definitions.clone();
    let mut async_functions = Vec::new();
    let worker_functions = &prepared.worker_functions;
    for mut expression in expressions {
        if matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#alias"))
        {
            continue;
        }
        if matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#export"))
        {
            let file = &source_files[expression.span.source_id as usize];
            let original = file
                .source
                .get(expression.span.start..expression.span.end)
                .unwrap_or("");
            let literal = parse(original).ok().is_some_and(|forms| forms.len() == 1 && matches!(&forms[0].expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#export")));
            if file.path.file_name().is_none_or(|name| name != "lib.lim") || !literal {
                return Err(SourceError::from(
                    "#export must be literal source in lib.lim, not generated code",
                )
                .at(expression.span)
                .attach(&source_files));
            }
            continue;
        }
        if !expand_async && is_async_invocation(&expression) {
            continue;
        }
        if is_async_invocation(&expression) {
            return Err(SourceError::new(
                "async invocations require graph expansion",
                DiagnosticCode::Type,
            )
            .at(expression.span)
            .attach(&source_files));
        }
        let original_async = async_source::Source::from_invocation(&expression)?;
        validate_primitive_spelling(&expression).map_err(|(message, span)| {
            attach_span_to_source_error_kind(message, span, &source_files, "parse error: ")
        })?;
        validate_prefixed_forms(&expression.expr).map_err(|error| {
            let span = reserved_declaration_span(&expression, &error).unwrap_or(expression.span);
            attach_span_to_source_error_kind(error, span, &source_files, "parse error: ")
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
            expression.children.is_empty() && invocation_text.starts_with("(#generate ");
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
                file_scope: None,
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
        let source_expression = SourceExpression::from(expression);
        let mut expression = normalize_keywords(normalized_invocation.clone());
        normalize_match_cases_expr(&mut expression);
        let mut generated_declarations = HashMap::new();
        if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::Generate)) {
                let kind = forms.get(1).and_then(|form| match form {
                    Expr::Symbol(kind) => Some(kind.as_str()),
                    _ => None,
                });
                if matches!(
                    kind,
                    Some(
                        "#thread-spawn"
                            | "#optional"
                            | "#array"
                            | "#result"
                            | "#vec"
                            | "#vec-alloc"
                            | "#vec-sort"
                    )
                ) {
                    let generated_text = kind.and_then(|kind| {
                        materialize_builtin_generated_source(
                            kind,
                            forms,
                            &worker_functions,
                            &async_copy_types,
                        )
                        .ok()
                    });
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
                        let generated_text = contextual_generated_source(
                            prepared,
                            &source_expression,
                            &generated_text,
                        );
                        let mut generated_forms = parse(&generated_text)?;
                        generated_forms
                            .retain(|form| !crate::generator_authority::is_header(&form.expr));
                        for generated_form in &mut generated_forms {
                            set_source_id(generated_form, source_id);
                            normalize_match_case_forms(generated_form)
                                .map_err(|(error, _)| error)?;
                            crate::generator_authority::transfer_builtin(
                                &source_expression,
                                generated_form,
                                &mut generated_definition_contexts,
                            );
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
                            file_scope: None,
                            path: PathBuf::from(source_path),
                            source: generated_text,
                        });
                        generated_source_invocations.insert(source_id, form_span);
                    }
                }
            }
        }
        let parsed_items = if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::Generate)) {
                parse_generated_items_with_copy_types(forms, &async_copy_types).map_err(
                    |error| {
                        attach_span_to_source_error_kind(
                            format!(
                                "{error} while expanding generated declaration {}",
                                expression_source(&expression).unwrap_or_else(|_| "<?>".into())
                            ),
                            form_span,
                            &source_files,
                            "generator error: ",
                        )
                    },
                )?
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
                let expression = generated_declarations.get(&name).map_or_else(
                    || source_expression.clone(),
                    |generated| SourceExpression::from(generated.clone()),
                );
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
    validate_syntax_bundle_declarations(
        &items,
        &declaration_spans,
        &prepared.bundles,
        &source_files,
    )?;
    let runtime_items = items.len();
    if !expand_async {
        for invocation in prepared
            .expressions
            .iter()
            .filter(|form| is_async_invocation(form))
        {
            let normalized = normalize_builtin_generator_invocation(&invocation.expr)?;
            items.push(super::async_interfaces::poll_pattern_declaration(
                &normalized,
            )?);
        }
    }
    crate::let_else::normalize(
        &mut items,
        &mut statement_spans,
        &mut statement_expressions,
        &mut declaration_expressions,
        &mut declaration_occurrences,
        !expand_async,
    )
    .map_err(|error| error.attach(&source_files))?;
    items.truncate(runtime_items);
    rename_shadowed_locals(
        &mut items,
        &statement_spans,
        &declaration_spans,
        &source_files,
        &prepared.bundles.definitions,
    )?;
    synthesize_thread_join_results(&mut items, &declaration_spans, &source_files)?;
    items.extend(crate::contracts::refinement_aliases(
        &declaration_expressions,
    )?);
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
        normalize_aggregate_literals(
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
        generated_definition_contexts,
        syntax_bundle_uses: prepared.bundles.uses.clone(),
        contracts: crate::contracts::Metadata::default(),
        generator_validation: None,
    };
    if expand_async {
        crate::contracts::prepare(&mut program, prepared.contract_checks)?;
    } else {
        program.contracts.instrumented = prepared.contract_checks;
        crate::contracts::erase_planning(&mut program)?;
    }
    async_source::attach_validation(&mut program, &async_functions);
    if expand_async {
        crate::file_access::validate(&program)?;
    }
    if expand_async {
        crate::call_graph::lower(&mut program)?;
    }
    if expand_async {
        validate_generation_requirements(prepared, &[])?;
    }
    if !program.contracts.originals.is_empty() {
        program.contracts.lowered_items = program.items.clone();
    }
    Ok(program)
}

/// Check generation contracts after expansion; these checks never schedule it.
fn validate_generation_requirements(
    prepared: &PreparedProgramSyntax,
    async_output: &[super::async_emit::Generated],
) -> Result<(), SourceError> {
    if prepared.generation_requirements.is_empty() {
        return Ok(());
    }
    let mut registry = prepared.generator_origins.generation.clone();
    let mut async_output = async_output.iter();
    for expression in &prepared.expressions {
        if !matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Generate)))
        {
            continue;
        }
        let source: std::borrow::Cow<'_, str> = if is_async_invocation(expression) {
            std::borrow::Cow::Borrowed(
                &async_output
                    .next()
                    .ok_or_else(|| {
                        SourceError::new(
                            "missing async generator output while validating provenance",
                            DiagnosticCode::Generator,
                        )
                        .at(expression.span)
                    })?
                    .source,
            )
        } else {
            let invocation = normalize_builtin_generator_invocation(&expression.expr)?;
            let Expr::List(forms) = normalize_keywords(invocation) else {
                unreachable!()
            };
            let kind = expect_symbol(forms.get(1), "generated declaration name")?;
            if !matches!(
                kind,
                "#thread-spawn"
                    | "#optional"
                    | "#result"
                    | "#array"
                    | "#vec"
                    | "#vec-alloc"
                    | "#vec-sort"
            ) {
                continue;
            }
            std::borrow::Cow::Owned(materialize_builtin_generated_source(
                kind,
                &forms,
                &prepared.worker_functions,
                &prepared.async_copy_types,
            )?)
        };
        registry.record_builtin_output(&expression.expr, &parse(&source)?)?;
    }
    registry
        .validate(&prepared.generation_requirements)
        .map_err(|error| error.attach(&prepared.source_files))
}

pub(crate) fn write_generated_sources_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    directory: &Path,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<(), SourceError> {
    let generated_cache = cache_directory
        .map(Path::to_path_buf)
        .unwrap_or_else(|| directory.join("cache"));
    let prepared =
        prepare_program_syntax(source, base, source_path, config, Some(&generated_cache))?;
    write_prepared_generated_sources(&prepared, directory, cache_directory)
}

pub(crate) fn write_prepared_generated_sources(
    prepared: &PreparedProgramSyntax,
    directory: &Path,
    cache_directory: Option<&Path>,
) -> Result<(), SourceError> {
    write_prepared_expanded_sources(prepared, directory, cache_directory, None)
}

pub(crate) fn write_prepared_expanded_sources(
    prepared: &PreparedProgramSyntax,
    directory: &Path,
    cache_directory: Option<&Path>,
    graph_output: Option<&[super::async_emit::Generated]>,
) -> Result<(), SourceError> {
    write_prepared_generated_sources_reusing_graph(
        prepared,
        directory,
        cache_directory,
        graph_output,
    )
}

fn record_generated_artifact(
    prepared: &PreparedProgramSyntax,
    expression: &SpannedExpr,
    directory: &Path,
    key: &str,
) -> Result<(), String> {
    if !crate::generated_lookup::enabled() {
        return Ok(());
    }
    let invocation = expression_source(&expression.expr)?;
    let spans = prepared.generator_origins.builtins.get(&invocation);
    let spans = spans
        .map(Vec::as_slice)
        .unwrap_or(std::slice::from_ref(&expression.span));
    let path = generator::cached_generated_source_path(directory, key);
    let Expr::List(items) = &expression.expr else {
        return Err("generated artifact requires an invocation".into());
    };
    let Some(Expr::Symbol(name)) = items.get(1) else {
        return Err("generated artifact requires a generator name".into());
    };
    for &span in spans {
        let nested = prepared
            .generator_origins
            .source_invocation_names
            .get(&span)
            .is_none_or(|caller| caller != name);
        crate::generated_lookup::record(
            span,
            &prepared.generator_origins.source_paths,
            &path,
            name,
            nested,
        );
    }
    Ok(())
}

fn write_prepared_generated_sources_reusing_graph(
    prepared: &PreparedProgramSyntax,
    directory: &Path,
    cache_directory: Option<&Path>,
    retained_graph_output: Option<&[super::async_emit::Generated]>,
) -> Result<(), SourceError> {
    let expanded = &prepared.expressions;
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
    let graph_output =
        if retained_graph_output.is_none() && expanded.iter().any(is_async_invocation) {
            graph_generated_program(prepared, Some(&generated_cache))?.1
        } else {
            Vec::new()
        };
    let mut graph_output = retained_graph_output.unwrap_or(&graph_output).iter();
    let graph_key_context = expanded
        .iter()
        .any(is_async_invocation)
        .then(|| graph_source_key_context(prepared));
    let mut written_builtin_keys = HashSet::new();
    for expression in expanded {
        if !matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Generate)))
        {
            continue;
        }
        let invocation = expression_source(&expression.expr)?;
        if is_async_invocation(expression) {
            // The planner and this loop both preserve invocation order, including
            // generator-produced forms whose original trees needed reparsing.
            let generated = graph_output.next().ok_or_else(|| {
                SourceError::new(
                    "missing graph output for async invocation",
                    DiagnosticCode::Type,
                )
                .at(expression.span)
                .attach(&prepared.source_files)
            })?;
            let key =
                graph_source_key(prepared, graph_key_context.as_deref().unwrap(), expression)?;
            let origins = builtin_origins
                .get(&invocation)
                .cloned()
                .unwrap_or_else(|| vec![location(expression.span)]);
            generator::cached_generated_source_with_origins(
                &generated_cache,
                &key,
                &origins,
                || Ok(generated.source.clone()),
            )?;
            record_generated_artifact(prepared, expression, &generated_cache, &key)?;
            continue;
        }
        let original = normalize_builtin_generator_invocation(&expression.expr)?;
        let Expr::List(forms) = normalize_keywords(original.clone()) else {
            continue;
        };
        if !matches!(forms.first(), Some(Expr::Generate)) {
            continue;
        }
        let kind = expect_symbol(forms.get(1), "generated declaration name")?;
        if !matches!(
            kind,
            "#thread-spawn"
                | "#vec"
                | "#vec-alloc"
                | "#vec-sort"
                | "#optional"
                | "#result"
                | "#array"
        ) {
            continue;
        }
        let context = contextual_generated_source(prepared, expression, "");
        let context = context.trim();
        let key = format!(
            "lim-inspectable-generated-source-v8\ncompiler={}\nimplementation={}\ndependency-context={}\nasync-copy-types={}\nasync-type-environment={}\ninvocation={invocation}\ncontext={context}",
            env!("CARGO_PKG_VERSION"),
            env!("LIM_BUILD_FINGERPRINT"),
            dependency_context,
            async_copy_type_identity(&copy_types),
            async_type_environment_identity(&async_types),
        );
        if !written_builtin_keys.insert(key.clone()) {
            continue;
        }
        let origins = builtin_origins
            .get(&invocation)
            .cloned()
            .unwrap_or_else(|| vec![location(expression.span)]);
        generator::cached_generated_source_with_origins(&generated_cache, &key, &origins, || {
            materialize_builtin_generated_source(&kind, &forms, &worker_functions, copy_types)
                .map(|source| contextual_generated_source(prepared, expression, &source))
        })?;
        record_generated_artifact(prepared, expression, &generated_cache, &key)?;
    }
    Ok(())
}

#[cfg(test)]
mod async_migration_tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    const CONTEXT: &str = "
      (#enum Child (#linear) ((Child.Start #u64) (Child.Resume #u64)))
      (#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64)))
      (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
        (#return (#match task
          (#case (Child.Start value) (ChildPoll.ChildPending (Child.Resume value)))
          (#case (Child.Resume value) (ChildPoll.ChildReady value)))))";

    fn source(body: &str) -> String {
        format!(
            "{CONTEXT}
          (#generate #async-fn (: protocol WorkAwait : waker #u64 : function
            (#fn work (: seed #u64) #u64 {body})))"
        )
    }

    fn syntax(text: &str, cache: Option<&Path>) -> PreparedProgramSyntax {
        prepare_program_syntax(text, Path::new("."), None, &CompileConfig::default(), cache)
            .unwrap()
    }

    #[test]
    fn shared_graph_key_context_preserves_complete_per_invocation_identity() {
        let text = format!(
            "{}\n{}",
            source("(#return seed)"),
            source("(#return (#u64::add-wrap seed 1u64))")
                .replace(CONTEXT, "")
                .replace("WorkAwait", "OtherAwait")
                .replace("#fn work", "#fn other")
        );
        let mut prepared = syntax(&text, None);
        let context = graph_source_key_context(&prepared);
        let invocations = prepared
            .expressions
            .iter()
            .filter(|node| is_async_invocation(node))
            .collect::<Vec<_>>();
        assert_eq!(invocations.len(), 2);
        let mut keys = Vec::new();
        for invocation in invocations {
            // The shared environment and each invocation's explicit module
            // context must both participate in the source-cache identity.
            let expected = format!("lim-inspectable-async-graph-v4\ncompiler={}\nimplementation={}\ndependency-context={}\ncopy-types={}\ntype-environment={}\ninvocation={}\ncontext={}",
                env!("CARGO_PKG_VERSION"), env!("LIM_BUILD_FINGERPRINT"), prepared.graph_dependency_context,
                async_copy_type_identity(&prepared.async_copy_types), async_type_environment_identity(&prepared.async_types), expression_source(&invocation.expr).unwrap(), contextual_generated_source(&prepared, invocation, "").trim());
            let actual = graph_source_key(&prepared, &context, invocation).unwrap();
            assert_eq!(actual, expected);
            keys.push(actual);
        }
        assert_ne!(keys[0], keys[1]);
        prepared
            .graph_dependency_context
            .push_str("changed dependency");
        assert_ne!(graph_source_key_context(&prepared), context);
        let dependency_context = graph_source_key_context(&prepared);
        prepared.async_copy_types.insert("NewCopyType".into());
        assert_ne!(graph_source_key_context(&prepared), dependency_context);
        let copy_context = graph_source_key_context(&prepared);
        prepared
            .async_types
            .aliases
            .insert("NewAlias".into(), "#u64".into());
        assert_ne!(graph_source_key_context(&prepared), copy_context);
    }

    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "lim-async-migration-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn graph_source_publication_checks_original_and_emitted_once() {
        let scratch = Scratch::new();
        let text =
            source("(#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)))");
        typecheck::SEMANTIC_PASSES.with(|count| count.set(0));
        write_generated_sources_in_directory(
            &text,
            Path::new("."),
            None,
            &scratch.0,
            &CompileConfig::default(),
            Some(&scratch.0),
        )
        .unwrap();
        typecheck::SEMANTIC_PASSES.with(|count| {
            assert_eq!(
                count.get(),
                2,
                "check the original source and ordinary emitted program once each"
            )
        });
    }

    #[test]
    #[ignore = "manual source-publication benchmark; run in release with --ignored --nocapture"]
    fn graph_source_publication_cold_timing() {
        let text =
            source("(#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)))");
        let mut walls = Vec::new();
        let mut passes = Vec::new();
        for _ in 0..8 {
            let scratch = Scratch::new();
            typecheck::SEMANTIC_PASSES.with(|count| count.set(0));
            let started = std::time::Instant::now();
            write_generated_sources_in_directory(
                &text,
                Path::new("."),
                None,
                &scratch.0,
                &CompileConfig::default(),
                Some(&scratch.0),
            )
            .unwrap();
            walls.push(started.elapsed().as_secs_f64() * 1000.0);
            passes.push(typecheck::SEMANTIC_PASSES.with(|count| count.get()));
            assert_eq!(
                fs::read_dir(generator::generated_source_directory(&scratch.0))
                    .unwrap()
                    .count(),
                1
            );
        }
        walls.remove(0); // Warm executable paths, not the measured source caches.
        passes.remove(0);
        walls.sort_by(f64::total_cmp);
        println!("cold inspectable graph source publication: median={:.3}ms samples={} semantic_passes={passes:?}; includes validation and cache writes, excludes backend emission/linking", walls[walls.len()/2], walls.len());
    }

    #[test]
    fn graph_owned_expansion_retains_validation_and_materializes_without_rechecking() {
        let scratch = Scratch::new();
        let text =
            source("(#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)))");
        let mut config = CompileConfig::default();
        config.set("async-lowering", "graph");
        let prepared =
            prepare_program_syntax(&text, Path::new("."), None, &config, Some(&scratch.0)).unwrap();
        for _ in 0..2 {
            let (mut owned, generated) =
                expand_prepared_owned_program(&prepared, &config, "check").unwrap();
            typecheck::SEMANTIC_PASSES.with(|passes| passes.set(0));
            let timing = crate::TimingSession::start();
            owned.validate().unwrap();
            write_prepared_expanded_sources(
                &prepared,
                &scratch.0,
                Some(&scratch.0),
                generated.as_deref(),
            )
            .unwrap();
            let events = timing.finish();
            typecheck::SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 0));
            assert!(
                !events
                    .iter()
                    .any(|event| event.stage == "semantic.referent_contracts"),
                "{events:?}"
            );
            owned.with_checked(|checked| {
                assert!(checked.program().generator_validation.is_some());
                crate::codegen::generate_checked_assembly(
                    checked,
                    crate::TargetDescription::X86_64_SYSTEM_V,
                )
                .unwrap();
            });
        }
    }

    #[test]
    fn graph_route_checks_and_publishes_the_same_ordinary_output_with_cache_and_headers() {
        let scratch = Scratch::new();
        let text =
            source("(#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)))");
        let prepared = syntax(&text, Some(&scratch.0));
        let emissions = super::super::async_emit::EMISSION_COUNT.with(|count| count.get());
        let program = expand_prepared_program(&prepared).unwrap();
        assert_eq!(
            super::super::async_emit::EMISSION_COUNT.with(|count| count.get()),
            emissions + 1
        );
        assert!(program.generator_validation.is_some());
        let graph_file = program
            .source_files
            .iter()
            .find(|file| file.path.to_string_lossy().starts_with("<async graph "))
            .unwrap();
        assert!(graph_file.source.contains("(#loop"));
        assert!(!graph_file.source.contains("poll-resume-"));
        for _ in 0..2 {
            write_prepared_generated_sources(&prepared, &scratch.0, Some(&scratch.0)).unwrap();
            let cached = expand_prepared_program(&prepared).unwrap();
            assert_eq!(
                cached.source_files.last().unwrap().source,
                graph_file.source
            );
        }
        assert_eq!(
            super::super::async_emit::EMISSION_COUNT.with(|count| count.get()),
            emissions + 1,
            "warm compile and publication hits must not invoke the emitter"
        );
        let sources = fs::read_dir(generator::generated_source_directory(&scratch.0))
            .unwrap()
            .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(sources.len(), 1);
        assert!(sources[0].starts_with("; Generated from:\n"));
        assert!(sources[0].ends_with(&graph_file.source));
        assert!(parse_program(&sources[0])
            .unwrap_err()
            .contains("compiler-owned"));
        let ordinary = parse_program(&format!(
            "{CONTEXT}\n{}",
            crate::generator_authority::without_header(&sources[0])
        ))
        .unwrap();
        typecheck::CheckedProgram::validate_with_span(&ordinary).unwrap();
        let keys = fs::read_dir(&scratch.0)
            .unwrap()
            .filter_map(|entry| {
                let path = entry.unwrap().path();
                (path.extension().and_then(|ext| ext.to_str()) == Some("key"))
                    .then(|| fs::read_to_string(path).unwrap())
            })
            .collect::<Vec<_>>();
        assert!(keys
            .iter()
            .any(|key| key.contains("lim-inspectable-async-graph-v4")));
        assert!(!keys.iter().any(|key| key.contains("async-capture-plan=")));
    }

    #[test]
    fn graph_cache_separates_files_and_reuses_locations_within_each_file() {
        let scratch = Scratch::new();
        let text = format!("{CONTEXT}
          (#struct Source (#linear) (: amount #u64))
          (#fn make (: amount #u64) Source (#return (#struct-literal Source (: amount amount))))
          (#fn consume (: owner Source : amount #u64) #u64
            (#let result #u64 (#u64::add-wrap (#get owner amount) amount)) (#forget owner) (#return result))
          (#generate #async-fn-pinned (: protocol WorkAwait : waker #u64 : function
            (#fn work (: seed #u64) #u64 (#return (#call consume
              (: owner (#call make (: amount seed))
                 : amount (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 2u64))))))))");
        let count = super::super::async_emit::EMISSION_COUNT.with(|count| count.get());
        let mut bodies = Vec::new();
        for (name, padding) in [
            ("first.lim", ""),
            ("second.lim", "\n\n\n"),
            ("first.lim", "\n"),
        ] {
            let path = scratch.0.join(name);
            let prepared = prepare_program_syntax(
                &format!("{padding}{text}"),
                &scratch.0,
                Some(&path),
                &CompileConfig::default(),
                Some(&scratch.0),
            )
            .unwrap();
            let program = expand_prepared_program(&prepared).unwrap();
            let output = &program.source_files.last().unwrap().source;
            assert!(
                output.contains("Work::Frame::Cleanup::Source-expression-"),
                "{output}"
            );
            bodies.push(output[output.find("(#struct Work::Frame ").unwrap()..].to_owned());
        }
        assert_eq!(bodies[0], bodies[1]);
        assert_eq!(bodies[0], bodies[2]);
        assert_eq!(
            super::super::async_emit::EMISSION_COUNT.with(|count| count.get()),
            count + 2
        );
        let artifacts = fs::read_dir(generator::generated_source_directory(&scratch.0))
            .unwrap()
            .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(artifacts.len(), 2);
        assert!(artifacts
            .iter()
            .any(|text| text.contains("first.lim:") && !text.contains("second.lim:")));
        assert!(artifacts
            .iter()
            .any(|text| text.contains("second.lim:") && !text.contains("first.lim:")));
    }

    #[test]
    fn graph_cache_does_not_publish_fresh_output_before_complete_validation() {
        let scratch = Scratch::new();
        let text = format!(
            "{}\n(#fn main () #u64 (#return true))",
            source("(#return seed)")
        );
        let prepared = syntax(&text, Some(&scratch.0));
        assert!(expand_prepared_program(&prepared).is_err());
        assert!(!generator::generated_source_directory(&scratch.0).exists());
    }

    #[test]
    fn graph_frame_protocol_collisions_reject_fresh_and_cached_output() {
        let scratch = Scratch::new();
        let text =
            source("(#return seed)").replace(": protocol WorkAwait", ": protocol Work::Task");
        let prepared = syntax(&text, Some(&scratch.0));
        let error = expand_prepared_program(&prepared).unwrap_err();
        assert!(error
            .to_string()
            .contains("declaration 'Work::Task' conflicts with a syntax bundle"));
        assert!(error.diagnostic().span.is_some());
        assert!(!generator::generated_source_directory(&scratch.0).exists());

        // Model an artifact accepted by the former graph path: its syntax,
        // key and digest are valid, but its public frame shadows the protocol.
        let planning = super::super::async_prepare::prepare(&prepared).unwrap();
        let invocation = prepared
            .expressions
            .iter()
            .find(|node| is_async_invocation(node))
            .unwrap();
        let key =
            graph_source_key(&prepared, &graph_source_key_context(&prepared), invocation).unwrap();
        let origin = vec![graph_source_origin(&prepared, invocation.span)];
        let mut output =
            super::super::async_emit::generate_function(&planning, &planning.functions[0]).unwrap();
        let normalized = normalize_builtin_generator_invocation(&invocation.expr).unwrap();
        output.source.push_str(&format!(
            "\n{}\n",
            expression_source(
                &super::super::async_interfaces::protocol_declaration(&normalized).unwrap(),
            )
            .unwrap()
        ));
        generator::cached_generated_source_with_origins(&scratch.0, &key, &origin, || {
            Ok(contextual_generated_source(
                &prepared,
                invocation,
                &output.source,
            ))
        })
        .unwrap();
        let artifact = fs::read_dir(generator::generated_source_directory(&scratch.0))
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        let before = fs::read_to_string(&artifact).unwrap();
        let emissions = super::super::async_emit::EMISSION_COUNT.with(|count| count.get());
        let error = expand_prepared_program(&prepared).unwrap_err();
        assert!(error
            .to_string()
            .contains("declaration 'Work::Task' conflicts with a syntax bundle"));
        assert_eq!(
            super::super::async_emit::EMISSION_COUNT.with(|count| count.get()),
            emissions
        );
        assert_eq!(fs::read_to_string(&artifact).unwrap(), before);
    }

    #[test]
    fn graph_cache_corruption_fails_closed_without_emission_or_repair() {
        let scratch = Scratch::new();
        let text = source("(#return seed)");
        let prepared = syntax(&text, Some(&scratch.0));
        expand_prepared_program(&prepared).unwrap();
        let emissions = super::super::async_emit::EMISSION_COUNT.with(|count| count.get());
        let artifact = fs::read_dir(generator::generated_source_directory(&scratch.0))
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        // Even parseable corruption must not be accepted or silently repaired.
        let corrupt = format!("{}\n; tampered\n", fs::read_to_string(&artifact).unwrap());
        fs::write(&artifact, &corrupt).unwrap();
        let error = expand_prepared_program(&prepared).unwrap_err().to_string();
        assert!(error.contains("invalid async graph cache entry"), "{error}");
        assert_eq!(
            super::super::async_emit::EMISSION_COUNT.with(|count| count.get()),
            emissions
        );
        assert_eq!(fs::read_to_string(artifact).unwrap(), corrupt);
    }

    #[test]
    fn graph_route_never_falls_back_for_unsupported_local_or_scoped_borrows() {
        for (body, expected) in [
            (
                "(#let owner (#tuple #u64 #u64) (#tuple (#tuple #u64 #u64) seed 2u64))
              (#let view (#ref #u64) (#borrow (#get owner 0)))
              (#return (#u64::add-wrap (#deref view)
                (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 2u64))))",
                "local references surviving suspension require a pinned async frame",
            ),
            (
                "(#let owner #u64 seed)
                 (#return (#borrow owner
                   (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start 0u64))))",
                "local references surviving suspension require a pinned async frame",
            ),
        ] {
            let text = source(body);
            let prepared = syntax(&text, None);
            let error = expand_prepared_program(&prepared).err().unwrap();
            assert!(error.message.contains(expected), "{error}");
            assert!(error.span.is_some());
            let scratch = Scratch::new();
            let error = write_prepared_generated_sources(&prepared, &scratch.0, Some(&scratch.0))
                .unwrap_err();
            assert!(error.message.contains(expected), "{error}");
            assert_eq!(fs::read_dir(&scratch.0).unwrap().count(), 0);
        }
    }

    #[test]
    fn graph_route_accepts_checked_source_named_cancellation_dispatcher() {
        let text =
            source("(#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)))")
                .replace("#generate #async-fn", "#generate #async-fn-pinned")
                .replace(
                    ": function",
                    ": cancel (work-cancel ((await-0 cancel-child))) : function",
                );
        let text =
            format!("{text}\n(#fn cancel-child (: child Child) () (#forget child) (#return ()))");
        let prepared = syntax(&text, None);
        let program = expand_prepared_program(&prepared).unwrap();
        let output = &program.source_files.last().unwrap().source;
        assert!(
            output.contains("(#fn work-cancel ((task Work::Frame::Cleanup)) ()"),
            "{output}"
        );
        assert!(output.contains("Work::Frame::Cleanup::Await-0.Full"));
        typecheck::CheckedProgram::validate_with_span(&program).unwrap();
    }

    #[test]
    fn graph_route_preserves_exact_original_type_errors() {
        let text = source("(#let answer #u64 true) (#return answer)");
        let prepared = syntax(&text, None);
        let error = expand_prepared_program(&prepared).err().unwrap();
        assert_eq!(error.code, DiagnosticCode::Type);
        let span = error.span.unwrap();
        assert_eq!(&text[span.start..span.end], "true");
    }

    #[test]
    fn graph_route_runs_through_pending_and_ready_as_ordinary_native_code() {
        let scratch = Scratch::new();
        let text = format!(
            "{}
          (#fn main () #u64
            (#let waker #u64 0u64)
            (#let first Work::Poll (#call Work::poll
              (: task (#call work (: seed 40u64)) : waker (#borrow waker))))
            (#let-else (Work::Poll.Pending next) Work::Poll first (#unreachable))
            (#return (#match (#call Work::poll (: task next : waker (#borrow waker)))
              (#case (Work::Poll.Ready value) value)
              (#case (Work::Poll.Pending bad) (#block (#forget bad) (#unreachable))))))",
            source(
                "(#let answer #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)))
              (#return (#u64::add-wrap answer 2u64))"
            )
        );
        let prepared = syntax(&text, None);
        let program = expand_prepared_program(&prepared).unwrap();
        let assembly = crate::generate_assembly(&program).unwrap();
        let binary = scratch.0.join("graph-runtime");
        crate::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            crate::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let output = crate::test_process::spawn(
            std::process::Command::new(binary)
                .stdin(std::process::Stdio::null())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped()),
            std::time::Duration::from_secs(5),
        )
        .unwrap()
        .wait_with_output()
        .unwrap();
        assert_eq!(output.status.code(), Some(42), "{:?}", output.stderr);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
    }

    #[test]
    fn graph_route_handles_generator_produced_async_forms_and_multiple_outputs() {
        let text = format!(
            "{CONTEXT}
          (#gn produce () `((#generate #async-fn (: protocol WorkAwait : waker #u64 : function
            (#fn work (: seed #u64) #u64
              (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed))))))))
          (#generate produce)
          (#generate #async-fn (: protocol SecondAwait : waker #u64 : function
            (#fn second (: seed #u64) #u64
              (#return (#await Work::Task Work::Poll.Pending Work::Poll.Ready Work::poll
                (#call work (: seed seed)))))))"
        );
        let scratch = Scratch::new();
        let prepared = syntax(&text, Some(&scratch.0));
        let program = expand_prepared_program(&prepared).unwrap();
        assert_eq!(
            program
                .source_files
                .iter()
                .filter(|file| file.path.to_string_lossy().starts_with("<async graph "))
                .count(),
            2
        );
        write_prepared_generated_sources(&prepared, &scratch.0, Some(&scratch.0)).unwrap();
        assert_eq!(
            fs::read_dir(generator::generated_source_directory(&scratch.0))
                .unwrap()
                .map(|entry| fs::read_to_string(entry.unwrap().path()).unwrap())
                .filter(|source| source.contains("(#fn Work::poll ")
                    || source.contains("(#fn Second::poll "))
                .count(),
            2
        );
    }

    #[test]
    fn graph_route_still_requires_the_completed_ordinary_program_check() {
        let text = format!(
            "{}\n(#fn invalid-ordinary () #u64 (#return true))",
            source("(#return seed)")
        );
        let prepared = syntax(&text, None);
        let error = expand_prepared_program(&prepared).err().unwrap();
        assert_eq!(error.code, DiagnosticCode::Type);
        let span = error.span.unwrap();
        assert_eq!(&text[span.start..span.end], "true");
    }

    #[test]
    fn obsolete_per_state_cancellation_patterns_are_not_supported() {
        let text = format!(
            "{}
          (#fn cancel-frame (: task Work::frame-state) ()
            (#match task
              (#case (work-frame-start seed) (#forget seed))
              (#case (work-frame-await-0 seed child) (#block (#forget seed) (#forget child)))
              (#case work-frame-done ()))
            (#return ()))",
            source(
                "(#let answer #u64 (#await Child ChildPoll.ChildPending ChildPoll.ChildReady child-poll (Child.Start seed)))
              (#return (#u64::add-wrap answer seed))"
            )
            .replace("#generate #async-fn", "#generate #async-fn-pinned")
        );
        let prepared = syntax(&text, None);
        let error = expand_prepared_program(&prepared).err().unwrap();
        assert!(
            error
                .message
                .contains("undeclared type 'Work::frame-state'"),
            "{error}"
        );
        let span = error.span.unwrap();
        assert_eq!(&text[span.start..span.end], "Work::frame-state");
    }

    #[test]
    fn default_uses_graph_and_non_async_programs_do_not_create_validation_witnesses() {
        let prepared = syntax(&source("(#return seed)"), None);
        let default = expand_prepared_program(&prepared).unwrap();
        assert!(default
            .source_files
            .iter()
            .any(|file| file.path.to_string_lossy().starts_with("<async graph ")));
        let prepared = syntax("(#fn main () #u64 (#return 42u64))", None);
        let program = expand_prepared_program(&prepared).unwrap();
        assert!(program.generator_validation.is_none());
    }

    #[test]
    fn obsolete_async_route_is_not_a_public_compilation_mode() {
        let mut config = CompileConfig::default();
        config.set("async-lowering", "legacy");
        let error = prepare_program_syntax(
            "(#fn main () #u64 (#return 42u64))",
            Path::new("."),
            None,
            &config,
            None,
        )
        .err()
        .expect("the obsolete route must not be publicly selectable");
        assert!(
            error
                .message
                .contains("unknown async-lowering 'legacy'; expected graph"),
            "{error}"
        );
    }
}
