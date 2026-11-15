//! Editor information uses the navigation resolver's declaration identities.
//! Presentation reads authored spans instead of exposing compiler-private names.
use super::navigation::{Index, binding_parts};
use crate::{Expr, SourceFile, Span, SpannedExpr as Node, Type, editor::NavigationContext};

pub(crate) struct Signature {
    pub label: String,
    pub parameters: Vec<(String, String)>,
    pub contracts: Vec<String>,
}

fn symbol(node: &Node) -> Option<&str> {
    match &node.expr {
        Expr::Symbol(name) | Expr::Function(name) => Some(name),
        _ => None,
    }
}
fn head(node: &Node) -> &str {
    node.children
        .first()
        .and_then(symbol)
        .unwrap_or("")
        .trim_start_matches('#')
}
fn name_index(node: &Node) -> usize {
    if head(node) == "extern-fn" { 2 } else { 1 }
}
fn is_function(node: &Node) -> bool {
    matches!(
        head(node),
        "fn" | "unsafe-fn" | "extern-fn" | "thread-task-spawn" | "thread-task-join"
    )
}
fn files(context: &NavigationContext) -> &[SourceFile] {
    context
        .program
        .as_ref()
        .map_or(&context.files, |program| &program.source_files)
}
fn roots(context: &NavigationContext) -> impl Iterator<Item = &Node> {
    context
        .forms
        .iter()
        .chain(context.program.iter().flat_map(|program| {
            program
                .declaration_occurrences
                .values()
                .flat_map(|nodes| nodes.iter().map(|node| &**node))
        }))
}
fn source_text<'a>(context: &'a NavigationContext, node: &Node) -> Option<&'a str> {
    let text = files(context)
        .get(node.span.source_id as usize)?
        .source
        .get(node.span.start..node.span.end)?;
    (!text.is_empty()).then_some(text)
}
fn text(context: &NavigationContext, node: &Node) -> String {
    source_text(context, node)
        .map(str::to_owned)
        .or_else(|| crate::expression_source(&node.expr).ok())
        .unwrap_or_default()
}
fn typed(node: &Node) -> bool {
    crate::parse_type(Some(&crate::normalize_keywords(node.expr.clone()))).is_ok()
}
fn token(node: &Node, file: u32, byte: usize) -> Option<&Node> {
    if node.span.source_id != file || byte < node.span.start || byte >= node.span.end {
        return None;
    }
    node.children
        .iter()
        .find_map(|child| token(child, file, byte))
        .or_else(|| symbol(node).map(|_| node))
}
fn name_for_type(context: &NavigationContext, name: &str) -> String {
    context
        .program
        .as_ref()
        .and_then(|program| program.declaration_expressions.get(name))
        .and_then(|node| node.children.get(name_index(node)))
        .and_then(|node| source_text(context, node))
        .unwrap_or(name)
        .to_owned()
}
fn display_type(context: &NavigationContext, kind: &Type) -> String {
    // Keep the compiler's type printer, replacing only metadata-resolved names.
    fn authored(context: &NavigationContext, kind: &Type) -> Type {
        match kind {
            Type::Named(name) => Type::Named(name_for_type(context, name)),
            Type::Reference { mutable, target } => Type::Reference {
                mutable: *mutable,
                target: Box::new(authored(context, target)),
            },
            Type::PinnedReference { mutable, target } => Type::PinnedReference {
                mutable: *mutable,
                target: Box::new(authored(context, target)),
            },
            Type::RawPointer { mutable, target } => Type::RawPointer {
                mutable: *mutable,
                target: Box::new(authored(context, target)),
            },
            Type::PinOwned(target) => Type::PinOwned(Box::new(authored(context, target))),
            Type::PinShared(target) => Type::PinShared(Box::new(authored(context, target))),
            Type::Slice(target) => Type::Slice(Box::new(authored(context, target))),
            Type::MutableSlice(target) => Type::MutableSlice(Box::new(authored(context, target))),
            Type::Atomic(target) => Type::Atomic(Box::new(authored(context, target))),
            Type::Tuple(fields) => {
                Type::Tuple(fields.iter().map(|kind| authored(context, kind)).collect())
            }
            Type::Array(element, length) => {
                Type::Array(Box::new(authored(context, element)), *length)
            }
            _ => kind.clone(),
        }
    }
    crate::type_source(&authored(context, kind))
}
/// Match the resolver's declaration identity, not the spelling at the call or
/// in the authored form. Imported/private functions may share local names.
fn computed_requirements<'a>(
    context: &'a NavigationContext,
    node: &Node,
) -> Option<&'a crate::contracts::prerequisites::Requirements> {
    let program = context.program.as_ref()?;
    let target = node.children.get(name_index(node))?.span;
    let mut candidates = program.contracts.effective_requires.iter()
        .filter(|(name, _)| {
            program.declaration_expressions.get(*name).is_some_and(|source| {
                is_function(source)
                    && source.children.get(name_index(source))
                        .is_some_and(|name| name.span == target)
            })
        });
    let (_, requirements) = candidates.next()?;
    candidates.next().is_none().then_some(requirements)
}

fn predicate_text(context: &NavigationContext, expression: &Expr) -> String {
    fn authored(context: &NavigationContext, expression: &Expr) -> Expr {
        match expression {
            Expr::List(xs) => {
                if let Some(Expr::Function(name)) = xs.first() {
                    if let Some(function) = context
                        .program
                        .as_ref()
                        .and_then(|program| program.contracts.originals.get(name))
                    {
                        let arguments = function.parameters.iter().zip(xs.iter().skip(1))
                            .map(|(parameter, argument)| {
                                Expr::List(vec![
                                    Expr::Symbol(parameter.name.clone()),
                                    authored(context, argument),
                                ].into())
                            })
                            .collect::<Vec<_>>();
                        return Expr::List(
                            vec![
                                Expr::Symbol("#call".into()),
                                Expr::Symbol(name_for_type(context, name)),
                                Expr::List(arguments.into()),
                            ].into(),
                        );
                    }
                }
                Expr::List(
                    xs.iter().enumerate().map(|(index, expression)| {
                        if index == 0 {
                            if let Expr::Symbol(name) = expression {
                                return Expr::Symbol(
                                    crate::names::numeric_source(name).unwrap_or_else(|| {
                                        format!("#{}", name.trim_start_matches('#'))
                                    }),
                                );
                            }
                        }
                        authored(context, expression)
                    }).collect::<Vec<_>>().into(),
                )
            }
            Expr::Symbol(name) | Expr::Function(name) => {
                Expr::Symbol(name_for_type(context, name))
            }
            _ => expression.clone(),
        }
    }
    crate::expression_source(&authored(context, expression)).unwrap_or_default()
}

fn origin_location(context: &NavigationContext, span: Span) -> String {
    files(context).get(span.source_id as usize).map_or_else(
        || format!("{}:{}", span.line, span.column),
        |file| format!("{}:{}:{}", file.path.display(), span.line, span.column),
    )
}

fn computed_contracts(context: &NavigationContext, node: &Node) -> Vec<String> {
    let Some(requirements) = computed_requirements(context, node) else {
        return Vec::new();
    };
    if requirements.nodes.is_empty() {
        return Vec::new();
    }
    // Metadata is bounded separately by the checker. Keep editor output small
    // too, and show DAG edges once instead of enumerating dependency paths.
    const NODE_LIMIT: usize = 64;
    const ORIGIN_LIMIT: usize = 128;
    const TEXT_LIMIT: usize = 64 * 1024;
    const OMITTED: &str = "// Additional prerequisite information omitted (display limit).";
    let mut output = Vec::new();
    let mut bytes = 0;
    let mut append = |line: String| {
        if bytes + line.len() + 1 > TEXT_LIMIT - OMITTED.len() - 1 {
            false
        } else {
            bytes += line.len() + 1;
            output.push(line);
            true
        }
    };
    let mut numbers = vec![None; requirements.nodes.len()];
    let mut roots = vec![false; requirements.nodes.len()];
    for root in &requirements.roots {
        roots[root.node] = true;
    }
    append("// Computed requirements (prerequisites first)".into());
    let mut omitted = requirements.order.len() > NODE_LIMIT;
    for (index, &id) in requirements.order.iter().take(NODE_LIMIT).enumerate() {
        let kind = if roots[id] {
            "requirement root"
        } else {
            "inherited prerequisite"
        };
        let expression = predicate_text(context, &requirements.nodes[id].expression);
        if !append(format!("// [{}] {kind}\n(#requires {expression})", index + 1)) {
            omitted = true;
            break;
        }
        numbers[id] = Some(index + 1);
    }
    append("// Origin chains (shared obligations reuse their number)".into());
    let fallback = node.children[name_index(node)].span;
    let mut origins = 0;
    for root in &requirements.roots {
        if let Some(number) = numbers[root.node] {
            if origins >= ORIGIN_LIMIT
                || !append(format!(
                    "// root requirement -> [{number}] at {}{}",
                    origin_location(context, root.span.unwrap_or(fallback)),
                    if root.span.is_none() { " (signature constraint)" } else { "" },
                ))
            {
                omitted = true;
                break;
            }
            origins += 1;
        }
    }
    for &id in requirements.order.iter().take(NODE_LIMIT) {
        let Some(parent) = numbers[id] else {
            continue;
        };
        for prerequisite in &requirements.nodes[id].prerequisites {
            let Some(child) = numbers[prerequisite.node] else {
                continue;
            };
            let location = prerequisite.span
                .map(|span| format!(" at {}", origin_location(context, span)))
                .unwrap_or_default();
            if origins >= ORIGIN_LIMIT
                || !append(format!("// [{parent}] -> prerequisite [{child}]{location}"))
            {
                omitted = true;
                break;
            }
            origins += 1;
        }
    }
    if omitted {
        // This short marker is always available even when the text cap is hit.
        output.push(OMITTED.into());
    }
    output
}

fn function_signature(context: &NavigationContext, node: &Node) -> Option<Signature> {
    if !is_function(node) {
        return None;
    }
    let ni = name_index(node);
    let name = text(context, node.children.get(ni)?);
    let parameters = node
        .children
        .get(ni + 1)?
        .children
        .iter()
        .map(|parameter| {
            let mutable = head(parameter) == "mut";
            let at = usize::from(mutable);
            let name = text(context, parameter.children.get(at)?);
            let kind = parameter.children.get(at + 1)?;
            if !typed(kind) {
                return None;
            }
            let label = if mutable {
                format!("#mut {name} {}", text(context, kind))
            } else {
                format!("{name} {}", text(context, kind))
            };
            Some((name, label))
        })
        .collect::<Option<Vec<_>>>()?;
    let return_type = node.children.get(ni + 2)?;
    if !typed(return_type) {
        return None;
    }
    let prefix = if ni == 2 {
        format!("#extern-fn {}", text(context, node.children.get(1)?))
    } else {
        format!("#{}", head(node))
    };
    let label = format!(
        "({prefix} {name} ({}) {})",
        parameters
            .iter()
            .map(|(_, label)| format!("({label})"))
            .collect::<Vec<_>>()
            .join(" "),
        text(context, return_type)
    );
    let mut contracts = node
        .children
        .iter()
        .skip(ni + 3)
        .filter(|child| matches!(head(child), "requires" | "ensures" | "preserves"))
        .map(|child| text(context, child))
        .collect::<Vec<_>>();
    if !contracts.is_empty() {
        contracts.insert(0, "// Authored contracts".into());
    }
    contracts.extend(computed_contracts(context, node));
    // Navigation selected the source declaration, including through aliases.
    // Permissions remain a separate written interface, never predicate facts.
    if let Some(effects) = node.children.get(ni + 3).filter(|node| head(node) == "effects") {
        contracts.push("// Declared effects".into());
        contracts.push(text(context, effects));
    }
    Some(Signature {
        label,
        parameters,
        contracts,
    })
}
fn declaration_signature(
    context: &NavigationContext,
    node: &Node,
    target: Span,
) -> Option<Signature> {
    if is_function(node)
        && node
            .children
            .get(name_index(node))
            .is_some_and(|name| name.span == target)
    {
        return function_signature(context, node);
    }
    node.children
        .iter()
        .find_map(|child| declaration_signature(context, child, target))
}

fn intrinsic_signature(
    context: &NavigationContext,
    span: Span,
    declaration: &crate::intrinsics::Declaration,
) -> Signature {
    let name = files(context)
        .get(span.source_id as usize)
        .and_then(|file| file.source.get(span.start..span.end))
        .unwrap_or(&declaration.operator);
    let parameters = declaration
        .parameters
        .iter()
        .map(|parameter| {
            (
                parameter.name.clone(),
                format!(
                    "{} {}",
                    parameter.name,
                    display_type(context, &parameter.ty)
                ),
            )
        })
        .collect::<Vec<_>>();
    let label = format!(
        "(#fn {name} ({}) {})",
        parameters
            .iter()
            .map(|(_, label)| format!("({label})"))
            .collect::<Vec<_>>()
            .join(" "),
        display_type(context, &declaration.return_type)
    );
    Signature {
        label,
        parameters,
        contracts: vec![],
    }
}

/// Resolve the callee's identity through the same source roles as definition.
pub(crate) fn signature(
    context: &NavigationContext,
    file: u32,
    callee_byte: usize,
) -> Option<Signature> {
    let index = Index::new(context.program.as_ref(), &context.forms, file, callee_byte);
    let targets = index.resolve();
    if let Some((span, declaration, None)) = index.intrinsic_information() {
        return Some(intrinsic_signature(context, span, &declaration));
    }
    let [target] = targets.as_slice() else {
        return None;
    };
    roots(context).find_map(|node| declaration_signature(context, node, *target))
}

fn description(context: &NavigationContext, node: &Node, target: Span) -> Option<String> {
    if is_function(node)
        && node
            .children
            .get(name_index(node))
            .is_some_and(|name| name.span == target)
    {
        let signature = function_signature(context, node)?;
        return Some(
            std::iter::once(signature.label)
                .chain(signature.contracts)
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
    let xs = &node.children;
    if xs.get(1).is_some_and(|name| name.span == target) {
        match head(node) {
            "let" | "let-mut" | "const" | "static" => {
                let kind = binding_parts(node).0.filter(|kind| typed(kind))?;
                return Some(format!(
                    "(#{} {} {})",
                    head(node),
                    text(context, &xs[1]),
                    text(context, kind)
                ));
            }
            "type" | "struct" | "enum" | "distributed-enum" | "capability" => {
                return Some(text(context, node));
            }
            "gn" | "gn-fn" => {
                return Some(format!(
                    "(#{} {} {})",
                    head(node),
                    text(context, &xs[1]),
                    text(context, xs.get(2)?)
                ));
            }
            "syntax" => return Some(format!("(#syntax {})", text(context, &xs[1]))),
            _ => {}
        }
    }
    if head(node) == "enum" {
        if let (Some(owner), Some(variants)) = (xs.get(1), xs.get(3)) {
            for variant in &variants.children {
                if variant.children.first().unwrap_or(variant).span == target {
                    return Some(format!(
                        "{} : {}",
                        text(context, variant),
                        text(context, owner)
                    ));
                }
            }
        }
    }
    // Only declaration sections introduce typed pairs. A pattern such as
    // (left right) must use the resolver's types, never parse `right` as a type.
    let pairs = if is_function(node) {
        xs.get(name_index(node) + 1)
            .map(|parameters| parameters.children.as_slice())
    } else if head(node) == "struct" {
        xs.get(3).map(|fields| fields.children.as_slice())
    } else {
        None
    };
    if let Some(pairs) = pairs {
        for pair in pairs {
            let ni = usize::from(head(pair) == "mut");
            if pair
                .children
                .get(ni)
                .is_some_and(|name| name.span == target)
            {
                let kind = pair.children.get(ni + 1).filter(|kind| typed(kind))?;
                return Some(format!(
                    "{}{} {}",
                    if ni == 1 { "#mut " } else { "" },
                    text(context, &pair.children[ni]),
                    text(context, kind)
                ));
            }
        }
    }
    if head(node) == "where" {
        if let Some(pair) = xs.get(1) {
            if pair
                .children
                .first()
                .is_some_and(|name| name.span == target)
            {
                return Some(format!(
                    "{} {}",
                    text(context, &pair.children[0]),
                    text(context, pair.children.get(1)?)
                ));
            }
        }
    }
    node.children
        .iter()
        .find_map(|child| description(context, child, target))
}

/// Return the authored query range and information for its resolved declaration.
pub(crate) fn hover(context: &NavigationContext, file: u32, byte: usize) -> Option<(Span, String)> {
    let index = Index::new(context.program.as_ref(), &context.forms, file, byte);
    let targets = index.resolve();
    if let Some((span, declaration, parameter)) = index.intrinsic_information() {
        let description = if let Some(parameter) = parameter {
            let parameter = declaration
                .parameters
                .iter()
                .find(|candidate| candidate.name == parameter)?;
            format!(
                "{} {}",
                parameter.name,
                display_type(context, &parameter.ty)
            )
        } else {
            // The lexical-only context has no source files on its Index. Check
            // the authored spelling here too, excluding lowered infix tokens.
            let authored = files(context)
                .get(span.source_id as usize)?
                .source
                .get(span.start..span.end)?;
            if crate::names::numeric_operation(authored).as_deref()
                != Some(declaration.operator.as_str())
            {
                return None;
            }
            intrinsic_signature(context, span, &declaration).label
        };
        return Some((span, description));
    }
    let queried = roots(context).find_map(|node| token(node, file, byte))?;
    let target = match targets.as_slice() {
        [target] => *target,
        [] => return None,
        targets => {
            // Each branch of an or-pattern declares the same lexical binding.
            // Several source targets are useful only when the resolver supplied
            // an identical type for every binding; global ambiguity stays inert.
            let kind = index.binding_type(targets[0])?;
            if targets
                .iter()
                .any(|target| index.binding_type(*target).as_ref() != Some(&kind))
            {
                return None;
            }
            return Some((
                queried.span,
                format!(
                    "{} {}",
                    text(context, queried),
                    display_type(context, &kind)
                ),
            ));
        }
    };
    let description = roots(context)
        .find_map(|node| description(context, node, target))
        .or_else(|| {
            let kind = index.binding_type(target)?;
            let binding =
                roots(context).find_map(|node| token(node, target.source_id, target.start))?;
            Some(format!(
                "{} {}",
                text(context, binding),
                display_type(context, &kind)
            ))
        })?;
    Some((queried.span, description))
}
