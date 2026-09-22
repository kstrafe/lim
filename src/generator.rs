//! Pure, immutable syntax generators used by `@name` declarations.

use std::{
    collections::{HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};

use crate::{Expr, Span, SpannedExpr};

const MAX_EVALUATION_STEPS: usize = 200_000;
const MAX_GENERATED_NODES: usize = 1_000_000;
const MAX_EXPANSION_DEPTH: usize = 128;

#[derive(Clone)]
struct Generator {
    parameters: Vec<String>,
    body: Expr,
    span: Span,
}

#[derive(Clone, Debug)]
enum Value {
    Syntax(Expr),
    Boolean(bool),
}

type Environment = HashMap<String, Expr>;
type ExpandedForms = (Vec<SpannedExpr>, Vec<Expr>);
type ExpandedFormsWithHits = (ExpandedForms, usize);

pub(crate) fn expand_with_generated_cached(
    expressions: Vec<SpannedExpr>,
    cache_dir: Option<&Path>,
) -> Result<(Vec<SpannedExpr>, Vec<Expr>), String> {
    expand_with_generated_cached_and_hits(expressions, cache_dir).map(|(result, _)| result)
}

fn expand_with_generated_cached_and_hits(
    expressions: Vec<SpannedExpr>,
    cache_dir: Option<&Path>,
) -> Result<ExpandedFormsWithHits, String> {
    let mut generators = HashMap::new();
    let mut remaining = Vec::new();
    for expression in expressions {
        if let Expr::List(items) = &expression.expr {
            if is_operator(items.first(), "#generator") {
                let generator = parse_generator(items, expression.span)
                    .map_err(|error| at_span(error, expression.span, "generator declaration"))?;
                let name = symbol(items.get(1), "generator name")?.to_owned();
                if generators.insert(name.clone(), generator).is_some() {
                    return Err(format!("duplicate generator declaration '{name}'"));
                }
                continue;
            }
        }
        remaining.push(expression);
    }

    let dependency_context = generator_dependency_context(&generators);
    let mut context = ExpansionContext {
        generators: &generators,
        active: Vec::new(),
        seen_invocations: HashSet::new(),
        budget: Budget {
            evaluation_steps: MAX_EVALUATION_STEPS,
            generated_nodes: 0,
        },
        invocation_traces: Vec::new(),
        cache_hits: 0,
        dependency_context,
        cache_dir,
    };
    let mut output = Vec::new();
    let mut generated = Vec::new();
    for expression in remaining {
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
        output.extend(expanded.into_iter().map(|expr| SpannedExpr {
            expr,
            span: expression.span,
        }));
    }
    Ok(((output, generated), context.cache_hits))
}

fn parse_generator(items: &[Expr], span: Span) -> Result<Generator, String> {
    if items.len() != 4 {
        return Err("#generator requires a name, parameter list, and body".into());
    }
    let name = symbol(items.get(1), "generator name")?;
    let parameters = match items.get(2) {
        Some(Expr::List(parameters)) => parameters,
        _ => return Err(format!("generator '{name}' parameters must be a list")),
    };
    let mut names = Vec::with_capacity(parameters.len());
    for parameter in parameters {
        let parameter = symbol(Some(parameter), "generator parameter")?;
        if parameter.starts_with('#') || parameter.starts_with('@') {
            return Err(format!("invalid generator parameter '{parameter}'"));
        }
        if names.iter().any(|existing| existing == parameter) {
            return Err(format!("duplicate generator parameter '{parameter}'"));
        }
        names.push(parameter.to_owned());
    }
    Ok(Generator {
        parameters: names,
        body: items[3].clone(),
        span,
    })
}

struct Budget {
    evaluation_steps: usize,
    generated_nodes: usize,
}

struct CachedExpansion {
    expressions: Vec<Expr>,
    invocations: Vec<String>,
}

struct ExpansionContext<'a> {
    generators: &'a HashMap<String, Generator>,
    active: Vec<String>,
    seen_invocations: HashSet<String>,
    budget: Budget,
    invocation_traces: Vec<HashSet<String>>,
    cache_hits: usize,
    dependency_context: String,
    cache_dir: Option<&'a Path>,
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
    let Some(generator) = context.generators.get(name) else {
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
            "@{name} expects {} syntax argument(s), received {}",
            generator.parameters.len(),
            items.len() - 2
        ));
    }
    if context.active.len() >= MAX_EXPANSION_DEPTH {
        return Err(format!(
            "generator expansion exceeds maximum depth of {MAX_EXPANSION_DEPTH}"
        ));
    }
    let invocation_key = format!("{name}:{:?}", &items[2..]);
    for trace in context.invocation_traces.iter_mut() {
        trace.insert(invocation_key.clone());
    }
    if !context.seen_invocations.insert(invocation_key) {
        return Ok(Vec::new());
    }
    let cache_key = format!(
        "lim-generator-cache-v2\ncompiler={}\ndependencies={}\ngenerator={name}\narguments={:?}",
        env!("CARGO_PKG_VERSION"),
        context.dependency_context,
        &items[2..]
    );
    if let Some(cached) = context
        .cache_dir
        .and_then(|directory| read_cached_expansion(directory, &cache_key))
    {
        context.cache_hits = context.cache_hits.saturating_add(1);
        for invocation in &cached.invocations {
            context.seen_invocations.insert(invocation.clone());
            for trace in context.invocation_traces.iter_mut() {
                trace.insert(invocation.clone());
            }
        }
        return Ok(cached.expressions);
    }
    context
        .invocation_traces
        .push(HashSet::from([format!("{name}:{:?}", &items[2..])]));
    let environment = generator
        .parameters
        .iter()
        .cloned()
        .zip(items[2..].iter().cloned())
        .collect();
    context.active.push(name.clone());
    let result = match evaluate(&generator.body, &environment, &mut context.budget) {
        Ok(result) => result,
        Err(error) => {
            context.active.pop();
            return Err(format!(
                "@{name} defined at {}:{}: {error}",
                generator.span.line, generator.span.column
            ));
        }
    };
    let Value::Syntax(Expr::List(forms)) = result else {
        context.active.pop();
        return Err(format!("@{name} must return a list of generated forms"));
    };
    let mut expanded = Vec::new();
    for form in forms {
        match expand_top(form, context) {
            Ok(forms) => expanded.extend(forms),
            Err(error) => {
                context.active.pop();
                return Err(error);
            }
        }
    }
    context.active.pop();
    let trace = context.invocation_traces.pop().unwrap_or_default();
    if let Some(directory) = context.cache_dir {
        write_cached_expansion(directory, &cache_key, &expanded, &trace);
    }
    Ok(expanded)
}

fn generator_dependency_context(generators: &HashMap<String, Generator>) -> String {
    let mut definitions = generators.iter().collect::<Vec<_>>();
    definitions.sort_by(|left, right| left.0.cmp(right.0));
    let definitions = definitions
        .into_iter()
        .map(|(name, generator)| format!("{name}:{:?}:{:?}", generator.parameters, generator.body))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        "runtime={:032x}\n{definitions}",
        stable_hash(include_bytes!("generator.rs"))
    )
}

fn cache_path(directory: &Path, key: &str) -> PathBuf {
    // Stable FNV-1a 128-bit naming; the complete key is stored and compared
    // inside each file, so a digest collision can never produce a false hit.
    directory.join(format!(
        "generator-{:032x}.cache",
        stable_hash(key.as_bytes())
    ))
}

fn stable_hash(bytes: &[u8]) -> u128 {
    let mut hash = 0x6c62272e07bb014262b821756295c58du128;
    for byte in bytes {
        hash ^= u128::from(*byte);
        hash = hash.wrapping_mul(0x0000000001000000000000000000013bu128);
    }
    hash
}

fn read_cached_expansion(directory: &Path, key: &str) -> Option<CachedExpansion> {
    let bytes = fs::read(cache_path(directory, key)).ok()?;
    let mut cursor = 0;
    let key_length = read_cache_length(&bytes, &mut cursor)?;
    let key_end = cursor.checked_add(key_length)?;
    if bytes.get(cursor..key_end)? != key.as_bytes() {
        return None;
    }
    cursor = key_end;
    let count = read_cache_length(&bytes, &mut cursor)?;
    if count > bytes.len().saturating_sub(cursor) / 8 {
        return None;
    }
    let mut invocations = Vec::with_capacity(count);
    for _ in 0..count {
        let length = read_cache_length(&bytes, &mut cursor)?;
        let end = cursor.checked_add(length)?;
        invocations.push(
            std::str::from_utf8(bytes.get(cursor..end)?)
                .ok()?
                .to_owned(),
        );
        cursor = end;
    }
    let source = std::str::from_utf8(bytes.get(cursor..)?).ok()?;
    let expressions = crate::parse(source)
        .ok()?
        .into_iter()
        .map(|expression| expression.expr)
        .collect();
    Some(CachedExpansion {
        expressions,
        invocations,
    })
}

fn read_cache_length(bytes: &[u8], cursor: &mut usize) -> Option<usize> {
    let end = cursor.checked_add(8)?;
    let length = u64::from_le_bytes(bytes.get(*cursor..end)?.try_into().ok()?);
    *cursor = end;
    usize::try_from(length).ok()
}

fn write_cached_expansion(
    directory: &Path,
    key: &str,
    expressions: &[Expr],
    invocations: &HashSet<String>,
) {
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
        let mut cursor = 0;
        if let Some(existing_length) = read_cache_length(&existing, &mut cursor) {
            if let Some(existing_end) = cursor.checked_add(existing_length) {
                if let Some(existing_key) = existing.get(cursor..existing_end) {
                    if existing_key != key.as_bytes()
                        && std::str::from_utf8(existing_key)
                            .is_ok_and(|value| cache_path(directory, value) == path)
                    {
                        // A genuine digest collision must not overwrite the other entry.
                        return;
                    }
                }
            }
        }
    }
    let mut contents = Vec::with_capacity(16 + key.len() + source.len());
    contents.extend_from_slice(&(key.len() as u64).to_le_bytes());
    contents.extend_from_slice(key.as_bytes());
    let mut invocations = invocations.iter().collect::<Vec<_>>();
    invocations.sort();
    contents.extend_from_slice(&(invocations.len() as u64).to_le_bytes());
    for invocation in invocations {
        contents.extend_from_slice(&(invocation.len() as u64).to_le_bytes());
        contents.extend_from_slice(invocation.as_bytes());
    }
    contents.extend_from_slice(source.as_bytes());
    let temporary = path.with_extension(format!("{}.tmp", std::process::id()));
    if fs::write(&temporary, contents).is_ok() {
        let _ = fs::rename(temporary, path);
    }
}

fn evaluate(
    expression: &Expr,
    environment: &Environment,
    budget: &mut Budget,
) -> Result<Value, String> {
    if budget.evaluation_steps == 0 {
        return Err(format!(
            "generator evaluation exceeds maximum of {MAX_EVALUATION_STEPS} steps"
        ));
    }
    budget.evaluation_steps -= 1;
    if let Expr::Symbol(name) = expression {
        return Ok(Value::Syntax(
            environment
                .get(name)
                .cloned()
                .unwrap_or_else(|| expression.clone()),
        ));
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
            match evaluate(&items[1], environment, budget)? {
                Value::Boolean(true) => evaluate(&items[2], environment, budget),
                Value::Boolean(false) => evaluate(&items[3], environment, budget),
                Value::Syntax(_) => Err("#gn-if condition must be a #gn predicate".into()),
            }
        }
        "#gn-equal" => {
            arity(operator, items, 3)?;
            let left = syntax(evaluate(&items[1], environment, budget)?, operator)?;
            let right = syntax(evaluate(&items[2], environment, budget)?, operator)?;
            Ok(Value::Boolean(left == right))
        }
        "#gn-symbol?" | "#gn-list?" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, budget)?, operator)?;
            Ok(Value::Boolean(if operator == "#gn-symbol?" {
                matches!(value, Expr::Symbol(_))
            } else {
                matches!(value, Expr::List(_))
            }))
        }
        "#gn-symbol" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, budget)?, operator)?;
            let Expr::String(value) = value else {
                return Err("#gn-symbol requires a string literal".into());
            };
            Ok(Value::Syntax(Expr::Symbol(value)))
        }
        "#gn-list" => {
            let mut values = Vec::with_capacity(items.len().saturating_sub(1));
            for item in &items[1..] {
                values.push(syntax(evaluate(item, environment, budget)?, operator)?);
            }
            Ok(Value::Syntax(Expr::List(values)))
        }
        "#gn-first" | "#gn-rest" => {
            arity(operator, items, 2)?;
            let value = syntax(evaluate(&items[1], environment, budget)?, operator)?;
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
            let list = syntax(evaluate(&items[2], environment, budget)?, operator)?;
            let Expr::List(values) = list else {
                return Err("#gn-for-each requires a list of syntax values".into());
            };
            let mut result = Vec::with_capacity(values.len());
            for value in values {
                let mut nested = environment.clone();
                nested.insert(variable.clone(), value);
                match evaluate(&items[3], &nested, budget)? {
                    Value::Syntax(syntax) => result.push(syntax),
                    Value::Boolean(_) => return Err("#gn-for-each body must produce syntax".into()),
                }
            }
            Ok(Value::Syntax(Expr::List(result)))
        }
        "#gn-error" => {
            arity(operator, items, 2)?;
            let message = syntax(evaluate(&items[1], environment, budget)?, operator)?;
            match message {
                Expr::String(message) => Err(format!("generator error: {message}")),
                _ => Err("#gn-error requires a string literal message".into()),
            }
        }
        _ if operator.starts_with("#gn-") => Err(format!("unknown generator builtin '{operator}'")),
        _ => Ok(Value::Syntax(expression.clone())),
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
    format!("{}:{}: {context}: {message}", span.line, span.column)
}

fn expression_nodes(expression: &Expr) -> usize {
    match expression {
        Expr::List(items) => 1usize.saturating_add(items.iter().map(expression_nodes).sum()),
        Expr::Quote(value) => 1usize.saturating_add(expression_nodes(value)),
        Expr::Labeled { expression, .. } => 1usize.saturating_add(expression_nodes(expression)),
        _ => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
            &mut Budget {
                evaluation_steps: MAX_EVALUATION_STEPS,
                generated_nodes: 0,
            },
        )
        .unwrap_err();
        assert!(error.contains("exceeds maximum"));
    }

    #[test]
    fn generated_syntax_cache_hits_and_invalidates_for_generator_dependencies() {
        let directory =
            std::env::temp_dir().join(format!("lim-generator-cache-{}", std::process::id()));
        let source = "(#generator alias (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name u64))) (#generator forward (call) (#gn-list call)) (@forward (@alias CachedType)) (@alias CachedType)";
        let parse_forms = |source: &str| crate::parse(source).unwrap();

        let ((first, _), first_hits) =
            expand_with_generated_cached_and_hits(parse_forms(source), Some(&directory)).unwrap();
        assert_eq!(first_hits, 0);
        assert_eq!(first.len(), 1, "nested duplicate invocations deduplicate");

        let ((second, _), second_hits) =
            expand_with_generated_cached_and_hits(parse_forms(source), Some(&directory)).unwrap();
        assert!(
            second_hits >= 1,
            "an identical generator call should hit disk cache"
        );
        assert_eq!(second, first);
        assert_eq!(
            second.len(),
            1,
            "cached dependency traces preserve deduplication"
        );

        let changed_dependency = source.replace("name u64", "name u32");
        let ((changed, _), changed_hits) = expand_with_generated_cached_and_hits(
            parse_forms(&changed_dependency),
            Some(&directory),
        )
        .unwrap();
        assert_eq!(
            changed_hits, 0,
            "changing a generator dependency invalidates cache entries"
        );
        assert_ne!(changed, second);
        let _ = std::fs::remove_dir_all(directory);
    }
}
