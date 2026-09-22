//! Pure, immutable syntax generators used by `@name` declarations.

use std::collections::{HashMap, HashSet};

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

pub(crate) fn expand(expressions: Vec<SpannedExpr>) -> Result<Vec<SpannedExpr>, String> {
    expand_with_generated(expressions).map(|(expressions, _)| expressions)
}

pub(crate) fn expand_with_generated(
    expressions: Vec<SpannedExpr>,
) -> Result<(Vec<SpannedExpr>, Vec<Expr>), String> {
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

    let mut output = Vec::new();
    let mut generated = Vec::new();
    let mut seen_invocations = HashSet::new();
    let mut budget = Budget {
        evaluation_steps: MAX_EVALUATION_STEPS,
        generated_nodes: 0,
    };
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
        let mut active = Vec::new();
        let expanded = expand_top(
            expression.expr,
            &generators,
            &mut active,
            &mut seen_invocations,
            &mut budget,
        )
        .map_err(|error| at_span(error, expression.span, "generator expansion"))?;
        if is_user_invocation {
            for form in &expanded {
                budget.generated_nodes = budget
                    .generated_nodes
                    .saturating_add(expression_nodes(form));
            }
            if budget.generated_nodes > MAX_GENERATED_NODES {
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
    Ok((output, generated))
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

fn expand_top(
    expression: Expr,
    generators: &HashMap<String, Generator>,
    active: &mut Vec<String>,
    seen_invocations: &mut HashSet<String>,
    budget: &mut Budget,
) -> Result<Vec<Expr>, String> {
    let Expr::List(items) = &expression else {
        return Ok(vec![expression]);
    };
    if !matches!(items.first(), Some(Expr::At)) {
        return Ok(vec![expression]);
    }
    let Some(Expr::Symbol(name)) = items.get(1) else {
        return Err("generator invocation requires a name after '@'".into());
    };
    let Some(generator) = generators.get(name) else {
        // Built-in declarations such as @optional are handled by the Lim parser.
        return Ok(vec![expression]);
    };
    if active.iter().any(|entry| entry == name) {
        let mut chain = active.join(" -> ");
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
    if active.len() >= MAX_EXPANSION_DEPTH {
        return Err(format!(
            "generator expansion exceeds maximum depth of {MAX_EXPANSION_DEPTH}"
        ));
    }
    let invocation_key = format!("{name}:{:?}", &items[2..]);
    if !seen_invocations.insert(invocation_key) {
        return Ok(Vec::new());
    }
    let environment = generator
        .parameters
        .iter()
        .cloned()
        .zip(items[2..].iter().cloned())
        .collect();
    active.push(name.clone());
    let result = match evaluate(&generator.body, &environment, budget) {
        Ok(result) => result,
        Err(error) => {
            active.pop();
            return Err(format!(
                "@{name} defined at {}:{}: {error}",
                generator.span.line, generator.span.column
            ));
        }
    };
    let Value::Syntax(Expr::List(forms)) = result else {
        active.pop();
        return Err(format!("@{name} must return a list of generated forms"));
    };
    let mut expanded = Vec::new();
    for form in forms {
        match expand_top(form, generators, active, seen_invocations, budget) {
            Ok(forms) => expanded.extend(forms),
            Err(error) => {
                active.pop();
                return Err(error);
            }
        }
    }
    active.pop();
    Ok(expanded)
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
}
