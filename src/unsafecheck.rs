use crate::analysis_error::{failure, Error, Site};

use crate::{Expr, Item, Program, Statement};

pub(crate) fn check_program_with_span(
    program: &Program,
) -> Result<(), (String, Option<crate::Span>)> {
    let statics = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Static { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect::<std::collections::HashSet<_>>();
    let external_functions = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) if function.external || function.unsafe_call => Some((
                function.name.as_str(),
                if function.external {
                    "external"
                } else {
                    "unsafe"
                },
            )),
            _ => None,
        })
        .collect::<std::collections::HashMap<_, _>>();
    for item in &program.items {
        if let Item::Function(function) = item {
            if function.external {
                continue;
            }
            // Function parameters shadow statics in the same way as local
            // bindings. The parser retains parameter spellings, so exclude
            // those names from this function's static-access set. Locals and
            // pattern bindings that shadow a static are alpha-renamed during
            // parsing and therefore no longer collide here.
            let shadowed_statics = function
                .parameters
                .iter()
                .map(|parameter| parameter.name.as_str())
                .collect::<std::collections::HashSet<_>>();
            let function_statics = statics
                .difference(&shadowed_statics)
                .copied()
                .collect::<std::collections::HashSet<_>>();
            for (index, statement) in function.body.iter().enumerate() {
                if let Err(error) =
                    check_statement(statement, false, &function_statics, &external_functions)
                {
                    let key = (function.name.clone(), index);
                    let span = error
                        .site
                        .and_then(|site| site.span(program))
                        .or_else(|| program.statement_spans.get(&key).copied());
                    return Err((error.message, span));
                }
            }
        }
    }
    Ok(())
}

fn check_statement(
    statement: &Statement,
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
    external_functions: &std::collections::HashMap<&str, &str>,
) -> Result<(), Error> {
    let _site = Site::statement(statement).enter();
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => {
            check_expression(value, unsafe_context, statics, external_functions)?
        }
        Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. } => {
            check_expression(value, unsafe_context, statics, external_functions)?
        }
        Statement::ArrayAssign { index, value, .. } => {
            check_expression(index, unsafe_context, statics, external_functions)?;
            check_expression(value, unsafe_context, statics, external_functions)?;
        }
        Statement::While { condition, body } => {
            check_expression(condition, unsafe_context, statics, external_functions)?;
            check_statements(body, unsafe_context, statics, external_functions)?;
        }
        Statement::Loop { body } => {
            check_statements(body, unsafe_context, statics, external_functions)?
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, unsafe_context, statics, external_functions)?;
            check_expression(condition, unsafe_context, statics, external_functions)?;
            check_statement(step, unsafe_context, statics, external_functions)?;
            check_statements(body, unsafe_context, statics, external_functions)?;
        }
        Statement::Labeled { statement, .. } => {
            check_statement(statement, unsafe_context, statics, external_functions)?
        }
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        check_statements(else_body, unsafe_context, statics, external_functions)?;
    }
    Ok(())
}

fn check_statements(
    statements: &[Statement],
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
    external_functions: &std::collections::HashMap<&str, &str>,
) -> Result<(), Error> {
    for statement in statements {
        check_statement(statement, unsafe_context, statics, external_functions)?;
    }
    Ok(())
}

fn check_expression(
    expression: &Expr,
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
    external_functions: &std::collections::HashMap<&str, &str>,
) -> Result<(), Error> {
    let _site = Site::expression(expression).enter();
    match expression {
        Expr::List(items) => {
            let operator = items.first().and_then(|item| match item {
                Expr::Symbol(name) => Some(name.as_str()),
                _ => None,
            });
            let nested_unsafe = operator == Some("unsafe");
            if let Some(operator) = operator {
                if !unsafe_context && !nested_unsafe {
                    if let Some(kind) = external_functions.get(operator) {
                        return Err(failure!(
                            "call to {kind} function '{operator}' requires an enclosing (#unsafe ...) block"
                        ).child(0));
                    }
                }
            }
            if let Some(Expr::Symbol(name)) = items.get(1) {
                if statics.contains(name.as_str()) && !unsafe_context && !nested_unsafe {
                    return Err(failure!(
                        "access to static '{name}' requires an enclosing (#unsafe ...) block"
                    )
                    .child(1));
                }
            }
            if matches!(
                operator,
                Some(
                    "addr-of"
                        | "addr-of-mut"
                        | "ptr-read"
                        | "ptr-write"
                        | "ptr-offset"
                        | "ptr-borrow"
                        | "ptr-borrow-mut"
                        | "asm"
                        | "linux-syscall",
                )
            ) && !unsafe_context
            {
                return Err(failure!(
                    "unsafe operation '{}' requires an enclosing (#unsafe ...) block",
                    operator.unwrap()
                )
                .child(0));
            }
            for item in items.iter().skip(1) {
                check_expression(
                    item,
                    unsafe_context || nested_unsafe,
                    statics,
                    external_functions,
                )?;
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            check_statements(statements, unsafe_context, statics, external_functions)?
        }
        Expr::Symbol(name) if statics.contains(name.as_str()) && !unsafe_context => {
            return Err(failure!(
                "access to static '{name}' requires an enclosing (#unsafe ...) block"
            ));
        }
        Expr::Labeled { expression, .. } => {
            check_expression(expression, unsafe_context, statics, external_functions)?
        }
        Expr::Quote(value) => check_expression(value, unsafe_context, statics, external_functions)?,
        Expr::QuasiQuote(value) | Expr::Unquote(value) | Expr::UnquoteSplicing(value) => {
            check_expression(value, unsafe_context, statics, external_functions)?
        }
        Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
    Ok(())
}
