use crate::{Expr, Item, Program, Statement};

pub(crate) fn check_program(program: &Program) -> Result<(), String> {
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
            Item::Function(function) if function.external => Some(function.name.as_str()),
            _ => None,
        })
        .collect::<std::collections::HashSet<_>>();
    for item in &program.items {
        if let Item::Function(function) = item {
            if function.external {
                continue;
            }
            for statement in &function.body {
                check_statement(statement, false, &statics, &external_functions)?;
            }
        }
    }
    Ok(())
}

fn check_statement(
    statement: &Statement,
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
    external_functions: &std::collections::HashSet<&str>,
) -> Result<(), String> {
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
    external_functions: &std::collections::HashSet<&str>,
) -> Result<(), String> {
    for statement in statements {
        check_statement(statement, unsafe_context, statics, external_functions)?;
    }
    Ok(())
}

fn check_expression(
    expression: &Expr,
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
    external_functions: &std::collections::HashSet<&str>,
) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            let operator = items.first().and_then(|item| match item {
                Expr::Symbol(name) => Some(name.as_str()),
                _ => None,
            });
            let nested_unsafe = operator == Some("unsafe");
            if let Some(operator) = operator {
                if external_functions.contains(operator) && !unsafe_context && !nested_unsafe {
                    return Err(format!(
                        "call to external function '{operator}' requires an enclosing (#unsafe ...) block"
                    ));
                }
            }
            if let Some(Expr::Symbol(name)) = items.get(1) {
                if statics.contains(name.as_str()) && !unsafe_context && !nested_unsafe {
                    return Err(format!(
                        "access to static '{name}' requires an enclosing (#unsafe ...) block"
                    ));
                }
            }
            if matches!(
                operator,
                Some("addr-of" | "addr-of-mut" | "ptr-read" | "ptr-write" | "ptr-offset")
            ) && !unsafe_context
            {
                return Err(format!(
                    "unsafe operation '{}' requires an enclosing (#unsafe ...) block",
                    operator.unwrap()
                ));
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
            return Err(format!(
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
