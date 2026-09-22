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
    for item in &program.items {
        if let Item::Function(function) = item {
            if function.external {
                continue;
            }
            for statement in &function.body {
                check_statement(statement, false, &statics)?;
            }
        }
    }
    Ok(())
}

fn check_statement(
    statement: &Statement,
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => check_expression(value, unsafe_context, statics)?,
        Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. } => {
            check_expression(value, unsafe_context, statics)?
        }
        Statement::ArrayAssign { index, value, .. } => {
            check_expression(index, unsafe_context, statics)?;
            check_expression(value, unsafe_context, statics)?;
        }
        Statement::While { condition, body } => {
            check_expression(condition, unsafe_context, statics)?;
            check_statements(body, unsafe_context, statics)?;
        }
        Statement::Loop { body } => check_statements(body, unsafe_context, statics)?,
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, unsafe_context, statics)?;
            check_expression(condition, unsafe_context, statics)?;
            check_statement(step, unsafe_context, statics)?;
            check_statements(body, unsafe_context, statics)?;
        }
        Statement::Labeled { statement, .. } => {
            check_statement(statement, unsafe_context, statics)?
        }
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        check_statements(else_body, unsafe_context, statics)?;
    }
    Ok(())
}

fn check_statements(
    statements: &[Statement],
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
) -> Result<(), String> {
    for statement in statements {
        check_statement(statement, unsafe_context, statics)?;
    }
    Ok(())
}

fn check_expression(
    expression: &Expr,
    unsafe_context: bool,
    statics: &std::collections::HashSet<&str>,
) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            let operator = items.first().and_then(|item| match item {
                Expr::Symbol(name) => Some(name.as_str()),
                _ => None,
            });
            let nested_unsafe = operator == Some("unsafe");
            if let Some(Expr::Symbol(name)) = items.get(1) {
                if statics.contains(name.as_str()) && !unsafe_context && !nested_unsafe {
                    return Err(format!(
                        "access to static '{name}' requires an enclosing (#unsafe ...) block"
                    ));
                }
            }
            if matches!(
                operator,
                Some("addr-of" | "addr-of-mut" | "ptr-read" | "ptr-write")
            ) && !unsafe_context
            {
                return Err(format!(
                    "unsafe operation '{}' requires an enclosing (#unsafe ...) block",
                    operator.unwrap()
                ));
            }
            for item in items.iter().skip(1) {
                check_expression(item, unsafe_context || nested_unsafe, statics)?;
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            check_statements(statements, unsafe_context, statics)?
        }
        Expr::Symbol(name) if statics.contains(name.as_str()) && !unsafe_context => {
            return Err(format!(
                "access to static '{name}' requires an enclosing (#unsafe ...) block"
            ));
        }
        Expr::Labeled { expression, .. } => check_expression(expression, unsafe_context, statics)?,
        Expr::Quote(value) => check_expression(value, unsafe_context, statics)?,
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
