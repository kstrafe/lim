use crate::{Expr, Item, Program, Statement};

pub(crate) fn check_program(program: &Program) -> Result<(), String> {
    for item in &program.items {
        if let Item::Function(function) = item {
            if function.external {
                continue;
            }
            for statement in &function.body {
                check_statement(statement, false)?;
            }
        }
    }
    Ok(())
}

fn check_statement(statement: &Statement, unsafe_context: bool) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => check_expression(value, unsafe_context)?,
        Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. } => check_expression(value, unsafe_context)?,
        Statement::ArrayAssign { index, value, .. } => {
            check_expression(index, unsafe_context)?;
            check_expression(value, unsafe_context)?;
        }
        Statement::While { condition, body } => {
            check_expression(condition, unsafe_context)?;
            check_statements(body, unsafe_context)?;
        }
        Statement::Loop { body } => check_statements(body, unsafe_context)?,
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, unsafe_context)?;
            check_expression(condition, unsafe_context)?;
            check_statement(step, unsafe_context)?;
            check_statements(body, unsafe_context)?;
        }
        Statement::Labeled { statement, .. } => check_statement(statement, unsafe_context)?,
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        check_statements(else_body, unsafe_context)?;
    }
    Ok(())
}

fn check_statements(statements: &[Statement], unsafe_context: bool) -> Result<(), String> {
    for statement in statements {
        check_statement(statement, unsafe_context)?;
    }
    Ok(())
}

fn check_expression(expression: &Expr, unsafe_context: bool) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            let operator = items.first().and_then(|item| match item {
                Expr::Symbol(name) => Some(name.as_str()),
                _ => None,
            });
            let nested_unsafe = operator == Some("unsafe");
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
                check_expression(item, unsafe_context || nested_unsafe)?;
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            check_statements(statements, unsafe_context)?
        }
        Expr::Labeled { expression, .. } => check_expression(expression, unsafe_context)?,
        Expr::Quote(value) => check_expression(value, unsafe_context)?,
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
