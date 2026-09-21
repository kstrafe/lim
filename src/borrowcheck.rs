//! Lexical borrow checking for Lim's first borrow model.
//!
//! Lim does not yet expose references as values.  A borrow is therefore an
//! expression scope: `(#borrow owner body)` or `(#borrow-mut owner body)`.
//! The owner is borrowed for exactly the duration of `body`.  This gives the
//! language useful, inferred borrow checking without inventing a runtime
//! representation before indirection is designed.

use std::collections::HashMap;

use crate::{Expr, Function, Item, Program, Statement};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LoanKind {
    Shared(usize),
    Mutable,
}

#[derive(Default)]
struct Loans {
    active: HashMap<String, LoanKind>,
}

impl Loans {
    fn borrow(&mut self, owner: &str, kind: LoanKind) -> Result<(), String> {
        match (self.active.get(owner).copied(), kind) {
            (None, _) => {
                self.active.insert(owner.to_owned(), kind);
                Ok(())
            }
            (Some(LoanKind::Shared(count)), LoanKind::Shared(_)) => {
                self.active
                    .insert(owner.to_owned(), LoanKind::Shared(count + 1));
                Ok(())
            }
            (Some(LoanKind::Shared(_)), LoanKind::Mutable) => Err(format!(
                "cannot borrow '{owner}' mutably because it is already borrowed"
            )),
            (Some(LoanKind::Mutable), _) => Err(format!(
                "cannot borrow '{owner}' because it is already borrowed mutably"
            )),
        }
    }

    fn end(&mut self, owner: &str) {
        match self.active.get_mut(owner) {
            Some(LoanKind::Shared(count)) if *count > 1 => *count -= 1,
            Some(_) => {
                self.active.remove(owner);
            }
            None => {}
        }
    }

    fn write(&self, owner: &str) -> Result<(), String> {
        match self.active.get(owner) {
            Some(LoanKind::Shared(_)) => Err(format!(
                "cannot mutate '{owner}' while it is immutably borrowed"
            )),
            Some(LoanKind::Mutable) | None => Ok(()),
        }
    }
}

pub(crate) fn check_program(program: &Program) -> Result<(), String> {
    for item in &program.items {
        if let Item::Function(function) = item {
            if !function.external {
                check_function(function)?;
            }
        }
    }
    Ok(())
}

fn check_function(function: &Function) -> Result<(), String> {
    let mut loans = Loans::default();
    for statement in &function.body {
        check_statement(statement, &mut loans)?;
    }
    Ok(())
}

fn check_statement(statement: &Statement, loans: &mut Loans) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. } => check_expression(value, loans)?,
        Statement::Assign { name, value }
        | Statement::FieldAssign { name, value, .. }
        | Statement::TupleAssign { name, value, .. }
        | Statement::EnumPayloadAssign { name, value, .. } => {
            check_expression(value, loans)?;
            loans.write(name)?;
        }
        Statement::ArrayAssign { name, index, value } => {
            check_expression(index, loans)?;
            check_expression(value, loans)?;
            loans.write(name)?;
        }
        Statement::While { condition, body } => {
            check_expression(condition, loans)?;
            check_statements(body, loans)?;
        }
        Statement::Loop { body } => check_statements(body, loans)?,
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, loans)?;
            check_expression(condition, loans)?;
            check_statements(body, loans)?;
            check_statement(step, loans)?;
        }
        Statement::Labeled { statement, .. } => check_statement(statement, loans)?,
        Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => check_expression(value, loans)?,
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        check_statements(else_body, loans)?;
    }
    Ok(())
}

fn check_statements(statements: &[Statement], loans: &mut Loans) -> Result<(), String> {
    for statement in statements {
        check_statement(statement, loans)?;
    }
    Ok(())
}

fn check_expression(expression: &Expr, loans: &mut Loans) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                if matches!(operator.as_str(), "borrow" | "borrow-mut") {
                    if items.len() != 3 {
                        return Err(format!(
                            "{operator} requires the form (#{operator} owner body)"
                        ));
                    }
                    let owner = match &items[1] {
                        Expr::Symbol(name) => name,
                        _ => return Err(format!("{operator} requires a variable name")),
                    };
                    let kind = if operator == "borrow" {
                        LoanKind::Shared(1)
                    } else {
                        LoanKind::Mutable
                    };
                    loans.borrow(owner, kind)?;
                    let result = check_expression(&items[2], loans);
                    loans.end(owner);
                    result?
                } else {
                    for item in &items[1..] {
                        check_expression(item, loans)?;
                    }
                }
            } else {
                for item in items {
                    check_expression(item, loans)?;
                }
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => check_statements(statements, loans)?,
        Expr::Labeled { expression, .. } => check_expression(expression, loans)?,
        Expr::Quote(value) => check_expression(value, loans)?,
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
