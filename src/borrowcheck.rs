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

struct Context {
    loans: Loans,
    returnable: std::collections::HashSet<String>,
    mutable: std::collections::HashSet<String>,
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
    let globals = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Let { name, .. } | Item::Static { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<std::collections::HashSet<_>>();
    for item in &program.items {
        if let Item::Function(function) = item {
            if !function.external {
                check_function(function, &globals)?;
            }
        }
    }
    Ok(())
}

fn check_function(
    function: &Function,
    globals: &std::collections::HashSet<String>,
) -> Result<(), String> {
    let mut returnable = globals.clone();
    let mut mutable = std::collections::HashSet::new();
    for parameter in &function.parameters {
        returnable.insert(parameter.name.clone());
        if parameter.mutable {
            mutable.insert(parameter.name.clone());
        }
    }
    let mut context = Context {
        loans: Loans::default(),
        returnable,
        mutable,
    };
    for statement in &function.body {
        check_statement(statement, &mut context)?;
    }
    Ok(())
}

fn check_statement(statement: &Statement, context: &mut Context) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. } => check_expression(value, context)?,
        Statement::Assign { name, value }
        | Statement::FieldAssign { name, value, .. }
        | Statement::TupleAssign { name, value, .. }
        | Statement::EnumPayloadAssign { name, value, .. } => {
            check_expression(value, context)?;
            context.loans.write(name)?;
        }
        Statement::ArrayAssign { name, index, value } => {
            check_expression(index, context)?;
            check_expression(value, context)?;
            context.loans.write(name)?;
        }
        Statement::While { condition, body } => {
            check_expression(condition, context)?;
            check_statements(body, context)?;
        }
        Statement::Loop { body } => check_statements(body, context)?,
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, context)?;
            check_expression(condition, context)?;
            check_statements(body, context)?;
            check_statement(step, context)?;
        }
        Statement::Labeled { statement, .. } => check_statement(statement, context)?,
        Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => check_expression(value, context)?,
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        check_statements(else_body, context)?;
    }
    Ok(())
}

fn check_statements(statements: &[Statement], context: &mut Context) -> Result<(), String> {
    for statement in statements {
        check_statement(statement, context)?;
    }
    Ok(())
}

fn check_expression(expression: &Expr, context: &mut Context) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                if matches!(operator.as_str(), "borrow" | "borrow-mut") {
                    if items.len() != 3 {
                        if items.len() == 2 {
                            let owner = match &items[1] {
                                Expr::Symbol(name) => name,
                                _ => return Err(format!("{operator} requires a variable name")),
                            };
                            if !context.returnable.contains(owner) {
                                return Err(format!(
                                    "cannot return a reference to local variable '{owner}'"
                                ));
                            }
                            if operator == "borrow-mut" && !context.mutable.contains(owner) {
                                return Err(format!(
                                    "cannot mutably borrow immutable variable '{owner}'"
                                ));
                            }
                            return Ok(());
                        }
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
                    context.loans.borrow(owner, kind)?;
                    let result = check_expression(&items[2], context);
                    context.loans.end(owner);
                    result?
                } else {
                    for item in &items[1..] {
                        check_expression(item, context)?;
                    }
                }
            } else {
                for item in items {
                    check_expression(item, context)?;
                }
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => check_statements(statements, context)?,
        Expr::Labeled { expression, .. } => check_expression(expression, context)?,
        Expr::Quote(value) => check_expression(value, context)?,
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
