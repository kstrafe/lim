//! Lexical borrow checking for Lim's first borrow model.
//!
//! Lim does not yet expose references as values.  A borrow is therefore an
//! expression scope: `(#borrow owner body)` or `(#borrow-mut owner body)`.
//! The owner is borrowed for exactly the duration of `body`.  This gives the
//! language useful, inferred borrow checking without inventing a runtime
//! representation before indirection is designed.

use std::collections::{HashMap, HashSet};

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
    returnable: HashSet<String>,
    mutable: HashSet<String>,
    reference_origins: HashMap<String, HashSet<String>>,
    allow_local_reference: bool,
    reference_types: HashSet<String>,
    reference_functions: HashSet<String>,
    function_names: HashSet<String>,
    return_contains_references: bool,
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
        .collect::<HashSet<_>>();
    let reference_types = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields, .. }
                if fields.iter().any(|field| {
                    type_contains_reference(&field.ty, program, &mut HashSet::new())
                }) =>
            {
                Some(name.clone())
            }
            Item::Enum { name, variants, .. }
                if variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|ty| type_contains_reference(ty, program, &mut HashSet::new())) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let reference_functions = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function)
                if contains_reference_type(&function.return_type, &reference_types) =>
            {
                Some(function.name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let function_names = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) => Some(function.name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    for item in &program.items {
        if let Item::Function(function) = item {
            if !function.external {
                check_function(
                    function,
                    &globals,
                    &reference_types,
                    &reference_functions,
                    &function_names,
                )?;
            }
        }
    }
    Ok(())
}

fn check_function(
    function: &Function,
    globals: &std::collections::HashSet<String>,
    reference_types: &HashSet<String>,
    reference_functions: &HashSet<String>,
    function_names: &HashSet<String>,
) -> Result<(), String> {
    let mut returnable = globals.clone();
    let mut mutable = std::collections::HashSet::new();
    let mut reference_origins = HashMap::new();
    for parameter in &function.parameters {
        returnable.insert(parameter.name.clone());
        if contains_reference_type(&parameter.ty, reference_types) {
            reference_origins.insert(
                parameter.name.clone(),
                HashSet::from([parameter.name.clone()]),
            );
        }
        if parameter.mutable {
            mutable.insert(parameter.name.clone());
        }
    }
    let mut context = Context {
        loans: Loans::default(),
        returnable,
        mutable,
        reference_origins,
        allow_local_reference: false,
        reference_types: reference_types.clone(),
        reference_functions: reference_functions.clone(),
        function_names: function_names.clone(),
        return_contains_references: contains_reference_type(&function.return_type, reference_types),
    };
    for statement in &function.body {
        check_statement(statement, &mut context)?;
    }
    Ok(())
}

fn check_statement(statement: &Statement, context: &mut Context) -> Result<(), String> {
    match statement {
        Statement::Let {
            name, ty, value, ..
        } => {
            let contains_references = contains_reference_type(ty, &context.reference_types);
            let origins = reference_origins(value, context, contains_references);
            context.allow_local_reference = true;
            let checked = check_expression(value, context);
            context.allow_local_reference = false;
            checked?;
            for owner in &origins {
                context.loans.borrow(owner, LoanKind::Shared(1))?;
            }
            if origins.is_empty() || !contains_references {
                context.reference_origins.remove(name);
            } else {
                context.reference_origins.insert(name.clone(), origins);
            }
        }
        Statement::Destructure { value, .. } | Statement::LetElse { value, .. } => {
            if !reference_origins(value, context, true).is_empty() {
                return Err("destructuring values that retain references is not supported".into());
            }
            check_expression(value, context)?;
        }
        Statement::Assign { name, value }
        | Statement::FieldAssign { name, value, .. }
        | Statement::TupleAssign { name, value, .. }
        | Statement::EnumPayloadAssign { name, value, .. } => {
            if matches!(statement, Statement::Assign { .. })
                && context.reference_origins.contains_key(name)
            {
                return Err(format!(
                    "cannot replace '{name}' while it retains references"
                ));
            }
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
        Statement::Return(Some(value)) => {
            check_expression(value, context)?;
            for owner in reference_origins(value, context, context.return_contains_references) {
                if !context.returnable.contains(&owner) {
                    return Err(format!(
                        "cannot return a value retaining a reference to local '{owner}'"
                    ));
                }
            }
        }
        Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
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
                            if !context.returnable.contains(owner) && !context.allow_local_reference
                            {
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
                } else if context.function_names.contains(operator) {
                    let previous = context.allow_local_reference;
                    context.allow_local_reference = true;
                    let checked = items[1..]
                        .iter()
                        .try_for_each(|item| check_expression(item, context));
                    context.allow_local_reference = previous;
                    checked?;
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

fn reference_origins(
    expression: &Expr,
    context: &Context,
    result_contains_references: bool,
) -> HashSet<String> {
    if !result_contains_references {
        return HashSet::new();
    }
    match expression {
        Expr::Symbol(name) => context
            .reference_origins
            .get(name)
            .cloned()
            .unwrap_or_default(),
        Expr::List(items) => {
            let Some(Expr::Symbol(operator)) = items.first() else {
                return HashSet::new();
            };
            if matches!(operator.as_str(), "borrow" | "borrow-mut") && items.len() == 2 {
                if let Some(Expr::Symbol(owner)) = items.get(1) {
                    return HashSet::from([owner.clone()]);
                }
            }
            if operator == "get" && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "deref" && items.len() == 2 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "cell-get" && items.len() == 2 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "if" {
                return items
                    .iter()
                    .skip(2)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            if context.reference_types.contains(operator)
                || context.reference_functions.contains(operator)
            {
                return items
                    .iter()
                    .skip(1)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            HashSet::new()
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            let Some(Statement::Expr(value) | Statement::Return(Some(value))) = statements.last()
            else {
                return HashSet::new();
            };
            reference_origins(value, context, true)
        }
        Expr::Labeled { expression, .. } | Expr::Quote(expression) => {
            reference_origins(expression, context, true)
        }
        _ => HashSet::new(),
    }
}

fn type_contains_reference(
    ty: &crate::Type,
    program: &Program,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        crate::Type::Reference { .. } => true,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            type_contains_reference(element, program, seen)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_reference(field, program, seen)),
        crate::Type::Named(name) if seen.insert(name.clone()) => {
            let result = program.items.iter().any(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => fields
                    .iter()
                    .any(|field| type_contains_reference(&field.ty, program, seen)),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_reference(field, program, seen)),
                _ => false,
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn contains_reference_type(ty: &crate::Type, reference_types: &HashSet<String>) -> bool {
    match ty {
        crate::Type::Reference { .. } => true,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            contains_reference_type(element, reference_types)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| contains_reference_type(field, reference_types)),
        crate::Type::Named(name) => reference_types.contains(name),
        _ => false,
    }
}
