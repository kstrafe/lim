use std::collections::{HashMap, HashSet};

use crate::{Expr, Function, Item, Program, Statement, Type};

#[derive(Clone)]
struct Signature {
    parameters: Vec<Type>,
    return_type: Type,
}

pub fn check_types(program: &Program) -> Result<(), String> {
    let mut functions = HashMap::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if functions
            .insert(
                function.name.clone(),
                Signature {
                    parameters: function
                        .parameters
                        .iter()
                        .map(|parameter| parameter.ty.clone())
                        .collect(),
                    return_type: function.return_type.clone(),
                },
            )
            .is_some()
        {
            return Err(format!("duplicate function '{}'", function.name));
        }
    }
    for item in &program.items {
        match item {
            Item::Function(function) => check_function(function, &functions)?,
            Item::Let {
                name, ty, value, ..
            } => {
                let actual = expression(value, &HashMap::new(), &functions, Some(ty))?;
                require_type(&actual, ty, &format!("top-level let '{name}'"))?;
            }
        }
    }
    Ok(())
}

fn check_function(
    function: &Function,
    functions: &HashMap<String, Signature>,
) -> Result<(), String> {
    let mut variables = HashMap::new();
    let mut mutable = HashSet::new();
    for parameter in &function.parameters {
        if variables
            .insert(parameter.name.clone(), parameter.ty.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate parameter '{}' in function '{}'",
                parameter.name, function.name
            ));
        }
    }
    let mut last_type = Type::Unit;
    for (index, statement) in function.body.iter().enumerate() {
        last_type = if index + 1 == function.body.len() {
            if let Statement::Expr(value) = statement {
                expression(value, &variables, functions, Some(&function.return_type))?
            } else {
                statement_type(
                    statement,
                    &mut variables,
                    &mut mutable,
                    functions,
                    &function.return_type,
                    false,
                )?
            }
        } else {
            statement_type(
                statement,
                &mut variables,
                &mut mutable,
                functions,
                &function.return_type,
                false,
            )?
        };
    }
    require_type(
        &last_type,
        &function.return_type,
        &format!("return of function '{}'", function.name),
    )
}

fn statement_type(
    statement: &Statement,
    variables: &mut HashMap<String, Type>,
    mutable: &mut HashSet<String>,
    functions: &HashMap<String, Signature>,
    return_type: &Type,
    in_loop: bool,
) -> Result<Type, String> {
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable: is_mutable,
        } => {
            if variables.contains_key(name) {
                return Err(format!("duplicate local '{name}'"));
            }
            let actual = expression(value, variables, functions, Some(ty))?;
            require_type(&actual, ty, &format!("let '{name}'"))?;
            variables.insert(name.clone(), ty.clone());
            if *is_mutable {
                mutable.insert(name.clone());
            }
            Ok(Type::Unit)
        }
        Statement::Assign { name, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let actual = expression(value, variables, functions, Some(&ty))?;
            require_type(&actual, &ty, &format!("assignment to '{name}'"))?;
            Ok(Type::Unit)
        }
        Statement::While { condition, body } => {
            let actual = expression(condition, variables, functions, Some(&Type::Bool))?;
            require_type(&actual, &Type::Bool, "while condition")?;
            for nested in body {
                statement_type(nested, variables, mutable, functions, return_type, true)?;
            }
            Ok(Type::Unit)
        }
        Statement::Break | Statement::Continue => {
            if in_loop {
                Ok(Type::Unit)
            } else {
                Err("break or continue used outside a loop".into())
            }
        }
        Statement::Return(value) => {
            let actual = match value {
                Some(value) => expression(value, variables, functions, Some(return_type))?,
                None => Type::Unit,
            };
            require_type(&actual, return_type, "return statement")?;
            Ok(return_type.clone())
        }
        Statement::Expr(value) => expression(value, variables, functions, None),
    }
}

fn expression(
    expression: &Expr,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    match expression {
        Expr::Integer(value) => {
            let ty = expected
                .filter(|ty| is_integer(ty))
                .cloned()
                .unwrap_or(Type::I64);
            if !fits_integer(*value, &ty) {
                return Err(format!("integer literal {value} does not fit in {ty:?}"));
            }
            Ok(ty)
        }
        Expr::Symbol(name) if name == "true" || name == "false" => Ok(Type::Bool),
        Expr::Symbol(name) => variables
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown variable '{name}'")),
        Expr::String(_) => Ok(Type::Named("str".into())),
        Expr::At | Expr::Quote(_) => {
            Err("generated and quoted expressions are not typed yet".into())
        }
        Expr::List(items) => list_expression(items, variables, functions, expected),
    }
}

fn list_expression(
    items: &[Expr],
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    let Some(Expr::Symbol(operator)) = items.first() else {
        return Err("expression list must start with a symbol".into());
    };
    match operator.as_str() {
        "+" | "-" | "*" => {
            require_arity(operator, items, 3)?;
            let left = expression(&items[1], variables, functions, expected)?;
            let right = expression(&items[2], variables, functions, Some(&left))?;
            require_same(&left, &right, operator)?;
            if !is_integer(&left) {
                return Err(format!("operator '{operator}' requires integer operands"));
            }
            Ok(left)
        }
        "<" | "<=" | ">" | ">=" | "==" | "!=" => {
            require_arity(operator, items, 3)?;
            let left = expression(&items[1], variables, functions, None)?;
            let right = expression(&items[2], variables, functions, Some(&left))?;
            require_same(&left, &right, operator)?;
            Ok(Type::Bool)
        }
        "if" => {
            require_arity(operator, items, 4)?;
            let condition = expression(&items[1], variables, functions, Some(&Type::Bool))?;
            require_type(&condition, &Type::Bool, "if condition")?;
            let then_type = expression(&items[2], variables, functions, expected)?;
            let else_type = expression(&items[3], variables, functions, Some(&then_type))?;
            require_same(&then_type, &else_type, "if branches")?;
            Ok(then_type)
        }
        "let" => Err("let is only valid as a statement".into()),
        _ => {
            let signature = functions
                .get(operator)
                .ok_or_else(|| format!("unknown function '{operator}'"))?;
            if items.len() - 1 != signature.parameters.len() {
                return Err(format!(
                    "function '{operator}' expects {} arguments",
                    signature.parameters.len()
                ));
            }
            for (argument, parameter_type) in items[1..].iter().zip(&signature.parameters) {
                let actual = expression(argument, variables, functions, Some(parameter_type))?;
                require_type(
                    &actual,
                    parameter_type,
                    &format!("argument to '{operator}'"),
                )?;
            }
            Ok(signature.return_type.clone())
        }
    }
}

fn require_arity(operator: &str, items: &[Expr], expected: usize) -> Result<(), String> {
    if items.len() != expected {
        Err(format!(
            "operator '{operator}' expects {} operands",
            expected - 1
        ))
    } else {
        Ok(())
    }
}

fn require_type(actual: &Type, expected: &Type, context: &str) -> Result<(), String> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "{context} has type {actual:?}, expected {expected:?}"
        ))
    }
}

fn require_same(left: &Type, right: &Type, context: &str) -> Result<(), String> {
    if left == right {
        Ok(())
    } else {
        Err(format!(
            "{context} has mismatched types {left:?} and {right:?}"
        ))
    }
}

fn is_integer(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Isize
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::Usize
    )
}

fn fits_integer(value: i128, ty: &Type) -> bool {
    let (minimum, maximum) = match ty {
        Type::I8 => (i8::MIN as i128, i8::MAX as i128),
        Type::I16 => (i16::MIN as i128, i16::MAX as i128),
        Type::I32 => (i32::MIN as i128, i32::MAX as i128),
        Type::I64 => (i64::MIN as i128, i64::MAX as i128),
        Type::I128 => (i128::MIN, i128::MAX),
        Type::Isize => (isize::MIN as i128, isize::MAX as i128),
        Type::U8 => (0, u8::MAX as i128),
        Type::U16 => (0, u16::MAX as i128),
        Type::U32 => (0, u32::MAX as i128),
        Type::U64 => (0, u64::MAX as i128),
        Type::U128 => (0, i128::MAX),
        Type::Usize => (0, usize::MAX as i128),
        _ => return false,
    };
    (minimum..=maximum).contains(&value)
}
