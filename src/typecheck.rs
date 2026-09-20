use std::collections::{HashMap, HashSet};

use crate::{parse_type, EnumVariant, Expr, Field, Function, Item, Program, Statement, Type};

#[derive(Clone)]
struct Signature {
    type_parameters: Vec<String>,
    parameters: Vec<Type>,
    return_type: Type,
}

pub fn check_types(program: &Program) -> Result<(), String> {
    let mut aliases = HashMap::new();
    for item in &program.items {
        if let Item::TypeAlias { name, target, .. } = item {
            if aliases.insert(name.clone(), target.clone()).is_some() {
                return Err(format!("duplicate type alias '{name}'"));
            }
        }
    }
    let mut globals = HashMap::new();
    for item in &program.items {
        let (name, ty, mutable) = match item {
            Item::Let {
                name, ty, mutable, ..
            } => (name, ty, *mutable),
            Item::Static { name, ty, .. } => (name, ty, false),
            _ => continue,
        };
        {
            if mutable {
                return Err(format!("top-level binding '{name}' cannot be mutable"));
            }
            if globals
                .insert(name.clone(), resolve_type(ty, &aliases)?)
                .is_some()
            {
                return Err(format!("duplicate global '{name}'"));
            }
        }
    }
    let mut structs = HashMap::new();
    for item in &program.items {
        if let Item::Struct { name, fields, .. } = item {
            let mut field_names = HashSet::new();
            let fields = fields
                .iter()
                .map(|field| {
                    if !field_names.insert(field.name.clone()) {
                        return Err(format!(
                            "duplicate field '{}' in struct '{name}'",
                            field.name
                        ));
                    }
                    Ok(Field {
                        name: field.name.clone(),
                        ty: resolve_type(&field.ty, &aliases)?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            if structs.insert(name.clone(), fields).is_some() {
                return Err(format!("duplicate struct '{name}'"));
            }
        }
    }
    let mut enums = HashMap::new();
    let mut variant_names = HashMap::new();
    for item in &program.items {
        if let Item::Enum { name, variants, .. } = item {
            let mut local_variant_names = HashSet::new();
            let variants = variants
                .iter()
                .map(|variant| {
                    if !local_variant_names.insert(variant.name.clone()) {
                        return Err(format!(
                            "duplicate variant '{}' in enum '{name}'",
                            variant.name
                        ));
                    }
                    if let Some(previous) = variant_names.insert(variant.name.clone(), name.clone())
                    {
                        return Err(format!(
                            "variant '{}' is already defined in enum '{previous}'",
                            variant.name
                        ));
                    }
                    Ok(EnumVariant {
                        name: variant.name.clone(),
                        fields: variant
                            .fields
                            .iter()
                            .map(|field| resolve_type(field, &aliases))
                            .collect::<Result<Vec<_>, _>>()?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            if enums.insert(name.clone(), variants).is_some() {
                return Err(format!("duplicate enum '{name}'"));
            }
        }
    }
    let mut functions = HashMap::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if functions
            .insert(
                function.name.clone(),
                Signature {
                    type_parameters: function.type_parameters.clone(),
                    parameters: function
                        .parameters
                        .iter()
                        .map(|parameter| resolve_type(&parameter.ty, &aliases))
                        .collect::<Result<Vec<_>, String>>()?,
                    return_type: resolve_type(&function.return_type, &aliases)?,
                },
            )
            .is_some()
        {
            return Err(format!("duplicate function '{}'", function.name));
        }
    }
    for item in &program.items {
        match item {
            Item::Function(function) => {
                check_function(function, &functions, &structs, &enums, &globals, &aliases)?
            }
            Item::TypeAlias { .. } | Item::Struct { .. } | Item::Enum { .. } => {}
            Item::Let { name, value, .. } | Item::Static { name, value, .. } => {
                let ty = globals.get(name).expect("global type collected");
                let actual = expression(
                    value,
                    &globals,
                    &functions,
                    &structs,
                    &enums,
                    &HashSet::new(),
                    &aliases,
                    Some(ty),
                )?;
                require_type(&actual, ty, &format!("top-level let '{name}'"))?;
            }
        }
    }
    Ok(())
}

fn check_function(
    function: &Function,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    globals: &HashMap<String, Type>,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    let mut variables = globals.clone();
    let mut mutable = HashSet::new();
    let return_type = resolve_type(&function.return_type, aliases)?;
    for parameter in &function.parameters {
        if variables
            .insert(
                parameter.name.clone(),
                resolve_type(&parameter.ty, aliases)?,
            )
            .is_some()
        {
            return Err(format!(
                "duplicate parameter '{}' in function '{}'",
                parameter.name, function.name
            ));
        }
        if parameter.mutable {
            mutable.insert(parameter.name.clone());
        }
    }
    let mut last_type = Type::Unit;
    for (index, statement) in function.body.iter().enumerate() {
        last_type = if index + 1 == function.body.len() {
            if let Statement::Expr(value) = statement {
                expression(
                    value,
                    &variables,
                    functions,
                    structs,
                    enums,
                    &mutable,
                    aliases,
                    Some(&return_type),
                )?
            } else {
                statement_type(
                    statement,
                    &mut variables,
                    &mut mutable,
                    functions,
                    structs,
                    enums,
                    &return_type,
                    aliases,
                    false,
                )?
            }
        } else {
            statement_type(
                statement,
                &mut variables,
                &mut mutable,
                functions,
                structs,
                enums,
                &return_type,
                aliases,
                false,
            )?
        };
    }
    require_type(
        &last_type,
        &return_type,
        &format!("return of function '{}'", function.name),
    )
}

fn statement_type(
    statement: &Statement,
    variables: &mut HashMap<String, Type>,
    mutable: &mut HashSet<String>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    return_type: &Type,
    aliases: &HashMap<String, Type>,
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
            let binding_type = resolve_type(ty, aliases)?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&binding_type),
            )?;
            require_type(&actual, &binding_type, &format!("let '{name}'"))?;
            variables.insert(name.clone(), binding_type);
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
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&ty),
            )?;
            require_type(&actual, &ty, &format!("assignment to '{name}'"))?;
            Ok(Type::Unit)
        }
        Statement::ArrayAssign { name, index, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Array(element, length) = ty else {
                return Err(format!("'{name}' is not an array"));
            };
            check_index(
                index, length, variables, functions, structs, enums, mutable, aliases,
            )?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&element),
            )?;
            require_type(&actual, &element, &format!("array assignment to '{name}'"))?;
            Ok(Type::Unit)
        }
        Statement::FieldAssign { name, field, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Named(struct_name) = ty else {
                return Err(format!("'{name}' is not a struct"));
            };
            let fields = structs
                .get(&struct_name)
                .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
            let field_type = fields
                .iter()
                .find(|field_info| field_info.name == *field)
                .map(|field_info| field_info.ty.clone())
                .ok_or_else(|| format!("struct '{struct_name}' has no field '{field}'"))?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&field_type),
            )?;
            require_type(
                &actual,
                &field_type,
                &format!("assignment to field '{field}'"),
            )?;
            Ok(Type::Unit)
        }
        Statement::TupleAssign { name, index, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Tuple(fields) = ty else {
                return Err(format!("'{name}' is not a tuple"));
            };
            let field_type = fields
                .get(*index)
                .ok_or_else(|| format!("tuple field index {index} is out of bounds"))?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(field_type),
            )?;
            require_type(
                &actual,
                field_type,
                &format!("assignment to tuple field {index}"),
            )?;
            Ok(Type::Unit)
        }
        Statement::While { condition, body } => {
            let actual = expression(
                condition,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&actual, &Type::Bool, "while condition")?;
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            for nested in body {
                statement_type(
                    nested,
                    &mut loop_variables,
                    &mut loop_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    true,
                )?;
            }
            Ok(Type::Unit)
        }
        Statement::Loop { body } => {
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            for nested in body {
                statement_type(
                    nested,
                    &mut loop_variables,
                    &mut loop_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    true,
                )?;
            }
            Ok(Type::Unit)
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            statement_type(
                init,
                &mut loop_variables,
                &mut loop_mutable,
                functions,
                structs,
                enums,
                return_type,
                aliases,
                false,
            )?;
            let actual = expression(
                condition,
                &loop_variables,
                functions,
                structs,
                enums,
                &loop_mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&actual, &Type::Bool, "for condition")?;
            for nested in body {
                statement_type(
                    nested,
                    &mut loop_variables,
                    &mut loop_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    true,
                )?;
            }
            statement_type(
                step,
                &mut loop_variables,
                &mut loop_mutable,
                functions,
                structs,
                enums,
                return_type,
                aliases,
                true,
            )?;
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
                Some(value) => expression(
                    value,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(return_type),
                )?,
                None => Type::Unit,
            };
            require_type(&actual, return_type, "return statement")?;
            Ok(return_type.clone())
        }
        Statement::Expr(value) => expression(
            value, variables, functions, structs, enums, mutable, aliases, None,
        ),
    }
}

fn expression(
    value: &Expr,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    match value {
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
        Expr::UnsignedInteger(value) => {
            let ty = expected
                .filter(|ty| is_integer(ty))
                .cloned()
                .unwrap_or(Type::U128);
            if !fits_unsigned_integer(*value, &ty) {
                return Err(format!("integer literal {value} does not fit in {ty:?}"));
            }
            Ok(ty)
        }
        Expr::Float(value) => {
            let ty = expected
                .filter(|ty| matches!(ty, Type::F32 | Type::F64))
                .cloned()
                .unwrap_or(Type::F64);
            let finite = if matches!(ty, Type::F32) {
                value
                    .parse::<f32>()
                    .map_err(|_| format!("invalid floating-point literal '{value}'"))?
                    .is_finite()
            } else {
                value
                    .parse::<f64>()
                    .map_err(|_| format!("invalid floating-point literal '{value}'"))?
                    .is_finite()
            };
            if !finite {
                return Err(format!(
                    "floating-point literal '{value}' is not finite for {ty:?}"
                ));
            }
            Ok(ty)
        }
        Expr::Char(_) => Ok(Type::Char),
        Expr::Symbol(name) if name == "true" || name == "false" => Ok(Type::Bool),
        Expr::Symbol(name) => variables
            .get(name)
            .cloned()
            .or_else(|| enum_variant_type(name, enums))
            .ok_or_else(|| format!("unknown variable or enum variant '{name}'")),
        Expr::String(_) => Ok(Type::Named("str".into())),
        Expr::Block(statements) => {
            let mut block_variables = variables.clone();
            let mut block_mutable = mutable.clone();
            let block_return = expected.cloned().unwrap_or(Type::Unit);
            let mut result = Type::Unit;
            for (index, statement) in statements.iter().enumerate() {
                result = if index + 1 == statements.len() {
                    if let Statement::Expr(value) = statement {
                        expression(
                            value,
                            &block_variables,
                            functions,
                            structs,
                            enums,
                            &block_mutable,
                            aliases,
                            expected,
                        )?
                    } else {
                        statement_type(
                            statement,
                            &mut block_variables,
                            &mut block_mutable,
                            functions,
                            structs,
                            enums,
                            &block_return,
                            aliases,
                            false,
                        )?
                    }
                } else {
                    statement_type(
                        statement,
                        &mut block_variables,
                        &mut block_mutable,
                        functions,
                        structs,
                        enums,
                        &block_return,
                        aliases,
                        false,
                    )?
                };
            }
            Ok(result)
        }
        Expr::At | Expr::Quote(_) => {
            Err("generated and quoted expressions are not typed yet".into())
        }
        Expr::List(items) => list_expression(
            items, variables, functions, structs, enums, mutable, aliases, expected,
        ),
    }
}

fn list_expression(
    items: &[Expr],
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    if items.is_empty() {
        return Ok(Type::Unit);
    }
    let Some(Expr::Symbol(operator)) = items.first() else {
        return Err("expression list must start with a symbol".into());
    };
    match operator.as_str() {
        "-" if items.len() == 2 => {
            let actual = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            if !is_numeric(&actual) {
                return Err("unary '-' requires a numeric operand".into());
            }
            Ok(actual)
        }
        "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" => {
            require_arity(operator, items, 3)?;
            let left = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            let right = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&left),
            )?;
            require_same(&left, &right, operator)?;
            let bitwise = matches!(operator.as_str(), "&" | "|" | "^");
            let valid = if bitwise {
                is_integer(&left) || matches!(left, Type::Bool)
            } else {
                is_numeric(&left)
            };
            if !valid {
                return Err(format!(
                    "operator '{operator}' requires integer or boolean operands"
                ));
            }
            if matches!(operator.as_str(), "<<" | ">>") {
                if let Expr::Integer(count) = &items[2] {
                    if *count < 0 || integer_width(&left).is_some_and(|width| *count >= width) {
                        return Err(format!("shift count {count} is out of range for {left:?}"));
                    }
                }
            }
            Ok(left)
        }
        "<" | "<=" | ">" | ">=" | "==" | "!=" => {
            require_arity(operator, items, 3)?;
            let left = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let right = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&left),
            )?;
            require_same(&left, &right, operator)?;
            Ok(Type::Bool)
        }
        "if" => {
            if items.len() != 3 && items.len() != 4 {
                return Err(
                    "if requires a condition, then expression, and optional else expression".into(),
                );
            }
            let condition = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&condition, &Type::Bool, "if condition")?;
            let then_type = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                if items.len() == 3 {
                    Some(&Type::Unit)
                } else {
                    expected
                },
            )?;
            if items.len() == 3 {
                require_type(&then_type, &Type::Unit, "if without else")?;
                return Ok(Type::Unit);
            }
            let else_type = expression(
                &items[3],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&then_type),
            )?;
            require_same(&then_type, &else_type, "if branches")?;
            Ok(then_type)
        }
        "as" => {
            require_arity(operator, items, 3)?;
            let source = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let target = resolve_type(&parse_type(items.get(2))?, aliases)?;
            if !is_cast_operand(&source) || !is_cast_target(&target) {
                return Err(
                    "as requires numeric, char, or bool operands and a numeric or char target"
                        .into(),
                );
            }
            Ok(target)
        }
        "size-of" | "align-of" => {
            require_arity(operator, items, 2)?;
            let ty = resolve_type(&parse_type(items.get(1))?, aliases)?;
            validate_layout_type(&ty, structs, enums)?;
            Ok(Type::Usize)
        }
        "array" => {
            let Some(Type::Array(element, length)) = expected else {
                return Err(
                    "array construction requires an expected (array Element N) type".into(),
                );
            };
            if items.len() - 1 != *length {
                return Err(format!("array constructor expects {length} elements"));
            }
            for value in &items[1..] {
                let actual = expression(
                    value,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(element),
                )?;
                require_type(&actual, element, "array element")?;
            }
            Ok(Type::Array(element.clone(), *length))
        }
        "array-repeat" => {
            let Some(Type::Array(element, length)) = expected else {
                return Err(
                    "array-repeat construction requires an expected (array Element N) type".into(),
                );
            };
            require_arity(operator, items, 2)?;
            let actual = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(element),
            )?;
            require_type(&actual, element, "array-repeat element")?;
            Ok(Type::Array(element.clone(), *length))
        }
        "tuple" => {
            let fields = match expected {
                Some(Type::Tuple(fields)) => fields.clone(),
                Some(_) => {
                    return Err("tuple construction requires an expected (tuple ...) type".into())
                }
                None => items[1..]
                    .iter()
                    .map(|value| {
                        expression(
                            value, variables, functions, structs, enums, mutable, aliases, None,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            };
            if items.len() - 1 != fields.len() {
                return Err(format!(
                    "tuple constructor expects {} elements",
                    fields.len()
                ));
            }
            for (value, field) in items[1..].iter().zip(fields.iter()) {
                let actual = expression(
                    value,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(field),
                )?;
                require_type(&actual, field, "tuple element")?;
            }
            Ok(Type::Tuple(fields))
        }
        "index" => {
            if items.len() != 3 {
                return Err("index requires the form (index array index)".into());
            }
            let Type::Array(element, length) = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err("index requires an array".into());
            };
            check_index(
                &items[2], length, variables, functions, structs, enums, mutable, aliases,
            )?;
            Ok(*element)
        }
        "match" => {
            if items.len() < 3 {
                return Err("match requires a value and at least one arm".into());
            }
            let scrutinee = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::Named(enum_name) = &scrutinee else {
                if !is_matchable_scalar(&scrutinee) {
                    return Err("match requires an enum or scalar value".into());
                }
                return check_scalar_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            };
            if !enums.contains_key(enum_name) {
                if !is_matchable_scalar(&scrutinee) {
                    return Err("match requires an enum or scalar value".into());
                }
                return check_scalar_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            }
            let variants = enums
                .get(enum_name)
                .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
            let mut wildcard = false;
            let mut seen = Vec::new();
            let mut result_type = None;
            for arm in &items[2..] {
                let arm = match arm {
                    Expr::List(arm) if arm.len() == 2 => arm,
                    _ => return Err("match arms must have the form (pattern expression)".into()),
                };
                let (pattern, payload_patterns) = match &arm[0] {
                    Expr::Symbol(pattern) => (pattern.as_str(), Vec::new()),
                    Expr::List(pattern) if !pattern.is_empty() => {
                        let variant = match &pattern[0] {
                            Expr::Symbol(variant) => variant.as_str(),
                            _ => return Err("match variant pattern must be a symbol".into()),
                        };
                        let payloads = pattern[1..]
                            .iter()
                            .map(|payload| match payload {
                                Expr::Symbol(payload) => Ok(payload.as_str()),
                                _ => Err("match payload pattern must be a symbol".to_owned()),
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        (variant, payloads)
                    }
                    _ => return Err("match pattern must be a symbol or (variant _)".into()),
                };
                if pattern == "_" {
                    if !payload_patterns.is_empty() {
                        return Err("wildcard pattern cannot have a payload".into());
                    }
                    if wildcard {
                        return Err("duplicate wildcard match pattern".into());
                    }
                    wildcard = true;
                } else {
                    let Some(variant) = variants.iter().find(|variant| variant.name == pattern)
                    else {
                        return Err(format!("'{pattern}' is not a variant of '{enum_name}'"));
                    };
                    if !payload_patterns.is_empty()
                        && payload_patterns.len() != variant.fields.len()
                    {
                        return Err(format!(
                            "variant '{pattern}' expects {} payload patterns",
                            variant.fields.len()
                        ));
                    }
                    if seen.iter().any(|seen: &&str| *seen == pattern) {
                        return Err(format!("duplicate enum match pattern '{pattern}'"));
                    }
                    seen.push(pattern);
                }
                let mut arm_variables = variables.clone();
                if !payload_patterns.is_empty() {
                    let variant = variants
                        .iter()
                        .find(|variant| variant.name == pattern)
                        .ok_or_else(|| format!("unknown variant '{pattern}'"))?;
                    for (binding, field_type) in payload_patterns.iter().zip(&variant.fields) {
                        if *binding == "_" {
                            continue;
                        }
                        if arm_variables
                            .insert((*binding).to_owned(), field_type.clone())
                            .is_some()
                        {
                            return Err(format!("duplicate match binding '{binding}'"));
                        }
                    }
                }
                let arm_type = expression(
                    &arm[1],
                    &arm_variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    result_type.as_ref().or(expected),
                )?;
                if let Some(previous) = &result_type {
                    require_same(previous, &arm_type, "match arms")?;
                } else {
                    result_type = Some(arm_type);
                }
            }
            if !wildcard && seen.len() != variants.len() {
                return Err("match is not exhaustive; add '_' arm".into());
            }
            Ok(result_type.unwrap_or(Type::Unit))
        }
        "!" => {
            require_arity(operator, items, 2)?;
            let operand = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            if !matches!(operand, Type::Bool) && !is_integer(&operand) {
                return Err("! operand must be a boolean or integer".into());
            }
            Ok(operand)
        }
        "&&" | "||" => {
            require_arity(operator, items, 3)?;
            for operand in &items[1..] {
                let actual = expression(
                    operand,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(&Type::Bool),
                )?;
                require_type(&actual, &Type::Bool, &format!("{operator} operand"))?;
            }
            Ok(Type::Bool)
        }
        "assert" | "debug-assert" => {
            require_arity(operator, items, 2)?;
            let actual = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&actual, &Type::Bool, &format!("{operator} condition"))?;
            Ok(Type::Unit)
        }
        "let" => Err("let is only valid as a statement".into()),
        "get" => {
            if items.len() != 3 {
                return Err("get requires the form (get value field)".into());
            }
            let value_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            if let Type::Tuple(fields) = value_type {
                let index = match &items[2] {
                    Expr::Integer(index) if *index >= 0 => usize::try_from(*index)
                        .map_err(|_| "tuple field index is too large".to_owned())?,
                    _ => return Err("tuple get requires a non-negative integer index".into()),
                };
                return fields
                    .get(index)
                    .cloned()
                    .ok_or_else(|| format!("tuple field index {index} is out of bounds"));
            }
            let Type::Named(struct_name) = value_type else {
                return Err("get requires a struct or tuple value".into());
            };
            let field_name = match &items[2] {
                Expr::Symbol(name) => name,
                _ => return Err("get requires a field name".into()),
            };
            let fields = structs
                .get(&struct_name)
                .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
            fields
                .iter()
                .find(|field| field.name == *field_name)
                .map(|field| field.ty.clone())
                .ok_or_else(|| format!("struct '{struct_name}' has no field '{field_name}'"))
        }
        _ => {
            if let Some(fields) = structs.get(operator) {
                if items.len() - 1 != fields.len() {
                    return Err(format!(
                        "constructor '{operator}' expects {} fields",
                        fields.len()
                    ));
                }
                for (argument, field) in items[1..].iter().zip(fields) {
                    let actual = expression(
                        argument,
                        variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        Some(&field.ty),
                    )?;
                    require_type(
                        &actual,
                        &field.ty,
                        &format!("field '{}' of '{operator}'", field.name),
                    )?;
                }
                return Ok(Type::Named(operator.clone()));
            }
            for (enum_name, variants) in enums {
                let Some(variant) = variants.iter().find(|variant| variant.name == *operator)
                else {
                    continue;
                };
                if items.len() - 1 != variant.fields.len() {
                    return Err(format!(
                        "variant '{operator}' expects {} payloads",
                        variant.fields.len()
                    ));
                }
                for (argument, field_type) in items[1..].iter().zip(&variant.fields) {
                    let actual = expression(
                        argument,
                        variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        Some(field_type),
                    )?;
                    require_type(&actual, field_type, &format!("payload of '{operator}'"))?;
                }
                return Ok(Type::Named(enum_name.clone()));
            }
            let (function_name, type_arguments) = split_generic_call(operator)?;
            let signature = functions
                .get(&function_name)
                .ok_or_else(|| format!("unknown function '{operator}'"))?;
            let substitutions = generic_substitutions(signature, &type_arguments, aliases)?;
            let parameter_types = signature
                .parameters
                .iter()
                .map(|parameter| substitute_type(parameter, &substitutions))
                .collect::<Vec<_>>();
            let return_type = substitute_type(&signature.return_type, &substitutions);
            if items.len() - 1 != signature.parameters.len() {
                return Err(format!(
                    "function '{operator}' expects {} arguments",
                    parameter_types.len()
                ));
            }
            for (argument, parameter_type) in items[1..].iter().zip(&parameter_types) {
                let actual = expression(
                    argument,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(parameter_type),
                )?;
                require_type(
                    &actual,
                    parameter_type,
                    &format!("argument to '{operator}'"),
                )?;
            }
            Ok(return_type)
        }
    }
}

fn check_scalar_match(
    items: &[Expr],
    scrutinee: &Type,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    let mut wildcard = false;
    let mut seen_bool = [false, false];
    let mut seen_integers = HashSet::new();
    let mut seen_chars = HashSet::new();
    let mut result_type = None;
    for arm in &items[2..] {
        let arm = match arm {
            Expr::List(arm) if arm.len() == 2 => arm,
            _ => return Err("match arms must have the form (pattern expression)".into()),
        };
        match &arm[0] {
            Expr::Symbol(pattern) if pattern == "_" => {
                if wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                wildcard = true;
            }
            Expr::Symbol(pattern) if matches!(scrutinee, Type::Bool) => {
                let index = match pattern.as_str() {
                    "false" => 0,
                    "true" => 1,
                    _ => return Err("boolean match pattern must be true, false, or _".into()),
                };
                if seen_bool[index] {
                    return Err(format!("duplicate boolean match pattern '{pattern}'"));
                }
                seen_bool[index] = true;
            }
            Expr::Integer(value) if is_integer(scrutinee) => {
                if !fits_integer(*value, scrutinee) {
                    return Err(format!(
                        "integer match pattern {value} does not fit in {scrutinee:?}"
                    ));
                }
                if !seen_integers.insert(*value) {
                    return Err(format!("duplicate integer match pattern {value}"));
                }
            }
            Expr::Char(value) if matches!(scrutinee, Type::Char) => {
                if !seen_chars.insert(*value) {
                    return Err(format!("duplicate character match pattern {value:?}"));
                }
            }
            _ => return Err("scalar match pattern does not match the scrutinee type".into()),
        }
        let arm_type = expression(
            &arm[1],
            variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type.as_ref().or(expected),
        )?;
        if let Some(previous) = &result_type {
            require_same(previous, &arm_type, "match arms")?;
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard && !(matches!(scrutinee, Type::Bool) && seen_bool.iter().all(|seen| *seen)) {
        return Err("match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
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

fn split_generic_call(operator: &str) -> Result<(String, Vec<String>), String> {
    let Some(open) = operator.find('<') else {
        return Ok((operator.to_owned(), Vec::new()));
    };
    if !operator.ends_with('>') || open == 0 {
        return Err(format!("malformed generic call '{operator}'"));
    }
    let name = operator[..open].to_owned();
    let arguments = &operator[open + 1..operator.len() - 1];
    if arguments.is_empty() {
        return Err(format!("generic call '{operator}' has no type arguments"));
    }
    let arguments = arguments
        .split(',')
        .map(str::trim)
        .map(|argument| {
            if argument.is_empty() {
                Err(format!(
                    "generic call '{operator}' has an empty type argument"
                ))
            } else {
                Ok(argument.to_owned())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((name, arguments))
}

fn generic_substitutions(
    signature: &Signature,
    arguments: &[String],
    aliases: &HashMap<String, Type>,
) -> Result<HashMap<String, Type>, String> {
    if signature.type_parameters.len() != arguments.len() {
        if signature.type_parameters.is_empty() && arguments.is_empty() {
            return Ok(HashMap::new());
        }
        return Err(format!(
            "generic function expects {} type arguments, got {}",
            signature.type_parameters.len(),
            arguments.len()
        ));
    }
    signature
        .type_parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            let ty = resolve_type(&Type::from_name(argument), aliases)?;
            if matches!(ty, Type::Generic(_)) {
                return Err(format!(
                    "generic type argument '{argument}' is not concrete"
                ));
            }
            Ok((parameter.clone(), ty))
        })
        .collect()
}

fn substitute_type(ty: &Type, substitutions: &HashMap<String, Type>) -> Type {
    match ty {
        Type::Generic(name) => substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        Type::Array(element, length) => {
            Type::Array(Box::new(substitute_type(element, substitutions)), *length)
        }
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|field| substitute_type(field, substitutions))
                .collect(),
        ),
        _ => ty.clone(),
    }
}

fn resolve_type(ty: &Type, aliases: &HashMap<String, Type>) -> Result<Type, String> {
    resolve_type_with_seen(ty, aliases, &mut HashSet::new())
}

fn resolve_type_with_seen(
    ty: &Type,
    aliases: &HashMap<String, Type>,
    seen: &mut HashSet<String>,
) -> Result<Type, String> {
    match ty {
        Type::Named(name) => {
            let Some(target) = aliases.get(name) else {
                return Ok(ty.clone());
            };
            if !seen.insert(name.clone()) {
                return Err(format!("type alias '{name}' is recursive"));
            }
            let result = resolve_type_with_seen(target, aliases, seen);
            seen.remove(name);
            result
        }
        Type::Array(element, length) => Ok(Type::Array(
            Box::new(resolve_type_with_seen(element, aliases, seen)?),
            *length,
        )),
        Type::Tuple(fields) => Ok(Type::Tuple(
            fields
                .iter()
                .map(|field| resolve_type_with_seen(field, aliases, seen))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        _ => Ok(ty.clone()),
    }
}

fn validate_layout_type(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<(), String> {
    match ty {
        Type::Named(name) if structs.contains_key(name) => structs
            .get(name)
            .into_iter()
            .flat_map(|fields| fields.iter())
            .try_for_each(|field| validate_layout_type(&field.ty, structs, enums)),
        Type::Named(name) if enums.contains_key(name) => enums
            .get(name)
            .into_iter()
            .flat_map(|variants| variants.iter())
            .flat_map(|variant| variant.fields.iter())
            .try_for_each(|field| validate_layout_type(field, structs, enums)),
        Type::Named(name) => Err(format!("unknown type '{name}' in size-of")),
        Type::Array(element, _) => validate_layout_type(element, structs, enums),
        Type::Tuple(fields) => fields
            .iter()
            .try_for_each(|field| validate_layout_type(field, structs, enums)),
        Type::Generic(name) => Err(format!("generic type '{name}' has no concrete size")),
        _ => Ok(()),
    }
}

fn enum_variant_type(name: &str, enums: &HashMap<String, Vec<EnumVariant>>) -> Option<Type> {
    enums.iter().find_map(|(enum_name, variants)| {
        variants
            .iter()
            .any(|variant| variant.name == name)
            .then(|| Type::Named(enum_name.clone()))
    })
}

fn check_index(
    index: &Expr,
    length: usize,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    let actual = expression(
        index, variables, functions, structs, enums, mutable, aliases, None,
    )?;
    if !is_integer(&actual) {
        return Err("array index must be an integer".into());
    }
    if let Expr::Integer(value) = index {
        if *value < 0 || *value >= length as i128 {
            return Err(format!(
                "array index {value} is out of bounds for length {length}"
            ));
        }
    }
    Ok(())
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

fn is_numeric(ty: &Type) -> bool {
    is_integer(ty) || matches!(ty, Type::F32 | Type::F64)
}

fn is_matchable_scalar(ty: &Type) -> bool {
    is_integer(ty) || matches!(ty, Type::Bool | Type::Char)
}

fn integer_width(ty: &Type) -> Option<i128> {
    match ty {
        Type::I8 | Type::U8 => Some(8),
        Type::I16 | Type::U16 => Some(16),
        Type::I32 | Type::U32 => Some(32),
        Type::I64 | Type::U64 | Type::Isize | Type::Usize => Some(64),
        Type::I128 | Type::U128 => Some(128),
        _ => None,
    }
}

fn is_cast_operand(ty: &Type) -> bool {
    is_numeric(ty) || matches!(ty, Type::Bool | Type::Char)
}

fn is_cast_target(ty: &Type) -> bool {
    is_numeric(ty) || matches!(ty, Type::Char)
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

fn fits_unsigned_integer(value: u128, ty: &Type) -> bool {
    let maximum = match ty {
        Type::I8 => i8::MAX as u128,
        Type::I16 => i16::MAX as u128,
        Type::I32 => i32::MAX as u128,
        Type::I64 => i64::MAX as u128,
        Type::I128 => i128::MAX as u128,
        Type::Isize => isize::MAX as u128,
        Type::U8 => u8::MAX as u128,
        Type::U16 => u16::MAX as u128,
        Type::U32 => u32::MAX as u128,
        Type::U64 => u64::MAX as u128,
        Type::U128 => u128::MAX,
        Type::Usize => usize::MAX as u128,
        _ => return false,
    };
    value <= maximum
}
