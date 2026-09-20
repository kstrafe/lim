use std::collections::{HashMap, HashSet};

use crate::{parse_type, EnumVariant, Expr, Field, Function, Item, Program, Statement, Type};

#[derive(Clone)]
struct Signature {
    parameters: Vec<Type>,
    return_type: Type,
}

pub fn check_types(program: &Program) -> Result<(), String> {
    let mut aliases = HashMap::new();
    for item in &program.items {
        if let Item::TypeAlias { name, target } = item {
            if aliases.insert(name.clone(), target.clone()).is_some() {
                return Err(format!("duplicate type alias '{name}'"));
            }
        }
    }
    let mut globals = HashMap::new();
    for item in &program.items {
        if let Item::Let {
            name, ty, mutable, ..
        } = item
        {
            if *mutable {
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
        if let Item::Struct { name, fields } = item {
            let fields = fields
                .iter()
                .map(|field| {
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
    for item in &program.items {
        if let Item::Enum { name, variants } = item {
            if enums.insert(name.clone(), variants.clone()).is_some() {
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
            Item::Let { name, value, .. } => {
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
            for nested in body {
                statement_type(
                    nested,
                    variables,
                    mutable,
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
            for nested in body {
                statement_type(
                    nested,
                    variables,
                    mutable,
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
            statement_type(
                init,
                variables,
                mutable,
                functions,
                structs,
                enums,
                return_type,
                aliases,
                false,
            )?;
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
            require_type(&actual, &Type::Bool, "for condition")?;
            for nested in body {
                statement_type(
                    nested,
                    variables,
                    mutable,
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
                variables,
                mutable,
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
        Expr::Float(value) => {
            let ty = expected
                .filter(|ty| matches!(ty, Type::F32 | Type::F64))
                .cloned()
                .unwrap_or(Type::F64);
            let parsed = value
                .parse::<f64>()
                .map_err(|_| format!("invalid floating-point literal '{value}'"))?;
            if matches!(ty, Type::F32) && !parsed.is_finite() {
                return Err(format!(
                    "floating-point literal '{value}' is not a finite f32"
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
            if !is_numeric(&left) {
                return Err(format!("operator '{operator}' requires numeric operands"));
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
            require_arity(operator, items, 4)?;
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
                &items[2], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
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
                    if !seen.iter().any(|seen: &&str| *seen == pattern) {
                        seen.push(pattern);
                    }
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
            Ok(signature.return_type.clone())
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
    let mut result_type = None;
    for arm in &items[2..] {
        let arm = match arm {
            Expr::List(arm) if arm.len() == 2 => arm,
            _ => return Err("match arms must have the form (pattern expression)".into()),
        };
        match &arm[0] {
            Expr::Symbol(pattern) if pattern == "_" => wildcard = true,
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
            }
            Expr::Char(_) if matches!(scrutinee, Type::Char) => {}
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

fn resolve_type(ty: &Type, aliases: &HashMap<String, Type>) -> Result<Type, String> {
    match ty {
        Type::Named(name) => match aliases.get(name) {
            Some(target) if target != ty => resolve_type(target, aliases),
            Some(_) => Err(format!("type alias '{name}' is recursive")),
            None => Ok(ty.clone()),
        },
        Type::Array(element, length) => Ok(Type::Array(
            Box::new(resolve_type(element, aliases)?),
            *length,
        )),
        Type::Tuple(fields) => Ok(Type::Tuple(
            fields
                .iter()
                .map(|field| resolve_type(field, aliases))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        _ => Ok(ty.clone()),
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
