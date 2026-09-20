//! Small native x86-64 backend for the currently supported integer subset.
//!
//! The backend emits GNU assembler syntax in Intel mode and follows the Linux
//! System V ABI. It intentionally rejects types and expressions that do not
//! have a representation in this first backend instead of silently generating
//! incorrect code.

use std::collections::HashMap;

use crate::{check_types, EnumVariant, Expr, Field, Function, Item, Program, Statement, Type};

const ARGUMENT_REGISTERS: [&str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
const VALUE_REGISTERS: [&str; 6] = ["rax", "rdx", "rcx", "r8", "r9", "rdi"];
const FLOAT_ARGUMENT_REGISTERS: [&str; 8] = [
    "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7",
];

#[derive(Clone)]
struct FunctionAbi {
    parameters: Vec<Type>,
    return_type: Type,
}

pub fn generate_assembly(program: &Program) -> Result<String, String> {
    check_types(program)?;
    let aliases: HashMap<String, Type> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target } => Some((name.clone(), target.clone())),
            _ => None,
        })
        .collect();
    let structs: HashMap<String, Vec<Field>> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields } => Some((
                name.clone(),
                fields
                    .iter()
                    .map(|field| Field {
                        name: field.name.clone(),
                        ty: resolve_type(&field.ty, &aliases).unwrap_or_else(|_| field.ty.clone()),
                    })
                    .collect(),
            )),
            _ => None,
        })
        .collect();
    let enums: HashMap<String, Vec<EnumVariant>> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { name, variants } => Some((name.clone(), variants.clone())),
            _ => None,
        })
        .collect();
    let mut functions = HashMap::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let parameters = function
            .parameters
            .iter()
            .map(|parameter| resolve_type(&parameter.ty, &aliases))
            .collect::<Result<Vec<_>, _>>()?;
        let return_type = resolve_type(&function.return_type, &aliases)?;
        functions.insert(
            function.name.clone(),
            FunctionAbi {
                parameters,
                return_type,
            },
        );
    }
    let mut globals = HashMap::new();
    for item in &program.items {
        if let Item::Let {
            name,
            ty,
            value,
            mutable,
        } = item
        {
            if *mutable {
                return Err(format!("top-level binding '{name}' cannot be mutable"));
            }
            ensure_scalar_type(&resolve_type(ty, &aliases)?, &enums)?;
            let value = constant_value(value, &enums)?;
            globals.insert(name.clone(), value);
        }
    }
    let mut output = String::from(".intel_syntax noprefix\n");
    if !globals.is_empty() {
        output.push_str(".section .rodata\n");
        for (name, value) in &globals {
            output.push_str(&format!(".align 8\n{name}:\n    .quad {value}\n"));
        }
    }
    output.push_str(".text\n");
    for item in &program.items {
        match item {
            Item::Function(function) => generate_function(
                function,
                &mut output,
                &structs,
                &enums,
                &globals,
                &aliases,
                &functions,
            )?,
            Item::Struct { .. } => {}
            Item::Enum { .. } => {}
            Item::TypeAlias { .. } => {}
            Item::Let { .. } => {}
        }
    }
    output.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    Ok(output)
}

fn generate_function(
    function: &Function,
    output: &mut String,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    globals: &HashMap<String, i128>,
    aliases: &HashMap<String, Type>,
    functions: &HashMap<String, FunctionAbi>,
) -> Result<(), String> {
    let return_type = resolve_type(&function.return_type, aliases)?;
    ensure_return_type(&return_type, enums, structs)?;
    for parameter in &function.parameters {
        let parameter_type = resolve_type(&parameter.ty, aliases)?;
        ensure_parameter_type(&parameter_type, enums, structs)?;
    }
    let has_float_parameter = function.parameters.iter().any(|parameter| {
        matches!(
            resolve_type(&parameter.ty, aliases),
            Ok(Type::F32 | Type::F64)
        )
    });
    let has_integer_parameter = function.parameters.iter().any(|parameter| {
        !matches!(
            resolve_type(&parameter.ty, aliases),
            Ok(Type::F32 | Type::F64)
        )
    });
    let float_parameter_type = function
        .parameters
        .iter()
        .find_map(|parameter| match resolve_type(&parameter.ty, aliases) {
            Ok(ty @ (Type::F32 | Type::F64)) => Some(ty),
            _ => None,
        });
    if function
        .parameters
        .iter()
        .any(|parameter| matches!(resolve_type(&parameter.ty, aliases), Ok(Type::F32)))
        && function
            .parameters
            .iter()
            .any(|parameter| matches!(resolve_type(&parameter.ty, aliases), Ok(Type::F64)))
    {
        return Err("native backend does not support mixed f32/f64 parameters".into());
    }

    let mut locals = HashMap::new();
    let mut next_slot = 1usize;
    for parameter in &function.parameters {
        add_local(
            &mut locals,
            &parameter.name,
            &parameter.ty,
            structs,
            enums,
            aliases,
            &mut next_slot,
        )?;
    }
    let mut local_types = HashMap::new();
    for parameter in &function.parameters {
        local_types.insert(
            parameter.name.clone(),
            resolve_type(&parameter.ty, aliases)?,
        );
    }
    for statement in &function.body {
        collect_local_types(statement, &mut local_types, aliases);
    }
    for statement in &function.body {
        collect_locals(
            statement,
            &mut locals,
            structs,
            enums,
            aliases,
            &mut next_slot,
        )?;
    }
    let frame_size = ((next_slot.saturating_sub(1) * 8 + 15) / 16) * 16;

    output.push_str(&format!(
        ".globl {}\n.type {}, @function\n{}:\n",
        function.name, function.name, function.name
    ));
    output.push_str("    push rbp\n    mov rbp, rsp\n");
    if frame_size != 0 {
        output.push_str(&format!("    sub rsp, {frame_size}\n"));
    }
    let all_float_parameters = has_float_parameter && !has_integer_parameter;
    let mixed_parameters = has_float_parameter && has_integer_parameter;
    if all_float_parameters && function.parameters.len() > FLOAT_ARGUMENT_REGISTERS.len() {
        return Err("native backend supports at most eight f64 parameters".into());
    }
    if mixed_parameters {
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        let mut stack_word = 0usize;
        for parameter in &function.parameters {
            let ty = resolve_type(&parameter.ty, aliases)?;
            if value_word_count(&ty, structs, enums)? != 1 {
                return Err(
                    "native backend does not support aggregate values in mixed ABI calls".into(),
                );
            }
            let slot = local_slots(&locals, &parameter.name)?[0];
            if matches!(ty, Type::F32 | Type::F64) {
                if float_index < FLOAT_ARGUMENT_REGISTERS.len() {
                    output.push_str(&format!(
                        "    {} QWORD PTR [rbp-{}], {}\n",
                        if matches!(ty, Type::F32) {
                            "movd"
                        } else {
                            "movq"
                        },
                        slot * 8,
                        FLOAT_ARGUMENT_REGISTERS[float_index]
                    ));
                    float_index += 1;
                } else {
                    let offset = 16 + stack_word * 8;
                    output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp+{offset}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        slot * 8
                    ));
                    stack_word += 1;
                }
            } else if integer_index < ARGUMENT_REGISTERS.len() {
                output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {}\n",
                    slot * 8,
                    ARGUMENT_REGISTERS[integer_index]
                ));
                integer_index += 1;
            } else {
                let offset = 16 + stack_word * 8;
                output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp+{offset}]\n    mov QWORD PTR [rbp-{}], rax\n",
                    slot * 8
                ));
                stack_word += 1;
            }
        }
    }
    let mut incoming_word = 0usize;
    for parameter in &function.parameters {
        if mixed_parameters {
            continue;
        }
        let ty = resolve_type(&parameter.ty, aliases)?;
        let words = value_word_count(&ty, structs, enums)?;
        let slots = local_slots(&locals, &parameter.name)?;
        if all_float_parameters {
            let slot = slots[0];
            output.push_str(&format!(
                "    {} QWORD PTR [rbp-{}], {}\n",
                if matches!(float_parameter_type, Some(Type::F32)) {
                    "movd"
                } else {
                    "movq"
                },
                slot * 8,
                FLOAT_ARGUMENT_REGISTERS[incoming_word]
            ));
            incoming_word += 1;
            continue;
        }
        for slot in slots.into_iter().take(words) {
            if incoming_word < ARGUMENT_REGISTERS.len() {
                output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {}\n",
                    slot * 8,
                    ARGUMENT_REGISTERS[incoming_word]
                ));
            } else {
                let incoming_offset = 16 + (incoming_word - ARGUMENT_REGISTERS.len()) * 8;
                output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp+{incoming_offset}]\n    mov QWORD PTR [rbp-{}], rax\n",
                    slot * 8
                ));
            }
            incoming_word += 1;
        }
    }

    let return_label = format!(".Lreturn_{}", function.name);
    let mut context = FunctionContext {
        locals,
        structs: structs.clone(),
        enums: enums.clone(),
        globals: globals.clone(),
        aliases: aliases.clone(),
        local_types,
        return_type,
        functions: functions.clone(),
        function_name: function.name.clone(),
        labels: 0,
        stack_depth: 0,
        loop_labels: Vec::new(),
        return_label: return_label.clone(),
        output: String::new(),
    };
    for statement in &function.body {
        context.statement(statement)?;
    }
    if function.body.is_empty() {
        context.output.push_str("    xor eax, eax\n");
    }
    output.push_str(&context.output);
    output.push_str(&format!("{return_label}:\n"));
    output.push_str("    mov rsp, rbp\n    pop rbp\n    ret\n\n");
    Ok(())
}

fn collect_local_types(
    statement: &Statement,
    types: &mut HashMap<String, Type>,
    aliases: &HashMap<String, Type>,
) {
    match statement {
        Statement::Let {
            name, ty, value, ..
        } => {
            if let Ok(ty) = resolve_type(ty, aliases) {
                types.insert(name.clone(), ty);
            }
            collect_expr_types(value, types, aliases);
        }
        Statement::While { condition, body } => {
            collect_expr_types(condition, types, aliases);
            for statement in body {
                collect_local_types(statement, types, aliases);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_local_types(statement, types, aliases);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_local_types(init, types, aliases);
            collect_expr_types(condition, types, aliases);
            collect_local_types(step, types, aliases);
            for statement in body {
                collect_local_types(statement, types, aliases);
            }
        }
        Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => collect_expr_types(value, types, aliases),
        Statement::ArrayAssign { index, value, .. } => {
            collect_expr_types(index, types, aliases);
            collect_expr_types(value, types, aliases);
        }
        Statement::Break | Statement::Continue | Statement::Return(None) => {}
    }
}

fn collect_expr_types(
    expression: &Expr,
    types: &mut HashMap<String, Type>,
    aliases: &HashMap<String, Type>,
) {
    match expression {
        Expr::List(items) => {
            for item in items {
                collect_expr_types(item, types, aliases);
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_local_types(statement, types, aliases);
            }
        }
        _ => {}
    }
}

fn collect_locals(
    statement: &Statement,
    locals: &mut HashMap<String, Storage>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    next_slot: &mut usize,
) -> Result<(), String> {
    match statement {
        Statement::Let { name, ty, .. } => {
            add_local(locals, name, ty, structs, enums, aliases, next_slot)?;
            if let Statement::Let { value, .. } = statement {
                collect_expr_locals(value, locals, structs, enums, aliases, next_slot)?;
            }
        }
        Statement::While { condition, body } => {
            collect_expr_locals(condition, locals, structs, enums, aliases, next_slot)?;
            for statement in body {
                collect_locals(statement, locals, structs, enums, aliases, next_slot)?;
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_locals(statement, locals, structs, enums, aliases, next_slot)?;
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_locals(init, locals, structs, enums, aliases, next_slot)?;
            collect_expr_locals(condition, locals, structs, enums, aliases, next_slot)?;
            collect_locals(step, locals, structs, enums, aliases, next_slot)?;
            for statement in body {
                collect_locals(statement, locals, structs, enums, aliases, next_slot)?;
            }
        }
        Statement::Assign { value, .. } => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot)?
        }
        Statement::ArrayAssign { index, value, .. } => {
            collect_expr_locals(index, locals, structs, enums, aliases, next_slot)?;
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot)?;
        }
        Statement::FieldAssign { value, .. } => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot)?
        }
        Statement::Return(Some(value)) | Statement::Expr(value) => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot)?
        }
        Statement::Break | Statement::Continue | Statement::Return(None) => {}
    }
    Ok(())
}

fn collect_expr_locals(
    expression: &Expr,
    locals: &mut HashMap<String, Storage>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    next_slot: &mut usize,
) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                for arm in items.iter().skip(2) {
                    let Expr::List(arm) = arm else { continue };
                    let Some(Expr::List(pattern)) = arm.first() else {
                        continue;
                    };
                    if pattern.len() != 2 {
                        continue;
                    }
                    let (Some(Expr::Symbol(variant_name)), Some(Expr::Symbol(binding))) =
                        (pattern.first(), pattern.get(1))
                    else {
                        continue;
                    };
                    if binding == "_" || locals.contains_key(binding) {
                        continue;
                    }
                    let Some(field_type) = enums.values().find_map(|variants| {
                        variants
                            .iter()
                            .find(|variant| variant.name == *variant_name)
                            .and_then(|variant| variant.fields.first())
                    }) else {
                        continue;
                    };
                    add_local(
                        locals, binding, field_type, structs, enums, aliases, next_slot,
                    )?;
                }
            }
            for item in items {
                collect_expr_locals(item, locals, structs, enums, aliases, next_slot)?;
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_locals(statement, locals, structs, enums, aliases, next_slot)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn add_local(
    locals: &mut HashMap<String, Storage>,
    name: &str,
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    next_slot: &mut usize,
) -> Result<(), String> {
    let ty = resolve_type(ty, aliases)?;
    let storage = if let Type::Named(enum_name) = &ty {
        if let Some(variants) = enums.get(enum_name) {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                let payload = variants
                    .iter()
                    .find_map(|variant| variant.fields.first())
                    .ok_or_else(|| "enum payload metadata is invalid".to_owned())?;
                ensure_scalar_type(payload, enums)
                    .map_err(|_| "native backend only supports scalar enum payloads".to_owned())?;
                let discriminant = *next_slot;
                let payload = discriminant + 1;
                *next_slot += 2;
                Storage::Enum {
                    discriminant,
                    payload,
                }
            } else {
                let slot = *next_slot;
                *next_slot += 1;
                Storage::Scalar(slot)
            }
        } else if let Some(fields) = structs.get(enum_name) {
            let mut slots = Vec::with_capacity(fields.len());
            for field in fields {
                ensure_scalar_type(&field.ty, enums)
                    .map_err(|_| format!("struct field '{}' is not scalar", field.name))?;
                slots.push((field.name.clone(), *next_slot));
                *next_slot += 1;
            }
            Storage::Struct(slots)
        } else {
            return Err(format!("unknown named local type '{enum_name}'"));
        }
    } else if ensure_scalar_type(&ty, enums).is_ok() {
        let slot = *next_slot;
        *next_slot += 1;
        Storage::Scalar(slot)
    } else if let Type::Array(element, length) = &ty {
        ensure_scalar_type(element, enums)
            .map_err(|_| "native backend only supports arrays of scalar values".to_owned())?;
        let base = *next_slot;
        *next_slot += length;
        Storage::Array {
            base,
            length: *length,
        }
    } else if let Type::Named(struct_name) = &ty {
        let fields = structs
            .get(struct_name)
            .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
        let mut slots = Vec::with_capacity(fields.len());
        for field in fields {
            ensure_scalar_type(&field.ty, enums)
                .map_err(|_| format!("struct field '{}' is not scalar", field.name))?;
            slots.push((field.name.clone(), *next_slot));
            *next_slot += 1;
        }
        Storage::Struct(slots)
    } else {
        return Err(format!("native backend does not support local type {ty:?}"));
    };
    if locals.insert(name.to_owned(), storage).is_some() {
        return Err(format!("duplicate local '{name}'"));
    }
    Ok(())
}

fn local_slots(locals: &HashMap<String, Storage>, name: &str) -> Result<Vec<usize>, String> {
    match locals
        .get(name)
        .ok_or_else(|| format!("unknown local '{name}'"))?
    {
        Storage::Scalar(slot) => Ok(vec![*slot]),
        Storage::Struct(slots) => Ok(slots.iter().map(|(_, slot)| *slot).collect()),
        Storage::Enum {
            discriminant,
            payload,
        } => Ok(vec![*discriminant, *payload]),
        Storage::Array { base, length } => Ok((*base..*base + *length).collect()),
    }
}

fn value_word_count(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<usize, String> {
    if ensure_scalar_type(ty, enums).is_ok() {
        return Ok(1);
    }
    if let Type::Named(name) = ty {
        if let Some(fields) = structs.get(name) {
            if fields.len() <= 2
                && fields
                    .iter()
                    .all(|field| ensure_scalar_type(&field.ty, enums).is_ok())
            {
                return Ok(fields.len());
            }
        }
        if let Some(variants) = enums.get(name) {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                return Ok(2);
            }
        }
    }
    if let Type::Array(element, length) = ty {
        if *length <= VALUE_REGISTERS.len() && ensure_scalar_type(element, enums).is_ok() {
            return Ok(*length);
        }
    }
    Err(format!("native ABI does not support value type {ty:?}"))
}

#[derive(Clone, Debug)]
enum Storage {
    Scalar(usize),
    Array { base: usize, length: usize },
    Struct(Vec<(String, usize)>),
    Enum { discriminant: usize, payload: usize },
}

fn scalar_slot(locals: &HashMap<String, Storage>, name: &str) -> usize {
    match locals.get(name).expect("validated local") {
        Storage::Scalar(slot) => *slot,
        Storage::Array { .. } | Storage::Struct(_) | Storage::Enum { .. } => {
            panic!("validated scalar local is aggregate")
        }
    }
}

fn ensure_integer_type(ty: &Type) -> Result<(), String> {
    if matches!(
        ty,
        Type::Bool
            | Type::Char
            | Type::I8
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
    ) {
        Ok(())
    } else {
        Err(format!(
            "native integer backend does not support type {ty:?}"
        ))
    }
}

fn is_unsigned_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 | Type::Usize
    )
}

fn is_float_type(ty: &Type) -> bool {
    matches!(ty, Type::F32 | Type::F64)
}

fn ensure_scalar_type(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> Result<(), String> {
    if matches!(ty, Type::F32 | Type::F64) {
        return Ok(());
    }
    if let Type::Named(name) = ty {
        if let Some(variants) = enums.get(name) {
            if variants.iter().all(|variant| variant.fields.is_empty()) {
                return Ok(());
            }
            return Err(format!("payload enum '{name}' is not a scalar"));
        }
    }
    ensure_integer_type(ty)
}

fn ensure_return_type(
    ty: &Type,
    enums: &HashMap<String, Vec<EnumVariant>>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    if ensure_scalar_type(ty, enums).is_ok() {
        return Ok(());
    }
    if value_word_count(ty, structs, enums).is_ok() {
        return Ok(());
    }
    let Type::Named(name) = ty else {
        return Err(format!(
            "native backend does not support return type {ty:?}"
        ));
    };
    if let Some(fields) = structs.get(name) {
        if fields.len() <= 2
            && fields
                .iter()
                .all(|field| ensure_scalar_type(&field.ty, enums).is_ok())
        {
            return Ok(());
        }
        return Err(format!(
            "native backend only supports scalar struct returns for '{name}'"
        ));
    }
    let Some(variants) = enums.get(name) else {
        return Err(format!("unknown return type '{name}'"));
    };
    if variants.iter().all(|variant| variant.fields.len() <= 1)
        && variants
            .iter()
            .filter_map(|variant| variant.fields.first())
            .all(|field| ensure_integer_type(field).is_ok())
    {
        Ok(())
    } else {
        Err(format!(
            "native backend only supports scalar payload returns for '{name}'"
        ))
    }
}

fn ensure_parameter_type(
    ty: &Type,
    enums: &HashMap<String, Vec<EnumVariant>>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    value_word_count(ty, structs, enums).map(|_| ())
}

fn resolve_type(ty: &Type, aliases: &HashMap<String, Type>) -> Result<Type, String> {
    match ty {
        Type::Named(name) => match aliases.get(name) {
            Some(target) if target != ty => resolve_type(target, aliases),
            Some(_) => Err(format!("recursive type alias '{name}'")),
            None => Ok(ty.clone()),
        },
        Type::Array(element, length) => Ok(Type::Array(
            Box::new(resolve_type(element, aliases)?),
            *length,
        )),
        _ => Ok(ty.clone()),
    }
}

fn constant_value(
    expression: &Expr,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<i128, String> {
    match expression {
        Expr::Integer(value) => Ok(*value),
        Expr::Char(value) => Ok(*value as i128),
        Expr::Float(_) => Err("floating-point global initializers are not supported".into()),
        Expr::Symbol(name) if name == "true" => Ok(1),
        Expr::Symbol(name) if name == "false" => Ok(0),
        Expr::Symbol(name) => enums
            .values()
            .find_map(|variants| {
                variants
                    .iter()
                    .position(|variant| variant.name == *name)
                    .map(|value| value as i128)
            })
            .ok_or_else(|| format!("global initializer '{name}' is not a constant")),
        Expr::List(items) if items.len() == 3 => {
            let operator = match &items[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => return Err("global initializer is not constant".into()),
            };
            let left = constant_value(&items[1], enums)?;
            let right = constant_value(&items[2], enums)?;
            match operator {
                "+" => Ok(left + right),
                "-" => Ok(left - right),
                "*" => Ok(left * right),
                _ => Err("global initializer is not constant".into()),
            }
        }
        _ => Err("global initializer is not constant".into()),
    }
}

struct FunctionContext {
    locals: HashMap<String, Storage>,
    structs: HashMap<String, Vec<Field>>,
    enums: HashMap<String, Vec<EnumVariant>>,
    globals: HashMap<String, i128>,
    aliases: HashMap<String, Type>,
    local_types: HashMap<String, Type>,
    return_type: Type,
    functions: HashMap<String, FunctionAbi>,
    function_name: String,
    labels: usize,
    stack_depth: usize,
    loop_labels: Vec<(String, String)>,
    return_label: String,
    output: String,
}

impl FunctionContext {
    fn statement(&mut self, statement: &Statement) -> Result<(), String> {
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                let ty = resolve_type(ty, &self.aliases)?;
                if let Type::Named(type_name) = &ty {
                    if self.enums.get(type_name).is_some_and(|variants| {
                        variants.iter().any(|variant| !variant.fields.is_empty())
                    }) {
                        self.store_enum(name, type_name, value)?;
                    } else {
                        self.store_struct(name, type_name, value)?;
                    }
                } else if matches!(ty, Type::Array(_, _)) {
                    self.store_array(name, value)?;
                } else {
                    if is_float_type(&ty) {
                        self.expression_as_float(value, &ty)?;
                    } else {
                        self.expression(value)?;
                    }
                    let slot = scalar_slot(&self.locals, name) * 8;
                    if matches!(ty, Type::F32) {
                        self.output.push_str(&format!(
                            "    movd eax, xmm0\n    mov DWORD PTR [rbp-{slot}], eax\n"
                        ));
                    } else if matches!(ty, Type::F64) {
                        self.output.push_str(&format!(
                            "    movq rax, xmm0\n    mov QWORD PTR [rbp-{slot}], rax\n"
                        ));
                    } else {
                        self.output
                            .push_str(&format!("    mov QWORD PTR [rbp-{slot}], rax\n"));
                    }
                }
            }
            Statement::Assign { name, value } => {
                let expected = self.local_types.get(name).cloned();
                if let Some(ty) = expected.as_ref().filter(|ty| is_float_type(ty)) {
                    self.expression_as_float(value, ty)?;
                } else {
                    self.expression(value)?;
                }
                let storage = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown variable '{name}'"))?;
                let Storage::Scalar(slot) = storage else {
                    return Err(format!("cannot assign aggregate local '{name}'"));
                };
                if self
                    .local_types
                    .get(name)
                    .is_some_and(|ty| matches!(ty, Type::F32 | Type::F64))
                {
                    if expected.as_ref().is_some_and(|ty| matches!(ty, Type::F32)) {
                        self.output.push_str(&format!(
                            "    movd eax, xmm0\n    mov DWORD PTR [rbp-{}], eax\n",
                            slot * 8
                        ));
                    } else {
                        self.output.push_str(&format!(
                            "    movq rax, xmm0\n    mov QWORD PTR [rbp-{}], rax\n",
                            slot * 8
                        ));
                    }
                } else {
                    self.output
                        .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
                }
            }
            Statement::ArrayAssign { name, index, value } => {
                let Storage::Array { base, length } = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown array '{name}'"))?
                else {
                    return Err(format!("'{name}' is not an array"));
                };
                let base = *base;
                let length = *length;
                let bounds_failure = self.label("bounds_failure");
                self.expression(index)?;
                self.output.push_str(&format!(
                    "    cmp rax, {length}\n    jae {bounds_failure}\n"
                ));
                self.push_rax();
                self.expression(value)?;
                self.output.push_str("    mov rdx, rax\n    pop rcx\n");
                self.stack_depth -= 1;
                self.output.push_str(&format!(
                    "    lea rax, [rbp-{}]\n    shl rcx, 3\n    sub rax, rcx\n    mov QWORD PTR [rax], rdx\n",
                    base * 8
                ));
                self.output
                    .push_str(&format!("    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n"));
            }
            Statement::FieldAssign { name, field, value } => {
                let Storage::Struct(fields) = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown struct '{name}'"))?
                else {
                    return Err(format!("'{name}' is not a struct"));
                };
                let slot = fields
                    .iter()
                    .find(|(field_name, _)| field_name == field)
                    .map(|(_, slot)| *slot)
                    .ok_or_else(|| format!("unknown field '{field}'"))?;
                self.expression(value)?;
                self.output
                    .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
            }
            Statement::While { condition, body } => {
                let start = self.label("while");
                let end = self.label("endwhile");
                self.output.push_str(&format!("{start}:\n"));
                self.expression(condition)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {end}\n"));
                self.loop_labels.push((start.clone(), end.clone()));
                for statement in body {
                    self.statement(statement)?;
                }
                self.loop_labels.pop();
                self.output.push_str(&format!("    jmp {start}\n{end}:\n"));
            }
            Statement::Loop { body } => {
                let start = self.label("loop");
                let end = self.label("endloop");
                self.output.push_str(&format!("{start}:\n"));
                self.loop_labels.push((start.clone(), end.clone()));
                for statement in body {
                    self.statement(statement)?;
                }
                self.loop_labels.pop();
                self.output.push_str(&format!("    jmp {start}\n{end}:\n"));
            }
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                self.statement(init)?;
                let start = self.label("for");
                let step_label = self.label("for_step");
                let end = self.label("endfor");
                self.output.push_str(&format!("{start}:\n"));
                self.expression(condition)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {end}\n"));
                self.loop_labels.push((step_label.clone(), end.clone()));
                for statement in body {
                    self.statement(statement)?;
                }
                self.loop_labels.pop();
                self.output.push_str(&format!("{step_label}:\n"));
                self.statement(step)?;
                self.output.push_str(&format!("    jmp {start}\n{end}:\n"));
            }
            Statement::Break => {
                let Some((_, end)) = self.loop_labels.last() else {
                    return Err("break used outside a loop".into());
                };
                self.output.push_str(&format!("    jmp {end}\n"));
            }
            Statement::Continue => {
                let Some((start, _)) = self.loop_labels.last() else {
                    return Err("continue used outside a loop".into());
                };
                self.output.push_str(&format!("    jmp {start}\n"));
            }
            Statement::Return(value) => {
                if let Some(value) = value {
                    self.return_value(value)?;
                } else {
                    self.output.push_str("    xor eax, eax\n");
                }
                self.output
                    .push_str(&format!("    jmp {}\n", self.return_label));
            }
            Statement::Expr(expression) => {
                if self.is_aggregate_type(&self.return_type) {
                    self.return_value(expression)?;
                } else if is_float_type(&self.return_type) {
                    self.expression_as_float(expression, &self.return_type.clone())?;
                } else {
                    self.expression(expression)?;
                }
            }
        }
        Ok(())
    }

    fn return_value(&mut self, value: &Expr) -> Result<(), String> {
        if is_float_type(&self.return_type) {
            let ty = self.return_type.clone();
            return self.expression_as_float(value, &ty);
        }
        if let Type::Array(_, length) = &self.return_type {
            return self.return_array_value(*length, value);
        }
        let Type::Named(struct_name) = &self.return_type else {
            self.expression(value)?;
            return Ok(());
        };
        let Some(fields) = self.structs.get(struct_name).cloned() else {
            if self
                .enums
                .get(struct_name)
                .is_some_and(|variants| variants.iter().any(|variant| !variant.fields.is_empty()))
            {
                if let Expr::Symbol(name) = value {
                    let Storage::Enum {
                        discriminant,
                        payload,
                    } = self
                        .locals
                        .get(name)
                        .ok_or_else(|| format!("unknown enum local '{name}'"))?
                    else {
                        return Err(format!("'{name}' is not a payload enum"));
                    };
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov rdx, QWORD PTR [rbp-{}]\n",
                        discriminant * 8,
                        payload * 8
                    ));
                    return Ok(());
                }
            }
            self.expression(value)?;
            return Ok(());
        };
        if let Expr::Symbol(name) = value {
            let Storage::Struct(slots) = self
                .locals
                .get(name)
                .ok_or_else(|| format!("unknown struct local '{name}'"))?
            else {
                return Err(format!("'{name}' is not a struct"));
            };
            let slots = slots.clone();
            for (index, (_, slot)) in slots.iter().enumerate() {
                let register = match index {
                    0 => "rax",
                    1 => "rdx",
                    _ => return Err("native struct return has too many fields".into()),
                };
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [rbp-{}]\n",
                    slot * 8
                ));
            }
            return Ok(());
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == struct_name) {
                if items.len() - 1 != fields.len() {
                    return Err(format!("constructor '{struct_name}' has wrong field count"));
                }
                if fields.len() > 2 {
                    return Err("native struct return has too many fields".into());
                }
                for (index, field) in items[1..].iter().enumerate() {
                    self.expression(field)?;
                    if index == 0 && fields.len() == 2 {
                        self.push_rax();
                    } else if index == 1 {
                        self.output.push_str("    mov rdx, rax\n");
                        self.output.push_str("    pop rax\n");
                        self.stack_depth -= 1;
                    }
                }
                return Ok(());
            }
        }
        self.expression(value)
    }

    fn return_array_value(&mut self, length: usize, value: &Expr) -> Result<(), String> {
        if let Expr::Symbol(name) = value {
            let Storage::Array {
                base,
                length: local_length,
            } = self
                .locals
                .get(name)
                .ok_or_else(|| format!("unknown array local '{name}'"))?
            else {
                return Err(format!("'{name}' is not an array"));
            };
            if *local_length != length {
                return Err("array return length mismatch".into());
            }
            let base = *base;
            for (index, register) in VALUE_REGISTERS[..length].iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [rbp-{}]\n",
                    (base + index) * 8
                ));
            }
            return Ok(());
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array-repeat") {
                if items.len() != 2 {
                    return Err("array-repeat requires one value".into());
                }
                for _ in 0..length {
                    self.expression(&items[1])?;
                    self.push_rax();
                }
                for register in VALUE_REGISTERS[..length].iter().rev() {
                    self.output.push_str(&format!("    pop {register}\n"));
                    self.stack_depth -= 1;
                }
                return Ok(());
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
                if items.len() - 1 != length {
                    return Err("array return has the wrong length".into());
                }
                for value in &items[1..] {
                    self.expression(value)?;
                    self.push_rax();
                }
                for register in VALUE_REGISTERS[..length].iter().rev() {
                    self.output.push_str(&format!("    pop {register}\n"));
                    self.stack_depth -= 1;
                }
                return Ok(());
            }
        }
        self.expression(value)
    }

    fn is_aggregate_type(&self, ty: &Type) -> bool {
        if matches!(ty, Type::Array(_, _)) {
            return true;
        }
        let Type::Named(name) = ty else { return false };
        self.structs.contains_key(name)
            || self
                .enums
                .get(name)
                .is_some_and(|variants| variants.iter().any(|variant| !variant.fields.is_empty()))
    }

    fn store_struct(&mut self, name: &str, struct_name: &str, value: &Expr) -> Result<(), String> {
        let Some(Storage::Struct(slots)) = self.locals.get(name).cloned() else {
            return Err(format!("'{name}' is not a struct"));
        };
        if !matches!(value, Expr::List(_)) {
            self.expression(value)?;
            if let Some((_, slot)) = slots.first() {
                self.output
                    .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
            }
            if let Some((_, slot)) = slots.get(1) {
                self.output
                    .push_str(&format!("    mov QWORD PTR [rbp-{}], rdx\n", slot * 8));
            }
            return Ok(());
        }
        let Expr::List(items) = value else {
            unreachable!()
        };
        let Some(Expr::Symbol(constructor)) = items.first() else {
            return Err("struct constructor must start with a symbol".into());
        };
        if constructor != struct_name {
            let Storage::Struct(slots) = self
                .locals
                .get(name)
                .ok_or_else(|| format!("unknown local '{name}'"))?
            else {
                return Err(format!("'{name}' is not a struct"));
            };
            let slots = slots.clone();
            self.expression(value)?;
            if let Some((_, slot)) = slots.first() {
                self.output
                    .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
            }
            if let Some((_, slot)) = slots.get(1) {
                self.output
                    .push_str(&format!("    mov QWORD PTR [rbp-{}], rdx\n", slot * 8));
            }
            return Ok(());
        }
        let fields = self
            .structs
            .get(struct_name)
            .ok_or_else(|| format!("unknown struct '{struct_name}'"))?
            .clone();
        if items.len() - 1 != fields.len() {
            return Err(format!("constructor '{struct_name}' has wrong field count"));
        }
        for ((_, slot), value) in slots.iter().zip(&items[1..]) {
            self.expression(value)?;
            self.output
                .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
        }
        Ok(())
    }

    fn store_enum(&mut self, name: &str, enum_name: &str, value: &Expr) -> Result<(), String> {
        let Some(Storage::Enum {
            discriminant,
            payload,
        }) = self.locals.get(name).cloned()
        else {
            return Err(format!("'{name}' is not a payload enum"));
        };
        if !matches!(value, Expr::List(_)) {
            self.expression(value)?;
            self.output.push_str(&format!(
                "    mov QWORD PTR [rbp-{}], rax\n    mov QWORD PTR [rbp-{}], rdx\n",
                discriminant * 8,
                payload * 8
            ));
            return Ok(());
        }
        let Expr::List(items) = value else {
            return Err(format!("enum local '{name}' requires a constructor"));
        };
        let Some(Expr::Symbol(variant_name)) = items.first() else {
            return Err("enum constructor must start with a variant name".into());
        };
        let variants = self
            .enums
            .get(enum_name)
            .ok_or_else(|| format!("unknown enum '{enum_name}'"))?
            .clone();
        let variant = variants
            .iter()
            .find(|variant| variant.name == *variant_name)
            .cloned();
        let Some(variant) = variant else {
            self.expression(value)?;
            self.output.push_str(&format!(
                "    mov QWORD PTR [rbp-{}], rax\n    mov QWORD PTR [rbp-{}], rdx\n",
                discriminant * 8,
                payload * 8
            ));
            return Ok(());
        };
        if items.len() - 1 != variant.fields.len() {
            return Err(format!("variant '{variant_name}' has wrong payload count"));
        }
        let variant_index = variants
            .iter()
            .position(|candidate| candidate.name == *variant_name)
            .expect("validated enum variant");
        self.output.push_str(&format!(
            "    mov QWORD PTR [rbp-{}], {}\n",
            discriminant * 8,
            variant_index
        ));
        if let Some(value) = items.get(1) {
            self.expression(value)?;
            self.output
                .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", payload * 8));
        }
        Ok(())
    }

    fn store_array(&mut self, name: &str, value: &Expr) -> Result<(), String> {
        let Storage::Array { base, length } = self
            .locals
            .get(name)
            .ok_or_else(|| format!("unknown array '{name}'"))?
        else {
            return Err(format!("'{name}' is not an array"));
        };
        let (base, length) = (*base, *length);
        let Expr::List(items) = value else {
            self.expression(value)?;
            for (index, register) in VALUE_REGISTERS[..length].iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {register}\n",
                    (base + index) * 8
                ));
            }
            return Ok(());
        };
        if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array-repeat") {
            if items.len() != 2 {
                return Err("array-repeat requires one value".into());
            }
            for index in 0..length {
                self.expression(&items[1])?;
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], rax\n",
                    (base + index) * 8
                ));
            }
            return Ok(());
        }
        if !matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
            self.expression(value)?;
            for (index, register) in VALUE_REGISTERS[..length].iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {register}\n",
                    (base + index) * 8
                ));
            }
            return Ok(());
        }
        if items.len() - 1 != length {
            return Err("array constructor has the wrong length".into());
        }
        for (index, value) in items[1..].iter().enumerate() {
            self.expression(value)?;
            self.output.push_str(&format!(
                "    mov QWORD PTR [rbp-{}], rax\n",
                (base + index) * 8
            ));
        }
        Ok(())
    }

    fn expression(&mut self, expression: &Expr) -> Result<(), String> {
        match expression {
            Expr::Integer(value) => self.output.push_str(&format!("    mov rax, {value}\n")),
            Expr::Char(value) => self
                .output
                .push_str(&format!("    mov rax, {}\n", *value as u32)),
            Expr::Float(value) => {
                let bits = value
                    .parse::<f64>()
                    .map_err(|_| format!("invalid floating-point literal '{value}'"))?
                    .to_bits();
                self.output
                    .push_str(&format!("    mov rax, 0x{bits:x}\n    movq xmm0, rax\n"));
            }
            Expr::Block(statements) => {
                if statements.is_empty() {
                    self.output.push_str("    xor eax, eax\n");
                }
                for statement in statements {
                    self.statement(statement)?;
                }
            }
            Expr::Symbol(name) if name == "true" => self.output.push_str("    mov eax, 1\n"),
            Expr::Symbol(name) if name == "false" => self.output.push_str("    xor eax, eax\n"),
            Expr::Symbol(name) if self.enum_value(name).is_some() => {
                self.output.push_str(&format!(
                    "    mov rax, {}\n",
                    self.enum_value(name).unwrap()
                ));
            }
            Expr::Symbol(name) => {
                if self.locals.contains_key(name) {
                    let slot = scalar_slot(&self.locals, name);
                    if self
                        .local_types
                        .get(name)
                        .is_some_and(|ty| matches!(ty, Type::F32 | Type::F64))
                    {
                        if self
                            .local_types
                            .get(name)
                            .is_some_and(|ty| matches!(ty, Type::F32))
                        {
                            self.output.push_str(&format!(
                                "    movss xmm0, DWORD PTR [rbp-{}]\n",
                                slot * 8
                            ));
                        } else {
                            self.output.push_str(&format!(
                                "    movq xmm0, QWORD PTR [rbp-{}]\n",
                                slot * 8
                            ));
                        }
                    } else {
                        self.output
                            .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
                    }
                } else if self.globals.contains_key(name) {
                    self.output
                        .push_str(&format!("    mov rax, QWORD PTR [rip+{name}]\n"));
                } else {
                    return Err(format!("unknown variable '{name}'"));
                }
            }
            Expr::List(items) => self.list_expression(items)?,
            Expr::String(_) => return Err("strings are not supported by the native backend".into()),
            Expr::At => return Err("@ is not an executable expression".into()),
            Expr::Quote(_) => return Err("quoted expressions are not executable".into()),
        }
        Ok(())
    }

    fn list_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        let operator = match items.first() {
            Some(Expr::Symbol(name)) => name.as_str(),
            _ => return Err("expression list must start with a symbol".into()),
        };
        if let Some((enum_name, variant)) = self.enums.iter().find_map(|(enum_name, variants)| {
            variants
                .iter()
                .find(|variant| variant.name == operator)
                .map(|variant| (enum_name.as_str(), variant))
        }) {
            if items.len() - 1 != variant.fields.len() {
                return Err(format!(
                    "variant '{operator}' expects {} payloads",
                    variant.fields.len()
                ));
            }
            let variant_index = self
                .enums
                .get(enum_name)
                .and_then(|variants| {
                    variants
                        .iter()
                        .position(|candidate| candidate.name == operator)
                })
                .expect("validated enum variant");
            if let Some(value) = items.get(1) {
                self.expression(value)?;
                self.output.push_str("    mov rdx, rax\n");
            }
            self.output
                .push_str(&format!("    mov rax, {variant_index}\n"));
            return Ok(());
        }
        match operator {
            "-" if items.len() == 2 => self.unary_negate(items),
            "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" => {
                self.binary_operator(operator, items)
            }
            "<" | "<=" | ">" | ">=" | "==" | "!=" => self.comparison(operator, items),
            "if" => self.if_expression(items),
            "as" => {
                if items.len() != 3 {
                    return Err("as requires a value and target type".into());
                }
                self.expression(&items[1])
            }
            "match" => self.match_expression(items),
            "index" => self.index_expression(items),
            "get" => self.field_expression(items),
            "!" => self.boolean_not(items),
            "&&" | "||" => self.boolean_logic(operator, items),
            _ => self.call(operator, &items[1..]),
        }
    }

    fn enum_value(&self, name: &str) -> Option<usize> {
        self.enums
            .values()
            .find_map(|variants| variants.iter().position(|variant| variant.name == name))
    }

    fn index_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err("index requires an array and index".into());
        }
        let name = match &items[1] {
            Expr::Symbol(name) => name,
            _ => return Err("index currently requires an array local".into()),
        };
        let Storage::Array { base, .. } = self
            .locals
            .get(name)
            .ok_or_else(|| format!("unknown array '{name}'"))?
        else {
            return Err(format!("'{name}' is not an array"));
        };
        let base = *base;
        let Storage::Array { length, .. } = self.locals.get(name).unwrap() else {
            unreachable!()
        };
        let length = *length;
        let bounds_failure = self.label("bounds_failure");
        self.expression(&items[2])?;
        self.output.push_str("    mov rcx, rax\n");
        self.output.push_str(&format!(
            "    cmp rcx, {length}\n    jae {bounds_failure}\n"
        ));
        self.output.push_str(&format!(
            "    lea rdx, [rbp-{}]\n    shl rcx, 3\n    sub rdx, rcx\n    mov rax, QWORD PTR [rdx]\n",
            base * 8
        ));
        self.output.push_str(&format!(
            "    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n"
        ));
        Ok(())
    }

    fn match_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() < 3 {
            return Err("match requires a value and an arm".into());
        }
        let end = self.label("match_end");
        let base_depth = self.stack_depth;
        let payload_slot = match &items[1] {
            Expr::Symbol(name) => match self.locals.get(name) {
                Some(Storage::Enum { payload, .. }) => Some(*payload),
                _ => None,
            },
            _ => None,
        };
        match &items[1] {
            Expr::Symbol(name) if matches!(self.locals.get(name), Some(Storage::Enum { .. })) => {
                let Storage::Enum { discriminant, .. } = self.locals.get(name).unwrap() else {
                    unreachable!()
                };
                self.output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp-{}]\n",
                    discriminant * 8
                ));
            }
            _ => self.expression(&items[1])?,
        }
        self.push_rax();
        for arm in &items[2..] {
            let arm = match arm {
                Expr::List(arm) if arm.len() == 2 => arm,
                _ => return Err("invalid match arm".into()),
            };
            let next = self.label("match_next");
            let (pattern, binding) = match &arm[0] {
                Expr::Symbol(pattern) => (pattern.as_str(), None),
                Expr::List(pattern) if pattern.len() == 2 => match (&pattern[0], &pattern[1]) {
                    (Expr::Symbol(pattern), Expr::Symbol(binding)) => {
                        (pattern.as_str(), Some(binding.as_str()))
                    }
                    _ => return Err("match variant pattern must be a symbol".into()),
                },
                _ => return Err("match pattern must be a symbol or (variant _)".into()),
            };
            if pattern != "_" {
                let value = self
                    .enum_value(pattern)
                    .ok_or_else(|| format!("unknown enum variant '{pattern}'"))?;
                self.output.push_str(&format!(
                    "    cmp QWORD PTR [rsp], {value}\n    jne {next}\n"
                ));
            }
            if let Some(binding) = binding.filter(|binding| *binding != "_") {
                let Some(payload_slot) = payload_slot else {
                    return Err("payload binding requires a local payload enum".into());
                };
                let slot = scalar_slot(&self.locals, binding);
                self.output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                    payload_slot * 8,
                    slot * 8
                ));
            }
            self.expression(&arm[1])?;
            self.output
                .push_str("    mov rdx, rax\n    pop rcx\n    mov rax, rdx\n");
            self.output.push_str(&format!("    jmp {end}\n{next}:\n"));
            self.stack_depth = base_depth + 1;
        }
        self.output.push_str(&format!("{end}:\n"));
        self.stack_depth = base_depth;
        Ok(())
    }

    fn unary_negate(&mut self, items: &[Expr]) -> Result<(), String> {
        if let Some(ty) = self.expression_float_type(&items[1]) {
            self.expression_as_float(&items[1], &ty)?;
            if matches!(ty, Type::F32) {
                self.output.push_str(
                    "    mov eax, 0x80000000\n    movd xmm1, eax\n    xorps xmm0, xmm1\n",
                );
            } else {
                self.output.push_str(
                    "    mov rax, 0x8000000000000000\n    movq xmm1, rax\n    xorpd xmm0, xmm1\n",
                );
            }
        } else {
            self.expression(&items[1])?;
            self.output.push_str("    neg rax\n");
        }
        Ok(())
    }

    fn field_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err("get requires a value and field".into());
        }
        let field_name = match &items[2] {
            Expr::Symbol(name) => name,
            _ => return Err("get requires a field name".into()),
        };
        match &items[1] {
            Expr::Symbol(local) => {
                let Storage::Struct(fields) = self
                    .locals
                    .get(local)
                    .ok_or_else(|| format!("unknown local '{local}'"))?
                else {
                    return Err(format!("'{local}' is not a struct"));
                };
                let slot = fields
                    .iter()
                    .find(|(name, _)| name == field_name)
                    .map(|(_, slot)| *slot)
                    .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                self.output
                    .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
                Ok(())
            }
            Expr::List(constructor) => {
                let Some(Expr::Symbol(struct_name)) = constructor.first() else {
                    return Err("get constructor must start with a struct name".into());
                };
                let fields = self
                    .structs
                    .get(struct_name)
                    .ok_or_else(|| format!("unknown struct '{struct_name}'"))?
                    .clone();
                let index = fields
                    .iter()
                    .position(|field| field.name == *field_name)
                    .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                let value = constructor
                    .get(index + 1)
                    .ok_or_else(|| "constructor has too few fields".to_owned())?;
                self.expression(value)
            }
            _ => Err("get requires a struct local or constructor".into()),
        }
    }

    fn boolean_not(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 2 {
            return Err("! requires one operand".into());
        }
        self.expression(&items[1])?;
        self.output.push_str("    xor eax, 1\n");
        Ok(())
    }

    fn boolean_logic(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("operator '{operator}' requires two operands"));
        }
        let short_label = self.label(if operator == "&&" {
            "and_false"
        } else {
            "or_true"
        });
        let end_label = self.label("logic_end");
        self.expression(&items[1])?;
        self.output.push_str(&format!(
            "    test rax, rax\n    {} {short_label}\n",
            if operator == "&&" { "jz" } else { "jnz" }
        ));
        self.expression(&items[2])?;
        self.output
            .push_str("    test rax, rax\n    setne al\n    movzx rax, al\n");
        self.output
            .push_str(&format!("    jmp {end_label}\n{short_label}:\n"));
        self.output.push_str(if operator == "&&" {
            "    xor eax, eax\n"
        } else {
            "    mov eax, 1\n"
        });
        self.output.push_str(&format!("{end_label}:\n"));
        Ok(())
    }

    fn binary_operator(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("operator '{operator}' requires two operands"));
        }
        if self.expression_is_float(&items[1]) {
            return self.float_binary_operator(operator, items);
        }
        self.expression(&items[1])?;
        self.push_rax();
        self.expression(&items[2])?;
        self.output.push_str("    mov rcx, rax\n    pop rax\n");
        self.stack_depth -= 1;
        match operator {
            "+" => self.output.push_str("    add rax, rcx\n"),
            "-" => self.output.push_str("    sub rax, rcx\n"),
            "*" => self.output.push_str("    imul rax, rcx\n"),
            "/" => {
                if self.expression_is_unsigned(&items[1]) {
                    self.output.push_str("    xor edx, edx\n    div rcx\n");
                } else {
                    self.output.push_str("    cqo\n    idiv rcx\n");
                }
            }
            "%" => {
                if self.expression_is_unsigned(&items[1]) {
                    self.output
                        .push_str("    xor edx, edx\n    div rcx\n    mov rax, rdx\n");
                } else {
                    self.output
                        .push_str("    cqo\n    idiv rcx\n    mov rax, rdx\n");
                }
            }
            "&" => self.output.push_str("    and rax, rcx\n"),
            "|" => self.output.push_str("    or rax, rcx\n"),
            "^" => self.output.push_str("    xor rax, rcx\n"),
            "<<" => self.output.push_str("    shl rax, cl\n"),
            ">>" => {
                if self.expression_is_unsigned(&items[1]) {
                    self.output.push_str("    shr rax, cl\n");
                } else {
                    self.output.push_str("    sar rax, cl\n");
                }
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn float_binary_operator(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        let ty = self.expression_float_type(&items[1]).unwrap_or(Type::F64);
        self.expression_as_float(&items[1], &ty)?;
        if matches!(ty, Type::F32) {
            self.output
                .push_str("    sub rsp, 8\n    movss DWORD PTR [rsp], xmm0\n");
        } else {
            self.output
                .push_str("    sub rsp, 8\n    movq QWORD PTR [rsp], xmm0\n");
        }
        self.stack_depth += 1;
        self.expression_as_float(&items[2], &ty)?;
        if matches!(ty, Type::F32) {
            self.output
                .push_str("    movss xmm1, DWORD PTR [rsp]\n    add rsp, 8\n");
        } else {
            self.output
                .push_str("    movq xmm1, QWORD PTR [rsp]\n    add rsp, 8\n");
        }
        self.stack_depth -= 1;
        let (add, sub, mul, div, copy) = if matches!(ty, Type::F32) {
            ("addss", "subss", "mulss", "divss", "movaps")
        } else {
            ("addsd", "subsd", "mulsd", "divsd", "movapd")
        };
        match operator {
            "+" => self
                .output
                .push_str(&format!("    {add} xmm1, xmm0\n    {copy} xmm0, xmm1\n")),
            "-" => self
                .output
                .push_str(&format!("    {sub} xmm1, xmm0\n    {copy} xmm0, xmm1\n")),
            "*" => self
                .output
                .push_str(&format!("    {mul} xmm1, xmm0\n    {copy} xmm0, xmm1\n")),
            "/" => self
                .output
                .push_str(&format!("    {div} xmm1, xmm0\n    {copy} xmm0, xmm1\n")),
            _ => {
                return Err(format!(
                    "floating-point operator '{operator}' is unsupported"
                ))
            }
        }
        Ok(())
    }

    fn comparison(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("comparison '{operator}' requires two operands"));
        }
        if self.expression_is_float(&items[1]) {
            return self.float_comparison(operator, items);
        }
        self.expression(&items[1])?;
        self.push_rax();
        self.expression(&items[2])?;
        self.output
            .push_str("    mov rcx, rax\n    pop rax\n    cmp rax, rcx\n");
        self.stack_depth -= 1;
        let unsigned = self.expression_is_unsigned(&items[1]);
        let condition = match operator {
            "<" if unsigned => "b",
            "<=" if unsigned => "be",
            ">" if unsigned => "a",
            ">=" if unsigned => "ae",
            "<" => "l",
            "<=" => "le",
            ">" => "g",
            ">=" => "ge",
            "==" => "e",
            "!=" => "ne",
            _ => unreachable!(),
        };
        self.output
            .push_str(&format!("    set{condition} al\n    movzx rax, al\n"));
        Ok(())
    }

    fn float_comparison(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        let ty = self.expression_float_type(&items[1]).unwrap_or(Type::F64);
        self.expression_as_float(&items[1], &ty)?;
        if matches!(ty, Type::F32) {
            self.output
                .push_str("    sub rsp, 8\n    movss DWORD PTR [rsp], xmm0\n");
        } else {
            self.output
                .push_str("    sub rsp, 8\n    movq QWORD PTR [rsp], xmm0\n");
        }
        self.stack_depth += 1;
        self.expression_as_float(&items[2], &ty)?;
        if matches!(ty, Type::F32) {
            self.output
                .push_str("    movss xmm1, DWORD PTR [rsp]\n    add rsp, 8\n");
        } else {
            self.output
                .push_str("    movq xmm1, QWORD PTR [rsp]\n    add rsp, 8\n");
        }
        self.stack_depth -= 1;
        self.output.push_str(if matches!(ty, Type::F32) {
            "    ucomiss xmm1, xmm0\n"
        } else {
            "    ucomisd xmm1, xmm0\n"
        });
        let condition = match operator {
            "<" => "b",
            "<=" => "be",
            ">" => "a",
            ">=" => "ae",
            "==" => "e",
            "!=" => "ne",
            _ => unreachable!(),
        };
        self.output
            .push_str(&format!("    set{condition} al\n    movzx rax, al\n"));
        Ok(())
    }

    fn expression_is_unsigned(&self, expression: &Expr) -> bool {
        match expression {
            Expr::Symbol(name) => self.local_types.get(name).is_some_and(is_unsigned_type),
            Expr::List(items) => match items.first() {
                Some(Expr::Symbol(operator))
                    if matches!(
                        operator.as_str(),
                        "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>"
                    ) =>
                {
                    items
                        .get(1)
                        .is_some_and(|value| self.expression_is_unsigned(value))
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn expression_is_float(&self, expression: &Expr) -> bool {
        self.expression_float_type(expression).is_some()
    }

    fn expression_float_type(&self, expression: &Expr) -> Option<Type> {
        match expression {
            Expr::Float(_) => Some(Type::F64),
            Expr::Symbol(name) => self
                .local_types
                .get(name)
                .filter(|ty| is_float_type(ty))
                .cloned(),
            Expr::List(items) => match items.first() {
                Some(Expr::Symbol(operator))
                    if matches!(operator.as_str(), "+" | "-" | "*" | "/") =>
                {
                    items
                        .get(1)
                        .and_then(|value| self.expression_float_type(value))
                }
                Some(Expr::Symbol(operator)) => self
                    .functions
                    .get(operator)
                    .map(|function| function.return_type.clone())
                    .filter(is_float_type),
                _ => None,
            },
            _ => None,
        }
    }

    fn expression_as_float(&mut self, expression: &Expr, ty: &Type) -> Result<(), String> {
        match expression {
            Expr::Float(value) => {
                let parsed = value
                    .parse::<f64>()
                    .map_err(|_| format!("invalid floating-point literal '{value}'"))?;
                if matches!(ty, Type::F32) {
                    let bits = (parsed as f32).to_bits();
                    self.output
                        .push_str(&format!("    mov eax, 0x{bits:x}\n    movd xmm0, eax\n"));
                } else {
                    self.output.push_str(&format!(
                        "    mov rax, 0x{:x}\n    movq xmm0, rax\n",
                        parsed.to_bits()
                    ));
                }
                Ok(())
            }
            _ => self.expression(expression),
        }
    }

    fn if_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 4 {
            return Err("if requires a condition, then expression, and else expression".into());
        }
        let else_label = self.label("else");
        let end_label = self.label("endif");
        self.expression(&items[1])?;
        self.output
            .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
        self.expression(&items[2])?;
        self.output
            .push_str(&format!("    jmp {end_label}\n{else_label}:\n"));
        self.expression(&items[3])?;
        self.output.push_str(&format!("{end_label}:\n"));
        Ok(())
    }

    fn call(&mut self, name: &str, arguments: &[Expr]) -> Result<(), String> {
        if arguments.len() > 32 {
            return Err(format!("call to '{name}' has more than 32 arguments"));
        }
        let abi = self
            .functions
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown function '{name}'"))?;
        if arguments.len() != abi.parameters.len() {
            return Err(format!("call to '{name}' has the wrong argument count"));
        }
        if abi.parameters.iter().all(is_float_type) {
            if let Some(ty) = abi.parameters.first() {
                if abi.parameters.iter().all(|other| other == ty) {
                    return self.call_float(name, arguments, ty);
                }
            }
        }
        if abi.parameters.iter().any(is_float_type) {
            return self.call_mixed(name, arguments, &abi.parameters);
        }
        let word_count = abi
            .parameters
            .iter()
            .map(|ty| value_word_count(ty, &self.structs, &self.enums))
            .collect::<Result<Vec<_>, _>>()?;
        let total_words = word_count.iter().sum::<usize>();
        if total_words > 32 {
            return Err(format!("call to '{name}' has more than 32 machine words"));
        }
        if total_words > ARGUMENT_REGISTERS.len() {
            let stack_arguments = total_words - ARGUMENT_REGISTERS.len();
            let needs_padding = (self.stack_depth + stack_arguments) % 2 == 1;
            if needs_padding {
                self.output.push_str("    sub rsp, 8\n");
                self.stack_depth += 1;
            }
            for (argument, ty) in arguments.iter().zip(&abi.parameters).rev() {
                self.push_value_words(argument, ty, true)?;
            }
            for (index, register) in ARGUMENT_REGISTERS.iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [rsp+{}]\n",
                    index * 8
                ));
            }
            self.output.push_str("    add rsp, 48\n");
            self.stack_depth -= ARGUMENT_REGISTERS.len();
            self.output.push_str(&format!("    call {name}\n"));
            self.output
                .push_str(&format!("    add rsp, {}\n", stack_arguments * 8));
            self.stack_depth -= stack_arguments;
            if needs_padding {
                self.output.push_str("    add rsp, 8\n");
                self.stack_depth -= 1;
            }
            return Ok(());
        }
        for (argument, ty) in arguments.iter().zip(&abi.parameters) {
            self.push_value_words(argument, ty, false)?;
        }
        for register in ARGUMENT_REGISTERS[..total_words].iter().rev() {
            self.output.push_str(&format!("    pop {register}\n"));
            self.stack_depth -= 1;
        }
        let needs_padding = self.stack_depth % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
        }
        self.output.push_str(&format!("    call {name}\n"));
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
        }
        Ok(())
    }

    fn call_float(&mut self, name: &str, arguments: &[Expr], ty: &Type) -> Result<(), String> {
        if arguments.len() > FLOAT_ARGUMENT_REGISTERS.len() {
            return Err(format!(
                "call to '{name}' has too many floating-point arguments"
            ));
        }
        for argument in arguments {
            self.expression_as_float(argument, ty)?;
            if matches!(ty, Type::F32) {
                self.output.push_str("    movd eax, xmm0\n    push rax\n");
            } else {
                self.output.push_str("    movq rax, xmm0\n    push rax\n");
            }
            self.stack_depth += 1;
        }
        for register in FLOAT_ARGUMENT_REGISTERS[..arguments.len()].iter().rev() {
            self.output.push_str("    pop rax\n");
            self.stack_depth -= 1;
            self.output.push_str(&format!(
                "    mov{} {register}, rax\n",
                if matches!(ty, Type::F32) { "d" } else { "q" }
            ));
        }
        let needs_padding = self.stack_depth % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
        }
        self.output.push_str(&format!("    call {name}\n"));
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
        }
        Ok(())
    }

    fn call_mixed(
        &mut self,
        name: &str,
        arguments: &[Expr],
        parameters: &[Type],
    ) -> Result<(), String> {
        if arguments.len() > ARGUMENT_REGISTERS.len() {
            return Err("native backend supports mixed calls with at most six arguments".into());
        }
        for ty in parameters {
            if value_word_count(ty, &self.structs, &self.enums)? != 1 {
                return Err(
                    "native backend does not support aggregate values in mixed calls".into(),
                );
            }
        }
        for (argument, ty) in arguments.iter().zip(parameters) {
            if is_float_type(ty) {
                self.expression_as_float(argument, ty)?;
                self.output.push_str(&format!(
                    "    mov{} {}, xmm0\n    push rax\n",
                    if matches!(ty, Type::F32) { "d" } else { "q" },
                    if matches!(ty, Type::F32) {
                        "eax"
                    } else {
                        "rax"
                    }
                ));
            } else {
                self.expression(argument)?;
                self.output.push_str("    push rax\n");
            }
            self.stack_depth += 1;
        }
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        let total = arguments.len();
        for (index, ty) in parameters.iter().enumerate() {
            let offset = (total - 1 - index) * 8;
            if is_float_type(ty) {
                self.output.push_str(&format!(
                    "    mov{} xmm{}, {} PTR [rsp+{offset}]\n",
                    if matches!(ty, Type::F32) { "d" } else { "q" },
                    float_index,
                    if matches!(ty, Type::F32) {
                        "DWORD"
                    } else {
                        "QWORD"
                    }
                ));
                float_index += 1;
            } else {
                self.output.push_str(&format!(
                    "    mov {}, QWORD PTR [rsp+{offset}]\n",
                    ARGUMENT_REGISTERS[integer_index]
                ));
                integer_index += 1;
            }
        }
        self.output
            .push_str(&format!("    add rsp, {}\n", total * 8));
        self.stack_depth -= total;
        let needs_padding = self.stack_depth % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
        }
        self.output.push_str(&format!("    call {name}\n"));
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
        }
        Ok(())
    }

    fn push_value_words(&mut self, value: &Expr, ty: &Type, reverse: bool) -> Result<(), String> {
        if let Type::Array(_, length) = ty {
            if let Expr::Symbol(local) = value {
                let Storage::Array {
                    base,
                    length: local_length,
                } = self
                    .locals
                    .get(local)
                    .ok_or_else(|| format!("unknown array local '{local}'"))?
                else {
                    return Err(format!("'{local}' is not an array"));
                };
                if local_length != length {
                    return Err("array argument length mismatch".into());
                }
                let base = *base;
                let length = *length;
                let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                    Box::new((0..length).rev())
                } else {
                    Box::new(0..length)
                };
                for index in indices {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n",
                        (base + index) * 8
                    ));
                    self.push_rax();
                }
                return Ok(());
            }
            if let Expr::List(items) = value {
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array-repeat")
                {
                    if items.len() != 2 {
                        return Err("array-repeat requires one value".into());
                    }
                    for _ in 0..*length {
                        self.expression(&items[1])?;
                        self.push_rax();
                    }
                    return Ok(());
                }
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
                    if items.len() - 1 != *length {
                        return Err("array argument has the wrong length".into());
                    }
                    let values: Box<dyn Iterator<Item = &Expr>> = if reverse {
                        Box::new(items[1..].iter().rev())
                    } else {
                        Box::new(items[1..].iter())
                    };
                    for value in values {
                        self.expression(value)?;
                        self.push_rax();
                    }
                    return Ok(());
                }
            }
            self.expression(value)?;
            let registers: Box<dyn Iterator<Item = &str>> = if reverse {
                Box::new(VALUE_REGISTERS[..*length].iter().rev().copied())
            } else {
                Box::new(VALUE_REGISTERS[..*length].iter().copied())
            };
            for register in registers {
                self.output.push_str(&format!("    push {register}\n"));
                self.stack_depth += 1;
            }
            return Ok(());
        }
        if let Type::Named(name) = ty {
            if let Some(fields) = self.structs.get(name).cloned() {
                if let Expr::Symbol(local) = value {
                    let Storage::Struct(slots) = self
                        .locals
                        .get(local)
                        .ok_or_else(|| format!("unknown struct local '{local}'"))?
                    else {
                        return Err(format!("'{local}' is not a struct"));
                    };
                    let slots = slots.clone();
                    let range: Box<dyn Iterator<Item = &(String, usize)>> = if reverse {
                        Box::new(slots.iter().rev())
                    } else {
                        Box::new(slots.iter())
                    };
                    for (_, slot) in range {
                        self.output
                            .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
                        self.push_rax();
                    }
                    return Ok(());
                }
                if let Expr::List(items) = value {
                    if matches!(items.first(), Some(Expr::Symbol(constructor)) if constructor == name)
                    {
                        if items.len() - 1 != fields.len() {
                            return Err(format!("constructor '{name}' has wrong field count"));
                        }
                        let values: Box<dyn Iterator<Item = &Expr>> = if reverse {
                            Box::new(items[1..].iter().rev())
                        } else {
                            Box::new(items[1..].iter())
                        };
                        for value in values {
                            self.expression(value)?;
                            self.push_rax();
                        }
                        return Ok(());
                    }
                }
            }
            if self
                .enums
                .get(name)
                .is_some_and(|variants| variants.iter().any(|variant| !variant.fields.is_empty()))
            {
                if let Expr::Symbol(local) = value {
                    let Storage::Enum {
                        discriminant,
                        payload,
                    } = self
                        .locals
                        .get(local)
                        .ok_or_else(|| format!("unknown enum local '{local}'"))?
                    else {
                        return Err(format!("'{local}' is not a payload enum"));
                    };
                    let slots = if reverse {
                        [*payload, *discriminant]
                    } else {
                        [*discriminant, *payload]
                    };
                    for slot in slots {
                        self.output
                            .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
                        self.push_rax();
                    }
                    return Ok(());
                }
            }
        }
        if matches!(ty, Type::Named(name) if self.enums.get(name).is_some_and(|variants| variants.iter().any(|variant| !variant.fields.is_empty())))
        {
            self.expression(value)?;
            if reverse {
                self.output.push_str("    push rdx\n");
                self.stack_depth += 1;
                self.push_rax();
            } else {
                self.push_rax();
                self.output.push_str("    push rdx\n");
                self.stack_depth += 1;
            }
            return Ok(());
        }
        self.expression(value)?;
        self.push_rax();
        Ok(())
    }

    fn push_rax(&mut self) {
        self.output.push_str("    push rax\n");
        self.stack_depth += 1;
    }

    fn label(&mut self, prefix: &str) -> String {
        let label = format!(".L{prefix}_{}_{}", self.function_name, self.labels);
        self.labels += 1;
        label
    }
}
