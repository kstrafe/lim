//! Small native x86-64 backend for the currently supported integer subset.
//!
//! The backend emits GNU assembler syntax in Intel mode and follows the Linux
//! System V ABI. It intentionally rejects types and expressions that do not
//! have a representation in this first backend instead of silently generating
//! incorrect code.

use std::collections::HashMap;

use crate::{
    check_types, parse_type, EnumVariant, Expr, Field, Function, Item, Program, Statement, Type,
};

const ARGUMENT_REGISTERS: [&str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
const VALUE_REGISTERS: [&str; 6] = ["rax", "rdx", "rcx", "r8", "r9", "rdi"];
const FLOAT_ARGUMENT_REGISTERS: [&str; 8] = [
    "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7",
];

fn asm_symbol(name: &str) -> String {
    let mut symbol = String::new();
    for byte in name.bytes() {
        if byte.is_ascii_alphanumeric() || byte == b'_' {
            symbol.push(byte as char);
        } else {
            symbol.push_str(&format!("_x{byte:02x}_"));
        }
    }
    if symbol
        .as_bytes()
        .first()
        .is_some_and(|byte| byte.is_ascii_digit())
    {
        symbol.insert(0, '_');
    }
    symbol
}

fn low_register(register: &str) -> &str {
    match register {
        "rax" => "eax",
        "rdx" => "edx",
        "rcx" => "ecx",
        "r8" => "r8d",
        "r9" => "r9d",
        "rdi" => "edi",
        _ => unreachable!("unknown native value register"),
    }
}

#[derive(Clone)]
enum GlobalValue {
    Integer(i128),
    Wide { low: u64, high: u64 },
    F32(u32),
    F64(u64),
}

#[derive(Clone)]
struct FunctionAbi {
    parameters: Vec<Type>,
    return_type: Type,
}

fn generic_call_parts(operator: &str) -> Option<(&str, Vec<&str>)> {
    let open = operator.find('<')?;
    if !operator.ends_with('>') || open == 0 {
        return None;
    }
    let base = &operator[..open];
    let arguments = &operator[open + 1..operator.len() - 1];
    if arguments.is_empty() {
        return None;
    }
    Some((base, arguments.split(',').map(str::trim).collect()))
}

fn specialized_type_name(ty: &Type) -> String {
    match ty {
        Type::Unit => "unit".into(),
        Type::Bool => "bool".into(),
        Type::Char => "char".into(),
        Type::I8 => "i8".into(),
        Type::I16 => "i16".into(),
        Type::I32 => "i32".into(),
        Type::I64 => "i64".into(),
        Type::I128 => "i128".into(),
        Type::Isize => "isize".into(),
        Type::U8 => "u8".into(),
        Type::U16 => "u16".into(),
        Type::U32 => "u32".into(),
        Type::U64 => "u64".into(),
        Type::U128 => "u128".into(),
        Type::Usize => "usize".into(),
        Type::F32 => "f32".into(),
        Type::F64 => "f64".into(),
        Type::Generic(name) | Type::Named(name) => name.clone(),
        Type::Tuple(fields) => format!(
            "tuple{}",
            fields
                .iter()
                .map(specialized_type_name)
                .collect::<Vec<_>>()
                .join("_")
        ),
        Type::Array(element, length) => {
            format!("array{}_{}", specialized_type_name(element), length)
        }
    }
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

fn substitute_expr(expression: &Expr, substitutions: &HashMap<String, Type>) -> Expr {
    match expression {
        Expr::List(items) => Expr::List(
            items
                .iter()
                .map(|item| substitute_expr(item, substitutions))
                .collect(),
        ),
        Expr::Block(statements) => Expr::Block(
            statements
                .iter()
                .map(|statement| substitute_statement(statement, substitutions))
                .collect(),
        ),
        Expr::Quote(value) => Expr::Quote(Box::new(substitute_expr(value, substitutions))),
        _ => expression.clone(),
    }
}

fn substitute_statement(statement: &Statement, substitutions: &HashMap<String, Type>) -> Statement {
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable,
        } => Statement::Let {
            name: name.clone(),
            ty: substitute_type(ty, substitutions),
            value: substitute_expr(value, substitutions),
            mutable: *mutable,
        },
        Statement::Assign { name, value } => Statement::Assign {
            name: name.clone(),
            value: substitute_expr(value, substitutions),
        },
        Statement::ArrayAssign { name, index, value } => Statement::ArrayAssign {
            name: name.clone(),
            index: substitute_expr(index, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Statement::FieldAssign { name, field, value } => Statement::FieldAssign {
            name: name.clone(),
            field: field.clone(),
            value: substitute_expr(value, substitutions),
        },
        Statement::TupleAssign { name, index, value } => Statement::TupleAssign {
            name: name.clone(),
            index: *index,
            value: substitute_expr(value, substitutions),
        },
        Statement::While { condition, body } => Statement::While {
            condition: substitute_expr(condition, substitutions),
            body: body
                .iter()
                .map(|s| substitute_statement(s, substitutions))
                .collect(),
        },
        Statement::Loop { body } => Statement::Loop {
            body: body
                .iter()
                .map(|s| substitute_statement(s, substitutions))
                .collect(),
        },
        Statement::For {
            init,
            condition,
            step,
            body,
        } => Statement::For {
            init: Box::new(substitute_statement(init, substitutions)),
            condition: substitute_expr(condition, substitutions),
            step: Box::new(substitute_statement(step, substitutions)),
            body: body
                .iter()
                .map(|s| substitute_statement(s, substitutions))
                .collect(),
        },
        Statement::Return(value) => Statement::Return(
            value
                .as_ref()
                .map(|value| substitute_expr(value, substitutions)),
        ),
        Statement::Expr(value) => Statement::Expr(substitute_expr(value, substitutions)),
        Statement::Break | Statement::Continue => statement.clone(),
    }
}

fn rewrite_expr(expression: &Expr, specializations: &HashMap<String, String>) -> Expr {
    match expression {
        Expr::List(items) => Expr::List(
            items
                .iter()
                .map(|item| rewrite_expr(item, specializations))
                .collect(),
        ),
        Expr::Block(statements) => Expr::Block(
            statements
                .iter()
                .map(|statement| rewrite_statement(statement, specializations))
                .collect(),
        ),
        Expr::Quote(value) => Expr::Quote(Box::new(rewrite_expr(value, specializations))),
        Expr::Symbol(name) => specializations
            .get(name)
            .cloned()
            .map(Expr::Symbol)
            .unwrap_or_else(|| expression.clone()),
        _ => expression.clone(),
    }
}

fn rewrite_statement(
    statement: &Statement,
    specializations: &HashMap<String, String>,
) -> Statement {
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable,
        } => Statement::Let {
            name: name.clone(),
            ty: ty.clone(),
            value: rewrite_expr(value, specializations),
            mutable: *mutable,
        },
        Statement::Assign { name, value } => Statement::Assign {
            name: name.clone(),
            value: rewrite_expr(value, specializations),
        },
        Statement::ArrayAssign { name, index, value } => Statement::ArrayAssign {
            name: name.clone(),
            index: rewrite_expr(index, specializations),
            value: rewrite_expr(value, specializations),
        },
        Statement::FieldAssign { name, field, value } => Statement::FieldAssign {
            name: name.clone(),
            field: field.clone(),
            value: rewrite_expr(value, specializations),
        },
        Statement::TupleAssign { name, index, value } => Statement::TupleAssign {
            name: name.clone(),
            index: *index,
            value: rewrite_expr(value, specializations),
        },
        Statement::While { condition, body } => Statement::While {
            condition: rewrite_expr(condition, specializations),
            body: body
                .iter()
                .map(|s| rewrite_statement(s, specializations))
                .collect(),
        },
        Statement::Loop { body } => Statement::Loop {
            body: body
                .iter()
                .map(|s| rewrite_statement(s, specializations))
                .collect(),
        },
        Statement::For {
            init,
            condition,
            step,
            body,
        } => Statement::For {
            init: Box::new(rewrite_statement(init, specializations)),
            condition: rewrite_expr(condition, specializations),
            step: Box::new(rewrite_statement(step, specializations)),
            body: body
                .iter()
                .map(|s| rewrite_statement(s, specializations))
                .collect(),
        },
        Statement::Return(value) => Statement::Return(
            value
                .as_ref()
                .map(|value| rewrite_expr(value, specializations)),
        ),
        Statement::Expr(value) => Statement::Expr(rewrite_expr(value, specializations)),
        Statement::Break | Statement::Continue => statement.clone(),
    }
}

fn collect_generic_calls_expr(expression: &Expr, calls: &mut Vec<String>) {
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                if generic_call_parts(operator).is_some() {
                    calls.push(operator.clone());
                }
            }
            for item in items {
                collect_generic_calls_expr(item, calls);
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_generic_calls_statement(statement, calls);
            }
        }
        Expr::Quote(value) => collect_generic_calls_expr(value, calls),
        _ => {}
    }
}

fn collect_generic_calls_statement(statement: &Statement, calls: &mut Vec<String>) {
    match statement {
        Statement::Let { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => collect_generic_calls_expr(value, calls),
        Statement::ArrayAssign { index, value, .. } => {
            collect_generic_calls_expr(index, calls);
            collect_generic_calls_expr(value, calls);
        }
        Statement::While { condition, body } => {
            collect_generic_calls_expr(condition, calls);
            for statement in body {
                collect_generic_calls_statement(statement, calls);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_generic_calls_statement(statement, calls);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_generic_calls_statement(init, calls);
            collect_generic_calls_expr(condition, calls);
            collect_generic_calls_statement(step, calls);
            for statement in body {
                collect_generic_calls_statement(statement, calls);
            }
        }
        Statement::Break | Statement::Continue | Statement::Return(None) => {}
    }
}

fn monomorphize_program(
    program: &Program,
    aliases: &HashMap<String, Type>,
) -> Result<Program, String> {
    let generic_functions: HashMap<String, Function> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) if !function.type_parameters.is_empty() => {
                Some((function.name.clone(), function.clone()))
            }
            _ => None,
        })
        .collect();
    let mut specializations = HashMap::new();
    let mut generated = Vec::new();
    let mut pending = Vec::new();
    for item in &program.items {
        if let Item::Function(function) = item {
            for statement in &function.body {
                collect_generic_calls_statement(statement, &mut pending);
            }
        }
    }
    let mut cursor = 0;
    while cursor < pending.len() {
        let operator = pending[cursor].clone();
        cursor += 1;
        if specializations.contains_key(&operator) {
            continue;
        }
        let Some((base, arguments)) = generic_call_parts(&operator) else {
            continue;
        };
        let Some(template) = generic_functions.get(base) else {
            return Err(format!("unknown generic function '{base}'"));
        };
        if arguments.len() != template.type_parameters.len() {
            return Err(format!(
                "generic function '{base}' expects {} type arguments, got {}",
                template.type_parameters.len(),
                arguments.len()
            ));
        }
        let concrete = arguments
            .iter()
            .map(|argument| resolve_type(&Type::from_name(argument), aliases))
            .collect::<Result<Vec<_>, _>>()?;
        let mut substitutions = HashMap::new();
        for (parameter, ty) in template.type_parameters.iter().zip(&concrete) {
            substitutions.insert(parameter.clone(), ty.clone());
        }
        let name = format!(
            "{}${}",
            base,
            concrete
                .iter()
                .map(specialized_type_name)
                .collect::<Vec<_>>()
                .join("$")
        );
        specializations.insert(operator, name.clone());
        let mut function = template.clone();
        function.name = name;
        function.type_parameters.clear();
        for parameter in &mut function.parameters {
            parameter.ty = substitute_type(&parameter.ty, &substitutions);
        }
        function.return_type = substitute_type(&function.return_type, &substitutions);
        function.body = function
            .body
            .iter()
            .map(|statement| substitute_statement(statement, &substitutions))
            .map(|statement| rewrite_statement(&statement, &specializations))
            .collect();
        let mut nested = Vec::new();
        for statement in &function.body {
            collect_generic_calls_statement(statement, &mut nested);
        }
        pending.extend(nested);
        generated.push(function);
    }
    let mut items = Vec::new();
    for item in &program.items {
        if !matches!(item, Item::Function(function) if !function.type_parameters.is_empty()) {
            items.push(item.clone());
        }
    }
    items.extend(generated.into_iter().map(Item::Function));
    for item in &mut items {
        if let Item::Function(function) = item {
            function.body = function
                .body
                .iter()
                .map(|statement| rewrite_statement(statement, &specializations))
                .collect();
        }
    }
    Ok(Program { items })
}

pub fn generate_assembly(program: &Program) -> Result<String, String> {
    check_types(program)?;
    let aliases: HashMap<String, Type> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. } => Some((name.clone(), target.clone())),
            _ => None,
        })
        .collect();
    let program = monomorphize_program(program, &aliases)?;
    let structs: HashMap<String, Vec<Field>> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields, .. } => Some((
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
    let mut enums = HashMap::new();
    for item in &program.items {
        if let Item::Enum { name, variants, .. } = item {
            let variants = variants
                .iter()
                .map(|variant| {
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
            enums.insert(name.clone(), variants);
        }
    }
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
    let mut global_types = HashMap::new();
    let mut constants = HashMap::new();
    for item in &program.items {
        let (name, ty, value, mutable) = match item {
            Item::Let {
                name,
                ty,
                value,
                mutable,
            } => (name, ty, value, *mutable),
            Item::Static { name, ty, value } => (name, ty, value, false),
            _ => continue,
        };
        {
            if mutable {
                return Err(format!("top-level binding '{name}' cannot be mutable"));
            }
            let ty = resolve_type(ty, &aliases)?;
            if !is_wide_integer(&ty) {
                ensure_scalar_type(&ty, &enums)?;
            }
            let global = match &ty {
                Type::I128 | Type::U128 => {
                    let value = constant_value(value, &enums, &constants)? as u128;
                    if matches!(item, Item::Let { .. }) {
                        constants.insert(name.clone(), value as i128);
                    }
                    GlobalValue::Wide {
                        low: value as u64,
                        high: (value >> 64) as u64,
                    }
                }
                Type::F32 => {
                    let Expr::Float(value) = value else {
                        return Err(format!("global '{name}' requires an f32 literal"));
                    };
                    GlobalValue::F32(
                        value
                            .parse::<f32>()
                            .map_err(|_| format!("invalid f32 global '{name}'"))?
                            .to_bits(),
                    )
                }
                Type::F64 => {
                    let Expr::Float(value) = value else {
                        return Err(format!("global '{name}' requires an f64 literal"));
                    };
                    GlobalValue::F64(
                        value
                            .parse::<f64>()
                            .map_err(|_| format!("invalid f64 global '{name}'"))?
                            .to_bits(),
                    )
                }
                _ => {
                    let normalized =
                        normalize_global_integer(constant_value(value, &enums, &constants)?, &ty);
                    if matches!(item, Item::Let { .. }) {
                        constants.insert(name.clone(), normalized);
                    }
                    GlobalValue::Integer(normalized)
                }
            };
            global_types.insert(name.clone(), ty);
            globals.insert(name.clone(), global);
        }
    }
    let mut output = String::from(".intel_syntax noprefix\n");
    if !globals.is_empty() {
        output.push_str(".section .rodata\n");
        for (name, value) in &globals {
            let symbol = asm_symbol(name);
            match value {
                GlobalValue::Integer(value) => {
                    output.push_str(&format!(".align 8\n{symbol}:\n    .quad {value}\n"));
                }
                GlobalValue::Wide { low, high } => {
                    output.push_str(&format!(
                        ".align 8\n{symbol}:\n    .quad {low}\n    .quad {high}\n"
                    ));
                }
                GlobalValue::F32(value) => {
                    output.push_str(&format!(".align 8\n{symbol}:\n    .long {value}\n"));
                }
                GlobalValue::F64(value) => {
                    output.push_str(&format!(".align 8\n{symbol}:\n    .quad {value}\n"));
                }
            }
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
                &global_types,
                &aliases,
                &functions,
            )?,
            Item::Struct { .. } => {}
            Item::Enum { .. } => {}
            Item::TypeAlias { .. } => {}
            Item::Let { .. } | Item::Static { .. } => {}
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
    globals: &HashMap<String, GlobalValue>,
    global_types: &HashMap<String, Type>,
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
        collect_local_types(statement, &mut local_types, aliases, enums);
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
    let function_symbol = asm_symbol(&function.name);

    output.push_str(&format!(
        ".globl {}\n.type {}, @function\n{}:\n",
        function_symbol, function_symbol, function_symbol
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
        let integer_words = function
            .parameters
            .iter()
            .filter_map(|parameter| resolve_type(&parameter.ty, aliases).ok())
            .filter(|ty| !is_float_type(ty))
            .map(|ty| value_word_count(&ty, structs, enums))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .sum::<usize>();
        if integer_words > ARGUMENT_REGISTERS.len() {
            return Err("native mixed calls support at most six integer ABI words".into());
        }
        let float_words = function
            .parameters
            .iter()
            .filter(|parameter| {
                resolve_type(&parameter.ty, aliases)
                    .ok()
                    .is_some_and(|ty| is_float_type(&ty))
            })
            .count();
        if float_words > FLOAT_ARGUMENT_REGISTERS.len() {
            return Err("native mixed calls support at most eight floating ABI words".into());
        }
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        for parameter in &function.parameters {
            let ty = resolve_type(&parameter.ty, aliases)?;
            if matches!(ty, Type::F32 | Type::F64) {
                let slot = local_slots(&locals, &parameter.name)?[0];
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
                let words = value_word_count(&ty, structs, enums)?;
                for slot in local_slots(&locals, &parameter.name)?
                    .into_iter()
                    .take(words)
                {
                    output.push_str(&format!(
                        "    mov QWORD PTR [rbp-{}], {}\n",
                        slot * 8,
                        ARGUMENT_REGISTERS[integer_index]
                    ));
                    integer_index += 1;
                }
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
            let register_type = ty.clone();
            output.push_str(&format!(
                "    {} QWORD PTR [rbp-{}], {}\n",
                if matches!(register_type, Type::F32) {
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

    let return_label = format!(".Lreturn_{}", asm_symbol(&function.name));
    let mut context = FunctionContext {
        locals,
        structs: structs.clone(),
        enums: enums.clone(),
        globals: globals.clone(),
        global_types: global_types.clone(),
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
    enums: &HashMap<String, Vec<EnumVariant>>,
) {
    match statement {
        Statement::Let {
            name, ty, value, ..
        } => {
            if let Ok(ty) = resolve_type(ty, aliases) {
                types.insert(name.clone(), ty);
            }
            collect_expr_types(value, types, aliases, enums);
        }
        Statement::While { condition, body } => {
            collect_expr_types(condition, types, aliases, enums);
            for statement in body {
                collect_local_types(statement, types, aliases, enums);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_local_types(statement, types, aliases, enums);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_local_types(init, types, aliases, enums);
            collect_expr_types(condition, types, aliases, enums);
            collect_local_types(step, types, aliases, enums);
            for statement in body {
                collect_local_types(statement, types, aliases, enums);
            }
        }
        Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => collect_expr_types(value, types, aliases, enums),
        Statement::ArrayAssign { index, value, .. } => {
            collect_expr_types(index, types, aliases, enums);
            collect_expr_types(value, types, aliases, enums);
        }
        Statement::Break | Statement::Continue | Statement::Return(None) => {}
    }
}

fn collect_expr_types(
    expression: &Expr,
    types: &mut HashMap<String, Type>,
    aliases: &HashMap<String, Type>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) {
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                for arm in items.iter().skip(2) {
                    let Expr::List(arm) = arm else { continue };
                    let Some(Expr::List(pattern)) = arm.first() else {
                        continue;
                    };
                    let Some(Expr::Symbol(variant_name)) = pattern.first() else {
                        continue;
                    };
                    let Some(variant) = enums
                        .values()
                        .flat_map(|variants| variants.iter())
                        .find(|variant| variant.name == *variant_name)
                    else {
                        continue;
                    };
                    for (binding, field_type) in pattern[1..].iter().zip(&variant.fields) {
                        let Expr::Symbol(binding) = binding else {
                            continue;
                        };
                        if binding != "_" {
                            if let Ok(field_type) = resolve_type(field_type, aliases) {
                                types.entry(binding.clone()).or_insert(field_type);
                            }
                        }
                    }
                }
            }
            for item in items {
                collect_expr_types(item, types, aliases, enums);
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_local_types(statement, types, aliases, enums);
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
        Statement::TupleAssign { value, .. } => {
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
                    if pattern.len() < 2 {
                        continue;
                    }
                    let Some(Expr::Symbol(variant_name)) = pattern.first() else {
                        continue;
                    };
                    let Some(fields) = enums.values().find_map(|variants| {
                        variants
                            .iter()
                            .find(|variant| variant.name == *variant_name)
                            .map(|variant| variant.fields.clone())
                    }) else {
                        continue;
                    };
                    for (binding, field_type) in pattern[1..].iter().zip(fields) {
                        let Expr::Symbol(binding) = binding else {
                            continue;
                        };
                        if binding == "_" || locals.contains_key(binding) {
                            continue;
                        }
                        add_local(
                            locals,
                            binding,
                            &field_type,
                            structs,
                            enums,
                            aliases,
                            next_slot,
                        )?;
                    }
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
                let discriminant = *next_slot;
                *next_slot += 1;
                let payload_count = variants
                    .iter()
                    .map(|variant| variant.fields.len())
                    .max()
                    .unwrap_or(0);
                let mut payload = Vec::with_capacity(payload_count);
                for index in 0..payload_count {
                    let field = variants
                        .iter()
                        .find_map(|variant| variant.fields.get(index))
                        .ok_or_else(|| "enum payload metadata is invalid".to_owned())?;
                    ensure_scalar_type(field, enums).map_err(|_| {
                        "native backend only supports scalar enum payloads".to_owned()
                    })?;
                    payload.push(*next_slot);
                    *next_slot += 1;
                }
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
    } else if is_wide_integer(&ty) {
        let low = *next_slot;
        let high = low + 1;
        *next_slot += 2;
        Storage::Wide { low, high }
    } else if let Type::Array(element, length) = &ty {
        ensure_scalar_type(element, enums)
            .map_err(|_| "native backend only supports arrays of scalar values".to_owned())?;
        let base = *next_slot;
        *next_slot += length;
        Storage::Array {
            base,
            length: *length,
        }
    } else if let Type::Tuple(fields) = &ty {
        for field in fields {
            ensure_scalar_type(field, enums)
                .map_err(|_| "native backend only supports tuples of scalar values".to_owned())?;
        }
        let base = *next_slot;
        *next_slot += fields.len();
        Storage::Tuple((base..base + fields.len()).collect())
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
        Storage::Wide { low, high } => Ok(vec![*low, *high]),
        Storage::Struct(slots) => Ok(slots.iter().map(|(_, slot)| *slot).collect()),
        Storage::Enum {
            discriminant,
            payload,
        } => Ok(std::iter::once(*discriminant)
            .chain(payload.iter().copied())
            .collect()),
        Storage::Array { base, length } => Ok((*base..*base + *length).collect()),
        Storage::Tuple(slots) => Ok(slots.clone()),
    }
}

fn value_word_count(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<usize, String> {
    if is_wide_integer(ty) {
        return Ok(2);
    }
    if ensure_scalar_type(ty, enums).is_ok() {
        return Ok(1);
    }
    if let Type::Named(name) = ty {
        if let Some(fields) = structs.get(name) {
            if fields.len() <= VALUE_REGISTERS.len()
                && fields
                    .iter()
                    .all(|field| ensure_scalar_type(&field.ty, enums).is_ok())
            {
                return Ok(fields.len());
            }
        }
        if let Some(variants) = enums.get(name) {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                let payload_count = variants
                    .iter()
                    .map(|variant| variant.fields.len())
                    .max()
                    .unwrap_or(0);
                if payload_count + 1 > VALUE_REGISTERS.len()
                    || !variants
                        .iter()
                        .flat_map(|variant| variant.fields.iter())
                        .all(|field| ensure_scalar_type(field, enums).is_ok())
                {
                    return Err(format!(
                        "native ABI does not support enum value type {ty:?}"
                    ));
                }
                return Ok(1 + payload_count);
            }
        }
    }
    if let Type::Array(element, length) = ty {
        if *length <= VALUE_REGISTERS.len() && ensure_scalar_type(element, enums).is_ok() {
            return Ok(*length);
        }
    }
    if let Type::Tuple(fields) = ty {
        if fields.len() <= VALUE_REGISTERS.len()
            && fields
                .iter()
                .all(|field| ensure_scalar_type(field, enums).is_ok())
        {
            return Ok(fields.len());
        }
    }
    Err(format!("native ABI does not support value type {ty:?}"))
}

#[derive(Clone, Debug)]
enum Storage {
    Scalar(usize),
    Array {
        base: usize,
        length: usize,
    },
    Tuple(Vec<usize>),
    Struct(Vec<(String, usize)>),
    Wide {
        low: usize,
        high: usize,
    },
    Enum {
        discriminant: usize,
        payload: Vec<usize>,
    },
}

fn scalar_slot(locals: &HashMap<String, Storage>, name: &str) -> usize {
    match locals.get(name).expect("validated local") {
        Storage::Scalar(slot) => *slot,
        Storage::Array { .. }
        | Storage::Tuple(_)
        | Storage::Struct(_)
        | Storage::Wide { .. }
        | Storage::Enum { .. } => {
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
            | Type::Isize
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::Usize
    ) {
        Ok(())
    } else {
        Err(format!(
            "native integer backend does not support type {ty:?}"
        ))
    }
}

fn is_narrow_integer(ty: &Type) -> bool {
    ensure_integer_type(ty).is_ok()
}

fn integer_bit_width(ty: Type) -> Option<i128> {
    match ty {
        Type::I8 | Type::U8 => Some(8),
        Type::I16 | Type::U16 => Some(16),
        Type::I32 | Type::U32 => Some(32),
        Type::I64 | Type::U64 | Type::Isize | Type::Usize => Some(64),
        Type::I128 | Type::U128 => Some(128),
        _ => None,
    }
}

fn is_unsigned_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 | Type::Usize
    )
}

fn is_wide_integer(ty: &Type) -> bool {
    matches!(ty, Type::I128 | Type::U128)
}

fn is_float_type(ty: &Type) -> bool {
    matches!(ty, Type::F32 | Type::F64)
}

fn ensure_scalar_type(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> Result<(), String> {
    if matches!(ty, Type::F32 | Type::F64) {
        return Ok(());
    }
    if is_wide_integer(ty) {
        return Err("128-bit integers occupy two native words".into());
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
    if matches!(ty, Type::Unit) {
        return Ok(());
    }
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
        if fields.len() <= VALUE_REGISTERS.len()
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
        Type::Tuple(fields) => Ok(Type::Tuple(
            fields
                .iter()
                .map(|field| resolve_type(field, aliases))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        _ => Ok(ty.clone()),
    }
}

fn constant_value(
    expression: &Expr,
    enums: &HashMap<String, Vec<EnumVariant>>,
    constants: &HashMap<String, i128>,
) -> Result<i128, String> {
    match expression {
        Expr::Integer(value) => Ok(*value),
        Expr::UnsignedInteger(value) => (*value)
            .try_into()
            .map_err(|_| "unsigned constant is too large for the native global evaluator".into()),
        Expr::Char(value) => Ok(*value as i128),
        Expr::Float(_) => Err("floating-point global initializers are not supported".into()),
        Expr::Symbol(name) if name == "true" => Ok(1),
        Expr::Symbol(name) if name == "false" => Ok(0),
        Expr::Symbol(name) if constants.contains_key(name) => Ok(constants[name]),
        Expr::Symbol(name) => enums
            .values()
            .find_map(|variants| {
                variants
                    .iter()
                    .position(|variant| variant.name == *name)
                    .map(|value| value as i128)
            })
            .ok_or_else(|| format!("global initializer '{name}' is not a constant")),
        Expr::List(items) if items.len() == 2 => {
            let operator = match &items[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => return Err("global initializer is not constant".into()),
            };
            let value = constant_value(&items[1], enums, constants)?;
            match operator {
                "-" => value
                    .checked_neg()
                    .ok_or_else(|| "constant negation overflowed".into()),
                "!" => Ok(!value),
                _ => Err("global initializer is not constant".into()),
            }
        }
        Expr::List(items) if items.len() == 3 => {
            let operator = match &items[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => return Err("global initializer is not constant".into()),
            };
            let left = constant_value(&items[1], enums, constants)?;
            let right = constant_value(&items[2], enums, constants)?;
            match operator {
                "+" => left
                    .checked_add(right)
                    .ok_or_else(|| "constant addition overflowed".into()),
                "-" => left
                    .checked_sub(right)
                    .ok_or_else(|| "constant subtraction overflowed".into()),
                "*" => left
                    .checked_mul(right)
                    .ok_or_else(|| "constant multiplication overflowed".into()),
                "/" => left
                    .checked_div(right)
                    .ok_or_else(|| "constant division failed".into()),
                "%" => left
                    .checked_rem(right)
                    .ok_or_else(|| "constant remainder failed".into()),
                "&" => Ok(left & right),
                "|" => Ok(left | right),
                "^" => Ok(left ^ right),
                "<<" => {
                    if !(0..128).contains(&right) {
                        return Err("constant shift count is out of range".into());
                    }
                    left.checked_shl(right as u32)
                        .ok_or_else(|| "constant left shift overflowed".into())
                }
                ">>" => {
                    if !(0..128).contains(&right) {
                        return Err("constant shift count is out of range".into());
                    }
                    Ok(left >> right)
                }
                "<" => Ok(i128::from(left < right)),
                "<=" => Ok(i128::from(left <= right)),
                ">" => Ok(i128::from(left > right)),
                ">=" => Ok(i128::from(left >= right)),
                "==" => Ok(i128::from(left == right)),
                "!=" => Ok(i128::from(left != right)),
                "&&" => Ok(i128::from(left != 0 && right != 0)),
                "||" => Ok(i128::from(left != 0 || right != 0)),
                _ => Err("global initializer is not constant".into()),
            }
        }
        _ => Err("global initializer is not constant".into()),
    }
}

fn normalize_global_integer(value: i128, ty: &Type) -> i128 {
    match ty {
        Type::I8 => (value as i8) as i128,
        Type::I16 => (value as i16) as i128,
        Type::I32 => (value as i32) as i128,
        Type::I64 | Type::Isize => (value as i64) as i128,
        Type::U8 => (value as u8) as i128,
        Type::U16 => (value as u16) as i128,
        Type::U32 => (value as u32) as i128,
        Type::U64 | Type::Usize => (value as u64) as i128,
        Type::Bool => i128::from(value != 0),
        Type::Char => (value as u32) as i128,
        _ => value,
    }
}

struct FunctionContext {
    locals: HashMap<String, Storage>,
    structs: HashMap<String, Vec<Field>>,
    enums: HashMap<String, Vec<EnumVariant>>,
    globals: HashMap<String, GlobalValue>,
    global_types: HashMap<String, Type>,
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
                } else if matches!(ty, Type::Tuple(_)) {
                    self.store_tuple(name, value)?;
                } else if is_wide_integer(&ty) {
                    self.expression(value)?;
                    let Storage::Wide { low, high } = self
                        .locals
                        .get(name)
                        .ok_or_else(|| format!("unknown variable '{name}'"))?
                    else {
                        return Err(format!("'{name}' is not a 128-bit integer"));
                    };
                    self.output.push_str(&format!(
                        "    mov QWORD PTR [rbp-{}], rax\n    mov QWORD PTR [rbp-{}], rdx\n",
                        low * 8,
                        high * 8
                    ));
                } else {
                    if is_float_type(&ty) {
                        self.expression_as_float(value, &ty)?;
                    } else {
                        self.expression(value)?;
                        if is_narrow_integer(&ty) {
                            self.normalize_integer(&ty)?;
                        }
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
                if let Some(ty) = expected.as_ref() {
                    match ty {
                        Type::Named(type_name)
                            if self.enums.get(type_name).is_some_and(|variants| {
                                variants.iter().any(|variant| !variant.fields.is_empty())
                            }) =>
                        {
                            return self.store_enum(name, type_name, value);
                        }
                        Type::Named(type_name) if self.structs.contains_key(type_name) => {
                            return self.store_struct(name, type_name, value);
                        }
                        Type::Tuple(_) => return self.store_tuple(name, value),
                        Type::Array(_, _) => return self.store_array(name, value),
                        _ => {}
                    }
                }
                if let Some(ty) = expected.as_ref().filter(|ty| is_float_type(ty)) {
                    self.expression_as_float(value, ty)?;
                } else {
                    self.expression(value)?;
                    if let Some(ty) = expected.as_ref().filter(|ty| is_narrow_integer(ty)) {
                        self.normalize_integer(ty)?;
                    }
                }
                let storage = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown variable '{name}'"))?;
                if let Storage::Wide { low, high } = storage {
                    let (low, high) = (*low, *high);
                    self.output.push_str(&format!(
                        "    mov QWORD PTR [rbp-{}], rax\n    mov QWORD PTR [rbp-{}], rdx\n",
                        low * 8,
                        high * 8
                    ));
                    return Ok(());
                }
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
                let element_type = match self.local_types.get(name).cloned() {
                    Some(Type::Array(element, _)) => *element,
                    _ => return Err(format!("'{name}' is not an array")),
                };
                let bounds_failure = self.label("bounds_failure");
                self.expression(index)?;
                self.output.push_str(&format!(
                    "    cmp rax, {length}\n    jae {bounds_failure}\n"
                ));
                self.push_rax();
                if is_float_type(&element_type) {
                    self.expression_as_float(value, &element_type)?;
                    if matches!(element_type, Type::F32) {
                        self.output.push_str("    movd edx, xmm0\n");
                    } else {
                        self.output.push_str("    movq rdx, xmm0\n");
                    }
                } else {
                    self.expression(value)?;
                    self.output.push_str("    mov rdx, rax\n");
                }
                self.output.push_str("    pop rcx\n");
                self.stack_depth -= 1;
                let store = if matches!(element_type, Type::F32) {
                    "mov DWORD PTR [rax], edx"
                } else if matches!(element_type, Type::F64) {
                    "mov QWORD PTR [rax], rdx"
                } else {
                    "mov QWORD PTR [rax], rdx"
                };
                self.output.push_str(&format!(
                    "    lea rax, [rbp-{}]\n    shl rcx, 3\n    sub rax, rcx\n    {store}\n",
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
                let struct_name = match self.local_types.get(name) {
                    Some(Type::Named(name)) => name,
                    _ => return Err(format!("'{name}' is not a struct")),
                };
                let field_type = self
                    .structs
                    .get(struct_name)
                    .and_then(|fields| fields.iter().find(|field_info| field_info.name == *field))
                    .map(|field_info| field_info.ty.clone())
                    .ok_or_else(|| format!("unknown field '{field}'"))?;
                self.store_scalar_at_slot(value, &field_type, slot)?;
            }
            Statement::TupleAssign { name, index, value } => {
                let Storage::Tuple(slots) = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown tuple local '{name}'"))?
                else {
                    return Err(format!("'{name}' is not a tuple"));
                };
                let slot = *slots
                    .get(*index)
                    .ok_or_else(|| format!("tuple field index {index} is out of bounds"))?;
                let field_type = match self.local_types.get(name).cloned() {
                    Some(Type::Tuple(fields)) => fields
                        .get(*index)
                        .cloned()
                        .ok_or_else(|| format!("tuple field index {index} is out of bounds"))?,
                    _ => return Err(format!("'{name}' is not a tuple")),
                };
                self.store_scalar_at_slot(value, &field_type, slot)?;
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

    fn store_scalar_at_slot(&mut self, value: &Expr, ty: &Type, slot: usize) -> Result<(), String> {
        if matches!(ty, Type::F32) {
            self.expression_as_float(value, ty)?;
            self.output.push_str(&format!(
                "    movd eax, xmm0\n    mov DWORD PTR [rbp-{}], eax\n",
                slot * 8
            ));
        } else if matches!(ty, Type::F64) {
            self.expression_as_float(value, ty)?;
            self.output.push_str(&format!(
                "    movq rax, xmm0\n    mov QWORD PTR [rbp-{}], rax\n",
                slot * 8
            ));
        } else {
            self.expression(value)?;
            if is_narrow_integer(ty) {
                self.normalize_integer(ty)?;
            }
            self.output
                .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
        }
        Ok(())
    }

    fn expression_as_expected(&mut self, value: &Expr, ty: &Type) -> Result<(), String> {
        if is_float_type(ty) {
            self.expression_as_float(value, ty)
        } else {
            self.expression(value)
        }
    }

    fn expression_as_abi_word(&mut self, value: &Expr, ty: &Type) -> Result<(), String> {
        if matches!(ty, Type::F32 | Type::F64) {
            self.expression_as_float(value, ty)?;
            if matches!(ty, Type::F32) {
                self.output.push_str("    movd eax, xmm0\n");
            } else {
                self.output.push_str("    movq rax, xmm0\n");
            }
            Ok(())
        } else {
            self.expression(value)
        }
    }

    fn cast_expression(&mut self, value: &Expr, target: &Type) -> Result<(), String> {
        let source = self.expression_type(value).unwrap_or(Type::I64);
        if source == *target {
            return self.expression_as_expected(value, target);
        }
        if matches!(target, Type::F32 | Type::F64) {
            if matches!(source, Type::F32 | Type::F64) {
                self.expression_as_float(value, &source)?;
                if matches!((&source, target), (Type::F32, Type::F64)) {
                    self.output.push_str("    cvtss2sd xmm0, xmm0\n");
                } else if matches!((&source, target), (Type::F64, Type::F32)) {
                    self.output.push_str("    cvtsd2ss xmm0, xmm0\n");
                }
            } else {
                self.expression(value)?;
                if matches!(target, Type::F32) {
                    self.output.push_str("    cvtsi2ss xmm0, rax\n");
                } else {
                    self.output.push_str("    cvtsi2sd xmm0, rax\n");
                }
            }
            return Ok(());
        }
        if is_wide_integer(target) {
            if matches!(source, Type::F32 | Type::F64) {
                self.expression_as_float(value, &source)?;
                if matches!(source, Type::F32) {
                    self.output.push_str("    cvttss2si rax, xmm0\n");
                } else {
                    self.output.push_str("    cvttsd2si rax, xmm0\n");
                }
            } else {
                self.expression(value)?;
            }
            if is_wide_integer(&source) {
                return Ok(());
            }
            self.normalize_integer(&source)?;
            if matches!(target, Type::U128) || is_unsigned_type(&source) {
                self.output.push_str("    xor edx, edx\n");
            } else {
                self.output.push_str("    mov rdx, rax\n    sar rdx, 63\n");
            }
            return Ok(());
        }
        if matches!(source, Type::F32 | Type::F64) {
            self.expression_as_float(value, &source)?;
            if matches!(source, Type::F32) {
                self.output.push_str("    cvttss2si rax, xmm0\n");
            } else {
                self.output.push_str("    cvttsd2si rax, xmm0\n");
            }
            return self.normalize_integer(target);
        }
        self.expression(value)?;
        self.normalize_integer(target)
    }

    fn normalize_integer(&mut self, target: &Type) -> Result<(), String> {
        match target {
            Type::I8 => self.output.push_str("    movsx rax, al\n"),
            Type::I16 => self.output.push_str("    movsx rax, ax\n"),
            Type::I32 => self.output.push_str("    movsxd rax, eax\n"),
            Type::U8 => self.output.push_str("    movzx eax, al\n"),
            Type::U16 => self.output.push_str("    movzx eax, ax\n"),
            Type::U32 | Type::Char => self.output.push_str("    mov eax, eax\n"),
            Type::I64 | Type::U64 | Type::Isize | Type::Usize => {}
            Type::Bool => self.output.push_str("    movzx eax, al\n"),
            Type::I128 | Type::U128 => unreachable!("wide casts are handled before normalization"),
            _ => {
                return Err(format!(
                    "native backend cannot normalize cast target {target:?}"
                ))
            }
        }
        Ok(())
    }

    fn expression_type(&self, expression: &Expr) -> Option<Type> {
        match expression {
            Expr::Integer(_) => Some(Type::I64),
            Expr::UnsignedInteger(_) => Some(Type::U128),
            Expr::Char(_) => Some(Type::Char),
            Expr::Float(_) => Some(Type::F64),
            Expr::Symbol(name) if name == "true" || name == "false" => Some(Type::Bool),
            Expr::Symbol(name) => self.local_types.get(name).cloned().or_else(|| {
                self.enums
                    .iter()
                    .find(|(_, variants)| variants.iter().any(|variant| variant.name == *name))
                    .map(|(enum_name, _)| Type::Named(enum_name.clone()))
            }),
            Expr::List(items) => match items.first() {
                Some(Expr::Symbol(operator)) if operator == "as" && items.len() == 3 => {
                    parse_type(items.get(2))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, &self.aliases).ok())
                }
                Some(Expr::Symbol(operator))
                    if matches!(
                        operator.as_str(),
                        "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" | "!"
                    ) =>
                {
                    items.get(1).and_then(|value| self.expression_type(value))
                }
                Some(Expr::Symbol(operator))
                    if matches!(operator.as_str(), "assert" | "debug-assert") =>
                {
                    Some(Type::Unit)
                }
                Some(Expr::Symbol(operator))
                    if matches!(operator.as_str(), "size-of" | "align-of") =>
                {
                    Some(Type::Usize)
                }
                Some(Expr::Symbol(operator)) if operator == "tuple" => Some(Type::Tuple(
                    items[1..]
                        .iter()
                        .map(|value| self.expression_type(value))
                        .collect::<Option<Vec<_>>>()?,
                )),
                Some(Expr::Symbol(operator)) => self
                    .enums
                    .iter()
                    .find(|(_, variants)| variants.iter().any(|variant| variant.name == *operator))
                    .map(|(name, _)| Type::Named(name.clone()))
                    .or_else(|| {
                        self.functions
                            .get(operator)
                            .map(|function| function.return_type.clone())
                    }),
                _ => None,
            },
            _ => None,
        }
    }

    fn return_value(&mut self, value: &Expr) -> Result<(), String> {
        if matches!(self.return_type, Type::Unit) {
            return Ok(());
        }
        if is_float_type(&self.return_type) {
            let ty = self.return_type.clone();
            return self.expression_as_float(value, &ty);
        }
        if is_wide_integer(&self.return_type) {
            return self.expression(value);
        }
        if let Type::Array(_, length) = &self.return_type {
            return self.return_array_value(*length, value);
        }
        if let Type::Tuple(fields) = self.return_type.clone() {
            return self.return_tuple_value(&fields, value);
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
                        "    mov rax, QWORD PTR [rbp-{}]\n",
                        discriminant * 8
                    ));
                    for (index, slot) in payload.iter().enumerate() {
                        if index + 1 >= VALUE_REGISTERS.len() {
                            return Err("native enum return has too many payloads".into());
                        }
                        self.output.push_str(&format!(
                            "    mov {}, QWORD PTR [rbp-{}]\n",
                            VALUE_REGISTERS[index + 1],
                            slot * 8
                        ));
                    }
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
                let register = VALUE_REGISTERS
                    .get(index)
                    .ok_or_else(|| "native struct return has too many fields".to_owned())?;
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
                if fields.len() > VALUE_REGISTERS.len() {
                    return Err("native struct return has too many fields".into());
                }
                for (index, field) in items[1..].iter().enumerate() {
                    self.expression_as_abi_word(field, &fields[index].ty)?;
                    self.push_rax();
                }
                for register in VALUE_REGISTERS[..fields.len()].iter().rev() {
                    self.output.push_str(&format!("    pop {register}\n"));
                    self.stack_depth -= 1;
                }
                return Ok(());
            }
        }
        self.expression(value)
    }

    fn return_tuple_value(&mut self, fields: &[Type], value: &Expr) -> Result<(), String> {
        if let Expr::Symbol(name) = value {
            let Storage::Tuple(slots) = self
                .locals
                .get(name)
                .ok_or_else(|| format!("unknown tuple local '{name}'"))?
            else {
                return Err(format!("'{name}' is not a tuple"));
            };
            for (index, slot) in slots.iter().enumerate() {
                let register = VALUE_REGISTERS
                    .get(index)
                    .ok_or_else(|| "native tuple return has too many fields".to_owned())?;
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [rbp-{}]\n",
                    slot * 8
                ));
            }
            return Ok(());
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == "tuple") {
                if items.len() - 1 != fields.len() {
                    return Err("tuple return has the wrong length".into());
                }
                for (field, ty) in items[1..].iter().zip(fields) {
                    self.expression_as_abi_word(field, ty)?;
                    self.push_rax();
                }
                for register in VALUE_REGISTERS[..fields.len()].iter().rev() {
                    self.output.push_str(&format!("    pop {register}\n"));
                    self.stack_depth -= 1;
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
                let Type::Array(element, _) = self.return_type.clone() else {
                    unreachable!()
                };
                for _ in 0..length {
                    self.expression_as_abi_word(&items[1], &element)?;
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
                let Type::Array(element, _) = self.return_type.clone() else {
                    unreachable!()
                };
                for value in &items[1..] {
                    self.expression_as_abi_word(value, &element)?;
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
        if matches!(ty, Type::Array(_, _) | Type::Tuple(_)) {
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
        for ((_, slot), (field, value)) in slots.iter().zip(fields.iter().zip(&items[1..])) {
            self.store_scalar_at_slot(value, &field.ty, *slot)?;
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
                "    mov QWORD PTR [rbp-{}], rax\n",
                discriminant * 8
            ));
            for (index, slot) in payload.iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {}\n",
                    slot * 8,
                    VALUE_REGISTERS[index + 1]
                ));
            }
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
                "    mov QWORD PTR [rbp-{}], rax\n",
                discriminant * 8
            ));
            for (index, slot) in payload.iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {}\n",
                    slot * 8,
                    VALUE_REGISTERS[index + 1]
                ));
            }
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
        for (index, slot) in payload.iter().enumerate() {
            if let Some(value) = items.get(index + 1) {
                self.store_scalar_at_slot(value, &variant.fields[index], *slot)?;
            } else {
                self.output
                    .push_str(&format!("    mov QWORD PTR [rbp-{}], 0\n", slot * 8));
            }
        }
        Ok(())
    }

    fn store_tuple(&mut self, name: &str, value: &Expr) -> Result<(), String> {
        let Storage::Tuple(slots) = self
            .locals
            .get(name)
            .ok_or_else(|| format!("unknown tuple local '{name}'"))?
        else {
            return Err(format!("'{name}' is not a tuple"));
        };
        let slots = slots.clone();
        let fields = match self.local_types.get(name).cloned() {
            Some(Type::Tuple(fields)) => fields,
            _ => return Err(format!("'{name}' is not a tuple")),
        };
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "tuple") {
                if items.len() - 1 != fields.len() {
                    return Err("tuple constructor has the wrong length".into());
                }
                for ((slot, ty), field) in slots.iter().zip(&fields).zip(&items[1..]) {
                    self.store_scalar_at_slot(field, ty, *slot)?;
                }
                return Ok(());
            }
        }
        self.expression(value)?;
        for (index, slot) in slots.iter().enumerate() {
            self.output.push_str(&format!(
                "    mov QWORD PTR [rbp-{}], {}\n",
                slot * 8,
                VALUE_REGISTERS[index]
            ));
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
            let element_type = match self.local_types.get(name).cloned() {
                Some(Type::Array(element, _)) => *element,
                _ => return Err(format!("'{name}' is not an array")),
            };
            for index in 0..length {
                self.store_scalar_at_slot(&items[1], &element_type, base + index)?;
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
        let element_type = match self.local_types.get(name).cloned() {
            Some(Type::Array(element, _)) => *element,
            _ => return Err(format!("'{name}' is not an array")),
        };
        for (index, value) in items[1..].iter().enumerate() {
            self.store_scalar_at_slot(value, &element_type, base + index)?;
        }
        Ok(())
    }

    fn expression(&mut self, expression: &Expr) -> Result<(), String> {
        match expression {
            Expr::Integer(value) => {
                if *value < i64::MIN as i128 || *value > i64::MAX as i128 {
                    self.output.push_str(&format!(
                        "    mov rax, 0x{:016x}\n    mov rdx, 0x{:016x}\n",
                        *value as u64,
                        if *value < 0 { u64::MAX } else { 0 },
                    ));
                } else {
                    self.output.push_str(&format!("    mov rax, {value}\n"));
                    self.output.push_str(&format!(
                        "    mov rdx, {}\n",
                        if *value < 0 { -1 } else { 0 }
                    ));
                }
            }
            Expr::UnsignedInteger(value) => {
                self.output.push_str(&format!(
                    "    mov rax, 0x{:016x}\n    mov rdx, 0x{:016x}\n",
                    *value as u64,
                    (*value >> 64) as u64
                ));
            }
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
                if let Some(payload_count) = self.enums.values().find_map(|variants| {
                    variants
                        .iter()
                        .find(|variant| variant.name == *name)
                        .map(|_| {
                            variants
                                .iter()
                                .map(|variant| variant.fields.len())
                                .max()
                                .unwrap_or(0)
                        })
                }) {
                    for index in 0..payload_count {
                        self.output.push_str(&format!(
                            "    xor {}, {}\n",
                            VALUE_REGISTERS[index + 1],
                            VALUE_REGISTERS[index + 1]
                        ));
                    }
                }
            }
            Expr::Symbol(name) => {
                if self.locals.contains_key(name) {
                    if let Some(Storage::Wide { low, high }) = self.locals.get(name) {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n    mov rdx, QWORD PTR [rbp-{}]\n",
                            low * 8,
                            high * 8
                        ));
                    } else {
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
                    }
                } else if self.globals.contains_key(name) {
                    match self.global_types.get(name) {
                        Some(Type::I128 | Type::U128) => self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rip+{}]\n    mov rdx, QWORD PTR [rip+{}+8]\n",
                            asm_symbol(name),
                            asm_symbol(name)
                        )),
                        Some(Type::F32) => self.output.push_str(&format!(
                            "    movss xmm0, DWORD PTR [rip+{}]\n",
                            asm_symbol(name)
                        )),
                        Some(Type::F64) => self.output.push_str(&format!(
                            "    movq xmm0, QWORD PTR [rip+{}]\n",
                            asm_symbol(name)
                        )),
                        _ => self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rip+{}]\n",
                            asm_symbol(name)
                        )),
                    }
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
        if items.is_empty() {
            return Ok(());
        }
        let operator = match items.first() {
            Some(Expr::Symbol(name)) => name.as_str(),
            _ => return Err("expression list must start with a symbol".into()),
        };
        if let Some((enum_name, variant_fields)) =
            self.enums.iter().find_map(|(enum_name, variants)| {
                variants
                    .iter()
                    .find(|variant| variant.name == operator)
                    .map(|variant| (enum_name.clone(), variant.fields.clone()))
            })
        {
            if items.len() - 1 != variant_fields.len() {
                return Err(format!(
                    "variant '{operator}' expects {} payloads",
                    variant_fields.len()
                ));
            }
            let variant_index = self
                .enums
                .get(&enum_name)
                .and_then(|variants| {
                    variants
                        .iter()
                        .position(|candidate| candidate.name == operator)
                })
                .expect("validated enum variant");
            for (index, value) in items[1..].iter().enumerate().rev() {
                self.expression(value)?;
                self.output
                    .push_str(&format!("    mov {}, rax\n", VALUE_REGISTERS[index + 1]));
            }
            let payload_count = self
                .enums
                .get(&enum_name)
                .map(|variants| {
                    variants
                        .iter()
                        .map(|variant| variant.fields.len())
                        .max()
                        .unwrap_or(0)
                })
                .unwrap_or(0);
            for index in items.len() - 1..payload_count {
                self.output.push_str(&format!(
                    "    xor {}, {}\n",
                    VALUE_REGISTERS[index + 1],
                    VALUE_REGISTERS[index + 1]
                ));
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
                let target = resolve_type(&parse_type(items.get(2))?, &self.aliases)?;
                self.cast_expression(&items[1], &target)
            }
            "size-of" => self.layout_size_expression("size-of", items),
            "align-of" => self.layout_size_expression("align-of", items),
            "match" => self.match_expression(items, None),
            "index" => self.index_expression(items),
            "get" => self.field_expression(items),
            "!" => self.boolean_not(items),
            "&&" | "||" => self.boolean_logic(operator, items),
            "assert" | "debug-assert" => self.assert_expression(operator, items),
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
        let Some(name) = (match &items[1] {
            Expr::Symbol(name) => Some(name),
            _ => None,
        }) else {
            let Type::Array(element, length) = self
                .expression_type(&items[1])
                .ok_or_else(|| "index requires an array value".to_owned())?
            else {
                return Err("index requires an array value".into());
            };
            if length > VALUE_REGISTERS.len() {
                return Err("native computed indexing supports at most six elements".into());
            }
            let bounds_failure = self.label("bounds_failure");
            self.expression(&items[1])?;
            for register in VALUE_REGISTERS[..length].iter().rev() {
                self.output.push_str(&format!("    push {register}\n"));
                self.stack_depth += 1;
            }
            self.expression(&items[2])?;
            self.output.push_str(&format!(
                "    mov rcx, rax\n    cmp rcx, {length}\n    jae {bounds_failure}\n    mov rax, QWORD PTR [rsp+rcx*8+{}]\n    add rsp, {}\n    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n",
                8,
                length * 8
            ));
            if matches!(*element, Type::F32) {
                self.output.push_str("    movd xmm0, eax\n");
            } else if matches!(*element, Type::F64) {
                self.output.push_str("    movq xmm0, rax\n");
            } else {
                ensure_integer_type(&element).map_err(|_| {
                    "native computed indexing supports scalar arrays only".to_owned()
                })?;
            }
            self.stack_depth -= length;
            return Ok(());
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
        let element_type = match self.local_types.get(name).cloned() {
            Some(Type::Array(element, _)) => *element,
            _ => return Err(format!("'{name}' is not an array")),
        };
        let bounds_failure = self.label("bounds_failure");
        self.expression(&items[2])?;
        self.output.push_str("    mov rcx, rax\n");
        self.output.push_str(&format!(
            "    cmp rcx, {length}\n    jae {bounds_failure}\n"
        ));
        self.output.push_str(&format!(
            "    lea rdx, [rbp-{}]\n    shl rcx, 3\n    sub rdx, rcx\n",
            base * 8
        ));
        if matches!(element_type, Type::F32) {
            self.output.push_str("    movss xmm0, DWORD PTR [rdx]\n");
        } else if matches!(element_type, Type::F64) {
            self.output.push_str("    movq xmm0, QWORD PTR [rdx]\n");
        } else {
            self.output.push_str("    mov rax, QWORD PTR [rdx]\n");
        }
        self.output.push_str(&format!(
            "    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n"
        ));
        Ok(())
    }

    fn match_expression(
        &mut self,
        items: &[Expr],
        float_type: Option<&Type>,
    ) -> Result<(), String> {
        if items.len() < 3 {
            return Err("match requires a value and an arm".into());
        }
        let end = self.label("match_end");
        let base_depth = self.stack_depth;
        let payload_slots = match &items[1] {
            Expr::Symbol(name) => match self.locals.get(name) {
                Some(Storage::Enum { payload, .. }) => Some(payload.clone()),
                _ => None,
            },
            _ => None,
        };
        let payload_count = if let Some(payload_slots) = &payload_slots {
            payload_slots.len()
        } else {
            let ty = self
                .expression_type(&items[1])
                .ok_or_else(|| "match scrutinee has no known type".to_owned())?;
            if self.is_enum_type(&ty) {
                self.enum_payload_count(&ty)?
            } else {
                0
            }
        };
        let staged_words = if payload_slots.is_some() {
            1
        } else {
            payload_count + 1
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
            _ => {
                self.expression(&items[1])?;
                for index in (0..payload_count).rev() {
                    self.output
                        .push_str(&format!("    push {}\n", VALUE_REGISTERS[index + 1]));
                    self.stack_depth += 1;
                }
                self.push_rax();
            }
        }
        if payload_slots.is_some() {
            self.push_rax();
        }
        for arm in &items[2..] {
            let arm = match arm {
                Expr::List(arm) if arm.len() == 2 => arm,
                _ => return Err("invalid match arm".into()),
            };
            let next = self.label("match_next");
            let bindings = match &arm[0] {
                Expr::Symbol(pattern) if pattern == "_" => Vec::new(),
                Expr::Symbol(pattern) if self.enum_value(pattern).is_some() => Vec::new(),
                Expr::List(pattern) if !pattern.is_empty() => {
                    let Expr::Symbol(pattern_name) = &pattern[0] else {
                        return Err("match variant pattern must be a symbol".into());
                    };
                    let bindings = pattern[1..]
                        .iter()
                        .map(|binding| match binding {
                            Expr::Symbol(binding) => Ok(binding.as_str()),
                            _ => Err("match payload pattern must be a symbol".to_owned()),
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if self.enum_value(pattern_name).is_none() {
                        return Err(format!("unknown enum variant '{pattern_name}'"));
                    }
                    bindings
                }
                Expr::Integer(value) => {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {value}\n    jne {next}\n"
                    ));
                    Vec::new()
                }
                Expr::Char(value) => {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                        *value as u32
                    ));
                    Vec::new()
                }
                Expr::Symbol(pattern) if pattern == "false" || pattern == "true" => {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                        if pattern == "true" { 1 } else { 0 }
                    ));
                    Vec::new()
                }
                _ => return Err("invalid scalar match pattern".into()),
            };
            if let Expr::Symbol(pattern) = &arm[0] {
                if pattern != "_" && self.enum_value(pattern).is_some() {
                    let value = self.enum_value(pattern).unwrap();
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {value}\n    jne {next}\n"
                    ));
                }
            } else if let Expr::List(pattern) = &arm[0] {
                let value = self
                    .enum_value(match &pattern[0] {
                        Expr::Symbol(pattern) => pattern,
                        _ => unreachable!(),
                    })
                    .ok_or_else(|| "unknown enum variant".to_owned())?;
                self.output.push_str(&format!(
                    "    cmp QWORD PTR [rsp], {value}\n    jne {next}\n"
                ));
            }
            if !bindings.is_empty() {
                for (index, binding) in bindings.iter().enumerate() {
                    if *binding == "_" {
                        continue;
                    }
                    let slot = scalar_slot(&self.locals, binding);
                    if let Some(payload_slots) = payload_slots.as_ref() {
                        let payload_slot = payload_slots.get(index).ok_or_else(|| {
                            "payload binding exceeds enum payload count".to_owned()
                        })?;
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                            payload_slot * 8,
                            slot * 8
                        ));
                    } else {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rsp+{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                            (index + 1) * 8,
                            slot * 8
                        ));
                    }
                }
            }
            if let Some(ty) = float_type {
                self.expression_as_float(&arm[1], ty)?;
            } else {
                self.expression(&arm[1])?;
            }
            self.output.push_str(&format!(
                "    mov rdx, rax\n    add rsp, {}\n    mov rax, rdx\n",
                staged_words * 8
            ));
            self.stack_depth -= staged_words;
            self.output.push_str(&format!("    jmp {end}\n{next}:\n"));
            self.stack_depth = base_depth + staged_words;
        }
        self.output.push_str(&format!("{end}:\n"));
        self.stack_depth = base_depth;
        Ok(())
    }

    fn enum_payload_count(&self, ty: &Type) -> Result<usize, String> {
        let Type::Named(name) = ty else {
            return Err("match scrutinee is not an enum value".into());
        };
        let variants = self
            .enums
            .get(name)
            .ok_or_else(|| format!("unknown enum '{name}'"))?;
        Ok(variants
            .iter()
            .map(|variant| variant.fields.len())
            .max()
            .unwrap_or(0))
    }

    fn is_enum_type(&self, ty: &Type) -> bool {
        matches!(ty, Type::Named(name) if self.enums.contains_key(name))
    }

    fn unary_negate(&mut self, items: &[Expr]) -> Result<(), String> {
        if self
            .expression_type(&items[1])
            .is_some_and(|ty| is_wide_integer(&ty))
        {
            self.expression(&items[1])?;
            self.output.push_str("    neg rax\n    sbb rdx, 0\n");
            return Ok(());
        }
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
            if let Some(ty) = self.expression_type(&items[1]) {
                if is_narrow_integer(&ty) {
                    self.normalize_integer(&ty)?;
                }
            }
        }
        Ok(())
    }

    fn field_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err("get requires a value and field".into());
        }
        if let Expr::Integer(index) = &items[2] {
            if *index < 0 {
                return Err("tuple field index must be non-negative".into());
            }
            let index =
                usize::try_from(*index).map_err(|_| "tuple field index is too large".to_owned())?;
            let tuple_type = self
                .expression_type(&items[1])
                .ok_or_else(|| "get requires a tuple value".to_owned())?;
            let Type::Tuple(fields) = tuple_type else {
                return Err("integer tuple fields require a tuple value".into());
            };
            let field_type = fields
                .get(index)
                .ok_or_else(|| format!("tuple field index {index} is out of bounds"))?
                .clone();
            if let Expr::List(constructor) = &items[1] {
                if matches!(constructor.first(), Some(Expr::Symbol(name)) if name == "tuple") {
                    let value = constructor
                        .get(index + 1)
                        .ok_or_else(|| "tuple constructor has too few fields".to_owned())?;
                    return self.expression_as_expected(value, &field_type);
                }
            }
            if let Expr::Symbol(local) = &items[1] {
                let Storage::Tuple(slots) = self
                    .locals
                    .get(local)
                    .ok_or_else(|| format!("unknown tuple local '{local}'"))?
                else {
                    return Err(format!("'{local}' is not a tuple"));
                };
                let slot = *slots
                    .get(index)
                    .ok_or_else(|| "native tuple has too many fields".to_owned())?;
                match field_type {
                    Type::F32 => self
                        .output
                        .push_str(&format!("    movss xmm0, DWORD PTR [rbp-{}]\n", slot * 8)),
                    Type::F64 => self
                        .output
                        .push_str(&format!("    movq xmm0, QWORD PTR [rbp-{}]\n", slot * 8)),
                    _ => self
                        .output
                        .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8)),
                }
            } else {
                self.expression(&items[1])?;
                let register = VALUE_REGISTERS
                    .get(index)
                    .ok_or_else(|| "native tuple has too many fields".to_owned())?;
                match field_type {
                    Type::F32 => self
                        .output
                        .push_str(&format!("    movd xmm0, {}\n", low_register(register))),
                    Type::F64 => self
                        .output
                        .push_str(&format!("    movq xmm0, {register}\n")),
                    _ => {
                        self.output.push_str(&format!("    mov rax, {register}\n"));
                    }
                }
            }
            return Ok(());
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
                let struct_name = match self.local_types.get(local) {
                    Some(Type::Named(name)) => name,
                    _ => return Err(format!("'{local}' is not a struct")),
                };
                let field_type = self
                    .structs
                    .get(struct_name)
                    .and_then(|fields| fields.iter().find(|field| field.name == *field_name))
                    .map(|field| field.ty.clone())
                    .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                if matches!(field_type, Type::F32) {
                    self.output
                        .push_str(&format!("    movss xmm0, DWORD PTR [rbp-{}]\n", slot * 8));
                } else if matches!(field_type, Type::F64) {
                    self.output
                        .push_str(&format!("    movq xmm0, QWORD PTR [rbp-{}]\n", slot * 8));
                } else {
                    self.output
                        .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
                }
                Ok(())
            }
            Expr::List(constructor) if matches!(constructor.first(), Some(Expr::Symbol(name)) if self.structs.contains_key(name)) =>
            {
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
                let field_type = fields[index].ty.clone();
                self.expression_as_expected(value, &field_type)
            }
            _ => {
                let Type::Named(struct_name) = self
                    .expression_type(&items[1])
                    .ok_or_else(|| "get requires a struct value".to_owned())?
                else {
                    return Err("get requires a struct value".into());
                };
                let fields = self
                    .structs
                    .get(&struct_name)
                    .ok_or_else(|| format!("unknown struct '{struct_name}'"))?
                    .clone();
                let index = fields
                    .iter()
                    .position(|field| field.name == *field_name)
                    .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                if index >= VALUE_REGISTERS.len() {
                    return Err("native returned struct has too many fields".into());
                }
                self.expression(&items[1])?;
                let register = VALUE_REGISTERS[index];
                let field_type = fields[index].ty.clone();
                match field_type {
                    Type::F32 => self
                        .output
                        .push_str(&format!("    movd xmm0, {}\n", low_register(register))),
                    Type::F64 => self
                        .output
                        .push_str(&format!("    movq xmm0, {register}\n")),
                    _ => {
                        ensure_integer_type(&fields[index].ty).map_err(|_| {
                            "native returned-struct field has unsupported type".to_owned()
                        })?;
                        if index != 0 {
                            self.output.push_str(&format!("    mov rax, {register}\n"));
                        }
                    }
                }
                Ok(())
            }
        }
    }

    fn boolean_not(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 2 {
            return Err("! requires one operand".into());
        }
        self.expression(&items[1])?;
        if self
            .expression_type(&items[1])
            .is_some_and(|ty| matches!(ty, Type::Bool))
        {
            self.output.push_str("    xor eax, 1\n");
        } else {
            self.output.push_str("    not rax\n");
            if let Some(ty) = self.expression_type(&items[1]) {
                if is_narrow_integer(&ty) {
                    self.normalize_integer(&ty)?;
                }
            }
        }
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

    fn assert_expression(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 2 {
            return Err(format!("{operator} requires one boolean condition"));
        }
        let failure = self.label("assert_failure");
        let done = self.label("assert_done");
        self.expression(&items[1])?;
        self.output.push_str(&format!(
            "    test rax, rax\n    jz {failure}\n    jmp {done}\n{failure}:\n    ud2\n{done}:\n    xor eax, eax\n"
        ));
        Ok(())
    }

    fn layout_size_expression(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 2 {
            return Err(format!("{operator} requires one type"));
        }
        let ty = resolve_type(&parse_type(items.get(1))?, &self.aliases)?;
        let value = if operator == "size-of" {
            self.native_type_size(&ty)?
        } else {
            self.native_type_align(&ty)?
        };
        self.output.push_str(&format!("    mov rax, {value}\n"));
        Ok(())
    }

    fn native_type_align(&self, ty: &Type) -> Result<usize, String> {
        match ty {
            Type::I128 | Type::U128 => Ok(8),
            Type::Array(element, _) => self.native_type_align(element),
            Type::Tuple(fields) => fields
                .iter()
                .map(|field| self.native_type_align(field))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(1)
                .try_into()
                .map_err(|_| "alignment is too large".to_owned()),
            Type::Named(name) => {
                if let Some(fields) = self.structs.get(name) {
                    return fields
                        .iter()
                        .map(|field| self.native_type_align(&field.ty))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .max()
                        .unwrap_or(1)
                        .try_into()
                        .map_err(|_| "alignment is too large".to_owned());
                }
                if self.enums.contains_key(name) {
                    return Ok(8);
                }
                Err(format!("unknown type '{name}' in align-of"))
            }
            Type::Generic(name) => Err(format!("generic type '{name}' has no concrete alignment")),
            _ => Ok(8),
        }
    }

    fn native_type_size(&self, ty: &Type) -> Result<usize, String> {
        match ty {
            Type::I128 | Type::U128 => Ok(16),
            Type::Array(element, length) => Ok(self.native_type_size(element)? * length),
            Type::Tuple(fields) => fields
                .iter()
                .map(|field| self.native_type_size(field))
                .sum(),
            Type::Named(name) => {
                if let Some(fields) = self.structs.get(name) {
                    return fields
                        .iter()
                        .map(|field| self.native_type_size(&field.ty))
                        .sum();
                }
                if let Some(variants) = self.enums.get(name) {
                    let payload = variants
                        .iter()
                        .map(|variant| {
                            variant
                                .fields
                                .iter()
                                .map(|field| self.native_type_size(field))
                                .sum::<Result<usize, String>>()
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .max()
                        .unwrap_or(0);
                    return Ok(8 + payload);
                }
                Err(format!("unknown type '{name}' in size-of"))
            }
            Type::Generic(name) => Err(format!("generic type '{name}' has no concrete size")),
            _ => Ok(8),
        }
    }

    fn binary_operator(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("operator '{operator}' requires two operands"));
        }
        if self.expression_is_float(&items[1]) {
            return self.float_binary_operator(operator, items);
        }
        if self
            .expression_type(&items[1])
            .is_some_and(|ty| is_wide_integer(&ty))
        {
            return self.wide_binary_operator(operator, items);
        }
        self.expression(&items[1])?;
        self.push_rax();
        self.expression(&items[2])?;
        self.output.push_str("    mov rcx, rax\n    pop rax\n");
        self.stack_depth -= 1;
        let shift_failure = if matches!(operator, "<<" | ">>") {
            let width = self
                .expression_type(&items[1])
                .and_then(integer_bit_width)
                .ok_or_else(|| "shift requires an integer operand".to_owned())?;
            let label = self.label("shift_failure");
            self.output
                .push_str(&format!("    cmp rcx, {width}\n    jae {label}\n"));
            Some(label)
        } else {
            None
        };
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
        if let Some(ty) = self.expression_type(&items[1]) {
            if is_narrow_integer(&ty) {
                self.normalize_integer(&ty)?;
            }
        }
        if let Some(label) = shift_failure {
            let done = self.label("shift_done");
            self.output
                .push_str(&format!("    jmp {done}\n{label}:\n    ud2\n{done}:\n"));
        }
        Ok(())
    }

    fn wide_binary_operator(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if !matches!(
            operator,
            "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>"
        ) {
            return Err(format!("128-bit operator '{operator}' is unsupported"));
        }
        self.expression(&items[1])?;
        self.output.push_str("    push rdx\n    push rax\n");
        self.stack_depth += 2;
        self.expression(&items[2])?;
        self.output
            .push_str("    mov rcx, rax\n    mov r8, rdx\n    pop rax\n    pop rdx\n");
        self.stack_depth -= 2;
        if matches!(operator, "<<" | ">>") {
            let failure = self.label("wide_shift_failure");
            let high = self.label("wide_shift_high");
            let done = self.label("wide_shift_done");
            self.output.push_str(&format!(
                "    cmp rcx, 128\n    jae {failure}\n    cmp rcx, 64\n    jae {high}\n"
            ));
            if operator == "<<" {
                self.output
                    .push_str("    shld rdx, rax, cl\n    shl rax, cl\n");
            } else if self
                .expression_type(&items[1])
                .is_some_and(|ty| matches!(ty, Type::U128))
            {
                self.output
                    .push_str("    shrd rax, rdx, cl\n    shr rdx, cl\n");
            } else {
                self.output
                    .push_str("    shrd rax, rdx, cl\n    sar rdx, cl\n");
            }
            self.output
                .push_str(&format!("    jmp {done}\n{high}:\n    sub rcx, 64\n"));
            if operator == "<<" {
                self.output
                    .push_str("    mov rdx, rax\n    shl rdx, cl\n    xor eax, eax\n");
            } else {
                self.output.push_str("    mov rax, rdx\n");
                if self
                    .expression_type(&items[1])
                    .is_some_and(|ty| matches!(ty, Type::U128))
                {
                    self.output.push_str("    shr rax, cl\n    xor edx, edx\n");
                } else {
                    self.output.push_str("    sar rax, cl\n    sar rdx, 63\n");
                }
            }
            self.output
                .push_str(&format!("    jmp {done}\n{failure}:\n    ud2\n{done}:\n"));
            return Ok(());
        }
        if operator == "*" {
            self.output.push_str(
                "    sub rsp, 16\n    mov QWORD PTR [rsp], rax\n    mov QWORD PTR [rsp+8], rdx\n    mul rcx\n    mov r9, rax\n    mov r10, rdx\n    mov rax, QWORD PTR [rsp+8]\n    mul rcx\n    add r10, rax\n    mov rax, QWORD PTR [rsp]\n    mul r8\n    add r10, rax\n    mov rax, r9\n    mov rdx, r10\n    add rsp, 16\n",
            );
            return Ok(());
        }
        if matches!(operator, "/" | "%") {
            let unsigned = self
                .expression_type(&items[1])
                .is_some_and(|ty| matches!(ty, Type::U128));
            self.wide_division(operator, !unsigned)?;
            return Ok(());
        }
        match operator {
            "+" => self.output.push_str("    add rax, rcx\n    adc rdx, r8\n"),
            "-" => self.output.push_str("    sub rax, rcx\n    sbb rdx, r8\n"),
            "&" => self.output.push_str("    and rax, rcx\n    and rdx, r8\n"),
            "|" => self.output.push_str("    or rax, rcx\n    or rdx, r8\n"),
            "^" => self.output.push_str("    xor rax, rcx\n    xor rdx, r8\n"),
            _ => unreachable!(),
        }
        Ok(())
    }

    fn wide_division(&mut self, operator: &str, signed: bool) -> Result<(), String> {
        let loop_label = self.label("wide_div_loop");
        let subtract_label = self.label("wide_div_subtract");
        let next_label = self.label("wide_div_next");
        let done_label = self.label("wide_div_done");
        let zero_label = self.label("wide_div_zero");
        if signed {
            self.output.push_str(
                "    sub rsp, 16\n    mov r9, rdx\n    sar r9, 63\n    mov QWORD PTR [rsp], r9\n    mov r10, r8\n    sar r10, 63\n    xor r9, r10\n    mov QWORD PTR [rsp+8], r9\n    mov r9, QWORD PTR [rsp]\n    xor rax, r9\n    xor rdx, r9\n    sub rax, r9\n    sbb rdx, r9\n    mov r10, r8\n    sar r10, 63\n    xor rcx, r10\n    xor r8, r10\n    sub rcx, r10\n    sbb r8, r10\n",
            );
            self.stack_depth += 2;
        }
        self.output.push_str("    push r12\n");
        self.stack_depth += 1;
        self.output.push_str(&format!(
            "    mov r9, r8\n    or r9, rcx\n    jz {zero_label}\n    xor r9d, r9d\n    xor r10d, r10d\n    xor r11d, r11d\n    xor edi, edi\n    mov r12, 128\n{loop_label}:\n    shl rax, 1\n    rcl rdx, 1\n    rcl rdi, 1\n    rcl r11, 1\n    shl r9, 1\n    rcl r10, 1\n    cmp r11, r8\n    ja {subtract_label}\n    jb {next_label}\n    cmp rdi, rcx\n    jae {subtract_label}\n    jmp {next_label}\n{subtract_label}:\n    sub rdi, rcx\n    sbb r11, r8\n    or r9, 1\n{next_label}:\n    dec r12\n    jnz {loop_label}\n"
        ));
        if operator == "/" {
            self.output.push_str("    mov rax, r9\n    mov rdx, r10\n");
        } else {
            self.output.push_str("    mov rax, rdi\n    mov rdx, r11\n");
        }
        self.output.push_str("    pop r12\n");
        self.stack_depth -= 1;
        if signed {
            if operator == "/" {
                self.output.push_str(
                    "    mov r9, QWORD PTR [rsp+8]\n    xor rax, r9\n    xor rdx, r9\n    sub rax, r9\n    sbb rdx, r9\n",
                );
            } else {
                self.output.push_str(
                    "    mov r9, QWORD PTR [rsp]\n    xor rdi, r9\n    xor r11, r9\n    sub rdi, r9\n    sbb r11, r9\n    mov rax, rdi\n    mov rdx, r11\n",
                );
            }
            self.output.push_str("    add rsp, 16\n");
            self.stack_depth -= 2;
        }
        self.output.push_str(&format!(
            "    jmp {done_label}\n{zero_label}:\n    ud2\n{done_label}:\n"
        ));
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
        if operator == "%" {
            return self.float_remainder(&ty);
        }
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

    fn float_remainder(&mut self, ty: &Type) -> Result<(), String> {
        let loop_label = self.label("float_remainder");
        let (store, load, memory) = if matches!(ty, Type::F32) {
            ("movss", "movss", "DWORD")
        } else {
            ("movq", "movq", "QWORD")
        };
        self.output.push_str(&format!(
            "    sub rsp, 16\n    {store} {memory} PTR [rsp], xmm1\n    {store} {memory} PTR [rsp+8], xmm0\n    fld {memory} PTR [rsp]\n    fld {memory} PTR [rsp+8]\n{loop_label}:\n    fprem\n    fstsw ax\n    test ah, 4\n    jnz {loop_label}\n    fstp st(0)\n    fstp {memory} PTR [rsp]\n    {load} xmm0, {memory} PTR [rsp]\n    add rsp, 16\n"
        ));
        Ok(())
    }
    fn comparison(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("comparison '{operator}' requires two operands"));
        }
        if self.expression_is_float(&items[1]) {
            return self.float_comparison(operator, items);
        }
        if self
            .expression_type(&items[1])
            .is_some_and(|ty| is_wide_integer(&ty))
        {
            return self.wide_comparison(operator, items);
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

    fn wide_comparison(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        self.expression(&items[1])?;
        self.output.push_str("    push rdx\n    push rax\n");
        self.stack_depth += 2;
        self.expression(&items[2])?;
        self.output
            .push_str("    mov rcx, rax\n    mov r8, rdx\n    pop rax\n    pop rdx\n");
        self.stack_depth -= 2;
        let unsigned = self
            .expression_type(&items[1])
            .is_some_and(|ty| matches!(ty, Type::U128));
        let true_label = self.label("wide_cmp_true");
        let false_label = self.label("wide_cmp_false");
        let end_label = self.label("wide_cmp_end");
        if matches!(operator, "==" | "!=") {
            self.output.push_str("    cmp rdx, r8\n");
            self.output.push_str(&format!(
                "    jne {}\n    cmp rax, rcx\n    {} {}\n",
                if operator == "==" {
                    false_label.as_str()
                } else {
                    true_label.as_str()
                },
                if operator == "==" { "jne" } else { "jne" },
                if operator == "==" {
                    false_label.as_str()
                } else {
                    true_label.as_str()
                }
            ));
            self.output.push_str(&format!(
                "    jmp {}\n",
                if operator == "==" {
                    true_label.as_str()
                } else {
                    false_label.as_str()
                }
            ));
        } else {
            let (high_true, high_false, low_condition) = match (operator, unsigned) {
                ("<", true) => ("b", "a", "b"),
                ("<=", true) => ("b", "a", "be"),
                (">", true) => ("a", "b", "a"),
                (">=", true) => ("a", "b", "ae"),
                ("<", false) => ("l", "g", "b"),
                ("<=", false) => ("l", "g", "be"),
                (">", false) => ("g", "l", "a"),
                (">=", false) => ("g", "l", "ae"),
                _ => unreachable!(),
            };
            self.output.push_str(&format!(
                "    cmp rdx, r8\n    j{high_true} {true_label}\n    j{high_false} {false_label}\n    cmp rax, rcx\n    j{low_condition} {true_label}\n    jmp {false_label}\n"
            ));
        }
        self.output.push_str(&format!(
            "{true_label}:\n    mov eax, 1\n    jmp {end_label}\n{false_label}:\n    xor eax, eax\n{end_label}:\n"
        ));
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
        let unordered = self.label("float_unordered");
        let done = self.label("float_cmp_done");
        let condition = match operator {
            "<" => "b",
            "<=" => "be",
            ">" => "a",
            ">=" => "ae",
            "==" => "e",
            "!=" => "ne",
            _ => unreachable!(),
        };
        self.output.push_str(&format!(
            "    jp {unordered}\n    set{condition} al\n    movzx rax, al\n    jmp {done}\n{unordered}:\n    mov eax, {}\n{done}:\n",
            if operator == "!=" { 1 } else { 0 }
        ));
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
                Some(Expr::Symbol(operator)) if operator == "if" && items.len() == 4 => self
                    .expression_float_type(&items[2])
                    .or_else(|| self.expression_float_type(&items[3])),
                Some(Expr::Symbol(operator)) if operator == "match" => items[2..]
                    .iter()
                    .filter_map(|arm| match arm {
                        Expr::List(arm) if arm.len() == 2 => self.expression_float_type(&arm[1]),
                        _ => None,
                    })
                    .next(),
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
        if let Expr::List(items) = expression {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                return self.if_expression_as_float(items, ty);
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                return self.match_expression(items, Some(ty));
            }
        }
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
        if items.len() != 3 && items.len() != 4 {
            return Err(
                "if requires a condition, then expression, and optional else expression".into(),
            );
        }
        let else_label = self.label("else");
        let end_label = self.label("endif");
        self.expression(&items[1])?;
        self.output
            .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
        self.expression(&items[2])?;
        self.output.push_str(&format!("    jmp {end_label}\n"));
        if items.len() == 4 {
            self.output.push_str(&format!("{else_label}:\n"));
            self.expression(&items[3])?;
        } else {
            self.output
                .push_str(&format!("{else_label}:\n    xor eax, eax\n"));
        }
        self.output.push_str(&format!("{end_label}:\n"));
        Ok(())
    }

    fn if_expression_as_float(&mut self, items: &[Expr], ty: &Type) -> Result<(), String> {
        if items.len() != 4 {
            return Err("if requires a condition, then expression, and else expression".into());
        }
        let else_label = self.label("else");
        let end_label = self.label("endif");
        self.expression(&items[1])?;
        self.output
            .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
        self.expression_as_float(&items[2], ty)?;
        self.output
            .push_str(&format!("    jmp {end_label}\n{else_label}:\n"));
        self.expression_as_float(&items[3], ty)?;
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
            self.output
                .push_str(&format!("    call {}\n", asm_symbol(name)));
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
        self.output
            .push_str(&format!("    call {}\n", asm_symbol(name)));
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
        self.output
            .push_str(&format!("    call {}\n", asm_symbol(name)));
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
        let integer_words = parameters
            .iter()
            .filter(|ty| !is_float_type(ty))
            .map(|ty| value_word_count(ty, &self.structs, &self.enums))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .sum::<usize>();
        if integer_words > ARGUMENT_REGISTERS.len() {
            return Err("native mixed calls support at most six integer ABI words".into());
        }
        let float_words = parameters.iter().filter(|ty| is_float_type(ty)).count();
        if float_words > FLOAT_ARGUMENT_REGISTERS.len() {
            return Err("native mixed calls support at most eight floating ABI words".into());
        }
        let mut stack_words = 0usize;
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
                self.stack_depth += 1;
                stack_words += 1;
            } else {
                let words = value_word_count(ty, &self.structs, &self.enums)?;
                self.push_value_words(argument, ty, false)?;
                stack_words += words;
            }
        }
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        let mut consumed_words = 0usize;
        for ty in parameters {
            let words = if is_float_type(ty) {
                1
            } else {
                value_word_count(ty, &self.structs, &self.enums)?
            };
            for word in 0..words {
                let offset = (stack_words - consumed_words - word - 1) * 8;
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
            consumed_words += words;
        }
        self.output
            .push_str(&format!("    add rsp, {}\n", stack_words * 8));
        self.stack_depth -= stack_words;
        let needs_padding = self.stack_depth % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
        }
        self.output
            .push_str(&format!("    call {}\n", asm_symbol(name)));
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
        }
        Ok(())
    }

    fn push_value_words(&mut self, value: &Expr, ty: &Type, reverse: bool) -> Result<(), String> {
        if is_wide_integer(ty) {
            self.expression(value)?;
            let registers = if reverse {
                ["rdx", "rax"]
            } else {
                ["rax", "rdx"]
            };
            for register in registers {
                self.output.push_str(&format!("    push {register}\n"));
                self.stack_depth += 1;
            }
            return Ok(());
        }
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
                    let Type::Array(element, _) = ty else {
                        unreachable!()
                    };
                    for _ in 0..*length {
                        self.expression_as_abi_word(&items[1], element)?;
                        self.push_rax();
                    }
                    return Ok(());
                }
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
                    if items.len() - 1 != *length {
                        return Err("array argument has the wrong length".into());
                    }
                    let values: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new((0..*length).rev())
                    } else {
                        Box::new(0..*length)
                    };
                    let Type::Array(element, _) = ty else {
                        unreachable!()
                    };
                    for index in values {
                        self.expression_as_abi_word(&items[index + 1], element)?;
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
        if let Type::Tuple(fields) = ty {
            let slots = if let Expr::Symbol(local) = value {
                let Storage::Tuple(slots) = self
                    .locals
                    .get(local)
                    .ok_or_else(|| format!("unknown tuple local '{local}'"))?
                else {
                    return Err(format!("'{local}' is not a tuple"));
                };
                slots.clone()
            } else {
                Vec::new()
            };
            if !slots.is_empty() {
                let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                    Box::new((0..slots.len()).rev())
                } else {
                    Box::new(0..slots.len())
                };
                for index in indices {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n",
                        slots[index] * 8
                    ));
                    self.push_rax();
                }
                return Ok(());
            }
            if let Expr::List(items) = value {
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "tuple") {
                    if items.len() - 1 != fields.len() {
                        return Err("tuple argument has the wrong length".into());
                    }
                    let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new((0..fields.len()).rev())
                    } else {
                        Box::new(0..fields.len())
                    };
                    for index in indices {
                        self.expression_as_abi_word(&items[index + 1], &fields[index])?;
                        self.push_rax();
                    }
                    return Ok(());
                }
            }
            self.expression(value)?;
            let registers: Box<dyn Iterator<Item = &str>> = if reverse {
                Box::new(VALUE_REGISTERS[..fields.len()].iter().rev().copied())
            } else {
                Box::new(VALUE_REGISTERS[..fields.len()].iter().copied())
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
                        let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                            Box::new((0..fields.len()).rev())
                        } else {
                            Box::new(0..fields.len())
                        };
                        for index in indices {
                            self.expression_as_abi_word(&items[index + 1], &fields[index].ty)?;
                            self.push_rax();
                        }
                        return Ok(());
                    }
                }
                self.expression(value)?;
                for register in VALUE_REGISTERS[..fields.len()].iter() {
                    self.output.push_str(&format!("    push {register}\n"));
                    self.stack_depth += 1;
                }
                return Ok(());
            }
            if self
                .enums
                .get(name)
                .is_some_and(|variants| variants.iter().any(|variant| !variant.fields.is_empty()))
            {
                if let Expr::Symbol(local) = value {
                    if !self.locals.contains_key(local) {
                        self.expression(value)?;
                        let words = value_word_count(ty, &self.structs, &self.enums)?;
                        let registers: Box<dyn Iterator<Item = &str>> = if reverse {
                            Box::new(VALUE_REGISTERS[..words].iter().rev().copied())
                        } else {
                            Box::new(VALUE_REGISTERS[..words].iter().copied())
                        };
                        for register in registers {
                            self.output.push_str(&format!("    push {register}\n"));
                            self.stack_depth += 1;
                        }
                        return Ok(());
                    }
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
                    let mut slots = Vec::with_capacity(1 + payload.len());
                    slots.push(*discriminant);
                    slots.extend(payload.iter().copied());
                    if reverse {
                        slots.reverse();
                    }
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
            let words = value_word_count(ty, &self.structs, &self.enums)?;
            let registers: Box<dyn Iterator<Item = &str>> = if reverse {
                Box::new(VALUE_REGISTERS[..words].iter().rev().copied())
            } else {
                Box::new(VALUE_REGISTERS[..words].iter().copied())
            };
            for register in registers {
                self.output.push_str(&format!("    push {register}\n"));
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
        let label = format!(
            ".L{prefix}_{}_{}",
            asm_symbol(&self.function_name),
            self.labels
        );
        self.labels += 1;
        label
    }
}
