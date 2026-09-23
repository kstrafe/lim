//! Small native x86-64 backend for the currently supported integer subset.
//!
//! The backend emits GNU assembler syntax in Intel mode and follows the Linux
//! System V ABI. It intentionally rejects types and expressions that do not
//! have a representation in this first backend instead of silently generating
//! incorrect code.

#![allow(clippy::too_many_arguments)]

use std::collections::{HashMap, HashSet};

use crate::typecheck::function_call_depths;
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
    if is_asm_reserved_symbol(&symbol) {
        symbol.insert_str(0, "_lim_");
    }
    symbol
}

fn is_asm_reserved_symbol(symbol: &str) -> bool {
    [
        "offset", "ptr", "byte", "word", "dword", "qword", "tbyte", "oword", "rip", "rsp", "rbp",
        "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14",
        "r15", "eax", "ebx", "ecx", "edx", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
        "r13d", "r14d", "r15d", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7",
    ]
    .iter()
    .any(|reserved| symbol.eq_ignore_ascii_case(reserved))
}

fn asm_u64_immediate(value: u64) -> String {
    if value <= i64::MAX as u64 {
        value.to_string()
    } else {
        format!("0x{value:016x}")
    }
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

fn operator_base(operator: &str) -> &str {
    let (_, base, _) = operator_parts(operator);
    base
}

fn operator_parts(operator: &str) -> (Option<&str>, &str, Option<&str>) {
    let Some((qualifier, operation)) = operator.split_once('.') else {
        return (None, operator, None);
    };
    if !is_builtin_operator_type(qualifier)
        || !matches!(
            operation.split('.').next(),
            Some(
                "+" | "-"
                    | "*"
                    | "/"
                    | "%"
                    | "&"
                    | "|"
                    | "^"
                    | "<<"
                    | ">>"
                    | "<"
                    | "<="
                    | ">"
                    | ">="
                    | "=="
                    | "!="
                    | "!"
                    | "&&"
                    | "||"
            )
        )
    {
        return (None, operator, None);
    }
    let Some((operation, mode)) = operation.split_once('.') else {
        return (Some(qualifier), operation, None);
    };
    (Some(qualifier), operation, Some(mode))
}

fn is_builtin_operator_type(name: &str) -> bool {
    matches!(
        name,
        "bool"
            | "char"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
    )
}

#[derive(Clone)]
enum GlobalValue {
    Zero,
    Integer(i128),
    Wide { low: u64, high: u64 },
    F32(u32),
    F64(u64),
    Aggregate(Vec<u64>),
}

#[derive(Clone)]
struct FunctionAbi {
    parameters: Vec<Type>,
    indirect_parameters: Vec<bool>,
    return_type: Type,
    indirect_return: bool,
    max_call_depth: usize,
}

enum ScalarRange {
    Signed(i128, i128),
    Unsigned(u128, u128),
    Char(u64, u64),
}

fn scalar_range_bounds(pattern: &Expr, ty: &Type) -> Result<ScalarRange, String> {
    let Expr::List(parts) = pattern else {
        return Err("range pattern must be a list".into());
    };
    if parts.len() != 3 || !matches!(parts.first(), Some(Expr::Symbol(name)) if name == "range") {
        return Err("range pattern must have the form (#range lower upper)".into());
    }
    if matches!(
        ty,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::Isize
    ) {
        let lower_expression = range_bound_expression(&parts[1], ty)?;
        let upper_expression = range_bound_expression(&parts[2], ty)?;
        let lower = signed_range_bound(lower_expression)?;
        let upper = signed_range_bound(upper_expression)?;
        if lower > upper {
            return Err("integer range pattern lower bound exceeds upper bound".into());
        }
        return Ok(ScalarRange::Signed(lower, upper));
    }
    if matches!(
        ty,
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 | Type::Usize
    ) {
        let lower_expression = range_bound_expression(&parts[1], ty)?;
        let upper_expression = range_bound_expression(&parts[2], ty)?;
        let lower = unsigned_range_bound(lower_expression)?;
        let upper = unsigned_range_bound(upper_expression)?;
        if lower > upper {
            return Err("unsigned range pattern lower bound exceeds upper bound".into());
        }
        return Ok(ScalarRange::Unsigned(lower, upper));
    }
    if matches!(ty, Type::Char) {
        let Expr::Char(lower) = parts[1] else {
            return Err("character range patterns require character bounds".into());
        };
        let Expr::Char(upper) = parts[2] else {
            return Err("character range patterns require character bounds".into());
        };
        if lower > upper {
            return Err("character range pattern lower bound exceeds upper bound".into());
        }
        return Ok(ScalarRange::Char(lower as u64, upper as u64));
    }
    Err("range patterns require an integer or char scrutinee".into())
}

fn range_bound_expression<'a>(expression: &'a Expr, scrutinee: &Type) -> Result<&'a Expr, String> {
    let Expr::List(items) = expression else {
        return Ok(expression);
    };
    if items.len() != 3 || !matches!(items.first(), Some(Expr::Symbol(name)) if name == "literal") {
        return Ok(expression);
    }
    let literal_type = parse_type(items.get(1))?;
    if &literal_type != scrutinee {
        return Err(format!(
            "typed range bound has type {literal_type:?}, expected {scrutinee:?}"
        ));
    }
    Ok(&items[2])
}

fn signed_range_bound(expression: &Expr) -> Result<i128, String> {
    match expression {
        Expr::Integer(value) => Ok(*value),
        Expr::UnsignedInteger(value) => i128::try_from(*value)
            .map_err(|_| "signed range bound is outside the signed scalar width".to_owned()),
        _ => Err("integer range patterns require integer bounds".into()),
    }
}

fn unsigned_range_bound(expression: &Expr) -> Result<u128, String> {
    match expression {
        Expr::Integer(value) if *value >= 0 => Ok(*value as u128),
        Expr::Integer(_) => Err("unsigned range bounds cannot be negative".into()),
        Expr::UnsignedInteger(value) => Ok(*value),
        _ => Err("integer range patterns require integer bounds".into()),
    }
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
        Type::Never => "never".into(),
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
        Type::Reference { mutable, target } => format!(
            "ref{}{}",
            if *mutable { "mut_" } else { "_" },
            specialized_type_name(target)
        ),
        Type::RawPointer { mutable, target } => format!(
            "ptr{}{}",
            if *mutable { "mut_" } else { "_" },
            specialized_type_name(target)
        ),
        Type::Cell(target) => format!("cell_{}", specialized_type_name(target)),
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
        Expr::Loop(statements) => Expr::Loop(
            statements
                .iter()
                .map(|statement| substitute_statement(statement, substitutions))
                .collect(),
        ),
        Expr::Labeled { label, expression } => Expr::Labeled {
            label: label.clone(),
            expression: Box::new(substitute_expr(expression, substitutions)),
        },
        Expr::Quote(value) => Expr::Quote(Box::new(substitute_expr(value, substitutions))),
        Expr::QuasiQuote(value) => {
            Expr::QuasiQuote(Box::new(substitute_expr(value, substitutions)))
        }
        Expr::Unquote(value) => Expr::Unquote(Box::new(substitute_expr(value, substitutions))),
        Expr::UnquoteSplicing(value) => {
            Expr::UnquoteSplicing(Box::new(substitute_expr(value, substitutions)))
        }
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
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable,
        } => Statement::Destructure {
            pattern: pattern.clone(),
            ty: substitute_type(ty, substitutions),
            value: substitute_expr(value, substitutions),
            mutable: *mutable,
        },
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => Statement::LetElse {
            pattern: pattern.clone(),
            ty: substitute_type(ty, substitutions),
            value: substitute_expr(value, substitutions),
            else_body: else_body
                .iter()
                .map(|statement| substitute_statement(statement, substitutions))
                .collect(),
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
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => Statement::EnumPayloadAssign {
            name: name.clone(),
            variant: variant.clone(),
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
        Statement::Labeled { label, statement } => Statement::Labeled {
            label: label.clone(),
            statement: Box::new(substitute_statement(statement, substitutions)),
        },
        Statement::Return(value) => Statement::Return(
            value
                .as_ref()
                .map(|value| substitute_expr(value, substitutions)),
        ),
        Statement::Expr(value) => Statement::Expr(substitute_expr(value, substitutions)),
        Statement::BreakValue(value) => {
            Statement::BreakValue(substitute_expr(value, substitutions))
        }
        Statement::BreakToValue { label, value } => Statement::BreakToValue {
            label: label.clone(),
            value: substitute_expr(value, substitutions),
        },
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => statement.clone(),
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
        Expr::Loop(statements) => Expr::Loop(
            statements
                .iter()
                .map(|statement| rewrite_statement(statement, specializations))
                .collect(),
        ),
        Expr::Labeled { label, expression } => Expr::Labeled {
            label: label.clone(),
            expression: Box::new(rewrite_expr(expression, specializations)),
        },
        Expr::Quote(value) => Expr::Quote(Box::new(rewrite_expr(value, specializations))),
        Expr::QuasiQuote(value) => Expr::QuasiQuote(Box::new(rewrite_expr(value, specializations))),
        Expr::Unquote(value) => Expr::Unquote(Box::new(rewrite_expr(value, specializations))),
        Expr::UnquoteSplicing(value) => {
            Expr::UnquoteSplicing(Box::new(rewrite_expr(value, specializations)))
        }
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
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable,
        } => Statement::Destructure {
            pattern: pattern.clone(),
            ty: ty.clone(),
            value: rewrite_expr(value, specializations),
            mutable: *mutable,
        },
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => Statement::LetElse {
            pattern: pattern.clone(),
            ty: ty.clone(),
            value: rewrite_expr(value, specializations),
            else_body: else_body
                .iter()
                .map(|statement| rewrite_statement(statement, specializations))
                .collect(),
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
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => Statement::EnumPayloadAssign {
            name: name.clone(),
            variant: variant.clone(),
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
        Statement::Labeled { label, statement } => Statement::Labeled {
            label: label.clone(),
            statement: Box::new(rewrite_statement(statement, specializations)),
        },
        Statement::Return(value) => Statement::Return(
            value
                .as_ref()
                .map(|value| rewrite_expr(value, specializations)),
        ),
        Statement::Expr(value) => Statement::Expr(rewrite_expr(value, specializations)),
        Statement::BreakValue(value) => Statement::BreakValue(rewrite_expr(value, specializations)),
        Statement::BreakToValue { label, value } => Statement::BreakToValue {
            label: label.clone(),
            value: rewrite_expr(value, specializations),
        },
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => statement.clone(),
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
        Expr::Loop(statements) => {
            for statement in statements {
                collect_generic_calls_statement(statement, calls);
            }
        }
        Expr::Labeled { expression, .. } => collect_generic_calls_expr(expression, calls),
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => collect_generic_calls_expr(value, calls),
        _ => {}
    }
}

fn collect_generic_calls_statement(statement: &Statement, calls: &mut Vec<String>) {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => collect_generic_calls_expr(value, calls),
        Statement::ArrayAssign { index, value, .. } => {
            collect_generic_calls_expr(index, calls);
            collect_generic_calls_expr(value, calls);
        }
        Statement::LetElse {
            value, else_body, ..
        } => {
            collect_generic_calls_expr(value, calls);
            for statement in else_body {
                collect_generic_calls_statement(statement, calls);
            }
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
        Statement::Labeled { statement, .. } => {
            collect_generic_calls_statement(statement, calls);
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
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

fn erase_unsafe_blocks(program: &Program) -> Program {
    fn expr(value: &Expr) -> Expr {
        if let Expr::List(items) = value {
            if items.len() == 2
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "unsafe")
            {
                return expr(&items[1]);
            }
            return Expr::List(items.iter().map(expr).collect());
        }
        match value {
            Expr::Block(body) => Expr::Block(body.iter().map(statement).collect()),
            Expr::Loop(body) => Expr::Loop(body.iter().map(statement).collect()),
            Expr::Labeled {
                label,
                expression: inner,
            } => Expr::Labeled {
                label: label.clone(),
                expression: Box::new(expr(inner)),
            },
            Expr::Quote(inner) => Expr::Quote(Box::new(expr(inner))),
            Expr::QuasiQuote(inner) => Expr::QuasiQuote(Box::new(expr(inner))),
            Expr::Unquote(inner) => Expr::Unquote(Box::new(expr(inner))),
            Expr::UnquoteSplicing(inner) => Expr::UnquoteSplicing(Box::new(expr(inner))),
            _ => value.clone(),
        }
    }
    fn statement(value: &Statement) -> Statement {
        match value {
            Statement::Let {
                name,
                ty,
                value,
                mutable,
            } => Statement::Let {
                name: name.clone(),
                ty: ty.clone(),
                value: expr(value),
                mutable: *mutable,
            },
            Statement::Destructure {
                pattern,
                ty,
                value,
                mutable,
            } => Statement::Destructure {
                pattern: expr(pattern),
                ty: ty.clone(),
                value: expr(value),
                mutable: *mutable,
            },
            Statement::LetElse {
                pattern,
                ty,
                value,
                else_body,
            } => Statement::LetElse {
                pattern: expr(pattern),
                ty: ty.clone(),
                value: expr(value),
                else_body: else_body.iter().map(statement).collect(),
            },
            Statement::Assign { name, value } => Statement::Assign {
                name: name.clone(),
                value: expr(value),
            },
            Statement::ArrayAssign { name, index, value } => Statement::ArrayAssign {
                name: name.clone(),
                index: expr(index),
                value: expr(value),
            },
            Statement::FieldAssign { name, field, value } => Statement::FieldAssign {
                name: name.clone(),
                field: field.clone(),
                value: expr(value),
            },
            Statement::TupleAssign { name, index, value } => Statement::TupleAssign {
                name: name.clone(),
                index: *index,
                value: expr(value),
            },
            Statement::EnumPayloadAssign {
                name,
                variant,
                index,
                value,
            } => Statement::EnumPayloadAssign {
                name: name.clone(),
                variant: variant.clone(),
                index: *index,
                value: expr(value),
            },
            Statement::While { condition, body } => Statement::While {
                condition: expr(condition),
                body: body.iter().map(statement).collect(),
            },
            Statement::Loop { body } => Statement::Loop {
                body: body.iter().map(statement).collect(),
            },
            Statement::For {
                init,
                condition,
                step,
                body,
            } => Statement::For {
                init: Box::new(statement(init)),
                condition: expr(condition),
                step: Box::new(statement(step)),
                body: body.iter().map(statement).collect(),
            },
            Statement::Labeled {
                label,
                statement: inner,
            } => Statement::Labeled {
                label: label.clone(),
                statement: Box::new(statement(inner)),
            },
            Statement::BreakValue(value) => Statement::BreakValue(expr(value)),
            Statement::BreakToValue { label, value } => Statement::BreakToValue {
                label: label.clone(),
                value: expr(value),
            },
            Statement::Return(value) => Statement::Return(value.as_ref().map(expr)),
            Statement::Expr(value) => Statement::Expr(expr(value)),
            other => other.clone(),
        }
    }
    let mut result = program.clone();
    for item in &mut result.items {
        match item {
            Item::Function(function) if !function.external => {
                function.body = function.body.iter().map(statement).collect();
            }
            Item::Let { value, .. } | Item::Static { value, .. } => *value = expr(value),
            _ => {}
        }
    }
    result
}

pub fn generate_assembly(program: &Program) -> Result<String, String> {
    let target = crate::TargetDescription::host()?;
    generate_assembly_for_target(program, target)
}

pub fn generate_assembly_for_target(
    program: &Program,
    target: crate::TargetDescription,
) -> Result<String, String> {
    if target != crate::TargetDescription::X86_64_SYSTEM_V {
        return Err("native backend has no implementation for the selected target".into());
    }
    check_types(program)?;
    let program = erase_unsafe_blocks(program);
    let aliases: HashMap<String, Type> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. } => Some((name.clone(), target.clone())),
            _ => None,
        })
        .collect();
    let program = monomorphize_program(&program, &aliases)?;
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
            Item::ThreadTask { name, .. } => Some((
                name.clone(),
                vec![Field {
                    name: "__lim_thread_context".into(),
                    ty: Type::RawPointer {
                        mutable: true,
                        target: Box::new(Type::Unit),
                    },
                }],
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
                        discriminant: variant.discriminant,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            enums.insert(name.clone(), variants);
        }
    }
    let mut functions = HashMap::new();
    let call_depths = function_call_depths(&program);
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let parameters = function
            .parameters
            .iter()
            .map(|parameter| resolve_type(&parameter.ty, &aliases))
            .collect::<Result<Vec<_>, _>>()?;
        let indirect_parameters: Vec<bool> = parameters
            .iter()
            .map(|ty| supports_indirect_return_type(ty, &structs, &enums))
            .collect();
        let return_type = resolve_type(&function.return_type, &aliases)?;
        let indirect_return = supports_indirect_return_type(&return_type, &structs, &enums);
        if function.external
            && (parameters
                .iter()
                .any(|parameter| !is_external_scalar_type(parameter, &enums))
                || (!matches!(return_type, Type::Unit)
                    && !is_external_scalar_type(&return_type, &enums)))
        {
            return Err(format!(
                "external function '{}' must use directly passed scalar values",
                function.name
            ));
        }
        for parameter in &parameters {
            if !supports_indirect_return_type(parameter, &structs, &enums) {
                ensure_parameter_type(parameter, &enums, &structs)?;
            }
        }
        ensure_return_type(&return_type, &enums, &structs)?;
        functions.insert(
            function.name.clone(),
            FunctionAbi {
                parameters,
                indirect_parameters,
                indirect_return,
                return_type,
                max_call_depth: *call_depths.get(&function.name).unwrap_or(&1),
            },
        );
    }
    for item in &program.items {
        let Item::ThreadTask { name, worker } = item else {
            continue;
        };
        let worker_abi = functions
            .get(worker)
            .cloned()
            .ok_or_else(|| format!("thread worker '{worker}' has no native signature"))?;
        let task_type = Type::Named(name.clone());
        let spawn_name = format!("{name}-spawn");
        let join_name = format!("{name}-join");
        for (function_name, abi) in [
            (
                spawn_name.clone(),
                FunctionAbi {
                    parameters: worker_abi.parameters.clone(),
                    indirect_parameters: worker_abi.indirect_parameters.clone(),
                    return_type: task_type.clone(),
                    indirect_return: false,
                    max_call_depth: 1,
                },
            ),
            (
                join_name.clone(),
                FunctionAbi {
                    parameters: vec![task_type],
                    indirect_parameters: vec![false],
                    indirect_return: worker_abi.indirect_return,
                    return_type: worker_abi.return_type.clone(),
                    max_call_depth: 1,
                },
            ),
        ] {
            if functions.insert(function_name.clone(), abi).is_some() {
                return Err(format!(
                    "generated thread function '{function_name}' conflicts with another function"
                ));
            }
        }
    }
    let mut globals = HashMap::new();
    let mut global_types = HashMap::new();
    let mut constants = HashMap::new();
    let mut float_constants = HashMap::new();
    let constant_initializers = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Let { name, value, .. } => Some((name.clone(), value.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let mut evaluating_constants = HashSet::new();
    let mut evaluating_float_constants = HashSet::new();
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
            let global = match &ty {
                Type::Unit => {
                    if !matches!(value, Expr::List(items) if items.is_empty()) {
                        return Err(format!("unit global '{name}' must be initialized with ()"));
                    }
                    GlobalValue::Zero
                }
                Type::Never => {
                    return Err(format!("global '{name}' cannot have the never type"));
                }
                Type::I128 | Type::U128 => {
                    let value = match value {
                        Expr::UnsignedInteger(value) => *value,
                        _ => constant_value(
                            value,
                            &enums,
                            &constants,
                            &constant_initializers,
                            &mut evaluating_constants,
                            Some(&ty),
                        )? as u128,
                    };
                    if matches!(item, Item::Let { .. }) {
                        constants.insert(name.clone(), value as i128);
                    }
                    GlobalValue::Wide {
                        low: value as u64,
                        high: (value >> 64) as u64,
                    }
                }
                Type::F32 => {
                    let value = constant_float_value(
                        value,
                        &constants,
                        &float_constants,
                        &constant_initializers,
                        &mut evaluating_float_constants,
                        true,
                    )? as f32;
                    if matches!(item, Item::Let { .. }) {
                        float_constants.insert(name.clone(), value as f64);
                    }
                    GlobalValue::F32(value.to_bits())
                }
                Type::F64 => {
                    let value = constant_float_value(
                        value,
                        &constants,
                        &float_constants,
                        &constant_initializers,
                        &mut evaluating_float_constants,
                        false,
                    )?;
                    if matches!(item, Item::Let { .. }) {
                        float_constants.insert(name.clone(), value);
                    }
                    GlobalValue::F64(value.to_bits())
                }
                _ if ensure_scalar_type(&ty, &enums).is_ok() => {
                    let normalized = normalize_global_integer(
                        constant_value(
                            value,
                            &enums,
                            &constants,
                            &constant_initializers,
                            &mut evaluating_constants,
                            Some(&ty),
                        )?,
                        &ty,
                    );
                    if matches!(item, Item::Let { .. }) {
                        constants.insert(name.clone(), normalized);
                    }
                    GlobalValue::Integer(normalized)
                }
                _ => GlobalValue::Aggregate(constant_aggregate_words(
                    value,
                    &ty,
                    &structs,
                    &enums,
                    &constants,
                    &float_constants,
                    &constant_initializers,
                    &mut evaluating_constants,
                    &mut evaluating_float_constants,
                )?),
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
                GlobalValue::Zero => {}
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
                GlobalValue::Aggregate(words) => {
                    output.push_str(&format!(".align 8\n{symbol}:\n"));
                    for word in words {
                        output.push_str(&format!("    .quad {word}\n"));
                    }
                }
            }
        }
    }
    output.push_str(".text\n");
    if program
        .items
        .iter()
        .any(|item| matches!(item, Item::ThreadTask { .. }))
    {
        output.push_str(".extern malloc\n.extern free\n.extern pthread_create\n.extern pthread_join\n.extern abort\n");
    }
    for item in &program.items {
        if let Item::Function(function) = item {
            if function.external {
                output.push_str(&format!(".extern {}\n", asm_symbol(&function.name)));
            }
        }
    }
    for item in &program.items {
        match item {
            Item::Function(function) if !function.external => generate_function(
                function,
                &mut output,
                &structs,
                &enums,
                &globals,
                &global_types,
                &aliases,
                &functions,
            )?,
            Item::Function(_) => {}
            Item::Struct { .. } => {}
            Item::Enum { .. } => {}
            Item::TypeAlias { .. } => {}
            Item::Let { .. } | Item::Static { .. } => {}
            Item::UnsafeAutoTraitImpl { .. } => {}
            Item::ThreadTask { name, worker } => generate_thread_task(
                name,
                worker,
                &mut output,
                &structs,
                &enums,
                &aliases,
                &functions,
            )?,
        }
    }
    output.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    Ok(output)
}

fn emit_indirect_parameter_copy(output: &mut String, slots: &[usize], source: &str) {
    output.push_str(&format!("    mov r10, {source}\n"));
    for (index, slot) in slots.iter().enumerate() {
        output.push_str(&format!(
            "    mov rax, QWORD PTR [r10-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
            index * 8,
            slot * 8
        ));
    }
}

fn generate_thread_task(
    name: &str,
    worker: &str,
    output: &mut String,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    functions: &HashMap<String, FunctionAbi>,
) -> Result<(), String> {
    let worker_abi = functions
        .get(worker)
        .ok_or_else(|| format!("thread worker '{worker}' has no native signature"))?;
    let result_type = &worker_abi.return_type;
    if matches!(result_type, Type::Never) {
        return Err(format!(
            "thread worker '{worker}' cannot return the never type"
        ));
    }

    let mut packet_offsets = Vec::with_capacity(worker_abi.parameters.len());
    let mut packet_offset = 8usize;
    for ty in &worker_abi.parameters {
        let words = storage_word_count(ty, structs, enums)?;
        if words == 0 {
            packet_offsets.push(None);
        } else {
            packet_offsets.push(Some(packet_offset));
            packet_offset += words * 8;
        }
    }
    let result_offset = packet_offset;
    let result_words = storage_word_count(result_type, structs, enums)?;
    let allocation_size = packet_offset + result_words * 8;
    let task_symbol = asm_symbol(name);
    let worker_symbol = asm_symbol(worker);
    let spawn_symbol = asm_symbol(&format!("{name}-spawn"));
    let join_symbol = asm_symbol(&format!("{name}-join"));
    let entry_symbol = format!(".Llim_thread_entry_{task_symbol}");

    let mut incoming = Vec::<Vec<(&'static str, String, usize)>>::new();
    let mut spill_words = 0usize;
    let mut integer_index = 0usize;
    let mut float_index = 0usize;
    let mut stack_index = 0usize;
    for (ty, indirect) in worker_abi
        .parameters
        .iter()
        .zip(&worker_abi.indirect_parameters)
    {
        let input_words = if *indirect || is_float_type(ty) {
            1
        } else {
            value_word_count(ty, structs, enums)?
        };
        let mut parameter_inputs = Vec::with_capacity(input_words);
        for _ in 0..input_words {
            let source = if !*indirect && is_float_type(ty) {
                let source = if float_index < FLOAT_ARGUMENT_REGISTERS.len() {
                    (
                        "float-register",
                        FLOAT_ARGUMENT_REGISTERS[float_index].to_owned(),
                    )
                } else {
                    let source = ("stack", (16 + stack_index * 8).to_string());
                    stack_index += 1;
                    source
                };
                float_index += 1;
                source
            } else {
                let source = if integer_index < ARGUMENT_REGISTERS.len() {
                    (
                        "integer-register",
                        ARGUMENT_REGISTERS[integer_index].to_owned(),
                    )
                } else {
                    let source = ("stack", (16 + stack_index * 8).to_string());
                    stack_index += 1;
                    source
                };
                integer_index += 1;
                source
            };
            parameter_inputs.push((source.0, source.1, spill_words + 1));
            spill_words += 1;
        }
        incoming.push(parameter_inputs);
    }
    let context_slot = spill_words + 1;
    let frame_size = (context_slot * 8).div_ceil(16) * 16;

    output.push_str(&format!(
        ".globl {spawn_symbol}\n.type {spawn_symbol}, @function\n{spawn_symbol}:\n    push rbp\n    mov rbp, rsp\n    sub rsp, {frame_size}\n"
    ));
    for parameter in &incoming {
        for (kind, source, spill_slot) in parameter {
            match *kind {
                "integer-register" => output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {source}\n",
                    spill_slot * 8
                )),
                "float-register" => output.push_str(&format!(
                    "    movq QWORD PTR [rbp-{}], {source}\n",
                    spill_slot * 8
                )),
                "stack" => output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp+{source}]\n    mov QWORD PTR [rbp-{}], rax\n",
                    spill_slot * 8
                )),
                _ => unreachable!(),
            }
        }
    }
    output.push_str(&format!(
        "    mov edi, {allocation_size}\n    call malloc\n    test rax, rax\n    je .Llim_thread_alloc_fail_{task_symbol}\n    mov QWORD PTR [rbp-{}], rax\n",
        context_slot * 8
    ));
    for (index, offset) in packet_offsets.iter().enumerate() {
        let Some(offset) = offset else {
            continue;
        };
        let ty = &worker_abi.parameters[index];
        let storage_words = storage_word_count(ty, structs, enums)?;
        if worker_abi.indirect_parameters[index] {
            let pointer_slot = incoming[index]
                .first()
                .map(|(_, _, slot)| *slot)
                .ok_or_else(|| "indirect thread argument has no input pointer".to_owned())?;
            for word in 0..storage_words {
                let source_offset = if word == 0 {
                    String::new()
                } else {
                    format!("-{}", word * 8)
                };
                output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp-{}]\n    mov rcx, QWORD PTR [rax{source_offset}]\n    mov rdx, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rdx+{}], rcx\n",
                    pointer_slot * 8,
                    context_slot * 8,
                    offset + (storage_words - 1 - word) * 8
                ));
            }
        } else {
            if incoming[index].len() != storage_words {
                return Err(format!(
                    "thread argument '{ty:?}' has incompatible native storage and value layouts"
                ));
            }
            for (word, (_, _, spill_slot)) in incoming[index].iter().enumerate() {
                output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp-{}]\n    mov rcx, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rax+{}], rcx\n",
                    context_slot * 8,
                    spill_slot * 8,
                    offset + word * 8
                ));
            }
        }
    }
    output.push_str(&format!(
        "    mov rax, QWORD PTR [rbp-{}]\n    mov rdi, rax\n    xor esi, esi\n    lea rdx, [rip+{entry_symbol}]\n    mov rcx, rax\n    call pthread_create\n    test eax, eax\n    jne .Llim_thread_create_fail_{task_symbol}\n    mov rax, QWORD PTR [rbp-{}]\n    leave\n    ret\n.Llim_thread_alloc_fail_{task_symbol}:\n    call abort\n    ud2\n.Llim_thread_create_fail_{task_symbol}:\n    mov rdi, QWORD PTR [rbp-{}]\n    call free\n    call abort\n    ud2\n.size {spawn_symbol}, .-{spawn_symbol}\n",
        context_slot * 8,
        context_slot * 8,
        context_slot * 8
    ));

    output.push_str(&format!(
        ".type {entry_symbol}, @function\n{entry_symbol}:\n    push rbp\n    mov rbp, rsp\n    sub rsp, 16\n    mov QWORD PTR [rbp-8], rdi\n"
    ));
    let mut outgoing = Vec::<(usize, bool, Option<Type>, Option<String>)>::new();
    integer_index = 0;
    float_index = 0;
    for (index, (ty, indirect)) in worker_abi
        .parameters
        .iter()
        .zip(&worker_abi.indirect_parameters)
        .enumerate()
    {
        let Some(offset) = packet_offsets[index] else {
            continue;
        };
        if *indirect {
            let register = if integer_index < ARGUMENT_REGISTERS.len() {
                Some(ARGUMENT_REGISTERS[integer_index].to_owned())
            } else {
                outgoing.push((
                    offset + (storage_word_count(ty, structs, enums)? - 1) * 8,
                    true,
                    None,
                    None,
                ));
                None
            };
            if let Some(register) = register {
                outgoing.push((
                    offset + (storage_word_count(ty, structs, enums)? - 1) * 8,
                    true,
                    None,
                    Some(register),
                ));
            }
            integer_index += 1;
        } else if is_float_type(ty) {
            if float_index < FLOAT_ARGUMENT_REGISTERS.len() {
                outgoing.push((
                    offset,
                    false,
                    Some(ty.clone()),
                    Some(FLOAT_ARGUMENT_REGISTERS[float_index].to_owned()),
                ));
            } else {
                outgoing.push((offset, false, Some(ty.clone()), None));
            }
            float_index += 1;
        } else {
            let words = value_word_count(ty, structs, enums)?;
            for word in 0..words {
                let register = if integer_index < ARGUMENT_REGISTERS.len() {
                    Some(ARGUMENT_REGISTERS[integer_index].to_owned())
                } else {
                    None
                };
                outgoing.push((offset + word * 8, false, None, register));
                integer_index += 1;
            }
        }
    }
    let overflow_words = outgoing
        .iter()
        .filter(|(_, _, _, register)| register.is_none())
        .count();
    let padding = overflow_words % 2;
    if padding != 0 {
        output.push_str("    sub rsp, 8\n");
    }
    for (offset, pointer, _, register) in outgoing.iter().rev() {
        if register.is_none() {
            if *pointer {
                output.push_str(&format!(
                    "    mov r10, QWORD PTR [rbp-8]\n    lea rax, [r10+{offset}]\n    push rax\n"
                ));
            } else {
                output.push_str(&format!(
                    "    mov r10, QWORD PTR [rbp-8]\n    mov rax, QWORD PTR [r10+{offset}]\n    push rax\n"
                ));
            }
        }
    }
    for (offset, pointer, float_ty, register) in &outgoing {
        let Some(register) = register else { continue };
        if let Some(ty) = float_ty {
            output.push_str(&format!(
                "    mov r10, QWORD PTR [rbp-8]\n    {} {register}, {} PTR [r10+{offset}]\n",
                if matches!(ty, Type::F32) {
                    "movd"
                } else {
                    "movq"
                },
                if matches!(ty, Type::F32) {
                    "DWORD"
                } else {
                    "QWORD"
                }
            ));
        } else if *pointer {
            output.push_str(&format!(
                "    mov r10, QWORD PTR [rbp-8]\n    lea {register}, [r10+{offset}]\n"
            ));
        } else {
            output.push_str(&format!(
                "    mov r10, QWORD PTR [rbp-8]\n    mov {register}, QWORD PTR [r10+{offset}]\n"
            ));
        }
    }
    if worker_abi.indirect_return {
        output.push_str(&format!(
            "    mov r10, QWORD PTR [rbp-8]\n    lea r10, [r10+{}]\n",
            result_offset + (result_words.saturating_sub(1)) * 8
        ));
    }
    output.push_str(&format!("    call {worker_symbol}\n"));
    if overflow_words + padding != 0 {
        output.push_str(&format!(
            "    add rsp, {}\n",
            (overflow_words + padding) * 8
        ));
    }
    if worker_abi.indirect_return {
        // The worker wrote its result directly into the reserved packet region.
    } else if matches!(result_type, Type::F32) {
        output.push_str(&format!(
            "    mov r10, QWORD PTR [rbp-8]\n    movd DWORD PTR [r10+{result_offset}], xmm0\n"
        ));
    } else if matches!(result_type, Type::F64) {
        output.push_str(&format!(
            "    mov r10, QWORD PTR [rbp-8]\n    movq QWORD PTR [r10+{result_offset}], xmm0\n"
        ));
    } else if result_words != 0 {
        let words = value_word_count(result_type, structs, enums)?;
        if words != result_words {
            return Err(format!(
                "thread result '{result_type:?}' has incompatible native layouts"
            ));
        }
        for (word, register) in VALUE_REGISTERS.iter().take(words).enumerate() {
            output.push_str(&format!(
                "    mov r10, QWORD PTR [rbp-8]\n    mov QWORD PTR [r10+{}], {register}\n",
                result_offset + word * 8
            ));
        }
    }
    output.push_str("    xor eax, eax\n    leave\n    ret\n");

    let join_frame_words = 2 + if worker_abi.indirect_return {
        0
    } else {
        result_words
    };
    let join_frame_size = (join_frame_words * 8).div_ceil(16) * 16;
    output.push_str(&format!(
        ".globl {join_symbol}\n.type {join_symbol}, @function\n{join_symbol}:\n    push rbp\n    mov rbp, rsp\n    sub rsp, {join_frame_size}\n    mov QWORD PTR [rbp-8], rdi\n"
    ));
    if worker_abi.indirect_return {
        output.push_str("    mov QWORD PTR [rbp-16], r10\n");
    }
    output.push_str(&format!(
        "    mov rdi, QWORD PTR [rdi]\n    xor esi, esi\n    call pthread_join\n    test eax, eax\n    jne .Llim_thread_join_fail_{task_symbol}\n"
    ));
    if worker_abi.indirect_return {
        for word in 0..result_words {
            let destination_offset = if word == 0 {
                String::new()
            } else {
                format!("-{}", word * 8)
            };
            output.push_str(&format!(
                "    mov r10, QWORD PTR [rbp-8]\n    mov r11, QWORD PTR [rbp-16]\n    mov rax, QWORD PTR [r10+{}]\n    mov QWORD PTR [r11{destination_offset}], rax\n",
                result_offset + (result_words - 1 - word) * 8,
            ));
        }
    } else if result_words > 0 && is_float_type(result_type) {
        let instruction = if matches!(result_type, Type::F32) {
            "movd"
        } else {
            "movq"
        };
        let size = if matches!(result_type, Type::F32) {
            "DWORD"
        } else {
            "QWORD"
        };
        output.push_str(&format!(
            "    mov r10, QWORD PTR [rbp-8]\n    {instruction} xmm0, {size} PTR [r10+{result_offset}]\n    {instruction} {size} PTR [rbp-24], xmm0\n"
        ));
    } else if !worker_abi.indirect_return {
        for word in 0..result_words {
            output.push_str(&format!(
                "    mov r10, QWORD PTR [rbp-8]\n    mov rax, QWORD PTR [r10+{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                result_offset + word * 8,
                (word + 3) * 8
            ));
        }
    }
    output.push_str("    mov rdi, QWORD PTR [rbp-8]\n    call free\n");
    if worker_abi.indirect_return {
        output.push_str("    mov rax, QWORD PTR [rbp-16]\n");
    } else if is_float_type(result_type) && result_words > 0 {
        let instruction = if matches!(result_type, Type::F32) {
            "movd"
        } else {
            "movq"
        };
        let size = if matches!(result_type, Type::F32) {
            "DWORD"
        } else {
            "QWORD"
        };
        output.push_str(&format!("    {instruction} xmm0, {size} PTR [rbp-24]\n"));
    } else {
        for (word, register) in VALUE_REGISTERS.iter().take(result_words).enumerate() {
            output.push_str(&format!(
                "    mov {register}, QWORD PTR [rbp-{}]\n",
                (word + 3) * 8
            ));
        }
    }
    output.push_str(&format!(
        "    leave\n    ret\n.Llim_thread_join_fail_{task_symbol}:\n    call abort\n    ud2\n.size {join_symbol}, .-{join_symbol}\n"
    ));

    let _ = aliases;
    Ok(())
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
    let indirect_parameters = functions
        .get(&function.name)
        .map(|abi| abi.indirect_parameters.clone())
        .unwrap_or_else(|| vec![false; function.parameters.len()]);
    for (parameter, indirect) in function.parameters.iter().zip(&indirect_parameters) {
        let parameter_type = resolve_type(&parameter.ty, aliases)?;
        if !indirect {
            ensure_parameter_type(&parameter_type, enums, structs)?;
        }
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
    for (name, abi) in functions {
        local_types
            .entry(name.clone())
            .or_insert_with(|| abi.return_type.clone());
    }
    for (name, ty) in global_types {
        local_types
            .entry(name.clone())
            .or_insert_with(|| ty.clone());
    }
    for statement in &function.body {
        collect_local_types(statement, &mut local_types, aliases, enums, structs);
    }
    for statement in &function.body {
        collect_locals(
            statement,
            &mut locals,
            structs,
            enums,
            aliases,
            &mut next_slot,
            &local_types,
        )?;
    }
    let indirect_return = functions
        .get(&function.name)
        .is_some_and(|abi| abi.indirect_return);
    let return_pointer_slot = if indirect_return {
        let slot = next_slot;
        next_slot += 1;
        Some(slot)
    } else {
        None
    };
    let aggregate_temp_words = functions
        .values()
        .flat_map(|abi| {
            let returns = abi
                .indirect_return
                .then(|| storage_word_count(&abi.return_type, structs, enums));
            let parameters = abi
                .parameters
                .iter()
                .zip(&abi.indirect_parameters)
                .filter(|(_, indirect)| **indirect)
                .map(|(ty, _)| storage_word_count(ty, structs, enums));
            returns.into_iter().chain(parameters)
        })
        .filter_map(Result::ok)
        .max()
        .unwrap_or(0)
        .max(
            local_types
                .values()
                .map(|ty| storage_word_count(ty, structs, enums))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(0),
        )
        .max(
            function
                .body
                .iter()
                .map(|statement| {
                    max_let_else_storage_in_statement(statement, structs, enums, aliases)
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(0),
        );
    let argument_temp_regions = functions
        .values()
        .map(|abi| {
            abi.indirect_parameters
                .iter()
                .filter(|indirect| **indirect)
                .count()
        })
        .max()
        .unwrap_or(1)
        .max(1);
    let projection_regions = function
        .body
        .iter()
        .map(max_projection_depth_in_statement)
        .max()
        .unwrap_or(0)
        + 1;
    let aggregate_temp_regions = argument_temp_regions + projection_regions;
    let aggregate_temp_base = if aggregate_temp_words == 0 {
        None
    } else {
        let base = next_slot;
        next_slot += aggregate_temp_words * aggregate_temp_regions;
        Some(base)
    };
    let frame_size = (next_slot.saturating_sub(1) * 8).div_ceil(16) * 16;
    let function_symbol = asm_symbol(&function.name);
    let max_call_depth = functions
        .get(&function.name)
        .map(|abi| abi.max_call_depth)
        .unwrap_or(1);

    output.push_str(&format!(
        ".globl {}\n.type {}, @function\n{}:\n    # lim frame size: {} bytes\n    # lim max call depth: {}\n",
        function_symbol, function_symbol, function_symbol, frame_size, max_call_depth
    ));
    output.push_str("    push rbp\n    mov rbp, rsp\n");
    if frame_size != 0 {
        output.push_str(&format!("    sub rsp, {frame_size}\n"));
    }
    if let Some(slot) = return_pointer_slot {
        output.push_str(&format!("    mov QWORD PTR [rbp-{}], r10\n", slot * 8));
    }
    let all_float_parameters = has_float_parameter && !has_integer_parameter;
    let mixed_parameters = has_float_parameter && has_integer_parameter;
    if all_float_parameters {
        let mut float_index = 0usize;
        let mut stack_index = 0usize;
        for parameter in &function.parameters {
            let ty = resolve_type(&parameter.ty, aliases)?;
            let slot = local_slots(&locals, &parameter.name)?[0];
            if float_index < FLOAT_ARGUMENT_REGISTERS.len() {
                output.push_str(&format!(
                    "    {} {} PTR [rbp-{}], {}\n",
                    if matches!(ty, Type::F32) {
                        "movd"
                    } else {
                        "movq"
                    },
                    if matches!(ty, Type::F32) {
                        "DWORD"
                    } else {
                        "QWORD"
                    },
                    slot * 8,
                    FLOAT_ARGUMENT_REGISTERS[float_index]
                ));
                float_index += 1;
            } else {
                let incoming_offset = 16 + stack_index * 8;
                output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp+{incoming_offset}]\n    mov QWORD PTR [rbp-{}], rax\n",
                    slot * 8
                ));
                stack_index += 1;
            }
        }
    }
    if mixed_parameters {
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        let mut stack_index = 0usize;
        for (parameter, indirect) in function.parameters.iter().zip(&indirect_parameters) {
            let ty = resolve_type(&parameter.ty, aliases)?;
            if matches!(ty, Type::F32 | Type::F64) {
                let slot = local_slots(&locals, &parameter.name)?[0];
                if float_index < FLOAT_ARGUMENT_REGISTERS.len() {
                    output.push_str(&format!(
                        "    {} {} PTR [rbp-{}], {}\n",
                        if matches!(ty, Type::F32) {
                            "movd"
                        } else {
                            "movq"
                        },
                        if matches!(ty, Type::F32) {
                            "DWORD"
                        } else {
                            "QWORD"
                        },
                        slot * 8,
                        FLOAT_ARGUMENT_REGISTERS[float_index]
                    ));
                    float_index += 1;
                } else {
                    let incoming_offset = 16 + stack_index * 8;
                    output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp+{incoming_offset}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        slot * 8
                    ));
                    stack_index += 1;
                }
            } else if *indirect {
                let slots = local_slots(&locals, &parameter.name)?;
                if integer_index < ARGUMENT_REGISTERS.len() {
                    emit_indirect_parameter_copy(output, &slots, ARGUMENT_REGISTERS[integer_index]);
                    integer_index += 1;
                } else {
                    let incoming_offset = 16 + stack_index * 8;
                    output.push_str(&format!("    mov r10, QWORD PTR [rbp+{incoming_offset}]\n"));
                    emit_indirect_parameter_copy(output, &slots, "r10");
                    stack_index += 1;
                }
            } else {
                let words = value_word_count(&ty, structs, enums)?;
                for slot in local_slots(&locals, &parameter.name)?
                    .into_iter()
                    .take(words)
                {
                    if integer_index < ARGUMENT_REGISTERS.len() {
                        output.push_str(&format!(
                            "    mov QWORD PTR [rbp-{}], {}\n",
                            slot * 8,
                            ARGUMENT_REGISTERS[integer_index]
                        ));
                        integer_index += 1;
                    } else {
                        let incoming_offset = 16 + stack_index * 8;
                        output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp+{incoming_offset}]\n    mov QWORD PTR [rbp-{}], rax\n",
                            slot * 8
                        ));
                        stack_index += 1;
                    }
                }
            }
        }
    }
    let mut incoming_word = 0usize;
    for (parameter, indirect) in function.parameters.iter().zip(&indirect_parameters) {
        if mixed_parameters {
            continue;
        }
        let ty = resolve_type(&parameter.ty, aliases)?;
        if *indirect {
            let slots = local_slots(&locals, &parameter.name)?;
            if incoming_word < ARGUMENT_REGISTERS.len() {
                emit_indirect_parameter_copy(output, &slots, ARGUMENT_REGISTERS[incoming_word]);
            } else {
                let incoming_offset = 16 + (incoming_word - ARGUMENT_REGISTERS.len()) * 8;
                output.push_str(&format!("    mov r10, QWORD PTR [rbp+{incoming_offset}]\n"));
                emit_indirect_parameter_copy(output, &slots, "r10");
            }
            incoming_word += 1;
            continue;
        }
        let words = value_word_count(&ty, structs, enums)?;
        let slots = local_slots(&locals, &parameter.name)?;
        if all_float_parameters {
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
        loop_names: Vec::new(),
        pending_loop_label: None,
        loop_result_types: Vec::new(),
        loop_indirect_results: Vec::new(),
        return_label: return_label.clone(),
        return_pointer_slot,
        aggregate_temp_base,
        aggregate_temp_words,
        aggregate_argument_regions: argument_temp_regions,
        aggregate_argument_cursor: 0,
        aggregate_projection_depth: 0,
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
    structs: &HashMap<String, Vec<Field>>,
) {
    match statement {
        Statement::Let {
            name, ty, value, ..
        } => {
            if let Ok(ty) = resolve_type(ty, aliases) {
                types.insert(name.clone(), ty);
            }
            collect_expr_types(value, types, aliases, enums, structs);
        }
        Statement::Destructure { value, .. } => {
            if let Statement::Destructure { pattern, ty, .. } = statement {
                if let Ok(ty) = resolve_type(ty, aliases) {
                    if let Ok(bindings) = destructure_bindings(pattern, &ty, structs) {
                        for (name, field_type) in bindings {
                            types.entry(name).or_insert(field_type);
                        }
                    }
                }
            }
            collect_expr_types(value, types, aliases, enums, structs);
        }
        Statement::While { condition, body } => {
            collect_expr_types(condition, types, aliases, enums, structs);
            for statement in body {
                collect_local_types(statement, types, aliases, enums, structs);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_local_types(statement, types, aliases, enums, structs);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_local_types(init, types, aliases, enums, structs);
            collect_expr_types(condition, types, aliases, enums, structs);
            collect_local_types(step, types, aliases, enums, structs);
            for statement in body {
                collect_local_types(statement, types, aliases, enums, structs);
            }
        }
        Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::Return(Some(value))
        | Statement::Expr(value) => collect_expr_types(value, types, aliases, enums, structs),
        Statement::ArrayAssign { index, value, .. } => {
            collect_expr_types(index, types, aliases, enums, structs);
            collect_expr_types(value, types, aliases, enums, structs);
        }
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => {
            if let Ok(ty) = resolve_type(ty, aliases) {
                if let Ok(bindings) = let_else_bindings(pattern, &ty, structs, enums) {
                    for (name, field_type) in bindings {
                        types.entry(name).or_insert(field_type);
                    }
                }
            }
            collect_expr_types(value, types, aliases, enums, structs);
            for statement in else_body {
                collect_local_types(statement, types, aliases, enums, structs);
            }
        }
        Statement::Labeled { statement, .. } => {
            collect_local_types(statement, types, aliases, enums, structs);
        }
        Statement::BreakToValue { value, .. } => {
            collect_expr_types(value, types, aliases, enums, structs);
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
}

fn collect_expr_types(
    expression: &Expr,
    types: &mut HashMap<String, Type>,
    aliases: &HashMap<String, Type>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    structs: &HashMap<String, Vec<Field>>,
) {
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                if let Some(scrutinee_type) = items.get(1).and_then(|scrutinee| {
                    collected_expression_type(scrutinee, types, aliases, structs)
                }) {
                    if matches!(&scrutinee_type, Type::Tuple(_) | Type::Array(_, _))
                        || matches!(&scrutinee_type, Type::Named(name) if structs.contains_key(name))
                    {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(pattern) = arm.first() else { continue };
                            collect_match_pattern_types(pattern, &scrutinee_type, types, structs);
                        }
                    }
                }
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    if let Some(Type::Tuple(fields)) = types.get(name).cloned() {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(Expr::List(pattern)) = arm.first() else {
                                continue;
                            };
                            if !matches!(
                                pattern.first(),
                                Some(Expr::Symbol(operator)) if operator == "tuple"
                            ) {
                                continue;
                            }
                            for (binding, field_type) in pattern[1..].iter().zip(fields.iter()) {
                                if let Expr::Symbol(binding) = binding {
                                    if binding != "_" {
                                        types.entry(binding.clone()).or_insert(field_type.clone());
                                    }
                                }
                            }
                        }
                    }
                    if let Some(Type::Array(element, length)) = types.get(name).cloned() {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(Expr::List(pattern)) = arm.first() else {
                                continue;
                            };
                            if !matches!(
                                pattern.first(),
                                Some(Expr::Symbol(operator)) if operator == "array"
                            ) {
                                continue;
                            }
                            for binding in pattern[1..].iter().take(length) {
                                if let Expr::Symbol(binding) = binding {
                                    if binding != "_" {
                                        types.entry(binding.clone()).or_insert((*element).clone());
                                    }
                                }
                            }
                        }
                    }
                    if let Some(Type::Named(struct_name)) = types.get(name).cloned() {
                        if let Some(fields) = structs.get(&struct_name) {
                            for arm in items.iter().skip(2) {
                                let Expr::List(arm) = arm else { continue };
                                let Some(Expr::List(pattern)) = arm.first() else {
                                    continue;
                                };
                                if !matches!(pattern.first(), Some(Expr::Symbol(pattern_name)) if pattern_name == &struct_name)
                                {
                                    continue;
                                }
                                for (binding, field) in pattern[1..].iter().zip(fields) {
                                    if let Expr::Symbol(binding) = binding {
                                        if binding != "_" {
                                            types
                                                .entry(binding.clone())
                                                .or_insert(field.ty.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                if let Some(scrutinee_type) = items.get(1).and_then(|scrutinee| {
                    collected_expression_type(scrutinee, types, aliases, structs)
                }) {
                    if let Type::Tuple(fields) = scrutinee_type.clone() {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(Expr::List(pattern)) = arm.first() else {
                                continue;
                            };
                            if !matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "tuple")
                            {
                                continue;
                            }
                            for (binding, field_type) in pattern[1..].iter().zip(&fields) {
                                if let Expr::Symbol(binding) = binding {
                                    if binding != "_" {
                                        types.entry(binding.clone()).or_insert(field_type.clone());
                                    }
                                }
                            }
                        }
                    }
                    if let Type::Array(element, length) = scrutinee_type.clone() {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(Expr::List(pattern)) = arm.first() else {
                                continue;
                            };
                            if !matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "array")
                            {
                                continue;
                            }
                            for binding in pattern[1..].iter().take(length) {
                                if let Expr::Symbol(binding) = binding {
                                    if binding != "_" {
                                        types.entry(binding.clone()).or_insert((*element).clone());
                                    }
                                }
                            }
                        }
                    }
                    if let Type::Named(struct_name) = scrutinee_type {
                        if let Some(fields) = structs.get(&struct_name) {
                            for arm in items.iter().skip(2) {
                                let Expr::List(arm) = arm else { continue };
                                let Some(Expr::List(pattern)) = arm.first() else {
                                    continue;
                                };
                                if !matches!(pattern.first(), Some(Expr::Symbol(name)) if name == &struct_name)
                                {
                                    continue;
                                }
                                for (binding, field) in pattern[1..].iter().zip(fields) {
                                    if let Expr::Symbol(binding) = binding {
                                        if binding != "_" {
                                            types
                                                .entry(binding.clone())
                                                .or_insert(field.ty.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
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
                        if let Ok(field_type) = resolve_type(field_type, aliases) {
                            collect_enum_pattern_types(binding, &field_type, types, structs);
                        }
                    }
                }
            }
            for item in items {
                collect_expr_types(item, types, aliases, enums, structs);
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_local_types(statement, types, aliases, enums, structs);
            }
        }
        Expr::Loop(statements) => {
            for statement in statements {
                collect_local_types(statement, types, aliases, enums, structs);
            }
        }
        _ => {}
    }
}

fn max_let_else_storage_in_expression(
    expression: &Expr,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
) -> Result<usize, String> {
    match expression {
        Expr::Block(statements) => {
            let max = statements
                .iter()
                .map(|statement| {
                    max_let_else_storage_in_statement(statement, structs, enums, aliases)
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(0);
            Ok(max)
        }
        Expr::List(items) => {
            let max = items
                .iter()
                .map(|item| max_let_else_storage_in_expression(item, structs, enums, aliases))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(0);
            Ok(max)
        }
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => {
            max_let_else_storage_in_expression(value, structs, enums, aliases)
        }
        _ => Ok(0),
    }
}

fn max_let_else_storage_in_statement(
    statement: &Statement,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
) -> Result<usize, String> {
    let nested = |statements: &[Statement]| {
        statements
            .iter()
            .map(|statement| max_let_else_storage_in_statement(statement, structs, enums, aliases))
            .collect::<Result<Vec<_>, _>>()
            .map(|values| values.into_iter().max().unwrap_or(0))
    };
    match statement {
        Statement::LetElse {
            ty,
            value,
            else_body,
            ..
        } => Ok(
            storage_word_count(&resolve_type(ty, aliases)?, structs, enums)?
                .max(max_let_else_storage_in_expression(
                    value, structs, enums, aliases,
                )?)
                .max(nested(else_body)?),
        ),
        Statement::While { condition, body } => Ok(max_let_else_storage_in_expression(
            condition, structs, enums, aliases,
        )?
        .max(nested(body)?)),
        Statement::Loop { body } => nested(body),
        Statement::For {
            condition, body, ..
        } => Ok(
            max_let_else_storage_in_expression(condition, structs, enums, aliases)?
                .max(nested(body)?),
        ),
        Statement::Expr(value)
        | Statement::Return(Some(value))
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. } => {
            max_let_else_storage_in_expression(value, structs, enums, aliases)
        }
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. } => {
            max_let_else_storage_in_expression(value, structs, enums, aliases)
        }
        Statement::ArrayAssign { index, value, .. } => Ok(max_let_else_storage_in_expression(
            index, structs, enums, aliases,
        )?
        .max(max_let_else_storage_in_expression(
            value, structs, enums, aliases,
        )?)),
        Statement::Labeled { statement, .. } => {
            max_let_else_storage_in_statement(statement, structs, enums, aliases)
        }
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => Ok(0),
    }
}

fn max_projection_depth_in_expression(expression: &Expr) -> usize {
    match expression {
        Expr::List(items) => {
            let children = items
                .iter()
                .map(max_projection_depth_in_expression)
                .max()
                .unwrap_or(0);
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "get" || operator == "index")
            {
                children.max(1 + max_projection_depth_in_expression(&items[1]))
            } else {
                children
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => statements
            .iter()
            .map(max_projection_depth_in_statement)
            .max()
            .unwrap_or(0),
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => max_projection_depth_in_expression(value),
        _ => 0,
    }
}

fn max_projection_depth_in_statement(statement: &Statement) -> usize {
    let nested = |statements: &[Statement]| {
        statements
            .iter()
            .map(max_projection_depth_in_statement)
            .max()
            .unwrap_or(0)
    };
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::Return(Some(value))
        | Statement::Expr(value) => max_projection_depth_in_expression(value),
        Statement::ArrayAssign { index, value, .. } => {
            max_projection_depth_in_expression(index).max(max_projection_depth_in_expression(value))
        }
        Statement::LetElse {
            value, else_body, ..
        } => max_projection_depth_in_expression(value).max(nested(else_body)),
        Statement::While { condition, body } => {
            max_projection_depth_in_expression(condition).max(nested(body))
        }
        Statement::Loop { body } => nested(body),
        Statement::For {
            init,
            condition,
            step,
            body,
        } => max_projection_depth_in_statement(init)
            .max(max_projection_depth_in_expression(condition))
            .max(max_projection_depth_in_statement(step))
            .max(nested(body)),
        Statement::Labeled { statement, .. } => max_projection_depth_in_statement(statement),
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::BreakToValue { .. }
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => 0,
    }
}

fn collect_match_pattern_types(
    pattern: &Expr,
    ty: &Type,
    types: &mut HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) {
    let Expr::List(items) = pattern else {
        if let Expr::Symbol(name) = pattern {
            if name != "_" && name != "true" && name != "false" {
                types.entry(name.clone()).or_insert_with(|| ty.clone());
            }
        }
        return;
    };
    let Some(Expr::Symbol(constructor)) = items.first() else {
        return;
    };
    let fields = match ty {
        Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
        Type::Array(element, length) if constructor == "array" => {
            vec![element.as_ref().clone(); *length]
        }
        Type::Named(name) if constructor == name => structs
            .get(name)
            .map(|fields| fields.iter().map(|field| field.ty.clone()).collect())
            .unwrap_or_default(),
        _ => return,
    };
    for (nested, field_type) in items[1..].iter().zip(fields.iter()) {
        collect_match_pattern_types(nested, field_type, types, structs);
    }
}

fn collect_enum_pattern_types(
    pattern: &Expr,
    ty: &Type,
    types: &mut HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) {
    let Expr::List(items) = pattern else {
        if let Expr::Symbol(name) = pattern {
            if name != "_" && name != "true" && name != "false" {
                types.entry(name.clone()).or_insert_with(|| ty.clone());
            }
        }
        return;
    };
    let Some(Expr::Symbol(constructor)) = items.first() else {
        return;
    };
    let fields = match ty {
        Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
        Type::Array(element, length) if constructor == "array" => {
            vec![element.as_ref().clone(); *length]
        }
        Type::Named(name) if constructor == name => structs
            .get(name)
            .map(|fields| fields.iter().map(|field| field.ty.clone()).collect())
            .unwrap_or_default(),
        _ => return,
    };
    for (nested, field_type) in items[1..].iter().zip(fields.iter()) {
        collect_enum_pattern_types(nested, field_type, types, structs);
    }
}

fn collect_locals(
    statement: &Statement,
    locals: &mut HashMap<String, Storage>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    next_slot: &mut usize,
    types: &HashMap<String, Type>,
) -> Result<(), String> {
    match statement {
        Statement::Let { name, ty, .. } => {
            add_local(locals, name, ty, structs, enums, aliases, next_slot)?;
            if let Statement::Let { value, .. } = statement {
                collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        Statement::Destructure {
            pattern, ty, value, ..
        } => {
            let ty = resolve_type(ty, aliases)?;
            for (name, field_type) in destructure_bindings(pattern, &ty, structs)? {
                add_local(
                    locals,
                    &name,
                    &field_type,
                    structs,
                    enums,
                    aliases,
                    next_slot,
                )?;
            }
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?;
        }
        Statement::While { condition, body } => {
            collect_expr_locals(condition, locals, structs, enums, aliases, next_slot, types)?;
            for statement in body {
                collect_locals(statement, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_locals(statement, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_locals(init, locals, structs, enums, aliases, next_slot, types)?;
            collect_expr_locals(condition, locals, structs, enums, aliases, next_slot, types)?;
            collect_locals(step, locals, structs, enums, aliases, next_slot, types)?;
            for statement in body {
                collect_locals(statement, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        Statement::Assign { value, .. } => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?
        }
        Statement::ArrayAssign { index, value, .. } => {
            collect_expr_locals(index, locals, structs, enums, aliases, next_slot, types)?;
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?;
        }
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => {
            let ty = resolve_type(ty, aliases)?;
            for (name, field_type) in let_else_bindings(pattern, &ty, structs, enums)? {
                add_local(
                    locals,
                    &name,
                    &field_type,
                    structs,
                    enums,
                    aliases,
                    next_slot,
                )?;
            }
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?;
            for statement in else_body {
                collect_locals(statement, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        Statement::FieldAssign { value, .. } => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?
        }
        Statement::TupleAssign { value, .. } => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?
        }
        Statement::EnumPayloadAssign { value, .. } => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?
        }
        Statement::BreakValue(value) => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?
        }
        Statement::BreakToValue { value, .. } => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?
        }
        Statement::Return(Some(value)) | Statement::Expr(value) => {
            collect_expr_locals(value, locals, structs, enums, aliases, next_slot, types)?
        }
        Statement::Labeled { statement, .. } => {
            collect_locals(statement, locals, structs, enums, aliases, next_slot, types)?;
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
    Ok(())
}

fn collect_match_pattern_locals(
    pattern: &Expr,
    ty: &Type,
    locals: &mut HashMap<String, Storage>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    next_slot: &mut usize,
) -> Result<(), String> {
    let Expr::List(items) = pattern else {
        if let Expr::Symbol(name) = pattern {
            if name != "_" && name != "true" && name != "false" && !locals.contains_key(name) {
                add_local(locals, name, ty, structs, enums, aliases, next_slot)?;
            }
        }
        return Ok(());
    };
    let Some(Expr::Symbol(constructor)) = items.first() else {
        return Ok(());
    };
    let fields = match ty {
        Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
        Type::Array(element, length) if constructor == "array" => {
            vec![element.as_ref().clone(); *length]
        }
        Type::Named(name) if constructor == name => structs
            .get(name)
            .map(|fields| fields.iter().map(|field| field.ty.clone()).collect())
            .unwrap_or_default(),
        _ => return Ok(()),
    };
    for (nested, field_type) in items[1..].iter().zip(fields.iter()) {
        collect_match_pattern_locals(
            nested, field_type, locals, structs, enums, aliases, next_slot,
        )?;
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
    types: &HashMap<String, Type>,
) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                if let Some(scrutinee_type) = items.get(1).and_then(|scrutinee| {
                    collected_expression_type(scrutinee, types, aliases, structs)
                }) {
                    if matches!(&scrutinee_type, Type::Tuple(_) | Type::Array(_, _))
                        || matches!(&scrutinee_type, Type::Named(name) if structs.contains_key(name))
                    {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(pattern) = arm.first() else { continue };
                            collect_match_pattern_locals(
                                pattern,
                                &scrutinee_type,
                                locals,
                                structs,
                                enums,
                                aliases,
                                next_slot,
                            )?;
                        }
                    }
                }
                if let Some(scrutinee_type) = items.get(1).and_then(|scrutinee| {
                    collected_expression_type(scrutinee, types, aliases, structs)
                }) {
                    match scrutinee_type {
                        Type::Tuple(fields) => {
                            for arm in items.iter().skip(2) {
                                let Expr::List(arm) = arm else { continue };
                                let Some(Expr::List(pattern)) = arm.first() else {
                                    continue;
                                };
                                if !matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "tuple")
                                {
                                    continue;
                                }
                                for (binding, field_type) in pattern[1..].iter().zip(&fields) {
                                    let Expr::Symbol(binding) = binding else {
                                        continue;
                                    };
                                    if binding == "_" || locals.contains_key(binding) {
                                        continue;
                                    }
                                    add_local(
                                        locals, binding, field_type, structs, enums, aliases,
                                        next_slot,
                                    )?;
                                }
                            }
                        }
                        Type::Array(element, length) => {
                            for arm in items.iter().skip(2) {
                                let Expr::List(arm) = arm else { continue };
                                let Some(Expr::List(pattern)) = arm.first() else {
                                    continue;
                                };
                                if !matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "array")
                                {
                                    continue;
                                }
                                for binding in pattern[1..].iter().take(length) {
                                    let Expr::Symbol(binding) = binding else {
                                        continue;
                                    };
                                    if binding == "_" || locals.contains_key(binding) {
                                        continue;
                                    }
                                    add_local(
                                        locals, binding, &element, structs, enums, aliases,
                                        next_slot,
                                    )?;
                                }
                            }
                        }
                        Type::Named(struct_name) => {
                            if let Some(fields) = structs.get(&struct_name) {
                                for arm in items.iter().skip(2) {
                                    let Expr::List(arm) = arm else { continue };
                                    let Some(Expr::List(pattern)) = arm.first() else {
                                        continue;
                                    };
                                    if !matches!(pattern.first(), Some(Expr::Symbol(name)) if name == &struct_name)
                                    {
                                        continue;
                                    }
                                    for (binding, field) in pattern[1..].iter().zip(fields) {
                                        let Expr::Symbol(binding) = binding else {
                                            continue;
                                        };
                                        if binding == "_" || locals.contains_key(binding) {
                                            continue;
                                        }
                                        add_local(
                                            locals, binding, &field.ty, structs, enums, aliases,
                                            next_slot,
                                        )?;
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    if let Some(Type::Tuple(fields)) = types.get(name) {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(Expr::List(pattern)) = arm.first() else {
                                continue;
                            };
                            if !matches!(
                                pattern.first(),
                                Some(Expr::Symbol(operator)) if operator == "tuple"
                            ) {
                                continue;
                            }
                            for (binding, field_type) in pattern[1..].iter().zip(fields) {
                                let Expr::Symbol(binding) = binding else {
                                    continue;
                                };
                                if binding == "_" || locals.contains_key(binding) {
                                    continue;
                                }
                                add_local(
                                    locals, binding, field_type, structs, enums, aliases, next_slot,
                                )?;
                            }
                        }
                    }
                    if let Some(Type::Array(element, length)) = types.get(name) {
                        for arm in items.iter().skip(2) {
                            let Expr::List(arm) = arm else { continue };
                            let Some(Expr::List(pattern)) = arm.first() else {
                                continue;
                            };
                            if !matches!(
                                pattern.first(),
                                Some(Expr::Symbol(operator)) if operator == "array"
                            ) {
                                continue;
                            }
                            for binding in pattern[1..].iter().take(*length) {
                                let Expr::Symbol(binding) = binding else {
                                    continue;
                                };
                                if binding == "_" || locals.contains_key(binding) {
                                    continue;
                                }
                                add_local(
                                    locals, binding, element, structs, enums, aliases, next_slot,
                                )?;
                            }
                        }
                    }
                }
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    if let Some(Type::Named(struct_name)) = types.get(name) {
                        if let Some(fields) = structs.get(struct_name) {
                            for arm in items.iter().skip(2) {
                                let Expr::List(arm) = arm else { continue };
                                let Some(Expr::List(pattern)) = arm.first() else {
                                    continue;
                                };
                                if !matches!(pattern.first(), Some(Expr::Symbol(pattern_name)) if pattern_name == struct_name)
                                {
                                    continue;
                                }
                                for (binding, field) in pattern[1..].iter().zip(fields) {
                                    let Expr::Symbol(binding) = binding else {
                                        continue;
                                    };
                                    if binding == "_" || locals.contains_key(binding) {
                                        continue;
                                    }
                                    add_local(
                                        locals, binding, &field.ty, structs, enums, aliases,
                                        next_slot,
                                    )?;
                                }
                            }
                        }
                    }
                }
            }
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
                        collect_enum_pattern_locals(
                            binding,
                            &field_type,
                            locals,
                            structs,
                            enums,
                            aliases,
                            next_slot,
                        )?;
                    }
                }
            }
            for item in items {
                collect_expr_locals(item, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_locals(statement, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        Expr::Loop(statements) => {
            for statement in statements {
                collect_locals(statement, locals, structs, enums, aliases, next_slot, types)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn collect_enum_pattern_locals(
    pattern: &Expr,
    ty: &Type,
    locals: &mut HashMap<String, Storage>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    next_slot: &mut usize,
) -> Result<(), String> {
    let Expr::List(items) = pattern else {
        if let Expr::Symbol(name) = pattern {
            if name != "_" && name != "true" && name != "false" && !locals.contains_key(name) {
                add_local(locals, name, ty, structs, enums, aliases, next_slot)?;
            }
        }
        return Ok(());
    };
    let Some(Expr::Symbol(constructor)) = items.first() else {
        return Ok(());
    };
    let fields = match ty {
        Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
        Type::Array(element, length) if constructor == "array" => {
            vec![element.as_ref().clone(); *length]
        }
        Type::Named(name) if constructor == name => structs
            .get(name)
            .map(|fields| fields.iter().map(|field| field.ty.clone()).collect())
            .unwrap_or_default(),
        _ => return Ok(()),
    };
    for (nested, field_type) in items[1..].iter().zip(fields.iter()) {
        collect_enum_pattern_locals(
            nested, field_type, locals, structs, enums, aliases, next_slot,
        )?;
    }
    Ok(())
}

fn collected_expression_type(
    expression: &Expr,
    types: &HashMap<String, Type>,
    aliases: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) -> Option<Type> {
    match expression {
        Expr::Symbol(name) => types.get(name).cloned(),
        Expr::List(items) => match items.first() {
            Some(Expr::Symbol(name)) if name == "array" && items.len() >= 2 => {
                match parse_type(items.get(1))
                    .ok()
                    .and_then(|ty| resolve_type(&ty, aliases).ok())
                {
                    Some(Type::Array(element, length)) if items.len() - 2 == length => {
                        Some(Type::Array(element, length))
                    }
                    _ => None,
                }
            }
            Some(Expr::Symbol(name)) if name == "tuple" && items.len() >= 2 => {
                match parse_type(items.get(1))
                    .ok()
                    .and_then(|ty| resolve_type(&ty, aliases).ok())
                {
                    Some(Type::Tuple(fields)) if items.len() - 2 == fields.len() => {
                        Some(Type::Tuple(fields))
                    }
                    _ => None,
                }
            }
            Some(Expr::Symbol(name)) if structs.contains_key(name) => {
                (items.len() - 1 == structs[name].len()).then(|| Type::Named(name.clone()))
            }
            Some(Expr::Symbol(name)) => types.get(name).cloned(),
            _ => None,
        },
        _ => None,
    }
}

fn destructure_bindings(
    pattern: &Expr,
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<Vec<(String, Type)>, String> {
    let Expr::List(items) = pattern else {
        return Err("destructuring pattern must be a tuple or struct constructor".into());
    };
    let Some(Expr::Symbol(constructor)) = items.first() else {
        return Err("destructuring pattern must start with a constructor".into());
    };
    let fields = match ty {
        Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
        Type::Array(element, length) if constructor == "array" => {
            vec![*element.clone(); *length]
        }
        Type::Named(name) if name == constructor => structs
            .get(name)
            .ok_or_else(|| format!("unknown struct '{name}'"))?
            .iter()
            .map(|field| field.ty.clone())
            .collect(),
        _ => return Err("destructuring pattern does not match its declared type".into()),
    };
    if items.len() - 1 != fields.len() {
        return Err(format!(
            "destructuring pattern expects {} fields",
            fields.len()
        ));
    }
    let mut bindings = Vec::new();
    for (binding, field_type) in items[1..].iter().zip(fields) {
        match binding {
            Expr::Symbol(binding) if binding == "_" => {}
            Expr::Symbol(binding) => bindings.push((binding.clone(), field_type)),
            Expr::List(_) => bindings.extend(destructure_bindings(binding, &field_type, structs)?),
            _ => return Err("destructuring fields must be bindings or nested patterns".into()),
        }
    }
    Ok(bindings)
}

fn let_else_bindings(
    pattern: &Expr,
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<Vec<(String, Type)>, String> {
    if matches!(pattern, Expr::Symbol(name) if name == "_") {
        return Ok(Vec::new());
    }
    if let Type::Named(enum_name) = ty {
        if let Some(variants) = enums.get(enum_name) {
            if let Expr::List(items) = pattern {
                if items.len() >= 2
                    && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or")
                {
                    for alternative in &items[1..] {
                        let (name, payload): (&str, Vec<&Expr>) = match alternative {
                            Expr::Symbol(name) => (name, Vec::new()),
                            Expr::List(items) if !items.is_empty() => {
                                let Expr::Symbol(name) = &items[0] else {
                                    return Err(
                                        "enum let-else alternatives must be variants".into()
                                    );
                                };
                                (name, items[1..].iter().collect())
                            }
                            _ => return Err("enum let-else alternatives must be variants".into()),
                        };
                        let Some(variant) = variants.iter().find(|variant| variant.name == name)
                        else {
                            return Err(format!("unknown enum variant '{name}'"));
                        };
                        if !payload.is_empty() && payload.len() != variant.fields.len() {
                            return Err(format!(
                                "variant '{name}' expects {} payload patterns",
                                variant.fields.len()
                            ));
                        }
                    }
                    return Ok(Vec::new());
                }
            }
            let (variant_name, payload) = match pattern {
                Expr::Symbol(name) => (name.as_str(), Vec::new()),
                Expr::List(items) if !items.is_empty() => {
                    let Expr::Symbol(name) = &items[0] else {
                        return Err("let-else enum pattern must start with a variant".into());
                    };
                    (name.as_str(), items[1..].iter().collect())
                }
                _ => return Err("let-else pattern must be an enum constructor".into()),
            };
            let variant = variants
                .iter()
                .find(|variant| variant.name == variant_name)
                .ok_or_else(|| format!("unknown enum variant '{variant_name}'"))?;
            if payload.len() != variant.fields.len() {
                return Err(format!(
                    "variant '{variant_name}' has the wrong payload count"
                ));
            }
            let mut bindings = Vec::new();
            for (pattern, field_type) in payload.iter().zip(&variant.fields) {
                collect_aggregate_binding_types(pattern, field_type, structs, &mut bindings)?;
            }
            return Ok(bindings);
        }
    }
    let mut bindings = Vec::new();
    collect_aggregate_binding_types(pattern, ty, structs, &mut bindings)?;
    Ok(bindings)
}

fn collect_aggregate_binding_types(
    pattern: &Expr,
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    bindings: &mut Vec<(String, Type)>,
) -> Result<(), String> {
    match pattern {
        Expr::Symbol(name) if name == "_" || name == "true" || name == "false" => Ok(()),
        Expr::Symbol(name) => {
            bindings.push((name.clone(), ty.clone()));
            Ok(())
        }
        Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Char(_) => Ok(()),
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "literal") =>
        {
            Ok(())
        }
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "range") =>
        {
            Ok(())
        }
        Expr::List(items)
            if items.len() >= 2
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or") =>
        {
            Ok(())
        }
        Expr::List(items) => {
            let Some(Expr::Symbol(constructor)) = items.first() else {
                return Err("let-else aggregate pattern must start with a constructor".into());
            };
            let fields = match ty {
                Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
                Type::Array(element, length) if constructor == "array" => {
                    vec![element.as_ref().clone(); *length]
                }
                Type::Named(name) if constructor == name => structs
                    .get(name)
                    .ok_or_else(|| format!("unknown struct '{name}'"))?
                    .iter()
                    .map(|field| field.ty.clone())
                    .collect(),
                _ => return Err("let-else pattern does not match its type".into()),
            };
            if items.len() - 1 != fields.len() {
                return Err("let-else aggregate pattern has the wrong field count".into());
            }
            for (pattern, field_type) in items[1..].iter().zip(fields) {
                collect_aggregate_binding_types(pattern, &field_type, structs, bindings)?;
            }
            Ok(())
        }
        _ => Err("unsupported let-else pattern".into()),
    }
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
    let storage = if matches!(ty, Type::Unit | Type::Never) {
        Storage::Zero
    } else if let Type::Named(enum_name) = &ty {
        if let Some(variants) = enums.get(enum_name) {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                let discriminant = *next_slot;
                *next_slot += 1;
                let payload_count = variants
                    .iter()
                    .map(|variant| {
                        variant
                            .fields
                            .iter()
                            .map(|field| storage_word_count(field, structs, enums))
                            .collect::<Result<Vec<_>, _>>()
                            .map(|words| words.into_iter().sum::<usize>())
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .max()
                    .unwrap_or(0);
                let mut payload = Vec::with_capacity(payload_count);
                for _ in 0..payload_count {
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
                let words = storage_word_count(&field.ty, structs, enums)?;
                let field_slots = flat_slots(*next_slot, words);
                *next_slot += words;
                slots.push((field.name.clone(), field_slots));
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
        let element_words = storage_word_count(element, structs, enums)?;
        let base = *next_slot;
        *next_slot += length * element_words;
        Storage::Array {
            base,
            length: *length,
            element_words,
        }
    } else if matches!(&ty, Type::Tuple(_)) {
        let base = *next_slot;
        let words = storage_word_count(&ty, structs, enums)?;
        *next_slot += words;
        Storage::Tuple((base..base + words).collect())
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
        Storage::Zero => Ok(Vec::new()),
        Storage::Scalar(slot) => Ok(vec![*slot]),
        Storage::Wide { low, high } => Ok(vec![*low, *high]),
        Storage::Struct(slots) => Ok(slots
            .iter()
            .flat_map(|(_, slots)| slots.iter().copied())
            .collect()),
        Storage::Enum {
            discriminant,
            payload,
        } => Ok(std::iter::once(*discriminant)
            .chain(payload.iter().copied())
            .collect()),
        Storage::Array {
            base,
            length,
            element_words,
        } => Ok((*base..*base + *length * *element_words).collect()),
        Storage::Tuple(slots) => Ok(slots.clone()),
    }
}

fn flat_slots(base: usize, words: usize) -> Vec<usize> {
    (base..base + words).collect()
}

fn storage_word_count(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<usize, String> {
    if matches!(ty, Type::Unit | Type::Never) {
        return Ok(0);
    }
    if is_wide_integer(ty) {
        return Ok(2);
    }
    if ensure_scalar_type(ty, enums).is_ok() {
        return Ok(1);
    }
    match ty {
        Type::Array(element, length) => {
            Ok(storage_word_count(element, structs, enums)?.saturating_mul(*length))
        }
        Type::Tuple(fields) => fields
            .iter()
            .map(|field| storage_word_count(field, structs, enums))
            .sum(),
        Type::Named(name) if structs.contains_key(name) => structs[name]
            .iter()
            .map(|field| storage_word_count(&field.ty, structs, enums))
            .sum(),
        Type::Named(name) if enums.contains_key(name) => {
            let payload_words = enums[name]
                .iter()
                .map(|variant| {
                    variant
                        .fields
                        .iter()
                        .map(|field| storage_word_count(field, structs, enums))
                        .sum::<Result<usize, String>>()
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(0);
            Ok(1 + payload_words)
        }
        _ => Err(format!("native backend does not support local type {ty:?}")),
    }
}

fn supports_indirect_return_type(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> bool {
    if !storage_word_count(ty, structs, enums).is_ok_and(|words| words > VALUE_REGISTERS.len()) {
        return false;
    }
    match ty {
        Type::Array(element, _) => storage_word_count(element, structs, enums).is_ok(),
        Type::Tuple(fields) => fields
            .iter()
            .all(|field| storage_word_count(field, structs, enums).is_ok()),
        Type::Named(name) => {
            if let Some(fields) = structs.get(name) {
                return fields
                    .iter()
                    .all(|field| storage_word_count(&field.ty, structs, enums).is_ok());
            }
            enums.get(name).is_some_and(|variants| {
                variants.iter().all(|variant| {
                    variant
                        .fields
                        .iter()
                        .all(|field| storage_word_count(field, structs, enums).is_ok())
                })
            })
        }
        _ => false,
    }
}

fn match_arm_parts(arm: &Expr) -> Result<(&Expr, Option<&Expr>, &Expr), String> {
    let Expr::List(arm) = arm else {
        return Err("match arms must have the form (pattern expression)".into());
    };
    match arm.as_slice() {
        [pattern, body] => Ok((pattern, None, body)),
        [pattern, Expr::List(guard), body]
            if matches!(guard.first(), Some(Expr::Symbol(name)) if name == "when")
                && guard.len() == 2 =>
        {
            Ok((pattern, Some(&guard[1]), body))
        }
        _ => Err(
            "match arms must have the form (pattern expression) or (pattern (when guard) expression)"
                .into(),
        ),
    }
}

fn value_word_count(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<usize, String> {
    if matches!(ty, Type::Unit | Type::Never) {
        return Ok(0);
    }
    if is_wide_integer(ty) {
        return Ok(2);
    }
    if ensure_scalar_type(ty, enums).is_ok() {
        return Ok(1);
    }
    if let Type::Named(name) = ty {
        if let Some(fields) = structs.get(name) {
            let words = fields
                .iter()
                .map(|field| value_word_count(&field.ty, structs, enums))
                .collect::<Result<Vec<_>, _>>()?;
            let total = words.into_iter().sum::<usize>();
            if total <= VALUE_REGISTERS.len() {
                return Ok(total);
            }
        }
        if let Some(variants) = enums.get(name) {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                let payload_words = variants
                    .iter()
                    .map(|variant| {
                        variant
                            .fields
                            .iter()
                            .map(|field| value_word_count(field, structs, enums))
                            .collect::<Result<Vec<_>, _>>()
                            .map(|words| words.into_iter().sum::<usize>())
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .max()
                    .unwrap_or(0);
                if payload_words + 1 > VALUE_REGISTERS.len() {
                    return Err(format!(
                        "native ABI does not support enum value type {ty:?}"
                    ));
                }
                return Ok(1 + payload_words);
            }
        }
    }
    if let Type::Array(element, length) = ty {
        let element_words = storage_word_count(element, structs, enums)?;
        let total = element_words.saturating_mul(*length);
        if total <= VALUE_REGISTERS.len() {
            return Ok(total);
        }
    }
    if let Type::Tuple(fields) = ty {
        let words = fields
            .iter()
            .map(|field| value_word_count(field, structs, enums))
            .collect::<Result<Vec<_>, _>>()?;
        let total = words.into_iter().sum::<usize>();
        if total <= VALUE_REGISTERS.len() {
            return Ok(total);
        }
    }
    Err(format!("native ABI does not support value type {ty:?}"))
}

#[derive(Clone, Debug)]
enum Storage {
    Zero,
    Scalar(usize),
    Array {
        base: usize,
        length: usize,
        element_words: usize,
    },
    Tuple(Vec<usize>),
    Struct(Vec<(String, Vec<usize>)>),
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
        Storage::Zero
        | Storage::Array { .. }
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

fn integer_bounds(ty: &Type) -> Option<(i128, i128)> {
    let width = integer_bit_width(ty.clone())?;
    if width == 128 {
        return if is_unsigned_type(ty) {
            None
        } else {
            Some((i128::MIN, i128::MAX))
        };
    }
    if is_unsigned_type(ty) {
        Some((0, (1_i128 << width) - 1))
    } else {
        let half = 1_i128 << (width - 1);
        Some((-half, half - 1))
    }
}

fn asm_integer_bound(value: i128, ty: &Type) -> String {
    if is_unsigned_type(ty)
        && matches!(ty, Type::U64 | Type::Usize)
        && value == i128::from(u64::MAX)
    {
        "-1".into()
    } else {
        value.to_string()
    }
}

fn is_unsigned_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 | Type::Usize
    )
}

fn typed_integer_pattern_value<'a>(
    pattern: &'a Expr,
    expected: &Type,
) -> Result<Option<&'a Expr>, String> {
    let Expr::List(items) = pattern else {
        return Ok(None);
    };
    if items.len() != 3 || !matches!(items.first(), Some(Expr::Symbol(name)) if name == "literal") {
        return Ok(None);
    }
    let literal_type = parse_type(items.get(1))?;
    if literal_type != *expected
        || !matches!(
            literal_type,
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
    {
        return Err(format!(
            "typed integer pattern has type {literal_type:?}, expected {expected:?}"
        ));
    }
    if !matches!(items[2], Expr::Integer(_) | Expr::UnsignedInteger(_)) {
        return Err("typed integer pattern requires an integer literal".into());
    }
    Ok(Some(&items[2]))
}

fn is_wide_integer(ty: &Type) -> bool {
    matches!(ty, Type::I128 | Type::U128)
}

fn is_scalar_pattern_type(ty: &Type) -> bool {
    matches!(
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
    )
}

fn is_float_type(ty: &Type) -> bool {
    matches!(ty, Type::F32 | Type::F64)
}

fn ensure_scalar_type(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> Result<(), String> {
    if let Type::Cell(target) = ty {
        return ensure_scalar_type(target, enums);
    }
    if matches!(ty, Type::Reference { .. } | Type::RawPointer { .. }) {
        return Ok(());
    }
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
    if matches!(ty, Type::Unit | Type::Never) {
        return Ok(());
    }
    if ensure_scalar_type(ty, enums).is_ok() {
        return Ok(());
    }
    if value_word_count(ty, structs, enums).is_ok() {
        return Ok(());
    }
    if let Type::Array(element, _) = ty {
        if storage_word_count(ty, structs, enums).is_ok()
            && storage_word_count(element, structs, enums).is_ok()
        {
            return Ok(());
        }
    }
    if let Type::Tuple(fields) = ty {
        if storage_word_count(ty, structs, enums).is_ok()
            && fields
                .iter()
                .all(|field| storage_word_count(field, structs, enums).is_ok())
        {
            return Ok(());
        }
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
        if supports_indirect_return_type(ty, structs, enums) {
            return Ok(());
        }
        return Err(format!(
            "native backend only supports scalar struct returns for '{name}'"
        ));
    }
    let Some(variants) = enums.get(name) else {
        return Err(format!("unknown return type '{name}'"));
    };
    if (variants.iter().all(|variant| variant.fields.len() <= 1)
        && variants
            .iter()
            .filter_map(|variant| variant.fields.first())
            .all(|field| ensure_integer_type(field).is_ok()))
        || supports_indirect_return_type(ty, structs, enums)
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
    if supports_indirect_return_type(ty, structs, enums) {
        return Ok(());
    }
    value_word_count(ty, structs, enums)?;
    if !is_flat_native_value(ty, structs, enums) {
        return Err(format!(
            "native backend only supports scalar-flattened parameter type {ty:?}"
        ));
    }
    Ok(())
}

fn is_external_scalar_type(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> bool {
    is_wide_integer(ty) || ensure_scalar_type(ty, enums).is_ok()
}

fn is_flat_native_value(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> bool {
    if matches!(ty, Type::Unit | Type::Never) {
        return true;
    }
    if ensure_scalar_type(ty, enums).is_ok() || is_wide_integer(ty) {
        return true;
    }
    match ty {
        Type::Array(element, length) => {
            *length == 0
                || (value_word_count(ty, structs, enums).is_ok()
                    && is_flat_native_value(element, structs, enums))
        }
        Type::Tuple(fields) => {
            value_word_count(ty, structs, enums).is_ok()
                && fields
                    .iter()
                    .all(|field| is_flat_native_value(field, structs, enums))
        }
        Type::Named(name) => {
            if let Some(fields) = structs.get(name) {
                return value_word_count(ty, structs, enums).is_ok()
                    && fields
                        .iter()
                        .all(|field| is_flat_native_value(&field.ty, structs, enums));
            }
            if let Some(variants) = enums.get(name) {
                return variants.iter().all(|variant| {
                    variant
                        .fields
                        .iter()
                        .all(|field| is_flat_native_value(field, structs, enums))
                });
            }
            false
        }
        _ => false,
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
                return Err(format!("recursive type alias '{name}'"));
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

fn constant_value(
    expression: &Expr,
    enums: &HashMap<String, Vec<EnumVariant>>,
    constants: &HashMap<String, i128>,
    initializers: &HashMap<String, Expr>,
    evaluating: &mut HashSet<String>,
    target: Option<&Type>,
) -> Result<i128, String> {
    match expression {
        Expr::Integer(value) => Ok(*value),
        Expr::UnsignedInteger(value) => {
            if matches!(target, Some(Type::U128)) {
                Ok(*value as i128)
            } else {
                (*value).try_into().map_err(|_| {
                    "unsigned constant is too large for the native global evaluator".into()
                })
            }
        }
        Expr::Char(value) => Ok(*value as i128),
        Expr::Float(_) => Err("floating-point global initializers are not supported".into()),
        Expr::Symbol(name) if name == "true" => Ok(1),
        Expr::Symbol(name) if name == "false" => Ok(0),
        Expr::Symbol(name) if constants.contains_key(name) => Ok(constants[name]),
        Expr::Symbol(name) if initializers.contains_key(name) => {
            if !evaluating.insert(name.clone()) {
                return Err(format!("constant '{name}' is recursive"));
            }
            let result = constant_value(
                &initializers[name],
                enums,
                constants,
                initializers,
                evaluating,
                target,
            );
            evaluating.remove(name);
            result
        }
        Expr::Symbol(name) => enums
            .values()
            .find_map(|variants| {
                variants
                    .iter()
                    .find(|variant| variant.name == *name)
                    .map(|variant| variant.discriminant as i128)
            })
            .ok_or_else(|| format!("global initializer '{name}' is not a constant")),
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "literal") =>
        {
            let literal_type = parse_type(items.get(1))?;
            constant_value(
                &items[2],
                enums,
                constants,
                initializers,
                evaluating,
                Some(&literal_type),
            )
        }
        Expr::List(items)
            if items.len() == 4
                && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") =>
        {
            let condition = constant_value(
                &items[1],
                enums,
                constants,
                initializers,
                evaluating,
                Some(&Type::Bool),
            )?;
            constant_value(
                if condition != 0 { &items[2] } else { &items[3] },
                enums,
                constants,
                initializers,
                evaluating,
                target,
            )
        }
        Expr::List(items) if items.len() == 2 => {
            let operator = match &items[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => return Err("global initializer is not constant".into()),
            };
            let (qualifier, operator, mode) = operator_parts(operator);
            let value = constant_value(
                &items[1],
                enums,
                constants,
                initializers,
                evaluating,
                target,
            )?;
            if operator == "-"
                && (matches!(qualifier.map(Type::from_name), Some(Type::U128))
                    || matches!(target, Some(Type::U128)))
            {
                if mode == Some("saturate") {
                    return Ok(0);
                }
                return Ok((0u128.wrapping_sub(value as u128)) as i128);
            }
            if operator == "-" {
                let operation_type = qualifier.map(Type::from_name).or_else(|| target.cloned());
                if matches!(operation_type, Some(Type::I128)) {
                    return Ok(if mode == Some("saturate") {
                        if value == i128::MIN {
                            i128::MAX
                        } else {
                            -value
                        }
                    } else {
                        value.wrapping_neg()
                    });
                }
                if mode == Some("saturate") {
                    if let Some(ty) = operation_type.as_ref() {
                        if is_unsigned_type(ty) {
                            return Ok(0);
                        }
                        if let Some((minimum, maximum)) = integer_bounds(ty) {
                            return Ok(if value == minimum {
                                maximum
                            } else {
                                value.checked_neg().ok_or_else(|| {
                                    "constant saturating negation overflowed".to_owned()
                                })?
                            });
                        }
                    }
                }
            }
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
            let (qualifier, operator, mode) = operator_parts(operator);
            if operator == "as" {
                let value = constant_value(
                    &items[1],
                    enums,
                    constants,
                    initializers,
                    evaluating,
                    target,
                )?;
                let cast_target = parse_type(items.get(2))?;
                if !matches!(
                    cast_target,
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
                        | Type::Bool
                        | Type::Char
                ) {
                    return Err("global initializer cast is not an integer constant".into());
                }
                return Ok(normalize_global_integer(value, &cast_target));
            }
            let left = constant_value(
                &items[1],
                enums,
                constants,
                initializers,
                evaluating,
                target,
            )?;
            if operator == "&&" && left == 0 {
                return Ok(0);
            }
            if operator == "||" && left != 0 {
                return Ok(1);
            }
            let right = constant_value(
                &items[2],
                enums,
                constants,
                initializers,
                evaluating,
                target,
            )?;
            let operation_type = qualifier.map(Type::from_name).or_else(|| target.cloned());
            if let Some(ty) = operation_type
                .as_ref()
                .filter(|ty| is_unsigned_type(ty) && !matches!(ty, Type::U128))
            {
                let Some(width) = integer_bit_width(ty.clone()) else {
                    return Err("unsigned constant has no integer width".to_owned());
                };
                let maximum = (1_u128 << width) - 1;
                let left = left as u128;
                let right = right as u128;
                let result = match operator {
                    "+" if mode == Some("saturate") => {
                        left.checked_add(right).unwrap_or(maximum).min(maximum)
                    }
                    "+" => left.wrapping_add(right) & maximum,
                    "-" if mode == Some("saturate") => left.saturating_sub(right),
                    "-" => left.wrapping_sub(right) & maximum,
                    "*" if mode == Some("saturate") => {
                        left.checked_mul(right).unwrap_or(maximum).min(maximum)
                    }
                    "*" => left.wrapping_mul(right) & maximum,
                    "/" => left
                        .checked_div(right)
                        .ok_or_else(|| "constant division failed".to_owned())?,
                    "%" => left
                        .checked_rem(right)
                        .ok_or_else(|| "constant remainder failed".to_owned())?,
                    "&" => left & right,
                    "|" => left | right,
                    "^" => left ^ right,
                    "<<" => {
                        if right >= width as u128 {
                            return Err("constant shift count is out of range".to_owned());
                        }
                        (left << right) & maximum
                    }
                    ">>" => {
                        if right >= width as u128 {
                            return Err("constant shift count is out of range".to_owned());
                        }
                        left >> right
                    }
                    "<" => u128::from(left < right),
                    "<=" => u128::from(left <= right),
                    ">" => u128::from(left > right),
                    ">=" => u128::from(left >= right),
                    "==" => u128::from(left == right),
                    "!=" => u128::from(left != right),
                    "&&" => u128::from(left != 0 && right != 0),
                    "||" => u128::from(left != 0 || right != 0),
                    _ => return Err("global initializer is not constant".to_owned()),
                };
                return Ok(result as i128);
            }
            if matches!(operation_type, Some(Type::U128)) {
                let left = left as u128;
                let right = right as u128;
                let result = match operator {
                    "+" if mode == Some("saturate") => left.saturating_add(right),
                    "+" => left.wrapping_add(right),
                    "-" if mode == Some("saturate") => left.saturating_sub(right),
                    "-" => left.wrapping_sub(right),
                    "*" if mode == Some("saturate") => left.saturating_mul(right),
                    "*" => left.wrapping_mul(right),
                    "/" => left
                        .checked_div(right)
                        .ok_or_else(|| "constant division failed".to_owned())?,
                    "%" => left
                        .checked_rem(right)
                        .ok_or_else(|| "constant remainder failed".to_owned())?,
                    "&" => left & right,
                    "|" => left | right,
                    "^" => left ^ right,
                    "<<" => {
                        if right >= 128 {
                            return Err("constant shift count is out of range".to_owned());
                        }
                        left << right
                    }
                    ">>" => {
                        if right >= 128 {
                            return Err("constant shift count is out of range".to_owned());
                        }
                        left >> right
                    }
                    "<" => u128::from(left < right),
                    "<=" => u128::from(left <= right),
                    ">" => u128::from(left > right),
                    ">=" => u128::from(left >= right),
                    "==" => u128::from(left == right),
                    "!=" => u128::from(left != right),
                    "&&" => u128::from(left != 0 && right != 0),
                    "||" => u128::from(left != 0 || right != 0),
                    _ => return Err("global initializer is not constant".to_owned()),
                };
                return Ok(result as i128);
            }
            if matches!(operation_type, Some(Type::I128)) {
                match operator {
                    "+" => {
                        return Ok(if mode == Some("saturate") {
                            left.saturating_add(right)
                        } else {
                            left.wrapping_add(right)
                        });
                    }
                    "-" => {
                        return Ok(if mode == Some("saturate") {
                            left.saturating_sub(right)
                        } else {
                            left.wrapping_sub(right)
                        });
                    }
                    "*" => {
                        return Ok(if mode == Some("saturate") {
                            left.saturating_mul(right)
                        } else {
                            left.wrapping_mul(right)
                        });
                    }
                    _ => {}
                }
            }
            let result: i128 = match operator {
                "+" => left
                    .checked_add(right)
                    .ok_or_else(|| "constant addition overflowed".to_owned()),
                "-" => left
                    .checked_sub(right)
                    .ok_or_else(|| "constant subtraction overflowed".to_owned()),
                "*" => left
                    .checked_mul(right)
                    .ok_or_else(|| "constant multiplication overflowed".to_owned()),
                "/" if mode == Some("saturate")
                    && operation_type
                        .as_ref()
                        .and_then(integer_bounds)
                        .is_some_and(|(minimum, _)| left == minimum && right == -1) =>
                {
                    Ok(operation_type
                        .as_ref()
                        .and_then(integer_bounds)
                        .expect("checked saturating constant bounds")
                        .1)
                }
                "/" if matches!(operation_type, Some(Type::I128))
                    && left == i128::MIN
                    && right == -1 =>
                {
                    Ok(i128::MIN)
                }
                "/" => left
                    .checked_div(right)
                    .ok_or_else(|| "constant division failed".to_owned()),
                "%" if matches!(operation_type, Some(Type::I128))
                    && left == i128::MIN
                    && right == -1 =>
                {
                    Ok(0)
                }
                "%" => left
                    .checked_rem(right)
                    .ok_or_else(|| "constant remainder failed".to_owned()),
                "&" => Ok(left & right),
                "|" => Ok(left | right),
                "^" => Ok(left ^ right),
                "<<" => {
                    if !(0..128).contains(&right) {
                        return Err("constant shift count is out of range".to_owned());
                    }
                    if matches!(operation_type, Some(Type::I128)) {
                        Ok(left.wrapping_shl(right as u32))
                    } else {
                        left.checked_shl(right as u32)
                            .ok_or_else(|| "constant left shift overflowed".to_owned())
                    }
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
                _ => Err("global initializer is not constant".to_owned()),
            }?;
            if mode == Some("saturate") {
                let operation_type = operation_type
                    .ok_or_else(|| "saturating constant requires a typed operand".to_owned())?;
                if let Some((minimum, maximum)) = integer_bounds(&operation_type) {
                    return Ok(result.clamp(minimum, maximum));
                }
            }
            Ok(result)
        }
        _ => Err("global initializer is not constant".into()),
    }
}

fn constant_float_value(
    expression: &Expr,
    integer_constants: &HashMap<String, i128>,
    constants: &HashMap<String, f64>,
    initializers: &HashMap<String, Expr>,
    evaluating: &mut HashSet<String>,
    single_precision: bool,
) -> Result<f64, String> {
    let normalize = |value: f64| -> Result<f64, String> {
        let value = if single_precision {
            value as f32 as f64
        } else {
            value
        };
        if value.is_finite() {
            Ok(value)
        } else {
            Err("floating-point constant is not finite".into())
        }
    };
    match expression {
        Expr::Float(value) => normalize(
            value
                .parse::<f64>()
                .map_err(|_| format!("invalid floating-point literal '{value}'"))?,
        ),
        Expr::Symbol(name) if constants.contains_key(name) => Ok(constants[name]),
        Expr::Symbol(name) if initializers.contains_key(name) => {
            if !evaluating.insert(name.clone()) {
                return Err(format!("constant '{name}' is recursive"));
            }
            let result = constant_float_value(
                &initializers[name],
                integer_constants,
                constants,
                initializers,
                evaluating,
                single_precision,
            );
            evaluating.remove(name);
            result
        }
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "literal") =>
        {
            let ty = parse_type(items.get(1))?;
            let precision = match ty {
                Type::F32 => true,
                Type::F64 => false,
                _ => return Err("typed floating literal requires f32 or f64".into()),
            };
            constant_float_value(
                &items[2],
                integer_constants,
                constants,
                initializers,
                evaluating,
                precision,
            )
        }
        Expr::List(items)
            if items.len() == 4
                && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") =>
        {
            let condition = match &items[1] {
                Expr::Symbol(name) if name == "true" => true,
                Expr::Symbol(name) if name == "false" => false,
                Expr::Symbol(name) if integer_constants.contains_key(name) => {
                    integer_constants[name] != 0
                }
                _ => return Err("floating-point constant condition must be constant".into()),
            };
            constant_float_value(
                if condition { &items[2] } else { &items[3] },
                integer_constants,
                constants,
                initializers,
                evaluating,
                single_precision,
            )
        }
        Expr::List(items) if items.len() == 2 => {
            let operator = match &items[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => return Err("floating-point global initializer is not constant".into()),
            };
            let operator = operator_base(operator);
            let value = constant_float_value(
                &items[1],
                integer_constants,
                constants,
                initializers,
                evaluating,
                single_precision,
            )?;
            match operator {
                "-" => normalize(-value),
                _ => Err("floating-point global initializer is not constant".into()),
            }
        }
        Expr::List(items) if items.len() == 3 => {
            let operator = match &items[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => return Err("floating-point global initializer is not constant".into()),
            };
            let operator = operator_base(operator);
            let left = constant_float_value(
                &items[1],
                integer_constants,
                constants,
                initializers,
                evaluating,
                single_precision,
            )?;
            let right = constant_float_value(
                &items[2],
                integer_constants,
                constants,
                initializers,
                evaluating,
                single_precision,
            )?;
            match operator {
                "+" => normalize(left + right),
                "-" => normalize(left - right),
                "*" => normalize(left * right),
                "/" => normalize(left / right),
                "%" => normalize(left % right),
                _ => Err("floating-point global initializer is not constant".into()),
            }
        }
        _ => Err("floating-point global initializer is not constant".into()),
    }
}

fn constant_aggregate_words(
    expression: &Expr,
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    constants: &HashMap<String, i128>,
    float_constants: &HashMap<String, f64>,
    initializers: &HashMap<String, Expr>,
    evaluating_constants: &mut HashSet<String>,
    evaluating_float_constants: &mut HashSet<String>,
) -> Result<Vec<u64>, String> {
    if matches!(ty, Type::Unit | Type::Never) {
        return Ok(Vec::new());
    }
    let mut scalar_word = |value: &Expr| -> Result<u64, String> {
        if matches!(ty, Type::F32 | Type::F64) {
            let number = constant_float_value(
                value,
                constants,
                float_constants,
                initializers,
                evaluating_float_constants,
                matches!(ty, Type::F32),
            )?;
            return Ok(if matches!(ty, Type::F32) {
                (number as f32).to_bits() as u64
            } else {
                number.to_bits()
            });
        }
        Ok(normalize_global_integer(
            constant_value(
                value,
                enums,
                constants,
                initializers,
                evaluating_constants,
                Some(ty),
            )?,
            ty,
        ) as u64)
    };

    match ty {
        Type::Array(element, length) => {
            if let Expr::String(string) = expression {
                if !matches!(**element, Type::Char) || string.chars().count() != *length {
                    return Err("string length or element type does not match static array".into());
                }
                return Ok(string.chars().map(|value| value as u64).collect());
            }
            let Expr::List(items) = expression else {
                return Err("static array initializer must be an array constructor".into());
            };
            let (value_start, repeat) = if matches!(
                items.first(),
                Some(Expr::Symbol(operator)) if operator == "array-repeat"
            ) {
                (2, true)
            } else if matches!(
                items.first(),
                Some(Expr::Symbol(operator)) if operator == "array"
            ) {
                (2, false)
            } else {
                return Err("static array initializer must use array or array-repeat".into());
            };
            if parse_type(items.get(1)).ok() != Some(ty.clone()) {
                return Err("static array initializer requires its explicit array type".into());
            }
            if repeat {
                if items.len() != 3 {
                    return Err("array-repeat requires one value".into());
                }
                let words = constant_aggregate_words(
                    &items[2],
                    element,
                    structs,
                    enums,
                    constants,
                    float_constants,
                    initializers,
                    evaluating_constants,
                    evaluating_float_constants,
                )?;
                let mut result = Vec::with_capacity(words.len() * *length);
                for _ in 0..*length {
                    result.extend_from_slice(&words);
                }
                return Ok(result);
            }
            if items.len() - value_start != *length {
                return Err("static array initializer has the wrong length".into());
            }
            items[value_start..]
                .iter()
                .map(|value| {
                    constant_aggregate_words(
                        value,
                        element,
                        structs,
                        enums,
                        constants,
                        float_constants,
                        initializers,
                        evaluating_constants,
                        evaluating_float_constants,
                    )
                })
                .collect::<Result<Vec<_>, _>>()
                .map(|words| words.into_iter().flatten().collect())
        }
        Type::Tuple(fields) => {
            let Expr::List(items) = expression else {
                return Err("static tuple initializer must be a tuple constructor".into());
            };
            if !matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "tuple") {
                return Err("static tuple initializer must use tuple".into());
            }
            let value_start = if parse_type(items.get(1)).ok() == Some(ty.clone()) {
                2
            } else {
                1
            };
            if items.len() - value_start != fields.len() {
                return Err("static tuple initializer has the wrong length".into());
            }
            fields
                .iter()
                .zip(&items[value_start..])
                .map(|(field, value)| {
                    constant_aggregate_words(
                        value,
                        field,
                        structs,
                        enums,
                        constants,
                        float_constants,
                        initializers,
                        evaluating_constants,
                        evaluating_float_constants,
                    )
                })
                .collect::<Result<Vec<_>, _>>()
                .map(|words| words.into_iter().flatten().collect())
        }
        Type::Named(name) if structs.contains_key(name) => {
            let Expr::List(items) = expression else {
                return Err("static struct initializer must be a constructor".into());
            };
            if !matches!(items.first(), Some(Expr::Symbol(constructor)) if constructor == name) {
                return Err("static struct initializer has the wrong constructor".into());
            }
            let fields = &structs[name];
            if items.len() - 1 != fields.len() {
                return Err("static struct initializer has the wrong field count".into());
            }
            fields
                .iter()
                .zip(&items[1..])
                .map(|(field, value)| {
                    constant_aggregate_words(
                        value,
                        &field.ty,
                        structs,
                        enums,
                        constants,
                        float_constants,
                        initializers,
                        evaluating_constants,
                        evaluating_float_constants,
                    )
                })
                .collect::<Result<Vec<_>, _>>()
                .map(|words| words.into_iter().flatten().collect())
        }
        Type::Named(name) if enums.contains_key(name) => {
            let Expr::List(items) = expression else {
                return Err("static enum initializer must be a constructor".into());
            };
            let Some(Expr::Symbol(variant_name)) = items.first() else {
                return Err("static enum initializer must start with a variant".into());
            };
            let variants = &enums[name];
            let Some((_variant_index, variant)) = variants
                .iter()
                .enumerate()
                .find(|(_, variant)| variant.name == *variant_name)
            else {
                return Err(format!("unknown enum variant '{variant_name}'"));
            };
            if items.len() - 1 != variant.fields.len() {
                return Err("static enum initializer has the wrong payload count".into());
            }
            let payload_words = variants
                .iter()
                .map(|candidate| {
                    candidate
                        .fields
                        .iter()
                        .map(|field| storage_word_count(field, structs, enums))
                        .collect::<Result<Vec<_>, _>>()
                        .map(|words| words.into_iter().sum::<usize>())
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(0);
            let mut words = vec![variant.discriminant];
            for (field, value) in variant.fields.iter().zip(&items[1..]) {
                words.extend(constant_aggregate_words(
                    value,
                    field,
                    structs,
                    enums,
                    constants,
                    float_constants,
                    initializers,
                    evaluating_constants,
                    evaluating_float_constants,
                )?);
            }
            words.resize(payload_words + 1, 0);
            Ok(words)
        }
        _ => Ok(vec![scalar_word(expression)?]),
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
    loop_names: Vec<Option<String>>,
    pending_loop_label: Option<String>,
    loop_result_types: Vec<Option<Type>>,
    loop_indirect_results: Vec<bool>,
    return_label: String,
    return_pointer_slot: Option<usize>,
    aggregate_temp_base: Option<usize>,
    aggregate_temp_words: usize,
    aggregate_argument_regions: usize,
    aggregate_argument_cursor: usize,
    aggregate_projection_depth: usize,
    output: String,
}

impl FunctionContext {
    fn clone_operand(&self, expression: &Expr) -> Expr {
        let Expr::List(items) = expression else {
            return expression.clone();
        };
        if !matches!(items.first(), Some(Expr::Symbol(name)) if name == "clone") || items.len() != 2
        {
            return expression.clone();
        }
        let custom = self
            .expression_type(&items[1])
            .and_then(|ty| match ty {
                Type::Named(name) => Some(format!("{name}-clone")),
                _ => None,
            })
            .filter(|name| self.functions.contains_key(name));
        if let Some(function) = custom {
            Expr::List(vec![Expr::Symbol(function), items[1].clone()])
        } else {
            items[1].clone()
        }
    }

    fn statement(&mut self, statement: &Statement) -> Result<(), String> {
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                let ty = resolve_type(ty, &self.aliases)?;
                let clone_value;
                let value = if matches!(value, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "clone"))
                {
                    clone_value = self.clone_operand(value);
                    &clone_value
                } else {
                    value
                };
                if matches!(ty, Type::Unit | Type::Never) {
                    self.expression(value)?;
                } else if matches!(&ty, Type::Named(type_name)
                if self.structs.contains_key(type_name)
                    || self.enums.get(type_name).is_some_and(|variants| {
                        variants.iter().any(|variant| !variant.fields.is_empty())
                    }))
                {
                    let Type::Named(type_name) = &ty else {
                        unreachable!("named aggregate type matched above")
                    };
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
            Statement::Destructure {
                pattern, ty, value, ..
            } => {
                self.emit_destructure(pattern, ty, value)?;
            }
            Statement::Assign { name, value } => {
                let expected = self.local_types.get(name).cloned();
                if expected
                    .as_ref()
                    .is_some_and(|ty| matches!(ty, Type::Unit | Type::Never))
                {
                    self.expression(value)?;
                    return Ok(());
                }
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
                let Storage::Array {
                    base,
                    length,
                    element_words,
                } = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown array '{name}'"))?
                else {
                    return Err(format!("'{name}' is not an array"));
                };
                let base = *base;
                let length = *length;
                let element_words = *element_words;
                let element_type = match self.local_types.get(name).cloned() {
                    Some(Type::Array(element, _)) => *element,
                    _ => return Err(format!("'{name}' is not an array")),
                };
                let bounds_failure = self.label("bounds_failure");
                self.expression(index)?;
                self.output.push_str(&format!(
                    "    cmp rax, {length}\n    jae {bounds_failure}\n"
                ));
                if element_words == 0 {
                    self.expression(value)?;
                    self.output.push_str(&format!(
                        "    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n"
                    ));
                    return Ok(());
                }
                if element_words > VALUE_REGISTERS.len() {
                    let temp_base = self
                        .aggregate_temp_base
                        .ok_or_else(|| "no aggregate temporary is available".to_owned())?;
                    self.push_rax();
                    self.store_value_to_slots(
                        value,
                        &element_type,
                        &flat_slots(temp_base, element_words),
                    )?;
                    self.output.push_str("    pop rcx\n");
                    self.stack_depth -= 1;
                    self.output.push_str(&format!(
                        "    lea r11, [rbp-{}]\n    imul rcx, {}\n    shl rcx, 3\n    sub r11, rcx\n",
                        base * 8,
                        element_words
                    ));
                    for word in 0..element_words {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                            (temp_base + word) * 8,
                            word * 8
                        ));
                    }
                    self.output.push_str(&format!(
                        "    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n"
                    ));
                    return Ok(());
                }
                self.push_rax();
                if element_words > 1 {
                    self.push_value_words(value, &element_type, false)?;
                    for register in VALUE_REGISTERS[..element_words].iter().rev() {
                        self.output.push_str(&format!("    pop {register}\n"));
                        self.stack_depth -= 1;
                    }
                    self.output.push_str("    pop rcx\n");
                    self.stack_depth -= 1;
                    self.output.push_str(&format!(
                        "    lea r11, [rbp-{}]\n    imul rcx, {}\n    shl rcx, 3\n    sub r11, rcx\n",
                        base * 8,
                        element_words
                    ));
                    for (index, register) in VALUE_REGISTERS[..element_words].iter().enumerate() {
                        self.output.push_str(&format!(
                            "    mov QWORD PTR [r11-{}], {register}\n",
                            index * 8
                        ));
                    }
                    self.output.push_str(&format!(
                        "    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n"
                    ));
                    return Ok(());
                }
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
                    .map(|(_, slots)| slots.clone())
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
                if slot.len() == 1 {
                    self.store_scalar_at_slot(value, &field_type, slot[0])?;
                } else {
                    self.store_value_to_slots(value, &field_type, &slot)?;
                }
            }
            Statement::EnumPayloadAssign {
                name,
                variant,
                index,
                value,
            } => {
                let Storage::Enum {
                    discriminant,
                    payload,
                } = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown enum '{name}'"))?
                    .clone()
                else {
                    return Err(format!("'{name}' is not a payload enum"));
                };
                let enum_name = match self.local_types.get(name) {
                    Some(Type::Named(enum_name)) => enum_name.clone(),
                    _ => return Err(format!("'{name}' is not a payload enum")),
                };
                let variants = self
                    .enums
                    .get(&enum_name)
                    .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
                let variant_index = variants
                    .iter()
                    .position(|candidate| candidate.name == *variant)
                    .ok_or_else(|| format!("enum '{enum_name}' has no variant '{variant}'"))?;
                let variant_fields = &variants[variant_index].fields;
                let field_type = variant_fields.get(*index).cloned().ok_or_else(|| {
                    format!("variant '{variant}' has no payload field at index {index}")
                })?;
                let field_offset = variant_fields[..*index]
                    .iter()
                    .map(|field| storage_word_count(field, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                let field_words = storage_word_count(&field_type, &self.structs, &self.enums)?;
                let field_slots = payload
                    .get(field_offset..field_offset + field_words)
                    .ok_or_else(|| "enum payload exceeds native storage".to_owned())?;
                let inactive = self.label("inactive_enum_payload");
                let done = self.label("inactive_enum_payload_done");
                self.output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp-{}]\n    cmp rax, {}\n    jne {inactive}\n",
                    discriminant * 8,
                    variant_index
                ));
                self.store_value_to_slots(value, &field_type, field_slots)?;
                self.output
                    .push_str(&format!("    jmp {done}\n{inactive}:\n    ud2\n{done}:\n"));
            }
            Statement::TupleAssign { name, index, value } => {
                let Storage::Tuple(slots) = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown tuple local '{name}'"))?
                    .clone()
                else {
                    return Err(format!("'{name}' is not a tuple"));
                };
                let fields = match self.local_types.get(name).cloned() {
                    Some(Type::Tuple(fields)) => fields,
                    _ => return Err(format!("'{name}' is not a tuple")),
                };
                let field_type = fields
                    .get(*index)
                    .cloned()
                    .ok_or_else(|| format!("tuple field index {index} is out of bounds"))?;
                let field_offset = fields[..*index]
                    .iter()
                    .map(|field| storage_word_count(field, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                let field_words = storage_word_count(&field_type, &self.structs, &self.enums)?;
                let field_slots = slots
                    .get(field_offset..field_offset + field_words)
                    .ok_or_else(|| "native tuple has too many fields".to_owned())?;
                if field_words == 1 {
                    self.store_scalar_at_slot(value, &field_type, field_slots[0])?;
                } else {
                    self.store_value_to_slots(value, &field_type, field_slots)?;
                }
            }
            Statement::LetElse {
                pattern,
                ty,
                value,
                else_body,
            } => {
                let storage_words = storage_word_count(ty, &self.structs, &self.enums)?;
                let words = if storage_words > VALUE_REGISTERS.len() {
                    let base = self
                        .aggregate_temp_base
                        .ok_or_else(|| "no aggregate temporary is available".to_owned())?;
                    let slots = flat_slots(base, storage_words);
                    self.store_value_to_slots(value, ty, &slots)?;
                    for slot in slots.iter().rev() {
                        self.output
                            .push_str(&format!("    push QWORD PTR [rbp-{}]\n", slot * 8));
                        self.stack_depth += 1;
                    }
                    storage_words
                } else {
                    let words = value_word_count(ty, &self.structs, &self.enums)?;
                    self.push_value_words(value, ty, true)?;
                    words
                };
                let failure = self.label("let_else_failure");
                let done = self.label("let_else_done");
                let mut bindings = Vec::new();
                let enum_type = matches!(
                    ty,
                    Type::Named(name)
                        if self.enums.get(name).is_some_and(|variants| {
                            variants.iter().any(|variant| !variant.fields.is_empty())
                        })
                );
                let fieldless_enum_type = matches!(
                    ty,
                    Type::Named(name)
                        if self.enums.get(name).is_some_and(|variants| {
                            !variants.is_empty()
                                && variants.iter().all(|variant| variant.fields.is_empty())
                        })
                );
                if fieldless_enum_type {
                    self.emit_let_else_fieldless_enum_pattern(pattern, ty, &failure)?;
                } else if enum_type {
                    if matches!(
                        pattern,
                        Expr::List(items)
                            if items.len() >= 2
                                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or")
                    ) {
                        self.emit_let_else_enum_or_pattern(pattern, ty, &failure)?;
                    } else {
                        self.emit_let_else_enum_pattern(pattern, ty, &failure, &mut bindings)?;
                    }
                } else if is_scalar_pattern_type(ty) {
                    let low_operand = "QWORD PTR [rsp]";
                    let high_operand = if is_wide_integer(ty) {
                        Some("QWORD PTR [rsp+8]")
                    } else {
                        None
                    };
                    self.emit_scalar_pattern_at(pattern, ty, low_operand, high_operand, &failure)?;
                } else {
                    let constructor = match pattern {
                        Expr::List(items) => match items.first() {
                            Some(Expr::Symbol(name)) => name.as_str(),
                            _ => {
                                return Err("let-else pattern must start with a constructor".into())
                            }
                        },
                        Expr::Symbol(name) if name == "_" => "",
                        _ => return Err("let-else pattern must be a constructor".into()),
                    };
                    if !constructor.is_empty() {
                        self.emit_aggregate_pattern(
                            pattern,
                            constructor,
                            ty,
                            0,
                            &failure,
                            &mut bindings,
                        )?;
                    }
                }
                for (name, offset, binding_type) in bindings {
                    let slots = local_slots(&self.locals, &name)?;
                    let binding_words =
                        storage_word_count(&binding_type, &self.structs, &self.enums)?;
                    if slots.len() != binding_words {
                        return Err(format!(
                            "let-else binding '{name}' has inconsistent storage"
                        ));
                    }
                    let stack_offset = if enum_type { offset + 1 } else { offset };
                    for (index, slot) in slots.into_iter().enumerate() {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rsp+{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                            (stack_offset + index) * 8,
                            slot * 8
                        ));
                    }
                }
                self.output
                    .push_str(&format!("    add rsp, {}\n", words * 8));
                self.stack_depth -= words;
                self.output
                    .push_str(&format!("    jmp {done}\n{failure}:\n"));
                for statement in else_body {
                    self.statement(statement)?;
                }
                self.output.push_str(&format!("{done}:\n"));
            }
            Statement::Labeled { label, statement } => {
                let previous = self.pending_loop_label.replace(label.clone());
                let result = self.statement(statement);
                self.pending_loop_label = previous;
                result?
            }
            Statement::While { condition, body } => {
                let start = self.label("while");
                let end = self.label("endwhile");
                self.output.push_str(&format!("{start}:\n"));
                self.expression(condition)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {end}\n"));
                self.loop_labels.push((start.clone(), end.clone()));
                self.loop_names.push(self.pending_loop_label.take());
                self.loop_result_types.push(None);
                self.loop_indirect_results.push(false);
                for statement in body {
                    self.statement(statement)?;
                }
                self.loop_labels.pop();
                self.loop_names.pop();
                self.loop_result_types.pop();
                self.loop_indirect_results.pop();
                self.output.push_str(&format!("    jmp {start}\n{end}:\n"));
            }
            Statement::Loop { body } => {
                let start = self.label("loop");
                let end = self.label("endloop");
                self.output.push_str(&format!("{start}:\n"));
                self.loop_labels.push((start.clone(), end.clone()));
                self.loop_names.push(self.pending_loop_label.take());
                self.loop_result_types.push(None);
                self.loop_indirect_results.push(false);
                for statement in body {
                    self.statement(statement)?;
                }
                self.loop_labels.pop();
                self.loop_names.pop();
                self.loop_result_types.pop();
                self.loop_indirect_results.pop();
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
                self.loop_names.push(self.pending_loop_label.take());
                self.loop_result_types.push(None);
                self.loop_indirect_results.push(false);
                for statement in body {
                    self.statement(statement)?;
                }
                self.loop_labels.pop();
                self.loop_names.pop();
                self.loop_result_types.pop();
                self.loop_indirect_results.pop();
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
            Statement::BreakTo(label) => {
                let Some(index) = self
                    .loop_names
                    .iter()
                    .rposition(|name| name.as_deref() == Some(label))
                else {
                    return Err(format!("unknown or inactive loop label '{label}'"));
                };
                let end = self.loop_labels[index].1.clone();
                self.output.push_str(&format!("    jmp {end}\n"));
            }
            Statement::BreakToValue { label, value } => {
                let Some(index) = self
                    .loop_names
                    .iter()
                    .rposition(|name| name.as_deref() == Some(label))
                else {
                    return Err(format!("unknown or inactive loop label '{label}'"));
                };
                let end = self.loop_labels[index].1.clone();
                if self
                    .loop_indirect_results
                    .get(index)
                    .copied()
                    .unwrap_or(false)
                {
                    let ty = self
                        .loop_result_types
                        .get(index)
                        .and_then(Clone::clone)
                        .ok_or_else(|| "indirect labeled loop result has no type".to_owned())?;
                    self.store_indirect_value_words(value, &ty, 0)?;
                } else if let Some(Some(ty)) = self.loop_result_types.get(index).cloned() {
                    self.expression_as_expected(value, &ty)?;
                } else {
                    self.expression(value)?;
                }
                self.output.push_str(&format!("    jmp {end}\n"));
            }
            Statement::BreakValue(value) => {
                let Some((_, end)) = self.loop_labels.last().cloned() else {
                    return Err("break with a value used outside a loop".into());
                };
                if self.loop_indirect_results.last().copied().unwrap_or(false) {
                    let ty = self
                        .loop_result_types
                        .last()
                        .and_then(Clone::clone)
                        .ok_or_else(|| "indirect loop result has no type".to_owned())?;
                    self.store_indirect_value_words(value, &ty, 0)?;
                } else if let Some(Some(ty)) = self.loop_result_types.last().cloned() {
                    self.expression_as_expected(value, &ty)?;
                } else {
                    self.expression(value)?;
                }
                self.output.push_str(&format!("    jmp {end}\n"));
            }
            Statement::Continue => {
                let Some((start, _)) = self.loop_labels.last() else {
                    return Err("continue used outside a loop".into());
                };
                self.output.push_str(&format!("    jmp {start}\n"));
            }
            Statement::ContinueTo(label) => {
                let Some(index) = self
                    .loop_names
                    .iter()
                    .rposition(|name| name.as_deref() == Some(label))
                else {
                    return Err(format!("unknown or inactive loop label '{label}'"));
                };
                let start = self.loop_labels[index].0.clone();
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
                if let Some(Some(ty)) = self.loop_result_types.last().cloned() {
                    self.expression_as_expected(expression, &ty)?;
                } else if let Some(ty) = self
                    .expression_type(expression)
                    .filter(|ty| self.is_aggregate_type(ty))
                {
                    self.expression_as_expected(expression, &ty)?;
                } else if self.is_aggregate_type(&self.return_type) {
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

    fn emit_destructure(&mut self, pattern: &Expr, ty: &Type, value: &Expr) -> Result<(), String> {
        let storage_words = storage_word_count(ty, &self.structs, &self.enums)?;
        if storage_words > VALUE_REGISTERS.len() {
            let source_slots = if let Expr::Symbol(name) = value {
                Some(local_slots(&self.locals, name)?)
            } else if let Expr::List(items) = value {
                match items.first() {
                    Some(Expr::Symbol(function_name))
                        if self
                            .functions
                            .get(function_name)
                            .is_some_and(|function| function.indirect_return) =>
                    {
                        let base = self.call_to_aggregate_temp(function_name, &items[1..])?;
                        Some(flat_slots(base, storage_words))
                    }
                    _ => None,
                }
            } else {
                None
            };
            if let Some(source_slots) = source_slots {
                if source_slots.len() != storage_words {
                    return Err("large destructuring source has inconsistent storage".into());
                }
                return self.emit_destructure_pattern_from_slots(pattern, ty, 0, &source_slots);
            }
        }
        let words = value_word_count(ty, &self.structs, &self.enums)?;
        self.push_value_words(value, ty, false)?;
        for register in VALUE_REGISTERS[..words].iter().rev() {
            self.output.push_str(&format!("    pop {register}\n"));
            self.stack_depth -= 1;
        }
        self.emit_destructure_pattern(pattern, ty, 0)
    }

    fn emit_destructure_pattern_from_slots(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        offset: usize,
        source_slots: &[usize],
    ) -> Result<(), String> {
        let Expr::List(pattern_items) = pattern else {
            return Err("destructuring pattern must be a constructor list".into());
        };
        let Some(Expr::Symbol(constructor)) = pattern_items.first() else {
            return Err("destructuring pattern must start with a constructor".into());
        };
        let fields = self.aggregate_pattern_fields(ty, constructor)?;
        if pattern_items.len() - 1 != fields.len() {
            return Err("destructuring pattern has the wrong field count".into());
        }
        let mut field_offset = offset;
        for (binding, field_type) in pattern_items[1..].iter().zip(fields) {
            let field_words = storage_word_count(&field_type, &self.structs, &self.enums)?;
            match binding {
                Expr::Symbol(name) if name == "_" => {}
                Expr::Symbol(name) => {
                    let slots = local_slots(&self.locals, name)?;
                    if slots.len() != field_words {
                        return Err(
                            "destructuring binding has an inconsistent flattened layout".into()
                        );
                    }
                    for (index, slot) in slots.iter().enumerate() {
                        let source_slot = source_slots
                            .get(field_offset + index)
                            .ok_or_else(|| "destructuring source exceeds storage".to_owned())?;
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                            source_slot * 8,
                            slot * 8
                        ));
                    }
                }
                Expr::List(_) => self.emit_destructure_pattern_from_slots(
                    binding,
                    &field_type,
                    field_offset,
                    source_slots,
                )?,
                _ => return Err("destructuring fields must be bindings or nested patterns".into()),
            }
            field_offset += field_words;
        }
        Ok(())
    }

    fn emit_destructure_pattern(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        offset: usize,
    ) -> Result<(), String> {
        let Expr::List(pattern_items) = pattern else {
            return Err("destructuring pattern must be a constructor list".into());
        };
        let Some(Expr::Symbol(constructor)) = pattern_items.first() else {
            return Err("destructuring pattern must start with a constructor".into());
        };
        let fields = self.aggregate_pattern_fields(ty, constructor)?;
        if pattern_items.len() - 1 != fields.len() {
            return Err("destructuring pattern has the wrong field count".into());
        }
        let mut field_offset = offset;
        for (binding, field_type) in pattern_items[1..].iter().zip(fields) {
            let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
            match binding {
                Expr::Symbol(name) if name == "_" => {}
                Expr::Symbol(name) => {
                    let slots = local_slots(&self.locals, name)?;
                    if slots.len() != field_words {
                        return Err(
                            "destructuring binding has an inconsistent flattened layout".into()
                        );
                    }
                    for (index, slot) in slots.iter().enumerate() {
                        self.output.push_str(&format!(
                            "    mov QWORD PTR [rbp-{}], {}\n",
                            slot * 8,
                            VALUE_REGISTERS[field_offset + index]
                        ));
                    }
                }
                Expr::List(_) => {
                    self.emit_destructure_pattern(binding, &field_type, field_offset)?;
                }
                _ => return Err("destructuring fields must be bindings or nested patterns".into()),
            }
            field_offset += field_words;
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
        } else if self.is_aggregate_type(ty) {
            if let Expr::List(items) = value {
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                    return self.if_expression_as_aggregate(items, ty);
                }
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                    return self.match_expression(items, None, Some(ty));
                }
            }
            if let Expr::Block(statements) = value {
                return self.block_expression_as_expected(statements, ty);
            }
            if let Expr::Loop(body) = value {
                return self.loop_expression(body, Some(ty));
            }
            if let Expr::Labeled { label, expression } = value {
                let previous = self.pending_loop_label.replace(label.clone());
                let result = self.expression_as_expected(expression, ty);
                self.pending_loop_label = previous;
                return result;
            }
            let words = value_word_count(ty, &self.structs, &self.enums)?;
            if words > VALUE_REGISTERS.len() {
                return Err("native aggregate value has too many value words".into());
            }
            self.push_value_words(value, ty, false)?;
            for register in VALUE_REGISTERS[..words].iter().rev() {
                self.output.push_str(&format!("    pop {register}\n"));
                self.stack_depth -= 1;
            }
            Ok(())
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
        let fieldless_enum = matches!(&source, Type::Named(name)
        if self.enums.get(name).is_some_and(|variants| {
            variants.iter().all(|variant| variant.fields.is_empty())
        }));
        if fieldless_enum {
            self.expression(value)?;
            if is_wide_integer(target) {
                self.output.push_str("    xor edx, edx\n");
            } else {
                self.normalize_integer(target)?;
            }
            return Ok(());
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
            if is_unsigned_type(&source) {
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
            Expr::String(value) => Some(Type::Array(Box::new(Type::Char), value.chars().count())),
            Expr::Symbol(name) if name == "true" || name == "false" => Some(Type::Bool),
            Expr::Symbol(name) => self
                .local_types
                .get(name)
                .cloned()
                .or_else(|| self.global_types.get(name).cloned())
                .or_else(|| {
                    self.enums
                        .iter()
                        .find(|(_, variants)| variants.iter().any(|variant| variant.name == *name))
                        .map(|(enum_name, _)| Type::Named(enum_name.clone()))
                }),
            Expr::Block(statements) => statements.last().and_then(|statement| match statement {
                Statement::Expr(expression) | Statement::Return(Some(expression)) => {
                    self.expression_type(expression)
                }
                _ => Some(Type::Unit),
            }),
            Expr::List(items) => match items.first() {
                Some(Expr::Symbol(operator)) if operator == "clone" && items.len() == 2 => {
                    self.expression_type(&items[1])
                }
                Some(Expr::Symbol(operator)) if operator == "cell" && items.len() == 2 => self
                    .expression_type(&items[1])
                    .map(|inner| Type::Cell(Box::new(inner))),
                Some(Expr::Symbol(operator)) if operator == "cell-get" && items.len() == 2 => {
                    match self.expression_type(&items[1])? {
                        Type::Cell(inner) => Some(*inner),
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "cell-set" => Some(Type::Unit),
                Some(Expr::Symbol(operator)) if operator == "deref-set" => Some(Type::Unit),
                Some(Expr::Symbol(operator)) if operator == "get" && items.len() == 3 => {
                    let base = self.expression_type(&items[1])?;
                    let base = match base {
                        Type::Reference { target, .. } => *target,
                        other => other,
                    };
                    match (base, &items[2]) {
                        (Type::Tuple(fields), Expr::Integer(index)) if *index >= 0 => {
                            fields.get(usize::try_from(*index).ok()?).cloned()
                        }
                        (Type::Named(name), Expr::Symbol(field)) => self
                            .structs
                            .get(&name)?
                            .iter()
                            .find(|candidate| candidate.name == *field)
                            .map(|candidate| candidate.ty.clone()),
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "get-payload" && items.len() == 4 => {
                    let base = self.expression_type(&items[1])?;
                    let Type::Named(enum_name) = (match base {
                        Type::Reference { target, .. } => *target,
                        other => other,
                    }) else {
                        return None;
                    };
                    let Expr::Symbol(variant_name) = &items[2] else {
                        return None;
                    };
                    let index = match &items[3] {
                        Expr::Integer(index) if *index >= 0 => usize::try_from(*index).ok()?,
                        Expr::UnsignedInteger(index) => usize::try_from(*index).ok()?,
                        _ => return None,
                    };
                    self.enums
                        .get(&enum_name)?
                        .iter()
                        .find(|variant| variant.name == *variant_name)?
                        .fields
                        .get(index)
                        .cloned()
                }
                Some(Expr::Symbol(operator)) if operator == "as" && items.len() == 3 => {
                    parse_type(items.get(2))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, &self.aliases).ok())
                }
                Some(Expr::Symbol(operator)) if operator == "literal" && items.len() == 3 => {
                    parse_type(items.get(1))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, &self.aliases).ok())
                }
                Some(Expr::Symbol(operator))
                    if matches!(operator.as_str(), "borrow" | "borrow-mut") && items.len() == 2 =>
                {
                    let target = match items.get(1)? {
                        Expr::Symbol(name) => self
                            .local_types
                            .get(name)
                            .cloned()
                            .or_else(|| self.global_types.get(name).cloned())?,
                        Expr::List(place) if matches!(place.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "get" | "index" | "get-payload")) => {
                            self.expression_type(&items[1])?
                        }
                        _ => return None,
                    };
                    Some(Type::Reference {
                        mutable: operator == "borrow-mut",
                        target: Box::new(target),
                    })
                }
                Some(Expr::Symbol(operator)) if operator == "deref" && items.len() == 2 => {
                    match self.expression_type(&items[1])? {
                        Type::Reference { target, .. } => Some(*target),
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "unsafe" && items.len() == 2 => {
                    self.expression_type(&items[1])
                }
                Some(Expr::Symbol(operator))
                    if matches!(operator.as_str(), "addr-of" | "addr-of-mut")
                        && items.len() == 2 =>
                {
                    let owner = match items.get(1) {
                        Some(Expr::Symbol(name)) => name,
                        _ => return None,
                    };
                    self.local_types
                        .get(owner)
                        .cloned()
                        .or_else(|| self.global_types.get(owner).cloned())
                        .map(|target| Type::RawPointer {
                            mutable: operator == "addr-of-mut",
                            target: Box::new(target),
                        })
                }
                Some(Expr::Symbol(operator)) if operator == "ptr-read" && items.len() == 2 => {
                    match self.expression_type(&items[1])? {
                        Type::RawPointer { target, .. } => Some(*target),
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "ptr-write" => Some(Type::Unit),
                Some(Expr::Symbol(operator)) if operator == "if" => {
                    if items.len() == 4 {
                        self.expression_type(&items[2])
                            .or_else(|| self.expression_type(&items[3]))
                    } else {
                        Some(Type::Unit)
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "match" => items[2..]
                    .iter()
                    .find_map(|arm| match_arm_parts(arm).ok())
                    .and_then(|(_, _, body)| self.expression_type(body)),
                Some(Expr::Symbol(operator))
                    if matches!(
                        operator_base(operator.as_str()),
                        "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" | "!"
                    ) =>
                {
                    operator_parts(operator.as_str())
                        .0
                        .map(Type::from_name)
                        .or_else(|| items.get(1).and_then(|value| self.expression_type(value)))
                }
                Some(Expr::Symbol(operator))
                    if matches!(operator_base(operator.as_str()), "assert" | "debug-assert") =>
                {
                    Some(Type::Unit)
                }
                Some(Expr::Symbol(operator))
                    if matches!(operator_base(operator.as_str()), "size-of" | "align-of") =>
                {
                    Some(Type::Usize)
                }
                Some(Expr::Symbol(operator)) if operator == "index" && items.len() == 3 => {
                    match self.expression_type(&items[1])? {
                        Type::Array(element, _) => Some(*element),
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "array" && items.len() >= 2 => {
                    match parse_type(items.get(1))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, &self.aliases).ok())
                    {
                        Some(Type::Array(element, length)) if items.len() - 2 == length => {
                            Some(Type::Array(element, length))
                        }
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "array-repeat" && items.len() == 3 => {
                    match parse_type(items.get(1))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, &self.aliases).ok())
                    {
                        Some(Type::Array(element, length)) => Some(Type::Array(element, length)),
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) if operator == "get" && items.len() == 3 => match self
                    .expression_type(&items[1])?
                {
                    Type::Tuple(fields) => match &items[2] {
                        Expr::Integer(index) if *index >= 0 => fields.get(*index as usize).cloned(),
                        _ => None,
                    },
                    Type::Named(name) => match &items[2] {
                        Expr::Symbol(field_name) => self.structs.get(&name).and_then(|fields| {
                            fields
                                .iter()
                                .find(|field| field.name == *field_name)
                                .map(|field| field.ty.clone())
                        }),
                        _ => None,
                    },
                    _ => None,
                },
                Some(Expr::Symbol(operator)) if operator == "tuple" && items.len() >= 3 => {
                    match parse_type(items.get(1)).ok() {
                        Some(Type::Tuple(fields)) if items.len() - 2 == fields.len() => {
                            Some(Type::Tuple(fields))
                        }
                        _ => None,
                    }
                }
                Some(Expr::Symbol(operator)) => self
                    .structs
                    .get(operator)
                    .filter(|fields| items.len() - 1 == fields.len())
                    .map(|_| Type::Named(operator.clone()))
                    .or_else(|| {
                        self.enums
                            .iter()
                            .find(|(_, variants)| {
                                variants.iter().any(|variant| variant.name == *operator)
                            })
                            .map(|(name, _)| Type::Named(name.clone()))
                    })
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

    fn return_indirect_struct_value(
        &mut self,
        struct_name: &str,
        fields: &[Field],
        value: &Expr,
    ) -> Result<(), String> {
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "deref")
                && items.len() == 2
            {
                let ty = Type::Named(struct_name.to_owned());
                return self.store_indirect_value_words(value, &ty, 0);
            }
        }
        if fields.iter().any(|field| {
            storage_word_count(&field.ty, &self.structs, &self.enums).is_ok_and(|words| words > 1)
        }) {
            let ty = Type::Named(struct_name.to_owned());
            return self.store_indirect_value_words(value, &ty, 0);
        }
        let pointer_slot = self
            .return_pointer_slot
            .ok_or_else(|| "missing indirect return pointer".to_owned())?;
        let mut offset = 0usize;
        if let Expr::Symbol(name) = value {
            if let Some(Storage::Struct(source_fields)) = self.locals.get(name).cloned() {
                for ((_, source_slots), field) in source_fields.iter().zip(fields) {
                    let words = storage_word_count(&field.ty, &self.structs, &self.enums)?;
                    if words == 0 {
                        continue;
                    }
                    if source_slots.len() != words {
                        return Err("large struct returns currently require scalar fields".into());
                    }
                    for (index, source_slot) in source_slots.iter().enumerate() {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                            source_slot * 8,
                            pointer_slot * 8,
                            (offset + index) * 8
                        ));
                    }
                    offset += words;
                }
                return Ok(());
            }
            if matches!(
                self.global_types.get(name),
                Some(Type::Named(global_name)) if global_name == struct_name
            ) {
                for field in fields {
                    let words = storage_word_count(&field.ty, &self.structs, &self.enums)?;
                    if words == 0 {
                        continue;
                    }
                    if words != 1 {
                        return Err("large struct returns currently require scalar fields".into());
                    }
                    self.load_global_word(name, offset)?;
                    self.output.push_str(&format!(
                        "    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                        pointer_slot * 8,
                        offset * 8
                    ));
                    offset += words;
                }
                return Ok(());
            }
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == struct_name) {
                if items.len() - 1 != fields.len() {
                    return Err(format!("constructor '{struct_name}' has wrong field count"));
                }
                for (field_value, field) in items[1..].iter().zip(fields) {
                    let words = storage_word_count(&field.ty, &self.structs, &self.enums)?;
                    self.store_indirect_value_words(field_value, &field.ty, offset)?;
                    offset += words;
                }
                return Ok(());
            }
        }
        Err("large struct return requires a struct value or local".into())
    }

    fn return_indirect_enum_value(&mut self, enum_name: &str, value: &Expr) -> Result<(), String> {
        if self.enums.get(enum_name).is_some_and(|variants| {
            variants.iter().any(|variant| {
                variant.fields.iter().any(|field| {
                    storage_word_count(field, &self.structs, &self.enums)
                        .is_ok_and(|words| words > 1)
                })
            })
        }) {
            let ty = Type::Named(enum_name.to_owned());
            return self.store_indirect_value_words(value, &ty, 0);
        }
        let pointer_slot = self
            .return_pointer_slot
            .ok_or_else(|| "missing indirect return pointer".to_owned())?;
        let variants = self
            .enums
            .get(enum_name)
            .cloned()
            .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
        let storage_words = storage_word_count(
            &Type::Named(enum_name.to_owned()),
            &self.structs,
            &self.enums,
        )?;
        if let Expr::Symbol(name) = value {
            if let Some(Storage::Enum {
                discriminant,
                payload,
            }) = self.locals.get(name).cloned()
            {
                if payload.len() + 1 != storage_words {
                    return Err("enum return has an inconsistent flattened layout".into());
                }
                for (index, source_slot) in std::iter::once(discriminant).chain(payload).enumerate()
                {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                        source_slot * 8,
                        pointer_slot * 8,
                        index * 8
                    ));
                }
                return Ok(());
            }
            if matches!(
                self.global_types.get(name),
                Some(Type::Named(global_name)) if global_name == enum_name
            ) {
                for index in 0..storage_words {
                    self.load_global_word(name, index)?;
                    self.output.push_str(&format!(
                        "    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                        pointer_slot * 8,
                        index * 8
                    ));
                }
                return Ok(());
            }
        }
        let Expr::List(items) = value else {
            return Err("large enum return requires a constructor or local".into());
        };
        let Some(Expr::Symbol(variant_name)) = items.first() else {
            return Err("enum constructor must start with a variant name".into());
        };
        let variant_index = variants
            .iter()
            .position(|variant| variant.name == *variant_name)
            .ok_or_else(|| format!("unknown enum variant '{variant_name}'"))?;
        let variant = &variants[variant_index];
        if items.len() - 1 != variant.fields.len() {
            return Err(format!("variant '{variant_name}' has wrong payload count"));
        }
        self.output.push_str(&format!(
            "    mov rax, {}\n    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11], rax\n",
            variant.discriminant,
            pointer_slot * 8
        ));
        let mut offset = 1usize;
        for (field_value, field_type) in items[1..].iter().zip(&variant.fields) {
            let words = storage_word_count(field_type, &self.structs, &self.enums)?;
            self.store_indirect_value_words(field_value, field_type, offset)?;
            offset += words;
        }
        while offset < storage_words {
            self.output.push_str(&format!(
                "    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], 0\n",
                pointer_slot * 8,
                offset * 8
            ));
            offset += 1;
        }
        Ok(())
    }

    fn return_value(&mut self, value: &Expr) -> Result<(), String> {
        if matches!(self.return_type, Type::Unit) {
            return Ok(());
        }
        if self.return_pointer_slot.is_some()
            && self.is_aggregate_type(&self.return_type)
            && matches!(value, Expr::List(items) if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "get" || operator == "index"))
        {
            return self.return_indirect_projection(value);
        }
        if self.return_pointer_slot.is_some()
            && self.is_aggregate_type(&self.return_type)
            && matches!(&value, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if"))
        {
            let return_type = self.return_type.clone();
            return self.store_indirect_value_words(value, &return_type, 0);
        }
        if self.return_pointer_slot.is_some() && self.is_aggregate_type(&self.return_type) {
            let return_type = self.return_type.clone();
            match value {
                Expr::Loop(body) => return self.loop_expression_indirect(body, &return_type),
                Expr::Labeled { label, expression } => {
                    let Expr::Loop(body) = expression.as_ref() else {
                        unreachable!()
                    };
                    let previous = self.pending_loop_label.replace(label.clone());
                    let result = self.loop_expression_indirect(body, &return_type);
                    self.pending_loop_label = previous;
                    return result;
                }
                _ => {}
            }
        }
        if self.is_aggregate_type(&self.return_type)
            && matches!(
                value,
                Expr::List(items)
                    if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if" || operator == "match")
            )
        {
            let return_type = self.return_type.clone();
            return self.expression_as_expected(value, &return_type);
        }
        if self.is_aggregate_type(&self.return_type)
            && matches!(value, Expr::Loop(_) | Expr::Labeled { .. })
        {
            let return_type = self.return_type.clone();
            return self.expression_as_expected(value, &return_type);
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
            if self.return_pointer_slot.is_some() && self.enums.contains_key(struct_name) {
                let enum_name = struct_name.to_owned();
                return self.return_indirect_enum_value(&enum_name, value);
            }
            if self
                .enums
                .get(struct_name)
                .is_some_and(|variants| variants.iter().any(|variant| !variant.fields.is_empty()))
            {
                if let Expr::Symbol(name) = value {
                    if matches!(
                        self.global_types.get(name),
                        Some(Type::Named(global_name)) if global_name == struct_name
                    ) {
                        let words =
                            value_word_count(&self.return_type, &self.structs, &self.enums)?;
                        for index in (0..words).rev() {
                            let register = VALUE_REGISTERS[index];
                            self.load_global_word(name, index)?;
                            self.output.push_str(&format!("    mov {register}, rax\n"));
                        }
                        return Ok(());
                    }
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
        if self.return_pointer_slot.is_some() {
            let struct_name = struct_name.to_owned();
            return self.return_indirect_struct_value(&struct_name, &fields, value);
        }
        if let Expr::Symbol(name) = value {
            if matches!(self.global_types.get(name), Some(Type::Named(global_name)) if global_name == struct_name)
            {
                let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
                if words > VALUE_REGISTERS.len() {
                    return Err("native struct return has too many fields".into());
                }
                for index in (0..words).rev() {
                    let register = VALUE_REGISTERS[index];
                    self.load_global_word(name, index)?;
                    self.output.push_str(&format!("    mov {register}, rax\n"));
                }
                return Ok(());
            }
            let Storage::Struct(slots) = self
                .locals
                .get(name)
                .ok_or_else(|| format!("unknown struct local '{name}'"))?
            else {
                return Err(format!("'{name}' is not a struct"));
            };
            let slots = slots.clone();
            let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
            let flat = slots
                .iter()
                .flat_map(|(_, field_slots)| field_slots.iter().copied())
                .collect::<Vec<_>>();
            for (index, slot) in flat.iter().take(words).enumerate() {
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
                    self.push_value_words(field, &fields[index].ty, false)?;
                }
                let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
                for register in VALUE_REGISTERS[..words].iter().rev() {
                    self.output.push_str(&format!("    pop {register}\n"));
                    self.stack_depth -= 1;
                }
                return Ok(());
            }
        }
        self.expression(value)
    }

    fn return_indirect_projection(&mut self, value: &Expr) -> Result<(), String> {
        let pointer_slot = self
            .return_pointer_slot
            .ok_or_else(|| "missing indirect return pointer".to_owned())?;
        let words = storage_word_count(&self.return_type, &self.structs, &self.enums)?;
        let temp_base = self
            .aggregate_temp_base
            .ok_or_else(|| "no aggregate temporary is available".to_owned())?;
        self.store_value_to_slots(
            value,
            &self.return_type.clone(),
            &flat_slots(temp_base, words),
        )?;
        for index in 0..words {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rbp-{}]\n    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                (temp_base + index) * 8,
                pointer_slot * 8,
                index * 8
            ));
        }
        Ok(())
    }

    fn return_indirect_tuple_value(&mut self, fields: &[Type], value: &Expr) -> Result<(), String> {
        if fields.iter().any(|field| {
            storage_word_count(field, &self.structs, &self.enums).is_ok_and(|words| words > 1)
        }) {
            let ty = Type::Tuple(fields.to_vec());
            return self.store_indirect_value_words(value, &ty, 0);
        }
        let pointer_slot = self
            .return_pointer_slot
            .ok_or_else(|| "missing indirect return pointer".to_owned())?;
        let mut offset = 0usize;
        if let Expr::Symbol(name) = value {
            if let Some(Storage::Tuple(slots)) = self.locals.get(name).cloned() {
                if slots.len() != fields.len() {
                    return Err("tuple return has an inconsistent flattened layout".into());
                }
                let mut source_offset = 0;
                for field in fields {
                    let words = storage_word_count(field, &self.structs, &self.enums)?;
                    if words == 0 {
                        continue;
                    }
                    if words != 1 || slots.get(source_offset).is_none() {
                        return Err("large tuple returns currently require scalar fields".into());
                    }
                    let source_slot = slots[source_offset];
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                        source_slot * 8,
                        pointer_slot * 8,
                        offset * 8
                    ));
                    source_offset += words;
                    offset += words;
                }
                return Ok(());
            }
            if matches!(
                self.global_types.get(name),
                Some(Type::Tuple(global_fields)) if global_fields == fields
            ) {
                for field in fields {
                    let words = storage_word_count(field, &self.structs, &self.enums)?;
                    if words == 0 {
                        continue;
                    }
                    if words != 1 {
                        return Err("large tuple returns currently require scalar fields".into());
                    }
                    self.load_global_word(name, offset)?;
                    self.output.push_str(&format!(
                        "    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                        pointer_slot * 8,
                        offset * 8
                    ));
                    offset += words;
                }
                return Ok(());
            }
        }
        if let Expr::List(items) = value {
            let value_start = if parse_type(items.get(1))
                .ok()
                .is_some_and(|ty| matches!(ty, Type::Tuple(_)))
            {
                2
            } else {
                1
            };
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "tuple") {
                if items.len() - value_start != fields.len() {
                    return Err("tuple return has the wrong length".into());
                }
                for (field_value, field) in items[value_start..].iter().zip(fields) {
                    let words = storage_word_count(field, &self.structs, &self.enums)?;
                    self.store_indirect_value_words(field_value, field, offset)?;
                    offset += words;
                }
                return Ok(());
            }
        }
        Err("large tuple return requires a tuple value or local".into())
    }

    fn return_tuple_value(&mut self, fields: &[Type], value: &Expr) -> Result<(), String> {
        if self.return_pointer_slot.is_some() {
            return self.return_indirect_tuple_value(fields, value);
        }
        if let Expr::Symbol(name) = value {
            if matches!(self.global_types.get(name), Some(Type::Tuple(global_fields)) if global_fields == fields)
            {
                if fields.len() > VALUE_REGISTERS.len() {
                    return Err("native tuple return has too many fields".into());
                }
                let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
                for index in (0..words).rev() {
                    let register = VALUE_REGISTERS[index];
                    self.load_global_word(name, index)?;
                    self.output.push_str(&format!("    mov {register}, rax\n"));
                }
                return Ok(());
            }
            let Storage::Tuple(slots) = self
                .locals
                .get(name)
                .ok_or_else(|| format!("unknown tuple local '{name}'"))?
            else {
                return Err(format!("'{name}' is not a tuple"));
            };
            let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
            for (index, slot) in slots.iter().take(words).enumerate() {
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
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|ty| matches!(ty, Type::Tuple(_)))
                {
                    2
                } else {
                    1
                };
                if items.len() - value_start != fields.len() {
                    return Err("tuple return has the wrong length".into());
                }
                for (field, ty) in items[value_start..].iter().zip(fields) {
                    self.push_value_words(field, ty, false)?;
                }
                let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
                for register in VALUE_REGISTERS[..words].iter().rev() {
                    self.output.push_str(&format!("    pop {register}\n"));
                    self.stack_depth -= 1;
                }
                return Ok(());
            }
        }
        self.expression(value)
    }

    fn store_indirect_word(&mut self, register: &str, offset: usize) -> Result<(), String> {
        let pointer_slot = self
            .return_pointer_slot
            .ok_or_else(|| "missing indirect return pointer".to_owned())?;
        self.output.push_str(&format!(
            "    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], {register}\n",
            pointer_slot * 8,
            offset * 8
        ));
        Ok(())
    }

    fn store_indirect_value_words(
        &mut self,
        value: &Expr,
        ty: &Type,
        offset: usize,
    ) -> Result<(), String> {
        let words = storage_word_count(ty, &self.structs, &self.enums)?;
        if words == 0 {
            self.expression(value)?;
            return Ok(());
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                if items.len() != 4 {
                    return Err("aggregate if requires condition, then, and else values".into());
                }
                let else_label = self.label("indirect_aggregate_else");
                let done_label = self.label("indirect_aggregate_done");
                self.expression(&items[1])?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
                self.store_indirect_value_words(&items[2], ty, offset)?;
                self.output
                    .push_str(&format!("    jmp {done_label}\n{else_label}:\n"));
                self.store_indirect_value_words(&items[3], ty, offset)?;
                self.output.push_str(&format!("{done_label}:\n"));
                return Ok(());
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "deref")
                && items.len() == 2
            {
                self.expression(&items[1])?;
                self.output.push_str("    and rax, -2\n    mov rcx, rax\n");
                for index in 0..words {
                    self.output
                        .push_str(&format!("    mov rax, QWORD PTR [rcx+{}]\n", index * 8));
                    self.store_indirect_word("rax", offset + index)?;
                }
                return Ok(());
            }
        }
        if let Expr::Symbol(name) = value {
            if let Ok(source_slots) = local_slots(&self.locals, name) {
                if source_slots.len() == words {
                    for (index, source_slot) in source_slots.into_iter().enumerate() {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n",
                            source_slot * 8
                        ));
                        self.store_indirect_word("rax", offset + index)?;
                    }
                    return Ok(());
                }
            }
            if self.global_types.get(name) == Some(ty) {
                for index in 0..words {
                    self.load_global_word(name, index)?;
                    self.store_indirect_word("rax", offset + index)?;
                }
                return Ok(());
            }
        }
        if let (Expr::String(string), Type::Array(element, length)) = (value, ty) {
            if matches!(element.as_ref(), Type::Char) && string.chars().count() == *length {
                for (index, character) in string.chars().enumerate() {
                    self.output
                        .push_str(&format!("    mov rax, {}\n", character as u32));
                    self.store_indirect_word("rax", offset + index)?;
                }
                return Ok(());
            }
        }
        if let (Expr::Symbol(variant_name), Type::Named(enum_name)) = (value, ty) {
            if let Some(variants) = self.enums.get(enum_name) {
                if let Some(variant) = variants
                    .iter()
                    .find(|variant| variant.name == *variant_name)
                {
                    self.output
                        .push_str(&format!("    mov rax, {}\n", variant.discriminant));
                    self.store_indirect_word("rax", offset)?;
                    let storage_words = storage_word_count(ty, &self.structs, &self.enums)?;
                    for index in 1..storage_words {
                        self.output.push_str("    xor rax, rax\n");
                        self.store_indirect_word("rax", offset + index)?;
                    }
                    return Ok(());
                }
            }
        }
        if words <= VALUE_REGISTERS.len() {
            self.push_value_words(value, ty, false)?;
            for (index, register) in VALUE_REGISTERS[..words].iter().rev().enumerate() {
                self.output.push_str(&format!("    pop {register}\n"));
                self.stack_depth -= 1;
                self.store_indirect_word(register, offset + words - index - 1)?;
            }
            return Ok(());
        }
        let Expr::List(items) = value else {
            return Err("large aggregate return requires a value constructor or local".into());
        };
        let Some(Expr::Symbol(constructor)) = items.first() else {
            return Err("large aggregate return constructor must start with a symbol".into());
        };
        match ty {
            Type::Array(element, length) if constructor == "array" => {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|declared| declared == *ty)
                {
                    2
                } else {
                    1
                };
                if items.len() - value_start != *length {
                    return Err("large array return has the wrong length".into());
                }
                let element_words = storage_word_count(element, &self.structs, &self.enums)?;
                for (index, item) in items[value_start..].iter().enumerate() {
                    self.store_indirect_value_words(item, element, offset + index * element_words)?;
                }
                Ok(())
            }
            Type::Array(element, length) if constructor == "array-repeat" => {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|declared| declared == *ty)
                {
                    2
                } else {
                    1
                };
                if items.len() != value_start + 1 {
                    return Err("large array-repeat return requires one value".into());
                }
                let element_words = storage_word_count(element, &self.structs, &self.enums)?;
                for index in 0..*length {
                    self.store_indirect_value_words(
                        &items[value_start],
                        element,
                        offset + index * element_words,
                    )?;
                }
                Ok(())
            }
            Type::Tuple(fields) if constructor == "tuple" => {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|declared| declared == *ty)
                {
                    2
                } else {
                    1
                };
                if items.len() - value_start != fields.len() {
                    return Err("large tuple return has the wrong length".into());
                }
                let mut field_offset = offset;
                for (item, field) in items[value_start..].iter().zip(fields) {
                    self.store_indirect_value_words(item, field, field_offset)?;
                    field_offset += storage_word_count(field, &self.structs, &self.enums)?;
                }
                Ok(())
            }
            Type::Named(name) if self.structs.contains_key(name) && constructor == name => {
                let fields = self.structs.get(name).cloned().unwrap_or_default();
                if items.len() - 1 != fields.len() {
                    return Err(format!(
                        "large struct return '{name}' has the wrong field count"
                    ));
                }
                let mut field_offset = offset;
                for (item, field) in items[1..].iter().zip(&fields) {
                    self.store_indirect_value_words(item, &field.ty, field_offset)?;
                    field_offset += storage_word_count(&field.ty, &self.structs, &self.enums)?;
                }
                Ok(())
            }
            Type::Named(enum_name) if self.enums.contains_key(enum_name) => {
                let variants = self.enums.get(enum_name).cloned().unwrap_or_default();
                let variant_index = variants
                    .iter()
                    .position(|variant| variant.name == *constructor)
                    .ok_or_else(|| format!("unknown enum variant '{constructor}'"))?;
                let variant = &variants[variant_index];
                if items.len() - 1 != variant.fields.len() {
                    return Err(format!(
                        "enum variant '{constructor}' has the wrong payload count"
                    ));
                }
                self.output
                    .push_str(&format!("    mov rax, {}\n", variant.discriminant));
                self.store_indirect_word("rax", offset)?;
                let mut field_offset = offset + 1;
                for (item, field) in items[1..].iter().zip(&variant.fields) {
                    self.store_indirect_value_words(item, field, field_offset)?;
                    field_offset += storage_word_count(field, &self.structs, &self.enums)?;
                }
                let total_words = storage_word_count(ty, &self.structs, &self.enums)?;
                for index in field_offset..offset + total_words {
                    self.output.push_str("    xor rax, rax\n");
                    self.store_indirect_word("rax", index)?;
                }
                Ok(())
            }
            _ => Err("large aggregate return constructor has the wrong type".into()),
        }
    }

    fn return_indirect_array_value(&mut self, length: usize, value: &Expr) -> Result<(), String> {
        let Type::Array(element, _) = self.return_type.clone() else {
            return Err("indirect return target is not an array".into());
        };
        let element_words = storage_word_count(&element, &self.structs, &self.enums)?;
        let pointer_slot = self
            .return_pointer_slot
            .ok_or_else(|| "missing indirect return pointer".to_owned())?;
        if let Expr::Symbol(name) = value {
            if let Some(Storage::Array {
                base,
                length: source_length,
                element_words: source_element_words,
            }) = self.locals.get(name).cloned()
            {
                if source_length != length || source_element_words != element_words {
                    return Err("array return length mismatch".into());
                }
                for index in 0..length * element_words {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                        (base + index) * 8,
                        pointer_slot * 8,
                        index * 8
                    ));
                }
                return Ok(());
            }
            if matches!(
                self.global_types.get(name),
                Some(Type::Array(_, global_length)) if *global_length == length
            ) {
                for index in 0..length * element_words {
                    self.load_global_word(name, index)?;
                    self.output.push_str(&format!(
                        "    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], rax\n",
                        pointer_slot * 8,
                        index * 8
                    ));
                }
                return Ok(());
            }
        }
        if let Expr::String(string) = value {
            let characters = string.chars().collect::<Vec<_>>();
            if characters.len() != length || !matches!(*element, Type::Char) {
                return Err("string length does not match array return type".into());
            }
            for (index, character) in characters.into_iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov r11, QWORD PTR [rbp-{}]\n    mov QWORD PTR [r11-{}], {}\n",
                    pointer_slot * 8,
                    index * 8,
                    character as u32
                ));
            }
            return Ok(());
        }
        if let Expr::List(items) = value {
            let value_start = if parse_type(items.get(1))
                .ok()
                .is_some_and(|ty| matches!(ty, Type::Array(_, _)))
            {
                2
            } else {
                1
            };
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array-repeat") {
                if items.len() != value_start + 1 {
                    return Err("array-repeat requires one value".into());
                }
                for index in 0..length {
                    self.store_indirect_value_words(
                        &items[value_start],
                        &element,
                        index * element_words,
                    )?;
                }
                return Ok(());
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
                if items.len() - value_start != length {
                    return Err("array return has the wrong length".into());
                }
                for (index, item) in items[value_start..].iter().enumerate() {
                    self.store_indirect_value_words(item, &element, index * element_words)?;
                }
                return Ok(());
            }
        }
        Err("large array return requires an array value or local".into())
    }

    fn return_array_value(&mut self, length: usize, value: &Expr) -> Result<(), String> {
        if self.return_pointer_slot.is_some() {
            return self.return_indirect_array_value(length, value);
        }
        if let Expr::Symbol(name) = value {
            if matches!(
                self.global_types.get(name),
                Some(Type::Array(_, global_length)) if *global_length == length
            ) {
                let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
                if words > VALUE_REGISTERS.len() {
                    return Err("native array return has too many value words".into());
                }
                for index in (0..words).rev() {
                    let register = VALUE_REGISTERS[index];
                    self.load_global_word(name, index)?;
                    self.output.push_str(&format!("    mov {register}, rax\n"));
                }
                return Ok(());
            }
            let Storage::Array {
                base,
                length: local_length,
                element_words: _,
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
            let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
            if words > VALUE_REGISTERS.len() {
                return Err("native array return has too many value words".into());
            }
            let base = *base;
            for (index, register) in VALUE_REGISTERS[..words].iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [rbp-{}]\n",
                    (base + index) * 8
                ));
            }
            return Ok(());
        }
        if let Expr::String(string) = value {
            let characters = string.chars().collect::<Vec<_>>();
            if characters.len() != length {
                return Err("string length does not match array return type".into());
            }
            for character in characters {
                self.expression_as_abi_word(&Expr::Char(character), &Type::Char)?;
                self.push_rax();
            }
            let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
            for register in VALUE_REGISTERS[..words].iter().rev() {
                self.output.push_str(&format!("    pop {register}\n"));
                self.stack_depth -= 1;
            }
            return Ok(());
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array-repeat") {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|ty| matches!(ty, Type::Array(_, _)))
                {
                    2
                } else {
                    1
                };
                if items.len() != value_start + 1 {
                    return Err("array-repeat requires one value".into());
                }
                let Type::Array(element, _) = self.return_type.clone() else {
                    unreachable!()
                };
                for _ in 0..length {
                    self.push_value_words(&items[value_start], &element, false)?;
                }
                let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
                for register in VALUE_REGISTERS[..words].iter().rev() {
                    self.output.push_str(&format!("    pop {register}\n"));
                    self.stack_depth -= 1;
                }
                return Ok(());
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|ty| matches!(ty, Type::Array(_, _)))
                {
                    2
                } else {
                    1
                };
                if items.len() - value_start != length {
                    return Err("array return has the wrong length".into());
                }
                let Type::Array(element, _) = self.return_type.clone() else {
                    unreachable!()
                };
                for value in &items[value_start..] {
                    self.push_value_words(value, &element, false)?;
                }
                let words = value_word_count(&self.return_type, &self.structs, &self.enums)?;
                for register in VALUE_REGISTERS[..words].iter().rev() {
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
        let fields = self
            .structs
            .get(struct_name)
            .ok_or_else(|| format!("unknown struct '{struct_name}'"))?
            .clone();
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                if items.len() != 4 {
                    return Err(
                        "if requires a condition, then expression, and else expression".into(),
                    );
                }
                let else_label = self.label("large_struct_if_else");
                let done_label = self.label("large_struct_if_done");
                self.expression(&items[1])?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
                self.store_struct(name, struct_name, &items[2])?;
                self.output
                    .push_str(&format!("    jmp {done_label}\n{else_label}:\n"));
                self.store_struct(name, struct_name, &items[3])?;
                self.output.push_str(&format!("{done_label}:\n"));
                return Ok(());
            }
        }
        if let Expr::List(items) = value {
            if let Some(Expr::Symbol(function_name)) = items.first() {
                if self
                    .functions
                    .get(function_name)
                    .is_some_and(|function| function.indirect_return)
                {
                    let base = slots
                        .iter()
                        .flat_map(|(_, field_slots)| field_slots.iter())
                        .next()
                        .copied()
                        .ok_or_else(|| "struct has no storage fields".to_owned())?;
                    self.call(function_name, &items[1..], Some(base))?;
                    return Ok(());
                }
            }
        }
        if let Expr::List(items) = value {
            let Some(Expr::Symbol(constructor)) = items.first() else {
                return Err("struct constructor must start with a symbol".into());
            };
            if constructor == struct_name {
                if items.len() - 1 != fields.len() {
                    return Err(format!("constructor '{struct_name}' has wrong field count"));
                }
                for (index, (field, field_value)) in fields.iter().zip(&items[1..]).enumerate() {
                    self.store_value_to_slots(field_value, &field.ty, &slots[index].1)?;
                }
                return Ok(());
            }
        }
        if let Expr::Symbol(source) = value {
            if let Some(Storage::Struct(source_fields)) = self.locals.get(source).cloned() {
                let source_slots = source_fields
                    .iter()
                    .flat_map(|(_, field_slots)| field_slots.iter().copied())
                    .collect::<Vec<_>>();
                let destination_slots = slots
                    .iter()
                    .flat_map(|(_, field_slots)| field_slots.iter().copied())
                    .collect::<Vec<_>>();
                if source_slots.len() != destination_slots.len() {
                    return Err("struct assignment has an inconsistent flattened layout".into());
                }
                for (source_slot, destination_slot) in source_slots.iter().zip(destination_slots) {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        source_slot * 8,
                        destination_slot * 8
                    ));
                }
                return Ok(());
            }
        }
        let ty = Type::Named(struct_name.to_owned());
        let flat = slots
            .iter()
            .flat_map(|(_, field_slots)| field_slots.iter().copied())
            .collect::<Vec<_>>();
        self.store_value_words(value, &ty, &flat)
    }

    fn store_enum(&mut self, name: &str, enum_name: &str, value: &Expr) -> Result<(), String> {
        let Some(Storage::Enum {
            discriminant,
            payload,
        }) = self.locals.get(name).cloned()
        else {
            return Err(format!("'{name}' is not a payload enum"));
        };
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                if items.len() != 4 {
                    return Err(
                        "if requires a condition, then expression, and else expression".into(),
                    );
                }
                let else_label = self.label("large_enum_if_else");
                let done_label = self.label("large_enum_if_done");
                self.expression(&items[1])?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
                self.store_enum(name, enum_name, &items[2])?;
                self.output
                    .push_str(&format!("    jmp {done_label}\n{else_label}:\n"));
                self.store_enum(name, enum_name, &items[3])?;
                self.output.push_str(&format!("{done_label}:\n"));
                return Ok(());
            }
        }
        if let Expr::List(items) = value {
            if let Some(Expr::Symbol(function_name)) = items.first() {
                if self
                    .functions
                    .get(function_name)
                    .is_some_and(|function| function.indirect_return)
                {
                    self.call(function_name, &items[1..], Some(discriminant))?;
                    return Ok(());
                }
            }
        }
        if let Expr::Symbol(source) = value {
            if matches!(
                self.global_types.get(source),
                Some(Type::Named(global_name)) if global_name == enum_name
            ) {
                let words = 1 + payload.len();
                for (index, slot) in std::iter::once(discriminant)
                    .chain(payload.iter().copied())
                    .enumerate()
                {
                    if index >= words {
                        break;
                    }
                    self.load_global_word(source, index)?;
                    self.output
                        .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
                }
                return Ok(());
            }
            if let Some(Storage::Enum {
                discriminant: source_discriminant,
                payload: source_payload,
            }) = self.locals.get(source).cloned()
            {
                if source_payload.len() != payload.len() {
                    return Err("enum assignment has an inconsistent storage layout".into());
                }
                for (source_slot, destination_slot) in std::iter::once(source_discriminant)
                    .chain(source_payload)
                    .zip(std::iter::once(discriminant).chain(payload.iter().copied()))
                {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        source_slot * 8,
                        destination_slot * 8
                    ));
                }
                return Ok(());
            }
        }
        if let Expr::Symbol(variant_name) = value {
            if let Some(variant) = self.enums.get(enum_name).and_then(|variants| {
                variants
                    .iter()
                    .find(|variant| variant.name == *variant_name)
            }) {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {}\n",
                    discriminant * 8,
                    variant.discriminant
                ));
                for slot in &payload {
                    self.output
                        .push_str(&format!("    mov QWORD PTR [rbp-{}], 0\n", slot * 8));
                }
                return Ok(());
            }
        }
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
            variants[variant_index].discriminant
        ));
        let mut offset = 0;
        for (index, field_type) in variant.fields.iter().enumerate() {
            let field_words = storage_word_count(field_type, &self.structs, &self.enums)?;
            let field_slots = payload
                .get(offset..offset + field_words)
                .ok_or_else(|| "enum payload exceeds native storage".to_owned())?;
            self.store_value_to_slots(&items[index + 1], field_type, field_slots)?;
            offset += field_words;
        }
        for slot in payload.iter().skip(offset) {
            self.output
                .push_str(&format!("    mov QWORD PTR [rbp-{}], 0\n", slot * 8));
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
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                if items.len() != 4 {
                    return Err(
                        "if requires a condition, then expression, and else expression".into(),
                    );
                }
                let else_label = self.label("large_tuple_if_else");
                let done_label = self.label("large_tuple_if_done");
                self.expression(&items[1])?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
                self.store_tuple(name, &items[2])?;
                self.output
                    .push_str(&format!("    jmp {done_label}\n{else_label}:\n"));
                self.store_tuple(name, &items[3])?;
                self.output.push_str(&format!("{done_label}:\n"));
                return Ok(());
            }
        }
        if let Expr::List(items) = value {
            if let Some(Expr::Symbol(function_name)) = items.first() {
                if self
                    .functions
                    .get(function_name)
                    .is_some_and(|function| function.indirect_return)
                {
                    let base = *slots
                        .first()
                        .ok_or_else(|| "tuple has no storage slots".to_owned())?;
                    self.call(function_name, &items[1..], Some(base))?;
                    return Ok(());
                }
            }
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "tuple") {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|ty| matches!(ty, Type::Tuple(_)))
                {
                    2
                } else {
                    1
                };
                if items.len() - value_start != fields.len() {
                    return Err("tuple constructor has the wrong length".into());
                }
                let mut offset = 0;
                for (field, ty) in items[value_start..].iter().zip(&fields) {
                    let words = storage_word_count(ty, &self.structs, &self.enums)?;
                    self.store_value_to_slots(field, ty, &slots[offset..offset + words])?;
                    offset += words;
                }
                return Ok(());
            }
        }
        if let Expr::Symbol(source) = value {
            if let Some(Storage::Tuple(source_slots)) = self.locals.get(source).cloned() {
                if source_slots.len() != slots.len() {
                    return Err("tuple assignment has an inconsistent flattened layout".into());
                }
                for (source_slot, destination_slot) in source_slots.iter().zip(&slots) {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        source_slot * 8,
                        destination_slot * 8
                    ));
                }
                return Ok(());
            }
        }
        let ty = Type::Tuple(fields);
        self.store_value_words(value, &ty, &slots)
    }

    fn store_value_words(
        &mut self,
        value: &Expr,
        ty: &Type,
        slots: &[usize],
    ) -> Result<(), String> {
        let words = value_word_count(ty, &self.structs, &self.enums)?;
        if slots.len() != words {
            return Err("aggregate local has an inconsistent flattened layout".into());
        }
        self.push_value_words(value, ty, false)?;
        for (slot, register) in slots
            .iter()
            .rev()
            .zip(VALUE_REGISTERS[..words].iter().rev())
        {
            self.output.push_str(&format!(
                "    pop {register}\n    mov QWORD PTR [rbp-{}], {register}\n",
                slot * 8
            ));
            self.stack_depth -= 1;
        }
        Ok(())
    }

    fn store_array(&mut self, name: &str, value: &Expr) -> Result<(), String> {
        let Storage::Array {
            base,
            length,
            element_words,
        } = self
            .locals
            .get(name)
            .ok_or_else(|| format!("unknown array '{name}'"))?
        else {
            return Err(format!("'{name}' is not an array"));
        };
        let (base, length, element_words) = (*base, *length, *element_words);
        let array_type = self
            .local_types
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown array local '{name}'"))?;
        let Type::Array(element_type, declared_length) = &array_type else {
            return Err(format!("'{name}' is not an array"));
        };
        if *declared_length != length {
            return Err("array local length metadata is inconsistent".into());
        }
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                if items.len() != 4 {
                    return Err(
                        "if requires a condition, then expression, and else expression".into(),
                    );
                }
                let else_label = self.label("large_array_if_else");
                let done_label = self.label("large_array_if_done");
                self.expression(&items[1])?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
                self.store_array(name, &items[2])?;
                self.output
                    .push_str(&format!("    jmp {done_label}\n{else_label}:\n"));
                self.store_array(name, &items[3])?;
                self.output.push_str(&format!("{done_label}:\n"));
                return Ok(());
            }
        }
        if let Expr::List(items) = value {
            if let Some(Expr::Symbol(function_name)) = items.first() {
                if self
                    .functions
                    .get(function_name)
                    .is_some_and(|function| function.indirect_return)
                {
                    self.call(function_name, &items[1..], Some(base))?;
                    return Ok(());
                }
            }
        }
        let slots = flat_slots(base, length * element_words);
        if length.saturating_mul(element_words) > VALUE_REGISTERS.len()
            && (self.store_oversized_index_to_slots(value, &array_type, &slots)?
                || self.store_oversized_field_to_slots(value, &array_type, &slots)?)
        {
            return Ok(());
        }
        if let Expr::String(string) = value {
            let characters = string.chars().collect::<Vec<_>>();
            if characters.len() != length || element_words != 1 {
                return Err("string length does not match array local".into());
            }
            for (index, character) in characters.into_iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {}\n",
                    (base + index * element_words) * 8,
                    character as u32
                ));
            }
            return Ok(());
        }
        if let Expr::List(items) = value {
            let value_start = if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array" || operator == "array-repeat")
                && parse_type(items.get(1))
                    .ok()
                    .is_some_and(|ty| matches!(ty, Type::Array(_, _)))
            {
                2
            } else {
                1
            };
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array-repeat") {
                if items.len() != value_start + 1 {
                    return Err("array-repeat requires one value".into());
                }
                for index in 0..length {
                    let start = base + index * element_words;
                    self.store_value_to_slots(
                        &items[value_start],
                        element_type,
                        &flat_slots(start, element_words),
                    )?;
                }
                return Ok(());
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
                if items.len() - value_start != length {
                    return Err("array constructor has the wrong length".into());
                }
                for (index, value) in items[value_start..].iter().enumerate() {
                    let start = base + index * element_words;
                    self.store_value_to_slots(
                        value,
                        element_type,
                        &flat_slots(start, element_words),
                    )?;
                }
                return Ok(());
            }
        }
        if let Expr::Symbol(source) = value {
            if let Some(Storage::Array {
                base: source_base,
                length: source_length,
                element_words: source_element_words,
            }) = self.locals.get(source).cloned()
            {
                if source_length != length || source_element_words != element_words {
                    return Err("array assignment has an inconsistent flattened layout".into());
                }
                for offset in 0..length * element_words {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        (source_base + offset) * 8,
                        (base + offset) * 8
                    ));
                }
                return Ok(());
            }
        }
        self.store_value_to_slots(value, &array_type, &slots)
    }

    fn loop_expression(
        &mut self,
        body: &[Statement],
        result_type: Option<&Type>,
    ) -> Result<(), String> {
        let start = self.label("value_loop");
        let end = self.label("end_value_loop");
        self.output.push_str(&format!("{start}:\n"));
        self.loop_labels.push((start.clone(), end.clone()));
        self.loop_names.push(self.pending_loop_label.take());
        self.loop_result_types.push(result_type.cloned());
        self.loop_indirect_results.push(false);
        for statement in body {
            self.statement(statement)?;
        }
        self.loop_labels.pop();
        self.loop_names.pop();
        self.loop_result_types.pop();
        self.loop_indirect_results.pop();
        self.output.push_str(&format!("    jmp {start}\n{end}:\n"));
        Ok(())
    }

    fn loop_expression_indirect(
        &mut self,
        body: &[Statement],
        result_type: &Type,
    ) -> Result<(), String> {
        let start = self.label("indirect_value_loop");
        let end = self.label("end_indirect_value_loop");
        self.output.push_str(&format!("{start}:\n"));
        self.loop_labels.push((start.clone(), end.clone()));
        self.loop_names.push(self.pending_loop_label.take());
        self.loop_result_types.push(Some(result_type.clone()));
        self.loop_indirect_results.push(true);
        for statement in body {
            self.statement(statement)?;
        }
        self.loop_labels.pop();
        self.loop_names.pop();
        self.loop_result_types.pop();
        self.loop_indirect_results.pop();
        self.output.push_str(&format!("    jmp {start}\n{end}:\n"));
        Ok(())
    }

    fn expression(&mut self, expression: &Expr) -> Result<(), String> {
        match expression {
            Expr::Integer(value) => {
                if *value < i64::MIN as i128 || *value > i64::MAX as i128 {
                    self.output.push_str(&format!(
                        "    mov rax, 0x{:016x}\n    mov rdx, 0x{:016x}\n",
                        *value as u64,
                        (*value as u128 >> 64) as u64,
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
            Expr::Loop(statements) => self.loop_expression(statements, None)?,
            Expr::Labeled { label, expression } => {
                let previous = self.pending_loop_label.replace(label.clone());
                let result = self.expression(expression);
                self.pending_loop_label = previous;
                result?;
            }
            Expr::Symbol(name) if name == "true" => self.output.push_str("    mov eax, 1\n"),
            Expr::Symbol(name) if name == "false" => self.output.push_str("    xor eax, eax\n"),
            Expr::Symbol(name) if self.enum_value(name).is_some() => {
                self.output.push_str(&format!(
                    "    mov rax, {}\n",
                    asm_u64_immediate(self.enum_value(name).unwrap())
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
                    if payload_count + 1 > VALUE_REGISTERS.len() {
                        return Err(
                            "large payload enum values must be stored in local aggregate storage"
                                .into(),
                        );
                    }
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
                if self
                    .local_types
                    .get(name)
                    .is_some_and(|ty| matches!(ty, Type::Unit | Type::Never))
                {
                    return Ok(());
                }
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
                        Some(Type::Unit | Type::Never) => {}
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
            Expr::String(value) => {
                let characters = value.chars().collect::<Vec<_>>();
                if characters.len() > VALUE_REGISTERS.len() {
                    return Err("native string expression has too many value words".into());
                }
                for (register, character) in VALUE_REGISTERS.iter().zip(characters) {
                    self.output
                        .push_str(&format!("    mov {register}, {}\n", character as u32));
                }
            }
            Expr::At => return Err("@ is not an executable expression".into()),
            Expr::Quote(_) | Expr::QuasiQuote(_) | Expr::Unquote(_) | Expr::UnquoteSplicing(_) => {
                return Err("quoted expressions are not executable".into())
            }
        }
        Ok(())
    }

    fn borrow_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if let Some(Expr::List(place)) = items.get(1) {
            if matches!(place.first(), Some(Expr::Symbol(name)) if name == "get-payload")
                && place.len() == 4
            {
                let base_type = self.expression_type(&place[1]).ok_or_else(|| {
                    "cannot determine reference type for enum payload borrow".to_owned()
                })?;
                let Type::Reference { target, .. } = base_type else {
                    return Err("enum payload borrow requires a reference".into());
                };
                let Type::Named(enum_name) = *target else {
                    return Err("enum payload borrow requires a reference to an enum".into());
                };
                let Expr::Symbol(variant_name) = &place[2] else {
                    return Err("enum payload borrow requires a variant name".into());
                };
                let index = match &place[3] {
                    Expr::Integer(index) if *index >= 0 => usize::try_from(*index)
                        .map_err(|_| "enum payload index is too large".to_owned())?,
                    Expr::UnsignedInteger(index) => usize::try_from(*index)
                        .map_err(|_| "enum payload index is too large".to_owned())?,
                    _ => return Err("enum payload borrow requires a non-negative index".into()),
                };
                let variant = self
                    .enums
                    .get(&enum_name)
                    .ok_or_else(|| format!("unknown enum '{enum_name}'"))?
                    .iter()
                    .find(|variant| variant.name == *variant_name)
                    .cloned()
                    .ok_or_else(|| format!("unknown enum variant '{variant_name}'"))?;
                let _field_type = variant.fields.get(index).ok_or_else(|| {
                    format!("variant '{variant_name}' has no payload field at index {index}")
                })?;
                let payload_offset = 1 + variant.fields[..index]
                    .iter()
                    .map(|field| storage_word_count(field, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                let inactive = self.label("inactive_enum_payload_borrow");
                let done = self.label("inactive_enum_payload_borrow_done");
                self.expression(&place[1])?;
                self.output.push_str(&format!(
                    "    and rax, -2\n    mov rcx, QWORD PTR [rax]\n    cmp rcx, {}\n    jne {inactive}\n",
                    variant.discriminant
                ));
                self.emit_reference_field_address(&place[1], payload_offset, true)?;
                self.output
                    .push_str(&format!("    jmp {done}\n{inactive}:\n    ud2\n{done}:\n"));
                return Ok(());
            }
            if matches!(place.first(), Some(Expr::Symbol(name)) if name == "get")
                && place.len() == 3
            {
                let base_type = self
                    .expression_type(&place[1])
                    .ok_or_else(|| "cannot determine reference type for field borrow".to_owned())?;
                let Type::Reference { target, .. } = base_type else {
                    return Err("field borrow requires a reference to a struct".into());
                };
                let Type::Named(struct_name) = *target else {
                    return Err("field borrow requires a reference to a struct".into());
                };
                let field_name = match &place[2] {
                    Expr::Symbol(name) => name,
                    _ => return Err("field borrow requires a named struct field".into()),
                };
                let fields = self
                    .structs
                    .get(&struct_name)
                    .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
                let index = fields
                    .iter()
                    .position(|field| field.name == *field_name)
                    .ok_or_else(|| format!("struct '{struct_name}' has no field '{field_name}'"))?;
                let offset_words = fields[..index]
                    .iter()
                    .map(|field| storage_word_count(&field.ty, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                self.emit_reference_field_address(&place[1], offset_words, true)?;
                return Ok(());
            }
        }
        let owner = match items.get(1) {
            Some(Expr::Symbol(name)) => name,
            _ => return Err("borrow requires a variable or struct field place".into()),
        };
        if self.locals.contains_key(owner) {
            let slot = local_slots(&self.locals, owner)?
                .first()
                .copied()
                .ok_or_else(|| format!("cannot borrow zero-sized variable '{owner}'"))?;
            self.output
                .push_str(&format!("    lea rax, [rbp-{}]\n", slot * 8));
            if matches!(items.first(), Some(Expr::Symbol(operator)) if matches!(operator.as_str(), "borrow" | "borrow-mut"))
                && self.local_types.get(owner).is_some_and(
                    |ty| matches!(ty, Type::Named(name) if self.structs.contains_key(name)),
                )
            {
                self.output.push_str("    or rax, 1\n");
            }
            return Ok(());
        }
        if self.globals.contains_key(owner) {
            self.output
                .push_str(&format!("    lea rax, [rip+{}]\n", asm_symbol(owner)));
            return Ok(());
        }
        Err(format!("unknown variable '{owner}'"))
    }

    fn emit_reference_field_address(
        &mut self,
        reference: &Expr,
        offset_words: usize,
        preserve_layout_tag: bool,
    ) -> Result<(), String> {
        // Stack aggregates are laid out toward lower addresses; statics are laid
        // out toward higher addresses. Struct references use the aligned pointer's
        // low bit to carry that distinction across calls and reference storage.
        self.expression(reference)?;
        let offset = offset_words * 8;
        if offset == 0 {
            if !preserve_layout_tag {
                self.output.push_str("    and rax, -2\n");
            }
            return Ok(());
        }
        let global_layout = self.label("reference_global_layout");
        let done = self.label("reference_field_address_done");
        self.output.push_str(&format!(
            "    test al, 1\n    jz {global_layout}\n    and rax, -2\n    sub rax, {offset}\n"
        ));
        if preserve_layout_tag {
            self.output.push_str("    or rax, 1\n");
        }
        self.output.push_str(&format!(
            "    jmp {done}\n{global_layout}:\n    add rax, {offset}\n{done}:\n"
        ));
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
        let (qualifier, operator, mode) = operator_parts(operator);
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
            let mut variant_words = 0;
            for (value, field_type) in items[1..].iter().zip(&variant_fields) {
                self.push_value_words(value, field_type, false)?;
                variant_words += value_word_count(field_type, &self.structs, &self.enums)?;
            }
            for register in VALUE_REGISTERS[1..1 + variant_words].iter().rev() {
                self.output.push_str(&format!("    pop {register}\n"));
                self.stack_depth -= 1;
            }
            let payload_words = self
                .enums
                .get(&enum_name)
                .map(|variants| {
                    variants
                        .iter()
                        .map(|variant| {
                            variant
                                .fields
                                .iter()
                                .map(|field| value_word_count(field, &self.structs, &self.enums))
                                .collect::<Result<Vec<_>, _>>()
                                .map(|words| words.into_iter().sum::<usize>())
                        })
                        .collect::<Result<Vec<_>, _>>()
                        .ok()
                        .and_then(|words| words.into_iter().max())
                        .unwrap_or(0)
                })
                .unwrap_or(0);
            for index in variant_words..payload_words {
                self.output.push_str(&format!(
                    "    xor {}, {}\n",
                    VALUE_REGISTERS[index + 1],
                    VALUE_REGISTERS[index + 1]
                ));
            }
            let variant_discriminant = self
                .enums
                .get(&enum_name)
                .and_then(|variants| variants.get(variant_index))
                .expect("validated enum variant")
                .discriminant;
            self.output.push_str(&format!(
                "    mov rax, {}\n",
                asm_u64_immediate(variant_discriminant)
            ));
            return Ok(());
        }
        match operator {
            "clone" => {
                if items.len() != 2 {
                    return Err("clone requires one value".into());
                }
                let clone_function = self.expression_type(&items[1]).and_then(|ty| match ty {
                    Type::Named(name) => Some(format!("{name}-clone")),
                    _ => None,
                });
                if let Some(function) =
                    clone_function.filter(|name| self.functions.contains_key(name))
                {
                    self.list_expression(&[Expr::Symbol(function), items[1].clone()])
                } else {
                    self.expression(&items[1])
                }
            }
            "drop" => {
                if items.len() != 2 {
                    return Err("drop requires one value".into());
                }
                let ty = self.expression_type(&items[1]).unwrap_or(Type::Unit);
                let before = self.stack_depth;
                self.push_value_words(&items[1], &ty, false)?;
                let words = self.stack_depth - before;
                if words > 0 {
                    self.output
                        .push_str(&format!("    add rsp, {}\n", words * 8));
                    self.stack_depth -= words;
                }
                self.output.push_str("    xor eax, eax\n");
                Ok(())
            }
            "cell" => {
                if items.len() != 2 {
                    return Err("cell requires one initial value".into());
                }
                self.expression(&items[1])
            }
            "cell-get" => self.cell_get_expression(items),
            "cell-set" => self.cell_set_expression(items),
            "-" if items.len() == 2 => self.unary_negate(items, qualifier, mode),
            "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" => {
                self.binary_operator(operator, qualifier, mode, items)
            }
            "<" | "<=" | ">" | ">=" | "==" | "!=" => self.comparison(operator, items),
            "if" => self.if_expression(items),
            "borrow" | "borrow-mut" => {
                if items.len() == 3 {
                    return self.expression(&items[2]);
                }
                if items.len() != 2 {
                    return Err(format!("{operator} requires an owner and optional body"));
                }
                self.borrow_expression(items)
            }
            "deref" => {
                if items.len() != 2 {
                    return Err("deref requires a reference".into());
                }
                let target = self
                    .expression_type(&items[1])
                    .and_then(|ty| match ty {
                        Type::Reference { target, .. } => Some(*target),
                        _ => None,
                    })
                    .ok_or_else(|| "deref requires a reference".to_owned())?;
                self.expression(&items[1])?;
                match &target {
                    Type::F32 => self.output.push_str(
                        "    and rax, -2\n    movss xmm0, DWORD PTR [rax]\n",
                    ),
                    Type::F64 => self
                        .output
                        .push_str("    and rax, -2\n    movq xmm0, QWORD PTR [rax]\n"),
                    Type::I128 | Type::U128 => self
                        .output
                        .push_str("    and rax, -2\n    mov rdx, QWORD PTR [rax+8]\n    mov rax, QWORD PTR [rax]\n"),
                    _ => {
                        let words = storage_word_count(&target, &self.structs, &self.enums)?;
                        if words > VALUE_REGISTERS.len() {
                            return Err(
                                "deref aggregate target exceeds native value registers".into(),
                            );
                        }
                        self.output.push_str("    and rax, -2\n");
                        self.output.push_str("    mov rcx, rax\n");
                        for (index, register) in
                            VALUE_REGISTERS.iter().take(words).enumerate()
                        {
                            self.output.push_str(&format!(
                                "    mov {register}, QWORD PTR [rcx+{}]\n",
                                index * 8
                            ));
                        }
                    }
                }
                Ok(())
            }
            "deref-set" => {
                if items.len() != 3 {
                    return Err("deref-set requires a mutable reference and value".into());
                }
                let target = self
                    .expression_type(&items[1])
                    .and_then(|ty| match ty {
                        Type::Reference {
                            mutable: true,
                            target,
                        } => Some(*target),
                        _ => None,
                    })
                    .ok_or_else(|| "deref-set requires a mutable reference".to_owned())?;
                self.expression(&items[1])?;
                self.output.push_str("    and rax, -2\n");
                self.output.push_str("    push rax\n");
                self.stack_depth += 1;
                let words = storage_word_count(&target, &self.structs, &self.enums)?;
                if words > VALUE_REGISTERS.len() {
                    return Err("deref-set aggregate target exceeds native value registers".into());
                }
                if words > 1 {
                    self.expression_as_expected(&items[2], &target)?;
                    self.output.push_str("    pop rcx\n");
                    self.stack_depth -= 1;
                    for (index, register) in VALUE_REGISTERS.iter().take(words).enumerate() {
                        self.output.push_str(&format!(
                            "    mov QWORD PTR [rcx+{}], {register}\n",
                            index * 8
                        ));
                    }
                    return Ok(());
                }
                if is_float_type(&target) {
                    self.expression_as_float(&items[2], &target)?;
                } else {
                    self.expression(&items[2])?;
                }
                self.output.push_str("    pop rcx\n");
                self.stack_depth -= 1;
                match target {
                    Type::F32 => self.output.push_str("    movd DWORD PTR [rcx], xmm0\n"),
                    Type::F64 => self.output.push_str("    movq QWORD PTR [rcx], xmm0\n"),
                    _ => self.output.push_str("    mov QWORD PTR [rcx], rax\n"),
                }
                Ok(())
            }
            "unsafe" => {
                if items.len() != 2 {
                    return Err("unsafe requires one body expression".into());
                }
                self.expression(&items[1])
            }
            "addr-of" | "addr-of-mut" => self.borrow_expression(items),
            "ptr-read" => {
                if items.len() != 2 {
                    return Err("ptr-read requires a raw pointer".into());
                }
                let target = self
                    .expression_type(&items[1])
                    .and_then(|ty| match ty {
                        Type::RawPointer { target, .. } => Some(*target),
                        _ => None,
                    })
                    .ok_or_else(|| "ptr-read requires a raw pointer".to_owned())?;
                self.expression(&items[1])?;
                match target {
                    Type::F32 => self.output.push_str("    movss xmm0, DWORD PTR [rax]\n"),
                    Type::F64 => self.output.push_str("    movq xmm0, QWORD PTR [rax]\n"),
                    Type::I128 | Type::U128 => self
                        .output
                        .push_str("    mov rdx, QWORD PTR [rax+8]\n    mov rax, QWORD PTR [rax]\n"),
                    _ => self.output.push_str("    mov rax, QWORD PTR [rax]\n"),
                }
                Ok(())
            }
            "ptr-write" => {
                if items.len() != 3 {
                    return Err("ptr-write requires a pointer and value".into());
                }
                let target = self
                    .expression_type(&items[1])
                    .and_then(|ty| match ty {
                        Type::RawPointer {
                            mutable: true,
                            target,
                        } => Some(*target),
                        _ => None,
                    })
                    .ok_or_else(|| "ptr-write requires a mutable raw pointer".to_owned())?;
                self.expression(&items[1])?;
                self.output.push_str("    push rax\n");
                self.stack_depth += 1;
                self.expression(&items[2])?;
                self.output.push_str("    pop rcx\n");
                self.stack_depth -= 1;
                match target {
                    Type::F32 => self.output.push_str("    movd DWORD PTR [rcx], xmm0\n"),
                    Type::F64 => self.output.push_str("    movq QWORD PTR [rcx], xmm0\n"),
                    Type::I128 | Type::U128 => self
                        .output
                        .push_str("    mov QWORD PTR [rcx], rax\n    mov QWORD PTR [rcx+8], rdx\n"),
                    _ => self.output.push_str("    mov QWORD PTR [rcx], rax\n"),
                }
                Ok(())
            }
            "as" => {
                if items.len() != 3 {
                    return Err("as requires a value and target type".into());
                }
                let target = resolve_type(&parse_type(items.get(2))?, &self.aliases)?;
                self.cast_expression(&items[1], &target)
            }
            "literal" => {
                if items.len() != 3 {
                    return Err("literal requires an integer type and value".into());
                }
                let target = resolve_type(&parse_type(items.get(1))?, &self.aliases)?;
                if is_float_type(&target) {
                    self.expression_as_float(&items[2], &target)?;
                } else {
                    self.expression(&items[2])?;
                    if is_narrow_integer(&target) {
                        self.normalize_integer(&target)?;
                    }
                }
                Ok(())
            }
            "size-of" => self.layout_size_expression("size-of", items),
            "align-of" => self.layout_size_expression("align-of", items),
            "match" => self.match_expression(items, None, None),
            "index" => self.index_expression(items),
            "get" => self.field_expression(items),
            "get-payload" => self.enum_payload_expression(items),
            "!" => self.boolean_not(items),
            "&&" | "||" => self.boolean_logic(operator, items),
            "assert" | "debug-assert" => self.assert_expression(operator, items),
            "panic" | "unreachable" => {
                if items.len() != 1 {
                    return Err(format!("{operator} takes no arguments"));
                }
                self.output.push_str("    ud2\n");
                Ok(())
            }
            _ => self.call(operator, &items[1..], None),
        }
    }

    fn enum_value(&self, name: &str) -> Option<u64> {
        self.enums.values().find_map(|variants| {
            variants
                .iter()
                .find(|variant| variant.name == name)
                .map(|variant| variant.discriminant)
        })
    }

    fn index_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err("index requires an array and index".into());
        }
        if let Expr::String(string) = &items[1] {
            let characters = string.chars().collect::<Vec<_>>();
            let bounds_failure = self.label("string_index_bounds_failure");
            let done = self.label("string_index_done");
            self.expression(&items[2])?;
            self.output.push_str(&format!(
                "    mov rcx, rax\n    cmp rcx, {}\n    jae {bounds_failure}\n",
                characters.len()
            ));
            for (index, character) in characters.iter().enumerate() {
                let next = self.label("string_index_next");
                self.output.push_str(&format!(
                    "    cmp rcx, {index}\n    jne {next}\n    mov rax, {}\n    jmp {done}\n{next}:\n",
                    *character as u32
                ));
            }
            self.output
                .push_str(&format!("{bounds_failure}:\n    ud2\n{done}:\n"));
            return Ok(());
        }
        if let Expr::List(call_items) = &items[1] {
            if let Some(Expr::Symbol(function_name)) = call_items.first() {
                if self
                    .functions
                    .get(function_name)
                    .is_some_and(|function| function.indirect_return)
                {
                    let Type::Array(element, length) = self
                        .expression_type(&items[1])
                        .ok_or_else(|| "large aggregate call has no known type".to_owned())?
                    else {
                        return Err("indirect aggregate indexing requires an array result".into());
                    };
                    let element_words = value_word_count(&element, &self.structs, &self.enums)?;
                    if element_words > VALUE_REGISTERS.len() {
                        return Err(
                            "direct indexing of large arrays exceeds value registers".into()
                        );
                    }
                    let base = self.call_to_aggregate_temp(function_name, &call_items[1..])?;
                    let bounds_failure = self.label("indirect_array_index_bounds_failure");
                    let done = self.label("indirect_array_index_done");
                    self.expression(&items[2])?;
                    self.output.push_str(&format!(
                "    mov rcx, rax\n    cmp rcx, {length}\n    jae {bounds_failure}\n    lea r11, [rbp-{}]\n    imul rcx, {}\n    shl rcx, 3\n    sub r11, rcx\n",
                        base * 8,
                        element_words
                    ));
                    if element_words > 1 {
                        for (index, register) in VALUE_REGISTERS[..element_words].iter().enumerate()
                        {
                            self.output.push_str(&format!(
                                "    mov {register}, QWORD PTR [r11-{}]\n",
                                index * 8
                            ));
                        }
                    } else if matches!(*element, Type::F32) {
                        self.output.push_str("    movss xmm0, DWORD PTR [r11]\n");
                    } else if matches!(*element, Type::F64) {
                        self.output.push_str("    movq xmm0, QWORD PTR [r11]\n");
                    } else {
                        self.output.push_str("    mov rax, QWORD PTR [r11]\n");
                    }
                    self.output.push_str(&format!(
                        "    jmp {done}\n{bounds_failure}:\n    ud2\n{done}:\n"
                    ));
                    return Ok(());
                }
            }
        }
        if let Expr::List(repeat_items) = &items[1] {
            if matches!(
                repeat_items.first(),
                Some(Expr::Symbol(operator)) if operator == "array-repeat"
            ) {
                let Some(Type::Array(element, length)) = parse_type(repeat_items.get(1))
                    .ok()
                    .and_then(|ty| resolve_type(&ty, &self.aliases).ok())
                else {
                    return Err(
                        "direct array-repeat constructors require an explicit (array Element Length) type"
                            .into(),
                    );
                };
                if repeat_items.len() != 3 {
                    return Err("array-repeat requires one value".into());
                }
                let element_words = value_word_count(&element, &self.structs, &self.enums)?;
                if element_words > VALUE_REGISTERS.len() {
                    return Err("native computed indexing supports at most six value words".into());
                }
                let bounds_failure = self.label("array_repeat_index_bounds_failure");
                let done = self.label("array_repeat_index_done");
                self.expression(&items[2])?;
                self.output.push_str(&format!(
                    "    mov rcx, rax\n    cmp rcx, {length}\n    jae {bounds_failure}\n"
                ));
                if element_words == 1 {
                    self.expression_as_expected(&repeat_items[2], &element)?;
                } else {
                    self.push_value_words(&repeat_items[2], &element, false)?;
                    for register in VALUE_REGISTERS[..element_words].iter().rev() {
                        self.output.push_str(&format!("    pop {register}\n"));
                        self.stack_depth -= 1;
                    }
                }
                self.output.push_str(&format!(
                    "    jmp {done}\n{bounds_failure}:\n    ud2\n{done}:\n"
                ));
                return Ok(());
            }
        }
        if let Expr::List(array_items) = &items[1] {
            if !matches!(
                array_items.first(),
                Some(Expr::Symbol(operator)) if operator == "array"
            ) {
                return self.index_expression_without_literal(items);
            }
            let Some(Type::Array(element, length)) = parse_type(array_items.get(1))
                .ok()
                .and_then(|ty| resolve_type(&ty, &self.aliases).ok())
            else {
                return Err(
                    "direct array constructors require an explicit (array Element Length) type"
                        .into(),
                );
            };
            let values = &array_items[2..];
            if values.len() != length {
                return Err("array constructor has the wrong length".into());
            }
            if values.is_empty() {
                return Err("cannot index an empty array constructor".into());
            }
            let element_words = value_word_count(&element, &self.structs, &self.enums)?;
            if element_words > VALUE_REGISTERS.len() {
                return Err("native computed indexing supports at most six value words".into());
            }
            let bounds_failure = self.label("array_index_bounds_failure");
            let done = self.label("array_index_done");
            self.expression(&items[2])?;
            self.output.push_str(&format!(
                "    mov rcx, rax\n    cmp rcx, {}\n    jae {bounds_failure}\n",
                values.len()
            ));
            for (index, value) in values.iter().enumerate() {
                let next = self.label("array_index_next");
                self.output
                    .push_str(&format!("    cmp rcx, {index}\n    jne {next}\n"));
                if element_words == 1 {
                    self.expression_as_expected(value, &element)?;
                } else {
                    self.push_value_words(value, &element, false)?;
                    for register in VALUE_REGISTERS[..element_words].iter().rev() {
                        self.output.push_str(&format!("    pop {register}\n"));
                        self.stack_depth -= 1;
                    }
                }
                self.output.push_str(&format!("    jmp {done}\n{next}:\n"));
            }
            self.output
                .push_str(&format!("{bounds_failure}:\n    ud2\n{done}:\n"));
            return Ok(());
        }
        self.index_expression_without_literal(items)
    }

    fn index_expression_without_literal(&mut self, items: &[Expr]) -> Result<(), String> {
        if !matches!(&items[1], Expr::Symbol(_)) {
            if let Some(Type::Array(element, length)) = self.expression_type(&items[1]) {
                let element_words = storage_word_count(&element, &self.structs, &self.enums)?;
                let words = length.saturating_mul(element_words);
                if words > VALUE_REGISTERS.len() {
                    if element_words > VALUE_REGISTERS.len() {
                        return Err(
                            "native computed indexing cannot return an oversized array element"
                                .into(),
                        );
                    }
                    let temp_base = self
                        .aggregate_temp_base
                        .ok_or_else(|| "no aggregate temporary is available".to_owned())?;
                    self.store_value_to_slots(
                        &items[1],
                        &Type::Array(element.clone(), length),
                        &flat_slots(temp_base, words),
                    )?;
                    let bounds_failure = self.label("temporary_array_bounds_failure");
                    let done = self.label("temporary_array_index_done");
                    self.expression(&items[2])?;
                    self.output.push_str(&format!(
                        "    mov rcx, rax\n    cmp rcx, {length}\n    jae {bounds_failure}\n    imul rcx, {}\n    shl rcx, 3\n    lea r11, [rbp-{}]\n    sub r11, rcx\n",
                        element_words,
                        temp_base * 8
                    ));
                    for (word, register) in VALUE_REGISTERS[..element_words].iter().enumerate() {
                        self.output.push_str(&format!(
                            "    mov {register}, QWORD PTR [r11-{}]\n",
                            word * 8
                        ));
                    }
                    self.output.push_str(&format!(
                        "    jmp {done}\n{bounds_failure}:\n    ud2\n{done}:\n"
                    ));
                    if element_words == 1 && matches!(*element, Type::F32) {
                        self.output.push_str("    movd xmm0, eax\n");
                    } else if element_words == 1 && matches!(*element, Type::F64) {
                        self.output.push_str("    movq xmm0, rax\n");
                    }
                    return Ok(());
                }
            }
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
            let element_words = value_word_count(&element, &self.structs, &self.enums)?;
            let words = length.saturating_mul(element_words);
            if words > VALUE_REGISTERS.len() {
                return Err("native computed indexing supports at most six value words".into());
            }
            let bounds_failure = self.label("bounds_failure");
            self.expression_as_expected(&items[1], &Type::Array(element.clone(), length))?;
            for register in VALUE_REGISTERS[..words].iter().rev() {
                self.output.push_str(&format!("    push {register}\n"));
                self.stack_depth += 1;
            }
            self.expression(&items[2])?;
            self.output.push_str(&format!(
                "    mov rcx, rax\n    cmp rcx, {length}\n    jae {bounds_failure}\n    imul rcx, {element_words}\n"
            ));
            if element_words == 1 {
                self.output.push_str("    mov rax, QWORD PTR [rsp+rcx*8]\n");
            } else {
                for (index, register) in VALUE_REGISTERS[..element_words].iter().enumerate() {
                    self.output.push_str(&format!(
                        "    mov {register}, QWORD PTR [rsp+rcx*8+{}]\n",
                        index * 8
                    ));
                }
            }
            self.output.push_str(&format!(
                "    add rsp, {}\n    jmp {bounds_failure}_done\n{bounds_failure}:\n    ud2\n{bounds_failure}_done:\n",
                words * 8
            ));
            if element_words == 1 && matches!(*element, Type::F32) {
                self.output.push_str("    movd xmm0, eax\n");
            } else if element_words == 1 && matches!(*element, Type::F64) {
                self.output.push_str("    movq xmm0, rax\n");
            } else if element_words == 1 {
                ensure_integer_type(&element).map_err(|_| {
                    "native computed indexing supports scalar arrays only".to_owned()
                })?;
            }
            self.stack_depth -= words;
            return Ok(());
        };
        if let Some(Type::Array(element, length)) = self.global_types.get(name).cloned() {
            if !matches!(self.globals.get(name), Some(GlobalValue::Aggregate(_))) {
                return Err(format!("global '{name}' is not an aggregate array"));
            }
            let bounds_failure = self.label("global_array_bounds_failure");
            let done = self.label("global_array_index_done");
            let element_words = value_word_count(&element, &self.structs, &self.enums)?;
            self.expression(&items[2])?;
            self.output.push_str(&format!(
                "    mov rcx, rax\n    cmp rcx, {length}\n    jae {bounds_failure}\n    imul rcx, {element_words}\n    lea r11, [rip+{}]\n",
                asm_symbol(name)
            ));
            if element_words == 1 {
                self.output.push_str("    mov rax, QWORD PTR [r11+rcx*8]\n");
            } else {
                for (index, register) in VALUE_REGISTERS[..element_words].iter().enumerate() {
                    self.output.push_str(&format!(
                        "    mov {register}, QWORD PTR [r11+rcx*8+{}]\n",
                        index * 8
                    ));
                }
            }
            self.output.push_str(&format!(
                "    jmp {done}\n{bounds_failure}:\n    ud2\n{done}:\n"
            ));
            if element_words == 1 && matches!(*element, Type::F32) {
                self.output.push_str("    movd xmm0, eax\n");
            } else if element_words == 1 && matches!(*element, Type::F64) {
                self.output.push_str("    movq xmm0, rax\n");
            } else if element_words == 1 {
                ensure_integer_type(&element).map_err(|_| {
                    "native computed indexing supports scalar arrays only".to_owned()
                })?;
            }
            return Ok(());
        }
        let Storage::Array {
            base,
            element_words,
            ..
        } = self
            .locals
            .get(name)
            .ok_or_else(|| format!("unknown array '{name}'"))?
        else {
            return Err(format!("'{name}' is not an array"));
        };
        let base = *base;
        let element_words = *element_words;
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
            "    lea r11, [rbp-{}]\n    imul rcx, {}\n    shl rcx, 3\n    sub r11, rcx\n",
            base * 8,
            element_words
        ));
        if element_words == 1 && matches!(element_type, Type::F32) {
            self.output.push_str("    movss xmm0, DWORD PTR [r11]\n");
        } else if element_words == 1 && matches!(element_type, Type::F64) {
            self.output.push_str("    movq xmm0, QWORD PTR [r11]\n");
        } else if element_words == 1 {
            self.output.push_str("    mov rax, QWORD PTR [r11]\n");
        } else {
            for (index, register) in VALUE_REGISTERS[..element_words].iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [r11-{}]\n",
                    index * 8
                ));
            }
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
        result_type: Option<&Type>,
    ) -> Result<(), String> {
        if items.len() < 3 {
            return Err("match requires a value and an arm".into());
        }
        if let Expr::List(clone) = &items[1] {
            if matches!(clone.first(), Some(Expr::Symbol(head)) if head == "clone")
                && clone.len() == 2
            {
                let mut unwrapped = items.to_vec();
                unwrapped[1] = clone[1].clone();
                return self.match_expression(&unwrapped, float_type, result_type);
            }
        }
        if let Some(Type::Tuple(fields)) = self.expression_type(&items[1]) {
            return self.aggregate_match_expression(
                items,
                "tuple",
                &fields,
                Type::Tuple(fields.clone()),
                float_type,
                result_type,
            );
        }
        if let Some(Type::Array(element, length)) = self.expression_type(&items[1]) {
            let element_type = (*element).clone();
            let fields = vec![*element; length];
            return self.aggregate_match_expression(
                items,
                "array",
                &fields,
                Type::Array(Box::new(element_type), length),
                float_type,
                result_type,
            );
        }
        if let Some(Type::Named(name)) = self.expression_type(&items[1]) {
            if let Some(fields) = self.structs.get(&name).cloned() {
                let field_types = fields.into_iter().map(|field| field.ty).collect::<Vec<_>>();
                return self.aggregate_match_expression(
                    items,
                    &name,
                    &field_types,
                    Type::Named(name.clone()),
                    float_type,
                    result_type,
                );
            }
        }
        let direct_enum_call = match &items[1] {
            Expr::List(call_items) => match call_items.first() {
                Some(Expr::Symbol(function_name))
                    if self
                        .functions
                        .get(function_name)
                        .is_some_and(|function| function.indirect_return)
                        && self
                            .expression_type(&items[1])
                            .is_some_and(|ty| self.is_enum_type(&ty)) =>
                {
                    Some((function_name.clone(), call_items[1..].to_vec()))
                }
                _ => None,
            },
            _ => None,
        };
        let direct_enum_base = if let Some((function_name, arguments)) = direct_enum_call {
            Some(self.call_to_aggregate_temp(&function_name, &arguments)?)
        } else {
            None
        };
        let end = self.label("match_end");
        let base_depth = self.stack_depth;
        let payload_slots = if let Some(base) = direct_enum_base {
            let ty = self
                .expression_type(&items[1])
                .ok_or_else(|| "match scrutinee has no known type".to_owned())?;
            let payload_words = storage_word_count(&ty, &self.structs, &self.enums)? - 1;
            Some((base + 1..base + 1 + payload_words).collect())
        } else {
            match &items[1] {
                Expr::Symbol(name) => match self.locals.get(name) {
                    Some(Storage::Enum { payload, .. }) => Some(payload.clone()),
                    _ => None,
                },
                _ => None,
            }
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
        let wide_scrutinee = payload_slots.is_none()
            && self
                .expression_type(&items[1])
                .is_some_and(|ty| is_wide_integer(&ty));
        let staged_words = if payload_slots.is_some() {
            1
        } else if wide_scrutinee {
            2
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
            Expr::List(_) if direct_enum_base.is_some() => {
                self.output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp-{}]\n",
                    direct_enum_base.unwrap() * 8
                ));
            }
            Expr::Symbol(name)
                if self
                    .global_types
                    .get(name)
                    .is_some_and(|ty| self.is_enum_type(ty))
                    && matches!(self.globals.get(name), Some(GlobalValue::Aggregate(_))) =>
            {
                let words = 1 + payload_count;
                if words > VALUE_REGISTERS.len() {
                    for index in (0..words).rev() {
                        self.load_global_word(name, index)?;
                        self.push_rax();
                    }
                } else {
                    for index in (0..words).rev() {
                        let register = VALUE_REGISTERS[index];
                        self.load_global_word(name, index)?;
                        self.output.push_str(&format!("    mov {register}, rax\n"));
                    }
                    for index in (0..payload_count).rev() {
                        self.output
                            .push_str(&format!("    push {}\n", VALUE_REGISTERS[index + 1]));
                        self.stack_depth += 1;
                    }
                    self.push_rax();
                }
            }
            _ => {
                self.expression(&items[1])?;
                if wide_scrutinee {
                    self.output.push_str("    push rdx\n    push rax\n");
                    self.stack_depth += 2;
                } else {
                    for index in (0..payload_count).rev() {
                        self.output
                            .push_str(&format!("    push {}\n", VALUE_REGISTERS[index + 1]));
                        self.stack_depth += 1;
                    }
                    self.push_rax();
                }
            }
        }
        if payload_slots.is_some() {
            self.push_rax();
        }
        for arm in &items[2..] {
            let (pattern, guard, body) = match_arm_parts(arm)?;
            let next = self.label("match_next");
            let (variant_name, payload_patterns): (&str, Vec<&Expr>) = match pattern {
                Expr::Symbol(pattern) if pattern == "_" => ("", Vec::new()),
                Expr::Symbol(pattern) if self.enum_value(pattern).is_some() => {
                    (pattern.as_str(), Vec::new())
                }
                Expr::List(pattern)
                    if pattern.len() >= 2
                        && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or")
                        && self
                            .expression_type(&items[1])
                            .is_some_and(|ty| self.is_enum_type(&ty)) =>
                {
                    let matched = self.label("enum_or_pattern_matched");
                    let scrutinee_type = self
                        .expression_type(&items[1])
                        .ok_or_else(|| "enum match scrutinee has no known type".to_owned())?;
                    let Type::Named(enum_name) = scrutinee_type else {
                        return Err("enum or-pattern scrutinee has no named type".into());
                    };
                    for (index, alternative) in pattern[1..].iter().enumerate() {
                        let (alternative_name, payload_patterns): (&str, Vec<&Expr>) =
                            match alternative {
                                Expr::Symbol(name) => (name, Vec::new()),
                                Expr::List(items) if !items.is_empty() => {
                                    let Expr::Symbol(name) = &items[0] else {
                                        return Err(
                                            "enum or-pattern alternatives must be variants".into(),
                                        );
                                    };
                                    (name, items[1..].iter().collect())
                                }
                                _ => {
                                    return Err(
                                        "enum or-pattern alternatives must be variants".into()
                                    )
                                }
                            };
                        let last = index + 1 == pattern.len() - 1;
                        let alternative_next = if last {
                            next.clone()
                        } else {
                            self.label("enum_or_pattern_next")
                        };
                        let value = self
                            .enums
                            .get(&enum_name)
                            .and_then(|variants| {
                                variants
                                    .iter()
                                    .find(|variant| variant.name == alternative_name)
                            })
                            .ok_or_else(|| format!("unknown enum variant '{alternative_name}'"))?
                            .clone();
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp], {}\n    jne {alternative_next}\n",
                            asm_u64_immediate(value.discriminant)
                        ));
                        if !payload_patterns.is_empty()
                            && payload_patterns.len() != value.fields.len()
                        {
                            return Err(format!(
                                "variant '{alternative_name}' has the wrong payload count"
                            ));
                        }
                        let mut offset = 0;
                        for (payload, field_type) in payload_patterns.iter().zip(&value.fields) {
                            self.emit_enum_payload_pattern(
                                payload,
                                field_type,
                                offset,
                                payload_slots.as_ref(),
                                &alternative_next,
                            )?;
                            offset += storage_word_count(field_type, &self.structs, &self.enums)?;
                        }
                        self.output.push_str(&format!("    jmp {matched}\n"));
                        if !last {
                            self.output.push_str(&format!("{alternative_next}:\n"));
                        }
                    }
                    self.output.push_str(&format!("{matched}:\n"));
                    ("", Vec::new())
                }
                Expr::List(pattern)
                    if pattern.len() >= 2
                        && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
                {
                    let scrutinee_type = self
                        .expression_type(&items[1])
                        .ok_or_else(|| "match scrutinee has no known type".to_owned())?;
                    let matched = self.label("or_pattern_matched");
                    for (index, alternative) in pattern[1..].iter().enumerate() {
                        let last = index + 1 == pattern.len() - 1;
                        let alternative_next = if last {
                            next.clone()
                        } else {
                            self.label("or_pattern_next")
                        };
                        self.emit_scalar_pattern_test(
                            alternative,
                            &scrutinee_type,
                            &alternative_next,
                        )?;
                        self.output.push_str(&format!("    jmp {matched}\n"));
                        if !last {
                            self.output.push_str(&format!("{alternative_next}:\n"));
                        }
                    }
                    self.output.push_str(&format!("{matched}:\n"));
                    ("", Vec::new())
                }
                Expr::List(pattern)
                    if pattern.len() == 3
                        && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "literal") =>
                {
                    let scrutinee_type = self
                        .expression_type(&items[1])
                        .ok_or_else(|| "match scrutinee has no known type".to_owned())?;
                    self.emit_scalar_pattern_test(
                        &Expr::List(pattern.clone()),
                        &scrutinee_type,
                        &next,
                    )?;
                    ("", Vec::new())
                }
                Expr::List(pattern)
                    if pattern.len() == 3
                        && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "range") =>
                {
                    let scrutinee_type = self
                        .expression_type(&items[1])
                        .ok_or_else(|| "match scrutinee has no known type".to_owned())?;
                    self.emit_scalar_range_pattern(
                        &Expr::List(pattern.clone()),
                        &scrutinee_type,
                        &next,
                    )?;
                    ("", Vec::new())
                }
                Expr::List(pattern) if !pattern.is_empty() => {
                    let Expr::Symbol(pattern_name) = &pattern[0] else {
                        return Err("match variant pattern must be a symbol".into());
                    };
                    if self.enum_value(pattern_name).is_none() {
                        return Err(format!("unknown enum variant '{pattern_name}'"));
                    }
                    (pattern_name.as_str(), pattern[1..].iter().collect())
                }
                Expr::Integer(value) => {
                    if wide_scrutinee {
                        let bits = *value as u128;
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp], {}\n    jne {next}\n    cmp QWORD PTR [rsp+8], {}\n    jne {next}\n",
                            bits as u64,
                            (bits >> 64) as u64
                        ));
                    } else {
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp], {value}\n    jne {next}\n"
                        ));
                    }
                    ("", Vec::new())
                }
                Expr::UnsignedInteger(value) => {
                    if wide_scrutinee {
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp], {}\n    jne {next}\n    cmp QWORD PTR [rsp+8], {}\n    jne {next}\n",
                            *value as u64,
                            (*value >> 64) as u64
                        ));
                    } else {
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                            *value as u64
                        ));
                    }
                    ("", Vec::new())
                }
                Expr::Char(value) => {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                        *value as u32
                    ));
                    ("", Vec::new())
                }
                Expr::Symbol(pattern) if pattern == "false" || pattern == "true" => {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                        if pattern == "true" { 1 } else { 0 }
                    ));
                    ("", Vec::new())
                }
                _ => return Err("invalid scalar match pattern".into()),
            };
            if let Expr::Symbol(pattern) = pattern {
                if pattern != "_" && self.enum_value(pattern).is_some() {
                    let value = self.enum_value(pattern).unwrap();
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                        asm_u64_immediate(value)
                    ));
                }
            } else if !variant_name.is_empty() {
                let value = self
                    .enum_value(variant_name)
                    .ok_or_else(|| "unknown enum variant".to_owned())?;
                self.output.push_str(&format!(
                    "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                    asm_u64_immediate(value)
                ));
            }
            let payload_fields = if !variant_name.is_empty() {
                let scrutinee_type = self
                    .expression_type(&items[1])
                    .ok_or_else(|| "match scrutinee has no known type".to_owned())?;
                let Type::Named(enum_name) = scrutinee_type else {
                    return Err("enum match scrutinee has no named type".into());
                };
                self.enums
                    .get(&enum_name)
                    .and_then(|variants| {
                        variants.iter().find(|variant| variant.name == variant_name)
                    })
                    .map(|variant| variant.fields.clone())
                    .ok_or_else(|| format!("unknown enum variant '{variant_name}'"))?
            } else {
                Vec::new()
            };
            if payload_patterns.len() != payload_fields.len() && !payload_patterns.is_empty() {
                return Err(format!(
                    "variant '{variant_name}' expects {} payload patterns",
                    payload_fields.len()
                ));
            }
            let mut payload_offset = 0;
            for (pattern, field_type) in payload_patterns.iter().zip(&payload_fields) {
                self.emit_enum_payload_pattern(
                    pattern,
                    field_type,
                    payload_offset,
                    payload_slots.as_ref(),
                    &next,
                )?;
                payload_offset += storage_word_count(field_type, &self.structs, &self.enums)?;
            }
            let mut bindings = Vec::new();
            let mut binding_offset = 0;
            for (pattern, field_type) in payload_patterns.iter().zip(&payload_fields) {
                self.collect_enum_pattern_bindings(
                    pattern,
                    field_type,
                    binding_offset,
                    &mut bindings,
                )?;
                binding_offset += storage_word_count(field_type, &self.structs, &self.enums)?;
            }
            for (binding, offset, binding_type) in bindings {
                let slots = local_slots(&self.locals, &binding)?;
                let binding_words = storage_word_count(&binding_type, &self.structs, &self.enums)?;
                if slots.len() != binding_words {
                    return Err(format!("enum binding '{binding}' has inconsistent storage"));
                }
                for (word, slot) in slots.into_iter().enumerate() {
                    if let Some(payload_slots) = payload_slots.as_ref() {
                        let payload_slot = payload_slots.get(offset + word).ok_or_else(|| {
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
                            (offset + word + 1) * 8,
                            slot * 8
                        ));
                    }
                }
            }
            if let Some(guard) = guard {
                self.expression(guard)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {next}\n"));
            }
            if let Some(ty) = float_type {
                self.expression_as_float(body, ty)?;
            } else if let Some(ty) = result_type {
                self.expression_as_expected(body, ty)?;
            } else {
                self.expression(body)?;
            }
            self.output
                .push_str(&format!("    add rsp, {}\n", staged_words * 8));
            self.stack_depth -= staged_words;
            self.output.push_str(&format!("    jmp {end}\n{next}:\n"));
            self.stack_depth = base_depth + staged_words;
        }
        self.output.push_str(&format!("{end}:\n"));
        self.stack_depth = base_depth;
        Ok(())
    }

    fn emit_scalar_range_pattern(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        next: &str,
    ) -> Result<(), String> {
        let range = scalar_range_bounds(pattern, ty)?;
        let operand = "QWORD PTR [rsp]";
        match range {
            ScalarRange::Signed(lower, upper) => {
                if matches!(ty, Type::I128) {
                    return self.emit_wide_scalar_range(lower as u128, upper as u128, true, next);
                }
                self.output.push_str(&format!(
                    "    cmp {operand}, {lower}\n    jl {next}\n    cmp {operand}, {upper}\n    jg {next}\n"
                ));
            }
            ScalarRange::Unsigned(lower, upper) => {
                if matches!(ty, Type::U128) {
                    return self.emit_wide_scalar_range(lower, upper, false, next);
                }
                self.output.push_str(&format!(
                    "    cmp {operand}, {}\n    jb {next}\n    cmp {operand}, {}\n    ja {next}\n",
                    asm_u64_immediate(lower as u64),
                    asm_u64_immediate(upper as u64)
                ));
            }
            ScalarRange::Char(lower, upper) => {
                self.output.push_str(&format!(
                    "    cmp {operand}, {}\n    jb {next}\n    cmp {operand}, {}\n    ja {next}\n",
                    asm_u64_immediate(lower),
                    asm_u64_immediate(upper)
                ));
            }
        }
        Ok(())
    }

    fn emit_scalar_pattern_test(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        next: &str,
    ) -> Result<(), String> {
        if let Some(value) = typed_integer_pattern_value(pattern, ty)? {
            return self.emit_scalar_pattern_test(value, ty, next);
        }
        if matches!(pattern, Expr::List(parts) if parts.len() == 3
            && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "range"))
        {
            return self.emit_scalar_range_pattern(pattern, ty, next);
        }
        match pattern {
            Expr::Symbol(name) if name == "_" => Ok(()),
            Expr::Symbol(name) if name == "true" || name == "false" => {
                self.output.push_str(&format!(
                    "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                    if name == "true" { 1 } else { 0 }
                ));
                Ok(())
            }
            Expr::Integer(value) => {
                if is_wide_integer(ty) {
                    let bits = *value as u128;
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n    cmp QWORD PTR [rsp+8], {}\n    jne {next}\n",
                        asm_u64_immediate(bits as u64),
                        asm_u64_immediate((bits >> 64) as u64)
                    ));
                } else {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {value}\n    jne {next}\n"
                    ));
                }
                Ok(())
            }
            Expr::UnsignedInteger(value) => {
                if is_wide_integer(ty) {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n    cmp QWORD PTR [rsp+8], {}\n    jne {next}\n",
                        asm_u64_immediate(*value as u64),
                        asm_u64_immediate((*value >> 64) as u64)
                    ));
                } else {
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                        asm_u64_immediate(*value as u64)
                    ));
                }
                Ok(())
            }
            Expr::Char(value) => {
                self.output.push_str(&format!(
                    "    cmp QWORD PTR [rsp], {}\n    jne {next}\n",
                    *value as u32
                ));
                Ok(())
            }
            _ => Err("invalid scalar or-pattern alternative".into()),
        }
    }

    fn emit_enum_scalar_pattern_test(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        low_operand: &str,
        high_operand: Option<&str>,
        next: &str,
    ) -> Result<(), String> {
        if let Some(value) = typed_integer_pattern_value(pattern, ty)? {
            return self.emit_enum_scalar_pattern_test(value, ty, low_operand, high_operand, next);
        }
        if matches!(pattern, Expr::List(parts) if parts.len() == 3
            && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "range"))
        {
            let range = scalar_range_bounds(pattern, ty)?;
            match range {
                ScalarRange::Signed(lower, upper) if matches!(ty, Type::I128) => {
                    let high_operand = high_operand.ok_or_else(|| {
                        "wide payload pattern is missing its high word".to_owned()
                    })?;
                    return self.emit_wide_scalar_range_at(
                        lower as u128,
                        upper as u128,
                        true,
                        low_operand,
                        high_operand,
                        next,
                    );
                }
                ScalarRange::Unsigned(lower, upper) if matches!(ty, Type::U128) => {
                    let high_operand = high_operand.ok_or_else(|| {
                        "wide payload pattern is missing its high word".to_owned()
                    })?;
                    return self.emit_wide_scalar_range_at(
                        lower,
                        upper,
                        false,
                        low_operand,
                        high_operand,
                        next,
                    );
                }
                ScalarRange::Signed(lower, upper) => {
                    self.output.push_str(&format!(
                        "    cmp {low_operand}, {lower}\n    jl {next}\n    cmp {low_operand}, {upper}\n    jg {next}\n"
                    ));
                }
                ScalarRange::Unsigned(lower, upper) => {
                    self.output.push_str(&format!(
                        "    cmp {low_operand}, {}\n    jb {next}\n    cmp {low_operand}, {}\n    ja {next}\n",
                        asm_u64_immediate(lower as u64),
                        asm_u64_immediate(upper as u64)
                    ));
                }
                ScalarRange::Char(lower, upper) => {
                    self.output.push_str(&format!(
                        "    cmp {low_operand}, {}\n    jb {next}\n    cmp {low_operand}, {}\n    ja {next}\n",
                        asm_u64_immediate(lower),
                        asm_u64_immediate(upper)
                    ));
                }
            }
            return Ok(());
        }
        match pattern {
            Expr::Symbol(name) if name == "_" => Ok(()),
            Expr::Symbol(name) if name == "true" || name == "false" => {
                self.output.push_str(&format!(
                    "    cmp {low_operand}, {}\n    jne {next}\n",
                    if name == "true" { 1 } else { 0 }
                ));
                Ok(())
            }
            Expr::Integer(value) => {
                if is_wide_integer(ty) {
                    let high_operand = high_operand.ok_or_else(|| {
                        "wide payload pattern is missing its high word".to_owned()
                    })?;
                    let bits = *value as u128;
                    self.output.push_str(&format!(
                        "    cmp {low_operand}, {}\n    jne {next}\n    cmp {high_operand}, {}\n    jne {next}\n",
                        asm_u64_immediate(bits as u64),
                        asm_u64_immediate((bits >> 64) as u64)
                    ));
                } else {
                    self.output
                        .push_str(&format!("    cmp {low_operand}, {value}\n    jne {next}\n"));
                }
                Ok(())
            }
            Expr::UnsignedInteger(value) => {
                if is_wide_integer(ty) {
                    let high_operand = high_operand.ok_or_else(|| {
                        "wide payload pattern is missing its high word".to_owned()
                    })?;
                    self.output.push_str(&format!(
                        "    cmp {low_operand}, {}\n    jne {next}\n    cmp {high_operand}, {}\n    jne {next}\n",
                        asm_u64_immediate(*value as u64),
                        asm_u64_immediate((*value >> 64) as u64)
                    ));
                } else {
                    self.output.push_str(&format!(
                        "    cmp {low_operand}, {}\n    jne {next}\n",
                        asm_u64_immediate(*value as u64)
                    ));
                }
                Ok(())
            }
            Expr::Char(value) => {
                self.output.push_str(&format!(
                    "    cmp {low_operand}, {}\n    jne {next}\n",
                    *value as u32
                ));
                Ok(())
            }
            _ => Err("invalid scalar enum payload alternative".into()),
        }
    }

    fn emit_scalar_pattern_at(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        low_operand: &str,
        high_operand: Option<&str>,
        next: &str,
    ) -> Result<(), String> {
        if let Expr::List(parts) = pattern {
            if parts.len() >= 2 && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or")
            {
                let matched = self.label("nested_or_pattern_matched");
                for (index, alternative) in parts[1..].iter().enumerate() {
                    let last = index + 1 == parts.len() - 1;
                    let alternative_next = if last {
                        next.to_owned()
                    } else {
                        self.label("nested_or_pattern_next")
                    };
                    self.emit_scalar_pattern_at(
                        alternative,
                        ty,
                        low_operand,
                        high_operand,
                        &alternative_next,
                    )?;
                    self.output.push_str(&format!("    jmp {matched}\n"));
                    if !last {
                        self.output.push_str(&format!("{alternative_next}:\n"));
                    }
                }
                self.output.push_str(&format!("{matched}:\n"));
                return Ok(());
            }
        }
        self.emit_enum_scalar_pattern_test(pattern, ty, low_operand, high_operand, next)
    }

    fn emit_wide_scalar_range_at(
        &mut self,
        lower: u128,
        upper: u128,
        signed: bool,
        low_operand: &str,
        high_operand: &str,
        next: &str,
    ) -> Result<(), String> {
        let lower_ok = self.label("payload_range_lower_ok");
        let upper_ok = self.label("payload_range_upper_ok");
        let low_jump = if signed { "jl" } else { "jb" };
        let high_jump = if signed { "jg" } else { "ja" };
        self.output.push_str(&format!(
            "    cmp {high_operand}, {}\n    {low_jump} {next}\n    {high_jump} {lower_ok}\n    cmp {low_operand}, {}\n    jb {next}\n{lower_ok}:\n    cmp {high_operand}, {}\n    {high_jump} {next}\n    {low_jump} {upper_ok}\n    cmp {low_operand}, {}\n    ja {next}\n{upper_ok}:\n",
            asm_u64_immediate((lower >> 64) as u64),
            asm_u64_immediate(lower as u64),
            asm_u64_immediate((upper >> 64) as u64),
            asm_u64_immediate(upper as u64),
        ));
        Ok(())
    }

    fn emit_wide_scalar_range(
        &mut self,
        lower: u128,
        upper: u128,
        signed: bool,
        next: &str,
    ) -> Result<(), String> {
        let lower_ok = self.label("range_lower_ok");
        let upper_ok = self.label("range_upper_ok");
        let low_jump = if signed { "jl" } else { "jb" };
        let high_jump = if signed { "jg" } else { "ja" };
        self.output.push_str(&format!(
            "    cmp QWORD PTR [rsp+8], {}\n    {low_jump} {next}\n    {high_jump} {lower_ok}\n    cmp QWORD PTR [rsp], {}\n    jb {next}\n{lower_ok}:\n    cmp QWORD PTR [rsp+8], {}\n    {high_jump} {next}\n    {low_jump} {upper_ok}\n    cmp QWORD PTR [rsp], {}\n    ja {next}\n{upper_ok}:\n",
            asm_u64_immediate((lower >> 64) as u64),
            asm_u64_immediate(lower as u64),
            asm_u64_immediate((upper >> 64) as u64),
            asm_u64_immediate(upper as u64),
        ));
        Ok(())
    }

    fn aggregate_match_expression(
        &mut self,
        items: &[Expr],
        constructor: &str,
        fields: &[Type],
        ty: Type,
        float_type: Option<&Type>,
        result_type: Option<&Type>,
    ) -> Result<(), String> {
        let storage_words = storage_word_count(&ty, &self.structs, &self.enums)?;
        if storage_words > VALUE_REGISTERS.len() {
            if fields.iter().all(|field| {
                value_word_count(field, &self.structs, &self.enums).is_ok_and(|words| words == 1)
            }) {
                if let Expr::Symbol(name) = &items[1] {
                    if self.locals.contains_key(name) {
                        let source_slots = local_slots(&self.locals, name)?;
                        return self.large_scalar_aggregate_match_slots(
                            items,
                            constructor,
                            fields,
                            &source_slots,
                            float_type,
                            result_type,
                        );
                    }
                }
                if let Expr::List(call_items) = &items[1] {
                    if let Some(Expr::Symbol(function_name)) = call_items.first() {
                        if self
                            .functions
                            .get(function_name)
                            .is_some_and(|function| function.indirect_return)
                        {
                            let base =
                                self.call_to_aggregate_temp(function_name, &call_items[1..])?;
                            let storage_words =
                                storage_word_count(&ty, &self.structs, &self.enums)?;
                            let source_slots = flat_slots(base, storage_words);
                            return self.large_scalar_aggregate_match_slots(
                                items,
                                constructor,
                                fields,
                                &source_slots,
                                float_type,
                                result_type,
                            );
                        }
                    }
                }
            }
            let source_slots = if let Expr::Symbol(name) = &items[1] {
                self.locals
                    .contains_key(name)
                    .then(|| local_slots(&self.locals, name))
                    .transpose()?
            } else if let Expr::List(call_items) = &items[1] {
                match call_items.first() {
                    Some(Expr::Symbol(function_name))
                        if self
                            .functions
                            .get(function_name)
                            .is_some_and(|function| function.indirect_return) =>
                    {
                        let base = self.call_to_aggregate_temp(function_name, &call_items[1..])?;
                        Some(flat_slots(base, storage_words))
                    }
                    _ => None,
                }
            } else {
                None
            };
            if let Some(source_slots) = source_slots {
                return self.aggregate_match_from_slots(
                    items,
                    constructor,
                    &ty,
                    &source_slots,
                    storage_words,
                    float_type,
                    result_type,
                );
            }
            if let Expr::List(value_items) = &items[1] {
                if matches!(
                    value_items.first(),
                    Some(Expr::Symbol(name)) if name == constructor
                ) {
                    let base_depth = self.stack_depth;
                    self.push_value_words(&items[1], &ty, true)?;
                    return self.aggregate_match_from_staged_stack(
                        items,
                        constructor,
                        &ty,
                        storage_words,
                        float_type,
                        result_type,
                        base_depth,
                    );
                }
            }
            if let Expr::Symbol(name) = &items[1] {
                if self.global_types.get(name) == Some(&ty) {
                    let base_depth = self.stack_depth;
                    for index in (0..storage_words).rev() {
                        self.load_global_word(name, index)?;
                        self.push_rax();
                    }
                    return self.aggregate_match_from_staged_stack(
                        items,
                        constructor,
                        &ty,
                        storage_words,
                        float_type,
                        result_type,
                        base_depth,
                    );
                }
            }
        }
        let words = value_word_count(&ty, &self.structs, &self.enums)?;
        let base_depth = self.stack_depth;
        let direct_values = if let Expr::List(value_items) = &items[1] {
            let value_start = match constructor {
                "tuple" | "array" if matches!(value_items.first(), Some(Expr::Symbol(name)) if name == constructor) => {
                    if parse_type(value_items.get(1))
                        .ok()
                        .is_some_and(|declared| declared == ty)
                    {
                        2
                    } else {
                        1
                    }
                }
                _ if constructor != "tuple"
                    && constructor != "array"
                    && matches!(value_items.first(), Some(Expr::Symbol(name)) if name == constructor) =>
                {
                    1
                }
                _ => usize::MAX,
            };
            if value_start != usize::MAX && value_items.len() - value_start == fields.len() {
                Some(value_items[value_start..].iter().collect::<Vec<_>>())
            } else {
                None
            }
        } else {
            None
        };
        if let Some(values) = direct_values.as_ref() {
            for (value, field_type) in values.iter().zip(fields) {
                self.push_value_words(value, field_type, false)?;
            }
            for register in VALUE_REGISTERS[..words].iter().rev() {
                self.output.push_str(&format!("    pop {register}\n"));
                self.stack_depth -= 1;
            }
        }
        let empty_direct_array = words == 0
            && constructor == "array"
            && matches!(&items[1], Expr::List(value) if matches!(value.first(), Some(Expr::Symbol(name)) if name == "array"));
        if empty_direct_array {
            // An empty value has no ABI words to evaluate or stage.
        } else if direct_values.is_some() {
            for register in VALUE_REGISTERS[..words].iter().rev() {
                self.output.push_str(&format!("    push {register}\n"));
                self.stack_depth += 1;
            }
        } else if let Expr::Symbol(name) = &items[1] {
            if self.locals.contains_key(name) {
                for slot in local_slots(&self.locals, name)?.into_iter().rev() {
                    self.output
                        .push_str(&format!("    push QWORD PTR [rbp-{}]\n", slot * 8));
                    self.stack_depth += 1;
                }
            } else {
                self.expression(&items[1])?;
                for register in VALUE_REGISTERS[..words].iter().rev() {
                    self.output.push_str(&format!("    push {register}\n"));
                    self.stack_depth += 1;
                }
            }
        } else {
            self.expression(&items[1])?;
            for register in VALUE_REGISTERS[..words].iter().rev() {
                self.output.push_str(&format!("    push {register}\n"));
                self.stack_depth += 1;
            }
        }
        let end = self.label("tuple_match_end");
        for arm in &items[2..] {
            let (pattern, guard, body) = match_arm_parts(arm)?;
            let next = self.label("tuple_match_next");
            let mut bindings = Vec::new();
            self.emit_aggregate_pattern(pattern, constructor, &ty, 0, &next, &mut bindings)?;
            for (name, offset, binding_type) in bindings {
                let slots = local_slots(&self.locals, &name)?;
                let binding_words = value_word_count(&binding_type, &self.structs, &self.enums)?;
                if slots.len() != binding_words {
                    return Err(format!("match binding '{name}' has inconsistent storage"));
                }
                for (index, slot) in slots.into_iter().enumerate() {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rsp+{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        (offset + index) * 8,
                        slot * 8
                    ));
                }
            }
            if let Some(guard) = guard {
                self.expression(guard)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {next}\n"));
            }
            if let Some(ty) = float_type {
                self.expression_as_float(body, ty)?;
                self.output.push_str(&format!(
                    "    add rsp, {}\n    jmp {end}\n{next}:\n",
                    words * 8
                ));
            } else {
                if let Some(ty) = result_type {
                    self.expression_as_expected(body, ty)?;
                } else {
                    self.expression(body)?;
                }
                self.output.push_str(&format!(
                    "    add rsp, {}\n    jmp {end}\n{next}:\n",
                    words * 8
                ));
            }
            self.stack_depth = base_depth + words;
        }
        self.output.push_str(&format!("{end}:\n"));
        self.stack_depth = base_depth;
        Ok(())
    }

    fn aggregate_match_from_slots(
        &mut self,
        items: &[Expr],
        constructor: &str,
        ty: &Type,
        source_slots: &[usize],
        storage_words: usize,
        float_type: Option<&Type>,
        result_type: Option<&Type>,
    ) -> Result<(), String> {
        if source_slots.len() != storage_words {
            return Err("large aggregate match has an inconsistent storage layout".into());
        }
        let base_depth = self.stack_depth;
        for slot in source_slots.iter().rev() {
            self.output
                .push_str(&format!("    push QWORD PTR [rbp-{}]\n", slot * 8));
            self.stack_depth += 1;
        }
        self.aggregate_match_from_staged_stack(
            items,
            constructor,
            ty,
            storage_words,
            float_type,
            result_type,
            base_depth,
        )
    }

    fn aggregate_match_from_staged_stack(
        &mut self,
        items: &[Expr],
        constructor: &str,
        ty: &Type,
        storage_words: usize,
        float_type: Option<&Type>,
        result_type: Option<&Type>,
        base_depth: usize,
    ) -> Result<(), String> {
        let end = self.label("aggregate_match_end");
        for arm in &items[2..] {
            let (pattern, guard, body) = match_arm_parts(arm)?;
            let next = self.label("aggregate_match_next");
            let mut bindings = Vec::new();
            self.emit_aggregate_pattern(pattern, constructor, ty, 0, &next, &mut bindings)?;
            for (name, offset, binding_type) in bindings {
                let slots = local_slots(&self.locals, &name)?;
                let binding_words = storage_word_count(&binding_type, &self.structs, &self.enums)?;
                if slots.len() != binding_words {
                    return Err(format!(
                        "match binding '{name}' has inconsistent flattened layout"
                    ));
                }
                for (index, slot) in slots.into_iter().enumerate() {
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rsp+{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        (offset + index) * 8,
                        slot * 8
                    ));
                }
            }
            if let Some(guard) = guard {
                self.expression(guard)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {next}\n"));
            }
            if let Some(ty) = float_type {
                self.expression_as_float(body, ty)?;
            } else if let Some(ty) = result_type {
                self.expression_as_expected(body, ty)?;
            } else {
                self.expression(body)?;
            }
            self.output.push_str(&format!(
                "    add rsp, {}\n    jmp {end}\n{next}:\n",
                storage_words * 8
            ));
            self.stack_depth = base_depth + storage_words;
        }
        self.output.push_str(&format!("{end}:\n"));
        self.stack_depth = base_depth;
        Ok(())
    }

    fn large_scalar_aggregate_match_slots(
        &mut self,
        items: &[Expr],
        constructor: &str,
        fields: &[Type],
        source_slots: &[usize],
        float_type: Option<&Type>,
        result_type: Option<&Type>,
    ) -> Result<(), String> {
        if source_slots.len() != fields.len() {
            return Err("large aggregate match has an inconsistent local layout".into());
        }
        let end = self.label("large_local_match_end");
        for arm in &items[2..] {
            let (pattern, guard, body) = match_arm_parts(arm)?;
            let next = self.label("large_local_match_next");
            let mut bindings = Vec::new();
            self.emit_large_scalar_aggregate_pattern(
                pattern,
                constructor,
                fields,
                source_slots,
                &next,
                &mut bindings,
            )?;
            for (binding, source_slot, binding_type) in bindings {
                let destination_slots = local_slots(&self.locals, &binding)?;
                if destination_slots.len() != 1
                    || value_word_count(&binding_type, &self.structs, &self.enums)? != 1
                {
                    return Err("large aggregate bindings must be scalar".into());
                }
                self.output.push_str(&format!(
                    "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                    source_slot * 8,
                    destination_slots[0] * 8
                ));
            }
            if let Some(guard) = guard {
                self.expression(guard)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {next}\n"));
            }
            if let Some(ty) = float_type {
                self.expression_as_float(body, ty)?;
            } else if let Some(ty) = result_type {
                self.expression_as_expected(body, ty)?;
            } else {
                self.expression(body)?;
            }
            self.output.push_str(&format!("    jmp {end}\n{next}:\n"));
        }
        self.output.push_str(&format!("{end}:\n"));
        Ok(())
    }

    fn emit_large_scalar_aggregate_pattern(
        &mut self,
        pattern: &Expr,
        constructor: &str,
        fields: &[Type],
        source_slots: &[usize],
        next: &str,
        bindings: &mut Vec<(String, usize, Type)>,
    ) -> Result<(), String> {
        if matches!(pattern, Expr::Symbol(name) if name == "_") {
            return Ok(());
        }
        if let Expr::List(parts) = pattern {
            if parts.len() >= 2 && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or")
            {
                let matched = self.label("large_aggregate_or_pattern_matched");
                for (index, alternative) in parts[1..].iter().enumerate() {
                    let last = index + 1 == parts.len() - 1;
                    let alternative_next = if last {
                        next.to_owned()
                    } else {
                        self.label("large_aggregate_or_pattern_next")
                    };
                    let mut alternative_bindings = Vec::new();
                    self.emit_large_scalar_aggregate_pattern(
                        alternative,
                        constructor,
                        fields,
                        source_slots,
                        &alternative_next,
                        &mut alternative_bindings,
                    )?;
                    if !alternative_bindings.is_empty() {
                        return Err("aggregate or-pattern alternatives cannot bind values".into());
                    }
                    self.output.push_str(&format!("    jmp {matched}\n"));
                    if !last {
                        self.output.push_str(&format!("{alternative_next}:\n"));
                    }
                }
                self.output.push_str(&format!("{matched}:\n"));
                return Ok(());
            }
            if !matches!(
                parts.first(),
                Some(Expr::Symbol(name)) if name == constructor
            ) {
                return Err("aggregate match pattern has the wrong shape".into());
            }
            if parts.len() - 1 != fields.len() {
                return Err("aggregate match pattern has the wrong shape".into());
            }
            for (index, (field_pattern, field_type)) in parts[1..].iter().zip(fields).enumerate() {
                if is_scalar_pattern_type(field_type)
                    && matches!(
                        field_pattern,
                        Expr::List(items)
                            if matches!(items.first(), Some(Expr::Symbol(name))
                                if matches!(name.as_str(), "or" | "range" | "literal"))
                    )
                {
                    let low_operand = format!("QWORD PTR [rbp-{}]", source_slots[index] * 8);
                    let high_operand = if is_wide_integer(field_type) {
                        Some(format!("QWORD PTR [rbp-{}]", source_slots[index] * 8 + 8))
                    } else {
                        None
                    };
                    self.emit_scalar_pattern_at(
                        field_pattern,
                        field_type,
                        &low_operand,
                        high_operand.as_deref(),
                        next,
                    )?;
                    continue;
                }
                let field_pattern = typed_integer_pattern_value(field_pattern, field_type)?
                    .unwrap_or(field_pattern);
                let slot = source_slots[index];
                match field_pattern {
                    Expr::Symbol(field) if field == "_" => {}
                    Expr::Symbol(field) if field == "true" || field == "false" => {
                        if !matches!(field_type, Type::Bool) {
                            return Err("boolean aggregate pattern has a non-boolean field".into());
                        }
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rbp-{}], {}\n    jne {next}\n",
                            slot * 8,
                            if field == "true" { 1 } else { 0 }
                        ));
                    }
                    Expr::Symbol(field) => {
                        bindings.push((field.clone(), slot, field_type.clone()));
                    }
                    Expr::Integer(value) => {
                        if ensure_integer_type(field_type).is_err() {
                            return Err("integer aggregate pattern has a non-integer field".into());
                        }
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rbp-{}], {}\n    jne {next}\n",
                            slot * 8,
                            value
                        ));
                    }
                    Expr::UnsignedInteger(value) => {
                        if ensure_integer_type(field_type).is_err() {
                            return Err("integer aggregate pattern has a non-integer field".into());
                        }
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rbp-{}], {}\n    jne {next}\n",
                            slot * 8,
                            *value as u64
                        ));
                    }
                    Expr::Char(value) => {
                        if !matches!(field_type, Type::Char) {
                            return Err(
                                "character aggregate pattern has a non-character field".into()
                            );
                        }
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rbp-{}], {}\n    jne {next}\n",
                            slot * 8,
                            *value as u32
                        ));
                    }
                    _ => return Err("unsupported large aggregate field pattern".into()),
                }
            }
            return Ok(());
        }
        Err("aggregate match pattern has the wrong shape".into())
    }

    fn emit_aggregate_pattern(
        &mut self,
        pattern: &Expr,
        constructor: &str,
        ty: &Type,
        offset: usize,
        next: &str,
        bindings: &mut Vec<(String, usize, Type)>,
    ) -> Result<(), String> {
        if matches!(pattern, Expr::Symbol(name) if name == "_") {
            return Ok(());
        }
        if let Expr::List(parts) = pattern {
            if parts.len() >= 2 && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or")
            {
                let matched = self.label("aggregate_or_pattern_matched");
                for (index, alternative) in parts[1..].iter().enumerate() {
                    let last = index + 1 == parts.len() - 1;
                    let alternative_next = if last {
                        next.to_owned()
                    } else {
                        self.label("aggregate_or_pattern_next")
                    };
                    let mut alternative_bindings = Vec::new();
                    self.emit_aggregate_pattern(
                        alternative,
                        constructor,
                        ty,
                        offset,
                        &alternative_next,
                        &mut alternative_bindings,
                    )?;
                    if !alternative_bindings.is_empty() {
                        return Err("aggregate or-pattern alternatives cannot bind values".into());
                    }
                    self.output.push_str(&format!("    jmp {matched}\n"));
                    if !last {
                        self.output.push_str(&format!("{alternative_next}:\n"));
                    }
                }
                self.output.push_str(&format!("{matched}:\n"));
                return Ok(());
            }
        }
        let Expr::List(pattern) = pattern else {
            return Err("aggregate match pattern must be a constructor pattern".into());
        };
        if !matches!(pattern.first(), Some(Expr::Symbol(name)) if name == constructor) {
            return Err("aggregate match pattern has the wrong shape".into());
        }
        let fields = match ty {
            Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
            Type::Array(element, length) if constructor == "array" => {
                vec![element.as_ref().clone(); *length]
            }
            Type::Named(name) if constructor == name => self
                .structs
                .get(name)
                .ok_or_else(|| format!("unknown struct '{name}'"))?
                .iter()
                .map(|field| field.ty.clone())
                .collect(),
            _ => return Err("aggregate match pattern has the wrong type".into()),
        };
        if pattern.len() - 1 != fields.len() {
            return Err("aggregate match pattern has the wrong shape".into());
        }
        let mut field_offset = offset;
        for (field, field_type) in pattern[1..].iter().zip(fields) {
            if is_scalar_pattern_type(&field_type)
                && matches!(
                    field,
                    Expr::List(items)
                        if matches!(items.first(), Some(Expr::Symbol(name))
                            if matches!(name.as_str(), "or" | "range" | "literal"))
                )
            {
                let low_operand = format!("QWORD PTR [rsp+{}]", field_offset * 8);
                let high_operand = if is_wide_integer(&field_type) {
                    Some(format!("QWORD PTR [rsp+{}]", (field_offset + 1) * 8))
                } else {
                    None
                };
                self.emit_scalar_pattern_at(
                    field,
                    &field_type,
                    &low_operand,
                    high_operand.as_deref(),
                    next,
                )?;
                field_offset += storage_word_count(&field_type, &self.structs, &self.enums)?;
                continue;
            }
            let field = typed_integer_pattern_value(field, &field_type)?.unwrap_or(field);
            let field_words = storage_word_count(&field_type, &self.structs, &self.enums)?;
            let address = field_offset * 8;
            match field {
                Expr::Symbol(name) if name == "_" => {}
                Expr::Symbol(name) if name == "true" || name == "false" => {
                    if !matches!(&field_type, Type::Bool) || field_words != 1 {
                        return Err("boolean aggregate pattern has a non-boolean field".into());
                    }
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp+{address}], {}\n    jne {next}\n",
                        if name == "true" { 1 } else { 0 }
                    ));
                }
                Expr::Symbol(name) => {
                    bindings.push((name.clone(), field_offset, field_type.clone()))
                }
                Expr::Integer(value) => {
                    if field_words == 2 {
                        let bits = *value as u128;
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp+{address}], 0x{:016x}\n    jne {next}\n    cmp QWORD PTR [rsp+{}], 0x{:016x}\n    jne {next}\n",
                            bits as u64,
                            address + 8,
                            (bits >> 64) as u64
                        ));
                    } else if field_words == 1 {
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp+{address}], {value}\n    jne {next}\n"
                        ));
                    } else {
                        return Err("integer aggregate pattern has an unsupported width".into());
                    }
                }
                Expr::UnsignedInteger(value) => {
                    if field_words == 2 {
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp+{address}], 0x{:016x}\n    jne {next}\n    cmp QWORD PTR [rsp+{}], 0x{:016x}\n    jne {next}\n",
                            *value as u64,
                            address + 8,
                            (*value >> 64) as u64
                        ));
                    } else if field_words == 1 {
                        self.output.push_str(&format!(
                            "    cmp QWORD PTR [rsp+{address}], {}\n    jne {next}\n",
                            *value as u64
                        ));
                    } else {
                        return Err("integer aggregate pattern has an unsupported width".into());
                    }
                }
                Expr::Char(value) => {
                    if field_words != 1 {
                        return Err("wide character aggregate patterns are unsupported".into());
                    }
                    self.output.push_str(&format!(
                        "    cmp QWORD PTR [rsp+{address}], {}\n    jne {next}\n",
                        *value as u32
                    ));
                }
                Expr::List(_) => {
                    let nested_constructor = match field {
                        Expr::List(items) => match items.first() {
                            Some(Expr::Symbol(name)) => name.as_str(),
                            _ => {
                                return Err(
                                    "nested aggregate pattern must start with a constructor".into(),
                                )
                            }
                        },
                        _ => unreachable!(),
                    };
                    self.emit_aggregate_pattern(
                        field,
                        nested_constructor,
                        &field_type,
                        field_offset,
                        next,
                        bindings,
                    )?;
                }
                _ => return Err("unsupported aggregate field pattern".into()),
            }
            field_offset += field_words;
        }
        Ok(())
    }

    fn emit_let_else_enum_pattern(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        failure: &str,
        bindings: &mut Vec<(String, usize, Type)>,
    ) -> Result<(), String> {
        if matches!(pattern, Expr::Symbol(name) if name == "_") {
            return Ok(());
        }
        let Type::Named(enum_name) = ty else {
            return Err("let-else enum pattern requires a named enum".into());
        };
        let (variant_name, payload_patterns): (&str, Vec<&Expr>) = match pattern {
            Expr::Symbol(name) => (name, Vec::new()),
            Expr::List(items) if !items.is_empty() => {
                let Expr::Symbol(name) = &items[0] else {
                    return Err("let-else enum pattern must start with a variant".into());
                };
                (name, items[1..].iter().collect())
            }
            _ => return Err("let-else enum pattern must be a variant".into()),
        };
        let variants = self
            .enums
            .get(enum_name)
            .ok_or_else(|| format!("unknown enum '{enum_name}'"))?
            .clone();
        let variant_index = variants
            .iter()
            .position(|variant| variant.name == variant_name)
            .ok_or_else(|| format!("unknown enum variant '{variant_name}'"))?;
        let variant_fields = variants[variant_index].fields.clone();
        if payload_patterns.len() != variant_fields.len() {
            return Err(format!(
                "variant '{variant_name}' has the wrong payload count"
            ));
        }
        self.output.push_str(&format!(
            "    cmp QWORD PTR [rsp], {}\n    jne {failure}\n",
            variants[variant_index].discriminant
        ));
        let mut offset = 0;
        for (pattern, field_type) in payload_patterns.iter().zip(&variant_fields) {
            self.emit_enum_payload_pattern(pattern, field_type, offset, None, failure)?;
            self.collect_enum_pattern_bindings(pattern, field_type, offset, bindings)?;
            offset += storage_word_count(field_type, &self.structs, &self.enums)?;
        }
        Ok(())
    }

    fn emit_let_else_fieldless_enum_pattern(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        failure: &str,
    ) -> Result<(), String> {
        let Type::Named(enum_name) = ty else {
            return Err("fieldless enum let-else pattern requires a named enum".into());
        };
        let variants = self
            .enums
            .get(enum_name)
            .ok_or_else(|| format!("unknown enum '{enum_name}'"))?
            .clone();
        let alternatives: Vec<&Expr> = if let Expr::List(items) = pattern {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == "or") {
                items[1..].iter().collect()
            } else {
                vec![pattern]
            }
        } else {
            vec![pattern]
        };
        let matched = self.label("fieldless_let_else_matched");
        for alternative in alternatives {
            let Expr::Symbol(name) = alternative else {
                return Err("fieldless enum let-else pattern must be a variant".into());
            };
            let discriminant = variants
                .iter()
                .find(|variant| variant.name == *name)
                .map(|variant| variant.discriminant)
                .ok_or_else(|| format!("unknown enum variant '{name}'"))?;
            self.output.push_str(&format!(
                "    cmp QWORD PTR [rsp], {}\n    je {matched}\n",
                asm_u64_immediate(discriminant)
            ));
        }
        self.output
            .push_str(&format!("    jmp {failure}\n{matched}:\n"));
        Ok(())
    }

    fn emit_let_else_enum_or_pattern(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        failure: &str,
    ) -> Result<(), String> {
        let Type::Named(enum_name) = ty else {
            return Err("enum let-else or-pattern requires a named enum".into());
        };
        let variants = self
            .enums
            .get(enum_name)
            .ok_or_else(|| format!("unknown enum '{enum_name}'"))?
            .clone();
        let Expr::List(items) = pattern else {
            return Err("enum let-else or-pattern must be a list".into());
        };
        let matched = self.label("enum_let_else_or_matched");
        for (index, alternative) in items[1..].iter().enumerate() {
            let (variant_name, payload_patterns): (&str, Vec<&Expr>) = match alternative {
                Expr::Symbol(name) => (name, Vec::new()),
                Expr::List(items) if !items.is_empty() => {
                    let Expr::Symbol(name) = &items[0] else {
                        return Err("enum let-else alternatives must be variants".into());
                    };
                    (name, items[1..].iter().collect())
                }
                _ => return Err("enum let-else alternatives must be variants".into()),
            };
            let variant = variants
                .iter()
                .find(|variant| variant.name == variant_name)
                .ok_or_else(|| format!("unknown enum variant '{variant_name}'"))?;
            let alternative_next = if index + 1 == items.len() - 2 {
                failure.to_owned()
            } else {
                self.label("enum_let_else_or_next")
            };
            self.output.push_str(&format!(
                "    cmp QWORD PTR [rsp], {}\n    jne {alternative_next}\n",
                asm_u64_immediate(variant.discriminant)
            ));
            if !payload_patterns.is_empty() && payload_patterns.len() != variant.fields.len() {
                return Err(format!(
                    "variant '{variant_name}' expects {} payload patterns",
                    variant.fields.len()
                ));
            }
            let mut offset = 0;
            for (payload, field_type) in payload_patterns.iter().zip(&variant.fields) {
                self.emit_enum_payload_pattern(
                    payload,
                    field_type,
                    offset,
                    None,
                    &alternative_next,
                )?;
                offset += storage_word_count(field_type, &self.structs, &self.enums)?;
            }
            self.output.push_str(&format!("    jmp {matched}\n"));
            if index + 1 != items.len() - 2 {
                self.output.push_str(&format!("{alternative_next}:\n"));
            }
        }
        self.output.push_str(&format!("{matched}:\n"));
        Ok(())
    }

    fn emit_enum_payload_pattern(
        &mut self,
        pattern: &Expr,
        ty: &Type,
        offset: usize,
        payload_slots: Option<&Vec<usize>>,
        next: &str,
    ) -> Result<(), String> {
        if let Some(value) = typed_integer_pattern_value(pattern, ty)? {
            return self.emit_enum_payload_pattern(value, ty, offset, payload_slots, next);
        }
        let operand = |offset: usize| -> Result<String, String> {
            if let Some(payload_slots) = payload_slots {
                let slot = payload_slots.get(offset).ok_or_else(|| {
                    "enum payload pattern exceeds local payload storage".to_owned()
                })?;
                Ok(format!("QWORD PTR [rbp-{}]", slot * 8))
            } else {
                Ok(format!("QWORD PTR [rsp+{}]", (offset + 1) * 8))
            }
        };
        if let Expr::List(items) = pattern {
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "range")
            {
                let low_operand = operand(offset)?;
                let high_operand = if is_wide_integer(ty) {
                    Some(operand(offset + 1)?)
                } else {
                    None
                };
                return self.emit_scalar_pattern_at(
                    pattern,
                    ty,
                    &low_operand,
                    high_operand.as_deref(),
                    next,
                );
            }
            if items.len() >= 2 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or")
            {
                let matched = self.label("payload_or_pattern_matched");
                for (index, alternative) in items[1..].iter().enumerate() {
                    let last = index + 1 == items.len() - 1;
                    let alternative_next = if last {
                        next.to_owned()
                    } else {
                        self.label("payload_or_pattern_next")
                    };
                    let low_operand = operand(offset)?;
                    let high_operand = if is_wide_integer(ty) {
                        Some(operand(offset + 1)?)
                    } else {
                        None
                    };
                    self.emit_enum_scalar_pattern_test(
                        alternative,
                        ty,
                        &low_operand,
                        high_operand.as_deref(),
                        &alternative_next,
                    )?;
                    self.output.push_str(&format!("    jmp {matched}\n"));
                    if !last {
                        self.output.push_str(&format!("{alternative_next}:\n"));
                    }
                }
                self.output.push_str(&format!("{matched}:\n"));
                return Ok(());
            }
            let Some(Expr::Symbol(constructor)) = items.first() else {
                return Err("nested enum payload pattern must start with a constructor".into());
            };
            let fields = self.aggregate_pattern_fields(ty, constructor)?;
            if items.len() - 1 != fields.len() {
                return Err("nested enum payload pattern has the wrong shape".into());
            }
            let mut field_offset = offset;
            for (nested, field_type) in items[1..].iter().zip(fields) {
                self.emit_enum_payload_pattern(
                    nested,
                    &field_type,
                    field_offset,
                    payload_slots,
                    next,
                )?;
                field_offset += storage_word_count(&field_type, &self.structs, &self.enums)?;
            }
            return Ok(());
        }
        match pattern {
            Expr::Symbol(name) if name == "_" => Ok(()),
            Expr::Symbol(name) if name == "true" || name == "false" => {
                if !matches!(ty, Type::Bool) {
                    return Err("boolean enum payload pattern has a non-boolean type".into());
                }
                let value = if name == "true" { 1 } else { 0 };
                self.output.push_str(&format!(
                    "    cmp {}, {value}\n    jne {next}\n",
                    operand(offset)?
                ));
                Ok(())
            }
            Expr::Symbol(_) => Ok(()),
            Expr::Integer(value) => {
                let words = value_word_count(ty, &self.structs, &self.enums)?;
                if words == 2 {
                    let bits = *value as u128;
                    self.output.push_str(&format!(
                        "    cmp {}, 0x{:016x}\n    jne {next}\n    cmp {}, 0x{:016x}\n    jne {next}\n",
                        operand(offset)?,
                        bits as u64,
                        operand(offset + 1)?,
                        (bits >> 64) as u64
                    ));
                } else if words == 1 {
                    self.output.push_str(&format!(
                        "    cmp {}, {value}\n    jne {next}\n",
                        operand(offset)?
                    ));
                } else {
                    return Err("integer enum payload pattern has an unsupported width".into());
                }
                Ok(())
            }
            Expr::UnsignedInteger(value) => {
                let words = value_word_count(ty, &self.structs, &self.enums)?;
                if words == 2 {
                    self.output.push_str(&format!(
                        "    cmp {}, 0x{:016x}\n    jne {next}\n    cmp {}, 0x{:016x}\n    jne {next}\n",
                        operand(offset)?,
                        *value as u64,
                        operand(offset + 1)?,
                        (*value >> 64) as u64
                    ));
                } else if words == 1 {
                    self.output.push_str(&format!(
                        "    cmp {}, {}\n    jne {next}\n",
                        operand(offset)?,
                        *value as u64
                    ));
                } else {
                    return Err("integer enum payload pattern has an unsupported width".into());
                }
                Ok(())
            }
            Expr::Char(value) => {
                self.output.push_str(&format!(
                    "    cmp {}, {}\n    jne {next}\n",
                    operand(offset)?,
                    *value as u32
                ));
                Ok(())
            }
            _ => Err("unsupported enum payload pattern".into()),
        }
    }

    fn aggregate_pattern_fields(&self, ty: &Type, constructor: &str) -> Result<Vec<Type>, String> {
        match ty {
            Type::Tuple(fields) if constructor == "tuple" => Ok(fields.clone()),
            Type::Array(element, length) if constructor == "array" => {
                Ok(vec![element.as_ref().clone(); *length])
            }
            Type::Named(name) if constructor == name => self
                .structs
                .get(name)
                .map(|fields| fields.iter().map(|field| field.ty.clone()).collect())
                .ok_or_else(|| format!("unknown struct '{name}'")),
            _ => Err("aggregate pattern constructor does not match its payload type".into()),
        }
    }

    fn collect_enum_pattern_bindings(
        &self,
        pattern: &Expr,
        ty: &Type,
        offset: usize,
        bindings: &mut Vec<(String, usize, Type)>,
    ) -> Result<(), String> {
        if typed_integer_pattern_value(pattern, ty)?.is_some()
            || matches!(
                pattern,
                Expr::List(items)
                    if items.len() == 3
                        && matches!(items.first(), Some(Expr::Symbol(name)) if name == "range")
            )
        {
            return Ok(());
        }
        if matches!(pattern, Expr::List(items) if items.len() >= 2
            && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or"))
        {
            return Ok(());
        }
        if let Expr::List(items) = pattern {
            let Some(Expr::Symbol(constructor)) = items.first() else {
                return Err("nested enum payload pattern must start with a constructor".into());
            };
            let fields = self.aggregate_pattern_fields(ty, constructor)?;
            if items.len() - 1 != fields.len() {
                return Err("nested enum payload pattern has the wrong shape".into());
            }
            let mut field_offset = offset;
            for (nested, field_type) in items[1..].iter().zip(fields) {
                self.collect_enum_pattern_bindings(nested, &field_type, field_offset, bindings)?;
                field_offset += storage_word_count(&field_type, &self.structs, &self.enums)?;
            }
        } else if let Expr::Symbol(name) = pattern {
            if name != "_" && name != "true" && name != "false" {
                bindings.push((name.clone(), offset, ty.clone()));
            }
        }
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
        variants
            .iter()
            .map(|variant| {
                variant
                    .fields
                    .iter()
                    .map(|field| storage_word_count(field, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()
                    .map(|words| words.into_iter().sum::<usize>())
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|words| words.into_iter().max().unwrap_or(0))
    }

    fn is_enum_type(&self, ty: &Type) -> bool {
        matches!(ty, Type::Named(name) if self.enums.contains_key(name))
    }

    fn unary_negate(
        &mut self,
        items: &[Expr],
        qualifier: Option<&str>,
        mode: Option<&str>,
    ) -> Result<(), String> {
        let operand_type = qualifier
            .map(Type::from_name)
            .or_else(|| self.expression_type(&items[1]));
        if operand_type.as_ref().is_some_and(is_wide_integer) {
            self.expression(&items[1])?;
            if mode == Some("saturate") {
                if operand_type == Some(Type::U128) {
                    self.output.push_str("    xor eax, eax\n    xor edx, edx\n");
                } else {
                    let done = self.label("saturating_negate_done");
                    let normal = self.label("saturating_negate_normal");
                    self.output.push_str(&format!(
                        "    cmp rdx, 0x8000000000000000\n    jne {normal}\n    test rax, rax\n    jne {normal}\n    mov rax, 0xffffffffffffffff\n    mov rdx, 0x7fffffffffffffff\n    jmp {done}\n{normal}:\n    neg rax\n    sbb rdx, 0\n{done}:\n"
                    ));
                }
            } else {
                self.output.push_str("    neg rax\n    sbb rdx, 0\n");
            }
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
            if mode == Some("saturate") {
                self.emit_saturating_integer_result("-", qualifier, items)?;
            }
            if let Some(ty) = operand_type.as_ref() {
                if is_narrow_integer(ty) {
                    self.normalize_integer(ty)?;
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
            if let Expr::List(call_items) = &items[1] {
                if let Some(Expr::Symbol(function_name)) = call_items.first() {
                    if self
                        .functions
                        .get(function_name)
                        .is_some_and(|function| function.indirect_return)
                    {
                        let field_words =
                            value_word_count(&field_type, &self.structs, &self.enums)?;
                        if field_words > VALUE_REGISTERS.len() {
                            return Err("direct large tuple access exceeds value registers".into());
                        }
                        let offset = fields[..index]
                            .iter()
                            .map(|field| value_word_count(field, &self.structs, &self.enums))
                            .collect::<Result<Vec<_>, _>>()?
                            .into_iter()
                            .sum::<usize>();
                        let base = self.call_to_aggregate_temp(function_name, &call_items[1..])?;
                        self.load_aggregate_temp_value(base, offset, &field_type)?;
                        return Ok(());
                    }
                }
            }
            if let Expr::List(constructor) = &items[1] {
                if matches!(constructor.first(), Some(Expr::Symbol(name)) if name == "tuple") {
                    let value = constructor
                        .get(index + 2)
                        .ok_or_else(|| "tuple constructor has too few fields".to_owned())?;
                    let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                    if field_words > 1 {
                        self.push_value_words(value, &field_type, false)?;
                        for register in VALUE_REGISTERS[..field_words].iter().rev() {
                            self.output.push_str(&format!("    pop {register}\n"));
                            self.stack_depth -= 1;
                        }
                        return Ok(());
                    }
                    return self.expression_as_expected(value, &field_type);
                }
            }
            if let Expr::Symbol(local) = &items[1] {
                if matches!(self.global_types.get(local), Some(Type::Tuple(_))) {
                    if !matches!(self.globals.get(local), Some(GlobalValue::Aggregate(_))) {
                        return Err(format!("global '{local}' is not an aggregate tuple"));
                    }
                    let offset_words = fields[..index]
                        .iter()
                        .map(|field| value_word_count(field, &self.structs, &self.enums))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .sum::<usize>();
                    let offset = offset_words * 8;
                    let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                    if field_words > 1 {
                        for (word, register) in VALUE_REGISTERS[..field_words].iter().enumerate() {
                            self.load_global_word(local, offset_words + word)?;
                            self.output.push_str(&format!("    mov {register}, rax\n"));
                        }
                        return Ok(());
                    }
                    match field_type {
                        Type::F32 => self.output.push_str(&format!(
                            "    movss xmm0, DWORD PTR [rip+{}+{offset}]\n",
                            asm_symbol(local)
                        )),
                        Type::F64 => self.output.push_str(&format!(
                            "    movq xmm0, QWORD PTR [rip+{}+{offset}]\n",
                            asm_symbol(local)
                        )),
                        _ => self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rip+{}+{offset}]\n",
                            asm_symbol(local)
                        )),
                    }
                    return Ok(());
                }
                let Storage::Tuple(slots) = self
                    .locals
                    .get(local)
                    .ok_or_else(|| format!("unknown tuple local '{local}'"))?
                else {
                    return Err(format!("'{local}' is not a tuple"));
                };
                let slot_index = fields[..index]
                    .iter()
                    .map(|field| value_word_count(field, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                let slot = *slots
                    .get(slot_index)
                    .ok_or_else(|| "native tuple has too many fields".to_owned())?;
                let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                if field_words > 1 {
                    for (word, register) in VALUE_REGISTERS[..field_words].iter().enumerate() {
                        let source_slot = slots
                            .get(slot_index + word)
                            .ok_or_else(|| "native tuple has too many fields".to_owned())?;
                        self.output.push_str(&format!(
                            "    mov {register}, QWORD PTR [rbp-{}]\n",
                            source_slot * 8
                        ));
                    }
                    return Ok(());
                }
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
                let register_index = fields[..index]
                    .iter()
                    .map(|field| value_word_count(field, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                self.expression_as_expected(&items[1], &Type::Tuple(fields.clone()))?;
                if field_words > 1 {
                    for (word, destination) in VALUE_REGISTERS.iter().enumerate().take(field_words)
                    {
                        let source = VALUE_REGISTERS
                            .get(register_index + word)
                            .ok_or_else(|| "native tuple has too many fields".to_owned())?;
                        if *source != *destination {
                            self.output
                                .push_str(&format!("    mov {destination}, {source}\n"));
                        }
                    }
                    return Ok(());
                }
                let register = VALUE_REGISTERS
                    .get(register_index)
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
        if let Some(Type::Reference { target, .. }) = self.expression_type(&items[1]) {
            let Type::Named(struct_name) = *target else {
                return Err("named field access through a reference requires a struct".into());
            };
            let fields = self
                .structs
                .get(&struct_name)
                .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
            let index = fields
                .iter()
                .position(|field| field.name == *field_name)
                .ok_or_else(|| format!("struct '{struct_name}' has no field '{field_name}'"))?;
            let field_type = fields[index].ty.clone();
            let offset_words = fields[..index]
                .iter()
                .map(|field| storage_word_count(&field.ty, &self.structs, &self.enums))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .sum::<usize>();
            let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
            if field_words > VALUE_REGISTERS.len() {
                return Err("large fields projected through references are unsupported".into());
            }
            self.emit_reference_field_address(&items[1], offset_words, false)?;
            if field_words > 1 {
                for (word, register) in VALUE_REGISTERS.iter().enumerate().take(field_words) {
                    self.output.push_str(&format!(
                        "    mov {register}, QWORD PTR [rax+{}]\n",
                        word * 8
                    ));
                }
            } else {
                match field_type {
                    Type::F32 => self.output.push_str("    movss xmm0, DWORD PTR [rax]\n"),
                    Type::F64 => self.output.push_str("    movq xmm0, QWORD PTR [rax]\n"),
                    _ => self.output.push_str("    mov rax, QWORD PTR [rax]\n"),
                }
            }
            return Ok(());
        }
        match &items[1] {
            Expr::Symbol(local) => {
                if let Some(Type::Named(struct_name)) = self.global_types.get(local) {
                    let fields = self
                        .structs
                        .get(struct_name)
                        .ok_or_else(|| format!("'{local}' is not a struct"))?;
                    let (index, field_type) = fields
                        .iter()
                        .enumerate()
                        .find(|(_, field)| field.name == *field_name)
                        .map(|(index, field)| (index, field.ty.clone()))
                        .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                    if !matches!(self.globals.get(local), Some(GlobalValue::Aggregate(_))) {
                        return Err(format!("global '{local}' is not an aggregate struct"));
                    }
                    let offset_words = fields[..index]
                        .iter()
                        .map(|field| value_word_count(&field.ty, &self.structs, &self.enums))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .sum::<usize>();
                    let offset = offset_words * 8;
                    let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                    if field_words > 1 {
                        for (word, register) in VALUE_REGISTERS[..field_words].iter().enumerate() {
                            self.load_global_word(local, offset_words + word)?;
                            self.output.push_str(&format!("    mov {register}, rax\n"));
                        }
                        return Ok(());
                    }
                    if matches!(field_type, Type::F32) {
                        self.output.push_str(&format!(
                            "    movss xmm0, DWORD PTR [rip+{}+{offset}]\n",
                            asm_symbol(local)
                        ));
                    } else if matches!(field_type, Type::F64) {
                        self.output.push_str(&format!(
                            "    movq xmm0, QWORD PTR [rip+{}+{offset}]\n",
                            asm_symbol(local)
                        ));
                    } else {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rip+{}+{offset}]\n",
                            asm_symbol(local)
                        ));
                    }
                    return Ok(());
                }
                let Storage::Struct(fields) = self
                    .locals
                    .get(local)
                    .ok_or_else(|| format!("unknown local '{local}'"))?
                    .clone()
                else {
                    return Err(format!("'{local}' is not a struct"));
                };
                let slot = fields
                    .iter()
                    .find(|(name, _)| name == field_name)
                    .map(|(_, slots)| slots.clone())
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
                let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                if field_words > 1 {
                    for (word, register) in VALUE_REGISTERS[..field_words].iter().enumerate() {
                        let source_slot = slot
                            .get(word)
                            .ok_or_else(|| "native struct has too many fields".to_owned())?;
                        self.output.push_str(&format!(
                            "    mov {register}, QWORD PTR [rbp-{}]\n",
                            source_slot * 8
                        ));
                    }
                    return Ok(());
                }
                let slot = slot[0];
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
                let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                if field_words > 1 {
                    self.push_value_words(value, &field_type, false)?;
                    for register in VALUE_REGISTERS[..field_words].iter().rev() {
                        self.output.push_str(&format!("    pop {register}\n"));
                        self.stack_depth -= 1;
                    }
                    return Ok(());
                }
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
                if let Expr::List(call_items) = &items[1] {
                    if let Some(Expr::Symbol(function_name)) = call_items.first() {
                        if self
                            .functions
                            .get(function_name)
                            .is_some_and(|function| function.indirect_return)
                        {
                            let field_type = fields[index].ty.clone();
                            let field_words =
                                value_word_count(&field_type, &self.structs, &self.enums)?;
                            if field_words > VALUE_REGISTERS.len() {
                                return Err(
                                    "direct large struct access exceeds value registers".into()
                                );
                            }
                            let offset = fields[..index]
                                .iter()
                                .map(|field| {
                                    value_word_count(&field.ty, &self.structs, &self.enums)
                                })
                                .collect::<Result<Vec<_>, _>>()?
                                .into_iter()
                                .sum::<usize>();
                            let base =
                                self.call_to_aggregate_temp(function_name, &call_items[1..])?;
                            self.load_aggregate_temp_value(base, offset, &field_type)?;
                            return Ok(());
                        }
                    }
                }
                self.expression_as_expected(&items[1], &Type::Named(struct_name.clone()))?;
                let field_type = fields[index].ty.clone();
                let register_index = fields[..index]
                    .iter()
                    .map(|field| value_word_count(&field.ty, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
                if field_words > 1 {
                    for (word, destination) in VALUE_REGISTERS.iter().enumerate().take(field_words)
                    {
                        let source =
                            VALUE_REGISTERS.get(register_index + word).ok_or_else(|| {
                                "native returned struct has too many fields".to_owned()
                            })?;
                        if *source != *destination {
                            self.output
                                .push_str(&format!("    mov {destination}, {source}\n"));
                        }
                    }
                    return Ok(());
                }
                let register = VALUE_REGISTERS
                    .get(register_index)
                    .ok_or_else(|| "native returned struct has too many fields".to_owned())?;
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

    fn enum_payload_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 4 {
            return Err("get-payload requires an enum, variant, and index".into());
        }
        let Type::Reference { target, .. } = self
            .expression_type(&items[1])
            .ok_or_else(|| "get-payload has no known source type".to_owned())?
        else {
            return Err("get-payload currently requires an enum reference".into());
        };
        let Type::Named(enum_name) = *target else {
            return Err("get-payload requires a reference to an enum".into());
        };
        let Expr::Symbol(variant_name) = &items[2] else {
            return Err("get-payload requires a variant name".into());
        };
        let index =
            match &items[3] {
                Expr::Integer(index) if *index >= 0 => usize::try_from(*index)
                    .map_err(|_| "enum payload index is too large".to_owned())?,
                Expr::UnsignedInteger(index) => usize::try_from(*index)
                    .map_err(|_| "enum payload index is too large".to_owned())?,
                _ => return Err("get-payload requires a non-negative integer index".into()),
            };
        let variant = self
            .enums
            .get(&enum_name)
            .ok_or_else(|| format!("unknown enum '{enum_name}'"))?
            .iter()
            .find(|variant| variant.name == *variant_name)
            .cloned()
            .ok_or_else(|| format!("unknown enum variant '{variant_name}'"))?;
        let field_type = variant.fields.get(index).cloned().ok_or_else(|| {
            format!("variant '{variant_name}' has no payload field at index {index}")
        })?;
        let payload_offset = 1 + variant.fields[..index]
            .iter()
            .map(|field| storage_word_count(field, &self.structs, &self.enums))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .sum::<usize>();
        let inactive = self.label("inactive_enum_payload_projection");
        let done = self.label("inactive_enum_payload_projection_done");
        self.expression(&items[1])?;
        self.output.push_str(&format!(
            "    and rax, -2\n    mov rcx, QWORD PTR [rax]\n    cmp rcx, {}\n    jne {inactive}\n",
            variant.discriminant
        ));
        self.emit_reference_field_address(&items[1], payload_offset, false)?;
        let field_words = value_word_count(&field_type, &self.structs, &self.enums)?;
        if field_words > VALUE_REGISTERS.len() {
            return Err("large enum payload projections are unsupported".into());
        }
        if field_words > 1 {
            for (word, register) in VALUE_REGISTERS.iter().enumerate().take(field_words) {
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [rax+{}]\n",
                    word * 8
                ));
            }
        } else if matches!(field_type, Type::F32) {
            self.output.push_str("    movss xmm0, DWORD PTR [rax]\n");
        } else if matches!(field_type, Type::F64) {
            self.output.push_str("    movq xmm0, QWORD PTR [rax]\n");
        } else {
            self.output.push_str("    mov rax, QWORD PTR [rax]\n");
        }
        self.output
            .push_str(&format!("    jmp {done}\n{inactive}:\n    ud2\n{done}:\n"));
        Ok(())
    }

    fn cell_place_address(&mut self, place: &Expr) -> Result<Type, String> {
        let ty = self
            .expression_type(place)
            .ok_or_else(|| "cell operation requires a cell place".to_owned())?;
        let Type::Cell(inner) = ty else {
            return Err("cell operation requires a cell place".into());
        };
        match place {
            Expr::Symbol(name) => {
                let slots = local_slots(&self.locals, name)?;
                let slot = slots
                    .first()
                    .ok_or_else(|| format!("cell '{name}' has no storage"))?;
                self.output
                    .push_str(&format!("    lea rax, [rbp-{}]\n", slot * 8));
            }
            Expr::List(items)
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "get")
                    && items.len() == 3 =>
            {
                let Expr::Symbol(field_name) = &items[2] else {
                    return Err("cell field projection requires a named field".into());
                };
                let base_type = self
                    .expression_type(&items[1])
                    .ok_or_else(|| "cell field base has no known type".to_owned())?;
                let (struct_name, is_reference) = match base_type {
                    Type::Reference { target, .. } => match *target {
                        Type::Named(name) => (name, true),
                        _ => return Err("cell field reference must target a struct".into()),
                    },
                    Type::Named(name) => (name, false),
                    _ => return Err("cell field base must be a struct".into()),
                };
                let fields = self
                    .structs
                    .get(&struct_name)
                    .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
                let index = fields
                    .iter()
                    .position(|field| field.name == *field_name)
                    .ok_or_else(|| format!("struct '{struct_name}' has no field '{field_name}'"))?;
                let offset_words = fields[..index]
                    .iter()
                    .map(|field| storage_word_count(&field.ty, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                if is_reference {
                    self.emit_reference_field_address(&items[1], offset_words, false)?;
                } else if let Expr::Symbol(local) = &items[1] {
                    if let Some(Storage::Struct(slots)) = self.locals.get(local) {
                        let slot = slots
                            .get(index)
                            .and_then(|(_, slots)| slots.first())
                            .ok_or_else(|| "cell field has no storage".to_owned())?;
                        self.output
                            .push_str(&format!("    lea rax, [rbp-{}]\n", slot * 8));
                    } else if self.globals.contains_key(local) {
                        self.output.push_str(&format!(
                            "    lea rax, [rip+{}+{}]\n",
                            asm_symbol(local),
                            offset_words * 8
                        ));
                    } else {
                        return Err(format!("unknown cell field base '{local}'"));
                    }
                } else {
                    return Err("cell field base must be a struct variable".into());
                }
            }
            _ => return Err("cell operations require a cell local or struct field".into()),
        }
        Ok(*inner)
    }

    fn cell_get_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 2 {
            return Err("cell-get requires one cell place".into());
        }
        let inner = self.cell_place_address(&items[1])?;
        match inner {
            Type::F32 => self.output.push_str("    movss xmm0, DWORD PTR [rax]\n"),
            Type::F64 => self.output.push_str("    movq xmm0, QWORD PTR [rax]\n"),
            _ => self.output.push_str("    mov rax, QWORD PTR [rax]\n"),
        }
        Ok(())
    }

    fn cell_set_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err("cell-set requires a cell place and value".into());
        }
        let inner = self.cell_place_address(&items[1])?;
        self.output.push_str("    push rax\n");
        self.stack_depth += 1;
        self.expression_as_expected(&items[2], &inner)?;
        self.output.push_str("    pop r11\n");
        self.stack_depth -= 1;
        match inner {
            Type::F32 => self.output.push_str("    movss DWORD PTR [r11], xmm0\n"),
            Type::F64 => self.output.push_str("    movq QWORD PTR [r11], xmm0\n"),
            _ => self.output.push_str("    mov QWORD PTR [r11], rax\n"),
        }
        self.output.push_str("    xor eax, eax\n");
        Ok(())
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
            Type::Unit | Type::Never => Ok(1),
            Type::I128 | Type::U128 => Ok(8),
            Type::Array(element, _) => self.native_type_align(element),
            Type::Tuple(fields) => Ok(fields
                .iter()
                .map(|field| self.native_type_align(field))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .max()
                .unwrap_or(1)),
            Type::Named(name) => {
                if let Some(fields) = self.structs.get(name) {
                    return Ok(fields
                        .iter()
                        .map(|field| self.native_type_align(&field.ty))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .max()
                        .unwrap_or(1));
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
            Type::Unit | Type::Never => Ok(0),
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

    fn binary_operator(
        &mut self,
        operator: &str,
        qualifier: Option<&str>,
        mode: Option<&str>,
        items: &[Expr],
    ) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("operator '{operator}' requires two operands"));
        }
        let operand_type = qualifier.map(Type::from_name);
        if operand_type.as_ref().is_some_and(is_float_type) || self.expression_is_float(&items[1]) {
            return self.float_binary_operator(operator, items);
        }
        if operand_type.as_ref().is_some_and(is_wide_integer)
            || self
                .expression_type(&items[1])
                .is_some_and(|ty| is_wide_integer(&ty))
        {
            return self.wide_binary_operator(operator, mode, items);
        }
        self.expression(&items[1])?;
        self.push_rax();
        self.expression(&items[2])?;
        self.output.push_str("    mov rcx, rax\n    pop rax\n");
        self.stack_depth -= 1;
        let division_by_zero = if matches!(operator, "/" | "%") {
            let trap = self.label("division_by_zero");
            let nonzero = self.label("division_nonzero");
            self.output.push_str(&format!(
                "    test rcx, rcx\n    jne {nonzero}\n    jmp {trap}\n{nonzero}:\n"
            ));
            Some(trap)
        } else {
            None
        };
        let shift_failure = if matches!(operator, "<<" | ">>") {
            let width = operand_type
                .clone()
                .or_else(|| self.expression_type(&items[1]))
                .and_then(integer_bit_width)
                .ok_or_else(|| "shift requires an integer operand".to_owned())?;
            let label = self.label("shift_failure");
            self.output
                .push_str(&format!("    cmp rcx, {width}\n    jae {label}\n"));
            Some(label)
        } else {
            None
        };
        let native_operand_type = operand_type
            .clone()
            .or_else(|| self.expression_type(&items[1]));
        let signed_division_overflow = if matches!(mode, Some("wrap") | Some("saturate"))
            && matches!(operator, "/" | "%")
            && native_operand_type
                .as_ref()
                .is_some_and(|ty| matches!(ty, Type::I64 | Type::Isize))
        {
            let normal = self.label("wrapping_division_normal");
            let done = self.label("wrapping_division_done");
            self.output.push_str(&format!(
                "    mov r8, 0x8000000000000000\n    cmp rax, r8\n    jne {normal}\n    cmp rcx, -1\n    jne {normal}\n"
            ));
            if operator == "/" {
                let result = if mode == Some("saturate") {
                    "0x7fffffffffffffff"
                } else {
                    "0x8000000000000000"
                };
                self.output.push_str(&format!(
                    "    mov rax, {result}\n    jmp {done}\n{normal}:\n"
                ));
            } else {
                self.output
                    .push_str(&format!("    xor eax, eax\n    jmp {done}\n{normal}:\n"));
            }
            Some(done)
        } else {
            None
        };
        match operator {
            "+" => self.output.push_str("    add rax, rcx\n"),
            "-" => self.output.push_str("    sub rax, rcx\n"),
            "*" => {
                if mode == Some("saturate")
                    && (operand_type.as_ref().is_some_and(is_unsigned_type)
                        || self.expression_is_unsigned(&items[1]))
                {
                    self.output.push_str("    mul rcx\n");
                } else {
                    self.output.push_str("    imul rax, rcx\n");
                }
            }
            "/" => {
                if operand_type.as_ref().is_some_and(is_unsigned_type)
                    || self.expression_is_unsigned(&items[1])
                {
                    self.output.push_str("    xor edx, edx\n    div rcx\n");
                } else {
                    self.output.push_str("    cqo\n    idiv rcx\n");
                }
            }
            "%" => {
                if operand_type.as_ref().is_some_and(is_unsigned_type)
                    || self.expression_is_unsigned(&items[1])
                {
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
                if operand_type.as_ref().is_some_and(is_unsigned_type)
                    || self.expression_is_unsigned(&items[1])
                {
                    self.output.push_str("    shr rax, cl\n");
                } else {
                    self.output.push_str("    sar rax, cl\n");
                }
            }
            _ => unreachable!(),
        }
        let skip_saturating_division = mode == Some("saturate")
            && matches!(operator, "/" | "%")
            && native_operand_type
                .as_ref()
                .is_some_and(|ty| matches!(ty, Type::I64 | Type::Isize));
        if mode == Some("saturate") && !skip_saturating_division {
            self.emit_saturating_integer_result(operator, qualifier, items)?;
        }
        if let Some(ty) = operand_type.or_else(|| self.expression_type(&items[1])) {
            if is_narrow_integer(&ty) {
                self.normalize_integer(&ty)?;
            }
        }
        if let Some(label) = shift_failure {
            let done = self.label("shift_done");
            self.output
                .push_str(&format!("    jmp {done}\n{label}:\n    ud2\n{done}:\n"));
        }
        if let Some(done) = signed_division_overflow {
            self.output.push_str(&format!("{done}:\n"));
        }
        if let Some(trap) = division_by_zero {
            let done = self.label("division_done");
            self.output
                .push_str(&format!("    jmp {done}\n{trap}:\n    ud2\n{done}:\n"));
        }
        Ok(())
    }

    fn emit_saturating_integer_result(
        &mut self,
        operator: &str,
        qualifier: Option<&str>,
        items: &[Expr],
    ) -> Result<(), String> {
        let ty = qualifier
            .map(Type::from_name)
            .or_else(|| self.expression_type(&items[1]))
            .ok_or_else(|| "saturating arithmetic requires a typed operand".to_owned())?;
        let Some((minimum, maximum)) = integer_bounds(&ty) else {
            return Err("saturating arithmetic requires an integer operand".into());
        };
        let minimum = asm_integer_bound(minimum, &ty);
        let maximum = asm_integer_bound(maximum, &ty);
        let high = self.label("saturate_high");
        let low = self.label("saturate_low");
        let overflow = self.label("saturate_overflow");
        let done = self.label("saturate_done");
        if is_unsigned_type(&ty) {
            if matches!(operator, "+" | "-" | "*") {
                let overflow = if operator == "-" {
                    low.clone()
                } else {
                    high.clone()
                };
                self.output.push_str(&format!("    jc {overflow}\n"));
            }
            self.output.push_str(&format!(
                "    cmp rax, {maximum}\n    ja {high}\n    jmp {done}\n{high}:\n    mov rax, {maximum}\n    jmp {done}\n{low}:\n    xor eax, eax\n{done}:\n"
            ));
        } else {
            self.output.push_str(&format!(
                "    jo {overflow}\n    cmp rax, {maximum}\n    jg {high}\n    cmp rax, {minimum}\n    jl {low}\n    jmp {done}\n{overflow}:\n    js {high}\n    jmp {low}\n{high}:\n    mov rax, {maximum}\n    jmp {done}\n{low}:\n    mov rax, {minimum}\n{done}:\n"
            ));
        }
        Ok(())
    }

    fn wide_binary_operator(
        &mut self,
        operator: &str,
        mode: Option<&str>,
        items: &[Expr],
    ) -> Result<(), String> {
        if mode == Some("saturate") && !matches!(operator, "+" | "-" | "*" | "/" | "%") {
            return Err(format!(
                "saturating 128-bit operator '{operator}' is unsupported"
            ));
        }
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
        if mode == Some("saturate") && matches!(operator, "+" | "-") {
            let unsigned = self
                .expression_type(&items[1])
                .is_some_and(|ty| matches!(ty, Type::U128));
            self.emit_wide_saturating_add_sub(operator, unsigned);
            return Ok(());
        }
        if mode == Some("saturate") && operator == "*" {
            let unsigned = self
                .expression_type(&items[1])
                .is_some_and(|ty| matches!(ty, Type::U128));
            if unsigned {
                self.emit_wide_saturating_unsigned_multiply();
            } else {
                self.emit_wide_saturating_signed_multiply();
            }
            return Ok(());
        }
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
            let division_by_zero = self.label("wide_division_by_zero");
            let division_nonzero = self.label("wide_division_nonzero");
            let division_done = self.label("wide_division_done");
            self.output.push_str(&format!(
                "    test rcx, rcx\n    jne {division_nonzero}\n    test r8, r8\n    jne {division_nonzero}\n    jmp {division_by_zero}\n{division_nonzero}:\n"
            ));
            let unsigned = self
                .expression_type(&items[1])
                .is_some_and(|ty| matches!(ty, Type::U128));
            let saturating_division = mode == Some("saturate") && !unsigned;
            let done = if saturating_division {
                let normal = self.label("wide_saturating_division_normal");
                let done = self.label("wide_saturating_division_done");
                self.output.push_str(&format!(
                    "    mov r9, 0x8000000000000000\n    cmp rdx, r9\n    jne {normal}\n    test rax, rax\n    jne {normal}\n    cmp r8, -1\n    jne {normal}\n    cmp rcx, -1\n    jne {normal}\n"
                ));
                if operator == "/" {
                    self.output.push_str(&format!(
                        "    mov rax, -1\n    mov rdx, 0x7fffffffffffffff\n    jmp {done}\n{normal}:\n"
                    ));
                } else {
                    self.output.push_str(&format!(
                        "    xor eax, eax\n    xor edx, edx\n    jmp {done}\n{normal}:\n"
                    ));
                }
                Some(done)
            } else {
                None
            };
            self.wide_division(operator, !unsigned)?;
            if let Some(done) = done {
                self.output.push_str(&format!("{done}:\n"));
            }
            self.output.push_str(&format!(
                "    jmp {division_done}\n{division_by_zero}:\n    ud2\n{division_done}:\n"
            ));
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

    fn emit_wide_saturating_add_sub(&mut self, operator: &str, unsigned: bool) {
        let high = self.label("wide_saturate_high");
        let low = self.label("wide_saturate_low");
        let overflow = self.label("wide_saturate_overflow");
        let done = self.label("wide_saturate_done");
        if unsigned {
            if operator == "+" {
                self.output.push_str(&format!(
                    "    add rax, rcx\n    adc rdx, r8\n    jc {high}\n    jmp {done}\n{high}:\n    mov rax, -1\n    mov rdx, -1\n    jmp {done}\n"
                ));
            } else {
                self.output.push_str(&format!(
                    "    sub rax, rcx\n    sbb rdx, r8\n    jc {low}\n    jmp {done}\n{low}:\n    xor eax, eax\n    xor edx, edx\n    jmp {done}\n"
                ));
            }
        } else if operator == "+" {
            self.output.push_str(&format!(
                "    mov r9, rdx\n    add rax, rcx\n    adc rdx, r8\n    mov r10, r9\n    xor r10, r8\n    js {done}\n    mov r10, r9\n    xor r10, rdx\n    jns {done}\n    jmp {overflow}\n{overflow}:\n    test rdx, rdx\n    js {high}\n    jmp {low}\n{high}:\n    mov rax, 0xffffffffffffffff\n    mov rdx, 0x7fffffffffffffff\n    jmp {done}\n{low}:\n    xor eax, eax\n    mov rdx, 0x8000000000000000\n"
            ));
        } else {
            self.output.push_str(&format!(
                "    mov r9, rdx\n    mov r10, r8\n    sub rax, rcx\n    sbb rdx, r8\n    mov r11, r9\n    xor r11, r10\n    js {overflow}\n    jmp {done}\n{overflow}:\n    mov r11, r9\n    xor r11, rdx\n    jns {done}\n    test rdx, rdx\n    js {high}\n    jmp {low}\n{high}:\n    mov rax, 0xffffffffffffffff\n    mov rdx, 0x7fffffffffffffff\n    jmp {done}\n{low}:\n    xor eax, eax\n    mov rdx, 0x8000000000000000\n"
            ));
        }
        self.output.push_str(&format!("{done}:\n"));
    }

    fn emit_wide_saturating_unsigned_multiply(&mut self) {
        let overflow = self.label("wide_saturate_mul_overflow");
        let done = self.label("wide_saturate_mul_done");
        self.output.push_str(&format!(
            "    sub rsp, 16\n    mov QWORD PTR [rsp], rax\n    mov QWORD PTR [rsp+8], rdx\n    mul rcx\n    mov r9, rax\n    mov r10, rdx\n    mov rax, QWORD PTR [rsp+8]\n    mul rcx\n    test rdx, rdx\n    jnz {overflow}\n    add r10, rax\n    jc {overflow}\n    mov rax, QWORD PTR [rsp]\n    mul r8\n    test rdx, rdx\n    jnz {overflow}\n    add r10, rax\n    jc {overflow}\n    mov rax, QWORD PTR [rsp+8]\n    mul r8\n    or rax, rdx\n    jnz {overflow}\n    mov rax, r9\n    mov rdx, r10\n    add rsp, 16\n    jmp {done}\n{overflow}:\n    add rsp, 16\n    mov rax, -1\n    mov rdx, -1\n{done}:\n"
        ));
    }

    fn emit_wide_saturating_signed_multiply(&mut self) {
        let multiplication_overflow = self.label("wide_saturate_signed_mul_overflow");
        let bound_overflow = self.label("wide_saturate_signed_mul_bound_overflow");
        let positive = self.label("wide_saturate_signed_mul_positive");
        let negative_path = self.label("wide_saturate_signed_mul_negative");
        let negative_clamp = self.label("wide_saturate_signed_mul_negative_clamp");
        let done = self.label("wide_saturate_signed_mul_done");
        let product = self.label("wide_saturate_signed_mul_product");
        let within = self.label("wide_saturate_signed_mul_within");
        let assembly = format!(
            r#"    mov r11, rdx
    xor r11, r8
    shr r11, 63
    mov r9, rdx
    sar r9, 63
    xor rax, r9
    xor rdx, r9
    sub rax, r9
    sbb rdx, r9
    mov r10, r8
    sar r10, 63
    xor rcx, r10
    xor r8, r10
    sub rcx, r10
    sbb r8, r10
    sub rsp, 16
    mov QWORD PTR [rsp], rax
    mov QWORD PTR [rsp+8], rdx
    mul rcx
    mov r9, rax
    mov r10, rdx
    mov rax, QWORD PTR [rsp+8]
    mul rcx
    test rdx, rdx
    jnz {multiplication_overflow}
    add r10, rax
    jc {multiplication_overflow}
    mov rax, QWORD PTR [rsp]
    mul r8
    test rdx, rdx
    jnz {multiplication_overflow}
    add r10, rax
    jc {multiplication_overflow}
    mov rax, QWORD PTR [rsp+8]
    mul r8
    or rax, rdx
    jnz {multiplication_overflow}
    mov rax, r9
    mov rdx, r10
    jmp {product}
{multiplication_overflow}:
    mov rax, 1
    mov rdx, 0x8000000000000000
{product}:
    add rsp, 16
    test r11, r11
    jnz {negative_path}
    jmp {positive}
{positive}:
    bt rdx, 63
    jc {bound_overflow}
    jmp {within}
{negative_path}:
    mov r9, 0x8000000000000000
    cmp rdx, r9
    ja {bound_overflow}
    jne {within}
    test rax, rax
    jnz {bound_overflow}
{within}:
    jmp {done}
{bound_overflow}:
    test r11, r11
    jnz {negative_clamp}
    mov rax, 0xffffffffffffffff
    mov rdx, 0x7fffffffffffffff
    jmp {done}
{negative_clamp}:
    xor eax, eax
    mov rdx, 0x8000000000000000
{done}:
"#,
        );
        self.output.push_str(&assembly);
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
            "    sub rsp, 16\n    {store} {memory} PTR [rsp], xmm1\n    {store} {memory} PTR [rsp+8], xmm0\n    fld {memory} PTR [rsp+8]\n    fld {memory} PTR [rsp]\n{loop_label}:\n    fprem\n    fstsw ax\n    test ah, 4\n    jnz {loop_label}\n    fstp {memory} PTR [rsp]\n    fstp st(0)\n    {load} xmm0, {memory} PTR [rsp]\n    add rsp, 16\n"
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
                "jne",
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
        if let Some(ty) = self.expression_type(expression) {
            return is_unsigned_type(&ty);
        }
        match expression {
            Expr::Symbol(name) => self.local_types.get(name).is_some_and(is_unsigned_type),
            Expr::List(items) => match items.first() {
                Some(Expr::Symbol(operator))
                    if matches!(
                        operator_base(operator.as_str()),
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
                .cloned()
                .or_else(|| {
                    self.global_types
                        .get(name)
                        .filter(|ty| is_float_type(ty))
                        .cloned()
                }),
            Expr::List(items) => match items.first() {
                Some(Expr::Symbol(operator))
                    if matches!(
                        operator_base(operator.as_str()),
                        "+" | "-" | "*" | "/" | "%"
                    ) =>
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
                Some(Expr::Symbol(operator))
                    if matches!(operator_base(operator.as_str()), "index" | "get") =>
                {
                    self.expression_type(expression).filter(is_float_type)
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
        if let Expr::List(items) = expression {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                return self.if_expression_as_float(items, ty);
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "match") {
                return self.match_expression(items, Some(ty), None);
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

    fn if_expression_as_aggregate(&mut self, items: &[Expr], ty: &Type) -> Result<(), String> {
        if items.len() != 4 {
            return Err(
                "aggregate if requires a condition, then expression, and else expression".into(),
            );
        }
        let else_label = self.label("aggregate_else");
        let end_label = self.label("aggregate_endif");
        self.expression(&items[1])?;
        self.output
            .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
        self.expression_as_expected(&items[2], ty)?;
        self.output
            .push_str(&format!("    jmp {end_label}\n{else_label}:\n"));
        self.expression_as_expected(&items[3], ty)?;
        self.output.push_str(&format!("{end_label}:\n"));
        Ok(())
    }

    fn block_expression_as_expected(
        &mut self,
        statements: &[Statement],
        ty: &Type,
    ) -> Result<(), String> {
        let Some((last, preceding)) = statements.split_last() else {
            return Err("aggregate block expression cannot be empty".into());
        };
        for statement in preceding {
            self.statement(statement)?;
        }
        if let Statement::Expr(expression) = last {
            self.expression_as_expected(expression, ty)
        } else {
            self.statement(last)
        }
    }

    fn store_value_to_slots(
        &mut self,
        value: &Expr,
        ty: &Type,
        slots: &[usize],
    ) -> Result<(), String> {
        let words = storage_word_count(ty, &self.structs, &self.enums)?;
        if slots.len() != words {
            return Err("aggregate temporary has an inconsistent layout".into());
        }
        if words > VALUE_REGISTERS.len() {
            if let Expr::List(items) = value {
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "deref")
                    && items.len() == 2
                {
                    self.copy_reference_to_slots(&items[1], slots)?;
                    return Ok(());
                }
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "get")
                    && items.len() == 3
                    && matches!(items[2], Expr::Symbol(_))
                    && matches!(
                        self.expression_type(&items[1]),
                        Some(Type::Reference { .. })
                    )
                {
                    self.copy_reference_field_to_slots(value, slots)?;
                    return Ok(());
                }
            }
        }
        if words > VALUE_REGISTERS.len()
            && (self.store_oversized_index_to_slots(value, ty, slots)?
                || self.store_oversized_field_to_slots(value, ty, slots)?)
        {
            return Ok(());
        }
        if words <= VALUE_REGISTERS.len() {
            return self.store_value_words(value, ty, slots);
        }
        if let Expr::Symbol(name) = value {
            if let Ok(source_slots) = local_slots(&self.locals, name) {
                if source_slots.len() == words {
                    for (source, destination) in source_slots.iter().zip(slots) {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                            source * 8,
                            destination * 8
                        ));
                    }
                    return Ok(());
                }
            }
            if self.global_types.get(name) == Some(ty) {
                for (index, destination) in slots.iter().enumerate() {
                    self.load_global_word(name, index)?;
                    self.output.push_str(&format!(
                        "    mov QWORD PTR [rbp-{}], rax\n",
                        destination * 8
                    ));
                }
                return Ok(());
            }
            if let Type::Named(enum_name) = ty {
                if let Some(variants) = self.enums.get(enum_name) {
                    if let Some(variant) = variants.iter().find(|variant| variant.name == *name) {
                        self.output.push_str(&format!(
                            "    mov QWORD PTR [rbp-{}], {}\n",
                            slots[0] * 8,
                            variant.discriminant
                        ));
                        for slot in &slots[1..] {
                            self.output
                                .push_str(&format!("    mov QWORD PTR [rbp-{}], 0\n", slot * 8));
                        }
                        return Ok(());
                    }
                }
            }
        }
        if let Expr::List(items) = value {
            if let Some(Expr::Symbol(function_name)) = items.first() {
                if self
                    .functions
                    .get(function_name)
                    .is_some_and(|function| function.indirect_return)
                {
                    let base = *slots
                        .first()
                        .ok_or_else(|| "aggregate temporary has no storage".to_owned())?;
                    self.call(function_name, &items[1..], Some(base))?;
                    return Ok(());
                }
            }
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if") {
                if items.len() != 4 {
                    return Err("aggregate if requires condition, then, and else values".into());
                }
                let else_label = self.label("aggregate_argument_else");
                let done_label = self.label("aggregate_argument_done");
                self.expression(&items[1])?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
                self.store_value_to_slots(&items[2], ty, slots)?;
                self.output
                    .push_str(&format!("    jmp {done_label}\n{else_label}:\n"));
                self.store_value_to_slots(&items[3], ty, slots)?;
                self.output.push_str(&format!("{done_label}:\n"));
                return Ok(());
            }
        }
        let Expr::List(items) = value else {
            return Err("large aggregate argument requires a constructor or local value".into());
        };
        let Some(Expr::Symbol(constructor)) = items.first() else {
            return Err("large aggregate argument constructor must start with a symbol".into());
        };
        match ty {
            Type::Array(element, length) if constructor == "array" => {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|declared| declared == *ty)
                {
                    2
                } else {
                    1
                };
                if items.len() - value_start != *length {
                    return Err("large array argument has the wrong length".into());
                }
                let element_words = storage_word_count(element, &self.structs, &self.enums)?;
                for (index, item) in items[value_start..].iter().enumerate() {
                    self.store_value_to_slots(
                        item,
                        element,
                        &slots[index * element_words..(index + 1) * element_words],
                    )?;
                }
                Ok(())
            }
            Type::Array(element, length) if constructor == "array-repeat" => {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|declared| declared == *ty)
                {
                    2
                } else {
                    1
                };
                if items.len() != value_start + 1 {
                    return Err("large array-repeat argument requires one value".into());
                }
                let element_words = storage_word_count(element, &self.structs, &self.enums)?;
                for index in 0..*length {
                    self.store_value_to_slots(
                        &items[value_start],
                        element,
                        &slots[index * element_words..(index + 1) * element_words],
                    )?;
                }
                Ok(())
            }
            Type::Tuple(fields) if constructor == "tuple" => {
                let value_start = if parse_type(items.get(1))
                    .ok()
                    .is_some_and(|declared| declared == *ty)
                {
                    2
                } else {
                    1
                };
                if items.len() - value_start != fields.len() {
                    return Err("large tuple argument has the wrong length".into());
                }
                let mut offset = 0;
                for (item, field) in items[value_start..].iter().zip(fields) {
                    let field_words = storage_word_count(field, &self.structs, &self.enums)?;
                    self.store_value_to_slots(item, field, &slots[offset..offset + field_words])?;
                    offset += field_words;
                }
                Ok(())
            }
            Type::Named(name) if self.structs.contains_key(name) && constructor == name => {
                let fields = self.structs.get(name).cloned().unwrap_or_default();
                if items.len() - 1 != fields.len() {
                    return Err(format!(
                        "large struct argument '{name}' has the wrong field count"
                    ));
                }
                let mut offset = 0;
                for (item, field) in items[1..].iter().zip(&fields) {
                    let field_words = storage_word_count(&field.ty, &self.structs, &self.enums)?;
                    self.store_value_to_slots(
                        item,
                        &field.ty,
                        &slots[offset..offset + field_words],
                    )?;
                    offset += field_words;
                }
                Ok(())
            }
            Type::Named(enum_name) if self.enums.contains_key(enum_name) => {
                let variants = self.enums.get(enum_name).cloned().unwrap_or_default();
                let variant = variants
                    .iter()
                    .find(|variant| variant.name == *constructor)
                    .ok_or_else(|| format!("unknown enum variant '{constructor}'"))?;
                if items.len() - 1 != variant.fields.len() {
                    return Err(format!(
                        "large enum variant '{constructor}' has the wrong payload count"
                    ));
                }
                self.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], {}\n",
                    slots[0] * 8,
                    variant.discriminant
                ));
                let mut offset = 1;
                for (item, field) in items[1..].iter().zip(&variant.fields) {
                    let field_words = storage_word_count(field, &self.structs, &self.enums)?;
                    self.store_value_to_slots(item, field, &slots[offset..offset + field_words])?;
                    offset += field_words;
                }
                for slot in &slots[offset..] {
                    self.output
                        .push_str(&format!("    mov QWORD PTR [rbp-{}], 0\n", slot * 8));
                }
                Ok(())
            }
            _ => Err("large aggregate argument constructor has the wrong type".into()),
        }
    }

    fn store_oversized_index_to_slots(
        &mut self,
        value: &Expr,
        ty: &Type,
        destination: &[usize],
    ) -> Result<bool, String> {
        let Expr::List(items) = value else {
            return Ok(false);
        };
        if items.len() != 3
            || !matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "index")
        {
            return Ok(false);
        }
        let Some(Type::Array(element, length)) = self.expression_type(&items[1]) else {
            return Ok(false);
        };
        let element_words = storage_word_count(&element, &self.structs, &self.enums)?;
        let result_words = storage_word_count(ty, &self.structs, &self.enums)?;
        if result_words != element_words || destination.len() != element_words {
            return Ok(false);
        }
        enum Source {
            Local(usize),
            Global(String),
        }
        let source = match &items[1] {
            Expr::Symbol(name) => {
                if let Some(Storage::Array { base, .. }) = self.locals.get(name) {
                    Some(Source::Local(*base))
                } else if matches!(self.globals.get(name), Some(GlobalValue::Aggregate(_))) {
                    Some(Source::Global(name.clone()))
                } else {
                    None
                }
            }
            Expr::List(call_items) => match call_items.first() {
                Some(Expr::Symbol(operator)) if operator == "get" => {
                    let source_type = self
                        .expression_type(&items[1])
                        .ok_or_else(|| "large aggregate field has no known type".to_owned())?;
                    let source_words =
                        storage_word_count(&source_type, &self.structs, &self.enums)?;
                    let temp_base = self
                        .aggregate_temp_base
                        .ok_or_else(|| "no aggregate temporary is available".to_owned())?
                        + (self.aggregate_argument_regions + self.aggregate_projection_depth)
                            * self.aggregate_temp_words;
                    self.aggregate_projection_depth += 1;
                    self.store_value_to_slots(
                        &items[1],
                        &source_type,
                        &flat_slots(temp_base, source_words),
                    )?;
                    self.aggregate_projection_depth -= 1;
                    Some(Source::Local(temp_base))
                }
                Some(Expr::Symbol(function_name))
                    if self
                        .functions
                        .get(function_name)
                        .is_some_and(|function| function.indirect_return) =>
                {
                    Some(Source::Local(
                        self.call_to_aggregate_temp(function_name, &call_items[1..])?,
                    ))
                }
                _ => {
                    let source_type = self
                        .expression_type(&items[1])
                        .ok_or_else(|| "large aggregate projection has no known type".to_owned())?;
                    let source_words =
                        storage_word_count(&source_type, &self.structs, &self.enums)?;
                    let temp_base = self
                        .aggregate_temp_base
                        .ok_or_else(|| "no aggregate temporary is available".to_owned())?
                        + (self.aggregate_argument_regions + self.aggregate_projection_depth)
                            * self.aggregate_temp_words;
                    self.aggregate_projection_depth += 1;
                    self.store_value_to_slots(
                        &items[1],
                        &source_type,
                        &flat_slots(temp_base, source_words),
                    )?;
                    self.aggregate_projection_depth -= 1;
                    Some(Source::Local(temp_base))
                }
            },
            _ => None,
        };
        let Some(source) = source else {
            return Ok(false);
        };
        let global = matches!(source, Source::Global(_));
        let bounds_failure = self.label("oversized_index_bounds_failure");
        let done = self.label("oversized_index_done");
        self.expression(&items[2])?;
        self.output.push_str(&format!(
            "    mov rcx, rax\n    cmp rcx, {length}\n    jae {bounds_failure}\n    imul rcx, {element_words}\n    shl rcx, 3\n"
        ));
        match source {
            Source::Local(base) => self.output.push_str(&format!(
                "    lea r11, [rbp-{}]\n    sub r11, rcx\n",
                base * 8
            )),
            Source::Global(name) => self.output.push_str(&format!(
                "    lea r11, [rip+{}]\n    add r11, rcx\n",
                asm_symbol(&name)
            )),
        }
        for (index, slot) in destination.iter().enumerate() {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [r11{}{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                if global { "+" } else { "-" },
                index * 8,
                slot * 8
            ));
        }
        self.output.push_str(&format!(
            "    jmp {done}\n{bounds_failure}:\n    ud2\n{done}:\n"
        ));
        Ok(true)
    }

    fn store_oversized_field_to_slots(
        &mut self,
        value: &Expr,
        ty: &Type,
        destination: &[usize],
    ) -> Result<bool, String> {
        let Expr::List(items) = value else {
            return Ok(false);
        };
        if items.len() != 3
            || !matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "get")
        {
            return Ok(false);
        }
        let source_type = self
            .expression_type(&items[1])
            .ok_or_else(|| "get source has no known type".to_owned())?;
        let offset = match (&source_type, &items[2]) {
            (Type::Tuple(fields), Expr::Integer(index)) if *index >= 0 => {
                let index = usize::try_from(*index)
                    .map_err(|_| "tuple field index is too large".to_owned())?;
                let offset = fields
                    .get(..index)
                    .ok_or_else(|| "tuple field index is out of bounds".to_owned())?
                    .iter()
                    .map(|field| storage_word_count(field, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                offset
            }
            (Type::Named(name), Expr::Symbol(field_name)) => {
                let fields = self
                    .structs
                    .get(name)
                    .ok_or_else(|| format!("'{name}' is not a struct"))?;
                let index = fields
                    .iter()
                    .position(|field| field.name == *field_name)
                    .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                let offset = fields[..index]
                    .iter()
                    .map(|field| storage_word_count(&field.ty, &self.structs, &self.enums))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .sum::<usize>();
                offset
            }
            _ => return Ok(false),
        };
        let field_words = storage_word_count(ty, &self.structs, &self.enums)?;
        if field_words != destination.len() {
            return Ok(false);
        }
        enum Source {
            Slots(Vec<usize>),
            Global(String),
        }
        let source = match &items[1] {
            Expr::Symbol(name) => {
                if let Ok(slots) = local_slots(&self.locals, name) {
                    Some(Source::Slots(slots))
                } else if matches!(self.globals.get(name), Some(GlobalValue::Aggregate(_))) {
                    Some(Source::Global(name.clone()))
                } else {
                    None
                }
            }
            Expr::List(call_items) => match call_items.first() {
                Some(Expr::Symbol(function_name))
                    if self
                        .functions
                        .get(function_name)
                        .is_some_and(|function| function.indirect_return) =>
                {
                    let base = self.call_to_aggregate_temp(function_name, &call_items[1..])?;
                    let source_words =
                        storage_word_count(&source_type, &self.structs, &self.enums)?;
                    Some(Source::Slots(flat_slots(base, source_words)))
                }
                _ => {
                    let temp_base = self
                        .aggregate_temp_base
                        .ok_or_else(|| "no aggregate temporary is available".to_owned())?
                        + (self.aggregate_argument_regions + self.aggregate_projection_depth)
                            * self.aggregate_temp_words;
                    let source_words =
                        storage_word_count(&source_type, &self.structs, &self.enums)?;
                    self.aggregate_projection_depth += 1;
                    self.store_value_to_slots(
                        &items[1],
                        &source_type,
                        &flat_slots(temp_base, source_words),
                    )?;
                    self.aggregate_projection_depth -= 1;
                    Some(Source::Slots(flat_slots(temp_base, source_words)))
                }
            },
            _ => None,
        };
        let Some(source) = source else {
            return Ok(false);
        };
        match source {
            Source::Slots(slots) => {
                for (index, destination_slot) in destination.iter().enumerate() {
                    let source_slot = slots
                        .get(offset + index)
                        .ok_or_else(|| "aggregate field exceeds source storage".to_owned())?;
                    self.output.push_str(&format!(
                        "    mov rax, QWORD PTR [rbp-{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                        source_slot * 8,
                        destination_slot * 8
                    ));
                }
            }
            Source::Global(name) => {
                for (index, destination_slot) in destination.iter().enumerate() {
                    self.load_global_word(&name, offset + index)?;
                    self.output.push_str(&format!(
                        "    mov QWORD PTR [rbp-{}], rax\n",
                        destination_slot * 8
                    ));
                }
            }
        }
        Ok(true)
    }

    fn push_call_argument(
        &mut self,
        value: &Expr,
        ty: &Type,
        indirect: bool,
    ) -> Result<(), String> {
        if !indirect {
            return self.push_value_words(value, ty, false);
        }
        let base = if let Expr::Symbol(name) = value {
            let slots = local_slots(&self.locals, name)?;
            *slots
                .first()
                .ok_or_else(|| "large aggregate argument has no storage".to_owned())?
        } else {
            let base = self
                .aggregate_temp_base
                .ok_or_else(|| "no aggregate temporary is available".to_owned())?;
            let region = self.aggregate_argument_cursor;
            self.aggregate_argument_cursor += 1;
            let base = base + region * self.aggregate_temp_words;
            let words = storage_word_count(ty, &self.structs, &self.enums)?;
            let slots = flat_slots(base, words);
            self.store_value_to_slots(value, ty, &slots)?;
            base
        };
        self.output
            .push_str(&format!("    lea rax, [rbp-{}]\n", base * 8));
        self.push_rax();
        Ok(())
    }

    fn copy_reference_to_slots(&mut self, reference: &Expr, slots: &[usize]) -> Result<(), String> {
        self.expression(reference)?;
        self.output.push_str("    and rax, -2\n    mov rcx, rax\n");
        for (index, slot) in slots.iter().enumerate() {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rcx+{}]\n    mov QWORD PTR [rbp-{}], rax\n",
                index * 8,
                slot * 8
            ));
        }
        Ok(())
    }

    fn copy_reference_field_to_slots(
        &mut self,
        value: &Expr,
        slots: &[usize],
    ) -> Result<(), String> {
        let Expr::List(items) = value else {
            return Err("large reference projection must be a get expression".into());
        };
        let field_name = match items.get(2) {
            Some(Expr::Symbol(name)) => name,
            _ => return Err("large reference projection requires a named field".into()),
        };
        let Type::Reference { target, .. } = self
            .expression_type(&items[1])
            .ok_or_else(|| "large reference projection has no base type".to_owned())?
        else {
            return Err("large reference projection requires a reference".into());
        };
        let Type::Named(struct_name) = *target else {
            return Err("large reference projection requires a struct reference".into());
        };
        let fields = self
            .structs
            .get(&struct_name)
            .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
        let index = fields
            .iter()
            .position(|field| field.name == *field_name)
            .ok_or_else(|| format!("struct '{struct_name}' has no field '{field_name}'"))?;
        let offset = fields[..index]
            .iter()
            .map(|field| storage_word_count(&field.ty, &self.structs, &self.enums))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .sum::<usize>();
        self.emit_reference_field_address(&items[1], offset, false)?;
        for (index, slot) in slots.iter().enumerate() {
            self.output.push_str(&format!(
                "    mov rcx, QWORD PTR [rax+{}]\n    mov QWORD PTR [rbp-{}], rcx\n",
                index * 8,
                slot * 8
            ));
        }
        Ok(())
    }

    fn emit_indirect_return_target(&mut self, slot: Option<usize>) {
        if let Some(slot) = slot {
            self.output
                .push_str(&format!("    lea r10, [rbp-{}]\n", slot * 8));
        }
    }

    fn call_to_aggregate_temp(&mut self, name: &str, arguments: &[Expr]) -> Result<usize, String> {
        let base = self
            .aggregate_temp_base
            .ok_or_else(|| "no aggregate temporary is available".to_owned())?;
        self.call(name, arguments, Some(base))?;
        Ok(base)
    }

    fn load_aggregate_temp_scalar(
        &mut self,
        base: usize,
        offset: usize,
        ty: &Type,
    ) -> Result<(), String> {
        let slot = base + offset;
        if matches!(ty, Type::F32) {
            self.output
                .push_str(&format!("    movss xmm0, DWORD PTR [rbp-{}]\n", slot * 8));
        } else if matches!(ty, Type::F64) {
            self.output
                .push_str(&format!("    movq xmm0, QWORD PTR [rbp-{}]\n", slot * 8));
        } else {
            self.output
                .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
        }
        Ok(())
    }

    fn load_aggregate_temp_value(
        &mut self,
        base: usize,
        offset: usize,
        ty: &Type,
    ) -> Result<(), String> {
        let words = value_word_count(ty, &self.structs, &self.enums)?;
        if words == 1 {
            return self.load_aggregate_temp_scalar(base, offset, ty);
        }
        if words > VALUE_REGISTERS.len() {
            return Err("aggregate temporary value exceeds value registers".into());
        }
        for (index, register) in VALUE_REGISTERS[..words].iter().enumerate() {
            self.output.push_str(&format!(
                "    mov {register}, QWORD PTR [rbp-{}]\n",
                (base + offset + index) * 8
            ));
        }
        Ok(())
    }

    fn call(
        &mut self,
        name: &str,
        arguments: &[Expr],
        indirect_return_slot: Option<usize>,
    ) -> Result<(), String> {
        let saved_cursor = self.aggregate_argument_cursor;
        self.aggregate_argument_cursor = 0;
        let result = self.call_inner(name, arguments, indirect_return_slot);
        self.aggregate_argument_cursor = saved_cursor;
        result
    }

    fn call_inner(
        &mut self,
        name: &str,
        arguments: &[Expr],
        indirect_return_slot: Option<usize>,
    ) -> Result<(), String> {
        if arguments.len() > 32 {
            return Err(format!("call to '{name}' has more than 32 arguments"));
        }
        let abi = self
            .functions
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown function '{name}'"))?;
        if abi.indirect_return && indirect_return_slot.is_none() {
            return Err(format!(
                "large aggregate call to '{name}' must initialize a local value"
            ));
        }
        if arguments.len() != abi.parameters.len() {
            return Err(format!("call to '{name}' has the wrong argument count"));
        }
        if abi.parameters.iter().all(is_float_type) {
            if let Some(ty) = abi.parameters.first() {
                if abi.parameters.iter().all(|other| other == ty) {
                    return self.call_float(name, arguments, ty, indirect_return_slot);
                }
            }
        }
        if abi.parameters.iter().any(is_float_type) {
            return self.call_mixed(
                name,
                arguments,
                &abi.parameters,
                &abi.indirect_parameters,
                indirect_return_slot,
            );
        }
        let word_count = abi
            .parameters
            .iter()
            .zip(&abi.indirect_parameters)
            .map(|(ty, indirect)| {
                if *indirect {
                    Ok(1)
                } else {
                    value_word_count(ty, &self.structs, &self.enums)
                }
            })
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
            for ((argument, ty), indirect) in arguments
                .iter()
                .zip(&abi.parameters)
                .zip(&abi.indirect_parameters)
                .rev()
            {
                if *indirect {
                    self.push_call_argument(argument, ty, true)?;
                } else {
                    self.push_value_words(argument, ty, true)?;
                }
            }
            for (index, register) in ARGUMENT_REGISTERS.iter().enumerate() {
                self.output.push_str(&format!(
                    "    mov {register}, QWORD PTR [rsp+{}]\n",
                    index * 8
                ));
            }
            self.output.push_str("    add rsp, 48\n");
            self.stack_depth -= ARGUMENT_REGISTERS.len();
            self.emit_indirect_return_target(indirect_return_slot);
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
        for ((argument, ty), indirect) in arguments
            .iter()
            .zip(&abi.parameters)
            .zip(&abi.indirect_parameters)
        {
            self.push_call_argument(argument, ty, *indirect)?;
        }
        for register in ARGUMENT_REGISTERS[..total_words].iter().rev() {
            self.output.push_str(&format!("    pop {register}\n"));
            self.stack_depth -= 1;
        }
        let needs_padding = self.stack_depth % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
        }
        self.emit_indirect_return_target(indirect_return_slot);
        self.output
            .push_str(&format!("    call {}\n", asm_symbol(name)));
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
        }
        Ok(())
    }

    fn call_float(
        &mut self,
        name: &str,
        arguments: &[Expr],
        ty: &Type,
        indirect_return_slot: Option<usize>,
    ) -> Result<(), String> {
        let overflow_words = arguments
            .len()
            .saturating_sub(FLOAT_ARGUMENT_REGISTERS.len());
        let total_words = arguments.len();
        let needs_padding = (self.stack_depth + total_words + overflow_words) % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
            self.stack_depth += 1;
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
        for (copied_words, argument_index) in (FLOAT_ARGUMENT_REGISTERS.len()..arguments.len())
            .rev()
            .enumerate()
        {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rsp+{}]\n    push rax\n",
                (total_words - argument_index - 1 + copied_words) * 8
            ));
            self.stack_depth += 1;
        }
        for (argument_index, register) in FLOAT_ARGUMENT_REGISTERS
            .iter()
            .enumerate()
            .take(arguments.len())
        {
            let offset = (overflow_words + total_words - argument_index - 1) * 8;
            self.output.push_str(&format!(
                "    mov{} {}, {} PTR [rsp+{offset}]\n",
                if matches!(ty, Type::F32) { "d" } else { "q" },
                register,
                if matches!(ty, Type::F32) {
                    "DWORD"
                } else {
                    "QWORD"
                }
            ));
        }
        self.emit_indirect_return_target(indirect_return_slot);
        self.output
            .push_str(&format!("    call {}\n", asm_symbol(name)));
        self.output.push_str(&format!(
            "    add rsp, {}\n",
            (total_words + overflow_words) * 8
        ));
        self.stack_depth -= total_words + overflow_words;
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
            self.stack_depth -= 1;
        }
        Ok(())
    }

    fn call_mixed(
        &mut self,
        name: &str,
        arguments: &[Expr],
        parameters: &[Type],
        indirect_parameters: &[bool],
        indirect_return_slot: Option<usize>,
    ) -> Result<(), String> {
        let word_counts = parameters
            .iter()
            .zip(indirect_parameters)
            .map(|(ty, indirect)| {
                if *indirect || is_float_type(ty) {
                    Ok(1)
                } else {
                    value_word_count(ty, &self.structs, &self.enums)
                }
            })
            .collect::<Result<Vec<_>, String>>()?;
        let total_words = word_counts.iter().sum::<usize>();
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        let mut overflow_offsets = Vec::new();
        let mut source_offset = 0usize;
        for ((ty, indirect), words) in parameters.iter().zip(indirect_parameters).zip(&word_counts)
        {
            if !*indirect && is_float_type(ty) {
                if float_index >= FLOAT_ARGUMENT_REGISTERS.len() {
                    overflow_offsets.push(source_offset);
                }
                float_index += 1;
            } else {
                for word in 0..*words {
                    if integer_index >= ARGUMENT_REGISTERS.len() {
                        overflow_offsets.push(source_offset + word);
                    }
                    integer_index += 1;
                }
            }
            source_offset += words;
        }
        let overflow_words = overflow_offsets.len();
        let needs_padding = (self.stack_depth + total_words + overflow_words) % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
            self.stack_depth += 1;
        }
        for ((argument, ty), indirect) in arguments.iter().zip(parameters).zip(indirect_parameters)
        {
            self.push_call_argument(argument, ty, *indirect)?;
        }
        for (copied_words, source_offset) in overflow_offsets.iter().rev().enumerate() {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rsp+{}]\n    push rax\n",
                (total_words - source_offset - 1 + copied_words) * 8
            ));
            self.stack_depth += 1;
        }
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        let mut source_offset = 0usize;
        for ((ty, indirect), words) in parameters.iter().zip(indirect_parameters).zip(&word_counts)
        {
            for word in 0..*words {
                let offset = (overflow_words + total_words - (source_offset + word) - 1) * 8;
                if !*indirect && is_float_type(ty) {
                    if float_index < FLOAT_ARGUMENT_REGISTERS.len() {
                        self.output.push_str(&format!(
                            "    mov{} {}, {} PTR [rsp+{offset}]\n",
                            if matches!(ty, Type::F32) { "d" } else { "q" },
                            FLOAT_ARGUMENT_REGISTERS[float_index],
                            if matches!(ty, Type::F32) {
                                "DWORD"
                            } else {
                                "QWORD"
                            }
                        ));
                    }
                    float_index += 1;
                } else if integer_index < ARGUMENT_REGISTERS.len() {
                    self.output.push_str(&format!(
                        "    mov {}, QWORD PTR [rsp+{offset}]\n",
                        ARGUMENT_REGISTERS[integer_index]
                    ));
                    integer_index += 1;
                } else {
                    integer_index += 1;
                }
            }
            source_offset += words;
        }
        self.emit_indirect_return_target(indirect_return_slot);
        self.output
            .push_str(&format!("    call {}\n", asm_symbol(name)));
        self.output.push_str(&format!(
            "    add rsp, {}\n",
            (total_words + overflow_words) * 8
        ));
        self.stack_depth -= total_words + overflow_words;
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
            self.stack_depth -= 1;
        }
        Ok(())
    }

    fn push_value_words(&mut self, value: &Expr, ty: &Type, reverse: bool) -> Result<(), String> {
        if let Expr::List(items) = value {
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "clone")
                && items.len() == 2
            {
                let normalized = self.clone_operand(value);
                return self.push_value_words(&normalized, ty, reverse);
            }
        }
        if matches!(ty, Type::Unit | Type::Never) {
            self.expression(value)?;
            return Ok(());
        }
        if self.is_aggregate_type(ty)
            && (matches!(value, Expr::Block(_) | Expr::Loop(_) | Expr::Labeled { .. })
                || matches!(
                    value,
                    Expr::List(items)
                        if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "if" || operator == "match")
                ))
        {
            self.expression_as_expected(value, ty)?;
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
        if is_float_type(ty) {
            self.expression_as_abi_word(value, ty)?;
            self.push_rax();
            return Ok(());
        }
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
            if let Expr::String(string) = value {
                let characters = string.chars().collect::<Vec<_>>();
                if characters.len() != *length {
                    return Err("string length does not match array argument".into());
                }
                let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                    Box::new((0..*length).rev())
                } else {
                    Box::new(0..*length)
                };
                for index in indices {
                    self.output
                        .push_str(&format!("    mov rax, {}\n", characters[index] as u32));
                    self.push_rax();
                }
                return Ok(());
            }
            if let Expr::Symbol(local) = value {
                if matches!(
                    self.global_types.get(local),
                    Some(Type::Array(_, global_length)) if *global_length == *length
                ) {
                    let Type::Array(element, _) = ty else {
                        unreachable!()
                    };
                    let element_words = value_word_count(element, &self.structs, &self.enums)?;
                    let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new((0..*length).rev())
                    } else {
                        Box::new(0..*length)
                    };
                    for index in indices {
                        let words: Box<dyn Iterator<Item = usize>> = if reverse {
                            Box::new((0..element_words).rev())
                        } else {
                            Box::new(0..element_words)
                        };
                        for word in words {
                            self.load_global_word(local, index * element_words + word)?;
                            self.push_rax();
                        }
                    }
                    return Ok(());
                }
                let Storage::Array {
                    base,
                    length: local_length,
                    element_words,
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
                let element_words = *element_words;
                let length = *length;
                let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                    Box::new((0..length).rev())
                } else {
                    Box::new(0..length)
                };
                for index in indices {
                    let words: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new((0..element_words).rev())
                    } else {
                        Box::new(0..element_words)
                    };
                    for word in words {
                        self.output.push_str(&format!(
                            "    mov rax, QWORD PTR [rbp-{}]\n",
                            (base + index * element_words + word) * 8
                        ));
                        self.push_rax();
                    }
                }
                return Ok(());
            }
            if let Expr::List(items) = value {
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array-repeat")
                {
                    let value_start = if parse_type(items.get(1))
                        .ok()
                        .is_some_and(|ty| matches!(ty, Type::Array(_, _)))
                    {
                        2
                    } else {
                        1
                    };
                    if items.len() != value_start + 1 {
                        return Err("array-repeat requires one value".into());
                    }
                    let Type::Array(element, _) = ty else {
                        unreachable!()
                    };
                    let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new((0..*length).rev())
                    } else {
                        Box::new(0..*length)
                    };
                    for _ in indices {
                        self.push_value_words(&items[value_start], element, reverse)?;
                    }
                    return Ok(());
                }
                if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "array") {
                    let value_start = if parse_type(items.get(1))
                        .ok()
                        .is_some_and(|ty| matches!(ty, Type::Array(_, _)))
                    {
                        2
                    } else {
                        1
                    };
                    if items.len() - value_start != *length {
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
                        self.push_value_words(&items[index + value_start], element, reverse)?;
                    }
                    return Ok(());
                }
            }
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
        if let Type::Tuple(fields) = ty {
            let slots = if let Expr::Symbol(local) = value {
                if matches!(
                    self.global_types.get(local),
                    Some(Type::Tuple(global_fields)) if global_fields == fields
                ) {
                    let words = value_word_count(ty, &self.structs, &self.enums)?;
                    let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new((0..words).rev())
                    } else {
                        Box::new(0..words)
                    };
                    for index in indices {
                        self.load_global_word(local, index)?;
                        self.push_rax();
                    }
                    return Ok(());
                }
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
                    let value_start = if parse_type(items.get(1))
                        .ok()
                        .is_some_and(|ty| matches!(ty, Type::Tuple(_)))
                    {
                        2
                    } else {
                        1
                    };
                    if items.len() - value_start != fields.len() {
                        return Err("tuple argument has the wrong length".into());
                    }
                    let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new((0..fields.len()).rev())
                    } else {
                        Box::new(0..fields.len())
                    };
                    for index in indices {
                        self.push_value_words(
                            &items[index + value_start],
                            &fields[index],
                            reverse,
                        )?;
                    }
                    return Ok(());
                }
            }
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
        if let Type::Named(name) = ty {
            if let Some(fields) = self.structs.get(name).cloned() {
                if let Expr::Symbol(local) = value {
                    if matches!(
                        self.global_types.get(local),
                        Some(Type::Named(global_name)) if global_name == name
                    ) {
                        let words = value_word_count(ty, &self.structs, &self.enums)?;
                        let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                            Box::new((0..words).rev())
                        } else {
                            Box::new(0..words)
                        };
                        for index in indices {
                            self.load_global_word(local, index)?;
                            self.push_rax();
                        }
                        return Ok(());
                    }
                    let Storage::Struct(slots) = self
                        .locals
                        .get(local)
                        .ok_or_else(|| format!("unknown struct local '{local}'"))?
                    else {
                        return Err(format!("'{local}' is not a struct"));
                    };
                    let flat = slots
                        .iter()
                        .flat_map(|(_, field_slots)| field_slots.iter().copied())
                        .collect::<Vec<_>>();
                    let range: Box<dyn Iterator<Item = usize>> = if reverse {
                        Box::new(flat.into_iter().rev())
                    } else {
                        Box::new(flat.into_iter())
                    };
                    for slot in range {
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
                            self.push_value_words(&items[index + 1], &fields[index].ty, reverse)?;
                        }
                        return Ok(());
                    }
                }
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
            if self
                .enums
                .get(name)
                .is_some_and(|variants| variants.iter().any(|variant| !variant.fields.is_empty()))
            {
                if let Expr::Symbol(local) = value {
                    if matches!(
                        self.global_types.get(local),
                        Some(Type::Named(global_name)) if global_name == name
                    ) {
                        let words = value_word_count(ty, &self.structs, &self.enums)?;
                        let indices: Box<dyn Iterator<Item = usize>> = if reverse {
                            Box::new((0..words).rev())
                        } else {
                            Box::new(0..words)
                        };
                        for index in indices {
                            self.load_global_word(local, index)?;
                            self.push_rax();
                        }
                        return Ok(());
                    }
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

    fn load_global_word(&mut self, name: &str, index: usize) -> Result<(), String> {
        if !matches!(self.globals.get(name), Some(GlobalValue::Aggregate(_))) {
            return Err(format!("global '{name}' is not aggregate storage"));
        }
        let offset = index * 8;
        if offset == 0 {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rip+{}]\n",
                asm_symbol(name)
            ));
        } else {
            self.output.push_str(&format!(
                "    mov rax, QWORD PTR [rip+{}+{offset}]\n",
                asm_symbol(name)
            ));
        }
        Ok(())
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
