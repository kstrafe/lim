#![allow(clippy::too_many_arguments)]

use std::collections::{HashMap, HashSet};

use crate::{
    parse_type, AutoTrait, EnumVariant, Expr, Field, Function, Item, Program, Statement, Type,
};

const LOOP_VALUE_CONTEXT: &str = "\0lim-loop-value";

#[derive(Clone)]
struct Signature {
    type_parameters: Vec<String>,
    parameters: Vec<Type>,
    return_type: Type,
}

pub fn check_types(program: &Program) -> Result<(), String> {
    let mut declared_types = HashSet::new();
    for item in &program.items {
        match item {
            Item::TypeAlias { name, .. }
            | Item::Struct { name, .. }
            | Item::Enum { name, .. }
            | Item::ThreadTask { name, .. }
                if !declared_types.insert(name) =>
            {
                return Err(format!("duplicate type name '{name}'"));
            }
            _ => {}
        }
    }
    let mut unsafe_auto_traits = HashSet::new();
    for item in &program.items {
        let Item::UnsafeAutoTraitImpl {
            trait_kind,
            type_name,
        } = item
        else {
            continue;
        };
        if !declared_types.contains(type_name) {
            return Err(format!(
                "unsafe {:?} implementation refers to undeclared type '{type_name}'",
                trait_kind
            ));
        }
        let generic = program.items.iter().any(|declaration| match declaration {
            Item::Struct {
                name,
                type_parameters,
                ..
            }
            | Item::Enum {
                name,
                type_parameters,
                ..
            }
            | Item::TypeAlias {
                name,
                type_parameters,
                ..
            } if name == type_name => !type_parameters.is_empty(),
            _ => false,
        });
        if generic {
            return Err(format!(
                "unsafe {:?} implementation for generic type '{type_name}' is not supported",
                trait_kind
            ));
        }
        if !unsafe_auto_traits.insert((type_name.clone(), *trait_kind)) {
            return Err(format!(
                "duplicate unsafe {:?} implementation for '{type_name}'",
                trait_kind
            ));
        }
    }
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
        if let Item::ThreadTask { name, .. } = item {
            if structs
                .insert(
                    name.clone(),
                    vec![Field {
                        name: "__lim_thread_context".into(),
                        ty: Type::RawPointer {
                            mutable: true,
                            target: Box::new(Type::Unit),
                        },
                    }],
                )
                .is_some()
            {
                return Err(format!("duplicate thread task type '{name}'"));
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
                        discriminant: variant.discriminant,
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
        if function.external && !function.type_parameters.is_empty() {
            return Err(format!(
                "external function '{}' cannot be generic",
                function.name
            ));
        }
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
        let Item::ThreadTask { name, worker } = item else {
            continue;
        };
        let worker_item = program.items.iter().find_map(|item| match item {
            Item::Function(function) if function.name == *worker => Some(function),
            _ => None,
        });
        let Some(worker_item) = worker_item else {
            return Err(format!(
                "thread task '{name}' refers to unknown worker function '{worker}'"
            ));
        };
        if !worker_item.type_parameters.is_empty() {
            return Err(format!(
                "thread worker '{worker}' must be monomorphic; specialize it before spawning"
            ));
        }
        let worker_signature = functions
            .get(worker)
            .expect("worker signature collected")
            .clone();
        for (parameter, ty) in worker_item
            .parameters
            .iter()
            .zip(&worker_signature.parameters)
        {
            if !type_has_auto_trait(program, ty, AutoTrait::Send)? {
                return Err(format!(
                    "thread worker '{worker}' parameter '{}' does not implement Send",
                    parameter.name
                ));
            }
        }
        if !type_has_auto_trait(program, &worker_signature.return_type, AutoTrait::Send)? {
            return Err(format!(
                "thread worker '{worker}' return type does not implement Send"
            ));
        }
        if contains_reference_type(
            &worker_signature.return_type,
            &structs,
            &enums,
            &mut HashSet::new(),
        ) {
            return Err(format!(
                "thread worker '{worker}' cannot return reference-containing values"
            ));
        }
        let task_type = Type::Named(name.clone());
        for (generated_name, signature) in [
            (
                format!("{name}-spawn"),
                Signature {
                    type_parameters: Vec::new(),
                    parameters: worker_signature.parameters.clone(),
                    return_type: task_type.clone(),
                },
            ),
            (
                format!("{name}-join"),
                Signature {
                    type_parameters: Vec::new(),
                    parameters: vec![task_type],
                    return_type: worker_signature.return_type,
                },
            ),
        ] {
            if functions
                .insert(generated_name.clone(), signature)
                .is_some()
            {
                return Err(format!(
                    "generated thread function '{generated_name}' conflicts with an existing function"
                ));
            }
        }
    }
    reject_recursive_calls(program, &functions)?;
    for item in &program.items {
        match item {
            Item::Function(function) if function.external => {}
            Item::Function(function) => {
                check_function(function, &functions, &structs, &enums, &globals, &aliases)?
            }
            Item::TypeAlias { .. }
            | Item::Struct { .. }
            | Item::Enum { .. }
            | Item::UnsafeAutoTraitImpl { .. }
            | Item::ThreadTask { .. } => {}
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
    check_thread_task_ownership(program, &aliases)?;
    crate::linearcheck::check_program(program)?;
    crate::borrowcheck::check_program(program)?;
    crate::unsafecheck::check_program(program)?;
    Ok(())
}

fn check_thread_task_ownership(
    program: &Program,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    let tasks = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::ThreadTask { name, worker } => Some((name.clone(), worker.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    if tasks.is_empty() {
        return Ok(());
    }

    for item in &program.items {
        match item {
            Item::Struct { name, fields, .. } => {
                for field in fields {
                    if type_mentions_task(&resolve_type(&field.ty, aliases)?, &tasks) {
                        return Err(format!(
                            "thread task handles cannot be stored in struct '{name}'"
                        ));
                    }
                }
            }
            Item::Enum { name, variants, .. } => {
                if variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|ty| {
                        resolve_type(ty, aliases).is_ok_and(|ty| type_mentions_task(&ty, &tasks))
                    })
                {
                    return Err(format!(
                        "thread task handles cannot be stored in enum '{name}'"
                    ));
                }
            }
            Item::TypeAlias { name, target, .. } => {
                if type_mentions_task(&resolve_type(target, aliases)?, &tasks) {
                    return Err(format!(
                        "type alias '{name}' cannot contain a thread task handle"
                    ));
                }
            }
            Item::Let { name, ty, .. } | Item::Static { name, ty, .. } => {
                if type_mentions_task(&resolve_type(ty, aliases)?, &tasks) {
                    return Err(format!(
                        "global '{name}' cannot contain a thread task handle"
                    ));
                }
            }
            Item::Function(function) => {
                if function.parameters.iter().any(|parameter| {
                    resolve_type(&parameter.ty, aliases)
                        .is_ok_and(|ty| type_mentions_task(&ty, &tasks))
                }) || type_mentions_task(&resolve_type(&function.return_type, aliases)?, &tasks)
                {
                    return Err(format!(
                        "function '{}' cannot accept, return, or retain a thread task handle",
                        function.name
                    ));
                }
                check_function_task_uses(function, &tasks)?;
            }
            Item::UnsafeAutoTraitImpl { .. } | Item::ThreadTask { .. } => {}
        }
    }
    Ok(())
}

fn type_mentions_task(ty: &Type, tasks: &HashMap<String, String>) -> bool {
    match ty {
        Type::Named(name) => tasks.contains_key(name),
        Type::Reference { target, .. }
        | Type::RawPointer { target, .. }
        | Type::Cell(target)
        | Type::Array(target, _) => type_mentions_task(target, tasks),
        Type::Tuple(fields) => fields.iter().any(|field| type_mentions_task(field, tasks)),
        _ => false,
    }
}

fn check_function_task_uses(
    function: &Function,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    let mut handles = HashMap::<String, String>::new();
    let mut pending = HashSet::<String>::new();
    let mut consumed = HashSet::<String>::new();
    for statement in &function.body {
        match statement {
            Statement::Let {
                name,
                ty: Type::Named(task_type),
                value,
                mutable,
            } if tasks.contains_key(task_type) => {
                if *mutable {
                    return Err(format!(
                        "thread task handle '{name}' must be immutable and consumed by join"
                    ));
                }
                let expected_spawn = format!("{task_type}-spawn");
                if !is_direct_thread_call(value, &expected_spawn) {
                    return Err(format!(
                        "thread task '{name}' must be initialized directly by '{expected_spawn}'"
                    ));
                }
                let Expr::List(items) = value else {
                    unreachable!()
                };
                check_task_expression_children(&items[1..], &handles, tasks)?;
                if handles.insert(name.clone(), task_type.clone()).is_some() {
                    return Err(format!("duplicate thread task binding '{name}'"));
                }
                pending.insert(name.clone());
            }
            Statement::Let { name, value, .. } => {
                if let Some((task_type, handle)) = direct_task_join(value, tasks) {
                    consume_thread_handle(
                        &task_type,
                        &handle,
                        &handles,
                        &mut pending,
                        &mut consumed,
                    )?;
                } else {
                    check_task_statement_expr(value, &handles, tasks)?;
                    reject_thread_control_flow_while_pending(value, &pending)?;
                }
                let _ = name;
            }
            Statement::Expr(value) => {
                if let Some((task_type, handle)) = direct_task_join(value, tasks) {
                    consume_thread_handle(
                        &task_type,
                        &handle,
                        &handles,
                        &mut pending,
                        &mut consumed,
                    )?;
                } else {
                    check_task_statement_expr(value, &handles, tasks)?;
                    reject_thread_control_flow_while_pending(value, &pending)?;
                }
            }
            Statement::Return(Some(value)) => {
                if let Some((task_type, handle)) = direct_task_join(value, tasks) {
                    consume_thread_handle(
                        &task_type,
                        &handle,
                        &handles,
                        &mut pending,
                        &mut consumed,
                    )?;
                } else {
                    check_task_statement_expr(value, &handles, tasks)?;
                    if !pending.is_empty() {
                        return Err(format!(
                            "function '{}' may return while thread task '{}' is still running",
                            function.name,
                            pending.iter().next().unwrap()
                        ));
                    }
                }
            }
            Statement::Return(None) => {
                if !pending.is_empty() {
                    return Err(format!(
                        "function '{}' may return while thread task '{}' is still running",
                        function.name,
                        pending.iter().next().unwrap()
                    ));
                }
            }
            _ => {
                check_task_statement(statement, &handles, tasks)?;
                if !pending.is_empty() && is_control_statement(statement) {
                    return Err(format!(
                        "thread task handles cannot cross control flow; join '{}' before this statement",
                        pending.iter().next().unwrap()
                    ));
                }
            }
        }
    }
    if let Some(handle) = pending.iter().next() {
        return Err(format!(
            "thread task handle '{handle}' is not joined exactly once"
        ));
    }
    if let Some(handle) = handles.keys().find(|handle| !consumed.contains(*handle)) {
        return Err(format!(
            "thread task handle '{handle}' is not joined exactly once"
        ));
    }
    Ok(())
}

fn reject_thread_control_flow_while_pending(
    expression: &Expr,
    pending: &HashSet<String>,
) -> Result<(), String> {
    if !pending.is_empty() && expression_has_control_flow(expression) {
        return Err(format!(
            "thread task handles cannot cross control flow; join '{}' first",
            pending.iter().next().unwrap()
        ));
    }
    Ok(())
}

fn is_control_statement(statement: &Statement) -> bool {
    matches!(
        statement,
        Statement::While { .. }
            | Statement::Loop { .. }
            | Statement::For { .. }
            | Statement::Labeled { .. }
            | Statement::Break
            | Statement::BreakValue(_)
            | Statement::BreakTo(_)
            | Statement::BreakToValue { .. }
            | Statement::Continue
            | Statement::ContinueTo(_)
            | Statement::LetElse { .. }
    )
}

fn expression_has_control_flow(expression: &Expr) -> bool {
    match expression {
        Expr::List(items) => {
            matches!(items.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "if" | "if-let" | "match" | "while" | "loop" | "for"))
                || items.iter().any(expression_has_control_flow)
        }
        Expr::Block(_) | Expr::Loop(_) => true,
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => expression_has_control_flow(expression),
        _ => false,
    }
}

fn direct_task_join(
    expression: &Expr,
    tasks: &HashMap<String, String>,
) -> Option<(String, String)> {
    let Expr::List(items) = expression else {
        return None;
    };
    let Expr::Symbol(operator) = items.first()? else {
        return None;
    };
    for task_type in tasks.keys() {
        if operator == &format!("{task_type}-join") && items.len() == 2 {
            let Expr::Symbol(handle) = &items[1] else {
                return None;
            };
            return Some((task_type.clone(), handle.clone()));
        }
    }
    None
}

fn is_direct_thread_call(expression: &Expr, expected: &str) -> bool {
    matches!(expression, Expr::List(items)
        if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == expected))
}

fn consume_thread_handle(
    task_type: &str,
    handle: &str,
    handles: &HashMap<String, String>,
    pending: &mut HashSet<String>,
    consumed: &mut HashSet<String>,
) -> Result<(), String> {
    match handles.get(handle) {
        Some(actual) if actual == task_type && pending.remove(handle) => {
            consumed.insert(handle.to_owned());
            Ok(())
        }
        Some(_) if consumed.contains(handle) => Err(format!(
            "thread task handle '{handle}' was joined more than once"
        )),
        Some(_) => Err(format!("thread task handle '{handle}' is not active")),
        None => Err(format!("'{handle}' is not a thread task handle")),
    }
}

fn contains_thread_operation(expression: &Expr, tasks: &HashMap<String, String>) -> bool {
    match expression {
        Expr::List(items) => {
            let head = items.first().and_then(|item| match item {
                Expr::Symbol(name) => Some(name),
                _ => None,
            });
            head.is_some_and(|head| {
                tasks
                    .keys()
                    .any(|task| head == &format!("{task}-spawn") || head == &format!("{task}-join"))
            }) || items
                .iter()
                .any(|item| contains_thread_operation(item, tasks))
        }
        Expr::Block(statements) | Expr::Loop(statements) => statements
            .iter()
            .any(|statement| statement_contains_thread_operation(statement, tasks)),
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => contains_thread_operation(expression, tasks),
        _ => false,
    }
}

fn check_task_statement_expr(
    expression: &Expr,
    handles: &HashMap<String, String>,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    if contains_thread_operation(expression, tasks) {
        return Err("thread spawn and join must be direct top-level statements".into());
    }
    check_task_expression_children(std::slice::from_ref(expression), handles, tasks)
}

fn check_task_expression_children(
    expressions: &[Expr],
    handles: &HashMap<String, String>,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    for expression in expressions {
        match expression {
            Expr::Symbol(name) if handles.contains_key(name) => {
                return Err(format!(
                    "thread task handle '{name}' may only be used once as the direct argument to join"
                ));
            }
            Expr::List(items) => {
                if let Some(Expr::Symbol(name)) = items.first() {
                    if tasks.contains_key(name) && items.len() > 1 {
                        return Err(format!(
                            "thread task type '{name}' is opaque and cannot be constructed directly"
                        ));
                    }
                }
                check_task_expression_children(items, handles, tasks)?;
            }
            Expr::Block(statements) | Expr::Loop(statements) => {
                for statement in statements {
                    check_task_statement(statement, handles, tasks)?;
                }
            }
            Expr::Labeled { expression, .. }
            | Expr::Quote(expression)
            | Expr::QuasiQuote(expression)
            | Expr::Unquote(expression)
            | Expr::UnquoteSplicing(expression) => {
                check_task_expression_children(std::slice::from_ref(expression), handles, tasks)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn statement_contains_thread_operation(
    statement: &Statement,
    tasks: &HashMap<String, String>,
) -> bool {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => contains_thread_operation(value, tasks),
        Statement::ArrayAssign { index, value, .. } => {
            contains_thread_operation(index, tasks) || contains_thread_operation(value, tasks)
        }
        Statement::While { condition, body } => {
            contains_thread_operation(condition, tasks)
                || body
                    .iter()
                    .any(|statement| statement_contains_thread_operation(statement, tasks))
        }
        Statement::Loop { body } => body
            .iter()
            .any(|statement| statement_contains_thread_operation(statement, tasks)),
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            statement_contains_thread_operation(init, tasks)
                || contains_thread_operation(condition, tasks)
                || statement_contains_thread_operation(step, tasks)
                || body
                    .iter()
                    .any(|statement| statement_contains_thread_operation(statement, tasks))
        }
        Statement::Labeled { statement, .. } => {
            statement_contains_thread_operation(statement, tasks)
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => false,
    }
}

fn check_task_statement(
    statement: &Statement,
    handles: &HashMap<String, String>,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => check_task_statement_expr(value, handles, tasks),
        Statement::ArrayAssign { index, value, .. } => {
            check_task_statement_expr(index, handles, tasks)?;
            check_task_statement_expr(value, handles, tasks)
        }
        Statement::While { condition, body } => {
            check_task_statement_expr(condition, handles, tasks)?;
            for statement in body {
                check_task_statement(statement, handles, tasks)?;
            }
            Ok(())
        }
        Statement::Loop { body } => {
            for statement in body {
                check_task_statement(statement, handles, tasks)?;
            }
            Ok(())
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_task_statement(init, handles, tasks)?;
            check_task_statement_expr(condition, handles, tasks)?;
            check_task_statement(step, handles, tasks)?;
            for statement in body {
                check_task_statement(statement, handles, tasks)?;
            }
            Ok(())
        }
        Statement::Labeled { statement, .. } => check_task_statement(statement, handles, tasks),
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => Ok(()),
    }
}

/// Determine whether a concrete type satisfies Lim's built-in Send or Sync
/// auto trait. Explicit `#unsafe-impl` declarations override structural rules.
pub fn type_has_auto_trait(
    program: &Program,
    ty: &Type,
    trait_kind: AutoTrait,
) -> Result<bool, String> {
    let aliases = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. } => Some((name.clone(), target.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let structs = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields, .. } => Some((
                name.clone(),
                fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), resolve_type(&field.ty, &aliases)?)))
                    .collect::<Result<Vec<_>, String>>(),
            )),
            Item::ThreadTask { name, .. } => Some((
                name.clone(),
                Ok(vec![(
                    "__lim_thread_context".to_owned(),
                    Type::RawPointer {
                        mutable: true,
                        target: Box::new(Type::Unit),
                    },
                )]),
            )),
            _ => None,
        })
        .map(|(name, fields)| fields.map(|fields| (name, fields)))
        .collect::<Result<HashMap<_, _>, _>>()?;
    let enums = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { name, variants, .. } => Some((
                name.clone(),
                variants
                    .iter()
                    .map(|variant| {
                        variant
                            .fields
                            .iter()
                            .map(|ty| resolve_type(ty, &aliases))
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .collect::<Result<Vec<_>, String>>(),
            )),
            _ => None,
        })
        .map(|(name, variants)| variants.map(|variants| (name, variants)))
        .collect::<Result<HashMap<_, _>, _>>()?;
    let overrides = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::UnsafeAutoTraitImpl {
                trait_kind,
                type_name,
            } => Some((type_name.clone(), *trait_kind)),
            _ => None,
        })
        .collect::<HashSet<_>>();
    type_has_auto_trait_inner(
        &resolve_type(ty, &aliases)?,
        trait_kind,
        &structs,
        &enums,
        &overrides,
        &mut HashSet::new(),
    )
}

fn type_has_auto_trait_inner(
    ty: &Type,
    trait_kind: AutoTrait,
    structs: &HashMap<String, Vec<(String, Type)>>,
    enums: &HashMap<String, Vec<Vec<Type>>>,
    overrides: &HashSet<(String, AutoTrait)>,
    active: &mut HashSet<String>,
) -> Result<bool, String> {
    let all = |types: Vec<&Type>, active: &mut HashSet<String>| -> Result<bool, String> {
        for nested in types {
            if !type_has_auto_trait_inner(nested, trait_kind, structs, enums, overrides, active)? {
                return Ok(false);
            }
        }
        Ok(true)
    };
    match ty {
        Type::Unit
        | Type::Never
        | Type::Bool
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
        | Type::F32
        | Type::F64 => Ok(true),
        Type::Generic(_) => Ok(false),
        Type::RawPointer { .. } => Ok(false),
        Type::Cell(inner) => match trait_kind {
            AutoTrait::Send => {
                type_has_auto_trait_inner(inner, trait_kind, structs, enums, overrides, active)
            }
            AutoTrait::Sync => Ok(false),
        },
        Type::Reference { mutable, target } => match (trait_kind, mutable) {
            (AutoTrait::Send, false) | (AutoTrait::Sync, _) => type_has_auto_trait_inner(
                target,
                AutoTrait::Sync,
                structs,
                enums,
                overrides,
                active,
            ),
            (AutoTrait::Send, true) => type_has_auto_trait_inner(
                target,
                AutoTrait::Send,
                structs,
                enums,
                overrides,
                active,
            ),
        },
        Type::Tuple(fields) => all(fields.iter().collect(), active),
        Type::Array(element, _) => {
            type_has_auto_trait_inner(element, trait_kind, structs, enums, overrides, active)
        }
        Type::Named(name) => {
            if overrides.contains(&(name.clone(), trait_kind)) {
                return Ok(true);
            }
            if !active.insert(name.clone()) {
                return Ok(true);
            }
            let result = if let Some(fields) = structs.get(name) {
                all(fields.iter().map(|(_, ty)| ty).collect(), active)?
            } else if let Some(variants) = enums.get(name) {
                all(
                    variants.iter().flat_map(|variant| variant.iter()).collect(),
                    active,
                )?
            } else {
                return Err(format!(
                    "unknown type '{name}' while checking {trait_kind:?}"
                ));
            };
            active.remove(name);
            Ok(result)
        }
    }
}

fn reject_recursive_calls(
    program: &Program,
    functions: &HashMap<String, Signature>,
) -> Result<(), String> {
    let names = functions.keys().cloned().collect::<HashSet<_>>();
    let mut edges = HashMap::<String, HashSet<String>>::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if function.external {
            continue;
        }
        let calls = edges.entry(function.name.clone()).or_default();
        for statement in &function.body {
            collect_statement_calls(statement, &names, calls);
        }
    }

    let mut state = HashMap::<String, bool>::new();
    let mut path = Vec::new();
    for name in names {
        visit_call_graph(&name, &edges, &mut state, &mut path)?;
    }
    Ok(())
}

pub(crate) fn function_call_depths(program: &Program) -> HashMap<String, usize> {
    let names = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) => Some(function.name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut edges = HashMap::<String, HashSet<String>>::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let calls = edges.entry(function.name.clone()).or_default();
        for statement in &function.body {
            collect_statement_calls(statement, &names, calls);
        }
    }
    let mut depths = HashMap::new();
    for name in &names {
        let depth = call_depth(name, &edges, &mut depths);
        depths.insert(name.clone(), depth);
    }
    depths
}

fn call_depth(
    name: &str,
    edges: &HashMap<String, HashSet<String>>,
    depths: &mut HashMap<String, usize>,
) -> usize {
    if let Some(depth) = depths.get(name) {
        return *depth;
    }
    let depth = edges
        .get(name)
        .into_iter()
        .flat_map(|calls| calls.iter())
        .map(|called| call_depth(called, edges, depths))
        .max()
        .unwrap_or(0)
        + 1;
    depths.insert(name.to_owned(), depth);
    depth
}

fn visit_call_graph(
    name: &str,
    edges: &HashMap<String, HashSet<String>>,
    state: &mut HashMap<String, bool>,
    path: &mut Vec<String>,
) -> Result<(), String> {
    if state.get(name) == Some(&true) {
        let start = path.iter().position(|item| item == name).unwrap_or(0);
        let mut cycle = path[start..].to_vec();
        cycle.push(name.to_owned());
        return Err(format!(
            "recursive calls are not allowed: {}",
            cycle.join(" -> ")
        ));
    }
    if state.get(name) == Some(&false) {
        return Ok(());
    }
    state.insert(name.to_owned(), true);
    path.push(name.to_owned());
    if let Some(calls) = edges.get(name) {
        for called in calls {
            visit_call_graph(called, edges, state, path)?;
        }
    }
    path.pop();
    state.insert(name.to_owned(), false);
    Ok(())
}

fn collect_statement_calls(
    statement: &Statement,
    functions: &HashSet<String>,
    calls: &mut HashSet<String>,
) {
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
        | Statement::Expr(value) => collect_expression_calls(value, functions, calls),
        Statement::ArrayAssign { index, value, .. } => {
            collect_expression_calls(index, functions, calls);
            collect_expression_calls(value, functions, calls);
        }
        Statement::While { condition, body } => {
            collect_expression_calls(condition, functions, calls);
            for statement in body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::LetElse {
            value, else_body, ..
        } => {
            collect_expression_calls(value, functions, calls);
            for statement in else_body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_statement_calls(init, functions, calls);
            collect_expression_calls(condition, functions, calls);
            collect_statement_calls(step, functions, calls);
            for statement in body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::Labeled { statement, .. } => {
            collect_statement_calls(statement, functions, calls);
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
}

fn collect_expression_calls(
    expression: &Expr,
    functions: &HashSet<String>,
    calls: &mut HashSet<String>,
) {
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                let candidate = operator.split('<').next().unwrap_or(operator);
                if functions.contains(operator) {
                    calls.insert(operator.clone());
                } else if functions.contains(candidate) {
                    calls.insert(candidate.to_owned());
                }
            }
            for item in items {
                collect_expression_calls(item, functions, calls);
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Expr::Loop(statements) => {
            for statement in statements {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Expr::Labeled { expression, .. } => {
            collect_expression_calls(expression, functions, calls);
        }
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => collect_expression_calls(value, functions, calls),
        Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
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
    let mut parameter_names = HashSet::new();
    let return_type = resolve_type(&function.return_type, aliases)?;
    for parameter in &function.parameters {
        if !parameter_names.insert(parameter.name.clone()) {
            return Err(format!(
                "duplicate parameter '{}' in function '{}'",
                parameter.name, function.name
            ));
        }
        variables.insert(
            parameter.name.clone(),
            resolve_type(&parameter.ty, aliases)?,
        );
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
        Statement::Labeled { label, statement } => {
            let marker = format!("\0lim-label:{label}");
            if mutable.contains(&marker) {
                return Err(format!("duplicate loop label '{label}'"));
            }
            let mut labeled_mutable = mutable.clone();
            labeled_mutable.insert(marker);
            statement_type(
                statement,
                variables,
                &mut labeled_mutable,
                functions,
                structs,
                enums,
                return_type,
                aliases,
                in_loop,
            )
        }
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable: is_mutable,
        } => {
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
            require_type(&actual, &binding_type, "destructuring let")?;
            for (name, field_type) in check_destructure_pattern(pattern, &binding_type, structs)? {
                if variables.contains_key(&name) {
                    return Err(format!("duplicate local '{name}'"));
                }
                variables.insert(name.clone(), field_type);
                if *is_mutable {
                    mutable.insert(name);
                }
            }
            Ok(Type::Unit)
        }
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => {
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
            require_type(&actual, &binding_type, "let-else value")?;
            if !else_body.last().is_some_and(statement_diverges) {
                return Err(
                    "let-else body must diverge with return, break, continue, panic, or unreachable"
                        .into(),
                );
            }
            let mut else_variables = variables.clone();
            let mut else_mutable = mutable.clone();
            for statement in else_body {
                statement_type(
                    statement,
                    &mut else_variables,
                    &mut else_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    in_loop,
                )?;
            }
            for (name, field_type) in
                check_let_else_pattern(pattern, &binding_type, variables, structs, enums)?
            {
                if variables.contains_key(&name) {
                    return Err(format!("duplicate local '{name}'"));
                }
                variables.insert(name, field_type);
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
            if contains_reference_type(&ty, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "cannot replace '{name}' because its type retains references"
                ));
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
            if contains_reference_type(&element, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "cannot replace reference-containing elements of '{name}'"
                ));
            }
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
            if contains_reference_type(&field_type, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "reference field '{field}' in '{struct_name}' cannot be replaced"
                ));
            }
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
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Named(enum_name) = ty else {
                return Err(format!("'{name}' is not an enum"));
            };
            let variants = enums
                .get(&enum_name)
                .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
            let enum_variant = variants
                .iter()
                .find(|candidate| candidate.name == *variant)
                .ok_or_else(|| format!("enum '{enum_name}' has no variant '{variant}'"))?;
            let field_type = enum_variant.fields.get(*index).ok_or_else(|| {
                format!("variant '{variant}' has no payload field at index {index}")
            })?;
            if contains_reference_type(field_type, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "reference payload '{variant}[{index}]' cannot be replaced"
                ));
            }
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
                &format!("assignment to enum payload '{variant}[{index}]'"),
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
            if contains_reference_type(field_type, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "cannot replace reference-containing tuple field {index}"
                ));
            }
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
            if body.iter().any(statement_has_value_break) {
                return Err("break with a value is only valid in a loop expression".into());
            }
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
            if body.iter().any(statement_has_value_break) {
                return Err("break with a value is only valid in a loop expression".into());
            }
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
            if body.iter().any(statement_has_value_break) {
                return Err("break with a value is only valid in a loop expression".into());
            }
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
        Statement::BreakValue(value) => {
            if !mutable.contains(LOOP_VALUE_CONTEXT) {
                return Err("break with a value used outside a loop".into());
            }
            expression(
                value, variables, functions, structs, enums, mutable, aliases, None,
            )
        }
        Statement::BreakToValue { label, value } => {
            if !mutable.contains(&format!("\0lim-value-label:{label}")) {
                return Err(format!(
                    "value break used with inactive or non-value label '{label}'"
                ));
            }
            expression(
                value, variables, functions, structs, enums, mutable, aliases, None,
            )
        }
        Statement::BreakTo(label) | Statement::ContinueTo(label) => {
            if mutable.contains(&format!("\0lim-label:{label}")) {
                Ok(Type::Unit)
            } else {
                Err(format!("unknown or inactive loop label '{label}'"))
            }
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

fn statement_diverges(statement: &Statement) -> bool {
    match statement {
        Statement::Return(_) | Statement::Break | Statement::Continue => true,
        Statement::Labeled { statement, .. } => statement_diverges(statement),
        Statement::Expr(Expr::List(items)) => matches!(
            items.first(),
            Some(Expr::Symbol(name)) if matches!(name.as_str(), "panic" | "unreachable")
        ),
        _ => false,
    }
}

fn check_destructure_pattern(
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
            Expr::List(_) => {
                bindings.extend(check_destructure_pattern(binding, &field_type, structs)?)
            }
            _ => return Err("destructuring fields must be bindings or nested patterns".into()),
        }
    }
    Ok(bindings)
}

fn check_let_else_pattern(
    pattern: &Expr,
    ty: &Type,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<Vec<(String, Type)>, String> {
    let mut bindings = variables.clone();
    if let Type::Named(enum_name) = ty {
        if let Some(variants) = enums.get(enum_name) {
            if let Expr::List(items) = pattern {
                if items.len() >= 2
                    && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or")
                {
                    for alternative in &items[1..] {
                        let (name, payload_patterns): (&str, Vec<&Expr>) = match alternative {
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
                        if !payload_patterns.is_empty()
                            && payload_patterns.len() != variant.fields.len()
                        {
                            return Err(format!(
                                "variant '{name}' expects {} payload patterns",
                                variant.fields.len()
                            ));
                        }
                        let mut alternative_variables = variables.clone();
                        for (binding, field_type) in payload_patterns.iter().zip(&variant.fields) {
                            check_enum_payload_pattern(
                                binding,
                                field_type,
                                &mut alternative_variables,
                                variables,
                                structs,
                            )?;
                        }
                        if alternative_variables.len() != variables.len() {
                            return Err("enum let-else alternatives cannot bind values".into());
                        }
                    }
                    return Ok(Vec::new());
                }
            }
            let (variant_name, payload_patterns): (&str, Vec<&Expr>) = match pattern {
                Expr::Symbol(name) => (name, Vec::new()),
                Expr::List(items) if !items.is_empty() => {
                    let Expr::Symbol(name) = &items[0] else {
                        return Err("let-else enum pattern must start with a variant".into());
                    };
                    (name, items[1..].iter().collect())
                }
                _ => return Err("let-else pattern must be a variant constructor".into()),
            };
            if variant_name == "_" {
                return Ok(Vec::new());
            }
            let variant = variants
                .iter()
                .find(|variant| variant.name == variant_name)
                .ok_or_else(|| format!("'{variant_name}' is not a variant of '{enum_name}'"))?;
            if payload_patterns.len() != variant.fields.len() {
                return Err(format!(
                    "variant '{variant_name}' expects {} payload patterns",
                    variant.fields.len()
                ));
            }
            for (binding, field_type) in payload_patterns.iter().zip(&variant.fields) {
                check_enum_payload_pattern(binding, field_type, &mut bindings, variables, structs)?;
            }
            return Ok(bindings
                .into_iter()
                .filter(|(name, _)| !variables.contains_key(name))
                .collect());
        }
    }
    check_aggregate_pattern(pattern, ty, &mut bindings, variables, structs)?;
    Ok(bindings
        .into_iter()
        .filter(|(name, _)| !variables.contains_key(name))
        .collect())
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
        Expr::String(value) => Ok(Type::Array(Box::new(Type::Char), value.chars().count())),
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
        Expr::Loop(statements) => {
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            loop_mutable.insert(LOOP_VALUE_CONTEXT.to_owned());
            let mut result_type = None;
            for statement in statements {
                let has_value_break = statement_has_value_break(statement);
                let actual = if let Statement::BreakValue(value)
                | Statement::BreakToValue { value, .. } = statement
                {
                    expression(
                        value,
                        &loop_variables,
                        functions,
                        structs,
                        enums,
                        &loop_mutable,
                        aliases,
                        expected,
                    )?
                } else {
                    statement_type(
                        statement,
                        &mut loop_variables,
                        &mut loop_mutable,
                        functions,
                        structs,
                        enums,
                        &expected.cloned().unwrap_or(Type::Unit),
                        aliases,
                        true,
                    )?
                };
                if has_value_break {
                    if let Some(previous) = &result_type {
                        result_type = Some(merge_types(previous, &actual, "loop break values")?);
                    } else {
                        result_type = Some(actual);
                    }
                }
            }
            let result = result_type.unwrap_or(Type::Unit);
            if let Some(expected) = expected {
                require_type(&result, expected, "loop expression")?;
            }
            Ok(result)
        }
        Expr::Labeled {
            label,
            expression: loop_expression,
        } => {
            if !matches!(loop_expression.as_ref(), Expr::Loop(_)) {
                return Err("expression label must wrap a value-producing loop".into());
            }
            let marker = format!("\0lim-label:{label}");
            if mutable.contains(&marker) {
                return Err(format!("duplicate loop label '{label}'"));
            }
            let mut labeled_mutable = mutable.clone();
            labeled_mutable.insert(marker);
            labeled_mutable.insert(format!("\0lim-value-label:{label}"));
            expression(
                loop_expression,
                variables,
                functions,
                structs,
                enums,
                &labeled_mutable,
                aliases,
                expected,
            )
        }
        Expr::At
        | Expr::Quote(_)
        | Expr::QuasiQuote(_)
        | Expr::Unquote(_)
        | Expr::UnquoteSplicing(_) => {
            Err("generated and quoted expressions are not typed yet".into())
        }
        Expr::List(items) => list_expression(
            items, variables, functions, structs, enums, mutable, aliases, expected,
        ),
    }
}

fn statement_has_value_break(statement: &Statement) -> bool {
    match statement {
        Statement::BreakValue(_) | Statement::BreakToValue { .. } => true,
        Statement::Expr(expression) => expression_has_value_break(expression),
        Statement::While { .. } | Statement::Loop { .. } | Statement::For { .. } => false,
        _ => false,
    }
}

fn expression_has_value_break(expression: &Expr) -> bool {
    match expression {
        Expr::Loop(_) | Expr::Labeled { .. } => false,
        Expr::Block(statements) => statements.iter().any(statement_has_value_break),
        Expr::List(items) => {
            if matches!(
                items.first(),
                Some(Expr::Symbol(name))
                    if matches!(name.as_str(), "loop" | "while" | "while-let" | "for" | "for-range")
            ) {
                false
            } else {
                items.iter().any(expression_has_value_break)
            }
        }
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => expression_has_value_break(value),
        _ => false,
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
    let raw_operator = operator.as_str();
    if raw_operator.contains('<') && raw_operator.contains('>') && !raw_operator.starts_with('#') {
        return Err(
            "angle-bracket generic calls are not supported; use a concrete generated function"
                .into(),
        );
    }
    let (qualifier, operator, mode) = typed_operator_parts(raw_operator);
    let operator_type = qualifier.map(Type::from_name);
    match operator {
        "clone" => {
            require_arity(operator, items, 2)?;
            let cloned = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            if type_contains_mutable_reference(&cloned, structs, enums, &mut HashSet::new()) {
                return Err("a mutable reference cannot be cloned".into());
            }
            if let Type::Named(name) = &cloned {
                if functions.contains_key(&format!("{name}-join")) {
                    return Err(format!("thread task '{name}' cannot be cloned"));
                }
                if let Some(signature) = functions.get(&format!("{name}-clone")) {
                    if signature.parameters != [cloned.clone()] || signature.return_type != cloned {
                        return Err(format!(
                            "'{name}-clone' must take and return exactly one '{name}' value"
                        ));
                    }
                }
            }
            Ok(cloned)
        }
        "drop" | "forget" => {
            require_arity(operator, items, 2)?;
            let forgotten = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            if let Type::Named(name) = &forgotten {
                if functions.contains_key(&format!("{name}-join")) {
                    return Err(format!(
                        "thread task '{name}' must be joined; it cannot be dropped or forgotten"
                    ));
                }
            }
            Ok(Type::Unit)
        }
        "cell" => {
            require_arity(operator, items, 2)?;
            let expected_inner = match expected {
                Some(Type::Cell(inner)) => Some(inner.as_ref()),
                _ => None,
            };
            let inner = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                expected_inner,
            )?;
            if !is_cell_value_type(&inner, enums) {
                return Err(format!("cell does not support values of type {inner:?}"));
            }
            Ok(Type::Cell(Box::new(inner)))
        }
        "cell-get" => {
            require_arity(operator, items, 2)?;
            match expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )? {
                Type::Cell(inner) => Ok(*inner),
                _ => Err("cell-get requires a cell place".into()),
            }
        }
        "cell-set" => {
            require_arity(operator, items, 3)?;
            let Type::Cell(inner) = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err("cell-set requires a cell place".into());
            };
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&inner),
            )?;
            require_type(&actual, &inner, "cell-set value")?;
            Ok(Type::Unit)
        }
        "-" if items.len() == 2 => {
            let actual = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            if !is_numeric(&actual) {
                return Err("unary '-' requires a numeric operand".into());
            }
            if let Some(qualifier) = qualifier {
                require_operator_type(qualifier, &actual, raw_operator)?;
                require_arithmetic_mode(operator, mode, raw_operator, &actual)?;
            }
            Ok(actual)
        }
        "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" => {
            require_arity(operator, items, 3)?;
            let left = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                operator_type.as_ref().or(expected),
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
            if let Some(qualifier) = qualifier {
                require_operator_type(qualifier, &left, raw_operator)?;
                require_arithmetic_mode(operator, mode, raw_operator, &left)?;
            }
            let bitwise = matches!(operator, "&" | "|" | "^");
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
            if matches!(operator, "<<" | ">>") {
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
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                operator_type.as_ref(),
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
            if let Some(qualifier) = qualifier {
                require_operator_type(qualifier, &left, raw_operator)?;
            }
            if !is_numeric(&left) && !matches!(left, Type::Bool | Type::Char) {
                return Err(format!(
                    "comparison operator '{operator}' requires scalar operands"
                ));
            }
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
                if matches!(then_type, Type::Never) {
                    expected
                } else {
                    Some(&then_type)
                },
            )?;
            merge_types(&then_type, &else_type, "if branches")
        }
        "as" => {
            require_arity(operator, items, 3)?;
            let source = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let target = resolve_type(&parse_type(items.get(2))?, aliases)?;
            let fieldless_enum = matches!(&source, Type::Named(name)
            if enums.get(name).is_some_and(|variants| {
                variants.iter().all(|variant| variant.fields.is_empty())
            }));
            if (!is_cast_operand(&source) && !fieldless_enum)
                || !is_cast_target(&target)
                || (fieldless_enum && !is_integer(&target))
            {
                return Err(
                    "as requires numeric, char, or bool operands and a numeric or char target"
                        .into(),
                );
            }
            Ok(target)
        }
        "literal" => {
            require_arity(operator, items, 3)?;
            let ty = resolve_type(&parse_type(items.get(1))?, aliases)?;
            if !is_integer(&ty) && !matches!(ty, Type::F32 | Type::F64) {
                return Err("typed literal suffix must name a numeric type".into());
            }
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&ty),
            )?;
            require_type(&actual, &ty, "typed literal")?;
            Ok(ty)
        }
        "borrow" | "borrow-mut" => {
            if items.len() == 2 {
                let (target, base_mutable) = match &items[1] {
                    Expr::Symbol(name) => {
                        let owner_type = variables.get(name).ok_or_else(|| {
                            format!("{operator} refers to unknown variable '{name}'")
                        })?;
                        if matches!(owner_type, Type::Reference { .. }) {
                            return Err(format!(
                                "{operator} cannot borrow a reference variable directly; borrow one of its fields"
                            ));
                        }
                        (owner_type.clone(), mutable.contains(name))
                    }
                    Expr::List(place)
                        if (place.len() == 3
                            && matches!(place.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index"))
                            || (place.len() == 4
                                && matches!(place.first(), Some(Expr::Symbol(name)) if name == "get-payload")) =>
                    {
                        let root = projection_root(&place[1]).ok_or_else(|| {
                            format!("{operator} projection borrowing requires a reference")
                        })?;
                        let base_type = expression(
                            root, variables, functions, structs, enums, mutable, aliases, None,
                        )?;
                        let Type::Reference {
                            mutable: reference_mutable,
                            target,
                        } = base_type
                        else {
                            return Err(format!(
                                "{operator} projection borrowing requires a reference"
                            ));
                        };
                        let _ = target;
                        let field_type = expression(
                            &items[1], variables, functions, structs, enums, mutable, aliases, None,
                        )?;
                        (field_type, reference_mutable)
                    }
                    _ => {
                        return Err(format!(
                            "{operator} requires a variable or a struct field through a reference"
                        ))
                    }
                };
                if operator == "borrow-mut" && !base_mutable {
                    return Err("cannot mutably borrow through an immutable reference".into());
                }
                if !is_reference_target(&target) {
                    return Err(format!("{operator} cannot borrow a unit or never value"));
                }
                return Ok(Type::Reference {
                    mutable: operator == "borrow-mut",
                    target: Box::new(target),
                });
            }
            require_arity(operator, items, 3)?;
            match &items[1] {
                Expr::Symbol(owner) => {
                    if !variables.contains_key(owner) {
                        return Err(format!("{operator} refers to unknown variable '{owner}'"));
                    }
                    if operator == "borrow-mut" && !mutable.contains(owner) {
                        return Err(format!(
                            "cannot mutably borrow immutable variable '{owner}'"
                        ));
                    }
                }
                Expr::List(place)
                    if (matches!(place.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index")
                        && place.len() == 3)
                        || (matches!(place.first(), Some(Expr::Symbol(name)) if name == "get-payload")
                            && place.len() == 4) =>
                {
                    let root = projection_root(&items[1]).ok_or_else(|| {
                        format!("{operator} projection borrowing requires a reference")
                    })?;
                    let Type::Reference {
                        mutable: reference_mutable,
                        ..
                    } = expression(
                        root, variables, functions, structs, enums, mutable, aliases, None,
                    )?
                    else {
                        return Err(format!(
                            "{operator} projection borrowing requires a reference"
                        ));
                    };
                    if operator == "borrow-mut" && !reference_mutable {
                        return Err("cannot mutably borrow through an immutable reference".into());
                    }
                    expression(
                        &items[1], variables, functions, structs, enums, mutable, aliases, None,
                    )?;
                }
                _ => {
                    return Err(format!(
                        "{operator} requires a variable or a struct field through a reference"
                    ))
                }
            }
            expression(
                &items[2], variables, functions, structs, enums, mutable, aliases, expected,
            )
        }
        "deref" => {
            require_arity(operator, items, 2)?;
            let actual = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            match actual {
                Type::Reference { target, .. } => Ok(*target),
                _ => Err("deref requires a reference".into()),
            }
        }
        "deref-set" => {
            require_arity(operator, items, 3)?;
            let reference_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::Reference {
                mutable: true,
                target,
            } = reference_type
            else {
                return Err("deref-set requires a mutable reference".into());
            };
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&target),
            )?;
            require_type(&actual, &target, "deref-set value")?;
            Ok(Type::Unit)
        }
        "unsafe" => {
            require_arity(operator, items, 2)?;
            expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )
        }
        "addr-of" | "addr-of-mut" => {
            require_arity(operator, items, 2)?;
            let owner = match &items[1] {
                Expr::Symbol(name) => name,
                _ => return Err(format!("{operator} requires a variable name")),
            };
            let owner_type = variables
                .get(owner)
                .ok_or_else(|| format!("{operator} refers to unknown variable '{owner}'"))?;
            if !is_scalar_reference_target(owner_type, enums) {
                return Err(format!("{operator} currently supports scalar values only"));
            }
            if operator == "addr-of-mut" && !mutable.contains(owner) {
                return Err(format!(
                    "cannot take a mutable pointer to immutable variable '{owner}'"
                ));
            }
            Ok(Type::RawPointer {
                mutable: operator == "addr-of-mut",
                target: Box::new(owner_type.clone()),
            })
        }
        "ptr-read" => {
            require_arity(operator, items, 2)?;
            let actual = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            match actual {
                Type::RawPointer { target, .. } => Ok(*target),
                _ => Err("ptr-read requires a raw pointer".into()),
            }
        }
        "ptr-write" => {
            require_arity(operator, items, 3)?;
            let pointer = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::RawPointer {
                mutable: true,
                target,
            } = pointer
            else {
                return Err("ptr-write requires a mutable raw pointer".into());
            };
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&target),
            )?;
            require_type(&actual, &target, "ptr-write value")?;
            Ok(Type::Unit)
        }
        "size-of" | "align-of" => {
            require_arity(operator, items, 2)?;
            let ty = resolve_type(&parse_type(items.get(1))?, aliases)?;
            validate_layout_type(&ty, structs, enums)?;
            Ok(Type::Usize)
        }
        "array" => {
            let (element, length, value_start) = match expected {
                Some(Type::Array(element, length)) => {
                    let explicit = parse_type(items.get(1))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, aliases).ok())
                        .is_some_and(|ty| ty == Type::Array(element.clone(), *length));
                    (
                        element.clone(),
                        *length,
                        if explicit && items.len() >= 2 { 2 } else { 1 },
                    )
                }
                Some(_) => {
                    return Err("array construction requires an array-typed expected value".into())
                }
                None => {
                    let declared = resolve_type(
                        &parse_type(items.get(1)).map_err(|_| {
                            "direct array constructors require an explicit (array Element Length) type"
                                .to_owned()
                        })?,
                        aliases,
                    )?;
                    let Type::Array(element, length) = declared else {
                        return Err("direct array constructors require an explicit (array Element Length) type".into());
                    };
                    (element, length, 2)
                }
            };
            if items.len() - value_start != length {
                return Err(format!("array constructor expects {length} elements"));
            }
            for value in &items[value_start..] {
                let actual = expression(
                    value,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(element.as_ref()),
                )?;
                require_type(&actual, element.as_ref(), "array element")?;
            }
            Ok(Type::Array(element, length))
        }
        "array-repeat" => {
            let (element, length, value_index) = match expected {
                Some(Type::Array(element, length)) => (element.clone(), *length, 1),
                Some(_) => {
                    return Err(
                        "array-repeat construction requires an array-typed expected value".into(),
                    )
                }
                None => {
                    let declared = resolve_type(
                        &parse_type(items.get(1)).map_err(|_| {
                            "direct array-repeat constructors require an explicit (array Element Length) type"
                                .to_owned()
                        })?,
                        aliases,
                    )?;
                    let Type::Array(element, length) = declared else {
                        return Err("direct array-repeat constructors require an explicit (array Element Length) type".into());
                    };
                    (element, length, 2)
                }
            };
            if items.len() != value_index + 1 {
                return Err("array-repeat requires one value".into());
            }
            let actual = expression(
                &items[value_index],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(element.as_ref()),
            )?;
            require_type(&actual, element.as_ref(), "array-repeat element")?;
            Ok(Type::Array(element, length))
        }
        "tuple" => {
            let (fields, value_start) = match expected {
                Some(Type::Tuple(fields)) => {
                    let explicit = parse_type(items.get(1))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, aliases).ok())
                        .is_some_and(|ty| ty == Type::Tuple(fields.clone()));
                    (
                        fields.clone(),
                        if explicit && items.len() >= 2 { 2 } else { 1 },
                    )
                }
                Some(_) => {
                    return Err("tuple construction requires an expected (tuple ...) type".into())
                }
                None => {
                    let declared = parse_type(items.get(1)).map_err(|_| {
                        "direct tuple constructors require an explicit (tuple Type ...) type"
                            .to_owned()
                    })?;
                    let Type::Tuple(fields) = declared else {
                        return Err(
                            "direct tuple constructors require an explicit (tuple Type ...) type"
                                .into(),
                        );
                    };
                    (fields, 2)
                }
            };
            if items.len() - value_start != fields.len() {
                return Err(format!(
                    "tuple constructor expects {} elements",
                    fields.len()
                ));
            }
            for (value, field) in items[value_start..].iter().zip(fields.iter()) {
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
            let array_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let array_type = match array_type {
                Type::Reference { target, .. } => *target,
                other => other,
            };
            let Type::Array(element, length) = array_type else {
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
            if matches!(scrutinee, Type::Tuple(_)) {
                return check_tuple_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            }
            if matches!(scrutinee, Type::Array(_, _)) {
                return check_array_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            }
            if let Type::Named(struct_name) = &scrutinee {
                if structs.contains_key(struct_name) {
                    return check_struct_match(
                        items,
                        struct_name,
                        variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        expected,
                    );
                }
            }
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
                let (pattern_expr, guard, body) = match_arm_parts(arm)?;
                let (pattern, payload_patterns, alternatives) = match pattern_expr {
                    Expr::Symbol(pattern) => (pattern.as_str(), Vec::new(), Vec::new()),
                    Expr::List(pattern)
                        if pattern.len() >= 2
                            && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
                    {
                        let alternatives = pattern[1..]
                            .iter()
                            .map(|alternative| match alternative {
                                Expr::Symbol(name) => Ok((name.as_str(), Vec::new())),
                                Expr::List(items) if !items.is_empty() => {
                                    let Expr::Symbol(name) = &items[0] else {
                                        return Err(
                                            "enum or-pattern alternatives must be variants"
                                                .to_owned(),
                                        );
                                    };
                                    Ok((name.as_str(), items[1..].iter().collect()))
                                }
                                _ => {
                                    Err("enum or-pattern alternatives must be variants".to_owned())
                                }
                            })
                            .collect::<Result<Vec<(&str, Vec<&Expr>)>, String>>()?;
                        ("", Vec::new(), alternatives)
                    }
                    Expr::List(pattern) if !pattern.is_empty() => {
                        let variant = match &pattern[0] {
                            Expr::Symbol(variant) => variant.as_str(),
                            _ => return Err("match variant pattern must be a symbol".into()),
                        };
                        let payloads = pattern[1..].iter().collect::<Vec<_>>();
                        (variant, payloads, Vec::new())
                    }
                    _ => return Err("match pattern must be a symbol or (variant _)".into()),
                };
                if !alternatives.is_empty() {
                    for (alternative, alternative_payloads) in alternatives {
                        let Some(variant) =
                            variants.iter().find(|variant| variant.name == alternative)
                        else {
                            return Err(format!(
                                "'{alternative}' is not a variant of '{enum_name}'"
                            ));
                        };
                        if !alternative_payloads.is_empty()
                            && alternative_payloads.len() != variant.fields.len()
                        {
                            return Err(format!(
                                "variant '{alternative}' expects {} payload patterns",
                                variant.fields.len()
                            ));
                        }
                        let mut alternative_variables = variables.clone();
                        for (binding, field_type) in
                            alternative_payloads.iter().zip(&variant.fields)
                        {
                            check_enum_payload_pattern(
                                binding,
                                field_type,
                                &mut alternative_variables,
                                variables,
                                structs,
                            )?;
                        }
                        if alternative_variables.len() != variables.len() {
                            return Err("enum or-pattern alternatives cannot bind values".into());
                        }
                        if guard.is_none() && !seen.contains(&alternative) {
                            seen.push(alternative);
                        }
                    }
                } else if pattern == "_" {
                    if !payload_patterns.is_empty() {
                        return Err("wildcard pattern cannot have a payload".into());
                    }
                    if guard.is_none() && wildcard {
                        return Err("duplicate wildcard match pattern".into());
                    }
                    if guard.is_none() {
                        wildcard = true;
                    }
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
                    if guard.is_none() && seen.contains(&pattern) {
                        return Err(format!("duplicate enum match pattern '{pattern}'"));
                    }
                    if guard.is_none() {
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
                        check_enum_payload_pattern(
                            binding,
                            field_type,
                            &mut arm_variables,
                            variables,
                            structs,
                        )?;
                    }
                }
                if let Some(guard) = guard {
                    let guard_type = expression(
                        guard,
                        &arm_variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        Some(&Type::Bool),
                    )?;
                    require_type(&guard_type, &Type::Bool, "match guard")?;
                }
                let arm_type = expression(
                    body,
                    &arm_variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    result_type
                        .as_ref()
                        .filter(|ty| !matches!(ty, Type::Never))
                        .or(expected),
                )?;
                if let Some(previous) = &result_type {
                    result_type = Some(merge_types(previous, &arm_type, "match arms")?);
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
        "panic" | "unreachable" => {
            require_arity(operator, items, 1)?;
            Ok(Type::Never)
        }
        "let" => Err("let is only valid as a statement".into()),
        "get" => {
            if items.len() != 3 {
                return Err("get requires the form (get value field)".into());
            }
            let value_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let value_type = match value_type {
                Type::Reference { target, .. } => *target,
                other => other,
            };
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
        "get-payload" => {
            if items.len() != 4 {
                return Err(
                    "get-payload requires the form (get-payload enum variant index)".into(),
                );
            }
            let value_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let value_type = match value_type {
                Type::Reference { target, .. } => *target,
                other => other,
            };
            let Type::Named(enum_name) = value_type else {
                return Err("get-payload requires an enum value".into());
            };
            let Expr::Symbol(variant_name) = &items[2] else {
                return Err("get-payload requires a variant name".into());
            };
            let index = match &items[3] {
                Expr::Integer(index) if *index >= 0 => usize::try_from(*index)
                    .map_err(|_| "enum payload index is too large".to_owned())?,
                Expr::UnsignedInteger(index) => usize::try_from(*index)
                    .map_err(|_| "enum payload index is too large".to_owned())?,
                _ => return Err("get-payload requires a non-negative integer index".into()),
            };
            let variants = enums
                .get(&enum_name)
                .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
            let variant = variants
                .iter()
                .find(|variant| variant.name == *variant_name)
                .ok_or_else(|| format!("enum '{enum_name}' has no variant '{variant_name}'"))?;
            variant.fields.get(index).cloned().ok_or_else(|| {
                format!("variant '{variant_name}' has no payload field at index {index}")
            })
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
                return Ok(Type::Named(operator.to_owned()));
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

fn projection_root(expression: &Expr) -> Option<&Expr> {
    match expression {
        Expr::Symbol(_) => Some(expression),
        Expr::List(items)
            if (items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index"))
                || (items.len() == 4
                    && matches!(items.first(), Some(Expr::Symbol(name)) if name == "get-payload")) =>
        {
            projection_root(&items[1])
        }
        _ => None,
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
    let mut seen_unsigned_integers = HashSet::new();
    let mut seen_chars = HashSet::new();
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        match pattern {
            pattern if is_typed_integer_pattern(pattern) => {
                check_scalar_pattern(pattern, scrutinee)?;
            }
            Expr::List(parts)
                if parts.len() >= 2
                    && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if parts[1..]
                    .iter()
                    .any(|alternative| matches!(alternative, Expr::Symbol(name) if name == "_"))
                    && guard.is_none()
                {
                    wildcard = true;
                }
                for alternative in &parts[1..] {
                    check_scalar_pattern(alternative, scrutinee)?;
                    if let Expr::Symbol(name) = alternative {
                        if matches!(scrutinee, Type::Bool)
                            && matches!(name.as_str(), "true" | "false")
                        {
                            let index = usize::from(name == "true");
                            if seen_bool[index] {
                                return Err(format!("duplicate boolean match pattern '{name}'"));
                            }
                            seen_bool[index] = true;
                        }
                    }
                }
            }
            Expr::List(parts)
                if parts.len() == 3
                    && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "range") =>
            {
                check_scalar_range_pattern(parts, scrutinee)?;
            }
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
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
            Expr::UnsignedInteger(value) if is_integer(scrutinee) => {
                if !fits_unsigned_integer(*value, scrutinee) {
                    return Err(format!(
                        "unsigned integer match pattern {value} does not fit in {scrutinee:?}"
                    ));
                }
                if !seen_unsigned_integers.insert(*value) {
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
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard && !(matches!(scrutinee, Type::Bool) && seen_bool.iter().all(|seen| *seen)) {
        return Err("match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_scalar_pattern(pattern: &Expr, scrutinee: &Type) -> Result<(), String> {
    if let Some(value) = typed_integer_pattern_value(pattern, scrutinee)? {
        return check_scalar_pattern(value, scrutinee);
    }
    if let Expr::List(parts) = pattern {
        if parts.len() >= 2 && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or") {
            for alternative in &parts[1..] {
                check_scalar_pattern(alternative, scrutinee)?;
            }
            return Ok(());
        }
    }
    match pattern {
        Expr::List(parts)
            if parts.len() == 3
                && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "range") =>
        {
            check_scalar_range_pattern(parts, scrutinee)
        }
        Expr::Symbol(name) if name == "_" => Ok(()),
        Expr::Symbol(name)
            if matches!(scrutinee, Type::Bool) && matches!(name.as_str(), "true" | "false") =>
        {
            Ok(())
        }
        Expr::Integer(value) if is_integer(scrutinee) && fits_integer(*value, scrutinee) => Ok(()),
        Expr::UnsignedInteger(value)
            if is_integer(scrutinee) && fits_unsigned_integer(*value, scrutinee) =>
        {
            Ok(())
        }
        Expr::Char(_) if matches!(scrutinee, Type::Char) => Ok(()),
        _ => Err("scalar or-pattern alternative does not match the scrutinee type".into()),
    }
}

fn check_scalar_range_pattern(parts: &[Expr], scrutinee: &Type) -> Result<(), String> {
    if is_integer(scrutinee) {
        let signed = matches!(
            scrutinee,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::Isize
        );
        if signed {
            let lower_expression = range_bound_expression(&parts[1], scrutinee)?;
            let upper_expression = range_bound_expression(&parts[2], scrutinee)?;
            let lower = signed_range_bound(lower_expression)?;
            let upper = signed_range_bound(upper_expression)?;
            if !fits_integer(lower, scrutinee) || !fits_integer(upper, scrutinee) {
                return Err("integer range pattern does not fit its scrutinee type".into());
            }
            if lower > upper {
                return Err("integer range pattern lower bound exceeds upper bound".into());
            }
        } else {
            let lower_expression = range_bound_expression(&parts[1], scrutinee)?;
            let upper_expression = range_bound_expression(&parts[2], scrutinee)?;
            let lower = unsigned_range_bound(lower_expression)?;
            let upper = unsigned_range_bound(upper_expression)?;
            if !fits_unsigned_integer(lower, scrutinee) || !fits_unsigned_integer(upper, scrutinee)
            {
                return Err("unsigned range pattern does not fit its scrutinee type".into());
            }
            if lower > upper {
                return Err("unsigned range pattern lower bound exceeds upper bound".into());
            }
        }
        return Ok(());
    }
    if matches!(scrutinee, Type::Char) {
        let Expr::Char(lower) = parts[1] else {
            return Err("character range patterns require character bounds".into());
        };
        let Expr::Char(upper) = parts[2] else {
            return Err("character range patterns require character bounds".into());
        };
        if lower > upper {
            return Err("character range pattern lower bound exceeds upper bound".into());
        }
        return Ok(());
    }
    Err("range patterns require an integer or char scrutinee".into())
}

fn is_typed_integer_pattern(pattern: &Expr) -> bool {
    matches!(
        pattern,
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "literal")
    )
}

fn typed_integer_pattern_value<'a>(
    pattern: &'a Expr,
    scrutinee: &Type,
) -> Result<Option<&'a Expr>, String> {
    let Expr::List(items) = pattern else {
        return Ok(None);
    };
    if !is_typed_integer_pattern(pattern) {
        return Ok(None);
    }
    let literal_type = parse_type(items.get(1))?;
    if literal_type != *scrutinee || !is_integer(&literal_type) {
        return Err(format!(
            "typed integer pattern has type {literal_type:?}, expected {scrutinee:?}"
        ));
    }
    if !matches!(items[2], Expr::Integer(_) | Expr::UnsignedInteger(_)) {
        return Err("typed integer pattern requires an integer literal".into());
    }
    Ok(Some(&items[2]))
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
        Expr::UnsignedInteger(value) => {
            i128::try_from(*value).map_err(|_| "signed range bound is too large".to_owned())
        }
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

fn check_tuple_match(
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
    let Type::Tuple(fields) = scrutinee else {
        unreachable!()
    };
    let mut wildcard = false;
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        let mut arm_variables = variables.clone();
        match pattern {
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern)
                if pattern.len() >= 2
                    && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if check_aggregate_or_pattern(pattern, scrutinee, structs)? && guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern) if matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "tuple") =>
            {
                if pattern.len() - 1 != fields.len() {
                    return Err(format!(
                        "tuple match pattern expects {} elements",
                        fields.len()
                    ));
                }
                for (pattern, field) in pattern[1..].iter().zip(fields) {
                    check_aggregate_pattern(
                        pattern,
                        field,
                        &mut arm_variables,
                        variables,
                        structs,
                    )?;
                }
            }
            _ => return Err("tuple match pattern must be _ or (tuple pattern ...)".into()),
        }
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                &arm_variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            &arm_variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err("tuple match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_aggregate_pattern(
    pattern: &Expr,
    ty: &Type,
    arm_variables: &mut HashMap<String, Type>,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    if let Some(value) = typed_integer_pattern_value(pattern, ty)? {
        return check_aggregate_pattern(value, ty, arm_variables, variables, structs);
    }
    if let Expr::List(items) = pattern {
        if items.len() == 3 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "range")
        {
            return check_scalar_range_pattern(items, ty);
        }
        if items.len() >= 2 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or") {
            if is_integer(ty) || matches!(ty, Type::Char | Type::Bool) {
                return check_scalar_pattern(pattern, ty);
            }
            check_aggregate_or_pattern(items, ty, structs)?;
            return Ok(());
        }
    }
    match pattern {
        Expr::Symbol(name) if name == "_" => Ok(()),
        Expr::Symbol(name) if name == "true" || name == "false" => {
            if !matches!(ty, Type::Bool) {
                return Err("boolean tuple pattern does not match its field type".into());
            }
            Ok(())
        }
        Expr::Symbol(name) => {
            if variables.contains_key(name) || arm_variables.contains_key(name) {
                return Err(format!("duplicate match binding '{name}'"));
            }
            arm_variables.insert(name.clone(), ty.clone());
            Ok(())
        }
        Expr::Integer(value) if is_integer(ty) => {
            if !fits_integer(*value, ty) {
                return Err(format!(
                    "integer match pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::UnsignedInteger(value) if is_integer(ty) => {
            if !fits_unsigned_integer(*value, ty) {
                return Err(format!(
                    "unsigned integer match pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::Char(_) if matches!(ty, Type::Char) => Ok(()),
        Expr::List(items) => {
            let Some(Expr::Symbol(constructor)) = items.first() else {
                return Err("aggregate pattern must start with a constructor".into());
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
                _ => {
                    return Err(
                        "aggregate pattern constructor does not match its field type".into(),
                    )
                }
            };
            if items.len() - 1 != fields.len() {
                return Err(format!("aggregate pattern expects {} fields", fields.len()));
            }
            for (nested, field) in items[1..].iter().zip(fields) {
                check_aggregate_pattern(nested, &field, arm_variables, variables, structs)?;
            }
            Ok(())
        }
        _ => Err("tuple field pattern does not match its field type".into()),
    }
}

fn check_aggregate_or_pattern(
    pattern: &[Expr],
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<bool, String> {
    let mut wildcard = false;
    for alternative in &pattern[1..] {
        if matches!(alternative, Expr::Symbol(name) if name == "_") {
            wildcard = true;
        }
        let mut bindings = HashMap::new();
        check_aggregate_pattern(alternative, ty, &mut bindings, &HashMap::new(), structs)?;
        if !bindings.is_empty() {
            return Err("aggregate or-pattern alternatives cannot bind values".into());
        }
    }
    Ok(wildcard)
}

fn check_array_match(
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
    let Type::Array(element, length) = scrutinee else {
        unreachable!()
    };
    let fields = vec![element.as_ref().clone(); *length];
    let mut wildcard = false;
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        let mut arm_variables = variables.clone();
        match pattern {
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern)
                if pattern.len() >= 2
                    && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if check_aggregate_or_pattern(pattern, scrutinee, structs)? && guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern) if matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "array") =>
            {
                if pattern.len() - 1 != *length {
                    return Err(format!("array match pattern expects {} elements", length));
                }
                for (pattern, field) in pattern[1..].iter().zip(&fields) {
                    check_aggregate_pattern(
                        pattern,
                        field,
                        &mut arm_variables,
                        variables,
                        structs,
                    )?;
                }
            }
            _ => return Err("array match pattern must be _ or (array pattern ...)".into()),
        }
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                &arm_variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            &arm_variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err("array match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_enum_payload_pattern(
    pattern: &Expr,
    ty: &Type,
    arm_variables: &mut HashMap<String, Type>,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    if let Some(value) = typed_integer_pattern_value(pattern, ty)? {
        return check_enum_payload_pattern(value, ty, arm_variables, variables, structs);
    }
    if let Expr::List(items) = pattern {
        if items.len() == 3 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "range")
        {
            return check_scalar_range_pattern(items, ty);
        }
    }
    match pattern {
        Expr::Symbol(name) if name == "_" => Ok(()),
        Expr::Symbol(name) if name == "true" || name == "false" => {
            if !matches!(ty, Type::Bool) {
                return Err("boolean enum payload pattern does not match its field type".into());
            }
            Ok(())
        }
        Expr::Symbol(name) => {
            if variables.contains_key(name) || arm_variables.contains_key(name) {
                return Err(format!("duplicate match binding '{name}'"));
            }
            arm_variables.insert(name.clone(), ty.clone());
            Ok(())
        }
        Expr::List(parts)
            if parts.len() >= 2
                && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or") =>
        {
            for alternative in &parts[1..] {
                check_scalar_pattern(alternative, ty)?;
            }
            Ok(())
        }
        Expr::Integer(value) if is_integer(ty) => {
            if !fits_integer(*value, ty) {
                return Err(format!(
                    "integer enum payload pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::UnsignedInteger(value) if is_integer(ty) => {
            if !fits_unsigned_integer(*value, ty) {
                return Err(format!(
                    "unsigned enum payload pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::Char(_) if matches!(ty, Type::Char) => Ok(()),
        Expr::List(_) => check_aggregate_pattern(pattern, ty, arm_variables, variables, structs),
        _ => Err("enum payload pattern does not match its field type".into()),
    }
}

fn check_struct_match(
    items: &[Expr],
    struct_name: &str,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    let fields = structs
        .get(struct_name)
        .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
    let mut wildcard = false;
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        let mut arm_variables = variables.clone();
        match pattern {
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern)
                if pattern.len() >= 2
                    && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if check_aggregate_or_pattern(
                    pattern,
                    &Type::Named(struct_name.to_owned()),
                    structs,
                )? && guard.is_none()
                {
                    wildcard = true;
                }
            }
            Expr::List(pattern) if matches!(pattern.first(), Some(Expr::Symbol(name)) if name == struct_name) =>
            {
                if pattern.len() - 1 != fields.len() {
                    return Err(format!(
                        "struct match pattern expects {} fields",
                        fields.len()
                    ));
                }
                for (pattern, field) in pattern[1..].iter().zip(fields) {
                    check_aggregate_pattern(
                        pattern,
                        &field.ty,
                        &mut arm_variables,
                        variables,
                        structs,
                    )?;
                }
            }
            _ => {
                return Err(format!(
                    "struct match pattern must be _ or ({struct_name} field-pattern ...)"
                ))
            }
        }
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                &arm_variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            &arm_variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err("struct match is not exhaustive; add '_' arm".into());
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
        Type::Reference { mutable, target } => Type::Reference {
            mutable: *mutable,
            target: Box::new(substitute_type(target, substitutions)),
        },
        Type::RawPointer { mutable, target } => Type::RawPointer {
            mutable: *mutable,
            target: Box::new(substitute_type(target, substitutions)),
        },
        Type::Cell(target) => Type::Cell(Box::new(substitute_type(target, substitutions))),
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
        Type::Reference { mutable, target } => Ok(Type::Reference {
            mutable: *mutable,
            target: Box::new(resolve_type_with_seen(target, aliases, seen)?),
        }),
        Type::RawPointer { mutable, target } => Ok(Type::RawPointer {
            mutable: *mutable,
            target: Box::new(resolve_type_with_seen(target, aliases, seen)?),
        }),
        Type::Cell(target) => Ok(Type::Cell(Box::new(resolve_type_with_seen(
            target, aliases, seen,
        )?))),
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
    if actual == expected || matches!(actual, Type::Never) {
        Ok(())
    } else {
        Err(format!(
            "{context} has type {actual:?}, expected {expected:?}"
        ))
    }
}

fn merge_types(left: &Type, right: &Type, context: &str) -> Result<Type, String> {
    if matches!(left, Type::Never) {
        return Ok(right.clone());
    }
    if matches!(right, Type::Never) {
        return Ok(left.clone());
    }
    require_same(left, right, context)?;
    Ok(left.clone())
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

fn is_reference_target(ty: &Type) -> bool {
    !matches!(ty, Type::Unit | Type::Never)
}

fn is_scalar_reference_target(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> bool {
    (is_numeric(ty) && !matches!(ty, Type::I128 | Type::U128))
        || matches!(ty, Type::Bool | Type::Char | Type::RawPointer { .. })
        || matches!(ty, Type::Named(name) if enums
            .get(name)
            .is_some_and(|variants| variants.iter().all(|variant| variant.fields.is_empty())))
}

fn is_cell_value_type(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> bool {
    if matches!(ty, Type::Cell(_)) {
        return false;
    }
    (is_numeric(ty) && !matches!(ty, Type::I128 | Type::U128))
        || matches!(ty, Type::Bool | Type::Char | Type::RawPointer { .. })
        || matches!(ty, Type::Named(name) if enums
            .get(name)
            .is_some_and(|variants| variants.iter().all(|variant| variant.fields.is_empty())))
}

fn contains_reference_type(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        Type::Reference { .. } => true,
        Type::Array(element, _) | Type::Cell(element) => {
            contains_reference_type(element, structs, enums, seen)
        }
        Type::Tuple(fields) => fields
            .iter()
            .any(|field| contains_reference_type(field, structs, enums, seen)),
        Type::Named(name) if seen.insert(name.clone()) => {
            let result = structs.get(name).is_some_and(|fields| {
                fields
                    .iter()
                    .any(|field| contains_reference_type(&field.ty, structs, enums, seen))
            }) || enums.get(name).is_some_and(|variants| {
                variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| contains_reference_type(field, structs, enums, seen))
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn type_contains_mutable_reference(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        Type::Reference { mutable: true, .. } => true,
        Type::Reference { mutable: false, .. } | Type::RawPointer { .. } => false,
        Type::Array(element, _) | Type::Cell(element) => {
            type_contains_mutable_reference(element, structs, enums, seen)
        }
        Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_mutable_reference(field, structs, enums, seen)),
        Type::Named(name) if seen.insert(name.clone()) => {
            let result = structs.get(name).is_some_and(|fields| {
                fields
                    .iter()
                    .any(|field| type_contains_mutable_reference(&field.ty, structs, enums, seen))
            }) || enums.get(name).is_some_and(|variants| {
                variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_mutable_reference(field, structs, enums, seen))
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn require_operator_type(qualifier: &str, ty: &Type, operator: &str) -> Result<(), String> {
    let expected = match ty {
        Type::Unit => "()",
        Type::Never => "!",
        Type::Bool => "bool",
        Type::Char => "char",
        Type::I8 => "i8",
        Type::I16 => "i16",
        Type::I32 => "i32",
        Type::I64 => "i64",
        Type::I128 => "i128",
        Type::Isize => "isize",
        Type::U8 => "u8",
        Type::U16 => "u16",
        Type::U32 => "u32",
        Type::U64 => "u64",
        Type::U128 => "u128",
        Type::Usize => "usize",
        Type::F32 => "f32",
        Type::F64 => "f64",
        Type::Reference { .. } => "reference",
        Type::RawPointer { .. } => "raw pointer",
        Type::Cell(_) => "interior mutable cell",
        Type::Generic(name) | Type::Named(name) => name,
        Type::Array(_, _) | Type::Tuple(_) => {
            return Err(format!(
                "operator '{operator}' has an unsupported operand type {ty:?}"
            ))
        }
    };
    if qualifier == expected {
        Ok(())
    } else {
        Err(format!(
            "operator '{operator}' is qualified for '{qualifier}', but its operand type is '{expected}'"
        ))
    }
}

fn typed_operator_parts(operator: &str) -> (Option<&str>, &str, Option<&str>) {
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

fn require_arithmetic_mode(
    operation: &str,
    mode: Option<&str>,
    operator: &str,
    ty: &Type,
) -> Result<(), String> {
    if !matches!(operation, "+" | "-" | "*" | "/" | "%") {
        if mode.is_some() {
            return Err(format!(
                "non-arithmetic operator '{operator}' cannot have a wrapping mode"
            ));
        }
        return Ok(());
    }
    if matches!(ty, Type::F32 | Type::F64) {
        if mode.is_some() {
            return Err(format!(
                "floating-point operator '{operator}' cannot have a wrapping mode"
            ));
        }
        return Ok(());
    }
    if !is_numeric(ty) {
        return Ok(());
    }
    let Some(mode) = mode else {
        return Err(format!(
            "arithmetic operator '{operator}' requires '.wrap' or '.saturate'"
        ));
    };
    if !matches!(mode, "wrap" | "saturate") {
        return Err(format!(
            "arithmetic operator '{operator}' has unknown mode '.{mode}'"
        ));
    }
    Ok(())
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
