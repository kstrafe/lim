use std::collections::HashSet;

use crate::{Expr, Item, Program, Statement, Type};

#[derive(Default)]
struct LinearTypes {
    aliases: std::collections::HashMap<String, Type>,
    structs: std::collections::HashMap<String, Vec<Type>>,
    enums: std::collections::HashMap<String, std::collections::HashMap<String, Vec<Type>>>,
}

/// Enforce linear use of owned values. Non-Copy values must be consumed exactly
/// once; Copy values and references do not create an ownership obligation.
pub(crate) fn check_program(program: &Program) -> Result<(), String> {
    let mut types = LinearTypes::default();
    for item in &program.items {
        match item {
            Item::TypeAlias { name, target, .. } => {
                types.aliases.insert(name.clone(), target.clone());
            }
            Item::Struct { name, fields, .. } => {
                types.structs.insert(
                    name.clone(),
                    fields.iter().map(|field| field.ty.clone()).collect(),
                );
            }
            Item::Enum { name, variants, .. } => {
                types.enums.insert(
                    name.clone(),
                    variants
                        .iter()
                        .map(|variant| (variant.name.clone(), variant.fields.clone()))
                        .collect(),
                );
            }
            _ => {}
        }
    }
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if function.external {
            continue;
        }
        let mut bindings = function
            .parameters
            .iter()
            .filter(|parameter| is_linear(&parameter.ty, &types, &mut HashSet::new()))
            .map(|p| p.name.clone())
            .collect::<HashSet<_>>();
        let mut moved = HashSet::new();
        for (index, statement) in function.body.iter().enumerate() {
            check_statements(
                std::slice::from_ref(statement),
                &mut bindings,
                &mut moved,
                &HashSet::new(),
                &types,
            )
            .map_err(|error| {
                let key = (function.name.clone(), index);
                let precise = program
                    .statement_expressions
                    .get(&key)
                    .and_then(|expression| precise_linear_span(expression, &error))
                    .or_else(|| {
                        error.contains("must be consumed").then(|| {
                            function.body.iter().enumerate().find_map(|(index, _)| {
                                let expression = program
                                    .statement_expressions
                                    .get(&(function.name.clone(), index))?;
                                let Expr::List(items) = &expression.expr else {
                                    return None;
                                };
                                if !matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let" | "#let-mut"))
                                {
                                    return None;
                                }
                                match (items.get(1), expression.children.get(1)) {
                                    (Some(Expr::Symbol(binding)), Some(binding_span))
                                        if binding == error.split('\'').nth(1)? =>
                                    {
                                        Some(binding_span.span)
                                    }
                                    _ => None,
                                }
                            })
                        })
                        .flatten()
                    });
                precise
                    .or_else(|| {
                        program
                            .statement_expressions
                            .get(&key)
                            .map(crate::source_value_span)
                    })
                    .or_else(|| program.statement_spans.get(&key).copied())
                    .map_or(error.clone(), |span| {
                        format!(
                            "{error}; source span {}:{}:{}",
                            span.source_id, span.start, span.end
                        )
                    })
            })?;
        }
    }
    Ok(())
}

fn precise_linear_span(expression: &crate::SpannedExpr, error: &str) -> Option<crate::Span> {
    let name = error.split('\'').nth(1)?;
    fn source_place_key(expression: &crate::SpannedExpr) -> Option<String> {
        match &expression.expr {
            Expr::Symbol(name) => Some(name.clone()),
            Expr::List(items) if items.len() == 3 => {
                let head = match items.first()? {
                    Expr::Symbol(head) => head.strip_prefix('#').unwrap_or(head),
                    _ => return None,
                };
                let mut base = source_place_key(expression.children.get(1)?)?;
                match head {
                    "get" => match &items[2] {
                        Expr::Symbol(field) => base.push_str(&format!(".{field}")),
                        Expr::Integer(index) => base.push_str(&format!(".{index}")),
                        _ => base.push_str(".*"),
                    },
                    "index" => match literal_index(&items[2]) {
                        Some(index) => base.push_str(&format!("[{index}]")),
                        None => base.push_str("[*]"),
                    },
                    _ => return None,
                }
                Some(base)
            }
            Expr::List(items) if items.len() == 4 => {
                let head = match items.first()? {
                    Expr::Symbol(head) => head.strip_prefix('#').unwrap_or(head),
                    _ => return None,
                };
                if head != "get-payload" {
                    return None;
                }
                let mut base = source_place_key(expression.children.get(1)?)?;
                if let Expr::Symbol(variant) = &items[2] {
                    base.push_str(&format!(".{variant}"));
                } else {
                    base.push_str(".*");
                }
                match literal_index(&items[3]) {
                    Some(index) => base.push_str(&format!(".{index}")),
                    None => base.push_str(".*"),
                }
                Some(base)
            }
            _ => None,
        }
    }
    fn occurrences<'a>(
        expression: &'a crate::SpannedExpr,
        name: &str,
        spans: &mut Vec<crate::Span>,
    ) {
        if matches!(&expression.expr, Expr::Symbol(symbol) if symbol == name)
            || source_place_key(expression).as_deref() == Some(name)
        {
            spans.push(expression.span);
        }
        for child in &expression.children {
            occurrences(child, name, spans);
        }
    }
    let mut spans = Vec::new();
    occurrences(expression, name, &mut spans);
    if error.contains("was used more than once") {
        spans.into_iter().max_by_key(|span| span.start)
    } else {
        spans.into_iter().next()
    }
}

fn check_statements(
    statements: &[Statement],
    bindings: &mut HashSet<String>,
    moved: &mut HashSet<String>,
    globals: &HashSet<String>,
    types: &LinearTypes,
) -> Result<(), String> {
    for statement in statements {
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                check_expr(value, bindings, moved, globals, false)?;
                if is_linear(ty, types, &mut HashSet::new()) {
                    bindings.insert(name.clone());
                }
                moved.remove(name);
            }
            Statement::Destructure {
                pattern, ty, value, ..
            } => {
                check_expr(value, bindings, moved, globals, false)?;
                collect_typed_pattern_names(pattern, ty, types, bindings);
            }
            Statement::LetElse {
                pattern,
                ty,
                value,
                else_body,
                ..
            } => {
                check_expr(value, bindings, moved, globals, false)?;
                let mut else_bindings = bindings.clone();
                let mut else_moved = moved.clone();
                check_scoped_statements(
                    else_body,
                    &mut else_bindings,
                    &mut else_moved,
                    globals,
                    types,
                )?;
                collect_typed_pattern_names(pattern, ty, types, bindings);
            }
            Statement::Assign { name, value } => {
                check_expr(value, bindings, moved, globals, false)?;
                if bindings.contains(name) {
                    if !moved.contains(name) {
                        return Err(format!("assignment would destroy live linear value '{name}'; consume it explicitly first"));
                    }
                    moved.remove(name);
                }
            }
            Statement::ArrayAssign { name, index, value } => {
                check_expr(index, bindings, moved, globals, false)?;
                check_expr(value, bindings, moved, globals, false)?;
                check_expr(&Expr::Symbol(name.clone()), bindings, moved, globals, true)?;
                moved.retain(|key| !key.starts_with(&format!("{name}[")));
            }
            Statement::FieldAssign { name, field, value } => {
                check_expr(value, bindings, moved, globals, false)?;
                moved.remove(&format!("{name}.{field}"));
            }
            Statement::TupleAssign { name, index, value } => {
                check_expr(value, bindings, moved, globals, false)?;
                moved.remove(&format!("{name}.{index}"));
            }
            Statement::EnumPayloadAssign {
                name,
                variant,
                index,
                value,
            } => {
                check_expr(value, bindings, moved, globals, false)?;
                moved.remove(&format!("{name}.{variant}.{index}"));
            }
            Statement::Return(value) => {
                if let Some(value) = value {
                    check_expr(value, bindings, moved, globals, false)?;
                }
                if let Some(name) = bindings.iter().find(|name| !moved.contains(*name)) {
                    return Err(format!("linear value '{name}' must be consumed before returning; use it, pass it to a destruction function, or explicitly (#forget {name})"));
                }
            }
            Statement::Expr(expr) | Statement::BreakValue(expr) => {
                check_expr(expr, bindings, moved, globals, false)?
            }
            Statement::BreakToValue { value, .. } => {
                check_expr(value, bindings, moved, globals, false)?
            }
            Statement::While { condition, body } => {
                let before_condition = moved.clone();
                if let Expr::List(parts) = condition {
                    if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "match") {
                        if let Some(owner) = parts.get(1) {
                            check_expr(owner, bindings, moved, globals, true)?;
                        }
                    } else {
                        check_expr(condition, bindings, moved, globals, false)?;
                    }
                } else {
                    check_expr(condition, bindings, moved, globals, false)?;
                }
                if *moved != before_condition {
                    return Err("a loop condition cannot consume an outer value; use #clone".into());
                }
                let mut body_moved = moved.clone();
                check_scoped_statements(body, bindings, &mut body_moved, globals, types)?;
                let moved_by_body = body_moved
                    .difference(moved)
                    .cloned()
                    .collect::<HashSet<_>>();
                for name in &moved_by_body {
                    if !assigned_before_read(body, name) {
                        return Err(format!("loop body moves '{name}' before the next iteration can restore it; clone the value"));
                    }
                }
                moved.extend(body_moved);
            }
            Statement::Loop { body } => {
                let mut body_moved = moved.clone();
                check_scoped_statements(body, bindings, &mut body_moved, globals, types)?;
                if body_moved != *moved {
                    return Err(
                        "a loop body cannot move an outer value; clone it before use".into(),
                    );
                }
            }
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                check_statements(std::slice::from_ref(init), bindings, moved, globals, types)?;
                let before_condition = moved.clone();
                check_expr(condition, bindings, moved, globals, false)?;
                if *moved != before_condition {
                    return Err("a loop condition cannot consume an outer value; use #clone".into());
                }
                let before = moved.clone();
                let mut inner = before.clone();
                check_scoped_statements(body, bindings, &mut inner, globals, types)?;
                check_statements(
                    std::slice::from_ref(step),
                    bindings,
                    &mut inner,
                    globals,
                    types,
                )?;
                if inner != before {
                    return Err(
                        "a loop body cannot move an outer value; clone it before use".into(),
                    );
                }
            }
            Statement::Labeled { statement, .. } => check_statements(
                std::slice::from_ref(statement),
                bindings,
                moved,
                globals,
                types,
            )?,
            _ => {}
        }
    }
    Ok(())
}

fn is_linear(ty: &Type, types: &LinearTypes, seen: &mut HashSet<String>) -> bool {
    match ty {
        Type::Unit
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
        | Type::F64
        | Type::Reference { .. }
        | Type::RawPointer { .. }
        | Type::Slice(_) => false,
        Type::MutableSlice(_) => true,
        Type::Tuple(items) => items.iter().any(|item| is_linear(item, types, seen)),
        Type::Array(element, _) => is_linear(element, types, seen),
        Type::Named(name) => {
            if let Some(alias) = types.aliases.get(name) {
                if !seen.insert(name.clone()) {
                    return true;
                }
                let result = is_linear(alias, types, seen);
                seen.remove(name);
                result
            } else if let Some(fields) = types.structs.get(name) {
                if !seen.insert(name.clone()) {
                    return true;
                }
                let result = fields.iter().any(|field| is_linear(field, types, seen));
                seen.remove(name);
                result
            } else if let Some(variants) = types.enums.get(name) {
                if !seen.insert(name.clone()) {
                    return true;
                }
                let result = variants
                    .values()
                    .flatten()
                    .any(|field| is_linear(field, types, seen));
                seen.remove(name);
                result
            } else {
                true
            }
        }
        Type::Cell(_) | Type::Generic(_) | Type::Never => true,
    }
}

fn collect_typed_pattern_names(
    pattern: &Expr,
    ty: &Type,
    types: &LinearTypes,
    bindings: &mut HashSet<String>,
) {
    if let Type::Named(name) = ty {
        if let Some(target) = types.aliases.get(name) {
            collect_typed_pattern_names(pattern, target, types, bindings);
            return;
        }
    }
    match pattern {
        Expr::Symbol(name) if name != "_" => {
            if is_linear(ty, types, &mut HashSet::new()) {
                bindings.insert(name.clone());
            }
        }
        Expr::List(parts) if !parts.is_empty() => {
            let head = match &parts[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => "",
            };
            let child_types: Vec<Type> = match (head, ty) {
                ("tuple", Type::Tuple(items)) => items.clone(),
                ("array", Type::Array(element, count)) => vec![(**element).clone(); *count],
                (_, Type::Named(name)) => types
                    .structs
                    .get(name)
                    .cloned()
                    .or_else(|| {
                        types
                            .enums
                            .get(name)
                            .and_then(|variants| variants.get(head).cloned())
                    })
                    .unwrap_or_default(),
                _ => Vec::new(),
            };
            for (child, child_ty) in parts.iter().skip(1).zip(child_types.iter()) {
                collect_typed_pattern_names(child, child_ty, types, bindings);
            }
        }
        _ => {}
    }
}

fn collect_pattern_names(pattern: &Expr, bindings: &mut HashSet<String>) {
    match pattern {
        Expr::Symbol(name) if name != "_" => {
            bindings.insert(name.clone());
        }
        Expr::List(items) => {
            for item in items {
                collect_pattern_names(item, bindings);
            }
        }
        _ => {}
    }
}

fn check_expr(
    expr: &Expr,
    bindings: &HashSet<String>,
    moved: &mut HashSet<String>,
    globals: &HashSet<String>,
    place: bool,
) -> Result<(), String> {
    match expr {
        Expr::Symbol(name) if bindings.contains(name) && !place => {
            if has_move_conflict(moved, name) {
                return Err(format!("linear value '{name}' was used more than once; use (#clone {name}) to make an explicit copy"));
            }
            moved.insert(name.clone());
        }
        Expr::List(items) if !items.is_empty() => {
            let head = match &items[0] {
                Expr::Symbol(s) => s.as_str(),
                _ => "",
            };
            if head == "clone" {
                if items.len() != 2 {
                    return Err("clone requires exactly one value".into());
                }
                check_clone(&items[1], bindings, moved)?;
            } else if matches!(head, "forget" | "drop") && items.len() == 2 {
                if let Some(key) = place_key(&items[1]) {
                    let root = key.split(['.', '[']).next().unwrap_or(&key);
                    if bindings.contains(root) {
                        if moved.iter().any(|existing| {
                            existing == &key
                                || key.starts_with(&format!("{existing}."))
                                || key.starts_with(&format!("{existing}["))
                        }) {
                            return Err(format!("linear value '{key}' was already consumed"));
                        }
                        moved.retain(|existing| {
                            !(existing.starts_with(&format!("{key}."))
                                || existing.starts_with(&format!("{key}[")))
                        });
                        moved.insert(key);
                    } else {
                        check_expr(&items[1], bindings, moved, globals, false)?;
                    }
                } else {
                    check_expr(&items[1], bindings, moved, globals, false)?;
                }
            } else if head == "if" && items.len() == 4 {
                check_expr(&items[1], bindings, moved, globals, false)?;
                let mut left = moved.clone();
                let mut right = moved.clone();
                check_expr(&items[2], bindings, &mut left, globals, false)?;
                check_expr(&items[3], bindings, &mut right, globals, false)?;
                require_same_consumption(bindings, &left, &right)?;
                // Both branches have consumed exactly the same outer places,
                // so the union now also represents definite consumption.
                *moved = left.union(&right).cloned().collect();
            } else if head == "match" && items.len() >= 3 {
                check_expr(&items[1], bindings, moved, globals, false)?;
                let after_scrutinee = moved.clone();
                let mut exits = Vec::new();
                for arm in &items[2..] {
                    let Expr::List(parts) = arm else { continue };
                    if parts.len() < 2 {
                        continue;
                    }
                    let mut arm_bindings = bindings.clone();
                    collect_pattern_names(&parts[0], &mut arm_bindings);
                    let mut arm_moved = after_scrutinee.clone();
                    let guard = parts.get(1).and_then(|expr| match expr {
                        Expr::List(when) if matches!(when.first(), Some(Expr::Symbol(head)) if head == "when") => Some(when),
                        _ => None,
                    });
                    if let Some(when) = guard {
                        let before_guard = arm_moved.clone();
                        for part in when.iter().skip(1) {
                            check_expr(part, &arm_bindings, &mut arm_moved, globals, false)?;
                        }
                        // Pattern payloads are inspected by guards, then
                        // consumed by the selected arm body.
                        for name in &arm_bindings {
                            if bindings.contains(name) {
                                continue;
                            }
                            if before_guard.contains(name) {
                                arm_moved.insert(name.clone());
                            } else {
                                arm_moved.remove(name);
                            }
                        }
                        if let Some(body) = parts.get(2) {
                            check_expr(body, &arm_bindings, &mut arm_moved, globals, false)?;
                        }
                    } else {
                        for part in &parts[1..] {
                            check_expr(part, &arm_bindings, &mut arm_moved, globals, false)?;
                        }
                    }
                    arm_moved.retain(|name| bindings.contains(name));
                    exits.push(arm_moved);
                }
                if let Some(first) = exits.first() {
                    for exit in exits.iter().skip(1) {
                        require_same_consumption(bindings, first, exit)?;
                    }
                    *moved = exits
                        .into_iter()
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                }
            } else if head == "while-let" && items.len() >= 4 {
                check_expr(&items[2], bindings, moved, globals, true)?;
                let before = moved.clone();
                let mut body_state = before.clone();
                for body in &items[3..] {
                    check_expr(body, bindings, &mut body_state, globals, false)?;
                }
                if body_state != before {
                    return Err(
                        "a #while-let body must restore outer values before the next iteration"
                            .into(),
                    );
                }
            } else if head == "if-let" && (items.len() == 4 || items.len() == 5) {
                check_expr(&items[2], bindings, moved, globals, true)?;
                let mut branch_bindings = bindings.clone();
                collect_pattern_names(&items[1], &mut branch_bindings);
                let mut then_state = moved.clone();
                check_expr(&items[3], &branch_bindings, &mut then_state, globals, false)?;
                then_state.retain(|name| bindings.contains(name));
                let mut else_state = moved.clone();
                if let Some(otherwise) = items.get(4) {
                    check_expr(otherwise, bindings, &mut else_state, globals, false)?;
                }
                require_same_consumption(bindings, &then_state, &else_state)?;
                *moved = then_state.union(&else_state).cloned().collect();
            } else if matches!(head, "&&" | "||") && items.len() == 3 {
                check_expr(&items[1], bindings, moved, globals, false)?;
                let mut taken = moved.clone();
                check_expr(&items[2], bindings, &mut taken, globals, false)?;
                require_same_consumption(bindings, moved, &taken)?;
                *moved = moved.union(&taken).cloned().collect();
            } else if head == "unsafe" || head == "block" {
                for arg in items.iter().skip(1) {
                    check_expr(arg, bindings, moved, globals, false)?;
                }
            } else if head == "get" && items.len() == 3 {
                if !place {
                    if let Some(mut key) = place_key(&items[1]) {
                        match &items[2] {
                            Expr::Symbol(field) => key.push_str(&format!(".{field}")),
                            Expr::Integer(index) => key.push_str(&format!(".{index}")),
                            _ => key.push_str(".*"),
                        }
                        if has_move_conflict(moved, &key) {
                            return Err(format!("linear projection '{key}' was used more than once; clone it explicitly"));
                        }
                        moved.insert(key);
                    } else {
                        check_expr(&items[1], bindings, moved, globals, false)?;
                    }
                } else {
                    check_expr(&items[1], bindings, moved, globals, true)?;
                }
            } else if head == "get-payload" && items.len() == 4 {
                if !place {
                    if let Some(mut key) = place_key(&items[1]) {
                        if let Expr::Symbol(variant) = &items[2] {
                            key.push_str(&format!(".{variant}"));
                        } else {
                            key.push_str(".*");
                        }
                        match &items[3] {
                            index if literal_index(index).is_some() => {
                                key.push_str(&format!(".{}", literal_index(index).unwrap()))
                            }
                            _ => key.push_str(".*"),
                        }
                        if has_move_conflict(moved, &key) {
                            return Err(format!("linear projection '{key}' was used more than once; clone it explicitly"));
                        }
                        moved.insert(key);
                    } else {
                        check_expr(&items[1], bindings, moved, globals, false)?;
                    }
                } else {
                    check_expr(&items[1], bindings, moved, globals, true)?;
                }
            } else if head == "index" && items.len() == 3 {
                check_expr(&items[2], bindings, moved, globals, false)?;
                if !place {
                    if let Some(mut key) = place_key(&items[1]) {
                        match &items[2] {
                            index if literal_index(index).is_some() => {
                                key.push_str(&format!("[{}]", literal_index(index).unwrap()))
                            }
                            _ => key.push_str("[*]"),
                        }
                        if has_move_conflict(moved, &key) {
                            return Err(format!("linear projection '{key}' was used more than once; clone it explicitly"));
                        }
                        moved.insert(key);
                    } else {
                        check_expr(&items[1], bindings, moved, globals, false)?;
                    }
                } else {
                    check_expr(&items[1], bindings, moved, globals, true)?;
                }
            } else if head == "slice-mut-split" && items.len() == 3 {
                check_expr(&items[1], bindings, moved, globals, false)?;
                check_expr(&items[2], bindings, moved, globals, false)?;
            } else if head == "slice-mut-idx" && items.len() == 3 {
                check_expr(&items[1], bindings, moved, globals, true)?;
                check_expr(&items[2], bindings, moved, globals, false)?;
            } else if head == "slice-mut-len" && items.len() == 2 {
                check_expr(&items[1], bindings, moved, globals, true)?;
            } else if head == "cell-get" {
                for arg in items.iter().skip(1) {
                    check_expr(arg, bindings, moved, globals, true)?;
                }
            } else if head == "tuple" || head == "array" {
                for arg in items.iter().skip(2) {
                    check_expr(arg, bindings, moved, globals, false)?;
                }
            } else if head == "array-repeat" {
                if let Some(value) = items.get(2) {
                    check_expr(value, bindings, moved, globals, false)?;
                }
            } else if head == "borrow" || head == "borrow-mut" {
                if items.len() == 3 {
                    let owner = simple_place_name(&items[1]);
                    if let Some(owner) = owner {
                        check_expr(&items[1], bindings, moved, globals, true)?;
                        check_expr_with_place(&items[2], bindings, moved, globals, Some(owner))?;
                    } else {
                        check_expr(&items[1], bindings, moved, globals, false)?;
                        check_expr(&items[2], bindings, moved, globals, false)?;
                    }
                } else {
                    for arg in items.iter().skip(1) {
                        check_expr(arg, bindings, moved, globals, true)?;
                    }
                }
            } else if head == "ptr-offset" {
                if let Some(pointer) = items.get(1) {
                    check_expr(pointer, bindings, moved, globals, false)?;
                }
                if let Some(index) = items.get(2) {
                    check_expr(index, bindings, moved, globals, false)?;
                }
            } else if head == "addr-of"
                || head == "addr-of-mut"
                || head == "deref"
                || head == "ptr-read"
                || head == "ptr-is-null"
                || head == "ptr-borrow"
                || head == "ptr-borrow-mut"
                || head == "ptr-write"
            {
                for arg in items.iter().skip(1) {
                    check_expr(arg, bindings, moved, globals, true)?;
                }
            } else {
                for arg in items.iter().skip(1) {
                    check_expr(arg, bindings, moved, globals, false)?;
                }
            }
        }
        Expr::List(items) => {
            for item in items {
                check_expr(item, bindings, moved, globals, false)?;
            }
        }
        Expr::Block(body) | Expr::Loop(body) => check_scoped_statements(
            body,
            &mut bindings.clone(),
            moved,
            globals,
            &LinearTypes::default(),
        )?,
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => {
            check_expr(expression, bindings, moved, globals, place)?
        }
        _ => {}
    }
    let _ = globals;
    Ok(())
}

fn simple_place_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Symbol(name) => Some(name),
        Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "get" || head == "get-payload") => {
            parts.get(1).and_then(|base| simple_place_name(base))
        }
        _ => None,
    }
}

fn check_clone(
    expr: &Expr,
    bindings: &HashSet<String>,
    moved: &HashSet<String>,
) -> Result<(), String> {
    if let Some(key) = place_key(expr) {
        if bindings.contains(key.split(['.', '[']).next().unwrap_or(&key))
            && has_move_conflict(moved, &key)
        {
            return Err(format!("cannot clone moved linear value '{key}'"));
        }
    }
    Ok(())
}

fn place_key(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Symbol(name) => Some(name.clone()),
        Expr::List(items)
            if (items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(head)) if head == "get" || head == "index"))
                || (items.len() == 4
                    && matches!(items.first(), Some(Expr::Symbol(head)) if head == "get-payload")) =>
        {
            match items.first() {
                Some(Expr::Symbol(head)) if head == "get" => {
                    let mut base = place_key(&items[1])?;
                    match &items[2] {
                        Expr::Symbol(field) => base.push_str(&format!(".{field}")),
                        Expr::Integer(index) => base.push_str(&format!(".{index}")),
                        _ => base.push_str(".*"),
                    }
                    Some(base)
                }
                Some(Expr::Symbol(head)) if head == "index" => {
                    let mut base = place_key(&items[1])?;
                    match &items[2] {
                        index if literal_index(index).is_some() => {
                            base.push_str(&format!("[{}]", literal_index(index).unwrap()))
                        }
                        _ => base.push_str("[*]"),
                    }
                    Some(base)
                }
                Some(Expr::Symbol(head)) if head == "get-payload" => {
                    let mut base = place_key(&items[1])?;
                    if let Expr::Symbol(variant) = &items[2] {
                        base.push_str(&format!(".{variant}"));
                    } else {
                        base.push_str(".*");
                    }
                    match &items[3] {
                        index if literal_index(index).is_some() => {
                            base.push_str(&format!(".{}", literal_index(index).unwrap()))
                        }
                        _ => base.push_str(".*"),
                    }
                    Some(base)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn literal_index(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Integer(index) => Some(index.to_string()),
        Expr::UnsignedInteger(index) => Some(index.to_string()),
        Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "literal") => {
            match parts.get(2) {
                Some(Expr::Integer(index)) => Some(index.to_string()),
                Some(Expr::UnsignedInteger(index)) => Some(index.to_string()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn has_move_conflict(moved: &HashSet<String>, key: &str) -> bool {
    moved.iter().any(|existing| {
        existing == key
            || existing.starts_with(&format!("{key}."))
            || existing.starts_with(&format!("{key}["))
            || key.starts_with(&format!("{existing}."))
            || key.starts_with(&format!("{existing}["))
    })
}

fn check_scoped_statements(
    statements: &[Statement],
    bindings: &mut HashSet<String>,
    moved: &mut HashSet<String>,
    globals: &HashSet<String>,
    types: &LinearTypes,
) -> Result<(), String> {
    let outer = bindings.clone();
    check_statements(statements, bindings, moved, globals, types)?;
    if let Some(name) = bindings
        .iter()
        .find(|name| !outer.contains(*name) && !moved.contains(*name))
    {
        return Err(format!("linear value '{name}' must be consumed before leaving its scope; use it, pass it to a destruction function, or explicitly (#forget {name})"));
    }
    bindings.retain(|name| outer.contains(name));
    moved.retain(|name| outer.contains(place_root(name)));
    Ok(())
}

fn require_same_consumption(
    bindings: &HashSet<String>,
    left: &HashSet<String>,
    right: &HashSet<String>,
) -> Result<(), String> {
    for binding in bindings {
        let left_places = left
            .iter()
            .filter(|place| place_root(place) == binding)
            .collect::<HashSet<_>>();
        let right_places = right
            .iter()
            .filter(|place| place_root(place) == binding)
            .collect::<HashSet<_>>();
        if left_places != right_places {
            return Err(format!(
                "linear value '{binding}' must be consumed consistently on every control-flow path"
            ));
        }
    }
    Ok(())
}

fn place_root(place: &str) -> &str {
    place.split(['.', '[']).next().unwrap_or(place)
}

fn assigned_before_read(statements: &[Statement], name: &str) -> bool {
    for statement in statements {
        match statement {
            Statement::Assign {
                name: target,
                value,
            } if target == name => {
                return !expression_mentions(value, name);
            }
            Statement::Let { value, .. }
            | Statement::Destructure { value, .. }
            | Statement::LetElse { value, .. }
            | Statement::Expr(value)
            | Statement::Return(Some(value)) => {
                if expression_mentions(value, name) {
                    return false;
                }
            }
            _ => {}
        }
    }
    false
}

fn expression_mentions(expression: &Expr, name: &str) -> bool {
    match expression {
        Expr::Symbol(found) => found == name,
        Expr::List(items) => items.iter().any(|item| expression_mentions(item, name)),
        Expr::Block(statements) | Expr::Loop(statements) => {
            statements.iter().any(|statement| match statement {
                Statement::Assign {
                    name: target,
                    value,
                } => target == name || expression_mentions(value, name),
                Statement::Expr(value) | Statement::Return(Some(value)) => {
                    expression_mentions(value, name)
                }
                _ => false,
            })
        }
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => expression_mentions(expression, name),
        _ => false,
    }
}

fn check_expr_with_place(
    expr: &Expr,
    bindings: &HashSet<String>,
    moved: &mut HashSet<String>,
    globals: &HashSet<String>,
    borrowed_place: Option<&str>,
) -> Result<(), String> {
    if let (Expr::Symbol(name), Some(place)) = (expr, borrowed_place) {
        if name == place {
            return Ok(());
        }
    }
    match expr {
        Expr::List(items) => {
            for (index, item) in items.iter().enumerate() {
                if index == 0 {
                    continue;
                }
                check_expr_with_place(item, bindings, moved, globals, borrowed_place)?;
            }
            Ok(())
        }
        Expr::Block(statements) => check_statements(
            statements,
            &mut bindings.clone(),
            moved,
            globals,
            &LinearTypes::default(),
        ),
        Expr::Symbol(name) if bindings.contains(name) => {
            if !moved.insert(name.clone()) {
                Err(format!("linear value '{name}' was used more than once; use (#clone {name}) to make an explicit copy"))
            } else {
                Ok(())
            }
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use crate::{check_types, parse_program};

    #[test]
    fn values_are_linear_and_clone_is_explicit() {
        let duplicate = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn consume ((value Resource)) () (#forget value) (#return ())) (#fn main () u64 (#let value Resource (#struct-literal Resource ((value (#cell 20u64))))) (#call consume (#fn-args (value value))) (#call consume (#fn-args (value value))) (#return 0u64))",
        ).unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("linear value 'value' was used more than once"));

        let cloned = parse_program(
            "(#struct Resource ((value u64))) (#fn main () u64 (#let value Resource (#struct-literal Resource ((value 20u64)))) (#forget (#clone value)) (#forget value) (#return 0u64))",
        )
        .unwrap();
        assert!(check_types(&cloned).is_ok());
    }

    #[test]
    fn cloning_a_moved_value_is_rejected() {
        let program = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn consume ((value Resource)) Resource (#return value)) (#fn inspect ((value Resource)) u64 (#forget value) (#return 0u64)) (#fn main () u64 (#let value Resource (#struct-literal Resource ((value (#cell 1u64))))) (#let moved Resource (#call consume (#fn-args (value value)))) (#forget moved) (#return (#call inspect (#fn-args (value (#clone value))))))",
        )
        .unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(
            error.contains("cannot clone moved linear value 'value'"),
            "{error}"
        );
    }

    #[test]
    fn mutable_references_cannot_be_cloned() {
        let program = parse_program(
            "(#fn main () (#ref-mut u64) (#let-mut value u64 1) (#let reference (#ref-mut u64) (#borrow-mut value)) (#return (#clone reference)))",
        )
        .unwrap();
        assert!(check_types(&program)
            .unwrap_err()
            .contains("a mutable reference cannot be cloned"));
    }

    #[test]
    fn loop_conditions_must_clone_values_that_are_reused() {
        let valid = parse_program(
            "(#fn main () u64 (#let-mut count u64 0) (#while (#u64.< (#clone count) 1) (#set count 1)) (#return count))",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok());
    }

    #[test]
    fn explicit_clone_codegen_handles_aggregates() {
        let program = parse_program(
            "(#struct Pair ((left u64) (right u64))) (#fn main () u64 (#let value Pair (#struct-literal Pair ((left 20) (right 22)))) (#let duplicate Pair (#clone value)) (#let result u64 (#u64.+.wrap (#get duplicate left) (#get duplicate right))) (#forget duplicate) (#forget value) (#return result))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(crate::generate_assembly(&program).is_ok());
    }

    #[test]
    fn named_clone_functions_define_deep_clone_behavior() {
        let program = parse_program(
            "(#struct Point ((x u64))) (#fn Point-clone ((source Point)) Point (#return source)) (#fn consume ((point Point)) u64 (#let result u64 (#get point x)) (#forget point) (#return result)) (#fn main () u64 (#let value Point (#struct-literal Point ((x 4)))) (#let result u64 (#call consume (#fn-args (point (#clone value))))) (#forget value) (#return result))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(crate::generate_assembly(&program)
            .unwrap()
            .contains("call Point_x2d_clone"));
    }

    #[test]
    fn field_values_are_moved_independently_and_can_be_cloned() {
        let duplicate = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn use ((resource Resource)) () (#forget resource) (#return ())) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value (#cell 20u64))))) (#call use (#fn-args (resource resource))) (#call use (#fn-args (resource resource))) (#return 0u64))",
        )
        .unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("linear value 'resource' was used more than once"));

        let cloned = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#struct Point ((x Resource) (y u64))) (#fn main () u64 (#let point Point (#struct-literal Point ((x (#struct-literal Resource ((value (#cell 20u64))))) (y 22u64)))) (#forget (#clone (#get point x))) (#forget point) (#return 0u64))",
        )
        .unwrap();
        assert!(check_types(&cloned).is_ok());
    }

    #[test]
    fn repeated_linear_field_move_highlights_the_repeated_projection() {
        let source = "(#struct Resource ((value (#cell u64))))\n(#struct Pair ((item Resource) (other u64)))\n(#fn main () u64\n  (#let pair Pair (#struct-literal Pair ((item (#struct-literal Resource ((value (#cell 1u64))))) (other 0u64))))\n  (#let first Resource (#get pair item))\n  (#let second Resource (#get pair item))\n  (#forget first)\n  (#forget second)\n  (#forget pair)\n  (#return 0u64))";
        let program = parse_program(source).unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(error.contains("linear projection 'pair.item' was used more than once"));
        let (start, end) = crate::span_after(&error, "source span ").unwrap();
        assert_eq!(&source[start..end], "(#get pair item)");
    }

    #[test]
    fn repeated_linear_array_move_highlights_the_repeated_index() {
        let source = "(#fn main () u64\n  (#let values (#array (#cell u64) 2) (#array (#array (#cell u64) 2) (#cell 1u64) (#cell 2u64)))\n  (#let first (#cell u64) (#index values 0))\n  (#let second (#cell u64) (#index values 0))\n  (#forget first)\n  (#forget second)\n  (#forget values)\n  (#return 0u64))";
        let program = parse_program(source).unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(error.contains("linear projection 'values[0]' was used more than once"));
        let (start, end) = crate::span_after(&error, "source span ").unwrap();
        assert_eq!(&source[start..end], "(#index values 0)");
    }

    #[test]
    fn linear_values_must_be_consumed_before_return() {
        let leaked = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value (#cell 1u64))))) (#return 0u64))",
        ).unwrap();
        assert!(check_types(&leaked)
            .unwrap_err()
            .contains("must be consumed before returning"));

        let forgotten = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value (#cell 1u64))))) (#forget resource) (#return 0u64))",
        ).unwrap();
        assert!(check_types(&forgotten).is_ok());

        let copied =
            parse_program("(#fn main () u64 (#let number u64 1u64) (#return 0u64))").unwrap();
        assert!(check_types(&copied).is_ok());
    }

    #[test]
    fn linearity_diagnostics_point_to_the_exact_binding() {
        let source = "(#struct Resource ((value (#cell u64))))\n(#fn main () u64\n  (#let resource Resource (#struct-literal Resource ((value (#cell 1u64)))))\n  (#return 0u64))";
        let program = parse_program(source).unwrap();
        let error = check_types(&program).unwrap_err();
        let (start, end) = crate::span_after(&error, "source span ").unwrap();
        assert_eq!(&source[start..end], "resource");
    }

    #[test]
    fn linearity_is_checked_at_scope_exits_and_control_flow_joins() {
        let escaping = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn main () u64 (#return (#block (#let resource Resource (#struct-literal Resource ((value (#cell 1u64))))) 0u64)))",
        ).unwrap();
        assert!(check_types(&escaping)
            .unwrap_err()
            .contains("before leaving its scope"));

        let branch_leak = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn consume ((value Resource)) u64 (#forget value) (#return 1u64)) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value (#cell 1u64))))) (#return (#if true (#call consume (#fn-args (value resource))) 0u64)))",
        ).unwrap();
        assert!(check_types(&branch_leak)
            .unwrap_err()
            .contains("consumed consistently on every control-flow path"));

        let both_branches_consume = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#fn consume ((value Resource)) u64 (#forget value) (#return 1u64)) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value (#cell 1u64))))) (#return (#if true (#call consume (#fn-args (value resource))) (#call consume (#fn-args (value resource))))))",
        ).unwrap();
        assert!(check_types(&both_branches_consume).is_ok());

        let different_fields = parse_program(
            "(#struct Resource ((value (#cell u64)))) (#struct Pair ((left Resource) (right Resource))) (#fn main () u64 (#let pair Pair (#struct-literal Pair ((left (#struct-literal Resource ((value (#cell 1u64))))) (right (#struct-literal Resource ((value (#cell 2u64)))))))) (#return (#if true (#block (#forget (#get pair left)) 1u64) (#block (#forget (#get pair right)) 2u64))))",
        ).unwrap();
        let error = check_types(&different_fields).unwrap_err();
        assert!(
            error.contains("consumed consistently on every control-flow path"),
            "{error}"
        );
    }

    #[test]
    fn thread_tasks_cannot_be_forgotten_instead_of_joined() {
        let program = parse_program(
            "(#fn worker ((value u64)) u64 (#return value)) (@thread-spawn Task worker) (#fn main () u64 (#let result Task-spawn-result (Task-spawn 1u64)) (#forget result) (#return 0u64))",
        ).unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(
            error.contains("cannot be dropped or forgotten; match and join them"),
            "{error}"
        );
    }
}
