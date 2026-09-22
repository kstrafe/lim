use std::collections::HashSet;

use crate::{Expr, Item, Program, Statement};

/// Enforce affine use of function-owned bindings. Values may be discarded, but
/// a binding may be consumed only once unless its value is explicitly cloned.
pub(crate) fn check_program(program: &Program) -> Result<(), String> {
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
            .map(|p| p.name.clone())
            .collect::<HashSet<_>>();
        let mut moved = HashSet::new();
        check_statements(&function.body, &mut bindings, &mut moved, &HashSet::new())?;
    }
    Ok(())
}

fn check_statements(
    statements: &[Statement],
    bindings: &mut HashSet<String>,
    moved: &mut HashSet<String>,
    globals: &HashSet<String>,
) -> Result<(), String> {
    for statement in statements {
        match statement {
            Statement::Let { name, value, .. } => {
                check_expr(value, bindings, moved, globals, false)?;
                bindings.insert(name.clone());
                moved.remove(name);
            }
            Statement::Destructure { pattern, value, .. } => {
                check_expr(value, bindings, moved, globals, false)?;
                collect_pattern_names(pattern, bindings);
            }
            Statement::LetElse {
                pattern,
                value,
                else_body,
                ..
            } => {
                check_expr(value, bindings, moved, globals, false)?;
                let mut else_bindings = bindings.clone();
                let mut else_moved = moved.clone();
                check_scoped_statements(else_body, &mut else_bindings, &mut else_moved, globals)?;
                collect_pattern_names(pattern, bindings);
            }
            Statement::Assign { name, value } => {
                check_expr(value, bindings, moved, globals, false)?;
                if bindings.contains(name) {
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
                check_scoped_statements(body, bindings, &mut body_moved, globals)?;
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
                check_scoped_statements(body, bindings, &mut body_moved, globals)?;
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
                check_statements(std::slice::from_ref(init), bindings, moved, globals)?;
                let before_condition = moved.clone();
                check_expr(condition, bindings, moved, globals, false)?;
                if *moved != before_condition {
                    return Err("a loop condition cannot consume an outer value; use #clone".into());
                }
                let before = moved.clone();
                let mut inner = before.clone();
                check_scoped_statements(body, bindings, &mut inner, globals)?;
                check_statements(std::slice::from_ref(step), bindings, &mut inner, globals)?;
                if inner != before {
                    return Err(
                        "a loop body cannot move an outer value; clone it before use".into(),
                    );
                }
            }
            Statement::Labeled { statement, .. } => {
                check_statements(std::slice::from_ref(statement), bindings, moved, globals)?
            }
            _ => {}
        }
    }
    Ok(())
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
            } else if head == "if" && items.len() == 4 {
                check_expr(&items[1], bindings, moved, globals, false)?;
                let mut left = moved.clone();
                let mut right = moved.clone();
                check_expr(&items[2], bindings, &mut left, globals, false)?;
                check_expr(&items[3], bindings, &mut right, globals, false)?;
                // A value moved on either path is considered unavailable after
                // the join; a value merely dropped on one path is still affine.
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
                if let Some(joined) = exits
                    .into_iter()
                    .reduce(|a, b| a.union(&b).cloned().collect())
                {
                    *moved = joined;
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
                *moved = then_state.union(&else_state).cloned().collect();
            } else if matches!(head, "&&" | "||") && items.len() == 3 {
                check_expr(&items[1], bindings, moved, globals, false)?;
                let mut taken = moved.clone();
                check_expr(&items[2], bindings, &mut taken, globals, false)?;
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
            } else if head == "addr-of"
                || head == "addr-of-mut"
                || head == "deref"
                || head == "ptr-read"
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
        Expr::Block(body) | Expr::Loop(body) => {
            check_scoped_statements(body, &mut bindings.clone(), moved, globals)?
        }
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
        Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "get") => {
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
        Expr::List(items) if items.len() == 3 => match items.first() {
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
            _ => None,
        },
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
) -> Result<(), String> {
    let outer = bindings.clone();
    check_statements(statements, bindings, moved, globals)?;
    bindings.retain(|name| outer.contains(name));
    moved.retain(|name| outer.contains(name));
    Ok(())
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
        Expr::Block(statements) => {
            check_statements(statements, &mut bindings.clone(), moved, globals)
        }
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
    fn values_are_affine_and_clone_is_explicit() {
        let duplicate = parse_program(
            "(#fn main () u64 (#let value u64 20) (#return (#u64.+.wrap value value)))",
        )
        .unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("use (#clone value)"));

        let cloned = parse_program(
            "(#fn main () u64 (#let value u64 20) (#return (#u64.+.wrap (#clone value) value)))",
        )
        .unwrap();
        assert!(check_types(&cloned).is_ok());
    }

    #[test]
    fn cloning_a_moved_value_is_rejected() {
        let program = parse_program(
            "(#fn consume ((value u64)) u64 (#return value)) (#fn main () u64 (#let value u64 1) (#let moved u64 (consume value)) (#return (#clone value)))",
        )
        .unwrap();
        assert!(check_types(&program)
            .unwrap_err()
            .contains("cannot clone moved linear value 'value'"));
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
        let invalid = parse_program(
            "(#fn main () u64 (#let-mut count u64 0) (#while (#u64.< count 1) (#set count 1)) (#return count))",
        )
        .unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("loop condition cannot consume"));

        let valid = parse_program(
            "(#fn main () u64 (#let-mut count u64 0) (#while (#u64.< (#clone count) 1) (#set count 1)) (#return count))",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok());
    }

    #[test]
    fn explicit_clone_codegen_handles_aggregates() {
        let program = parse_program(
            "(#struct Pair ((left u64) (right u64))) (#fn main () u64 (#let value Pair (Pair 20 22)) (#let duplicate Pair (#clone value)) (#return (#u64.+.wrap (#get duplicate left) (#get duplicate right))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(crate::generate_assembly(&program).is_ok());
    }

    #[test]
    fn named_clone_functions_define_deep_clone_behavior() {
        let program = parse_program(
            "(#struct Point ((x u64))) (#fn Point-clone ((source Point)) Point (#return source)) (#fn consume ((point Point)) u64 (#return (#get point x))) (#fn main () u64 (#let value Point (Point 4)) (#return (consume (#clone value))))",
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
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let point Point (Point 20 22)) (#return (#u64.+.wrap (#get point x) (#get point x))))",
        )
        .unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("linear projection 'point.x'"));

        let cloned = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let point Point (Point 20 22)) (#return (#u64.+.wrap (#clone (#get point x)) (#get point x))))",
        )
        .unwrap();
        assert!(check_types(&cloned).is_ok());
    }
}
