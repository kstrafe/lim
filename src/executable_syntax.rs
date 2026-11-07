//! Materialize distinct executable occurrences before assigning address IDs.
//! Source metadata and mathematical declarations retain their shared storage.
use std::collections::HashSet;

use crate::{Expr, Item, Program, Statement};

pub(crate) fn detach(program: &Program, selected: Option<&HashSet<String>>) -> Program {
    fn expression(value: &mut Expr) {
        match value {
            Expr::List(items) => {
                for item in items.iter_mut() {
                    expression(item);
                }
            }
            Expr::Block(body) | Expr::Loop(body) => statements(body),
            Expr::Labeled {
                expression: inner, ..
            }
            | Expr::Quote(inner)
            | Expr::QuasiQuote(inner)
            | Expr::Unquote(inner)
            | Expr::UnquoteSplicing(inner) => expression(inner),
            Expr::Function(_)
            | Expr::Symbol(_)
            | Expr::Integer(_)
            | Expr::UnsignedInteger(_)
            | Expr::Float(_)
            | Expr::Char(_)
            | Expr::String(_)
            | Expr::Generate => {}
        }
    }

    fn statements(body: &mut [Statement]) {
        for value in body {
            statement(value);
        }
    }

    fn statement(value: &mut Statement) {
        use Statement as S;
        match value {
            S::Let { value, .. }
            | S::Assign { value, .. }
            | S::FieldAssign { value, .. }
            | S::TupleAssign { value, .. }
            | S::EnumPayloadAssign { value, .. }
            | S::BreakValue(value)
            | S::Return(Some(value))
            | S::Expr(value) => expression(value),
            S::Destructure { pattern, value, .. } => {
                expression(pattern);
                expression(value);
            }
            S::LetElse {
                pattern,
                value,
                failure_pattern,
                else_body,
                ..
            } => {
                expression(pattern);
                expression(value);
                if let Some(pattern) = failure_pattern {
                    expression(pattern);
                }
                statements(else_body);
            }
            S::ArrayAssign { index, value, .. } => {
                expression(index);
                expression(value);
            }
            S::While { condition, body } => {
                expression(condition);
                statements(body);
            }
            S::Loop { body } => statements(body),
            S::For {
                init,
                condition,
                step,
                body,
            } => {
                statement(init);
                expression(condition);
                statement(step);
                statements(body);
            }
            S::Labeled {
                statement: inner, ..
            } => statement(inner),
            S::BreakToValue { value, .. } => expression(value),
            S::Break | S::BreakTo(_) | S::Continue | S::ContinueTo(_) | S::Return(None) => {}
        }
    }

    let mut detached = program.clone();
    for item in &mut detached.items {
        match item {
            Item::Function(function)
                if selected.is_none_or(|names| names.contains(&function.name)) =>
            {
                statements(&mut function.body);
            }
            Item::Let { value, .. } | Item::Static { value, .. } if selected.is_none() => {
                expression(value);
            }
            _ => {}
        }
    }
    detached
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    fn repeated_assertion() -> Program {
        let mut program =
            crate::parse_program("(#fn main () #u64 (#assert true) (#return 42u64))").unwrap();
        let Item::Function(function) = &mut program.items[0] else {
            unreachable!()
        };
        function.body.insert(1, function.body[0].clone());
        program
    }

    #[test]
    fn materialization_preserves_values_and_assigns_dense_occurrence_ids() {
        let program = repeated_assertion();
        assert!(crate::typed_ir::expression_ids_selected(&program, None).is_none());
        let detached = detach(&program, None);
        assert_eq!(program, detached);
        assert!(crate::typed_ir::expression_ids_selected(&program, None).is_none());
        let ids = crate::typed_ir::expression_ids_selected(&detached, None).unwrap();
        let mut dense = ids.values().map(|id| id.0).collect::<Vec<_>>();
        dense.sort_unstable();
        assert_eq!(dense, (0..ids.len()).collect::<Vec<_>>());
    }

    #[test]
    fn body_selection_does_not_claim_unselected_occurrences_are_materialized() {
        let mut program = repeated_assertion();
        let other = crate::parse_program("(#fn other () #u64 (#return 0u64))").unwrap();
        program.items.extend(other.items);
        let selected = HashSet::from(["other".to_owned()]);
        let detached = detach(&program, Some(&selected));
        assert_eq!(program, detached);
        assert!(crate::typed_ir::expression_ids_selected(&detached, Some(&selected)).is_some());
        assert!(crate::typed_ir::expression_ids_selected(&detached, None).is_none());
    }
}
