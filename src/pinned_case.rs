//! Explicit pin-borrowing match patterns, after surface arm normalization.

use crate::Expr;

pub(crate) fn parts(pattern: &Expr) -> Option<(bool, &Expr)> {
    let Expr::List(items) = pattern else {
        return None;
    };
    if items.len() != 2 {
        return None;
    }
    let Expr::Symbol(head) = &items[0] else {
        return None;
    };
    match head.as_str() {
        "#case-pin" => Some((false, &items[1])),
        "#case-pin-mut" => Some((true, &items[1])),
        _ => None,
    }
}
