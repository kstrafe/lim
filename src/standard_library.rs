//! Immutable, compiler-bundled Lim sources. Reserved absolute paths give them
//! stable import identities without consulting the caller's filesystem.
use std::path::Path;

pub(crate) const ROOT: &str = "/<lim-std>/std.lim";

/// Reserved generator definitions are immutable shipped declarations, even
/// when imported from a checkout rather than the embedded standard library.
/// Comparing syntax prevents a caller-controlled filename granting privileges.
pub(crate) fn is_generator_declaration(expression: &crate::Expr) -> bool {
    static DECLARATIONS: std::sync::OnceLock<Vec<crate::Expr>> = std::sync::OnceLock::new();
    DECLARATIONS
        .get_or_init(|| {
            [
                include_str!("../library/cell.lim"),
                include_str!("../library/collections.lim"),
                include_str!("../library/local_waker.lim"),
                include_str!("../library/ready_queue.lim"),
                include_str!("../library/pin.lim"),
                include_str!("../library/pin_box.lim"),
                include_str!("../library/pin_rc.lim"),
                include_str!("../library/pin_slot.lim"),
                include_str!("../library/tasks.lim"),
                include_str!("../library/utf8_view.lim"),
            ]
            .into_iter()
            .flat_map(|source| crate::parse(source).expect("valid standard library syntax"))
            .filter_map(|form| {
                matches!(&form.expr, crate::Expr::List(items)
                if matches!(items.first(), Some(crate::Expr::Symbol(head)) if head == "#gn"))
                .then_some(form.expr)
            })
            .collect()
        })
        .contains(expression)
}

pub(crate) fn source(path: &Path) -> Option<&'static str> {
    match path.to_str()? {
        ROOT => Some(include_str!("../library/std.lim")),
        "/<lim-std>/string.lim" => Some(include_str!("../library/string.lim")),
        "/<lim-std>/utf8_view.lim" => Some(include_str!("../library/utf8_view.lim")),
        "/<lim-std>/system_allocator.lim" => Some(include_str!("../library/system_allocator.lim")),
        "/<lim-std>/stdio.lim" => Some(include_str!("../library/stdio.lim")),
        "/<lim-std>/stdin.lim" => Some(include_str!("../library/stdin.lim")),
        "/<lim-std>/file.lim" => Some(include_str!("../library/file.lim")),
        _ => None,
    }
}
