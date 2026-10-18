//! Immutable, compiler-bundled Lim sources. Reserved absolute paths give them
//! stable import identities without consulting the caller's filesystem.
use std::path::Path;

pub(crate) const ROOT: &str = "/<lim-std>/std.lim";

/// Concrete names provided by the single #std instance. Generated APIs share
/// their explicitly named root, so e.g. StringView::new stays global too.
pub(crate) fn shared_names() -> &'static std::collections::HashSet<String> {
    static NAMES: std::sync::OnceLock<std::collections::HashSet<String>> =
        std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = std::collections::HashSet::new();
        for text in [
            include_str!("../library/allocator.lim"),
            include_str!("../library/string.lim"),
            include_str!("../library/utf8_view.lim"),
            include_str!("../library/system_allocator.lim"),
            include_str!("../library/stdio.lim"),
            include_str!("../library/stdin.lim"),
            include_str!("../library/file.lim"),
            include_str!("../library/enum_project.lim"),
        ] {
            for form in crate::parse(text).expect("valid standard library syntax") {
                names.extend(crate::generator_provenance::declared_names(&form.expr).into_iter().map(str::to_owned));
                if let crate::Expr::List(items) = &form.expr {
                    if matches!(items.first(), Some(crate::Expr::Generate)) {
                        if let Some(crate::Expr::List(arguments)) = items.get(2) {
                            for argument in arguments {
                                if let crate::Expr::List(pair) = argument {
                                    if matches!(pair.first(), Some(crate::Expr::Symbol(key)) if key == "name") {
                                        if let Some(crate::Expr::Symbol(name)) = pair.get(1) {
                                            names.insert(name.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        names
    })
}

/// Reserved generator definitions are immutable shipped declarations, even
/// when imported from a checkout rather than the embedded standard library.
/// Comparing syntax prevents a caller-controlled filename granting privileges.
pub(crate) fn is_generator_declaration(expression: &crate::Expr) -> bool {
    static DECLARATIONS: std::sync::OnceLock<Vec<crate::Expr>> = std::sync::OnceLock::new();
    DECLARATIONS
        .get_or_init(|| {
            [
                include_str!("../library/allocator.lim"),
                include_str!("../library/cell.lim"),
                include_str!("../library/local_waker.lim"),
                include_str!("../library/ready_queue.lim"),
                include_str!("../library/pin.lim"),
                include_str!("../library/pin_box.lim"),
                include_str!("../library/enum_project.lim"),
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
        "/<lim-std>/allocator.lim" => Some(include_str!("../library/allocator.lim")),
        "/<lim-std>/string.lim" => Some(include_str!("../library/string.lim")),
        "/<lim-std>/utf8_view.lim" => Some(include_str!("../library/utf8_view.lim")),
        "/<lim-std>/system_allocator.lim" => Some(include_str!("../library/system_allocator.lim")),
        "/<lim-std>/stdio.lim" => Some(include_str!("../library/stdio.lim")),
        "/<lim-std>/stdin.lim" => Some(include_str!("../library/stdin.lim")),
        "/<lim-std>/file.lim" => Some(include_str!("../library/file.lim")),
        "/<lim-std>/enum_project.lim" => Some(include_str!("../library/enum_project.lim")),
        _ => None,
    }
}
