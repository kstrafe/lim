//! Immutable, compiler-bundled Lim sources. Reserved absolute paths give them
//! stable import identities without consulting the caller's filesystem.
use std::path::Path;

pub(crate) const ROOT: &str = "/<lim-std>/std.lim";

pub(crate) fn source(path: &Path) -> Option<&'static str> {
    match path.to_str()? {
        ROOT => Some(include_str!("../library/std.lim")),
        "/<lim-std>/string.lim" => Some(include_str!("../library/string.lim")),
        "/<lim-std>/system_allocator.lim" => Some(include_str!("../library/system_allocator.lim")),
        "/<lim-std>/stdio.lim" => Some(include_str!("../library/stdio.lim")),
        "/<lim-std>/stdin.lim" => Some(include_str!("../library/stdin.lim")),
        "/<lim-std>/file.lim" => Some(include_str!("../library/file.lim")),
        _ => None,
    }
}
