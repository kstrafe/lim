//! Immutable, compiler-bundled Lim sources. Reserved absolute paths give them
//! stable import identities without consulting the caller's filesystem.
use std::path::Path;

pub(crate) const ROOT: &str = "/<lim-std>/std.lim";

pub(crate) const DIRECTORY: &str = "/<lim-std>";

pub(crate) fn println_name() -> &'static str {
    static NAME: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    NAME.get_or_init(|| {
        crate::file_access::qualified_identity(Path::new("/<lim-std>/stdio.lim"), "std-println")
    })
}

pub(crate) fn source(path: &Path) -> Option<&'static str> {
    match path.to_str()? {
        ROOT => Some(include_str!("../library/std.lim")),
        "/<lim-std>/aio_owned.lim" => Some(include_str!("../library/aio_owned.lim")),
        "/<lim-std>/allocator.lim" => Some(include_str!("../library/allocator.lim")),
        "/<lim-std>/async_poll4.lim" => Some(include_str!("../library/async_poll4.lim")),
        "/<lim-std>/async_stdin_byte.lim" => Some(include_str!("../library/async_stdin_byte.lim")),
        "/<lim-std>/cell.lim" => Some(include_str!("../library/cell.lim")),
        "/<lim-std>/enum_project.lim" => Some(include_str!("../library/enum_project.lim")),
        "/<lim-std>/file.lim" => Some(include_str!("../library/file.lim")),
        "/<lim-std>/linux_x86_64.lim" => Some(include_str!("../library/linux_x86_64.lim")),
        "/<lim-std>/linux_x86_64_syscall_numbers.lim" => {
            Some(include_str!("../library/linux_x86_64_syscall_numbers.lim"))
        }
        "/<lim-std>/local_waker.lim" => Some(include_str!("../library/local_waker.lim")),
        "/<lim-std>/pin.lim" => Some(include_str!("../library/pin.lim")),
        "/<lim-std>/pin_box.lim" => Some(include_str!("../library/pin_box.lim")),
        "/<lim-std>/pin_rc.lim" => Some(include_str!("../library/pin_rc.lim")),
        "/<lim-std>/pin_slot.lim" => Some(include_str!("../library/pin_slot.lim")),
        "/<lim-std>/ready_queue.lim" => Some(include_str!("../library/ready_queue.lim")),
        "/<lim-std>/stdin.lim" => Some(include_str!("../library/stdin.lim")),
        "/<lim-std>/stdio.lim" => Some(include_str!("../library/stdio.lim")),
        "/<lim-std>/string.lim" => Some(include_str!("../library/string.lim")),
        "/<lim-std>/system_allocator.lim" => Some(include_str!("../library/system_allocator.lim")),
        "/<lim-std>/tasks.lim" => Some(include_str!("../library/tasks.lim")),
        "/<lim-std>/timer_reactor1.lim" => Some(include_str!("../library/timer_reactor1.lim")),
        "/<lim-std>/utf8_view.lim" => Some(include_str!("../library/utf8_view.lim")),
        "/<lim-std>/wake_ready4.lim" => Some(include_str!("../library/wake_ready4.lim")),
        "/<lim-std>/wake_tokens.lim" => Some(include_str!("../library/wake_tokens.lim")),
        _ => None,
    }
}
