//! Versioned, allocation-safe byte-buffer ABI for a dedicated browser worker.
#[cfg(target_arch = "wasm32")]
mod abi {
    use lim::wasm::{self, ReturnType};
    use std::cell::RefCell;

    #[derive(Default)]
    struct Buffers {
        input: Vec<u8>,
        output: Vec<u8>,
        return_type: u32,
    }
    thread_local! { static BUFFERS: RefCell<Buffers> = RefCell::new(Buffers::default()); }

    #[no_mangle]
    pub extern "C" fn lim_abi_version() -> u32 {
        1
    }

    /// The caller writes UTF-8 into this compiler-owned buffer, then compiles.
    /// A null pointer rejects oversized input. No caller pointers are dereferenced.
    #[no_mangle]
    pub extern "C" fn lim_input_resize(length: u32) -> u32 {
        if length as usize > wasm::MAX_SOURCE_BYTES {
            return 0;
        }
        BUFFERS.with(|buffers| {
            let mut buffers = buffers.borrow_mut();
            buffers.input.resize(length as usize, 0);
            buffers.input.as_mut_ptr() as u32
        })
    }

    /// 0: emitted module; 1: check succeeded; 2: UTF-8 diagnostic text.
    /// mode 0 compiles, mode 1 checks without requiring backend support.
    #[no_mangle]
    pub extern "C" fn lim_compile(mode: u32) -> u32 {
        BUFFERS.with(|buffers| {
            let mut buffers = buffers.borrow_mut();
            buffers.output.clear();
            buffers.return_type = 0;
            let source = match std::str::from_utf8(&buffers.input) {
                Ok(source) => source,
                Err(_) => {
                    buffers
                        .output
                        .extend_from_slice(b"error: input is not UTF-8");
                    return 2;
                }
            };
            let result = match mode {
                0 => wasm::compile(source).map(Some),
                1 => wasm::check(source).map(|_| None),
                _ => {
                    buffers
                        .output
                        .extend_from_slice(b"error: unsupported compiler ABI mode");
                    return 2;
                }
            };
            match result {
                Ok(Some(module)) => {
                    buffers.return_type = match module.return_type {
                        ReturnType::Unit => 0,
                        ReturnType::Bool => 1,
                        ReturnType::Unsigned64 => 2,
                        ReturnType::Signed64 => 3,
                    };
                    buffers.output = module.bytes;
                    0
                }
                Ok(None) => {
                    buffers
                        .output
                        .extend_from_slice(b"Type, ownership, borrow and contract checks passed.");
                    1
                }
                Err(error) => {
                    let message = lim::render_diagnostic(&error, source, "playground.lim");
                    buffers.output = message.into_bytes();
                    2
                }
            }
        })
    }
    #[no_mangle]
    pub extern "C" fn lim_output_ptr() -> u32 {
        BUFFERS.with(|b| b.borrow().output.as_ptr() as u32)
    }
    #[no_mangle]
    pub extern "C" fn lim_output_len() -> u32 {
        BUFFERS.with(|b| b.borrow().output.len() as u32)
    }
    #[no_mangle]
    pub extern "C" fn lim_return_type() -> u32 {
        BUFFERS.with(|b| b.borrow().return_type)
    }
}
