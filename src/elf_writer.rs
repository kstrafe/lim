//! Minimal Linux x86-64 ELF image construction for the native backend.
//!
//! Writes static and dynamic ELF images with separate executable and writable
//! segments. Instruction encoding and symbol resolution live elsewhere.

#![allow(dead_code)]

const BASE_ADDRESS: u64 = 0x400000;
const DATA_ADDRESS: u64 = BASE_ADDRESS + 0x1000_0000;
const CODE_OFFSET: usize = 0x1000;
const ELF_HEADER_SIZE: usize = 64;
const PROGRAM_HEADER_SIZE: usize = 56;

pub(crate) fn code_address(offset: usize) -> Result<u64, String> {
    BASE_ADDRESS
        .checked_add(u64::try_from(CODE_OFFSET).map_err(|_| "ELF code offset overflow")?)
        .and_then(|base| {
            u64::try_from(offset)
                .ok()
                .and_then(|offset| base.checked_add(offset))
        })
        .ok_or("ELF code address overflow".into())
}

pub(crate) fn data_address(offset: usize) -> Result<u64, String> {
    DATA_ADDRESS
        .checked_add(u64::try_from(offset).map_err(|_| "ELF data offset overflow")?)
        .ok_or("ELF data address overflow".into())
}

fn put_u16(bytes: &mut [u8], offset: usize, value: u16) {
    bytes[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
}

fn put_u32(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn put_u64(bytes: &mut [u8], offset: usize, value: u64) {
    bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

/// Return an ET_EXEC image with read/execute code and a non-executable stack.
pub(crate) fn executable(text: &[u8], entry_offset: usize) -> Result<Vec<u8>, String> {
    if text.is_empty() || entry_offset >= text.len() {
        return Err("ELF entry must point into nonempty code".into());
    }
    let file_size = CODE_OFFSET
        .checked_add(text.len())
        .ok_or("ELF image size overflow")?;
    let file_size_u64 = u64::try_from(file_size).map_err(|_| "ELF image size exceeds u64")?;
    let entry = BASE_ADDRESS
        .checked_add(u64::try_from(CODE_OFFSET + entry_offset).map_err(|_| "ELF entry overflow")?)
        .ok_or("ELF entry overflow")?;
    let mut image = vec![0; file_size];
    image[0..4].copy_from_slice(b"\x7fELF");
    image[4] = 2; // ELFCLASS64
    image[5] = 1; // ELFDATA2LSB
    image[6] = 1; // EV_CURRENT
    image[7] = 0; // ELFOSABI_SYSV
    put_u16(&mut image, 16, 2); // ET_EXEC
    put_u16(&mut image, 18, 62); // EM_X86_64
    put_u32(&mut image, 20, 1); // EV_CURRENT
    put_u64(&mut image, 24, entry);
    put_u64(&mut image, 32, ELF_HEADER_SIZE as u64);
    put_u16(&mut image, 52, ELF_HEADER_SIZE as u16);
    put_u16(&mut image, 54, PROGRAM_HEADER_SIZE as u16);
    put_u16(&mut image, 56, 2); // e_phnum

    let program = ELF_HEADER_SIZE;
    put_u32(&mut image, program, 1); // PT_LOAD
    put_u32(&mut image, program + 4, 5); // PF_R | PF_X
    put_u64(&mut image, program + 8, 0); // p_offset
    put_u64(&mut image, program + 16, BASE_ADDRESS);
    put_u64(&mut image, program + 24, BASE_ADDRESS);
    put_u64(&mut image, program + 32, file_size_u64);
    put_u64(&mut image, program + 40, file_size_u64);
    put_u64(&mut image, program + 48, CODE_OFFSET as u64);
    let stack = program + PROGRAM_HEADER_SIZE;
    put_u32(&mut image, stack, 0x6474_e551); // PT_GNU_STACK
    put_u32(&mut image, stack + 4, 6); // PF_R | PF_W, no execute
    put_u64(&mut image, stack + 48, 16);
    image[CODE_OFFSET..].copy_from_slice(text);
    Ok(image)
}

/// Static executable with a separate writable PT_LOAD for supplied object
/// sections. The data virtual address is fixed so object relocations can be
/// resolved before file padding and ELF headers are laid out.
pub(crate) fn executable_with_data(
    text: &[u8],
    entry_offset: usize,
    data: &[u8],
) -> Result<Vec<u8>, String> {
    if data.is_empty() {
        return executable(text, entry_offset);
    }
    let mut image = executable(text, entry_offset)?;
    let code_end = image.len();
    if code_address(text.len())? >= DATA_ADDRESS {
        return Err("native code overlaps the data segment".into());
    }
    let data_offset = align_up(code_end, 4096)?;
    let file_end = data_offset
        .checked_add(data.len())
        .ok_or("ELF data image overflow")?;
    image.resize(file_end, 0);
    image[data_offset..file_end].copy_from_slice(data);
    put_u16(&mut image, 56, 3);
    let program = ELF_HEADER_SIZE + PROGRAM_HEADER_SIZE;
    put_u32(&mut image, program, 1); // PT_LOAD
    put_u32(&mut image, program + 4, 6); // PF_R | PF_W
    put_u64(
        &mut image,
        program + 8,
        u64::try_from(data_offset).map_err(|_| "ELF data offset overflow")?,
    );
    put_u64(&mut image, program + 16, DATA_ADDRESS);
    put_u64(&mut image, program + 24, DATA_ADDRESS);
    put_u64(
        &mut image,
        program + 32,
        u64::try_from(data.len()).map_err(|_| "ELF data size overflow")?,
    );
    put_u64(
        &mut image,
        program + 40,
        u64::try_from(data.len()).map_err(|_| "ELF data size overflow")?,
    );
    put_u64(&mut image, program + 48, 4096);
    let stack = program + PROGRAM_HEADER_SIZE;
    put_u32(&mut image, stack, 0x6474_e551);
    put_u32(&mut image, stack + 4, 6);
    put_u64(&mut image, stack + 48, 16);
    Ok(image)
}

fn align_up(value: usize, alignment: usize) -> Result<usize, String> {
    value
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
        .ok_or("ELF alignment overflow".into())
}

fn append_string(strings: &mut Vec<u8>, value: &str) -> Result<u32, String> {
    if value.is_empty() || value.as_bytes().contains(&0) {
        return Err("ELF dynamic string is empty or contains NUL".into());
    }
    let offset = u32::try_from(strings.len()).map_err(|_| "ELF string table exceeds 4 GiB")?;
    strings.extend_from_slice(value.as_bytes());
    strings.push(0);
    Ok(offset)
}

fn append_dynamic(data: &mut Vec<u8>, tag: u64, value: u64) {
    data.extend_from_slice(&tag.to_le_bytes());
    data.extend_from_slice(&value.to_le_bytes());
}

/// Build an ET_EXEC image with a dynamic interpreter and eager GOT entries.
/// Undefined calls target one compiler-owned jmp stub per imported symbol;
/// the loader fills each GOT slot with an R_X86_64_GLOB_DAT relocation.
pub(crate) fn dynamic_executable(
    linked: crate::native_linker::Linked,
    resolved: &crate::native_linker::ResolvedLibraries,
    interpreter: &str,
) -> Result<Vec<u8>, String> {
    use std::collections::BTreeMap;
    let needed = &resolved.paths;
    if needed.is_empty() {
        return Err("dynamic ELF needs at least one shared library".into());
    }
    if !interpreter.starts_with('/') {
        return Err("dynamic interpreter path must be absolute".into());
    }
    let mut code = linked.code;
    let mut data = linked.data;
    let mut copy_offsets = BTreeMap::new();
    for (symbol, size) in &resolved.copy_sizes {
        if *size == 0 {
            return Err(format!("zero-sized copy symbol '{symbol}'"));
        }
        let start = align_up(data.len(), 8)?;
        data.resize(
            start
                .checked_add(*size)
                .ok_or("copy symbol size overflow")?,
            0,
        );
        copy_offsets.insert(symbol.clone(), start);
    }
    if linked.entry >= code.len() {
        return Err("dynamic ELF entry lies outside code".into());
    }
    let mut import_names = std::collections::BTreeSet::new();
    for reference in &linked.foreign {
        if reference.symbol.is_empty() {
            return Err("unnamed foreign symbol".into());
        }
        import_names.insert(reference.symbol.clone());
    }
    for reference in &linked.foreign_got {
        if reference.symbol.is_empty() {
            return Err("unnamed foreign GOT symbol".into());
        }
        import_names.insert(reference.symbol.clone());
    }
    let imports = import_names
        .into_iter()
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect::<BTreeMap<_, _>>();
    if imports
        .keys()
        .any(|symbol| copy_offsets.contains_key(symbol))
    {
        return Err("symbol cannot be both a foreign call/GOT and a copy relocation".into());
    }
    for reference in &linked.foreign_copy {
        let offset = *copy_offsets
            .get(&reference.symbol)
            .ok_or("missing copy relocation symbol")?;
        let displacement = (data_address(offset)? as i128) + (reference.addend as i128)
            - (code_address(reference.offset)? as i128);
        let displacement =
            i32::try_from(displacement).map_err(|_| "COPY data displacement exceeds rel32")?;
        let after = reference
            .offset
            .checked_add(4)
            .ok_or("COPY reference offset overflow")?;
        code.get_mut(reference.offset..after)
            .ok_or("COPY reference extends beyond code")?
            .copy_from_slice(&displacement.to_le_bytes());
    }
    // Assign the stubs in symbol order so identical inputs produce identical ELF bytes.
    let mut stubs = BTreeMap::new();
    for symbol in imports.keys() {
        let start = code.len();
        code.extend_from_slice(&[0xff, 0x25, 0, 0, 0, 0]);
        stubs.insert(symbol.clone(), start);
    }
    for reference in &linked.foreign {
        let stub = *stubs
            .get(&reference.symbol)
            .ok_or("missing foreign call stub")?;
        let after = reference
            .offset
            .checked_add(4)
            .ok_or("foreign relocation offset overflow")?;
        let displacement = (stub as i128) + (reference.addend as i128) - (after as i128);
        let value =
            i32::try_from(displacement).map_err(|_| "foreign call displacement exceeds rel32")?;
        code.get_mut(reference.offset..after)
            .ok_or("foreign relocation extends beyond code")?
            .copy_from_slice(&value.to_le_bytes());
    }
    let interpreter_offset = CODE_OFFSET
        .checked_add(code.len())
        .ok_or("ELF interpreter offset overflow")?;
    let mut interp = Vec::new();
    append_string(&mut interp, interpreter)?;
    code.extend_from_slice(&interp);
    code.resize(align_up(code.len(), 8)?, 0);
    let string_offset = CODE_OFFSET
        .checked_add(code.len())
        .ok_or("ELF string offset overflow")?;
    let mut strings = vec![0];
    let mut search_paths = Vec::new();
    let needed_offsets = needed
        .iter()
        .map(|path| {
            let path = std::path::Path::new(path);
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("shared library has no UTF-8 name")?;
            let directory = path
                .parent()
                .and_then(|directory| directory.to_str())
                .ok_or("shared library has no UTF-8 directory")?;
            if !path.is_absolute() {
                return Err("shared library path must be absolute".into());
            }
            if !search_paths.iter().any(|item| *item == directory) {
                search_paths.push(directory);
            }
            append_string(&mut strings, name)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let runpath_offset = append_string(&mut strings, &search_paths.join(":"))?;
    let symbol_offsets = imports
        .keys()
        .map(|name| append_string(&mut strings, name))
        .collect::<Result<Vec<_>, _>>()?;
    let copy_symbol_offsets = copy_offsets
        .keys()
        .map(|name| append_string(&mut strings, name))
        .collect::<Result<Vec<_>, _>>()?;
    code.extend_from_slice(&strings);
    code.resize(align_up(code.len(), 8)?, 0);
    let symbol_offset = CODE_OFFSET
        .checked_add(code.len())
        .ok_or("ELF symbol table offset overflow")?;
    code.extend_from_slice(&[0; 24]); // STN_UNDEF
    for offset in symbol_offsets {
        code.extend_from_slice(&offset.to_le_bytes());
        code.extend_from_slice(&[0x12, 0, 0, 0]); // STB_GLOBAL, STT_FUNC, SHN_UNDEF
        code.extend_from_slice(&[0; 16]);
    }
    for ((name, offset), string_offset) in copy_offsets.iter().zip(copy_symbol_offsets) {
        let size = *resolved
            .copy_sizes
            .get(name)
            .ok_or("missing copy symbol size")?;
        code.extend_from_slice(&string_offset.to_le_bytes());
        code.extend_from_slice(&[0x11, 0, 1, 0]); // STB_GLOBAL, STT_OBJECT, defined section
        code.extend_from_slice(&data_address(*offset)?.to_le_bytes());
        code.extend_from_slice(
            &u64::try_from(size)
                .map_err(|_| "copy symbol size overflow")?
                .to_le_bytes(),
        );
    }
    code.resize(align_up(code.len(), 8)?, 0);
    let hash_offset = CODE_OFFSET
        .checked_add(code.len())
        .ok_or("ELF hash offset overflow")?;
    let chains = imports
        .len()
        .checked_add(copy_offsets.len())
        .ok_or("ELF symbol count overflow")?
        .checked_add(1)
        .ok_or("ELF symbol count overflow")?;
    code.extend_from_slice(&1u32.to_le_bytes()); // one bucket
    code.extend_from_slice(
        &u32::try_from(chains)
            .map_err(|_| "ELF symbol count exceeds u32")?
            .to_le_bytes(),
    );
    code.extend_from_slice(&(if chains == 1 { 0u32 } else { 1u32 }).to_le_bytes());
    for index in 0..chains {
        let next = if index == 0 || index + 1 == chains {
            0
        } else {
            index + 1
        };
        code.extend_from_slice(
            &u32::try_from(next)
                .map_err(|_| "ELF hash chain exceeds u32")?
                .to_le_bytes(),
        );
    }
    code.resize(align_up(code.len(), 8)?, 0);
    let relocation_offset = CODE_OFFSET
        .checked_add(code.len())
        .ok_or("ELF relocation offset overflow")?;
    let relocation_size = imports
        .len()
        .checked_add(copy_offsets.len())
        .ok_or("ELF relocation count overflow")?
        .checked_mul(24)
        .ok_or("ELF relocation table overflow")?;
    code.resize(
        code.len()
            .checked_add(relocation_size)
            .ok_or("ELF code size overflow")?,
        0,
    );
    let code_end = CODE_OFFSET
        .checked_add(code.len())
        .ok_or("ELF code size overflow")?;
    if BASE_ADDRESS
        .checked_add(u64::try_from(code_end).map_err(|_| "ELF code size overflow")?)
        .ok_or("ELF code address overflow")?
        >= DATA_ADDRESS
    {
        return Err("native code overlaps the data segment".into());
    }
    let data_offset = align_up(code_end, 4096)?;
    let got_size = imports
        .len()
        .checked_mul(8)
        .ok_or("ELF GOT size overflow")?;
    for reference in &linked.foreign_got {
        let index = *imports
            .get(&reference.symbol)
            .ok_or("missing foreign GOT symbol")?;
        let slot = data
            .len()
            .checked_add(index.checked_mul(8).ok_or("GOT index overflow")?)
            .ok_or("GOT slot overflow")?;
        let displacement = (data_address(slot)? as i128) + (reference.addend as i128)
            - (code_address(reference.offset)? as i128);
        let displacement =
            i32::try_from(displacement).map_err(|_| "foreign GOT displacement exceeds rel32")?;
        let after = reference
            .offset
            .checked_add(4)
            .ok_or("foreign GOT offset overflow")?;
        code.get_mut(reference.offset..after)
            .ok_or("foreign GOT relocation extends beyond code")?
            .copy_from_slice(&displacement.to_le_bytes());
    }
    for (name, index) in &imports {
        let stub = *stubs.get(name).ok_or("missing foreign stub")?;
        let from = code_address(stub.checked_add(6).ok_or("ELF stub overflow")?)?;
        let to = data_address(
            data.len()
                .checked_add(index.checked_mul(8).ok_or("ELF GOT index overflow")?)
                .ok_or("ELF GOT address overflow")?,
        )?;
        let displacement = (to as i128) - (from as i128);
        let displacement =
            i32::try_from(displacement).map_err(|_| "GOT is out of RIP-relative range")?;
        code[stub + 2..stub + 6].copy_from_slice(&displacement.to_le_bytes());
        let rela = relocation_offset - CODE_OFFSET + index * 24;
        code[rela..rela + 8].copy_from_slice(&to.to_le_bytes());
        let info =
            (u64::try_from(index + 1).map_err(|_| "ELF relocation symbol overflow")? << 32) | 6;
        code[rela + 8..rela + 16].copy_from_slice(&info.to_le_bytes());
    }
    for (index, (_, offset)) in copy_offsets.iter().enumerate() {
        let rela = relocation_offset - CODE_OFFSET + (imports.len() + index) * 24;
        code[rela..rela + 8].copy_from_slice(&data_address(*offset)?.to_le_bytes());
        let symbol_index = imports
            .len()
            .checked_add(index + 1)
            .ok_or("copy symbol index overflow")?;
        let info =
            (u64::try_from(symbol_index).map_err(|_| "copy symbol index overflow")? << 32) | 5;
        code[rela + 8..rela + 16].copy_from_slice(&info.to_le_bytes());
    }
    let got_file_offset = data.len();
    data.resize(
        data.len()
            .checked_add(got_size)
            .ok_or("ELF data size overflow")?,
        0,
    );
    let dynamic_offset = data_offset
        .checked_add(data.len())
        .ok_or("ELF dynamic offset overflow")?;
    for offset in needed_offsets {
        append_dynamic(&mut data, 1, u64::from(offset));
    }
    append_dynamic(&mut data, 29, u64::from(runpath_offset)); // DT_RUNPATH
    let virtual_address = |offset: usize| -> Result<u64, String> {
        BASE_ADDRESS
            .checked_add(u64::try_from(offset).map_err(|_| "ELF virtual address overflow")?)
            .ok_or("ELF virtual address overflow".into())
    };
    append_dynamic(&mut data, 4, virtual_address(hash_offset)?);
    append_dynamic(&mut data, 5, virtual_address(string_offset)?);
    append_dynamic(&mut data, 6, virtual_address(symbol_offset)?);
    append_dynamic(
        &mut data,
        10,
        u64::try_from(strings.len()).map_err(|_| "ELF string size overflow")?,
    );
    append_dynamic(&mut data, 11, 24);
    append_dynamic(&mut data, 7, virtual_address(relocation_offset)?);
    append_dynamic(
        &mut data,
        8,
        u64::try_from(relocation_size).map_err(|_| "ELF relocation size overflow")?,
    );
    append_dynamic(&mut data, 9, 24);
    append_dynamic(&mut data, 0, 0);
    let file_size = data_offset
        .checked_add(data.len())
        .ok_or("ELF image size overflow")?;
    let mut image = vec![0; file_size];
    image[0..4].copy_from_slice(b"\x7fELF");
    image[4..8].copy_from_slice(&[2, 1, 1, 0]);
    put_u16(&mut image, 16, 2);
    put_u16(&mut image, 18, 62);
    put_u32(&mut image, 20, 1);
    put_u64(&mut image, 24, code_address(linked.entry)?);
    put_u64(&mut image, 32, ELF_HEADER_SIZE as u64);
    put_u16(&mut image, 52, ELF_HEADER_SIZE as u16);
    put_u16(&mut image, 54, PROGRAM_HEADER_SIZE as u16);
    put_u16(&mut image, 56, 5);
    let program = ELF_HEADER_SIZE;
    put_u32(&mut image, program, 1); // RX PT_LOAD
    put_u32(&mut image, program + 4, 5);
    put_u64(&mut image, program + 16, BASE_ADDRESS);
    put_u64(&mut image, program + 24, BASE_ADDRESS);
    put_u64(
        &mut image,
        program + 32,
        u64::try_from(code_end).map_err(|_| "ELF code size overflow")?,
    );
    put_u64(
        &mut image,
        program + 40,
        u64::try_from(code_end).map_err(|_| "ELF code size overflow")?,
    );
    put_u64(&mut image, program + 48, 4096);
    let load_data = program + PROGRAM_HEADER_SIZE;
    put_u32(&mut image, load_data, 1); // RW PT_LOAD
    put_u32(&mut image, load_data + 4, 6);
    put_u64(
        &mut image,
        load_data + 8,
        u64::try_from(data_offset).map_err(|_| "ELF data offset overflow")?,
    );
    put_u64(&mut image, load_data + 16, DATA_ADDRESS);
    put_u64(&mut image, load_data + 24, DATA_ADDRESS);
    put_u64(
        &mut image,
        load_data + 32,
        u64::try_from(data.len()).map_err(|_| "ELF data size overflow")?,
    );
    put_u64(
        &mut image,
        load_data + 40,
        u64::try_from(data.len()).map_err(|_| "ELF data size overflow")?,
    );
    put_u64(&mut image, load_data + 48, 4096);
    let interp_header = load_data + PROGRAM_HEADER_SIZE;
    put_u32(&mut image, interp_header, 3); // PT_INTERP
    put_u32(&mut image, interp_header + 4, 4);
    put_u64(
        &mut image,
        interp_header + 8,
        u64::try_from(interpreter_offset).map_err(|_| "ELF interpreter offset overflow")?,
    );
    put_u64(
        &mut image,
        interp_header + 16,
        virtual_address(interpreter_offset)?,
    );
    put_u64(
        &mut image,
        interp_header + 24,
        virtual_address(interpreter_offset)?,
    );
    put_u64(
        &mut image,
        interp_header + 32,
        u64::try_from(interp.len()).map_err(|_| "ELF interpreter size overflow")?,
    );
    put_u64(
        &mut image,
        interp_header + 40,
        u64::try_from(interp.len()).map_err(|_| "ELF interpreter size overflow")?,
    );
    put_u64(&mut image, interp_header + 48, 1);
    let dynamic_header = interp_header + PROGRAM_HEADER_SIZE;
    put_u32(&mut image, dynamic_header, 2); // PT_DYNAMIC
    put_u32(&mut image, dynamic_header + 4, 6);
    put_u64(
        &mut image,
        dynamic_header + 8,
        u64::try_from(dynamic_offset).map_err(|_| "ELF dynamic offset overflow")?,
    );
    put_u64(
        &mut image,
        dynamic_header + 16,
        data_address(got_file_offset + got_size)?,
    );
    put_u64(
        &mut image,
        dynamic_header + 24,
        data_address(got_file_offset + got_size)?,
    );
    put_u64(
        &mut image,
        dynamic_header + 32,
        u64::try_from(data.len() - got_file_offset - got_size)
            .map_err(|_| "ELF dynamic size overflow")?,
    );
    put_u64(
        &mut image,
        dynamic_header + 40,
        u64::try_from(data.len() - got_file_offset - got_size)
            .map_err(|_| "ELF dynamic size overflow")?,
    );
    put_u64(&mut image, dynamic_header + 48, 8);
    let stack = dynamic_header + PROGRAM_HEADER_SIZE;
    put_u32(&mut image, stack, 0x6474_e551);
    put_u32(&mut image, stack + 4, 6);
    put_u64(&mut image, stack + 48, 16);
    image[CODE_OFFSET..code_end].copy_from_slice(&code);
    image[data_offset..file_size].copy_from_slice(&data);
    Ok(image)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction_encoder::{EncodedInstructions, Instruction, Register, Width};

    #[test]
    fn encodes_and_runs_a_standalone_elf_without_build_tools() {
        let mut code = EncodedInstructions::default();
        code.append(&Instruction::MovImmediate {
            width: Width::Dword,
            destination: Register::Rax,
            value: 60,
        })
        .unwrap();
        code.append(&Instruction::MovImmediate {
            width: Width::Dword,
            destination: Register::Rdi,
            value: 42,
        })
        .unwrap();
        code.append(&Instruction::Syscall).unwrap();
        let image = executable(&code.bytes, 0).unwrap();
        assert_eq!(&image[0..4], b"\x7fELF");
        assert_eq!(
            u64::from_le_bytes(image[24..32].try_into().unwrap()),
            0x401000
        );
        assert_eq!(u32::from_le_bytes(image[68..72].try_into().unwrap()), 5);
        assert_eq!(u32::from_le_bytes(image[124..128].try_into().unwrap()), 6);

        if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
            use std::os::unix::fs::PermissionsExt;
            let staging = crate::output::StagingDirectory::beside(
                &std::env::temp_dir().join("lim-internal-elf-test"),
            )
            .unwrap();
            let output = staging.0.join("program");
            std::fs::write(&output, &image).unwrap();
            std::fs::set_permissions(&output, std::fs::Permissions::from_mode(0o700)).unwrap();
            assert_eq!(
                std::process::Command::new(output).status().unwrap().code(),
                Some(42)
            );
        }
    }

    #[test]
    fn rejects_empty_and_out_of_bounds_entry() {
        assert!(executable(&[], 0).is_err());
        assert!(executable(&[0xc3], 1).is_err());
    }
}
