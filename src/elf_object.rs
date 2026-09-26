//! Read the ELF64 symbol table from relocatable x86-64 objects.
//!
//! The native linker uses this data instead of running `nm`. Bounds are
//! checked because `--link-object` accepts externally produced files.

fn u16_at(bytes: &[u8], offset: usize) -> Result<u16, String> {
    let data: [u8; 2] = bytes
        .get(offset..offset.checked_add(2).ok_or("ELF offset overflow")?)
        .ok_or("truncated ELF u16")?
        .try_into()
        .map_err(|_| "invalid ELF u16")?;
    Ok(u16::from_le_bytes(data))
}

fn u32_at(bytes: &[u8], offset: usize) -> Result<u32, String> {
    let data: [u8; 4] = bytes
        .get(offset..offset.checked_add(4).ok_or("ELF offset overflow")?)
        .ok_or("truncated ELF u32")?
        .try_into()
        .map_err(|_| "invalid ELF u32")?;
    Ok(u32::from_le_bytes(data))
}

fn u64_at(bytes: &[u8], offset: usize) -> Result<u64, String> {
    let data: [u8; 8] = bytes
        .get(offset..offset.checked_add(8).ok_or("ELF offset overflow")?)
        .ok_or("truncated ELF u64")?
        .try_into()
        .map_err(|_| "invalid ELF u64")?;
    Ok(u64::from_le_bytes(data))
}

fn usize_at(bytes: &[u8], offset: usize) -> Result<usize, String> {
    usize::try_from(u64_at(bytes, offset)?).map_err(|_| "ELF size exceeds host usize".into())
}

fn section_header(
    bytes: &[u8],
    table: usize,
    stride: usize,
    index: usize,
) -> Result<usize, String> {
    let offset = index
        .checked_mul(stride)
        .and_then(|step| table.checked_add(step))
        .ok_or("ELF section header offset overflow")?;
    bytes
        .get(
            offset
                ..offset
                    .checked_add(64)
                    .ok_or("ELF section header overflow")?,
        )
        .ok_or("truncated ELF section header")?;
    Ok(offset)
}

fn section_data<'a>(bytes: &'a [u8], header: usize) -> Result<&'a [u8], String> {
    let offset = usize_at(bytes, header + 24)?;
    let size = usize_at(bytes, header + 32)?;
    bytes
        .get(
            offset
                ..offset
                    .checked_add(size)
                    .ok_or("ELF section size overflow")?,
        )
        .ok_or("ELF section extends beyond file".into())
}

#[derive(Debug)]
pub(crate) struct Section {
    pub index: usize,
    pub name: String,
    pub data: Vec<u8>,
    pub size: usize,
    pub align: usize,
    pub writable: bool,
}

#[derive(Debug)]
pub(crate) struct Symbol {
    pub name: String,
    pub section: usize,
    pub value: usize,
    pub global: bool,
    pub weak: bool,
}

#[derive(Debug)]
pub(crate) struct ObjectRelocation {
    pub section: usize,
    pub offset: usize,
    pub symbol: usize,
    pub kind: u32,
    pub addend: i64,
}

#[derive(Debug)]
pub(crate) struct Object {
    pub sections: Vec<Section>,
    pub symbols: Vec<Symbol>,
    pub relocations: Vec<ObjectRelocation>,
}

fn string_at(strings: &[u8], offset: usize) -> Result<String, String> {
    let bytes = strings
        .get(offset..)
        .ok_or("ELF string offset out of range")?;
    let end = bytes
        .iter()
        .position(|byte| *byte == 0)
        .ok_or("unterminated ELF string")?;
    std::str::from_utf8(&bytes[..end])
        .map(str::to_owned)
        .map_err(|_| "non-UTF8 ELF string".into())
}

/// Parse the ELF64 ET_REL sections needed by the internal linker. Every
/// externally controlled offset is checked before it reaches the linker.
pub(crate) fn relocatable(bytes: &[u8]) -> Result<Object, String> {
    if bytes.get(0..7) != Some(b"\x7fELF\x02\x01\x01".as_slice())
        || u16_at(bytes, 16)? != 1
        || u16_at(bytes, 18)? != 62
    {
        return Err("expected little-endian x86-64 ELF relocatable object".into());
    }
    let table = usize_at(bytes, 40)?;
    let stride = usize::from(u16_at(bytes, 58)?);
    let count = usize::from(u16_at(bytes, 60)?);
    let names_index = usize::from(u16_at(bytes, 62)?);
    if stride < 64 || count == 0 || names_index >= count {
        return Err("invalid ELF section table".into());
    }
    let names_header = section_header(bytes, table, stride, names_index)?;
    let names = section_data(bytes, names_header)?;
    let mut sections = Vec::new();
    let mut symbols = Vec::new();
    let mut relocations = Vec::new();
    let mut symbol_table_index = None;
    for index in 0..count {
        let header = section_header(bytes, table, stride, index)?;
        let kind = u32_at(bytes, header + 4)?;
        let flags = u64_at(bytes, header + 8)?;
        if flags & 2 != 0 {
            if kind != 1 && kind != 7 && kind != 8 {
                return Err(format!("unsupported allocatable ELF section type {kind}"));
            }
            let size = usize_at(bytes, header + 32)?;
            let align = usize_at(bytes, header + 48)?.max(1);
            if !align.is_power_of_two() || align > 1 << 20 {
                return Err("unsupported ELF section alignment".into());
            }
            let name = string_at(
                names,
                usize::try_from(u32_at(bytes, header)?).map_err(|_| "ELF section name overflow")?,
            )?;
            let data = if kind == 8 {
                Vec::new()
            } else {
                section_data(bytes, header)?.to_vec()
            };
            if kind != 8 && data.len() != size {
                return Err("ELF section size mismatch".into());
            }
            sections.push(Section {
                index,
                name,
                data,
                size,
                align,
                writable: flags & 1 != 0,
            });
        }
        if kind == 2 {
            if symbol_table_index.replace(index).is_some() {
                return Err("multiple ELF symbol tables are unsupported".into());
            }
            let linked = usize::try_from(u32_at(bytes, header + 40)?)
                .map_err(|_| "ELF string table index overflow")?;
            if linked >= count {
                return Err("ELF string table index out of range".into());
            }
            let strings_header = section_header(bytes, table, stride, linked)?;
            if u32_at(bytes, strings_header + 4)? != 3 {
                return Err("ELF symbol names are not a string table".into());
            }
            let strings = section_data(bytes, strings_header)?;
            let data = section_data(bytes, header)?;
            let entry_size = usize_at(bytes, header + 56)?;
            if entry_size < 24 || data.len() % entry_size != 0 {
                return Err("invalid ELF symbol entry size".into());
            }
            for entry in data.chunks_exact(entry_size) {
                let binding = entry[4] >> 4;
                symbols.push(Symbol {
                    name: string_at(
                        strings,
                        usize::try_from(u32_at(entry, 0)?)
                            .map_err(|_| "ELF symbol name overflow")?,
                    )?,
                    section: usize::from(u16_at(entry, 6)?),
                    value: usize::try_from(u64_at(entry, 8)?)
                        .map_err(|_| "ELF symbol value overflow")?,
                    global: binding == 1 || binding == 2,
                    weak: binding == 2,
                });
            }
        }
    }
    for index in 0..count {
        let header = section_header(bytes, table, stride, index)?;
        let kind = u32_at(bytes, header + 4)?;
        if kind == 9 {
            return Err("ELF REL relocations without explicit addends are unsupported".into());
        }
        if kind != 4 {
            continue;
        }
        if Some(
            usize::try_from(u32_at(bytes, header + 40)?)
                .map_err(|_| "ELF relocation symbol table overflow")?,
        ) != symbol_table_index
        {
            return Err("ELF relocation references an unsupported symbol table".into());
        }
        let target = usize::try_from(u32_at(bytes, header + 44)?)
            .map_err(|_| "ELF relocation target overflow")?;
        if target >= count {
            return Err("ELF relocation target out of range".into());
        }
        let data = section_data(bytes, header)?;
        let entry_size = usize_at(bytes, header + 56)?;
        if entry_size < 24 || data.len() % entry_size != 0 {
            return Err("invalid ELF relocation entry size".into());
        }
        for entry in data.chunks_exact(entry_size) {
            let info = u64_at(entry, 8)?;
            let symbol =
                usize::try_from(info >> 32).map_err(|_| "ELF relocation symbol overflow")?;
            if symbol >= symbols.len() {
                return Err("ELF relocation symbol out of range".into());
            }
            relocations.push(ObjectRelocation {
                section: target,
                offset: usize::try_from(u64_at(entry, 0)?)
                    .map_err(|_| "ELF relocation offset overflow")?,
                symbol,
                kind: info as u32,
                addend: u64_at(entry, 16)? as i64,
            });
        }
    }
    Ok(Object {
        sections,
        symbols,
        relocations,
    })
}

/// Read defined global/weak names from an ELF shared library's dynamic table.
/// Versioned entries retain their base name in `.dynsym`; the dynamic loader
/// selects the default version at relocation time.
pub(crate) fn shared_exports(bytes: &[u8]) -> Result<std::collections::BTreeSet<String>, String> {
    if bytes.get(0..7) != Some(b"\x7fELF\x02\x01\x01".as_slice())
        || u16_at(bytes, 16)? != 3
        || u16_at(bytes, 18)? != 62
    {
        return Err("expected little-endian x86-64 ELF shared library".into());
    }
    let table = usize_at(bytes, 40)?;
    let stride = usize::from(u16_at(bytes, 58)?);
    let count = usize::from(u16_at(bytes, 60)?);
    if stride < 64 || count == 0 {
        return Err("invalid shared-library section table".into());
    }
    let mut exports = std::collections::BTreeSet::new();
    let mut found = false;
    for index in 0..count {
        let header = section_header(bytes, table, stride, index)?;
        if u32_at(bytes, header + 4)? != 11 {
            continue;
        } // SHT_DYNSYM
        found = true;
        let linked = usize::try_from(u32_at(bytes, header + 40)?)
            .map_err(|_| "ELF dynamic string table index overflow")?;
        if linked >= count {
            return Err("ELF dynamic string table index out of range".into());
        }
        let strings_header = section_header(bytes, table, stride, linked)?;
        if u32_at(bytes, strings_header + 4)? != 3 {
            return Err("ELF dynamic symbols lack a string table".into());
        }
        let strings = section_data(bytes, strings_header)?;
        let data = section_data(bytes, header)?;
        let entry_size = usize_at(bytes, header + 56)?;
        if entry_size < 24 || data.len() % entry_size != 0 {
            return Err("invalid ELF dynamic symbol size".into());
        }
        for entry in data.chunks_exact(entry_size) {
            if !matches!(entry[4] >> 4, 1 | 2) || u16_at(entry, 6)? == 0 {
                continue;
            }
            let name = string_at(
                strings,
                usize::try_from(u32_at(entry, 0)?).map_err(|_| "dynamic symbol offset overflow")?,
            )?;
            if !name.is_empty() {
                exports.insert(name);
            }
        }
    }
    if !found {
        return Err("shared library has no dynamic symbol table".into());
    }
    Ok(exports)
}

/// Sizes of defined global object symbols suitable for executable COPY
/// relocations. TLS and zero-sized symbols are deliberately excluded.
pub(crate) fn shared_data_exports(
    bytes: &[u8],
) -> Result<std::collections::BTreeMap<String, usize>, String> {
    if bytes.get(0..7) != Some(b"\x7fELF\x02\x01\x01".as_slice())
        || u16_at(bytes, 16)? != 3
        || u16_at(bytes, 18)? != 62
    {
        return Err("expected little-endian x86-64 ELF shared library".into());
    }
    let table = usize_at(bytes, 40)?;
    let stride = usize::from(u16_at(bytes, 58)?);
    let count = usize::from(u16_at(bytes, 60)?);
    if stride < 64 || count == 0 {
        return Err("invalid shared-library section table".into());
    }
    let mut exports = std::collections::BTreeMap::new();
    for index in 0..count {
        let header = section_header(bytes, table, stride, index)?;
        if u32_at(bytes, header + 4)? != 11 {
            continue;
        }
        let linked = usize::try_from(u32_at(bytes, header + 40)?)
            .map_err(|_| "ELF dynamic string table index overflow")?;
        if linked >= count {
            return Err("ELF dynamic string table index out of range".into());
        }
        let strings_header = section_header(bytes, table, stride, linked)?;
        if u32_at(bytes, strings_header + 4)? != 3 {
            return Err("ELF dynamic symbols lack a string table".into());
        }
        let strings = section_data(bytes, strings_header)?;
        let data = section_data(bytes, header)?;
        let entry_size = usize_at(bytes, header + 56)?;
        if entry_size < 24 || data.len() % entry_size != 0 {
            return Err("invalid ELF dynamic symbol size".into());
        }
        for entry in data.chunks_exact(entry_size) {
            if !matches!(entry[4] >> 4, 1 | 2) || entry[4] & 15 != 1 || u16_at(entry, 6)? == 0 {
                continue;
            }
            let size = usize::try_from(u64_at(entry, 16)?)
                .map_err(|_| "shared data symbol size overflow")?;
            if size == 0 {
                continue;
            }
            let name = string_at(
                strings,
                usize::try_from(u32_at(entry, 0)?)
                    .map_err(|_| "shared data symbol name overflow")?,
            )?;
            if !name.is_empty() {
                exports.entry(name).or_insert(size);
            }
        }
    }
    Ok(exports)
}

/// Read PT_INTERP from an ELF64 executable to select the target loader.
pub(crate) fn interpreter_path(bytes: &[u8]) -> Result<Option<String>, String> {
    if bytes.get(0..4) != Some(b"\x7fELF".as_slice())
        || bytes.get(4) != Some(&2)
        || bytes.get(5) != Some(&1)
    {
        return Err("expected little-endian ELF64 executable".into());
    }
    let table = usize_at(bytes, 32)?;
    let stride = usize::from(u16_at(bytes, 54)?);
    let count = usize::from(u16_at(bytes, 56)?);
    if stride < 56 && count != 0 {
        return Err("invalid ELF program header size".into());
    }
    for index in 0..count {
        let offset = index
            .checked_mul(stride)
            .and_then(|step| table.checked_add(step))
            .ok_or("ELF program header offset overflow")?;
        bytes
            .get(
                offset
                    ..offset
                        .checked_add(56)
                        .ok_or("ELF program header overflow")?,
            )
            .ok_or("truncated ELF program header")?;
        if u32_at(bytes, offset)? != 3 {
            continue;
        }
        let data_offset = usize_at(bytes, offset + 8)?;
        let size = usize_at(bytes, offset + 32)?;
        let data = bytes
            .get(
                data_offset
                    ..data_offset
                        .checked_add(size)
                        .ok_or("ELF interpreter size overflow")?,
            )
            .ok_or("ELF interpreter extends beyond file")?;
        let Some(raw) = data.strip_suffix(&[0]) else {
            return Err("ELF interpreter path is not null terminated".into());
        };
        let path = std::str::from_utf8(raw).map_err(|_| "ELF interpreter path is not UTF-8")?;
        if !path.starts_with('/') || path.len() < 2 {
            return Err("ELF interpreter path is not absolute".into());
        }
        return Ok(Some(path.to_owned()));
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_truncated_and_wrong_architecture_objects() {
        assert!(relocatable(&[]).is_err());
        assert!(relocatable(b"not an object").is_err());
        let mut header = vec![0; 64];
        header[..4].copy_from_slice(b"\x7fELF");
        header[4..7].copy_from_slice(&[2, 1, 1]);
        header[16..18].copy_from_slice(&1u16.to_le_bytes());
        header[18..20].copy_from_slice(&62u16.to_le_bytes());
        assert!(relocatable(&header).is_err());
    }

    #[test]
    fn reads_host_elf_interpreter_when_present() {
        let path = std::env::current_exe().unwrap();
        let bytes = std::fs::read(path).unwrap();
        let path = interpreter_path(&bytes).unwrap();
        if let Some(path) = path {
            assert!(path.starts_with('/'));
            assert!(std::path::Path::new(&path).exists());
        }
    }
}
