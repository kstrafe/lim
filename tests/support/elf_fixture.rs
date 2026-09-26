// Minimal ELF64 ET_REL fixtures for native-linker tests. This is intentionally
// test-only: the compiler reads objects, but does not need to emit them.

pub struct Section<'a> {
    pub name: &'a str,
    pub bytes: &'a [u8],
    pub size: usize,
    pub writable: bool,
    pub executable: bool,
}

pub struct Symbol<'a> {
    pub name: &'a str,
    pub section: Option<usize>, // index into the caller's section list
    pub value: u64,
    pub global: bool,
}

pub struct Relocation {
    pub section: usize,
    pub offset: u64,
    pub symbol: usize, // index into the caller's symbol list
    pub kind: u32,
    pub addend: i64,
}

fn align(bytes: &mut Vec<u8>, alignment: usize) {
    bytes.resize((bytes.len() + alignment - 1) & !(alignment - 1), 0);
}

fn string(table: &mut Vec<u8>, value: &str) -> u32 {
    let offset = u32::try_from(table.len()).unwrap();
    table.extend_from_slice(value.as_bytes());
    table.push(0);
    offset
}

fn u16_at(bytes: &mut [u8], offset: usize, value: u16) {
    bytes[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
}

fn u32_at(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn u64_at(bytes: &mut [u8], offset: usize, value: u64) {
    bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

struct Header {
    name: u32,
    kind: u32,
    flags: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    alignment: u64,
    entry_size: u64,
}

pub fn object(
    sections: &[Section<'_>],
    symbols: &[Symbol<'_>],
    relocations: &[Relocation],
) -> Vec<u8> {
    object_with_weak(sections, symbols, relocations, &[])
}

pub fn object_with_weak(
    sections: &[Section<'_>],
    symbols: &[Symbol<'_>],
    relocations: &[Relocation],
    weak_symbols: &[usize],
) -> Vec<u8> {
    let mut bytes = vec![0; 64];
    let mut names = vec![0];
    let mut headers = Vec::new();
    headers.push(Header {
        name: 0,
        kind: 0,
        flags: 0,
        offset: 0,
        size: 0,
        link: 0,
        info: 0,
        alignment: 0,
        entry_size: 0,
    });
    for section in sections {
        align(&mut bytes, 8);
        let offset = bytes.len();
        let kind = if section.bytes.len() == section.size {
            1
        } else {
            8
        };
        assert!(section.bytes.len() == section.size || section.bytes.is_empty());
        if kind == 1 {
            bytes.extend_from_slice(section.bytes);
        }
        headers.push(Header {
            name: string(&mut names, section.name),
            kind,
            flags: 2
                | if section.writable { 1 } else { 0 }
                | if section.executable { 4 } else { 0 },
            offset: offset as u64,
            size: section.size as u64,
            link: 0,
            info: 0,
            alignment: 8,
            entry_size: 0,
        });
    }
    let mut symbol_strings = vec![0];
    let mut symbol_data = vec![0; 24];
    for (index, symbol) in symbols.iter().enumerate() {
        let mut entry = [0u8; 24];
        u32_at(&mut entry, 0, string(&mut symbol_strings, symbol.name));
        entry[4] = if weak_symbols.contains(&index) {
            0x22
        } else if symbol.global {
            0x12
        } else {
            0x02
        };
        u16_at(
            &mut entry,
            6,
            symbol
                .section
                .map(|index| u16::try_from(index + 1).unwrap())
                .unwrap_or(0),
        );
        u64_at(&mut entry, 8, symbol.value);
        symbol_data.extend_from_slice(&entry);
    }
    let mut relocation_sections = Vec::new();
    for target in 0..sections.len() {
        let relevant = relocations
            .iter()
            .filter(|relocation| relocation.section == target)
            .collect::<Vec<_>>();
        if relevant.is_empty() {
            continue;
        }
        let mut data = Vec::new();
        for relocation in relevant {
            assert!(relocation.symbol < symbols.len());
            data.extend_from_slice(&relocation.offset.to_le_bytes());
            data.extend_from_slice(
                &(((relocation.symbol as u64 + 1) << 32) | u64::from(relocation.kind))
                    .to_le_bytes(),
            );
            data.extend_from_slice(&relocation.addend.to_le_bytes());
        }
        relocation_sections.push((target, data));
    }
    let symtab_index = u32::try_from(headers.len() + relocation_sections.len() + 1).unwrap();
    let strtab_index = symtab_index - 1;
    for (target, data) in relocation_sections {
        align(&mut bytes, 8);
        let offset = bytes.len();
        bytes.extend_from_slice(&data);
        headers.push(Header {
            name: string(&mut names, &format!(".rela{}", sections[target].name)),
            kind: 4,
            flags: 0,
            offset: offset as u64,
            size: data.len() as u64,
            link: symtab_index,
            info: u32::try_from(target + 1).unwrap(),
            alignment: 8,
            entry_size: 24,
        });
    }
    align(&mut bytes, 8);
    let strings_offset = bytes.len();
    bytes.extend_from_slice(&symbol_strings);
    headers.push(Header {
        name: string(&mut names, ".strtab"),
        kind: 3,
        flags: 0,
        offset: strings_offset as u64,
        size: symbol_strings.len() as u64,
        link: 0,
        info: 0,
        alignment: 1,
        entry_size: 0,
    });
    align(&mut bytes, 8);
    let symbols_offset = bytes.len();
    bytes.extend_from_slice(&symbol_data);
    headers.push(Header {
        name: string(&mut names, ".symtab"),
        kind: 2,
        flags: 0,
        offset: symbols_offset as u64,
        size: symbol_data.len() as u64,
        link: strtab_index,
        info: 1,
        alignment: 8,
        entry_size: 24,
    });
    let names_index = u16::try_from(headers.len()).unwrap();
    let names_header_name = string(&mut names, ".shstrtab");
    let names_offset = bytes.len();
    bytes.extend_from_slice(&names);
    headers.push(Header {
        name: names_header_name,
        kind: 3,
        flags: 0,
        offset: names_offset as u64,
        size: names.len() as u64,
        link: 0,
        info: 0,
        alignment: 1,
        entry_size: 0,
    });
    align(&mut bytes, 8);
    let table_offset = bytes.len();
    for header in &headers {
        let at = bytes.len();
        bytes.resize(at + 64, 0);
        u32_at(&mut bytes, at, header.name);
        u32_at(&mut bytes, at + 4, header.kind);
        u64_at(&mut bytes, at + 8, header.flags);
        u64_at(&mut bytes, at + 24, header.offset);
        u64_at(&mut bytes, at + 32, header.size);
        u32_at(&mut bytes, at + 40, header.link);
        u32_at(&mut bytes, at + 44, header.info);
        u64_at(&mut bytes, at + 48, header.alignment);
        u64_at(&mut bytes, at + 56, header.entry_size);
    }
    bytes[0..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    u16_at(&mut bytes, 16, 1);
    u16_at(&mut bytes, 18, 62);
    u32_at(&mut bytes, 20, 1);
    u64_at(&mut bytes, 40, table_offset as u64);
    u16_at(&mut bytes, 52, 64);
    u16_at(&mut bytes, 58, 64);
    u16_at(&mut bytes, 60, u16::try_from(headers.len()).unwrap());
    u16_at(&mut bytes, 62, names_index);
    bytes
}
