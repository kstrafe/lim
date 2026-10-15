//! Link compiler-encoded code with supported ELF64 relocatable objects.
//!
//! This module owns symbol resolution and object relocation. It does not
//! parse Lim source or encode instructions.

use std::collections::BTreeMap;
use std::{
    env, fs,
    path::{Path, PathBuf},
};

use crate::{
    elf_object, elf_writer,
    native_assembly::{Assembled, SectionOffset},
};

struct PlacedObject<'a> {
    object: &'a elf_object::Object,
    sections: BTreeMap<usize, Address>,
}

#[derive(Clone, Copy)]
pub(crate) enum Address {
    Code(usize),
    Rodata(usize),
    Data(usize),
    Absolute(u64),
}

impl Address {
    pub(crate) fn virtual_address(self) -> Result<u64, String> {
        match self {
            Self::Code(offset) => elf_writer::code_address(offset),
            Self::Rodata(offset) => elf_writer::rodata_address(offset),
            Self::Data(offset) => elf_writer::data_address(offset),
            Self::Absolute(address) => Ok(address),
        }
    }

    fn advance(self, count: usize) -> Result<Self, String> {
        match self {
            Self::Code(offset) => offset.checked_add(count).map(Self::Code),
            Self::Rodata(offset) => offset.checked_add(count).map(Self::Rodata),
            Self::Data(offset) => offset.checked_add(count).map(Self::Data),
            Self::Absolute(_) => None,
        }
        .ok_or("linked section address overflow".into())
    }
}

pub(crate) struct ForeignReference {
    pub offset: Address,
    pub symbol: String,
    pub addend: i64,
    pub origin: String,
}

pub(crate) struct ForeignGotReference {
    pub offset: Address,
    pub symbol: String,
    pub addend: i64,
    pub origin: String,
}

pub(crate) struct ForeignCopyReference {
    pub offset: Address,
    pub symbol: String,
    pub addend: i64,
    pub origin: String,
}

pub(crate) struct ForeignAbsoluteReference {
    pub offset: usize,
    pub symbol: String,
    pub addend: i64,
    pub origin: String,
}

pub(crate) struct Linked {
    pub code: Vec<u8>,
    pub rodata: Vec<u8>,
    pub data: Vec<u8>,
    pub entry: usize,
    pub foreign: Vec<ForeignReference>,
    pub foreign_got: Vec<ForeignGotReference>,
    pub foreign_copy: Vec<ForeignCopyReference>,
    pub foreign_absolute: Vec<ForeignAbsoluteReference>,
}

fn align_up(value: usize, align: usize) -> Result<usize, String> {
    value
        .checked_add(align - 1)
        .map(|value| value & !(align - 1))
        .ok_or("linked section alignment overflow".into())
}

fn defined_symbol(
    object: &PlacedObject<'_>,
    symbol: &elf_object::Symbol,
) -> Result<Option<Address>, String> {
    if symbol.section == 0 {
        return Ok(None);
    }
    if symbol.section >= 0xff00 {
        return Err(format!("unsupported special ELF symbol '{}'", symbol.name));
    }
    let section = object
        .object
        .sections
        .iter()
        .find(|section| section.index == symbol.section)
        .ok_or_else(|| format!("symbol '{}' is not in an allocated section", symbol.name))?;
    if symbol.value > section.size {
        return Err(format!("symbol '{}' exceeds its section", symbol.name));
    }
    object
        .sections
        .get(&symbol.section)
        .ok_or("linked symbol section was not placed")?
        .advance(symbol.value)
        .map(Some)
}

/// Return linked code and entry offset for objects using the supported ELF64
/// RELA relocations. An unsupported object is rejected without modifying the
/// caller's image.
pub(crate) fn link(
    assembled: &Assembled,
    objects: &[elf_object::Object],
    allow_foreign: bool,
) -> Result<Linked, String> {
    let mut code = assembled.code.bytes.clone();
    let mut rodata = assembled.rodata.clone();
    let mut data = assembled.data.clone();
    let mut foreign = Vec::new();
    let mut foreign_got = Vec::new();
    let mut foreign_copy = Vec::new();
    let mut foreign_absolute = Vec::new();
    let mut placed = Vec::new();
    for object in objects {
        let mut sections = BTreeMap::new();
        for section in &object.sections {
            if section.size > 128 * 1024 * 1024 {
                return Err(format!(
                    "ELF section '{}' exceeds the 128 MiB linker limit",
                    section.name
                ));
            }
            let (bytes, address) = if section.writable {
                (&mut data, 2)
            } else if section.executable {
                (&mut code, 0)
            } else {
                (&mut rodata, 1)
            };
            let start = align_up(bytes.len(), section.align)?;
            bytes.resize(start, 0);
            sections.insert(
                section.index,
                match address {
                    0 => Address::Code(start),
                    1 => Address::Rodata(start),
                    _ => Address::Data(start),
                },
            );
            bytes.extend_from_slice(&section.data);
            if section.data.len() < section.size {
                bytes.resize(
                    start
                        .checked_add(section.size)
                        .ok_or("ELF section size overflow")?,
                    0,
                );
            }
        }
        placed.push(PlacedObject { object, sections });
    }
    let mut globals = assembled
        .symbols
        .iter()
        .map(|(name, offset)| {
            (
                name.clone(),
                match offset {
                    SectionOffset::Code(offset) => Address::Code(*offset),
                    SectionOffset::Rodata(offset) => Address::Rodata(*offset),
                    SectionOffset::Data(offset) => Address::Data(*offset),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut weak = BTreeMap::new();
    for object in &placed {
        for symbol in &object.object.symbols {
            if !symbol.global || symbol.name.is_empty() {
                continue;
            }
            let Some(offset) = defined_symbol(object, symbol)? else {
                continue;
            };
            if symbol.weak {
                weak.entry(symbol.name.clone()).or_insert(offset);
            } else if globals.insert(symbol.name.clone(), offset).is_some() {
                return Err(format!("duplicate native symbol '{}'", symbol.name));
            }
        }
    }
    for (name, offset) in weak {
        globals.entry(name).or_insert(offset);
    }
    for difference in &assembled.data_differences {
        let target = globals
            .get(&difference.target)
            .ok_or("missing table target")?;
        let base = globals.get(&difference.base).ok_or("missing table base")?;
        let displacement =
            i32::try_from(target.virtual_address()? as i128 - base.virtual_address()? as i128)
                .map_err(|_| {
                    format!(
                        "assembly line {}: table displacement exceeds signed 32-bit range",
                        difference.line
                    )
                })?;
        rodata
            .get_mut(difference.offset..difference.offset + 4)
            .ok_or("table relocation extends beyond rodata")?
            .copy_from_slice(&displacement.to_le_bytes());
    }
    for relocation in &assembled.unresolved {
        let Some(target) = globals.get(&relocation.symbol) else {
            if allow_foreign {
                foreign.push(ForeignReference {
                    offset: Address::Code(relocation.offset),
                    symbol: relocation.symbol.clone(),
                    addend: relocation.addend,
                    origin: assembled
                        .relocation_lines
                        .get(&relocation.offset)
                        .map(|line| format!("assembly line {line}"))
                        .unwrap_or_else(|| "assembly relocation".into()),
                });
                continue;
            }
            return Err(format!("undefined native symbol '{}'", relocation.symbol));
        };
        let after = relocation
            .offset
            .checked_add(4)
            .ok_or("native relocation offset overflow")?;
        let displacement = (target.virtual_address()? as i128) + (relocation.addend as i128)
            - (elf_writer::code_address(after)? as i128);
        let displacement = i32::try_from(displacement)
            .map_err(|_| "native PC-relative relocation exceeds range")?;
        code.get_mut(relocation.offset..after)
            .ok_or("native relocation extends beyond code")?
            .copy_from_slice(&displacement.to_le_bytes());
    }
    for object in &placed {
        for relocation in &object.object.relocations {
            let Some(base) = object.sections.get(&relocation.section) else {
                continue;
            };
            let section = object
                .object
                .sections
                .iter()
                .find(|section| section.index == relocation.section)
                .ok_or("object relocation section missing")?;
            let width = match relocation.kind {
                1 => 8,                             // R_X86_64_64
                2 | 4 | 9 | 10 | 11 | 41 | 42 => 4, // PC32, PLT32, GOTPCREL, 32, 32S, GOTPCRELX
                kind => return Err(format!("unsupported x86-64 relocation type {kind}")),
            };
            let end = relocation
                .offset
                .checked_add(width)
                .ok_or("object relocation offset overflow")?;
            if end > section.size {
                return Err("object relocation extends beyond section".into());
            }
            let place = base.advance(relocation.offset)?;
            let symbol = &object.object.symbols[relocation.symbol];
            let target = match defined_symbol(object, symbol)? {
                Some(offset) => offset,
                None => match globals.get(&symbol.name) {
                    Some(offset) => *offset,
                    None if symbol.weak || symbol.name.is_empty() => Address::Absolute(0),
                    None if allow_foreign && relocation.kind == 1 => {
                        let Address::Data(offset) = place else {
                            return Err(
                                "foreign absolute relocation requires a writable data section"
                                    .into(),
                            );
                        };
                        foreign_absolute.push(ForeignAbsoluteReference {
                            offset,
                            symbol: symbol.name.clone(),
                            addend: relocation.addend,
                            origin: format!(
                                "object section {}+0x{:x}",
                                section.name, relocation.offset
                            ),
                        });
                        continue;
                    }
                    None if allow_foreign && matches!(relocation.kind, 9 | 41 | 42) => {
                        foreign_got.push(ForeignGotReference {
                            offset: place,
                            symbol: symbol.name.clone(),
                            addend: relocation.addend,
                            origin: format!(
                                "object section {}+0x{:x}",
                                section.name, relocation.offset
                            ),
                        });
                        continue;
                    }
                    None if allow_foreign && relocation.kind == 4 => {
                        foreign.push(ForeignReference {
                            offset: place,
                            symbol: symbol.name.clone(),
                            addend: relocation
                                .addend
                                .checked_add(4)
                                .ok_or("foreign relocation addend overflow")?,
                            origin: format!(
                                "object section {}+0x{:x}",
                                section.name, relocation.offset
                            ),
                        });
                        continue;
                    }
                    None if allow_foreign && relocation.kind == 2 => {
                        foreign_copy.push(ForeignCopyReference {
                            offset: place,
                            symbol: symbol.name.clone(),
                            addend: relocation.addend,
                            origin: format!(
                                "object section {}+0x{:x}",
                                section.name, relocation.offset
                            ),
                        });
                        continue;
                    }
                    None => return Err(format!("undefined native symbol '{}'", symbol.name)),
                },
            };
            let value = match relocation.kind {
                2 | 4 => {
                    (target.virtual_address()? as i128) + (relocation.addend as i128)
                        - (place.virtual_address()? as i128)
                }
                9 | 41 | 42 => {
                    let aligned = align_up(data.len(), 8)?;
                    data.resize(aligned, 0);
                    data.extend_from_slice(&target.virtual_address()?.to_le_bytes());
                    (elf_writer::data_address(aligned)? as i128) + (relocation.addend as i128)
                        - (place.virtual_address()? as i128)
                }
                _ => (target.virtual_address()? as i128) + (relocation.addend as i128),
            };
            let bytes = match place {
                Address::Code(offset) => code.get_mut(offset..offset + width),
                Address::Rodata(offset) => rodata.get_mut(offset..offset + width),
                Address::Data(offset) => data.get_mut(offset..offset + width),
                Address::Absolute(_) => None,
            }
            .ok_or("object relocation extends beyond image")?;
            match relocation.kind {
                1 => bytes.copy_from_slice(
                    &u64::try_from(value)
                        .map_err(|_| "absolute relocation exceeds 64 bits")?
                        .to_le_bytes(),
                ),
                2 | 4 | 9 | 11 | 41 | 42 => bytes.copy_from_slice(
                    &i32::try_from(value)
                        .map_err(|_| "signed relocation exceeds 32 bits")?
                        .to_le_bytes(),
                ),
                10 => bytes.copy_from_slice(
                    &u32::try_from(value)
                        .map_err(|_| "unsigned relocation exceeds 32 bits")?
                        .to_le_bytes(),
                ),
                _ => unreachable!(),
            }
        }
    }
    let entry = *globals
        .get("_start")
        .ok_or("linked ELF has no _start symbol")?;
    let Address::Code(entry) = entry else {
        return Err("native entry lies in data".into());
    };
    Ok(Linked {
        code,
        rodata,
        data,
        entry,
        foreign,
        foreign_got,
        foreign_copy,
        foreign_absolute,
    })
}

pub(crate) struct ResolvedLibraries {
    pub paths: Vec<String>,
    pub copy_sizes: BTreeMap<String, usize>,
}

fn search_directories(interpreter: &str) -> Vec<PathBuf> {
    let mut directories = Vec::new();
    if let Some(parent) = Path::new(interpreter).parent() {
        directories.push(parent.to_path_buf());
    }
    if let Some(value) = env::var_os("NIX_LDFLAGS") {
        for word in value.to_string_lossy().split_whitespace() {
            if let Some(directory) = word.strip_prefix("-L") {
                if !directory.is_empty() {
                    directories.push(PathBuf::from(directory));
                }
            }
        }
    }
    for variable in ["LIBRARY_PATH", "LD_LIBRARY_PATH"] {
        if let Some(value) = env::var_os(variable) {
            directories.extend(env::split_paths(&value));
        }
    }
    for directory in [
        "/lib64",
        "/lib/x86_64-linux-gnu",
        "/usr/lib/x86_64-linux-gnu",
        "/usr/lib64",
        "/usr/lib",
    ] {
        directories.push(PathBuf::from(directory));
    }
    directories
}

/// Resolve requested -l names to real ELF DSOs and check that every imported
/// symbol has at least one provider before publishing an executable.
pub(crate) fn resolve_libraries(
    foreign: &[ForeignReference],
    foreign_got: &[ForeignGotReference],
    foreign_copy: &[ForeignCopyReference],
    foreign_absolute: &[ForeignAbsoluteReference],
    requested: &[String],
    interpreter: &str,
) -> Result<ResolvedLibraries, String> {
    let mut names = requested.to_vec();
    if (!foreign.is_empty()
        || !foreign_got.is_empty()
        || !foreign_copy.is_empty()
        || !foreign_absolute.is_empty())
        && !names.iter().any(|name| name == "c")
    {
        names.push("c".into());
    }
    if names.is_empty() {
        return Ok(ResolvedLibraries {
            paths: Vec::new(),
            copy_sizes: BTreeMap::new(),
        });
    }
    let directories = search_directories(interpreter);
    let mut paths = Vec::new();
    let mut exports = std::collections::BTreeSet::new();
    let mut copy_sizes = BTreeMap::new();
    for name in names {
        if name.is_empty()
            || !name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'+'))
        {
            return Err(format!("invalid shared library name '{name}'"));
        }
        let candidates = [
            format!("lib{name}.so"),
            format!("lib{name}.so.6"),
            format!("lib{name}.so.0"),
            format!("lib{name}.so.1"),
            format!("lib{name}.so.2"),
        ];
        let mut found = None;
        for directory in &directories {
            for filename in &candidates {
                let path = directory.join(filename);
                let Ok(bytes) = fs::read(&path) else {
                    continue;
                };
                let Ok(symbols) = elf_object::shared_exports(&bytes) else {
                    continue;
                }; // skip linker scripts
                let data_symbols = elf_object::shared_data_exports(&bytes)?;
                let path = fs::canonicalize(&path).map_err(|error| {
                    format!("cannot resolve library {}: {error}", path.display())
                })?;
                found = Some((path, symbols, data_symbols));
                break;
            }
            if found.is_some() {
                break;
            }
        }
        let (path, symbols, data_symbols) =
            found.ok_or_else(|| format!("shared library '-l{name}' was not found"))?;
        exports.extend(symbols);
        for (symbol, size) in data_symbols {
            copy_sizes.entry(symbol).or_insert(size);
        }
        let path = path
            .to_str()
            .ok_or("shared library path is not UTF-8")?
            .to_owned();
        if !paths.contains(&path) {
            paths.push(path);
        }
    }
    for reference in foreign {
        if !exports.contains(&reference.symbol) {
            return Err(format!(
                "no linked shared library exports '{}' ({})",
                reference.symbol, reference.origin
            ));
        }
    }
    for reference in foreign_got {
        if !exports.contains(&reference.symbol) {
            return Err(format!(
                "no linked shared library exports '{}' ({})",
                reference.symbol, reference.origin
            ));
        }
    }
    for reference in foreign_absolute {
        if !exports.contains(&reference.symbol) {
            return Err(format!(
                "no linked shared library exports '{}' ({})",
                reference.symbol, reference.origin
            ));
        }
    }
    let mut requested_copies = BTreeMap::new();
    for reference in foreign_copy {
        let size = *copy_sizes.get(&reference.symbol).ok_or_else(|| {
            format!(
                "no linked shared library has a sized data symbol '{}' ({})",
                reference.symbol, reference.origin
            )
        })?;
        if size > 128 * 1024 * 1024 {
            return Err(format!(
                "foreign data symbol '{}' exceeds 128 MiB",
                reference.symbol
            ));
        }
        requested_copies.insert(reference.symbol.clone(), size);
    }
    Ok(ResolvedLibraries {
        paths,
        copy_sizes: requested_copies,
    })
}
