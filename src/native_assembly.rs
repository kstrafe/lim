//! Adapter from the backend's inspectable Intel assembly to machine operands.
//!
//! This is separate from Lim's source parser and semantic analyses. It rejects
//! syntax outside the implemented native instruction subset explicitly.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};

use crate::instruction_encoder::{
    AtomicOperation, BinaryOperation, Condition, EncodedInstructions, Instruction, Memory,
    Register, Relocation, ShiftOperation, UnaryOperation, Width, XmmOperand, XmmOperation,
};

pub(crate) struct Assembled {
    pub code: EncodedInstructions,
    pub rodata: Vec<u8>,
    pub symbols: BTreeMap<String, SectionOffset>,
    pub unresolved: Vec<Relocation>,
    pub relocation_lines: BTreeMap<usize, usize>,
}

#[derive(Clone, Copy)]
pub(crate) enum SectionOffset {
    Code(usize),
    Rodata(usize),
}

pub(crate) fn assemble(source: &str) -> Result<Assembled, String> {
    let mut code = EncodedInstructions::default();
    let mut symbols = BTreeMap::new();
    let mut numeric_definitions: BTreeMap<String, Vec<(usize, String)>> = BTreeMap::new();
    let mut set_definitions = BTreeMap::new();
    for (index, raw) in source.lines().enumerate() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if let Some(definition) = line.strip_prefix(".set ") {
            let (name, expression) = definition
                .split_once(',')
                .ok_or(".set requires name and value")?;
            let name = name.trim();
            if name.is_empty()
                || set_definitions
                    .insert(name.to_owned(), expression.trim().to_owned())
                    .is_some()
            {
                return Err(format!(
                    "assembly line {}: invalid or duplicate .set name",
                    index + 1
                ));
            }
        }
        if let Some(label) = line.strip_suffix(':') {
            if !label.is_empty() && label.bytes().all(|byte| byte.is_ascii_digit()) {
                let definitions = numeric_definitions.entry(label.to_owned()).or_default();
                let symbol = format!(".Llim_numeric_{label}_{}", definitions.len());
                definitions.push((index, symbol));
            }
        }
    }
    let mut constants = BTreeMap::new();
    for name in set_definitions.keys() {
        let value = resolve_set(name, &set_definitions, &mut constants, &mut BTreeSet::new())?;
        constants.insert(name.clone(), value);
    }
    let mut in_rodata = false;
    let mut rodata = Vec::new();
    let mut relocation_lines = BTreeMap::new();
    for (index, raw) in source.lines().enumerate() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if let Some(symbol) = line.strip_suffix(':') {
            let symbol = if symbol.bytes().all(|byte| byte.is_ascii_digit()) {
                numeric_definitions
                    .get(symbol)
                    .and_then(|definitions| definitions.iter().find(|(line, _)| *line == index))
                    .map(|(_, symbol)| symbol.as_str())
                    .ok_or("missing numeric label definition")?
            } else {
                symbol
            };
            let offset = if in_rodata {
                SectionOffset::Rodata(rodata.len())
            } else {
                SectionOffset::Code(code.bytes.len())
            };
            if symbols.insert(symbol.to_owned(), offset).is_some() {
                return Err(format!(
                    "assembly line {}: duplicate symbol '{symbol}'",
                    index + 1
                ));
            }
            continue;
        }
        if line.starts_with('.') {
            if line.starts_with(".set ") {
                continue;
            }
            if line == ".section .rodata" {
                in_rodata = true;
                continue;
            }
            if line == ".text" || line == ".section .text" {
                in_rodata = false;
                continue;
            }
            if let Some(value) = line.strip_prefix(".align ") {
                if !in_rodata {
                    return Err(format!(
                        "assembly line {}: alignment outside .rodata",
                        index + 1
                    ));
                }
                let alignment =
                    usize::try_from(parse_u64(value)?).map_err(|_| "alignment exceeds usize")?;
                if alignment == 0 || !alignment.is_power_of_two() || alignment > 4096 {
                    return Err(format!(
                        "assembly line {}: unsupported alignment",
                        index + 1
                    ));
                }
                let padding = (alignment - rodata.len() % alignment) % alignment;
                rodata.resize(rodata.len() + padding, 0);
                continue;
            }
            if let Some(value) = line.strip_prefix(".quad ") {
                if !in_rodata {
                    return Err(format!(
                        "assembly line {}: .quad outside .rodata",
                        index + 1
                    ));
                }
                rodata.extend_from_slice(&parse_u64(value)?.to_le_bytes());
                continue;
            }
            if let Some(value) = line.strip_prefix(".long ") {
                if !in_rodata {
                    return Err(format!(
                        "assembly line {}: .long outside .rodata",
                        index + 1
                    ));
                }
                let value = parse_u64(value)?;
                let value = u32::try_from(value).map_err(|_| "32-bit datum exceeds width")?;
                rodata.extend_from_slice(&value.to_le_bytes());
                continue;
            }
            if line == ".intel_syntax noprefix"
                || line.starts_with(".globl ")
                || line.starts_with(".type ")
                || line.starts_with(".size ")
                || line.starts_with(".extern ")
                || line.starts_with(".section .note.GNU-stack,")
            {
                continue;
            }
            return Err(format!(
                "assembly line {}: unsupported directive '{line}'",
                index + 1
            ));
        }
        if in_rodata {
            return Err(format!(
                "assembly line {}: instruction in .rodata",
                index + 1
            ));
        }
        let expanded;
        let line = if let Some(at) = line.find("OFFSET ") {
            let expression = &line[at + 7..];
            let value = evaluate_set_expression(
                expression,
                &set_definitions,
                &mut constants,
                &mut BTreeSet::new(),
            )?;
            expanded = format!("{}{value}", &line[..at]);
            expanded.as_str()
        } else {
            line
        };
        let mut instruction = parse_instruction(line)
            .map_err(|error| format!("assembly line {}: {error}: '{line}'", index + 1))?;
        resolve_numeric_instruction(&mut instruction, index, &numeric_definitions)
            .map_err(|error| format!("assembly line {}: {error}: '{line}'", index + 1))?;
        let first_relocation = code.relocations.len();
        code.append(&instruction)
            .map_err(|error| format!("assembly line {}: {error}: '{line}'", index + 1))?;
        for relocation in &code.relocations[first_relocation..] {
            relocation_lines.insert(relocation.offset, index + 1);
        }
    }
    let mut unresolved = Vec::new();
    for (index, relocation) in code.relocations.clone().iter().enumerate() {
        if let Some(&SectionOffset::Code(target)) = symbols.get(&relocation.symbol) {
            code.resolve_local(index, target)?;
        } else {
            unresolved.push(relocation.clone());
        }
    }
    Ok(Assembled {
        code,
        rodata,
        symbols,
        unresolved,
        relocation_lines,
    })
}

fn resolve_set(
    name: &str,
    definitions: &BTreeMap<String, String>,
    cache: &mut BTreeMap<String, i128>,
    visiting: &mut BTreeSet<String>,
) -> Result<i128, String> {
    if let Some(value) = cache.get(name) {
        return Ok(*value);
    }
    let expression = definitions
        .get(name)
        .ok_or_else(|| format!("undefined .set symbol '{name}'"))?;
    if !visiting.insert(name.to_owned()) {
        return Err(format!("cyclic .set expression at '{name}'"));
    }
    let result = evaluate_set_expression(expression, definitions, cache, visiting);
    visiting.remove(name);
    let value = result?;
    cache.insert(name.to_owned(), value);
    Ok(value)
}

fn evaluate_set_expression(
    expression: &str,
    definitions: &BTreeMap<String, String>,
    cache: &mut BTreeMap<String, i128>,
    visiting: &mut BTreeSet<String>,
) -> Result<i128, String> {
    let expression = expression.trim();
    if expression.is_empty() {
        return Err("empty .set expression".into());
    }
    let mut total = 0i128;
    let mut start = 0usize;
    let mut sign = 1i128;
    for (index, byte) in expression.bytes().enumerate() {
        if byte != b'+' && byte != b'-' {
            continue;
        }
        if index == start {
            sign = if byte == b'-' { -1 } else { 1 };
            start = index + 1;
            continue;
        }
        let term = expression[start..index].trim();
        let value = set_term(term, definitions, cache, visiting)?;
        total = total
            .checked_add(sign * value)
            .ok_or(".set arithmetic overflow")?;
        sign = if byte == b'-' { -1 } else { 1 };
        start = index + 1;
    }
    let value = set_term(expression[start..].trim(), definitions, cache, visiting)?;
    total
        .checked_add(sign * value)
        .ok_or(".set arithmetic overflow".into())
}

fn set_term(
    term: &str,
    definitions: &BTreeMap<String, String>,
    cache: &mut BTreeMap<String, i128>,
    visiting: &mut BTreeSet<String>,
) -> Result<i128, String> {
    if let Some(hex) = term.strip_prefix("0x") {
        return i128::from_str_radix(hex, 16).map_err(|_| "invalid .set hex value".into());
    }
    if let Ok(value) = term.parse::<i128>() {
        return Ok(value);
    }
    resolve_set(term, definitions, cache, visiting)
}

fn resolve_numeric_instruction(
    instruction: &mut Instruction,
    line: usize,
    definitions: &BTreeMap<String, Vec<(usize, String)>>,
) -> Result<(), String> {
    let target = match instruction {
        Instruction::Call(symbol)
        | Instruction::Jump(symbol)
        | Instruction::JumpCondition { symbol, .. }
        | Instruction::LoadRip { symbol, .. }
        | Instruction::StoreRip { symbol, .. }
        | Instruction::LeaRip { symbol, .. } => symbol,
        _ => return Ok(()),
    };
    let Some(direction) = target.chars().last() else {
        return Ok(());
    };
    if !matches!(direction, 'b' | 'f') {
        return Ok(());
    }
    let number = &target[..target.len() - 1];
    if number.is_empty() || !number.bytes().all(|byte| byte.is_ascii_digit()) {
        return Ok(());
    }
    let matching = definitions
        .get(number)
        .ok_or_else(|| format!("undefined numeric label {target}"))?;
    let definition = if direction == 'b' {
        matching.iter().rev().find(|(at, _)| *at < line)
    } else {
        matching.iter().find(|(at, _)| *at > line)
    };
    *target = definition
        .ok_or_else(|| format!("undefined numeric label {target}"))?
        .1
        .clone();
    Ok(())
}

fn parse_instruction(line: &str) -> Result<Instruction, String> {
    let (mnemonic, operands) = line.split_once(char::is_whitespace).unwrap_or((line, ""));
    let operands = operands.trim();
    if mnemonic == "lock" {
        let mut instruction = parse_instruction(operands)?;
        match &mut instruction {
            Instruction::AtomicMemoryRegister {
                operation: AtomicOperation::CompareExchange | AtomicOperation::ExchangeAdd,
                locked,
                ..
            } => {
                *locked = true;
                return Ok(instruction);
            }
            _ => return Err("lock requires cmpxchg or xadd with a memory destination".into()),
        }
    }
    let (left, right) = operands
        .split_once(',')
        .map(|(a, b)| (a.trim(), b.trim()))
        .unwrap_or((operands, ""));
    let register =
        |name: &str| parse_register(name).ok_or_else(|| format!("unknown register '{name}'"));
    let binary = |operation| -> Result<Instruction, String> {
        if let Some((width, memory)) = parse_memory(left)? {
            if let Some((register, register_width)) = parse_register(right) {
                if width != register_width {
                    return Err("memory/register operand widths differ".into());
                }
                return Ok(Instruction::BinaryMemoryRegister {
                    operation,
                    width,
                    memory,
                    register,
                    memory_destination: true,
                });
            }
            return Ok(Instruction::BinaryMemoryImmediate {
                operation,
                width,
                memory,
                value: parse_i32(right)?,
            });
        }
        let (destination, width) = register(left)?;
        if let Some((source, source_width)) = parse_register(right) {
            if width != source_width {
                return Err("register operand widths differ".into());
            }
            Ok(Instruction::BinaryRegister {
                operation,
                width,
                destination,
                source,
            })
        } else if let Some((source_width, memory)) = parse_memory(right)? {
            if width != source_width {
                return Err("register/memory operand widths differ".into());
            }
            Ok(Instruction::BinaryMemoryRegister {
                operation,
                width,
                memory,
                register: destination,
                memory_destination: false,
            })
        } else {
            Ok(Instruction::BinaryImmediate {
                operation,
                width,
                destination,
                value: parse_i32(right)?,
            })
        }
    };
    let branch = |condition| Instruction::JumpCondition {
        condition,
        symbol: left.to_owned(),
    };
    let set = |condition| -> Result<Instruction, String> {
        let (destination, width) = register(left)?;
        if width != Width::Byte {
            return Err("setcc requires a byte register".into());
        }
        Ok(Instruction::SetCondition {
            condition,
            destination,
        })
    };
    match mnemonic {
        "cmpxchg" | "xadd" | "xchg" => {
            let (width, memory) =
                parse_memory(left)?.ok_or("atomic operation requires memory destination")?;
            let (register, register_width) = register(right)?;
            if width != register_width {
                return Err("atomic operand widths differ".into());
            }
            let operation = match mnemonic {
                "cmpxchg" => AtomicOperation::CompareExchange,
                "xadd" => AtomicOperation::ExchangeAdd,
                _ => AtomicOperation::Exchange,
            };
            Ok(Instruction::AtomicMemoryRegister {
                operation,
                width,
                memory,
                register,
                locked: false,
            })
        }
        "movd" | "movq" | "movss" | "movsd" | "movaps" | "movapd" | "addss" | "addsd" | "subss"
        | "subsd" | "mulss" | "mulsd" | "divss" | "divsd" | "ucomiss" | "ucomisd" | "cvtsi2ss"
        | "cvtsi2sd" | "cvtss2sd" | "cvttss2si" | "cvttsd2si" => {
            let operation = match mnemonic {
                "movd" => XmmOperation::MoveBits32,
                "movq" => XmmOperation::MoveBits64,
                "movss" => XmmOperation::MoveScalar32,
                "movsd" => XmmOperation::MoveScalar64,
                "movaps" => XmmOperation::MoveAligned32,
                "movapd" => XmmOperation::MoveAligned64,
                "addss" => XmmOperation::Add32,
                "addsd" => XmmOperation::Add64,
                "subss" => XmmOperation::Subtract32,
                "subsd" => XmmOperation::Subtract64,
                "mulss" => XmmOperation::Multiply32,
                "mulsd" => XmmOperation::Multiply64,
                "divss" => XmmOperation::Divide32,
                "divsd" => XmmOperation::Divide64,
                "ucomiss" => XmmOperation::Compare32,
                "ucomisd" => XmmOperation::Compare64,
                "cvtsi2ss" => XmmOperation::ConvertInteger32,
                "cvtsi2sd" => XmmOperation::ConvertInteger64,
                "cvtss2sd" => XmmOperation::Convert32To64,
                "cvttss2si" => XmmOperation::Truncate32ToInteger,
                _ => XmmOperation::Truncate64ToInteger,
            };
            Ok(Instruction::Xmm {
                operation,
                destination: parse_xmm_operand(left)?,
                source: parse_xmm_operand(right)?,
            })
        }
        "mov" => {
            if let Some((destination, width)) = parse_register(left) {
                if let Some((source, source_width)) = parse_register(right) {
                    if width != source_width {
                        return Err("mov register widths differ".into());
                    }
                    Ok(Instruction::MovRegister {
                        width,
                        destination,
                        source,
                    })
                } else if let Some((memory_width, symbol, addend)) = parse_rip_memory(right)? {
                    if width != memory_width.ok_or("RIP load requires a width")? {
                        return Err("mov RIP load width differs from destination".into());
                    }
                    Ok(Instruction::LoadRip {
                        width,
                        destination,
                        symbol,
                        addend,
                    })
                } else if let Some((memory_width, source)) = parse_memory(right)? {
                    if width != memory_width {
                        return Err("mov load width differs from destination".into());
                    }
                    Ok(Instruction::Load {
                        width,
                        destination,
                        source,
                    })
                } else {
                    let mask = match width {
                        Width::Byte => u8::MAX as u64,
                        Width::Word => u16::MAX as u64,
                        Width::Dword => u32::MAX as u64,
                        Width::Qword => u64::MAX,
                    };
                    Ok(Instruction::MovImmediate {
                        width,
                        destination,
                        value: parse_u64(right)? & mask,
                    })
                }
            } else if let Some((width, symbol, addend)) = parse_rip_memory(left)? {
                let width = width.ok_or("RIP store requires a width")?;
                let (source, source_width) = register(right)?;
                if width != source_width {
                    return Err("mov RIP store width differs from source".into());
                }
                Ok(Instruction::StoreRip {
                    width,
                    symbol,
                    addend,
                    source,
                })
            } else if let Some((width, destination)) = parse_memory(left)? {
                if let Some((source, source_width)) = parse_register(right) {
                    if width != source_width {
                        return Err("mov store width differs from source".into());
                    }
                    Ok(Instruction::Store {
                        width,
                        destination,
                        source,
                    })
                } else {
                    Ok(Instruction::StoreImmediate {
                        width,
                        memory: destination,
                        value: parse_i32(right)?,
                    })
                }
            } else {
                Err("mov destination is not a register or memory operand".into())
            }
        }
        "lea" => {
            let (destination, width) = register(left)?;
            if width != Width::Qword {
                return Err("lea requires a 64-bit destination".into());
            }
            if let Some((_, symbol, addend)) = parse_rip_memory(right)? {
                return Ok(Instruction::LeaRip {
                    destination,
                    symbol,
                    addend,
                });
            }
            let (_, source) = parse_memory(right)?.ok_or("lea requires a memory operand")?;
            Ok(Instruction::Lea {
                destination,
                source,
            })
        }
        "xor" => binary(BinaryOperation::Xor),
        "or" => binary(BinaryOperation::Or),
        "add" => binary(BinaryOperation::Add),
        "adc" => binary(BinaryOperation::AddCarry),
        "and" => binary(BinaryOperation::And),
        "sub" => binary(BinaryOperation::Subtract),
        "sbb" => binary(BinaryOperation::SubtractBorrow),
        "cmp" => binary(BinaryOperation::Compare),
        "test" if left == "ah" => Ok(Instruction::TestAhImmediate(
            u8::try_from(parse_i32(right)?).map_err(|_| "AH test mask exceeds byte")?,
        )),
        "test" => binary(BinaryOperation::Test),
        "not" | "neg" | "mul" | "div" | "idiv" => {
            let (register, width) = register(left)?;
            let operation = match mnemonic {
                "not" => UnaryOperation::Not,
                "neg" => UnaryOperation::Negate,
                "mul" => UnaryOperation::Multiply,
                "div" => UnaryOperation::Divide,
                _ => UnaryOperation::SignedDivide,
            };
            Ok(Instruction::UnaryRegister {
                operation,
                width,
                register,
            })
        }
        "cqo" if operands.is_empty() => Ok(Instruction::SignExtendRax {
            width: Width::Qword,
        }),
        "cdq" if operands.is_empty() => Ok(Instruction::SignExtendRax {
            width: Width::Dword,
        }),
        "imul" => {
            if right.is_empty() {
                let (register, width) = register(left)?;
                return Ok(Instruction::UnaryRegister {
                    operation: UnaryOperation::SignedMultiply,
                    width,
                    register,
                });
            }
            let (destination, width) = register(left)?;
            if let Some((source, source_width)) = parse_register(right) {
                if width != source_width {
                    return Err("imul register widths differ".into());
                }
                Ok(Instruction::MultiplyRegister {
                    destination,
                    source,
                    width,
                })
            } else {
                Ok(Instruction::MultiplyImmediate {
                    width,
                    destination,
                    value: parse_i32(right)?,
                })
            }
        }
        "shl" | "shr" | "sar" | "rcl" => {
            let (destination, width) = register(left)?;
            let operation = match mnemonic {
                "shl" => ShiftOperation::Left,
                "shr" => ShiftOperation::Right,
                "sar" => ShiftOperation::ArithmeticRight,
                _ => ShiftOperation::RotateCarryLeft,
            };
            if right == "cl" {
                Ok(Instruction::ShiftCl {
                    operation,
                    width,
                    destination,
                })
            } else {
                let count =
                    u8::try_from(parse_i32(right)?).map_err(|_| "shift count exceeds byte")?;
                Ok(Instruction::ShiftImmediate {
                    operation,
                    width,
                    destination,
                    count,
                })
            }
        }
        "shld" | "shrd" => {
            let (source, count) = right
                .split_once(',')
                .ok_or("double shift needs three operands")?;
            if count.trim() != "cl" {
                return Err("double shift count must be cl".into());
            }
            let (destination, width) = register(left)?;
            let (source, source_width) = register(source.trim())?;
            if width != source_width {
                return Err("double shift operand widths differ".into());
            }
            Ok(Instruction::DoubleShiftCl {
                left: mnemonic == "shld",
                width,
                destination,
                source,
            })
        }
        "bt" => {
            let (register, width) = register(left)?;
            Ok(Instruction::BitTest {
                width,
                register,
                bit: u8::try_from(parse_i32(right)?).map_err(|_| "bit index exceeds byte")?,
            })
        }
        "fld" | "fstp" => {
            if right.is_empty() && left == "st(0)" && mnemonic == "fstp" {
                return Ok(Instruction::FloatPop);
            }
            let (width, memory) = parse_memory(left)?.ok_or("x87 instruction requires memory")?;
            if mnemonic == "fld" {
                Ok(Instruction::FloatLoad { width, memory })
            } else {
                Ok(Instruction::FloatStorePop { width, memory })
            }
        }
        "fprem" if operands.is_empty() => Ok(Instruction::FloatRemainder),
        "fstsw" if operands == "ax" => Ok(Instruction::FloatStatusAx),
        "movzx" => {
            let (destination, width) = register(left)?;
            if let Some((source, source_width)) = parse_register(right) {
                Ok(Instruction::ZeroExtendByte {
                    destination,
                    destination_width: width,
                    source,
                    source_width,
                })
            } else if let Some((source_width, source)) = parse_memory(right)? {
                Ok(Instruction::ZeroExtendMemory {
                    destination,
                    destination_width: width,
                    source,
                    source_width,
                })
            } else {
                Err("movzx source must be a byte or word register/memory".into())
            }
        }
        "inc" | "dec" => {
            let decrement = mnemonic == "dec";
            if let Some((width, memory)) = parse_memory(left)? {
                Ok(Instruction::IncrementMemory {
                    memory,
                    width,
                    decrement,
                })
            } else {
                let (register, width) = register(left)?;
                Ok(Instruction::IncrementRegister {
                    register,
                    width,
                    decrement,
                })
            }
        }
        "movsxd" => {
            let (destination, destination_width) = register(left)?;
            if destination_width != Width::Qword {
                return Err("movsxd destination must be 64-bit".into());
            }
            if let Some((source, source_width)) = parse_register(right) {
                if source_width != Width::Dword {
                    return Err("movsxd source must be 32-bit".into());
                }
                Ok(Instruction::SignExtendDword {
                    destination,
                    source,
                })
            } else if let Some((source_width, source)) = parse_memory(right)? {
                if source_width != Width::Dword {
                    return Err("movsxd memory source must be DWORD PTR".into());
                }
                Ok(Instruction::SignExtendDwordMemory {
                    destination,
                    source,
                })
            } else {
                Err("movsxd source must be a register or memory".into())
            }
        }
        "movsx" => {
            let (destination, destination_width) = register(left)?;
            if let Some((source, source_width)) = parse_register(right) {
                Ok(Instruction::SignExtendSmall {
                    destination,
                    destination_width,
                    source,
                    source_width,
                })
            } else if let Some((source_width, source)) = parse_memory(right)? {
                Ok(Instruction::SignExtendSmallMemory {
                    destination,
                    destination_width,
                    source,
                    source_width,
                })
            } else {
                Err("movsx source must be a register or memory".into())
            }
        }
        "push" => {
            if let Some((width, memory)) = parse_memory(left)? {
                if width != Width::Qword {
                    return Err("push memory requires QWORD PTR".into());
                }
                Ok(Instruction::PushMemory(memory))
            } else {
                Ok(Instruction::Push(register(left)?.0))
            }
        }
        "pop" => {
            if let Some((width, memory)) = parse_memory(left)? {
                if width != Width::Qword {
                    return Err("pop memory requires QWORD PTR".into());
                }
                Ok(Instruction::PopMemory(memory))
            } else {
                Ok(Instruction::Pop(register(left)?.0))
            }
        }
        "call" => Ok(Instruction::Call(left.to_owned())),
        "jmp" => Ok(Instruction::Jump(left.to_owned())),
        "jz" | "je" => Ok(branch(Condition::Equal)),
        "jnz" | "jne" => Ok(branch(Condition::NotEqual)),
        "jb" => Ok(branch(Condition::Below)),
        "jbe" => Ok(branch(Condition::BelowOrEqual)),
        "ja" => Ok(branch(Condition::Above)),
        "jae" => Ok(branch(Condition::AboveOrEqual)),
        "jl" => Ok(branch(Condition::Less)),
        "jle" => Ok(branch(Condition::LessOrEqual)),
        "jg" => Ok(branch(Condition::Greater)),
        "jge" => Ok(branch(Condition::GreaterOrEqual)),
        "js" => Ok(branch(Condition::Sign)),
        "jns" => Ok(branch(Condition::NotSign)),
        "jp" => Ok(branch(Condition::Parity)),
        "jnp" => Ok(branch(Condition::NotParity)),
        "jc" => Ok(branch(Condition::Below)),
        "jnc" => Ok(branch(Condition::AboveOrEqual)),
        "jo" => Ok(branch(Condition::Overflow)),
        "jno" => Ok(branch(Condition::NotOverflow)),
        "setz" | "sete" => set(Condition::Equal),
        "setnz" | "setne" => set(Condition::NotEqual),
        "setb" => set(Condition::Below),
        "setbe" => set(Condition::BelowOrEqual),
        "seta" => set(Condition::Above),
        "setae" => set(Condition::AboveOrEqual),
        "setl" => set(Condition::Less),
        "setle" => set(Condition::LessOrEqual),
        "setg" => set(Condition::Greater),
        "setge" => set(Condition::GreaterOrEqual),
        "syscall" if operands.is_empty() => Ok(Instruction::Syscall),
        "lfence" if operands.is_empty() => Ok(Instruction::LoadFence),
        "mfence" if operands.is_empty() => Ok(Instruction::MemoryFence),
        "rdpkru" if operands.is_empty() => Ok(Instruction::ReadPkru),
        "ret" if operands.is_empty() => Ok(Instruction::Return),
        "leave" if operands.is_empty() => Ok(Instruction::Leave),
        "ud2" if operands.is_empty() => Ok(Instruction::Undefined),
        _ => Err(format!("unsupported instruction '{mnemonic}'")),
    }
}

fn parse_xmm_operand(text: &str) -> Result<XmmOperand, String> {
    if let Some(number) = text
        .strip_prefix("xmm")
        .and_then(|number| number.parse::<u8>().ok())
    {
        if number < 16 {
            return Ok(XmmOperand::Xmm(number));
        }
        return Err("XMM register number exceeds architectural limit".into());
    }
    if let Some((register, width)) = parse_register(text) {
        return Ok(XmmOperand::General(register, width));
    }
    if let Some((width, symbol, addend)) = parse_rip_memory(text)? {
        return Ok(XmmOperand::Rip {
            width: width.ok_or("SSE RIP operand requires a width")?,
            symbol,
            addend,
        });
    }
    if let Some((width, memory)) = parse_memory(text)? {
        return Ok(XmmOperand::Memory(memory, width));
    }
    Err(format!("unsupported SSE operand '{text}'"))
}

fn parse_register(name: &str) -> Option<(Register, Width)> {
    use Register::*;
    use Width::*;
    let known = [
        (Rax, "rax", "eax", "ax", "al"),
        (Rcx, "rcx", "ecx", "cx", "cl"),
        (Rdx, "rdx", "edx", "dx", "dl"),
        (Rbx, "rbx", "ebx", "bx", "bl"),
        (Rsp, "rsp", "esp", "sp", "spl"),
        (Rbp, "rbp", "ebp", "bp", "bpl"),
        (Rsi, "rsi", "esi", "si", "sil"),
        (Rdi, "rdi", "edi", "di", "dil"),
    ];
    for (register, q, d, w, b) in known {
        for (spelling, width) in [(q, Qword), (d, Dword), (w, Word), (b, Byte)] {
            if name == spelling {
                return Some((register, width));
            }
        }
    }
    for (index, register) in [R8, R9, R10, R11, R12, R13, R14, R15]
        .into_iter()
        .enumerate()
    {
        let base = format!("r{}", index + 8);
        for (suffix, width) in [("", Qword), ("d", Dword), ("w", Word), ("b", Byte)] {
            if name == format!("{base}{suffix}") {
                return Some((register, width));
            }
        }
    }
    None
}

fn parse_memory(operand: &str) -> Result<Option<(Width, Memory)>, String> {
    let (width, body) = if let Some((width, body)) = operand.split_once(" PTR [") {
        let width = match width {
            "BYTE" => Width::Byte,
            "WORD" => Width::Word,
            "DWORD" => Width::Dword,
            "QWORD" => Width::Qword,
            _ => return Err("unsupported memory width".into()),
        };
        (width, body)
    } else if let Some(body) = operand.strip_prefix('[') {
        (Width::Qword, body)
    } else {
        return Ok(None);
    };
    let body = body
        .strip_suffix(']')
        .ok_or("unterminated memory operand")?;
    let normalized = body.replace('-', "+-");
    let mut parts = normalized.split('+');
    let base = parts.next().ok_or("memory operand has no base")?;
    let (base, base_width) = parse_register(base).ok_or("unknown memory base register")?;
    if base_width != Width::Qword {
        return Err("memory base must be a 64-bit register".into());
    }
    let mut displacement = 0i32;
    let mut index = None;
    for part in parts {
        if part.is_empty() {
            return Err("empty memory address component".into());
        }
        if let Some((name, scale)) = part.split_once('*') {
            if index.is_some() {
                return Err("multiple memory index registers".into());
            }
            let (register, register_width) =
                parse_register(name).ok_or("unknown memory index register")?;
            if register_width != Width::Qword {
                return Err("memory index must be a 64-bit register".into());
            }
            let scale = scale
                .parse::<u8>()
                .map_err(|_| "invalid memory index scale")?;
            index = Some((register, scale));
        } else if let Some((register, register_width)) = parse_register(part) {
            if register_width != Width::Qword || index.is_some() {
                return Err("invalid memory index register".into());
            }
            index = Some((register, 1));
        } else {
            displacement = displacement
                .checked_add(parse_i32(part)?)
                .ok_or("memory displacement overflow")?;
        }
    }
    Ok(Some((
        width,
        Memory {
            base,
            index,
            displacement,
        },
    )))
}

fn parse_rip_memory(operand: &str) -> Result<Option<(Option<Width>, String, i64)>, String> {
    let (width, body) = if let Some((width, body)) = operand.split_once(" PTR [rip+") {
        let width = match width {
            "BYTE" => Width::Byte,
            "WORD" => Width::Word,
            "DWORD" => Width::Dword,
            "QWORD" => Width::Qword,
            _ => return Err("unsupported RIP memory width".into()),
        };
        (Some(width), body)
    } else if let Some(body) = operand.strip_prefix("[rip+") {
        (None, body)
    } else {
        return Ok(None);
    };
    let body = body
        .strip_suffix(']')
        .ok_or("unterminated RIP memory operand")?;
    let split = body.find(['+', '-']);
    let (symbol, addend) = split.map(|at| body.split_at(at)).unwrap_or((body, ""));
    if symbol.is_empty() || symbol.chars().any(char::is_whitespace) {
        return Err("invalid RIP symbol".into());
    }
    let addend = if addend.is_empty() {
        0
    } else {
        i64::from(parse_i32(addend)?)
    };
    Ok(Some((width, symbol.to_owned(), addend)))
}

fn parse_u64(text: &str) -> Result<u64, String> {
    if let Some(value) = text.strip_prefix("0x") {
        u64::from_str_radix(value, 16).map_err(|_| "invalid hex immediate".into())
    } else if let Some(value) = text.strip_prefix('-') {
        value
            .parse::<u64>()
            .ok()
            .filter(|value| *value <= 1u64 << 63)
            .map(|value| value.wrapping_neg())
            .ok_or_else(|| "invalid negative immediate".into())
    } else {
        text.parse().map_err(|_| "invalid immediate".into())
    }
}

fn parse_i32(text: &str) -> Result<i32, String> {
    if let Ok(value) = text.parse::<i32>() {
        return Ok(value);
    }
    let value = parse_u64(text).map_err(|_| "invalid displacement or immediate")?;
    let encoded = value as u32 as i32;
    if value == u64::from(value as u32) || value == encoded as i64 as u64 {
        Ok(encoded)
    } else {
        Err("immediate does not fit a sign-extended 32-bit operand".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assembles_a_checked_lim_function_and_keeps_symbol_identity() {
        let source = "(#fn main () u64 (#return 42u64))";
        let program = crate::parse_program(source).unwrap();
        let assembly = crate::generate_assembly(&program).unwrap();
        let assembled = assemble(&assembly).unwrap();
        assert!(assembled.symbols.contains_key("main"));
        assert!(assembled.unresolved.is_empty());
        assert!(!assembled.code.bytes.is_empty());
    }

    #[test]
    fn catches_unsupported_assembly_with_line_number() {
        let error = assemble(".intel_syntax noprefix\n.text\nmain:\n  vaddps ymm0, ymm1, ymm2\n")
            .err()
            .unwrap();
        assert!(error.contains("line 4"), "{error}");
        assert!(error.contains("vaddps"), "{error}");
    }

    #[test]
    fn recognizes_foreign_reference_without_extern_directive() {
        let result = assemble(".text\nmain:\n call abs\n ret\n").unwrap();
        assert_eq!(result.unresolved.len(), 1);
        assert_eq!(result.unresolved[0].symbol, "abs");
    }

    #[test]
    fn resolves_repeated_forward_and_backward_numeric_labels() {
        let source = ".text\nmain:\n jmp 1f\n1:\n jmp 1b\n jmp 1f\n1:\n ret\n";
        let result = assemble(source).unwrap();
        assert!(result.unresolved.is_empty());
        assert_eq!(
            result.code.bytes,
            [0xe9, 0, 0, 0, 0, 0xe9, 0xfb, 0xff, 0xff, 0xff, 0xe9, 0, 0, 0, 0, 0xc3]
        );
    }

    #[test]
    fn resolves_forward_set_definitions_and_offsets() {
        let source = ".set .Ltotal, .Lbase+4096+8\n.text\nmain:\n mov eax, OFFSET .Ltotal-4096\n ret\n.set .Lbase, 8192\n";
        let assembled = assemble(source).unwrap();
        assert_eq!(assembled.code.bytes, [0xb8, 8, 32, 0, 0, 0xc3]);
        assert!(assemble(".set a, b\n.set b, a\n.text\nmain:\n ret\n").is_err());
    }

    #[test]
    fn wide_shifts_bit_tests_and_x87_have_stable_machine_bytes() {
        let assembly = ".text\nmain:\n shld rdx, rax, cl\n shrd rax, rdx, cl\n bt rdx, 63\n fld QWORD PTR [rsp+8]\n fprem\n fstsw ax\n test ah, 4\n fstp QWORD PTR [rsp]\n fstp st(0)\n ret\n";
        let bytes = assemble(assembly).unwrap().code.bytes;
        assert_eq!(
            bytes,
            [
                0x48, 0x0f, 0xa5, 0xc2, 0x48, 0x0f, 0xad, 0xd0, 0x48, 0x0f, 0xba, 0xe2, 0x3f, 0xdd,
                0x44, 0x24, 0x08, 0xd9, 0xf8, 0xdf, 0xe0, 0xf6, 0xc4, 0x04, 0xdd, 0x1c, 0x24, 0xdd,
                0xd8, 0xc3,
            ]
        );
    }

    #[test]
    fn full_width_immediates_preserve_two_complement() {
        assert_eq!(parse_u64("-9223372036854775808").unwrap(), 1u64 << 63);
        assert_eq!(parse_i32("0x80000002").unwrap(), i32::MIN + 2);
        assert_eq!(parse_i32("18446744073709551615").unwrap(), -1);
        assert!(parse_i32("0x100000000").is_err());
        assert!(parse_u64("-9223372036854775809").is_err());
    }
}
