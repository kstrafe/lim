//! x86-64 instruction bytes and relocations for the native backend.
//!
//! This module deals only with machine operands and bytes. Source syntax,
//! typing, ownership, and ELF layout belong to other compiler stages.

// The encoder is introduced before the native emission path is switched over.
#![allow(dead_code)]

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Width {
    Byte,
    Word,
    Dword,
    Qword,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Register {
    Rax,
    Rcx,
    Rdx,
    Rbx,
    Rsp,
    Rbp,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl Register {
    fn number(self) -> u8 {
        self as u8
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Memory {
    pub base: Register,
    pub index: Option<(Register, u8)>,
    pub displacement: i32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum XmmOperand {
    Xmm(u8),
    General(Register, Width),
    Memory(Memory, Width),
    Rip {
        width: Width,
        symbol: String,
        addend: i64,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum XmmOperation {
    MoveBits32,
    MoveBits64,
    MoveScalar32,
    MoveScalar64,
    MoveAligned32,
    MoveAligned64,
    Add32,
    Add64,
    Subtract32,
    Subtract64,
    Multiply32,
    Multiply64,
    Divide32,
    Divide64,
    Compare32,
    Compare64,
    ConvertInteger32,
    ConvertInteger64,
    Convert32To64,
    Truncate32ToInteger,
    Truncate64ToInteger,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BinaryOperation {
    Add,
    AddCarry,
    And,
    Or,
    Xor,
    Subtract,
    SubtractBorrow,
    Compare,
    Test,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UnaryOperation {
    Not,
    Negate,
    Multiply,
    SignedMultiply,
    Divide,
    SignedDivide,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AtomicOperation {
    CompareExchange,
    ExchangeAdd,
    Exchange,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ShiftOperation {
    Left,
    Right,
    ArithmeticRight,
    RotateCarryLeft,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Condition {
    Equal,
    NotEqual,
    Below,
    BelowOrEqual,
    Above,
    AboveOrEqual,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
    Sign,
    NotSign,
    Parity,
    NotParity,
    Overflow,
    NotOverflow,
}

impl Condition {
    fn code(self) -> u8 {
        match self {
            Self::Overflow => 0,
            Self::NotOverflow => 1,
            Self::Below => 2,
            Self::AboveOrEqual => 3,
            Self::Equal => 4,
            Self::NotEqual => 5,
            Self::BelowOrEqual => 6,
            Self::Above => 7,
            Self::Sign => 8,
            Self::NotSign => 9,
            Self::Parity => 10,
            Self::NotParity => 11,
            Self::Less => 12,
            Self::GreaterOrEqual => 13,
            Self::LessOrEqual => 14,
            Self::Greater => 15,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Instruction {
    Xmm {
        operation: XmmOperation,
        destination: XmmOperand,
        source: XmmOperand,
    },
    MovImmediate {
        width: Width,
        destination: Register,
        value: u64,
    },
    MovRegister {
        width: Width,
        destination: Register,
        source: Register,
    },
    Load {
        width: Width,
        destination: Register,
        source: Memory,
    },
    LoadRip {
        width: Width,
        destination: Register,
        symbol: String,
        addend: i64,
    },
    Store {
        width: Width,
        destination: Memory,
        source: Register,
    },
    StoreRip {
        width: Width,
        symbol: String,
        addend: i64,
        source: Register,
    },
    Lea {
        destination: Register,
        source: Memory,
    },
    LeaRip {
        destination: Register,
        symbol: String,
        addend: i64,
    },
    Xor {
        width: Width,
        destination: Register,
        source: Register,
    },
    BinaryRegister {
        operation: BinaryOperation,
        width: Width,
        destination: Register,
        source: Register,
    },
    BinaryMemoryRegister {
        operation: BinaryOperation,
        width: Width,
        memory: Memory,
        register: Register,
        memory_destination: bool,
    },
    AtomicMemoryRegister {
        operation: AtomicOperation,
        width: Width,
        memory: Memory,
        register: Register,
        locked: bool,
    },
    BinaryImmediate {
        operation: BinaryOperation,
        width: Width,
        destination: Register,
        value: i32,
    },
    StoreImmediate {
        width: Width,
        memory: Memory,
        value: i32,
    },
    UnaryRegister {
        operation: UnaryOperation,
        width: Width,
        register: Register,
    },
    SignExtendRax {
        width: Width,
    },
    BinaryMemoryImmediate {
        operation: BinaryOperation,
        width: Width,
        memory: Memory,
        value: i32,
    },
    MultiplyImmediate {
        width: Width,
        destination: Register,
        value: i32,
    },
    ShiftImmediate {
        operation: ShiftOperation,
        width: Width,
        destination: Register,
        count: u8,
    },
    ShiftCl {
        operation: ShiftOperation,
        width: Width,
        destination: Register,
    },
    DoubleShiftCl {
        left: bool,
        width: Width,
        destination: Register,
        source: Register,
    },
    BitTest {
        width: Width,
        register: Register,
        bit: u8,
    },
    FloatLoad {
        width: Width,
        memory: Memory,
    },
    FloatStorePop {
        width: Width,
        memory: Memory,
    },
    FloatRemainder,
    FloatStatusAx,
    FloatPop,
    TestAhImmediate(u8),
    SetCondition {
        condition: Condition,
        destination: Register,
    },
    JumpCondition {
        condition: Condition,
        symbol: String,
    },
    ZeroExtendByte {
        destination: Register,
        destination_width: Width,
        source: Register,
        source_width: Width,
    },
    ZeroExtendMemory {
        destination: Register,
        destination_width: Width,
        source: Memory,
        source_width: Width,
    },
    SignExtendDword {
        destination: Register,
        source: Register,
    },
    SignExtendDwordMemory {
        destination: Register,
        source: Memory,
    },
    SignExtendSmall {
        destination: Register,
        destination_width: Width,
        source: Register,
        source_width: Width,
    },
    SignExtendSmallMemory {
        destination: Register,
        destination_width: Width,
        source: Memory,
        source_width: Width,
    },
    LoadFence,
    MemoryFence,
    ReadPkru,
    IncrementRegister {
        register: Register,
        width: Width,
        decrement: bool,
    },
    IncrementMemory {
        memory: Memory,
        width: Width,
        decrement: bool,
    },
    MultiplyRegister {
        destination: Register,
        source: Register,
        width: Width,
    },
    Push(Register),
    Pop(Register),
    PushMemory(Memory),
    PopMemory(Memory),
    Call(String),
    Jump(String),
    Syscall,
    Return,
    Leave,
    Undefined,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RelocationKind {
    /// Signed displacement from the end of a four-byte branch operand.
    PcRelative32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Relocation {
    pub offset: usize,
    pub symbol: String,
    pub kind: RelocationKind,
    pub addend: i64,
}

#[derive(Default, Debug, Eq, PartialEq)]
pub(crate) struct EncodedInstructions {
    pub bytes: Vec<u8>,
    pub relocations: Vec<Relocation>,
}

impl EncodedInstructions {
    pub fn append(&mut self, instruction: &Instruction) -> Result<(), String> {
        use Instruction as I;
        match instruction {
            I::Xmm {
                operation,
                destination,
                source,
            } => self.xmm(*operation, destination, source)?,
            I::MovImmediate {
                width,
                destination,
                value,
            } => self.mov_immediate(*width, *destination, *value)?,
            I::MovRegister {
                width,
                destination,
                source,
            } => self.register_operands(*width, 0x88, 0x89, *source, *destination),
            I::Load {
                width,
                destination,
                source,
            } => self.memory_operand(*width, 0x8a, 0x8b, destination.number(), *source)?,
            I::LoadRip {
                width,
                destination,
                symbol,
                addend,
            } => {
                self.rip_operand(*width, 0x8a, 0x8b, *destination, symbol, *addend);
            }
            I::Store {
                width,
                destination,
                source,
            } => self.memory_operand(*width, 0x88, 0x89, source.number(), *destination)?,
            I::StoreRip {
                width,
                symbol,
                addend,
                source,
            } => {
                self.rip_operand(*width, 0x88, 0x89, *source, symbol, *addend);
            }
            I::Lea {
                destination,
                source,
            } => self.memory_operand(Width::Qword, 0, 0x8d, destination.number(), *source)?,
            I::LeaRip {
                destination,
                symbol,
                addend,
            } => {
                self.rip_operand(Width::Qword, 0, 0x8d, *destination, symbol, *addend);
            }
            I::Xor {
                width,
                destination,
                source,
            } => self.register_operands(*width, 0x30, 0x31, *source, *destination),
            I::BinaryRegister {
                operation,
                width,
                destination,
                source,
            } => self.binary_register(*operation, *width, *destination, *source),
            I::BinaryMemoryRegister {
                operation,
                width,
                memory,
                register,
                memory_destination,
            } => {
                let (byte_opcode, other_opcode) = match operation {
                    BinaryOperation::Add => (0x00, 0x01),
                    BinaryOperation::AddCarry => (0x10, 0x11),
                    BinaryOperation::And => (0x20, 0x21),
                    BinaryOperation::Or => (0x08, 0x09),
                    BinaryOperation::Xor => (0x30, 0x31),
                    BinaryOperation::Subtract => (0x28, 0x29),
                    BinaryOperation::SubtractBorrow => (0x18, 0x19),
                    BinaryOperation::Compare => (0x38, 0x39),
                    BinaryOperation::Test => (0x84, 0x85),
                };
                let offset = if *memory_destination || *operation == BinaryOperation::Test {
                    0
                } else {
                    2
                };
                self.memory_operand(
                    *width,
                    byte_opcode + offset,
                    other_opcode + offset,
                    register.number(),
                    *memory,
                )?;
            }
            I::AtomicMemoryRegister {
                operation,
                width,
                memory,
                register,
                locked,
            } => {
                if *operation == AtomicOperation::Exchange {
                    if *locked {
                        return Err("xchg already provides atomic memory exchange".into());
                    }
                    self.memory_operand(*width, 0x86, 0x87, register.number(), *memory)?;
                } else {
                    let (index, scale) = Self::memory_index(*memory)?;
                    if *width == Width::Word {
                        self.bytes.push(0x66);
                    }
                    if *locked {
                        self.bytes.push(0xf0);
                    }
                    let reg = register.number();
                    self.rex(
                        *width,
                        reg >= 8,
                        index >= 8,
                        memory.base.number() >= 8,
                        *width == Width::Byte && reg % 8 >= 4,
                    );
                    let opcode = match (operation, width) {
                        (AtomicOperation::CompareExchange, Width::Byte) => 0xb0,
                        (AtomicOperation::CompareExchange, _) => 0xb1,
                        (AtomicOperation::ExchangeAdd, Width::Byte) => 0xc0,
                        (AtomicOperation::ExchangeAdd, _) => 0xc1,
                        _ => unreachable!(),
                    };
                    self.bytes.extend_from_slice(&[0x0f, opcode]);
                    self.emit_memory_address(reg, *memory, index, scale);
                }
            }
            I::BinaryImmediate {
                operation,
                width,
                destination,
                value,
            } => self.binary_immediate(*operation, *width, *destination, *value)?,
            I::StoreImmediate {
                width,
                memory,
                value,
            } => {
                if *width == Width::Byte
                    && i8::try_from(*value).is_err()
                    && !(0..=255).contains(value)
                {
                    return Err("byte store immediate exceeds width".into());
                }
                if *width == Width::Word && i16::try_from(*value).is_err() {
                    return Err("word store immediate exceeds width".into());
                }
                self.memory_operand(*width, 0xc6, 0xc7, 0, *memory)?;
                match width {
                    Width::Byte => self.bytes.push(*value as u8),
                    Width::Word => self.bytes.extend_from_slice(&(*value as i16).to_le_bytes()),
                    Width::Dword | Width::Qword => {
                        self.bytes.extend_from_slice(&value.to_le_bytes())
                    }
                }
            }
            I::UnaryRegister {
                operation,
                width,
                register,
            } => {
                let group = match operation {
                    UnaryOperation::Not => 2,
                    UnaryOperation::Negate => 3,
                    UnaryOperation::Multiply => 4,
                    UnaryOperation::SignedMultiply => 5,
                    UnaryOperation::Divide => 6,
                    UnaryOperation::SignedDivide => 7,
                };
                if *width == Width::Word {
                    self.bytes.push(0x66);
                }
                let number = register.number();
                self.rex(
                    *width,
                    false,
                    false,
                    number >= 8,
                    *width == Width::Byte && number % 8 >= 4,
                );
                self.bytes
                    .push(if *width == Width::Byte { 0xf6 } else { 0xf7 });
                self.bytes.push(0xc0 | group << 3 | number % 8);
            }
            I::SignExtendRax { width } => {
                if *width == Width::Word {
                    self.bytes.push(0x66);
                }
                self.rex(*width, false, false, false, false);
                self.bytes.push(0x99);
            }
            I::BinaryMemoryImmediate {
                operation,
                width,
                memory,
                value,
            } => {
                if *width == Width::Byte
                    && i8::try_from(*value).is_err()
                    && !(0..=255).contains(value)
                {
                    return Err("byte memory immediate exceeds width".into());
                }
                if *width == Width::Word && i16::try_from(*value).is_err() {
                    return Err("word memory immediate exceeds width".into());
                }
                let group = match operation {
                    BinaryOperation::Add => 0,
                    BinaryOperation::Or => 1,
                    BinaryOperation::AddCarry => 2,
                    BinaryOperation::SubtractBorrow => 3,
                    BinaryOperation::And => 4,
                    BinaryOperation::Subtract => 5,
                    BinaryOperation::Xor => 6,
                    BinaryOperation::Compare => 7,
                    BinaryOperation::Test => {
                        return Err("memory test immediate requires a separate encoding".into())
                    }
                };
                let short = i8::try_from(*value).is_ok();
                let opcode = if *width == Width::Byte {
                    0x80
                } else if short {
                    0x83
                } else {
                    0x81
                };
                self.memory_operand(*width, opcode, opcode, group, *memory)?;
                if *width == Width::Byte || short {
                    self.bytes.push(*value as u8);
                } else if *width == Width::Word {
                    self.bytes.extend_from_slice(&(*value as i16).to_le_bytes());
                } else {
                    self.bytes.extend_from_slice(&value.to_le_bytes());
                }
            }
            I::MultiplyImmediate {
                width,
                destination,
                value,
            } => {
                if *width == Width::Byte {
                    return Err("imul immediate requires at least 16-bit operands".into());
                }
                if *width == Width::Word && i16::try_from(*value).is_err() {
                    return Err("word multiply immediate exceeds width".into());
                }
                if *width == Width::Word {
                    self.bytes.push(0x66);
                }
                let register = destination.number();
                self.rex(*width, register >= 8, false, register >= 8, false);
                let short = i8::try_from(*value).is_ok();
                self.bytes.push(if short { 0x6b } else { 0x69 });
                self.bytes.push(0xc0 | (register % 8) << 3 | register % 8);
                if short {
                    self.bytes.push(*value as u8);
                } else if *width == Width::Word {
                    self.bytes.extend_from_slice(&(*value as i16).to_le_bytes());
                } else {
                    self.bytes.extend_from_slice(&value.to_le_bytes());
                }
            }
            I::ShiftImmediate {
                operation,
                width,
                destination,
                count,
            } => {
                let group = match operation {
                    ShiftOperation::Left => 4,
                    ShiftOperation::Right => 5,
                    ShiftOperation::ArithmeticRight => 7,
                    ShiftOperation::RotateCarryLeft => 2,
                };
                if *width == Width::Word {
                    self.bytes.push(0x66);
                }
                let register = destination.number();
                self.rex(
                    *width,
                    false,
                    false,
                    register >= 8,
                    *width == Width::Byte && register % 8 >= 4,
                );
                self.bytes
                    .push(if *width == Width::Byte { 0xc0 } else { 0xc1 });
                self.bytes.push(0xc0 | group << 3 | register % 8);
                self.bytes.push(*count);
            }
            I::ShiftCl {
                operation,
                width,
                destination,
            } => {
                let group = match operation {
                    ShiftOperation::Left => 4,
                    ShiftOperation::Right => 5,
                    ShiftOperation::ArithmeticRight => 7,
                    ShiftOperation::RotateCarryLeft => 2,
                };
                if *width == Width::Word {
                    self.bytes.push(0x66);
                }
                let register = destination.number();
                self.rex(
                    *width,
                    false,
                    false,
                    register >= 8,
                    *width == Width::Byte && register % 8 >= 4,
                );
                self.bytes
                    .push(if *width == Width::Byte { 0xd2 } else { 0xd3 });
                self.bytes.push(0xc0 | group << 3 | register % 8);
            }
            I::DoubleShiftCl {
                left,
                width,
                destination,
                source,
            } => {
                if !matches!(width, Width::Dword | Width::Qword) {
                    return Err("double shift requires 32 or 64 bits".into());
                }
                let reg = source.number();
                let rm = destination.number();
                self.rex(*width, reg >= 8, false, rm >= 8, false);
                self.bytes.extend_from_slice(&[
                    0x0f,
                    if *left { 0xa5 } else { 0xad },
                    0xc0 | (reg % 8) << 3 | rm % 8,
                ]);
            }
            I::BitTest {
                width,
                register,
                bit,
            } => {
                if !matches!(width, Width::Dword | Width::Qword) {
                    return Err("bit test requires 32 or 64 bits".into());
                }
                let rm = register.number();
                self.rex(*width, false, false, rm >= 8, false);
                self.bytes
                    .extend_from_slice(&[0x0f, 0xba, 0xe0 | rm % 8, *bit]);
            }
            I::FloatLoad { width, memory } | I::FloatStorePop { width, memory } => {
                let store = matches!(instruction, I::FloatStorePop { .. });
                let (opcode, group) = match (width, store) {
                    (Width::Dword, false) => (0xd9, 0),
                    (Width::Qword, false) => (0xdd, 0),
                    (Width::Dword, true) => (0xd9, 3),
                    (Width::Qword, true) => (0xdd, 3),
                    _ => return Err("x87 memory must be DWORD or QWORD".into()),
                };
                let (index, scale) = Self::memory_index(*memory)?;
                self.rex(
                    Width::Dword,
                    false,
                    index >= 8,
                    memory.base.number() >= 8,
                    false,
                );
                self.bytes.push(opcode);
                self.emit_memory_address(group, *memory, index, scale);
            }
            I::FloatRemainder => self.bytes.extend_from_slice(&[0xd9, 0xf8]),
            I::FloatStatusAx => self.bytes.extend_from_slice(&[0xdf, 0xe0]),
            I::FloatPop => self.bytes.extend_from_slice(&[0xdd, 0xd8]),
            I::TestAhImmediate(value) => self.bytes.extend_from_slice(&[0xf6, 0xc4, *value]),
            I::SetCondition {
                condition,
                destination,
            } => {
                let number = destination.number();
                self.rex(Width::Byte, false, false, number >= 8, number % 8 >= 4);
                self.bytes
                    .extend_from_slice(&[0x0f, 0x90 + condition.code(), 0xc0 | number % 8]);
            }
            I::JumpCondition { condition, symbol } => {
                self.bytes
                    .extend_from_slice(&[0x0f, 0x80 + condition.code()]);
                self.relocation(symbol, 0);
            }
            I::ZeroExtendByte {
                destination,
                destination_width,
                source,
                source_width,
            } => {
                let reg = destination.number();
                let rm = source.number();
                if !matches!(destination_width, Width::Dword | Width::Qword) {
                    return Err("movzx destination must be 32 or 64 bits".into());
                }
                if !matches!(source_width, Width::Byte | Width::Word) {
                    return Err("movzx source must be byte or word".into());
                }
                self.rex(
                    *destination_width,
                    reg >= 8,
                    false,
                    rm >= 8,
                    *source_width == Width::Byte && rm % 8 >= 4,
                );
                self.bytes.extend_from_slice(&[
                    0x0f,
                    if *source_width == Width::Byte {
                        0xb6
                    } else {
                        0xb7
                    },
                    0xc0 | (reg % 8) << 3 | rm % 8,
                ]);
            }
            I::ZeroExtendMemory {
                destination,
                destination_width,
                source,
                source_width,
            } => {
                if !matches!(destination_width, Width::Dword | Width::Qword)
                    || !matches!(source_width, Width::Byte | Width::Word)
                {
                    return Err("movzx requires byte/word memory and dword/qword register".into());
                }
                let (index, scale) = Self::memory_index(*source)?;
                let reg = destination.number();
                self.rex(
                    *destination_width,
                    reg >= 8,
                    index >= 8,
                    source.base.number() >= 8,
                    false,
                );
                self.bytes.extend_from_slice(&[
                    0x0f,
                    if *source_width == Width::Byte {
                        0xb6
                    } else {
                        0xb7
                    },
                ]);
                self.emit_memory_address(reg, *source, index, scale);
            }
            I::SignExtendDword {
                destination,
                source,
            } => {
                let reg = destination.number();
                let rm = source.number();
                self.rex(Width::Qword, reg >= 8, false, rm >= 8, false);
                self.bytes
                    .extend_from_slice(&[0x63, 0xc0 | (reg % 8) << 3 | rm % 8]);
            }
            I::SignExtendDwordMemory {
                destination,
                source,
            } => {
                self.memory_operand(Width::Qword, 0x63, 0x63, destination.number(), *source)?;
            }
            I::SignExtendSmall {
                destination,
                destination_width,
                source,
                source_width,
            } => {
                if !matches!(source_width, Width::Byte | Width::Word)
                    || !matches!(destination_width, Width::Dword | Width::Qword)
                {
                    return Err("movsx requires byte/word input and dword/qword output".into());
                }
                let reg = destination.number();
                let rm = source.number();
                self.rex(
                    *destination_width,
                    reg >= 8,
                    false,
                    rm >= 8,
                    *source_width == Width::Byte && rm % 8 >= 4,
                );
                self.bytes.extend_from_slice(&[
                    0x0f,
                    if *source_width == Width::Byte {
                        0xbe
                    } else {
                        0xbf
                    },
                    0xc0 | (reg % 8) << 3 | rm % 8,
                ]);
            }
            I::SignExtendSmallMemory {
                destination,
                destination_width,
                source,
                source_width,
            } => {
                if !matches!(source_width, Width::Byte | Width::Word)
                    || !matches!(destination_width, Width::Dword | Width::Qword)
                {
                    return Err("movsx requires byte/word input and dword/qword output".into());
                }
                let (index, scale) = Self::memory_index(*source)?;
                let reg = destination.number();
                self.rex(
                    *destination_width,
                    reg >= 8,
                    index >= 8,
                    source.base.number() >= 8,
                    false,
                );
                self.bytes.extend_from_slice(&[
                    0x0f,
                    if *source_width == Width::Byte {
                        0xbe
                    } else {
                        0xbf
                    },
                ]);
                self.emit_memory_address(reg, *source, index, scale);
            }
            I::LoadFence => self.bytes.extend_from_slice(&[0x0f, 0xae, 0xe8]),
            I::MemoryFence => self.bytes.extend_from_slice(&[0x0f, 0xae, 0xf0]),
            I::ReadPkru => self.bytes.extend_from_slice(&[0x0f, 0x01, 0xee]),
            I::IncrementRegister {
                register,
                width,
                decrement,
            } => {
                if *width == Width::Word {
                    self.bytes.push(0x66);
                }
                let number = register.number();
                self.rex(
                    *width,
                    false,
                    false,
                    number >= 8,
                    *width == Width::Byte && number % 8 >= 4,
                );
                self.bytes
                    .push(if *width == Width::Byte { 0xfe } else { 0xff });
                self.bytes
                    .push(0xc0 | u8::from(*decrement) << 3 | number % 8);
            }
            I::IncrementMemory {
                memory,
                width,
                decrement,
            } => {
                self.memory_operand(*width, 0xfe, 0xff, u8::from(*decrement), *memory)?;
            }
            I::MultiplyRegister {
                destination,
                source,
                width,
            } => {
                if *width == Width::Byte {
                    return Err("two-operand imul requires at least 16 bits".into());
                }
                if *width == Width::Word {
                    self.bytes.push(0x66);
                }
                let reg = destination.number();
                let rm = source.number();
                self.rex(*width, reg >= 8, false, rm >= 8, false);
                self.bytes
                    .extend_from_slice(&[0x0f, 0xaf, 0xc0 | (reg % 8) << 3 | rm % 8]);
            }
            I::Push(register) => {
                if register.number() >= 8 {
                    self.bytes.push(0x41);
                }
                self.bytes.push(0x50 + register.number() % 8);
            }
            I::Pop(register) => {
                if register.number() >= 8 {
                    self.bytes.push(0x41);
                }
                self.bytes.push(0x58 + register.number() % 8);
            }
            I::PushMemory(memory) => self.memory_operand(Width::Dword, 0xff, 0xff, 6, *memory)?,
            I::PopMemory(memory) => self.memory_operand(Width::Dword, 0x8f, 0x8f, 0, *memory)?,
            I::Call(symbol) => self.branch(0xe8, symbol),
            I::Jump(symbol) => self.branch(0xe9, symbol),
            I::Syscall => self.bytes.extend_from_slice(&[0x0f, 0x05]),
            I::Return => self.bytes.push(0xc3),
            I::Leave => self.bytes.push(0xc9),
            I::Undefined => self.bytes.extend_from_slice(&[0x0f, 0x0b]),
        }
        Ok(())
    }

    fn branch(&mut self, opcode: u8, symbol: &str) {
        self.bytes.push(opcode);
        self.relocation(symbol, 0);
    }

    fn relocation(&mut self, symbol: &str, addend: i64) {
        self.relocations.push(Relocation {
            offset: self.bytes.len(),
            symbol: symbol.to_owned(),
            kind: RelocationKind::PcRelative32,
            addend,
        });
        self.bytes.extend_from_slice(&[0; 4]);
    }

    fn rip_operand(
        &mut self,
        width: Width,
        byte_opcode: u8,
        other_opcode: u8,
        reg: Register,
        symbol: &str,
        addend: i64,
    ) {
        if width == Width::Word {
            self.bytes.push(0x66);
        }
        let number = reg.number();
        self.rex(
            width,
            number >= 8,
            false,
            false,
            width == Width::Byte && number % 8 >= 4,
        );
        self.bytes.push(if width == Width::Byte {
            byte_opcode
        } else {
            other_opcode
        });
        self.bytes.push((number % 8) << 3 | 5);
        self.relocation(symbol, addend);
    }

    fn binary_register(
        &mut self,
        operation: BinaryOperation,
        width: Width,
        destination: Register,
        source: Register,
    ) {
        let opcode = match operation {
            BinaryOperation::Add => (0x00, 0x01),
            BinaryOperation::AddCarry => (0x10, 0x11),
            BinaryOperation::And => (0x20, 0x21),
            BinaryOperation::Or => (0x08, 0x09),
            BinaryOperation::Xor => (0x30, 0x31),
            BinaryOperation::Subtract => (0x28, 0x29),
            BinaryOperation::SubtractBorrow => (0x18, 0x19),
            BinaryOperation::Compare => (0x38, 0x39),
            BinaryOperation::Test => (0x84, 0x85),
        };
        self.register_operands(width, opcode.0, opcode.1, source, destination);
    }

    fn binary_immediate(
        &mut self,
        operation: BinaryOperation,
        width: Width,
        destination: Register,
        value: i32,
    ) -> Result<(), String> {
        let group = match operation {
            BinaryOperation::Add => 0,
            BinaryOperation::AddCarry => 2,
            BinaryOperation::Or => 1,
            BinaryOperation::And => 4,
            BinaryOperation::Xor => 6,
            BinaryOperation::Subtract => 5,
            BinaryOperation::SubtractBorrow => 3,
            BinaryOperation::Compare => 7,
            BinaryOperation::Test => {
                if width == Width::Byte
                    && i8::try_from(value).is_err()
                    && !(0..=255).contains(&value)
                {
                    return Err("byte test immediate exceeds width".into());
                }
                if width == Width::Word && i16::try_from(value).is_err() {
                    return Err("word test immediate exceeds width".into());
                }
                if width == Width::Word {
                    self.bytes.push(0x66);
                }
                let register = destination.number();
                self.rex(
                    width,
                    false,
                    false,
                    register >= 8,
                    width == Width::Byte && register % 8 >= 4,
                );
                self.bytes
                    .push(if width == Width::Byte { 0xf6 } else { 0xf7 });
                self.bytes.push(0xc0 | register % 8);
                if width == Width::Byte {
                    self.bytes.push(value as u8);
                } else if width == Width::Word {
                    self.bytes.extend_from_slice(&(value as i16).to_le_bytes());
                } else {
                    self.bytes.extend_from_slice(&value.to_le_bytes());
                }
                return Ok(());
            }
        };
        if width == Width::Word && i16::try_from(value).is_err() {
            return Err("word immediate exceeds width".into());
        }
        if width == Width::Byte && i8::try_from(value).is_err() && !(0..=255).contains(&value) {
            return Err("byte immediate exceeds width".into());
        }
        if width == Width::Word {
            self.bytes.push(0x66);
        }
        let register = destination.number();
        self.rex(
            width,
            false,
            false,
            register >= 8,
            width == Width::Byte && register % 8 >= 4,
        );
        let short = i8::try_from(value).is_ok();
        self.bytes.push(if width == Width::Byte {
            0x80
        } else if short {
            0x83
        } else {
            0x81
        });
        self.bytes.push(0xc0 | group << 3 | register % 8);
        if width == Width::Byte || short {
            self.bytes.push(value as u8);
        } else if width == Width::Word {
            self.bytes.extend_from_slice(&(value as i16).to_le_bytes());
        } else {
            self.bytes.extend_from_slice(&value.to_le_bytes());
        }
        Ok(())
    }

    fn mov_immediate(
        &mut self,
        width: Width,
        destination: Register,
        value: u64,
    ) -> Result<(), String> {
        let length = match width {
            Width::Byte if value <= u8::MAX as u64 => 1,
            Width::Word if value <= u16::MAX as u64 => 2,
            Width::Dword if value <= u32::MAX as u64 => 4,
            Width::Qword => 8,
            _ => return Err("immediate exceeds instruction width".into()),
        };
        if width == Width::Word {
            self.bytes.push(0x66);
        }
        let register = destination.number();
        self.rex(
            width,
            false,
            false,
            register >= 8,
            width == Width::Byte && register >= 4,
        );
        self.bytes
            .push(if width == Width::Byte { 0xb0 } else { 0xb8 } + register % 8);
        self.bytes.extend_from_slice(&value.to_le_bytes()[..length]);
        Ok(())
    }

    fn register_operands(
        &mut self,
        width: Width,
        byte_opcode: u8,
        other_opcode: u8,
        reg: Register,
        rm: Register,
    ) {
        if width == Width::Word {
            self.bytes.push(0x66);
        }
        let reg_number = reg.number();
        let rm_number = rm.number();
        let force_rex = width == Width::Byte && (reg_number % 8 >= 4 || rm_number % 8 >= 4);
        self.rex(width, reg_number >= 8, false, rm_number >= 8, force_rex);
        self.bytes.push(if width == Width::Byte {
            byte_opcode
        } else {
            other_opcode
        });
        self.bytes
            .push(0xc0 | (reg_number % 8) << 3 | rm_number % 8);
    }

    fn memory_operand(
        &mut self,
        width: Width,
        byte_opcode: u8,
        other_opcode: u8,
        reg_number: u8,
        memory: Memory,
    ) -> Result<(), String> {
        let (index_number, scale_bits) = Self::memory_index(memory)?;
        if width == Width::Word {
            self.bytes.push(0x66);
        }
        let base = memory.base.number();
        self.rex(
            width,
            reg_number >= 8,
            index_number >= 8,
            base >= 8,
            width == Width::Byte && reg_number % 8 >= 4,
        );
        self.bytes.push(if width == Width::Byte {
            byte_opcode
        } else {
            other_opcode
        });
        self.emit_memory_address(reg_number, memory, index_number, scale_bits);
        Ok(())
    }

    fn memory_index(memory: Memory) -> Result<(u8, u8), String> {
        Ok(match memory.index {
            None => (4, 0),
            Some((index, scale)) => {
                let scale_bits = match scale {
                    1 => 0,
                    2 => 1,
                    4 => 2,
                    8 => 3,
                    _ => return Err("memory index scale must be 1, 2, 4, or 8".into()),
                };
                if index.number() % 8 == 4 {
                    return Err("rsp/r12 cannot be a memory index".into());
                }
                (index.number(), scale_bits)
            }
        })
    }

    fn emit_memory_address(
        &mut self,
        reg_number: u8,
        memory: Memory,
        index_number: u8,
        scale_bits: u8,
    ) {
        let base = memory.base.number();
        let low_base = base % 8;
        let mode = if memory.displacement == 0 && low_base != 5 {
            0
        } else if i8::try_from(memory.displacement).is_ok() {
            1
        } else {
            2
        };
        let sib = memory.index.is_some() || low_base == 4;
        self.bytes
            .push(mode << 6 | (reg_number % 8) << 3 | if sib { 4 } else { low_base });
        if sib {
            self.bytes
                .push(scale_bits << 6 | (index_number % 8) << 3 | low_base);
        }
        match mode {
            1 => self.bytes.push(memory.displacement as i8 as u8),
            2 => self
                .bytes
                .extend_from_slice(&memory.displacement.to_le_bytes()),
            _ => {}
        }
    }

    fn xmm(
        &mut self,
        operation: XmmOperation,
        destination: &XmmOperand,
        source: &XmmOperand,
    ) -> Result<(), String> {
        use XmmOperand as O;
        use XmmOperation as Op;
        let (prefix, opcode, reg, rm, rex_w, width) = match operation {
            Op::MoveBits32 | Op::MoveBits64 => {
                let width = if operation == Op::MoveBits32 {
                    Width::Dword
                } else {
                    Width::Qword
                };
                match (destination, source) {
                    (O::Xmm(reg), rm @ (O::General(..) | O::Memory(..) | O::Rip { .. })) => (
                        Some(0x66),
                        0x6e,
                        *reg,
                        rm,
                        width == Width::Qword,
                        Some(width),
                    ),
                    (rm @ (O::General(..) | O::Memory(..) | O::Rip { .. }), O::Xmm(reg)) => (
                        Some(0x66),
                        0x7e,
                        *reg,
                        rm,
                        width == Width::Qword,
                        Some(width),
                    ),
                    _ => return Err("movd/movq needs one XMM register".into()),
                }
            }
            Op::MoveScalar32 | Op::MoveScalar64 => {
                let width = if operation == Op::MoveScalar32 {
                    Width::Dword
                } else {
                    Width::Qword
                };
                let prefix = Some(if width == Width::Dword { 0xf3 } else { 0xf2 });
                match (destination, source) {
                    (O::Xmm(reg), rm @ (O::Xmm(..) | O::Memory(..) | O::Rip { .. })) => {
                        (prefix, 0x10, *reg, rm, false, Some(width))
                    }
                    (O::Memory(..) | O::Rip { .. }, O::Xmm(reg)) => {
                        (prefix, 0x11, *reg, destination, false, Some(width))
                    }
                    _ => {
                        return Err(
                            "movss/movsd requires an XMM register and XMM or memory operand".into(),
                        )
                    }
                }
            }
            Op::MoveAligned32 | Op::MoveAligned64 => {
                let (O::Xmm(reg), O::Xmm(..)) = (destination, source) else {
                    return Err("aligned XMM move currently requires registers".into());
                };
                (
                    if operation == Op::MoveAligned64 {
                        Some(0x66)
                    } else {
                        None
                    },
                    0x28,
                    *reg,
                    source,
                    false,
                    None,
                )
            }
            Op::Add32
            | Op::Add64
            | Op::Subtract32
            | Op::Subtract64
            | Op::Multiply32
            | Op::Multiply64
            | Op::Divide32
            | Op::Divide64
            | Op::Compare32
            | Op::Compare64
            | Op::Convert32To64 => {
                let O::Xmm(reg) = destination else {
                    return Err("SSE destination must be XMM".into());
                };
                if !matches!(source, O::Xmm(..) | O::Memory(..) | O::Rip { .. }) {
                    return Err("SSE source must be XMM or memory".into());
                }
                let is_double = matches!(
                    operation,
                    Op::Add64 | Op::Subtract64 | Op::Multiply64 | Op::Divide64 | Op::Compare64
                );
                let width = if is_double {
                    Width::Qword
                } else {
                    Width::Dword
                };
                let prefix = if matches!(operation, Op::Compare32) {
                    None
                } else if matches!(operation, Op::Compare64) {
                    Some(0x66)
                } else if matches!(operation, Op::Convert32To64) {
                    Some(0xf3)
                } else {
                    Some(if is_double { 0xf2 } else { 0xf3 })
                };
                let opcode = match operation {
                    Op::Add32 | Op::Add64 => 0x58,
                    Op::Subtract32 | Op::Subtract64 => 0x5c,
                    Op::Multiply32 | Op::Multiply64 => 0x59,
                    Op::Divide32 | Op::Divide64 => 0x5e,
                    Op::Compare32 | Op::Compare64 => 0x2e,
                    Op::Convert32To64 => 0x5a,
                    _ => unreachable!(),
                };
                (prefix, opcode, *reg, source, false, Some(width))
            }
            Op::ConvertInteger32 | Op::ConvertInteger64 => {
                let O::Xmm(reg) = destination else {
                    return Err("float conversion destination must be XMM".into());
                };
                let source_width = match source {
                    O::General(_, width) | O::Memory(_, width) | O::Rip { width, .. } => *width,
                    _ => return Err("float conversion source must be integer".into()),
                };
                if !matches!(source_width, Width::Dword | Width::Qword) {
                    return Err("float conversion integer width must be 32 or 64".into());
                }
                (
                    Some(if operation == Op::ConvertInteger32 {
                        0xf3
                    } else {
                        0xf2
                    }),
                    0x2a,
                    *reg,
                    source,
                    source_width == Width::Qword,
                    Some(source_width),
                )
            }
            Op::Truncate32ToInteger | Op::Truncate64ToInteger => {
                let O::General(reg, destination_width) = destination else {
                    return Err("truncation destination must be general register".into());
                };
                if !matches!(source, O::Xmm(..) | O::Memory(..) | O::Rip { .. }) {
                    return Err("truncation source must be XMM or memory".into());
                }
                if !matches!(destination_width, Width::Dword | Width::Qword) {
                    return Err("truncation destination must be 32 or 64 bits".into());
                }
                let source_width = if operation == Op::Truncate32ToInteger {
                    Width::Dword
                } else {
                    Width::Qword
                };
                (
                    Some(if source_width == Width::Dword {
                        0xf3
                    } else {
                        0xf2
                    }),
                    0x2c,
                    reg.number(),
                    source,
                    *destination_width == Width::Qword,
                    Some(source_width),
                )
            }
        };
        if reg >= 16 {
            return Err("XMM register number exceeds architectural limit".into());
        }
        if let Some(expected) = width {
            match rm {
                O::General(_, actual) | O::Memory(_, actual) | O::Rip { width: actual, .. }
                    if *actual != expected =>
                {
                    return Err("SSE operand width mismatch".into())
                }
                _ => {}
            }
        }
        let (rm_number, memory, rip) = match rm {
            O::Xmm(number) if *number < 16 => (*number, None, None),
            O::General(register, _) => (register.number(), None, None),
            O::Memory(memory, _) => (0, Some(*memory), None),
            O::Rip { symbol, addend, .. } => (0, None, Some((symbol, *addend))),
            _ => return Err("invalid SSE source register".into()),
        };
        let index = if let Some(memory) = memory {
            Some(Self::memory_index(memory)?)
        } else {
            None
        };
        if let Some(prefix) = prefix {
            self.bytes.push(prefix);
        }
        self.rex(
            if rex_w { Width::Qword } else { Width::Dword },
            reg >= 8,
            index.is_some_and(|(number, _)| number >= 8),
            memory.is_some_and(|memory| memory.base.number() >= 8)
                || (memory.is_none() && rip.is_none() && rm_number >= 8),
            false,
        );
        self.bytes.extend_from_slice(&[0x0f, opcode]);
        if let Some(memory) = memory {
            let (index_number, scale_bits) = index.unwrap();
            self.emit_memory_address(reg, memory, index_number, scale_bits);
        } else if let Some((symbol, addend)) = rip {
            self.bytes.push((reg % 8) << 3 | 5);
            self.relocation(symbol, addend);
        } else {
            self.bytes.push(0xc0 | (reg % 8) << 3 | rm_number % 8);
        }
        Ok(())
    }

    fn rex(&mut self, width: Width, r: bool, x: bool, b: bool, force: bool) {
        let prefix = 0x40
            | u8::from(width == Width::Qword) << 3
            | u8::from(r) << 2
            | u8::from(x) << 1
            | u8::from(b);
        if prefix != 0x40 || force {
            self.bytes.push(prefix);
        }
    }

    /// Apply a relocation after all symbols have been assigned byte offsets.
    pub fn resolve_local(&mut self, relocation: usize, target: usize) -> Result<(), String> {
        let record = self
            .relocations
            .get(relocation)
            .ok_or("unknown relocation")?;
        let after = record
            .offset
            .checked_add(4)
            .ok_or("relocation offset overflow")?;
        let displacement = (target as i128) + (record.addend as i128) - (after as i128);
        let displacement =
            i32::try_from(displacement).map_err(|_| "branch displacement exceeds rel32 range")?;
        let bytes = self
            .bytes
            .get_mut(record.offset..after)
            .ok_or("relocation extends beyond code")?;
        bytes.copy_from_slice(&displacement.to_le_bytes());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registers_immediates_and_rex_prefixes() {
        let mut code = EncodedInstructions::default();
        code.append(&Instruction::MovImmediate {
            width: Width::Qword,
            destination: Register::R8,
            value: 0x1122334455667788,
        })
        .unwrap();
        code.append(&Instruction::MovRegister {
            width: Width::Dword,
            destination: Register::R9,
            source: Register::Rax,
        })
        .unwrap();
        code.append(&Instruction::Xor {
            width: Width::Byte,
            destination: Register::Rsi,
            source: Register::Rdi,
        })
        .unwrap();
        assert_eq!(
            code.bytes,
            [
                0x49, 0xb8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x41, 0x89, 0xc1, 0x40,
                0x30, 0xfe
            ]
        );
    }

    #[test]
    fn memory_addressing_handles_special_bases() {
        let mut code = EncodedInstructions::default();
        code.append(&Instruction::Load {
            width: Width::Qword,
            destination: Register::Rax,
            source: Memory {
                base: Register::Rbp,
                index: None,
                displacement: 0,
            },
        })
        .unwrap();
        code.append(&Instruction::Store {
            width: Width::Qword,
            destination: Memory {
                base: Register::R12,
                index: None,
                displacement: 127,
            },
            source: Register::R9,
        })
        .unwrap();
        code.append(&Instruction::Lea {
            destination: Register::R10,
            source: Memory {
                base: Register::Rsp,
                index: None,
                displacement: -256,
            },
        })
        .unwrap();
        assert_eq!(
            code.bytes,
            [
                0x48, 0x8b, 0x45, 0x00, 0x4d, 0x89, 0x4c, 0x24, 0x7f, 0x4c, 0x8d, 0x94, 0x24, 0x00,
                0xff, 0xff, 0xff
            ]
        );
    }

    #[test]
    fn local_relocations_are_checked() {
        let mut code = EncodedInstructions::default();
        code.append(&Instruction::Call("worker".into())).unwrap();
        code.append(&Instruction::Syscall).unwrap();
        code.append(&Instruction::Jump("exit".into())).unwrap();
        code.append(&Instruction::Return).unwrap();
        code.resolve_local(0, 13).unwrap();
        code.resolve_local(1, 0).unwrap();
        assert_eq!(
            code.bytes,
            [0xe8, 8, 0, 0, 0, 0x0f, 0x05, 0xe9, 0xf4, 0xff, 0xff, 0xff, 0xc3]
        );
        assert!(code.resolve_local(1, (i32::MAX as usize) + 20).is_err());
    }

    #[test]
    fn rejects_oversized_immediates() {
        let mut code = EncodedInstructions::default();
        assert!(code
            .append(&Instruction::MovImmediate {
                width: Width::Byte,
                destination: Register::Rax,
                value: 256
            })
            .is_err());
        assert!(code.bytes.is_empty());
    }
}
