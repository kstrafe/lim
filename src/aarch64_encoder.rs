//! A64 instruction encoding. No assembler, host CPU, or text lowering is used.
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Label(pub usize);

#[derive(Clone, Copy, Debug)]
pub enum Condition {
    Eq = 0,
    Ne = 1,
    Hs = 2,
    Lo = 3,
    Hi = 8,
    Ls = 9,
    Ge = 10,
    Lt = 11,
    Gt = 12,
    Le = 13,
}

struct Fixup {
    at: usize,
    label: Label,
    condition: Option<Condition>,
    link: bool,
}

#[derive(Default)]
pub struct Encoder {
    pub words: Vec<u32>,
    pub descriptions: Vec<String>,
    labels: HashMap<Label, usize>,
    fixups: Vec<Fixup>,
    next_label: usize,
}

impl Encoder {
    pub fn label(&mut self) -> Label {
        let label = Label(self.next_label);
        self.next_label += 1;
        label
    }
    pub fn bind(&mut self, label: Label) -> Result<(), String> {
        if self.labels.insert(label, self.words.len()).is_some() {
            return Err("AArch64 label bound twice".into());
        }
        Ok(())
    }
    pub fn emit(&mut self, word: u32, description: impl Into<String>) {
        self.words.push(word);
        self.descriptions.push(description.into());
    }
    pub fn branch(&mut self, label: Label, condition: Option<Condition>, link: bool) {
        self.fixups.push(Fixup {
            at: self.words.len(),
            label,
            condition,
            link,
        });
        self.emit(0, format!("{} {:?}", if link { "bl" } else { "b" }, label));
    }
    pub fn finish(&mut self) -> Result<(), String> {
        for fixup in &self.fixups {
            let target = *self
                .labels
                .get(&fixup.label)
                .ok_or("unresolved AArch64 label")?;
            let delta = i64::try_from(target).map_err(|_| "AArch64 code size overflow")?
                - i64::try_from(fixup.at).map_err(|_| "AArch64 code size overflow")?;
            let bits = if fixup.condition.is_some() { 19 } else { 26 };
            if delta < -(1i64 << (bits - 1)) || delta >= (1i64 << (bits - 1)) {
                return Err("AArch64 branch displacement out of range".into());
            }
            self.words[fixup.at] = if let Some(condition) = fixup.condition {
                0x54000000 | (((delta as u32) & 0x7ffff) << 5) | condition as u32
            } else {
                (if fixup.link { 0x94000000 } else { 0x14000000 }) | ((delta as u32) & 0x3ffffff)
            };
        }
        Ok(())
    }
    pub fn constant(&mut self, rd: u8, value: u64) {
        assert!(rd < 31);
        self.emit(
            0xd2800000 | (((value as u32) & 0xffff) << 5) | rd as u32,
            format!("movz x{rd}, #{}", value & 0xffff),
        );
        for half in 1..4 {
            let part = ((value >> (half * 16)) & 0xffff) as u32;
            if part != 0 {
                self.emit(
                    0xf2800000 | (half << 21) | (part << 5) | rd as u32,
                    format!("movk x{rd}, #{part}, lsl #{}", half * 16),
                );
            }
        }
    }
    pub fn mov(&mut self, rd: u8, rn: u8) {
        assert!(rd < 31 && rn < 31);
        self.emit(
            0xaa0003e0 | ((rn as u32) << 16) | rd as u32,
            format!("mov x{rd}, x{rn}"),
        );
    }
    pub fn immediate(&mut self, sub: bool, rd: u8, rn: u8, amount: usize) {
        assert!(rd <= 31 && rn <= 31 && amount <= 4095);
        self.emit(
            (if sub { 0xd1000000 } else { 0x91000000 })
                | ((amount as u32) << 10)
                | ((rn as u32) << 5)
                | rd as u32,
            format!(
                "{} x{rd}, x{rn}, #{amount}",
                if sub { "sub" } else { "add" }
            ),
        );
    }
    pub fn stack_adjust(&mut self, sub: bool, mut bytes: usize) {
        assert!(bytes % 16 == 0);
        while bytes != 0 {
            let amount = bytes.min(4080);
            self.immediate(sub, 31, 31, amount);
            bytes -= amount;
        }
    }
    pub fn three(&mut self, opcode: u32, rd: u8, rn: u8, rm: u8, name: &str) {
        assert!(rd < 32 && rn < 32 && rm < 32);
        self.emit(
            opcode | ((rm as u32) << 16) | ((rn as u32) << 5) | rd as u32,
            format!("{name} x{rd}, x{rn}, x{rm}"),
        );
    }
    pub fn compare(&mut self, rn: u8, rm: u8) {
        self.three(0xeb000000, 31, rn, rm, "cmp");
    }
    pub fn cset(&mut self, rd: u8, condition: Condition) {
        self.emit(
            0x9a9f07e0 | (((condition as u32) ^ 1) << 12) | rd as u32,
            format!("cset x{rd}, {condition:?}"),
        );
    }
    pub fn normalize(&mut self, rd: u8, bits: usize, signed: bool) {
        if bits == 64 {
            return;
        }
        assert!((1..64).contains(&bits));
        self.emit(
            (if signed { 0x93400000 } else { 0xd3400000 })
                | (((bits - 1) as u32) << 10)
                | ((rd as u32) << 5)
                | rd as u32,
            format!(
                "{} x{rd}, x{rd}, #0, #{}",
                if signed { "sbfx" } else { "ubfx" },
                bits
            ),
        );
    }
    pub fn memory(&mut self, load: bool, rt: u8, rn: u8, bytes: usize) {
        assert!(rt < 32 && rn < 32 && bytes % 8 == 0 && bytes / 8 < 4096);
        self.emit(
            (if load { 0xf9400000 } else { 0xf9000000 })
                | (((bytes / 8) as u32) << 10)
                | ((rn as u32) << 5)
                | rt as u32,
            format!(
                "{} x{rt}, [x{rn}, #{bytes}]",
                if load { "ldr" } else { "str" }
            ),
        );
    }
    pub fn ret(&mut self) {
        self.emit(0xd65f03c0, "ret");
    }
    pub fn syscall(&mut self) {
        self.emit(0xd4000001, "svc #0");
    }
    pub fn trap(&mut self) {
        self.emit(0xd4200000, "brk #0");
    }
}
