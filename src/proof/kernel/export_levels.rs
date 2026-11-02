//! Paged exact universe values for source replay. The arithmetic has already
//! computed these representations; reads restore fields without recomputation
//! or normalization. No context-dependent typing judgment is stored here.
use super::{spool::Spool, Level, Result};
use std::{borrow::Cow, cell::RefCell, collections::VecDeque};

const MEMORY_BYTES: usize = 2 * 1024 * 1024;
const MAX_WEIGHT: usize = 64 * 1024;
const MAX_RECORD: usize = 64 * 1024;
const INDEX_BYTES: usize = 16;
const MAX_TERMS: usize = 256;
const MAX_GUARDS: usize = 64;
const RECENT_BYTES: usize = 256 * 1024;
const RECENT_ENTRIES: usize = 32;

pub(super) struct Levels(Storage);
enum Storage {
    Memory {
        values: Vec<Level>,
        bytes: usize,
        limit: usize,
    },
    Spilled(Spilled),
}
struct Spilled {
    index: RefCell<Spool>,
    data: RefCell<Spool>,
    count: usize,
    recent: Recent,
}
#[derive(Clone, Copy)]
struct Meta {
    offset: u64,
    len: usize,
    weight: usize,
}
#[derive(Default)]
struct Recent {
    values: VecDeque<(Level, Meta, usize)>,
    bytes: usize,
}
impl Recent {
    fn find(&mut self, level: &Level) -> Option<Meta> {
        let at = self
            .values
            .iter()
            .position(|(value, _, _)| value == level)?;
        let entry = self.values.remove(at)?;
        let meta = entry.1;
        self.values.push_back(entry);
        Some(meta)
    }
    fn remember(&mut self, level: &Level, meta: Meta) {
        let bytes = level
            .storage_memory_weight()
            .saturating_add(std::mem::size_of::<(Level, Meta, usize)>());
        if bytes > RECENT_BYTES {
            return;
        }
        while self.values.len() >= RECENT_ENTRIES || self.bytes.saturating_add(bytes) > RECENT_BYTES
        {
            if let Some((_, _, old)) = self.values.pop_front() {
                self.bytes -= old;
            } else {
                break;
            }
        }
        self.bytes += bytes;
        self.values.push_back((level.clone(), meta, bytes));
    }
}

impl Levels {
    pub(super) fn new() -> Self {
        Self::with_limit(MEMORY_BYTES)
    }
    pub(super) fn with_limit(limit: usize) -> Self {
        // Defer fallible scratch creation until the first actual input record.
        Self(Storage::Memory {
            values: vec![Level::number(0).expect("zero universe")],
            bytes: 0,
            limit,
        })
    }
    pub(super) fn len(&self) -> usize {
        match &self.0 {
            Storage::Memory { values, .. } => values.len(),
            Storage::Spilled(s) => s.count,
        }
    }
    pub(super) fn get(&self, id: usize) -> Result<Cow<'_, Level>> {
        match &self.0 {
            Storage::Memory { values, .. } => values
                .get(id)
                .map(Cow::Borrowed)
                .ok_or_else(reference_error),
            Storage::Spilled(s) => s.get(id).map(Cow::Owned),
        }
    }
    pub(super) fn weight(&self, id: usize) -> Result<usize> {
        match &self.0 {
            Storage::Memory { values, .. } => values
                .get(id)
                .map(Level::memory_weight)
                .ok_or_else(reference_error),
            Storage::Spilled(s) => Ok(s.meta(id)?.weight),
        }
    }
    pub(super) fn push(&mut self, level: Level) -> Result<()> {
        if level.memory_weight() > MAX_WEIGHT {
            return Err("export universe payload limit exceeded".into());
        }
        if let Storage::Memory {
            values,
            bytes,
            limit,
        } = &mut self.0
        {
            let owned = level.storage_memory_weight();
            let capacity = if values.len() == values.capacity() {
                values.capacity().saturating_mul(2).max(4)
            } else {
                values.capacity()
            };
            let projected = capacity
                .saturating_mul(std::mem::size_of::<Level>())
                .saturating_add(*bytes)
                .saturating_add(owned);
            if projected <= *limit {
                *bytes += owned;
                values.push(level);
                return Ok(());
            }
            let mut spilled = Spilled {
                index: RefCell::new(Spool::new()?),
                data: RefCell::new(Spool::new()?),
                count: 0,
                recent: Recent::default(),
            };
            for value in values.iter() {
                spilled.push(value)?;
            }
            self.0 = Storage::Spilled(spilled);
        }
        let Storage::Spilled(spilled) = &mut self.0 else {
            unreachable!()
        };
        spilled.push(&level)
    }
    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self.0, Storage::Spilled(_))
    }
}

#[cfg(test)]
impl TryFrom<Vec<Level>> for Levels {
    type Error = String;
    fn try_from(values: Vec<Level>) -> Result<Self> {
        let mut result = Self(Storage::Memory {
            values: vec![],
            bytes: 0,
            limit: MEMORY_BYTES,
        });
        for value in values {
            result.push(value)?;
        }
        Ok(result)
    }
}

impl Spilled {
    fn push(&mut self, level: &Level) -> Result<()> {
        if let Some(meta) = self.recent.find(level) {
            return self.push_index(meta);
        }
        let bytes = encode(level)?;
        if &decode(&bytes)? != level {
            return Err("universe scratch round-trip mismatch".into());
        }
        let offset = self.data.get_mut().append(&bytes)?;
        let meta = Meta {
            offset,
            len: bytes.len(),
            weight: level.memory_weight(),
        };
        self.push_index(meta)?;
        self.recent.remember(level, meta);
        Ok(())
    }
    fn push_index(&mut self, meta: Meta) -> Result<()> {
        let mut index = [0u8; INDEX_BYTES];
        index[..8].copy_from_slice(&meta.offset.to_le_bytes());
        index[8..12].copy_from_slice(&(meta.len as u32).to_le_bytes());
        index[12..].copy_from_slice(&(meta.weight as u32).to_le_bytes());
        let at = self.index.get_mut().append(&index)?;
        if at != self.count as u64 * INDEX_BYTES as u64 {
            return Err("universe scratch index is not contiguous".into());
        }
        self.count += 1;
        Ok(())
    }
    fn meta(&self, id: usize) -> Result<Meta> {
        if id >= self.count {
            return Err(reference_error());
        }
        let offset = (id as u64)
            .checked_mul(INDEX_BYTES as u64)
            .ok_or("universe scratch index overflow")?;
        let mut index = [0u8; INDEX_BYTES];
        self.index.borrow_mut().read_into(offset, &mut index)?;
        let offset = u64::from_le_bytes(index[..8].try_into().unwrap());
        let len = u32::from_le_bytes(index[8..12].try_into().unwrap()) as usize;
        let weight = u32::from_le_bytes(index[12..].try_into().unwrap()) as usize;
        if !(2..=MAX_RECORD).contains(&len)
            || weight > MAX_WEIGHT
            || offset
                .checked_add(len as u64)
                .is_none_or(|end| end > self.data.borrow().len())
        {
            return Err("invalid universe scratch index record".into());
        }
        Ok(Meta {
            offset,
            len,
            weight,
        })
    }
    fn get(&self, id: usize) -> Result<Level> {
        let meta = self.meta(id)?;
        let mut bytes = vec![0u8; meta.len];
        self.data.borrow_mut().read_into(meta.offset, &mut bytes)?;
        let level = decode(&bytes)?;
        if level.memory_weight() != meta.weight {
            return Err("universe scratch payload metadata mismatch".into());
        }
        Ok(level)
    }
}

fn encode(level: &Level) -> Result<Vec<u8>> {
    if level.memory_weight() > MAX_WEIGHT {
        return Err("export universe payload limit exceeded".into());
    }
    let parts = level.storage_parts();
    let mut bytes = Vec::with_capacity(level.memory_weight().min(MAX_RECORD) + 2);
    bytes.extend_from_slice(&(parts.len() as u16).to_le_bytes());
    fn text(bytes: &mut Vec<u8>, value: &str) -> Result<()> {
        let len =
            u16::try_from(value.len()).map_err(|_| "universe scratch string limit exceeded")?;
        bytes.extend_from_slice(&len.to_le_bytes());
        bytes.extend_from_slice(value.as_bytes());
        Ok(())
    }
    for (base, guards, offset) in parts {
        match base {
            None => bytes.push(0),
            Some(base) => {
                bytes.push(1);
                text(&mut bytes, &base)?;
            }
        }
        bytes.push(guards.len() as u8);
        for guard in guards {
            text(&mut bytes, &guard)?;
        }
        bytes.extend_from_slice(&offset.to_le_bytes());
    }
    if bytes.len() > MAX_RECORD {
        return Err("universe scratch record byte limit exceeded".into());
    }
    Ok(bytes)
}
struct Cursor<'a>(&'a [u8]);
impl<'a> Cursor<'a> {
    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        if len > self.0.len() {
            return Err("truncated universe scratch record".into());
        }
        let (value, rest) = self.0.split_at(len);
        self.0 = rest;
        Ok(value)
    }
    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    fn u16(&mut self) -> Result<u16> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn text(&mut self, weight: &mut usize) -> Result<String> {
        let len = self.u16()? as usize;
        account(weight, len)?;
        std::str::from_utf8(self.take(len)?)
            .map(str::to_owned)
            .map_err(|_| "invalid universe scratch UTF-8".into())
    }
}
fn account(weight: &mut usize, bytes: usize) -> Result<()> {
    *weight = weight
        .checked_add(bytes)
        .filter(|value| *value <= MAX_WEIGHT)
        .ok_or("export universe payload limit exceeded")?;
    Ok(())
}
fn decode(bytes: &[u8]) -> Result<Level> {
    if !(2..=MAX_RECORD).contains(&bytes.len()) {
        return Err("invalid universe scratch record length".into());
    }
    let mut cursor = Cursor(bytes);
    let count = cursor.u16()? as usize;
    if count > MAX_TERMS {
        return Err("universe scratch term count limit exceeded".into());
    }
    let mut parts = Vec::with_capacity(count);
    let mut weight = 0;
    for _ in 0..count {
        account(&mut weight, 96)?;
        let base = match cursor.byte()? {
            0 => None,
            1 => Some(cursor.text(&mut weight)?),
            _ => return Err("invalid universe scratch base tag".into()),
        };
        let count = cursor.byte()? as usize;
        if count > MAX_GUARDS {
            return Err("universe scratch guard count limit exceeded".into());
        }
        account(&mut weight, count * 64)?;
        let mut guards = Vec::with_capacity(count);
        for _ in 0..count {
            guards.push(cursor.text(&mut weight)?);
        }
        parts.push((base, guards, cursor.u32()?));
    }
    if !cursor.0.is_empty() {
        return Err("trailing universe scratch bytes".into());
    }
    let level = Level::from_storage_parts(parts)?;
    if level.memory_weight() != weight {
        return Err("universe scratch weight mismatch".into());
    }
    Ok(level)
}
fn reference_error() -> String {
    "universe reference must refer to an earlier record".into()
}

#[cfg(test)]
#[path = "export_levels_tests.rs"]
mod tests;
