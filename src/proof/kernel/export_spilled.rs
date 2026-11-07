//! Bounded source-node storage. The scratch index and data pages are checked
//! against digests held by this invocation; neither contains checked judgments.
use super::super::strings::MAX_STRING_BYTES;
use super::super::{scratch, spool::Spool};
use super::*;
use std::borrow::Cow;

const MEMORY_BYTES: usize = 2 * 1024 * 1024;
const INDEX_BYTES: usize = 32;
const MAX_RECORD: usize = 4160;

pub(super) enum Entries {
    Memory {
        values: Vec<Entry>,
        bytes: usize,
        limit: usize,
        scratch_limit: u64,
    },
    Spilled(Spilled),
}

#[derive(Clone, Copy)]
pub(super) struct Meta {
    pub depth: usize,
    pub payload: usize,
    pub canonical: usize,
}

pub(super) struct Spilled {
    index: RefCell<Spool>,
    data: RefCell<Spool>,
    count: usize,
}

impl Entries {
    pub(super) fn new() -> Self {
        Self::with_limit(MEMORY_BYTES)
    }
    pub(super) fn with_limit(limit: usize) -> Self {
        Self::with_config(limit, scratch::DEFAULT_BYTES)
    }
    pub(super) fn with_scratch_limit(scratch_limit: u64) -> Self {
        Self::with_config(MEMORY_BYTES, scratch_limit)
    }
    #[cfg(test)]
    pub(super) fn with_storage_limits(limit: usize, scratch_limit: u64) -> Self {
        Self::with_config(limit, scratch_limit)
    }
    fn with_config(limit: usize, scratch_limit: u64) -> Self {
        Self::Memory {
            values: Vec::new(),
            bytes: 0,
            limit,
            scratch_limit,
        }
    }
    pub(super) fn len(&self) -> usize {
        match self {
            Self::Memory { values, .. } => values.len(),
            Self::Spilled(s) => s.count,
        }
    }
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self, Self::Spilled(_))
    }
    pub(super) fn meta(&self, id: usize) -> Result<Meta> {
        match self {
            Self::Memory { values, .. } => {
                let entry = values.get(id).ok_or_else(reference_error)?;
                Ok(Meta {
                    depth: entry.depth,
                    payload: entry.payload,
                    canonical: if let Expression::Alias(c) = entry.expression {
                        c
                    } else {
                        id
                    },
                })
            }
            Self::Spilled(s) => s.meta(id).map(|(_, _, meta)| meta),
        }
    }
    pub(super) fn get(&self, id: usize) -> Result<Cow<'_, Entry>> {
        match self {
            Self::Memory { values, .. } => values
                .get(id)
                .map(Cow::Borrowed)
                .ok_or_else(reference_error),
            Self::Spilled(s) => {
                let (offset, len, meta) = s.meta(id)?;
                let mut bytes = [0; MAX_RECORD];
                s.data.borrow_mut().read_into(offset, &mut bytes[..len])?;
                let expression = decode(&bytes[..len], id)?;
                let canonical = if let Expression::Alias(c) = expression {
                    c
                } else {
                    id
                };
                if canonical != meta.canonical {
                    return Err("replay scratch canonical index mismatch".into());
                }
                Ok(Cow::Owned(Entry {
                    expression,
                    depth: meta.depth,
                    payload: meta.payload,
                }))
            }
        }
    }
    pub(super) fn push(&mut self, entry: Entry) -> Result<()> {
        if let Self::Memory {
            values,
            bytes,
            limit,
            scratch_limit,
            ..
        } = self
        {
            let owned = match &entry.expression {
                Expression::Global(_, arguments) => arguments
                    .capacity()
                    .saturating_mul(std::mem::size_of::<usize>()),
                Expression::Natural(value) => value.decimal().len(),
                Expression::String(value) => value.capacity(),
                _ => 0,
            };
            let capacity = if values.len() == values.capacity() {
                values.capacity().saturating_mul(2).max(4)
            } else {
                values.capacity()
            };
            let projected = capacity
                .saturating_mul(std::mem::size_of::<Entry>())
                .saturating_add(*bytes)
                .saturating_add(owned);
            if projected <= *limit {
                *bytes += owned;
                values.push(entry);
                return Ok(());
            }
            let mut spilled = Spilled {
                index: RefCell::new(if *scratch_limit == scratch::DEFAULT_BYTES {
                    Spool::new()?
                } else {
                    Spool::with_limit(*scratch_limit)?
                }),
                data: RefCell::new(if *scratch_limit == scratch::DEFAULT_BYTES {
                    Spool::new()?
                } else {
                    Spool::with_limit(*scratch_limit)?
                }),
                count: 0,
            };
            for value in values.iter() {
                spilled.push(value)?;
            }
            *self = Self::Spilled(spilled);
        }
        let Self::Spilled(spilled) = self else {
            unreachable!()
        };
        spilled.push(&entry)
    }
}

impl Spilled {
    fn push(&mut self, entry: &Entry) -> Result<()> {
        let bytes = encode(&entry.expression)?;
        let offset = self.data.get_mut().append(&bytes)?;
        let canonical = if let Expression::Alias(c) = entry.expression {
            c
        } else {
            self.count
        };
        let mut index = Vec::with_capacity(INDEX_BYTES);
        index.extend_from_slice(&offset.to_le_bytes());
        index.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
        index.extend_from_slice(&(entry.depth as u16).to_le_bytes());
        index.extend_from_slice(&0u16.to_le_bytes());
        index.extend_from_slice(&(entry.payload as u64).to_le_bytes());
        index.extend_from_slice(&(canonical as u64).to_le_bytes());
        let at = self.index.get_mut().append(&index)?;
        if at != self.count as u64 * INDEX_BYTES as u64 {
            return Err("replay scratch index is not contiguous".into());
        }
        self.count += 1;
        Ok(())
    }
    fn meta(&self, id: usize) -> Result<(u64, usize, Meta)> {
        if id >= self.count {
            return Err(reference_error());
        }
        let offset = (id as u64)
            .checked_mul(INDEX_BYTES as u64)
            .ok_or("replay scratch index overflow")?;
        let mut index = [0; INDEX_BYTES];
        self.index.borrow_mut().read_into(offset, &mut index)?;
        let mut cursor = Cursor(&index);
        let data_offset = cursor.u64()?;
        let len = cursor.u32()? as usize;
        let depth = cursor.u16()? as usize;
        let reserved = cursor.u16()?;
        let payload =
            usize::try_from(cursor.u64()?).map_err(|_| "replay scratch payload overflow")?;
        let canonical = usize::try_from(cursor.u64()?)
            .map_err(|_| "replay scratch canonical index overflow")?;
        if len == 0
            || len > MAX_RECORD
            || depth == 0
            || depth > MAX_EXPRESSION_DEPTH
            || reserved != 0
            || payload > 64 * 1024 * 1024
            || canonical > id
            || data_offset
                .checked_add(len as u64)
                .is_none_or(|end| end > self.data.borrow().len())
        {
            return Err("invalid replay scratch index record".into());
        }
        Ok((
            data_offset,
            len,
            Meta {
                depth,
                payload,
                canonical,
            },
        ))
    }
}

fn encode(node: &Expression) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(32);
    fn number(out: &mut Vec<u8>, value: usize) -> Result<()> {
        let value = u32::try_from(value).map_err(|_| "replay scratch source index exceeds u32")?;
        out.extend_from_slice(&value.to_le_bytes());
        Ok(())
    }
    macro_rules! numbers { ($tag:expr,$($value:expr),+) => {{ out.push($tag); $(number(&mut out,*$value)?;)+ }}; }
    match node {
        Expression::Var(a) => numbers!(0, a),
        Expression::Sort(a) => numbers!(1, a),
        Expression::Global(name, args) => {
            if args.len() > 32 {
                return Err("replay scratch universe arity limit exceeded".into());
            }
            out.push(2);
            number(&mut out, *name)?;
            out.push(args.len() as u8);
            for id in args {
                number(&mut out, *id)?;
            }
        }
        Expression::App(a, b) => numbers!(3, a, b),
        Expression::Lam(a, b) => numbers!(4, a, b),
        Expression::Pi(a, b) => numbers!(5, a, b),
        Expression::Let(a, b, c) => numbers!(6, a, b, c),
        Expression::Project(a, b, c) => numbers!(7, a, b, c),
        Expression::Natural(n) => {
            out.push(8);
            out.extend_from_slice(&(n.decimal().len() as u16).to_le_bytes());
            out.extend_from_slice(n.decimal().as_bytes());
        }
        Expression::Alias(a) => numbers!(9, a),
        Expression::String(value) => {
            if value.len() > MAX_STRING_BYTES {
                return Err("replay scratch string byte limit exceeded".into());
            }
            out.push(10);
            out.extend_from_slice(&(value.len() as u16).to_le_bytes());
            out.extend_from_slice(value.as_bytes());
        }
    }
    if out.len() > MAX_RECORD {
        return Err("replay scratch record byte limit exceeded".into());
    }
    Ok(out)
}

fn decode(bytes: &[u8], id: usize) -> Result<Expression> {
    let mut c = Cursor(bytes);
    let tag = c.take(1)?[0];
    fn child(c: &mut Cursor<'_>, id: usize) -> Result<usize> {
        let child = c.u32()? as usize;
        if child >= id {
            Err("replay scratch expression is not a backward reference".into())
        } else {
            Ok(child)
        }
    }
    let result = match tag {
        0 => Expression::Var(c.u32()? as usize),
        1 => Expression::Sort(c.u32()? as usize),
        2 => {
            let name = c.u32()? as usize;
            let count = c.take(1)?[0] as usize;
            if count > 32 {
                return Err("replay scratch universe arity limit exceeded".into());
            }
            let args = (0..count)
                .map(|_| c.u32().map(|id| id as usize))
                .collect::<Result<Vec<_>>>()?;
            Expression::Global(name, args)
        }
        3 => Expression::App(child(&mut c, id)?, child(&mut c, id)?),
        4 => Expression::Lam(child(&mut c, id)?, child(&mut c, id)?),
        5 => Expression::Pi(child(&mut c, id)?, child(&mut c, id)?),
        6 => Expression::Let(child(&mut c, id)?, child(&mut c, id)?, child(&mut c, id)?),
        7 => Expression::Project(c.u32()? as usize, c.u32()? as usize, child(&mut c, id)?),
        8 => {
            let count = c.u16()? as usize;
            let text = std::str::from_utf8(c.take(count)?)
                .map_err(|_| "replay scratch natural is not UTF-8")?;
            Expression::Natural(Natural::parse(text)?)
        }
        9 => Expression::Alias(child(&mut c, id)?),
        10 => {
            let count = c.u16()? as usize;
            if count > MAX_STRING_BYTES {
                return Err("replay scratch string byte limit exceeded".into());
            }
            let text = std::str::from_utf8(c.take(count)?)
                .map_err(|_| "replay scratch string is not UTF-8")?;
            Expression::String(text.to_owned())
        }
        _ => return Err("unknown replay scratch expression tag".into()),
    };
    if !c.0.is_empty() {
        return Err("trailing replay scratch expression bytes".into());
    }
    Ok(result)
}

struct Cursor<'a>(&'a [u8]);
impl<'a> Cursor<'a> {
    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        if len > self.0.len() {
            return Err("truncated replay scratch record".into());
        }
        let (bytes, rest) = self.0.split_at(len);
        self.0 = rest;
        Ok(bytes)
    }
    fn u16(&mut self) -> Result<u16> {
        Ok(u16::from_le_bytes(
            self.take(2)?
                .try_into()
                .map_err(|_| "truncated replay scratch u16")?,
        ))
    }
    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_le_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| "truncated replay scratch u32")?,
        ))
    }
    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_le_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| "truncated replay scratch u64")?,
        ))
    }
}

#[cfg(test)]
#[path = "export_spilled_tests.rs"]
mod tests;
