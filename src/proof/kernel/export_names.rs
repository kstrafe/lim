//! Bounded storage of the export's name syntax. Hashes index duplicate
//! candidates only; exact keys determine identity. No checked judgment lives
//! in this table. Scratch pages are protected by current-process digests.
use super::{spool::Spool, Name, Result};
use std::{borrow::Cow, cell::RefCell, collections::HashMap, hash::BuildHasher};

const MEMORY_BYTES: usize = 1024 * 1024;
const INDEX_BYTES: usize = 16;
const MAX_PART_BYTES: usize = 16_384;
const MAX_DEPTH: usize = 256;
const RECORD_HEADER: usize = 10;
const MAX_RECORD: usize = RECORD_HEADER + MAX_PART_BYTES * 2;

pub(super) struct Names {
    storage: Storage,
    keys: HashMap<u64, Ids>,
}
enum Ids {
    One(usize),
    Many(Vec<usize>),
}
impl Ids {
    fn as_slice(&self) -> &[usize] {
        match self {
            Self::One(id) => std::slice::from_ref(id),
            Self::Many(ids) => ids,
        }
    }
    fn push(&mut self, id: usize) {
        match self {
            Self::One(first) => *self = Self::Many(vec![*first, id]),
            Self::Many(ids) => ids.push(id),
        }
    }
}
enum Storage {
    Memory {
        values: Vec<Name>,
        bytes: usize,
        limit: usize,
    },
    Spilled(Spilled),
}
struct Spilled {
    index: RefCell<Spool>,
    data: RefCell<Spool>,
    count: usize,
}

impl Names {
    pub(super) fn new() -> Self {
        Self::with_limit(MEMORY_BYTES)
    }
    pub(super) fn with_limit(limit: usize) -> Self {
        // The anonymous root is built in memory, even for a zero test limit;
        // the first actual name record can migrate it with normal I/O errors.
        let root = Name {
            key: "$lean:".into(),
            display: String::new(),
            depth: 0,
        };
        let bytes = root.key.capacity();
        let mut keys = HashMap::new();
        keys.insert(keys.hasher().hash_one(root.key.as_str()), Ids::One(0));
        Self {
            keys,
            storage: Storage::Memory {
                values: vec![root],
                bytes,
                limit,
            },
        }
    }
    pub(super) fn len(&self) -> usize {
        match &self.storage {
            Storage::Memory { values, .. } => values.len(),
            Storage::Spilled(s) => s.count,
        }
    }
    pub(super) fn get(&self, id: usize) -> Result<Cow<'_, Name>> {
        match &self.storage {
            Storage::Memory { values, .. } => values
                .get(id)
                .map(Cow::Borrowed)
                .ok_or_else(reference_error),
            Storage::Spilled(s) => s.get(id).map(Cow::Owned),
        }
    }
    pub(super) fn by_key(&self, key: &str) -> Result<Option<Cow<'_, Name>>> {
        if let Some(ids) = self.keys.get(&self.fingerprint(key)) {
            for id in ids.as_slice() {
                let name = self.get(*id)?;
                if name.key == key {
                    return Ok(Some(name));
                }
            }
        }
        Ok(None)
    }
    fn fingerprint(&self, key: &str) -> u64 {
        // This index is never persisted and never establishes equality.
        // Use the map's randomized hasher; page integrity uses SHA-256.
        self.keys.hasher().hash_one(key)
    }
    pub(super) fn push(&mut self, name: Name) -> Result<()> {
        let hash = self.fingerprint(&name.key);
        self.push_with_hash(name, hash)
    }
    fn push_with_hash(&mut self, name: Name, hash: u64) -> Result<()> {
        validate(&name)?;
        if let Some(ids) = self.keys.get(&hash) {
            for id in ids.as_slice() {
                if self.get(*id)?.key == name.key {
                    return Err("duplicate interned export name".into());
                }
            }
        }
        let id = self.len();
        self.storage.push(name)?;
        self.keys
            .entry(hash)
            .and_modify(|ids| ids.push(id))
            .or_insert(Ids::One(id));
        Ok(())
    }
    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self.storage, Storage::Spilled(_))
    }
}

#[cfg(test)]
impl TryFrom<Vec<Name>> for Names {
    type Error = String;
    fn try_from(values: Vec<Name>) -> Result<Self> {
        let mut result = Self {
            storage: Storage::Memory {
                values: vec![],
                bytes: 0,
                limit: MEMORY_BYTES,
            },
            keys: HashMap::new(),
        };
        for name in values {
            result.push(name)?;
        }
        Ok(result)
    }
}

impl Storage {
    fn push(&mut self, name: Name) -> Result<()> {
        if let Self::Memory {
            values,
            bytes,
            limit,
        } = self
        {
            let owned = name.key.capacity().saturating_add(name.display.capacity());
            let capacity = if values.len() == values.capacity() {
                values.capacity().saturating_mul(2).max(4)
            } else {
                values.capacity()
            };
            let projected = capacity
                .saturating_mul(std::mem::size_of::<Name>())
                .saturating_add(*bytes)
                .saturating_add(owned);
            if projected <= *limit {
                *bytes += owned;
                values.push(name);
                return Ok(());
            }
            let mut spilled = Spilled {
                index: RefCell::new(Spool::new()?),
                data: RefCell::new(Spool::new()?),
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
        spilled.push(&name)
    }
}

impl Spilled {
    fn push(&mut self, name: &Name) -> Result<()> {
        let bytes = encode(name)?;
        // Compare complete fields independently before releasing source names.
        if &decode(&bytes)? != name {
            return Err("name scratch round-trip mismatch".into());
        }
        let offset = self.data.get_mut().append(&bytes)?;
        let mut index = [0u8; INDEX_BYTES];
        index[..8].copy_from_slice(&offset.to_le_bytes());
        index[8..12].copy_from_slice(&(bytes.len() as u32).to_le_bytes());
        let at = self.index.get_mut().append(&index)?;
        if at != self.count as u64 * INDEX_BYTES as u64 {
            return Err("name scratch index is not contiguous".into());
        }
        self.count += 1;
        Ok(())
    }
    fn get(&self, id: usize) -> Result<Name> {
        if id >= self.count {
            return Err(reference_error());
        }
        let offset = (id as u64)
            .checked_mul(INDEX_BYTES as u64)
            .ok_or("name scratch index overflow")?;
        let mut index = [0u8; INDEX_BYTES];
        self.index.borrow_mut().read_into(offset, &mut index)?;
        let offset = u64::from_le_bytes(index[..8].try_into().unwrap());
        let len = u32::from_le_bytes(index[8..12].try_into().unwrap()) as usize;
        if !(RECORD_HEADER..=MAX_RECORD).contains(&len)
            || index[12..].iter().any(|byte| *byte != 0)
            || offset
                .checked_add(len as u64)
                .is_none_or(|end| end > self.data.borrow().len())
        {
            return Err("invalid name scratch index record".into());
        }
        let mut bytes = vec![0u8; len];
        self.data.borrow_mut().read_into(offset, &mut bytes)?;
        decode(&bytes)
    }
}

fn validate(name: &Name) -> Result<()> {
    if name.depth > MAX_DEPTH
        || name.key.len() > MAX_PART_BYTES
        || name.display.len() > MAX_PART_BYTES
    {
        Err("export name size or depth limit exceeded".into())
    } else {
        Ok(())
    }
}
fn encode(name: &Name) -> Result<Vec<u8>> {
    validate(name)?;
    let mut bytes = Vec::with_capacity(RECORD_HEADER + name.key.len() + name.display.len());
    bytes.extend_from_slice(&(name.depth as u16).to_le_bytes());
    bytes.extend_from_slice(&(name.key.len() as u32).to_le_bytes());
    bytes.extend_from_slice(&(name.display.len() as u32).to_le_bytes());
    bytes.extend_from_slice(name.key.as_bytes());
    bytes.extend_from_slice(name.display.as_bytes());
    Ok(bytes)
}
fn decode(bytes: &[u8]) -> Result<Name> {
    if !(RECORD_HEADER..=MAX_RECORD).contains(&bytes.len()) {
        return Err("invalid name scratch record length".into());
    }
    let depth = u16::from_le_bytes(bytes[..2].try_into().unwrap()) as usize;
    let key_len = u32::from_le_bytes(bytes[2..6].try_into().unwrap()) as usize;
    let display_len = u32::from_le_bytes(bytes[6..10].try_into().unwrap()) as usize;
    if key_len > MAX_PART_BYTES
        || display_len > MAX_PART_BYTES
        || RECORD_HEADER + key_len + display_len != bytes.len()
    {
        return Err("invalid name scratch string lengths".into());
    }
    let key = std::str::from_utf8(&bytes[RECORD_HEADER..RECORD_HEADER + key_len])
        .map_err(|_| "invalid name scratch UTF-8")?
        .to_owned();
    let display = std::str::from_utf8(&bytes[RECORD_HEADER + key_len..])
        .map_err(|_| "invalid name scratch UTF-8")?
        .to_owned();
    let name = Name {
        key,
        display,
        depth,
    };
    validate(&name)?;
    Ok(name)
}
fn reference_error() -> String {
    "name reference must refer to an earlier record".into()
}

#[cfg(test)]
#[path = "export_names_tests.rs"]
mod tests;
