//! Exact mutable metadata for invocation-local checked declaration storage.
//! Only records written by this process are readable; hashes route lookups,
//! while complete keys and protected scratch bytes establish identity.
use super::super::scratch::DEFAULT_BYTES;
use super::{Blob, Result, Spool, MAX_BLOB_BYTES};
use std::{
    cell::{Cell, RefCell},
    collections::{hash_map::RandomState, HashMap, VecDeque},
    hash::BuildHasher,
};

const MEMORY_BYTES: usize = 1024 * 1024;
const BUCKETS: usize = 65_536;
const INDEX_BYTES: usize = 24;
const MAX_KEY: usize = 128 * 1024 * 1024 - 64;
const CACHE_BYTES: usize = 64 * 1024;
const CACHE_ENTRIES: usize = 32;

pub(super) struct Directory {
    storage: Storage,
    hasher: RandomState,
    limit: usize,
    scratch_limit: u64,
    live: usize,
    poisoned: Cell<bool>,
}
enum Storage {
    Memory {
        values: HashMap<Vec<u8>, Blob>,
        owned: usize,
    },
    Spilled(RefCell<Backed>),
}
struct Backed {
    heads: Vec<u32>,
    index: Spool,
    data: Spool,
    count: u32,
    recent: VecDeque<(u64, Vec<u8>, Option<Blob>)>,
    recent_bytes: usize,
}

impl Default for Directory {
    fn default() -> Self {
        Self::new()
    }
}
impl Directory {
    pub(super) fn new() -> Self {
        Self::with_limits(MEMORY_BYTES, DEFAULT_BYTES)
    }
    pub(super) fn with_scratch_limit(scratch_limit: u64) -> Self {
        Self::with_limits(MEMORY_BYTES, scratch_limit)
    }
    #[cfg(test)]
    pub(super) fn with_limit(limit: usize) -> Self {
        Self::with_limits(limit, DEFAULT_BYTES)
    }
    fn with_limits(limit: usize, scratch_limit: u64) -> Self {
        Self {
            storage: Storage::Memory {
                values: HashMap::new(),
                owned: 0,
            },
            hasher: RandomState::new(),
            limit,
            scratch_limit,
            live: 0,
            poisoned: Cell::new(false),
        }
    }
    #[cfg(test)]
    pub(super) fn set_limit(&mut self, limit: usize) {
        self.limit = limit;
    }
    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.live
    }
    #[cfg(test)]
    pub(super) fn is_spilled(&self) -> bool {
        matches!(self.storage, Storage::Spilled(_))
    }
    #[cfg(test)]
    pub(super) fn corrupt_flushed_record(&mut self, key: &[u8]) -> Result<()> {
        let hash = self.hasher.hash_one(key);
        let Storage::Spilled(backed) = &mut self.storage else {
            return Err("declaration directory is not spilled".into());
        };
        let backed = backed.get_mut();
        backed.recent.clear();
        backed.recent_bytes = 0;
        let mut node = backed.heads[hash as usize & (BUCKETS - 1)];
        while node != 0 {
            let mut index = [0; INDEX_BYTES];
            backed
                .index
                .read_into((node as u64 - 1) * INDEX_BYTES as u64, &mut index)?;
            let candidate = u64::from_le_bytes(index[..8].try_into().unwrap());
            let offset = u64::from_le_bytes(index[8..16].try_into().unwrap());
            let len = u32::from_le_bytes(index[16..20].try_into().unwrap()) as usize;
            let next = u32::from_le_bytes(index[20..].try_into().unwrap());
            if candidate == hash && backed.read(offset, len, key)?.is_some() {
                backed.data.overwrite_flushed(offset + 4, &[b'!'])?;
                backed.recent.clear();
                backed.recent_bytes = 0;
                return Ok(());
            }
            node = next;
        }
        Err("declaration directory test key not found".into())
    }
    pub(super) fn healthy(&self) -> Result<()> {
        if self.poisoned.get() {
            Err("kernel declaration directory is invalid after a storage error".into())
        } else {
            Ok(())
        }
    }
    pub(super) fn get(&self, key: &[u8]) -> Result<Option<Blob>> {
        self.healthy()?;
        if key.len() > MAX_KEY {
            return Err("kernel declaration directory key limit exceeded".into());
        }
        if self.live == 0 {
            return Ok(None);
        }
        let result = match &self.storage {
            Storage::Memory { values, .. } => Ok(values.get(key).copied()),
            Storage::Spilled(backed) => backed.borrow_mut().get(self.hasher.hash_one(key), key),
        };
        if result.is_err() {
            self.poisoned.set(true);
        }
        result
    }
    pub(super) fn set(&mut self, key: &[u8], value: Option<Blob>) -> Result<()> {
        self.healthy()?;
        if key.len() > MAX_KEY {
            return Err("kernel declaration directory key limit exceeded".into());
        }
        if let Some(value) = value {
            validate_blob(value)?;
        }
        let old = self.get(key)?;
        if old == value {
            return Ok(());
        }
        let result = self.write(key, value);
        if result.is_err() {
            self.poisoned.set(true);
            return result;
        }
        match (old.is_some(), value.is_some()) {
            (false, true) => {
                self.live = self
                    .live
                    .checked_add(1)
                    .ok_or("declaration directory count overflow")?
            }
            (true, false) => {
                self.live = self
                    .live
                    .checked_sub(1)
                    .ok_or("declaration directory count underflow")?
            }
            _ => {}
        }
        Ok(())
    }
    fn write(&mut self, key: &[u8], value: Option<Blob>) -> Result<()> {
        match &mut self.storage {
            Storage::Spilled(backed) => backed.get_mut().put(self.hasher.hash_one(key), key, value),
            Storage::Memory { values, owned } => {
                if let Some(value) = value {
                    if let Some(previous) = values.get_mut(key) {
                        *previous = value;
                    } else {
                        let key = key.to_vec();
                        *owned += key.capacity();
                        values.insert(key, value);
                    }
                } else if let Some((key, _)) = values.remove_entry(key) {
                    *owned -= key.capacity();
                }
                if values.is_empty() {
                    values.shrink_to_fit();
                    return Ok(());
                }
                let weight = values
                    .capacity()
                    .saturating_mul(std::mem::size_of::<(Vec<u8>, Blob)>() + 1)
                    .saturating_mul(2)
                    .saturating_add(*owned);
                if weight <= self.limit {
                    return Ok(());
                }
                let mut backed = Backed::new(self.scratch_limit)?;
                for (key, value) in values.iter() {
                    backed.put(self.hasher.hash_one(key.as_slice()), key, Some(*value))?;
                }
                self.storage = Storage::Spilled(RefCell::new(backed));
                Ok(())
            }
        }
    }
}

fn validate_blob(blob: Blob) -> Result<()> {
    if blob.bytes == 0
        || blob.bytes > MAX_BLOB_BYTES
        || blob.offset.checked_add(blob.bytes as u64).is_none()
    {
        Err("invalid kernel declaration directory blob".into())
    } else {
        Ok(())
    }
}

impl Backed {
    fn new(scratch_limit: u64) -> Result<Self> {
        Ok(Self {
            heads: vec![0; BUCKETS],
            index: Spool::with_limit(scratch_limit)?,
            data: Spool::with_limit(scratch_limit)?,
            count: 0,
            recent: VecDeque::new(),
            recent_bytes: 0,
        })
    }
    fn remember(&mut self, hash: u64, key: &[u8], value: Option<Blob>) {
        let fixed = std::mem::size_of::<(u64, Vec<u8>, Option<Blob>)>();
        if let Some(at) = self
            .recent
            .iter()
            .position(|(h, k, _)| *h == hash && k == key)
        {
            let (_, old, _) = self.recent.remove(at).unwrap();
            self.recent_bytes -= old.capacity() + fixed;
        }
        let weight = key.len().saturating_add(fixed);
        if weight > CACHE_BYTES {
            return;
        }
        while self.recent.len() >= CACHE_ENTRIES
            || self.recent_bytes.saturating_add(weight) > CACHE_BYTES
        {
            let Some((_, old, _)) = self.recent.pop_front() else {
                break;
            };
            self.recent_bytes -= old.capacity() + fixed;
        }
        let key = key.to_vec();
        self.recent_bytes += key.capacity() + fixed;
        self.recent.push_back((hash, key, value));
    }
    fn put(&mut self, hash: u64, key: &[u8], value: Option<Blob>) -> Result<()> {
        let node = self
            .count
            .checked_add(1)
            .ok_or("declaration directory index count overflow")?;
        let bucket = hash as usize & (BUCKETS - 1);
        let next = self.heads[bucket];
        let len = key
            .len()
            .checked_add(if value.is_some() { 53 } else { 5 })
            .ok_or("directory record overflow")?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(len)
            .map_err(|_| "directory record allocation failed")?;
        let key_len = u32::try_from(key.len()).map_err(|_| "directory key length overflow")?;
        bytes.extend_from_slice(&key_len.to_le_bytes());
        bytes.extend_from_slice(key);
        bytes.push(u8::from(value.is_some()));
        if let Some(value) = value {
            validate_blob(value)?;
            bytes.extend_from_slice(&value.offset.to_le_bytes());
            bytes.extend_from_slice(&(value.bytes as u64).to_le_bytes());
            bytes.extend_from_slice(&value.digest);
        }
        let offset = self.data.append(&bytes)?;
        if self.read(offset, len, key)? != Some(value) {
            return Err("declaration directory round-trip mismatch".into());
        }
        let mut index = [0; INDEX_BYTES];
        index[..8].copy_from_slice(&hash.to_le_bytes());
        index[8..16].copy_from_slice(&offset.to_le_bytes());
        index[16..20].copy_from_slice(&(len as u32).to_le_bytes());
        index[20..].copy_from_slice(&next.to_le_bytes());
        let expected = self.count as u64 * INDEX_BYTES as u64;
        if self.index.append(&index)? != expected {
            return Err("declaration directory index is not contiguous".into());
        }
        let mut restored = [0; INDEX_BYTES];
        self.index.read_into(expected, &mut restored)?;
        if restored != index {
            return Err("declaration directory index round-trip mismatch".into());
        }
        self.heads[bucket] = node;
        self.count = node;
        self.remember(hash, key, value);
        Ok(())
    }
    fn get(&mut self, hash: u64, key: &[u8]) -> Result<Option<Blob>> {
        if self.index.len() != self.count as u64 * INDEX_BYTES as u64 {
            return Err("declaration directory index count mismatch".into());
        }
        if let Some(at) = self
            .recent
            .iter()
            .position(|(h, k, _)| *h == hash && k == key)
        {
            let entry = self.recent.remove(at).unwrap();
            let value = entry.2;
            self.recent.push_back(entry);
            return Ok(value);
        }
        let bucket = hash as usize & (BUCKETS - 1);
        let mut node = self.heads[bucket];
        while node != 0 {
            if node > self.count {
                return Err("invalid declaration directory link".into());
            }
            let mut bytes = [0; INDEX_BYTES];
            self.index
                .read_into((node as u64 - 1) * INDEX_BYTES as u64, &mut bytes)?;
            let candidate = u64::from_le_bytes(bytes[..8].try_into().unwrap());
            let offset = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
            let len = u32::from_le_bytes(bytes[16..20].try_into().unwrap()) as usize;
            let next = u32::from_le_bytes(bytes[20..].try_into().unwrap());
            if next >= node || candidate as usize & (BUCKETS - 1) != bucket {
                return Err("invalid declaration directory index record".into());
            }
            if candidate == hash {
                if let Some(value) = self.read(offset, len, key)? {
                    self.remember(hash, key, value);
                    return Ok(value);
                }
            }
            node = next;
        }
        self.remember(hash, key, None);
        Ok(None)
    }
    fn read(&mut self, offset: u64, len: usize, key: &[u8]) -> Result<Option<Option<Blob>>> {
        if len < 5
            || len > MAX_KEY + 53
            || offset
                .checked_add(len as u64)
                .is_none_or(|end| end > self.data.len())
        {
            return Err("invalid declaration directory data range".into());
        }
        let mut size = [0; 4];
        self.data.read_into(offset, &mut size)?;
        let key_len = u32::from_le_bytes(size) as usize;
        if key_len > MAX_KEY || key_len.checked_add(5).is_none_or(|n| n > len) {
            return Err("invalid declaration directory key length".into());
        }
        if key_len != key.len() {
            return Ok(None);
        }
        let mut buffer = [0; 512];
        for (i, part) in key.chunks(buffer.len()).enumerate() {
            self.data
                .read_into(offset + 4 + (i * 512) as u64, &mut buffer[..part.len()])?;
            if &buffer[..part.len()] != part {
                return Ok(None);
            }
        }
        let value_at = offset + 4 + key_len as u64;
        let mut tag = [0];
        self.data.read_into(value_at, &mut tag)?;
        match tag[0] {
            0 if len == key_len + 5 => Ok(Some(None)),
            1 if len == key_len + 53 => {
                let mut payload = [0; 48];
                self.data.read_into(value_at + 1, &mut payload)?;
                let bytes = usize::try_from(u64::from_le_bytes(payload[8..16].try_into().unwrap()))
                    .map_err(|_| "directory blob length overflow")?;
                let blob = Blob {
                    offset: u64::from_le_bytes(payload[..8].try_into().unwrap()),
                    bytes,
                    digest: payload[16..].try_into().unwrap(),
                };
                validate_blob(blob)?;
                Ok(Some(Some(blob)))
            }
            _ => Err("invalid declaration directory value record".into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn blob(n: u8) -> Blob {
        Blob {
            offset: n as u64,
            bytes: 1,
            digest: [n; 32],
        }
    }
    #[test]
    fn cold_latest_values_tombstones_and_reinsertion_do_not_resurrect_old_values() {
        let mut d = Directory::with_limit(0);
        d.set(b"name", Some(blob(1))).unwrap();
        assert!(d.is_spilled());
        assert_eq!(d.get(b"name").unwrap(), Some(blob(1)));
        d.set(b"name", Some(blob(2))).unwrap();
        d.set(b"other", Some(blob(3))).unwrap();
        d.set(b"name", None).unwrap();
        assert_eq!(d.get(b"name").unwrap(), None);
        d.set(b"name", Some(blob(4))).unwrap();
        assert_eq!(d.get(b"name").unwrap(), Some(blob(4)));
        assert_eq!(d.len(), 2);
        let Storage::Spilled(backed) = &mut d.storage else {
            unreachable!()
        };
        backed.get_mut().recent.clear();
        backed.get_mut().recent_bytes = 0;
        assert_eq!(d.get(b"name").unwrap(), Some(blob(4)));
    }
    #[test]
    fn full_hash_collisions_and_shared_bucket_hashes_keep_exact_byte_identity() {
        let mut b = Backed::new(DEFAULT_BYTES).unwrap();
        b.put(7, b"alpha", Some(blob(1))).unwrap();
        b.put(7, b"beta", Some(blob(2))).unwrap();
        b.put(7 + BUCKETS as u64, b"gamma", Some(blob(3))).unwrap();
        b.put(7, b"alpha", None).unwrap();
        b.recent.clear();
        b.recent_bytes = 0;
        assert_eq!(b.get(7, b"alpha").unwrap(), None);
        assert_eq!(b.get(7, b"beta").unwrap(), Some(blob(2)));
        assert_eq!(b.get(7, b"gamma").unwrap(), None);
        assert_eq!(b.get(7 + BUCKETS as u64, b"gamma").unwrap(), Some(blob(3)));
    }
    #[test]
    fn migration_and_long_binary_unicode_keys_preserve_values() {
        let keys = [
            "命題.λ".as_bytes().to_vec(),
            vec![0; 513],
            vec![255; 70_000],
        ];
        let mut d = Directory::with_limit(60_000);
        for (i, key) in keys.iter().enumerate() {
            d.set(key, Some(blob(i as u8))).unwrap();
        }
        assert!(d.is_spilled());
        for (i, key) in keys.iter().enumerate() {
            assert_eq!(d.get(key).unwrap(), Some(blob(i as u8)));
        }
    }
    #[test]
    fn untrusted_page_changes_fail_closed_and_poison_even_missing_lookups() {
        let mut d = Directory::with_limit(0);
        let key = vec![b'a'; 70_000];
        d.set(&key, Some(blob(1))).unwrap();
        let Storage::Spilled(backed) = &mut d.storage else {
            unreachable!()
        };
        let b = backed.get_mut();
        b.recent.clear();
        b.recent_bytes = 0;
        b.data.overwrite_flushed(9, &[b'b']).unwrap();
        assert!(d.get(&key).unwrap_err().contains("checksum"));
        assert!(d.get(b"absent").unwrap_err().contains("invalid after"));
        assert!(d.set(b"new", Some(blob(3))).is_err());
    }
    #[test]
    fn default_threshold_bounds_name_and_digest_directory_resident_capacity() {
        // Metadata stress only: these are not admitted proof declarations.
        for digest_keys in [false, true] {
            let mut directory = Directory::new();
            for n in 0u64..20_000 {
                let key = if digest_keys {
                    let mut key = vec![0; 32];
                    key[..8].copy_from_slice(&n.to_le_bytes());
                    key
                } else {
                    format!("checked-declaration-{n:08}").into_bytes()
                };
                directory.set(&key, Some(blob((n % 251) as u8))).unwrap();
            }
            assert!(directory.is_spilled());
            assert_eq!(directory.len(), 20_000);
            let Storage::Spilled(backed) = &directory.storage else {
                unreachable!()
            };
            let backed = backed.borrow();
            let bytes = backed.heads.capacity() * std::mem::size_of::<u32>()
                + backed.index.resident_bytes()
                + backed.data.resident_bytes()
                + backed.recent.capacity() * std::mem::size_of::<(u64, Vec<u8>, Option<Blob>)>()
                + backed
                    .recent
                    .iter()
                    .map(|(_, key, _)| key.capacity())
                    .sum::<usize>();
            assert!(
                bytes < 2 * MEMORY_BYTES,
                "resident metadata capacity: {bytes}"
            );
            assert!(backed.recent_bytes <= CACHE_BYTES);
            drop(backed);
            for n in (0u64..20_000).step_by(97) {
                let key = if digest_keys {
                    let mut key = vec![0; 32];
                    key[..8].copy_from_slice(&n.to_le_bytes());
                    key
                } else {
                    format!("checked-declaration-{n:08}").into_bytes()
                };
                assert_eq!(directory.get(&key).unwrap(), Some(blob((n % 251) as u8)));
            }
        }
    }
    #[test]
    fn repeated_updates_bound_the_recent_cache_and_keep_tombstones() {
        let mut d = Directory::with_limit(0);
        for i in 0..1000 {
            let key = format!("entry-{i}");
            d.set(key.as_bytes(), Some(blob(1))).unwrap();
        }
        for i in 0..1000 {
            let key = format!("entry-{i}");
            d.set(key.as_bytes(), None).unwrap();
        }
        assert_eq!(d.len(), 0);
        assert_eq!(d.get(b"entry-0").unwrap(), None);
        let Storage::Spilled(backed) = &d.storage else {
            unreachable!()
        };
        assert!(backed.borrow().recent_bytes <= CACHE_BYTES);
        assert!(backed.borrow().recent.len() <= CACHE_ENTRIES);
    }
}
